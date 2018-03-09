package Grammar::Graph2::Topology;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by uniq_by/;
use Set::IntSpan;
use Set::IntSpan::Partition;
use List::Util qw/uniq/;
use JSON;
use List::OrderBy;
use List::StackBy;

has 'g' => (
  is       => 'ro',
  required => 1,
);

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

has '_dbh' => (
  is       => 'rw',
);

sub BUILD {
  my ($self) = @_;

  # FIXME(bh): stealing other module's dbh is bad
  $self->_dbh( $self->g->g->{dbh} );

  local $self->g->g->{dbh}->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{

    -----------------------------------------------------------------
    -- view_parent_child
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_parent_child;
    CREATE VIEW view_parent_child AS
    WITH RECURSIVE pc(parent, child) AS (

      SELECT
        Edge.src AS parent,
        Edge.dst AS child
      FROM
        Edge
          INNER JOIN vertex_property as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN vertex_property as src_p
            ON (src_p.vertex = Edge.src)
      WHERE
        src_p.is_push
        -- AND dst_p.vertex <> src_p.partner

      UNION

      SELECT
        r.parent AS parent,
        COALESCE(partner_edges.dst, Edge.dst) AS child
      FROM Edge
        INNER JOIN pc AS r
          ON (Edge.src = r.child)
        INNER JOIN vertex_property AS src_p
          ON (Edge.src = src_p.vertex)
        INNER JOIN vertex_property AS dst_p
          ON (Edge.dst = dst_p.vertex)
        INNER JOIN vertex_property AS parent_p
          ON (r.parent = parent_p.vertex)
        INNER JOIN vertex_property AS child_p
          ON (r.child = child_p.vertex)
        LEFT JOIN Edge partner_edges
          ON (src_p.partner = partner_edges.src
            and src_p.is_push)
      WHERE
        parent_p.partner <> src_p.vertex
        -- AND COALESCE(partner_edges.dst, Edge.dst) <> parent_p.partner
    )
    SELECT
      pc.*
    FROM
      pc
        INNER JOIN vertex_property AS parent_p
          ON (pc.parent = parent_p.vertex)
        INNER JOIN vertex_property AS child_p
          ON (pc.child = child_p.vertex)
    WHERE
      1
      -- OR child_p.is_push

    ;
    
    -----------------------------------------------------------------
    -- view_paradoxical
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_paradoxical;
    CREATE VIEW view_paradoxical(parent, child) AS
    WITH RECURSIVE
    paradoxical(parent, child) AS (
      SELECT parent, child
      FROM view_parent_child
      INTERSECT
      SELECT child, parent
      FROM view_parent_child
    )
    SELECT
      parent,
      child
    FROM
      paradoxical
    ;

    -----------------------------------------------------------------
    -- view_productive_loops
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_productive_loops;
    CREATE VIEW view_productive_loops AS
    WITH RECURSIVE
    path(root, is_productive, dst) AS (
      SELECT
        src_p.vertex AS root,
        0 AS is_productive,
        dst_p.vertex AS dst
      FROM
        Edge
          INNER JOIN vertex_property as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN vertex_property as src_p
            ON (src_p.vertex = Edge.src)
      WHERE
        src_p.partner IS NOT NULL
        AND (
          src_p.vertex IN (SELECT parent FROM view_paradoxical)
          OR src_p.partner IN (SELECT parent FROM view_paradoxical)
        )

      UNION

      SELECT
        root_p.vertex AS root,
        r.is_productive
          OR src_p.type = 'Input' AS is_productive,
        dst_p.vertex AS dst
      FROM
        path r
          INNER JOIN Edge
            ON (Edge.src = r.dst)
          INNER JOIN vertex_property as src_p
            ON (src_p.vertex = Edge.src)
          INNER JOIN vertex_property as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN vertex_property as root_p
            ON (root_p.vertex = r.root)
            
      WHERE
        1 = 1
        AND src_p.vertex <> r.root
        AND src_p.vertex <> root_p.partner
    )
    SELECT
      root AS vertex
    FROM
      path
    WHERE
      root = dst
    GROUP BY
      root,
      dst
    HAVING
      MAX(is_productive) = 1

    ;

    -----------------------------------------------------------------
    -- view_self_loop
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_self_loop;
    CREATE VIEW view_self_loop AS
    SELECT
      src_p.vertex AS vertex,
      CASE
      WHEN (src_productive.vertex IS NOT NULL)
        AND (partner_productive.vertex IS NOT NULL) THEN 'irregular'
      WHEN (start_paradox.parent IS NOT NULL) THEN 'linear'
      WHEN (final_paradox.parent IS NOT NULL) THEN 'linear'
      ELSE 'no'
      END AS self_loop
    FROM
      vertex_property src_p
        LEFT JOIN view_paradoxical start_paradox
          ON (start_paradox.parent = src_p.vertex)
        LEFT JOIN view_paradoxical final_paradox
          ON (final_paradox.parent = src_p.partner)
        LEFT JOIN view_productive_loops src_productive
          ON (src_productive.vertex = src_p.vertex)
        LEFT JOIN view_productive_loops partner_productive
          ON (partner_productive.vertex = src_p.partner)

    ;

    -----------------------------------------------------------------
    -- view_epsilon_closure
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_epsilon_closure;
    CREATE VIEW view_epsilon_closure(vertex, e_reachable) AS
    WITH RECURSIVE
    all_e_successors_and_self(root, v) AS (

      SELECT vertex AS root, vertex AS v FROM vertex_property

      UNION

      SELECT
        r.root,
        Edge.dst
      FROM
        Edge
          INNER JOIN all_e_successors_and_self AS r
            ON (Edge.src = r.v)
          INNER JOIN vertex_property AS src_p
            ON (Edge.src = src_p.vertex)
      WHERE
        src_p.type <> 'Input'
    )
    SELECT
      root AS vertex,
      v AS e_reachable
    FROM
      all_e_successors_and_self
    ;

  });

  $self->_add_self_loop_attributes();
  $self->_add_topological_attributes();
  $self->_dbh->do(q{ ANALYZE });
}

local $Storable::canonical = 1;

sub _add_self_loop_attributes {
  my ($self) = @_;

  my @self_loop = $self->_dbh->selectall_array(q{
    SELECT vertex, self_loop
    FROM view_self_loop
  });

  $self->g->vp_self_loop(@$_)
    for @self_loop;
}

sub _strongly_connected_graph_feather {
  my ($g) = @_;

  my @sccs = $g->strongly_connected_components;

  @$_ = sort @$_ for @sccs;

  my %v_to_id;
  my %h;
  for (my $ix = 0; $ix < @sccs; ++$ix) {
    $v_to_id{ $_ } = $ix + 1 for @{ $sccs[$ix] };
    $h{ $ix + 1 } = $sccs[$ix];
  }

  my $scg2 = Graph::Feather->new(
    vertices => [ map { join '+', @$_ } values %h ],
    edges    => [ map {
      [ map { join '+', @{ $h{ $v_to_id{$_} } } } @$_ ]
    } $g->edges ],
  );

  $scg2->feather_delete_edges(
    map { [ $_, $_ ] } $scg2->vertices
  );

  return $scg2;
}

sub _scg_topological_depth {
  my ($d) = @_;

  my $scgf = _strongly_connected_graph_feather($d);

  my $result = $scgf->{dbh}->selectall_hashref(q{
    WITH RECURSIVE
    roots(vertex) AS (
      SELECT DISTINCT
        v.vertex_name AS vertex
      FROM
        vertex v
          LEFT JOIN Edge successors
            ON (successors.src = v.vertex_name)
          LEFT JOIN Edge predecessors
            ON (predecessors.dst = v.vertex_name)
      WHERE
        predecessors.src IS NULL
    ),
    dfs(vertex, depth) AS (
      SELECT
        vertex,
        0 AS depth
      FROM roots
      UNION ALL
      SELECT
        e.dst AS vertex,
        depth + 1 AS depth
      FROM dfs
        INNER JOIN Edge e
          ON (e.src = dfs.vertex)
    ),
    topology(vertex, max_depth, min_depth) AS (
      SELECT vertex, MAX(depth), MIN(depth) FROM dfs
      GROUP BY vertex
    )
    SELECT * FROM topology ORDER BY max_depth DESC
  }, 'vertex');

  for my $k (keys %$result) {
    next unless $k =~ /\+/;
    for my $v (split/\+/, $k) {
      # FIXME: clone?
      $result->{$v} = $result->{$k};
    }
  }

  return $result;
}

sub _topo_parent_child {
  my ($self) = @_;

  my $d = Graph::Directed->new;

  $d->add_vertices(
    map { @$_ } $self->_dbh->selectall_array(q{
      SELECT
        src_p.vertex
      FROM
        vertex_property src_p
    })
  );

  $d->add_edges(
    $self->_dbh->selectall_array(q{
      SELECT
        pc.parent AS parent,
        pc.child AS child
      FROM
        view_parent_child pc
          INNER JOIN vertex_property parent_p
            ON (pc.parent = parent_p.vertex)
          INNER JOIN vertex_property child_p
            ON (pc.child = child_p.vertex)

    })
  );

  return _scg_topological_depth($d);
}

sub _topo_epsilon {
  my ($self) = @_;

  my $d = Graph::Directed->new;

  $d->add_vertices(
    map { @$_ } $self->_dbh->selectall_array(q{
      SELECT
        src_p.vertex
      FROM
        vertex_property src_p
    })
  );

  $d->add_edges(
    $self->_dbh->selectall_array(q{
      SELECT
        src,
        dst
      FROM
        Edge
          INNER JOIN vertex_property src_p
            ON (src_p.vertex = Edge.src)
      WHERE
        src_p.type <> 'Input'
    })
  );

  return _scg_topological_depth($d)
}

sub _add_topological_attributes {
  my ($self) = @_;

  my $json = JSON->new
    ->canonical(1)
    ->ascii(1)
    ->indent(0);

  my $t1 = $self->_topo_epsilon();
  my $t2 = $self->_topo_parent_child();

  # FIXME: something to do with unreachable vertices?

  for ($self->g->g->vertices) {
    warn $_ unless defined $t1->{$_}{vertex};
    $self->g->vp_epsilon_group($_,
      $json->encode([ split/\+/, $t1->{$_}{vertex}])
    );
  }

  my @order = order_by_desc {
    $t1->{$_}{max_depth} // warn
  } then_by_desc {
    $t2->{$_}{max_depth} // warn
  } then_by_desc {
    $t1->{$_}{min_depth} // warn
  } then_by_desc {
    $t2->{$_}{min_depth} // warn
  } $self->g->g->vertices();

  my @stacks = stack_by {
    join ',', $t1->{$_}{max_depth},
              $t1->{$_}{min_depth},
              $t2->{$_}{max_depth},
              $t2->{$_}{min_depth}
  } @order;

  while (@stacks) {
    my $current = shift @stacks;
    $self->g->vp_topo($_, 2 + $#stacks)
      for @$current
  }

}

1;

__END__

