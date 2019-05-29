package Grammar::Graph2::Topology;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by uniq_by nsort_by/;
use Set::IntSpan;
use Set::IntSpan::Partition;
use List::Util qw/uniq/;
use JSON;
use List::OrderBy;
use List::StackBy;
use Acme::Partitioner;

has 'g' => (
  is       => 'ro',
  required => 1,
  weak_ref => 1,
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
  weak_ref => 1,
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
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as src_p
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
        INNER JOIN view_vp_plus AS src_p
          ON (Edge.src = src_p.vertex)
        INNER JOIN view_vp_plus AS dst_p
          ON (Edge.dst = dst_p.vertex)
        INNER JOIN view_vp_plus AS parent_p
          ON (r.parent = parent_p.vertex)
        INNER JOIN view_vp_plus AS child_p
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
          OR
          src_p.partner IN (SELECT parent FROM view_paradoxical)
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
    -- view_self_loop_linearity
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_self_loop_linearity;
    CREATE VIEW view_self_loop_linearity AS
    WITH RECURSIVE
    path(root, is_productive, dst) AS (
      SELECT
        src_p.vertex AS root,
        0 AS is_productive,
        dst_p.vertex AS dst
      FROM
        Edge
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as src_p
            ON (src_p.vertex = Edge.src)
          INNER JOIN view_vp_plus as src_partner_p
            ON (src_partner_p.vertex = src_p.partner)
      WHERE
        src_p.partner IS NOT NULL
        AND (
          src_partner_p.self_loop <> 'no'
          OR
          src_p.self_loop <> 'no'
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
          INNER JOIN view_vp_plus as src_p
            ON (src_p.vertex = Edge.src)
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as root_p
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

    -----------------------------------------------------------------
    -- view_relevant_stack_vertices
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_relevant_stack_vertices;
    CREATE VIEW view_relevant_stack_vertices AS
    SELECT
      vertex_p.vertex AS vertex
    FROM
      view_vp_plus vertex_p
        INNER JOIN view_start_vertex
        INNER JOIN view_final_vertex
    WHERE
      (vertex_p.is_stack AND vertex_p.self_loop <> 'no')
      OR
      (vertex_p.type IN ('If', 'If1', 'If2', 'Fi', 'Fi1', 'Fi2')
        AND vertex_p.contents_self_loop <> 'no')
      OR (vertex_p.vertex = view_start_vertex.vertex)
      OR (vertex_p.vertex = view_final_vertex.vertex)
    ;

    -----------------------------------------------------------------
    -- view_reverse_stack_closure
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_reverse_stack_closure;
    CREATE VIEW view_reverse_stack_closure(vertex, s_reachable) AS
    WITH RECURSIVE
    all_s_predecessors_and_self(root, v) AS (

      SELECT vertex AS root, vertex AS v FROM vertex_property

      UNION

      SELECT
        r.root,
        Edge.src
      FROM
        Edge
          INNER JOIN all_s_predecessors_and_self AS r
            ON (Edge.dst = r.v)
          INNER JOIN view_vp_plus AS dst_p
            ON (Edge.dst = dst_p.vertex)
      WHERE
        dst_p.vertex NOT IN (
          SELECT vertex FROM view_relevant_stack_vertices
        )
    )
    SELECT
      root AS vertex,
      v AS s_reachable
    FROM
      all_s_predecessors_and_self
    ;

    -----------------------------------------------------------------
    -- view_vertices_between_self_and_partner
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_vertices_between_self_and_partner;
    CREATE VIEW view_vertices_between_self_and_partner AS
    WITH RECURSIVE
    foo AS (
      SELECT
        vertex AS root,
        vertex AS reachable
      FROM
        vertex_property
      WHERE
        partner IS NOT NULL
      UNION
      SELECT
        foo.root AS root,
        Edge.dst AS reachable
      FROM
        foo
          INNER JOIN vertex_property root_p
            ON (root_p.vertex = foo.root)
          INNER JOIN Edge
            ON (Edge.src = foo.reachable)
      WHERE
        root_p.partner <> Edge.src
    )
    SELECT
      root,
      reachable
    FROM
      foo
    ;

    -----------------------------------------------------------------
    -- view_contents_self_loop
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_contents_self_loop;
    CREATE VIEW view_contents_self_loop AS
    WITH RECURSIVE
    base AS (
      SELECT
        vertex,
        self_loop
      FROM
        vertex_property
      UNION
      SELECT
        vpc.parent AS vertex,
        base.self_loop AS self_loop
      FROM
        base 
          INNER JOIN view_parent_child vpc
            ON (base.vertex = vpc.child)
          INNER JOIN vertex_property parent_p
            ON (parent_p.vertex = vpc.parent)
          INNER JOIN vertex_property child_p
            ON (child_p.vertex = vpc.child)
    ),
    cond AS (
      -- ensures symmetry
      SELECT
        *
      FROM
        base
      UNION
      SELECT
        vertex_p.partner,
        base.self_loop
      FROM
        base
          INNER JOIN vertex_property vertex_p
            ON (vertex_p.vertex = base.vertex)
      WHERE
        vertex_p.partner IS NOT NULL
    )
    SELECT
      vertex,
      MIN(self_loop) AS self_loop
    FROM
      cond
    GROUP BY
      vertex
    ;

    -----------------------------------------------------------------
    -- view_without_skippables
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_without_skippables;
    CREATE VIEW view_without_skippables AS 
    WITH RECURSIVE
    foo AS (
      SELECT * FROM edge
      UNION
      SELECT
        foo.src AS src,
        edge.dst AS dst
      FROM
        foo
          INNER JOIN edge
            ON (foo.dst = edge.src)
          INNER JOIN view_vp_plus mid_p
            ON (mid_p.vertex = foo.dst
              AND mid_p.skippable
              AND mid_p.type <> 'Input')
    )
    SELECT
      foo.*
    FROM
      foo
        INNER JOIN view_vp_plus src_p
          ON (src_p.vertex = foo.src)
        INNER JOIN view_vp_plus dst_p
          ON (dst_p.vertex = foo.dst)
    WHERE
      (src_p.type = 'Input' OR NOT(src_p.skippable))
      AND
      (dst_p.type = 'Input' OR NOT(dst_p.skippable))
    ;

  });

  $self->_add_topological_attributes();
  $self->_log->debugf("done _add_topological_attributes");

  $self->_add_self_loop_attributes_new();
  $self->_log->debugf("done _add_self_loop_attributes_new");

  $self->_add_stack_groups();
  $self->_log->debugf("done _add_stack_groups");

  $self->_add_skippable();
  $self->_log->debugf("done _add_skippable");

#  $self->_add_representative();
  $self->_dbh->do(q{ ANALYZE });
}

local $Storable::canonical = 1;

sub _add_self_loop_attributes_new {

  my ($self) = @_;

  my $dbh = $self->_dbh;

  my $g = Graph::Feather->new(
    edges => $dbh->selectall_arrayref(q{
      SELECT * FROM edge
    }),
  );

  # TODO: use proper accessors instead
  my $vp = $dbh->selectall_hashref(q{
    SELECT * FROM view_vp_plus
  }, 'vertex');

  for my $v ($g->vertices) {
    
    next if $vp->{$v}{is_stack};
    
    for my $p ($g->predecessors($v)) {
      for my $s ($g->successors($v)) {
        $g->add_edge( $p, $s );
      }
    }

    $g->delete_vertex( $v );

  }

  my @todo = $g->edges;

  my %seen;

  while (@todo) {

    my $e = shift @todo;

    next if $seen{ $e->[0] }{ $e->[1] }++;

    if ( $vp->{$e->[0]}{is_push} and $vp->{$e->[0]}{partner} eq $e->[1] ) {

      for my $p ( $g->predecessors($e->[0]) ) {
        for my $s ( $g->successors($e->[1]) ) {
          $g->add_edge( $p, $s );
          push @todo, [ $p, $s ];
        }
      }

      $g->delete_edge(@$e);

    }

  }

  for my $e ($g->edges) {

    $g->delete_edge(@$e) unless
      $vp->{$e->[0]}{is_push} and 
      $vp->{$e->[1]}{is_pop} and 
      $vp->{$e->[0]}{partner} ne $e->[1];

  }

  my %self_loop;

  for ($g->edges) {
    $self_loop{ $_->[0] }++;
    $self_loop{ $_->[1] }++;
    $self_loop{ $vp->{ $_->[0] }{ partner } }++;
    $self_loop{ $vp->{ $_->[1] }{ partner } }++;
  }

  $self->g->vp_self_loop($_, 'irregular') for keys %self_loop;

$self->_dbh->sqlite_backup_to_file('linearity.sqlite');

  my @prod = map { @$_ } $self->_dbh->selectall_array(q{
    SELECT vertex FROM view_self_loop_linearity
  });

  my %in_prod = map { $_ => 1 } @prod;

#use YAML::XS;
#warn Dump { in_prod => \%in_prod };

  for my $v (keys %self_loop) {
    if ( $in_prod{ $v } and $in_prod{ $self->g->vp_partner($v) } ) {
      next;
    }
    $self->g->vp_self_loop($v, 'linear');
  }

#  $self->g->vp_self_loop($_, 'linear')
#    for grep { not $in_prod{$_} } keys %self_loop;

  my @contents_self_loop = $self->_dbh->selectall_array(q{
    SELECT vertex, self_loop
    FROM view_contents_self_loop
  });

  $self->g->vp_contents_self_loop(@$_)
    for @contents_self_loop;

  for ($g->edges) {

    $self->_log->debugf('self_loop: %s',

      join " ", map {
        $_,
        $vp->{$_}{type},
        $vp->{$_}{name},
        $vp->{$_}{partner} // '_'
      } @$_

    );

  }

#  use YAML::XS;
#  say Dump \%self_loop;

}


sub _add_self_loop_attributes__old {
  my ($self) = @_;

  my $db_utils = Grammar::Graph2::DBUtils->new(
    g => $self);

  $db_utils->views_to_tables(
    'view_self_loop',
  );

  my @self_loop = $self->_dbh->selectall_array(q{
    SELECT vertex, self_loop
    FROM m_view_self_loop
  });

  $self->g->vp_self_loop(@$_)
    for @self_loop;

  $self->_log->debugf("done with m_view_self_loop");

  # Workaround for reftests/alxbug
  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      self_loop = (
        SELECT MIN(vertex_p.self_loop)
        FROM vertex_property vertex_p
        WHERE vertex_p.name = vertex_property.name
      )
    WHERE
      name IS NOT NULL
  }) if 1;

  # The above is incomplete :(

  my @contents_self_loop = $self->_dbh->selectall_array(q{
    SELECT vertex, self_loop
    FROM view_contents_self_loop
  });

  $self->g->vp_contents_self_loop(@$_)
    for @contents_self_loop;

  # Workaround
  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      self_loop = (
        SELECT MIN(vertex_p.self_loop, MIN(vertex_p.contents_self_loop))
        FROM vertex_property vertex_p
        WHERE vertex_p.name = vertex_property.name
      )
    WHERE
      name IS NOT NULL
  }) if 0;

}

sub _strongly_connected_graph_feather {
  my ($g) = @_;

  my @sccs = $g->strongly_connected_components;

  @$_ = sort @$_ for @sccs;

  my %v_to_id;
  my %h;
  
  for (my $ix = 0; $ix < @sccs; ++$ix) {
    $v_to_id{ $_ } = $ix for @{ $sccs[$ix] };
    $h{ $ix } = $sccs[$ix];
  }

  my $scg2 = Graph::Feather->new(
    vertices => [ map { join '+', @$_ } values %h ],
    edges    => [
      grep {
        $_->[0] ne $_->[1]
      }
      map {
        [ map { join '+', @{ $h{ $v_to_id{$_} } } } @$_ ]
      }
      $g->edges
    ],
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

  $self->_log->debugf("done _topo_epsilon");
  my $t1 = $self->_topo_epsilon();

  my $t2 = $self->_topo_parent_child();
  $self->_log->debugf("done _topo_parent_child");

  # FIXME: something to do with unreachable vertices?

  for ($self->g->g->vertices) {
    warn $_ unless defined $t1->{$_}{vertex};
    my @vertices = split/\+/, $t1->{$_}{vertex};
    next if @vertices == 1;
    $self->g->vp_epsilon_group($_,
      $json->encode([ @vertices ])
    );
  }

  my $helper = sub {
    my ($v) = @_;
    my @pred = $self->g->g->predecessors($v);
    my @succ = $self->g->g->successors($v);

    # TODO: simplify this code

    if ($self->g->is_if1_vertex($v)) {
      die unless @pred == 1;
      die unless $self->g->is_if_vertex(@pred);
      return $self->g->vp_name(@pred) eq '#ordered_choice';
    }

    if ($self->g->is_if2_vertex($v)) {
      die unless @pred == 1;
      die unless $self->g->is_if_vertex(@pred);
      return $self->g->vp_name(@pred) eq '#exclusion';
    }

    if ($self->g->is_fi1_vertex($v)) {
      die unless @succ == 1;
      die unless $self->g->is_fi_vertex(@succ);
      return $self->g->vp_name(@succ) eq '#ordered_choice';
    }

    if ($self->g->is_fi2_vertex($v)) {
      die unless @succ == 1;
      die unless $self->g->is_fi_vertex(@succ);
      return $self->g->vp_name(@succ) eq '#exclusion';
    }

    return 0;
  };

  my @order = order_by_desc {
    $t1->{$_}{max_depth} // warn
  } then_by_desc {
    $t2->{$_}{max_depth} // warn
  } then_by_desc {
    $t1->{$_}{min_depth} // warn
  } then_by_desc {
    $t2->{$_}{min_depth} // warn
  } then_by_desc {
    0 + $helper->($_)
  } $self->g->g->vertices();

  my @stacks = stack_by {
    join ',', $t1->{$_}{max_depth},
              $t1->{$_}{min_depth},
              $t2->{$_}{max_depth},
              $t2->{$_}{min_depth},
              0 + $helper->($_)
  } @order;

  while (@stacks) {
    my $current = shift @stacks;
    $self->g->vp_topo($_, 2 + $#stacks)
      for @$current
  }

}

sub _add_stack_groups {
  my ($self) = @_;

  my @stack_groups = $self->_dbh->selectall_array(q{
    WITH
    ordered AS (
      SELECT
        rs.*
      FROM
        view_reverse_stack_closure rs
          INNER JOIN view_relevant_stack_vertices rv
            ON (rs.s_reachable = rv.vertex)
          LEFT JOIN view_relevant_stack_vertices rr
            ON (rs.vertex = rr.vertex)
      WHERE
        rr.vertex IS NULL
      ORDER BY
        rs.vertex
    ),
    grouped AS (
      SELECT
        ordered.vertex AS vertex,
        /**/_json_array_uniq_sorted/**/(
          json_group_array(ordered.s_reachable)
        ) AS s_reachable
      FROM
        ordered
      GROUP BY
        ordered.vertex
    ),
    final AS (
      SELECT
        json_group_array(vertex) AS vertices,
        s_reachable AS grouping
      FROM
        grouped
      GROUP BY 
        s_reachable  
    ),
    single AS (
      SELECT
        json_group_array(json(vertices)) AS single
      FROM
        final
      GROUP BY 
        NULL
    ),
    vertex_stack_group AS (
      SELECT
        each_inner.value AS vertex,
        each_outer.key + 1 AS stack_group
      FROM
        single
          INNER JOIN json_each(single.single) each_outer
          INNER JOIN json_each(each_outer.value) each_inner
    ),
    group_min_vertex AS (
      SELECT
        vsg.stack_group,
        vertex_p.type = 'Input' AS is_input,
        MIN(vsg.vertex) AS min_vertex
      FROM
        vertex_stack_group vsg
          INNER JOIN vertex_property vertex_p
            ON (vertex_p.vertex = vsg.vertex
              AND vertex_p.type = 'Input')
      GROUP BY
        vsg.stack_group
      UNION
      SELECT
        vsg.stack_group,
        vertex_p.type = 'Input' AS is_input,
        MIN(vsg.vertex) AS min_vertex
      FROM
        vertex_stack_group vsg
          INNER JOIN vertex_property vertex_p
            ON (vertex_p.vertex = vsg.vertex
              AND vertex_p.type <> 'Input')
      GROUP BY
        vsg.stack_group
    ),
    result AS (
      SELECT
        vsg.vertex AS vertex,
        gmv.min_vertex AS stack_group
      FROM
        vertex_stack_group vsg
          INNER JOIN vertex_property vertex_p
            ON (vsg.vertex = vertex_p.vertex)
          INNER JOIN group_min_vertex gmv
            ON (gmv.stack_group = vsg.stack_group
              AND gmv.is_input = (vertex_p.type = 'Input'))
    )
    SELECT * FROM result
  });

  $self->g->vp_stack_group(@$_)
    for @stack_groups;
}

sub _add_skippable_old {
  my ($self) = @_;

  my @skippable = $self->_dbh->selectall_array(q{
    WITH 
    conditionals AS (
      SELECT
        if_p.vertex AS 'If',
        json_array(
          if_p.vertex, if_p.p1, if_p.p2,
          fi_p.vertex, fi_p.p1, fi_p.p2) AS six_tuple
      FROM
        view_vp_plus if_p
          INNER JOIN view_vp_plus fi_p
            ON (if_p.partner = fi_p.vertex
              AND if_p.type = 'If')
    ),
    base AS (
      SELECT
        conditionals.If AS root,
        each.value AS related
      FROM
        conditionals
          INNER JOIN json_each(conditionals.six_tuple) each
    ),
    if_property AS (
      SELECT
        base.root AS root,
        MIN(MIN(related_p.self_loop, related_p.contents_self_loop)) AS property
      FROM
        base
          INNER JOIN view_vp_plus related_p
            ON (base.related = related_p.vertex)
      GROUP BY 
        base.root
    ),
    result AS (
      SELECT
        base.related AS vertex,
        if_property.property AS property
      FROM
        if_property
          INNER JOIN base
            ON (if_property.root = base.root)
      UNION
      SELECT
        vertex_p.vertex AS vertex,
        vertex_p.self_loop
      FROM
        view_vp_plus vertex_p
      WHERE
        NOT(vertex_p.is_conditional)
    )
    SELECT
      result.vertex,
      property = 'no' AS skippable
    FROM
      result
        INNER JOIN view_start_vertex
        INNER JOIN view_final_vertex
    WHERE
      result.vertex NOT IN (view_start_vertex.vertex,
        view_final_vertex.vertex)
    UNION
    SELECT
      vertex,
      0
    FROM
      view_start_vertex
    UNION
    SELECT
      vertex,
      0
    FROM
      view_final_vertex
  });

  $self->g->vp_skippable(@$_)
    for @skippable;
  
}

sub _add_skippable {
  my ($self) = @_;

  my @skippable = $self->_dbh->selectall_array(q{
    WITH 
    conditionals AS (
      SELECT
        if_p.vertex AS 'If',
        json_array(
          if_p.vertex, if_p.p1, if_p.p2,
          fi_p.vertex, fi_p.p1, fi_p.p2) AS six_tuple
      FROM
        view_vp_plus if_p
          INNER JOIN view_vp_plus fi_p
            ON (if_p.partner = fi_p.vertex
              AND if_p.type = 'If')
    ),
    base AS (
      SELECT
        conditionals.If AS root,
        each.value AS related
      FROM
        conditionals
          INNER JOIN json_each(conditionals.six_tuple) each
    )
/*
    , if_property AS (
      SELECT
        base.root AS root,
        MIN(MIN(related_p.self_loop, related_p.contents_self_loop)) AS property
      FROM
        base
          INNER JOIN view_vp_plus related_p
            ON (base.related = related_p.vertex)
      GROUP BY 
        base.root
    ),
    result AS (
      SELECT
        base.related AS vertex,
        if_property.property AS property
      FROM
        if_property
          INNER JOIN base
            ON (if_property.root = base.root)
      UNION
      SELECT
        vertex_p.vertex AS vertex,
        vertex_p.self_loop
      FROM
        view_vp_plus vertex_p
      WHERE
        NOT(vertex_p.is_conditional)
    )
*/
    SELECT
      vertex_p.vertex,
      self_loop = 'no' AS skippable
    FROM
      vertex_property vertex_p
        INNER JOIN view_start_vertex
        INNER JOIN view_final_vertex
    WHERE
      vertex_p.vertex NOT IN (view_start_vertex.vertex,
        view_final_vertex.vertex)
      AND
      vertex_p.vertex NOT IN (SELECT related FROM base)
    UNION
    SELECT
      vertex,
      0
    FROM
      view_start_vertex
    UNION
    SELECT
      vertex,
      0
    FROM
      view_final_vertex
    UNION
    SELECT
      related,
      0
    FROM
      base
  });

  $self->g->vp_skippable(@$_)
    for @skippable;
  
}


sub _add_representative {
  my ($self) = @_;

  my $f = Graph::Feather->new(
    edges => [ $self->_dbh->selectall_array('
      SELECT * FROM view_without_skippables
    ') ]
  );

  my $p = Acme::Partitioner->using($f->vertices);

  my $partitioner =
    $p->once_by(sub {
        my ($skip) = $self->g->vp_skippable($_);
        return $skip ? '' : $_
      })
      ->then_by(sub {
        my $v = $_;

        my ($skip) = $self->g->vp_skippable($_);
        return '.' unless $skip;

        my @foo = sort { $a cmp $b } uniq
          map { $p->partition_of($_) } $f->predecessors($v); # add $v?

        return join ' ', @foo;
      })
      ;

  while ($partitioner->refine) {
    $self->_log->debugf("representative p size = %u", $p->size());
  }

  my $map_function = sub {
    my ($v) = @_;
    return unless $f->has_vertex($v);
    return [nsort_by { $self->g->vp_topo($_) } $p->items_in( $p->partition_of($v) )]->[0]
  };
  
  for my $v ($self->g->g->vertices) {
    $self->g->vp_representative($v, $map_function->($v) // $v);
  }

}

1;

__END__

    -----------------------------------------------------------------
    -- view_next_stack
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_next_stack;

    CREATE VIEW view_next_stack AS
    WITH RECURSIVE
    stop_vertex(vertex) AS (
      SELECT
        vertex
      FROM
        vertex_property
      WHERE
        type IN (
          'If1', 'If2', 'Fi1', 'Fi2',
          'If', 'Fi', 'Prelude', 'Postlude')
        OR
        self_loop <> 'no' -- TODO: 'irregular'?
        OR
        vertex IN (SELECT vertex FROM view_start_vertex
                   UNION
                   SELECT vertex FROM view_final_vertex)
    ),
    successors_and_self(origin, v) AS (

      SELECT vertex AS origin, vertex AS v FROM vertex_property

      UNION

      SELECT
        r.origin,
        Edge.dst
      FROM
        Edge
          INNER JOIN successors_and_self AS r
            ON (Edge.src = r.v)
          INNER JOIN vertex_property AS src_p
            ON (Edge.src = src_p.vertex)
      WHERE
        src_p.vertex NOT IN (SELECT * FROM stop_vertex)
    )
    SELECT
      origin AS vertex,
      v AS next_stack
    FROM
      successors_and_self
    WHERE
      v IN (SELECT * FROM stop_vertex)
    ORDER BY
      origin,
      v
    ;

