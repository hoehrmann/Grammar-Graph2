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
use Grammar::Graph2::Ordering;

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

  });

  my $o = Grammar::Graph2::Ordering->new(
    g => $self->g
  );

  $self->_add_self_loop_attributes_new();
  $self->_log->debugf("done _add_self_loop_attributes_new");

  $self->_add_skippable();
  $self->_log->debugf("done _add_skippable");

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

  # This removes interior vertices in the copy of the grammar graph
  # by connecting "stack" vertices directly to one another to prepare
  # further analysis.

  for my $v ($g->vertices) {
    
    next if $vp->{$v}{is_stack};
    
    for my $p ($g->predecessors($v)) {
      for my $s ($g->successors($v)) {
        $g->add_edge( $p, $s );
      }
    }

    $g->delete_vertex( $v );

  }

  # This replaces properly balanced parts of the graph with direct
  # connections between the neighbouring vertices, leaving only the
  # parts of the graph that are not well-behaved, i.e., irregular.

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

  # This removes all edges except (Start A) -> (Final B) edges. This
  # is a bit counter-intuitive and could use more elaborate comments.

  for my $e ($g->edges) {

    $g->delete_edge(@$e) unless
      $vp->{$e->[0]}{is_push} and 
      $vp->{$e->[1]}{is_pop} and 
      $vp->{$e->[0]}{partner} ne $e->[1];

  }

  # The vertices of remaining edges and their partner vertices are
  # unusual and are thus marked as irregular.

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

sub _add_skippable {
  my ($self) = @_;

  # TODO: simplify

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
    SELECT
      vertex_p.vertex,
      (self_loop = 'no') AS skippable
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

1;

__END__

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


--- this used to be in add_skippable

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
