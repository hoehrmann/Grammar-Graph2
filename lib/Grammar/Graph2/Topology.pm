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

  my @skippable = $self->_dbh->selectall_array(q{
    SELECT * FROM view_vertex_skippable
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
