package Grammar::Graph2::Megamata;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by nsort_by uniq_by/;
use List::MoreUtils qw/uniq/;
use Grammar::Graph2::Alphabet;
use Graph::SomeUtils qw/:all/;
use Algorithm::ConstructDFA2;
use Set::IntSpan;
use YAML::XS;
use Memoize;

use Grammar::Graph2::Automata;

has 'base_graph' => (
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

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

sub mega {

  my ($self) = @_;
  my $dbh = $self->base_graph->_dbh;
  my $g2 = $self->base_graph;

  my @edges = $dbh->selectall_array(q{
    WITH
    vertex_shadowed_by AS (
      SELECT 
        CAST(each.value AS TEXT) AS vertex,
        vertex_p.vertex AS by
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
    ),
    edge_selector AS (
      SELECT * FROM Edge
    ),
    edge_shadowed_by_or_self AS (
      SELECT
        COALESCE(src_shadow.by, e.src) AS src,
        COALESCE(dst_shadow.by, e.dst) AS dst
      FROM
        edge_selector e
          LEFT JOIN vertex_shadowed_by src_shadow
            ON (src_shadow.vertex = e.src)
          LEFT JOIN vertex_shadowed_by dst_shadow
            ON (dst_shadow.vertex = e.dst)
    ),
    stop_vertex(v) AS (
      SELECT
        vertex AS v
      FROM
        vertex_property
      WHERE
        type IN ('If', 'If1', 'If2', 'Fi2', 'Fi1', 'Fi')
        OR
        self_loop <> 'no'
        OR
        vertex IN (SELECT attribute_value
                   FROM graph_attribute
                   WHERE attribute_name
                     IN ('start_vertex', 'final_vertex'))
    )
    SELECT 
      e.src AS src,
      e.dst AS dst,
      CASE
      WHEN src_p.v IS NULL AND dst_p.v IS NULL THEN 'between'
      WHEN src_p.v IS NULL AND dst_p.v IS NOT NULL THEN 'rhs'
      WHEN src_p.v IS NOT NULL AND dst_p.v IS NULL THEN 'lhs'
      ELSE ''
      END AS type
    FROM
      edge_shadowed_by_or_self e
        LEFT JOIN stop_vertex src_p
          ON (src_p.v = e.src)
        LEFT JOIN stop_vertex dst_p
          ON (dst_p.v = e.dst)
  });

  my @start_vertices = uniq map {
    $_->[1]
  } grep {
    $_->[2] eq 'lhs'
  } @edges;

  my @final_vertices = uniq map {
    $_->[0]
  } grep {
    $_->[2] eq 'rhs'
  } @edges;

  my $vertex_that_does_not_exist = 0;

  my $subgraph = Graph::Feather->new(
    vertices => [ @start_vertices ],
    edges => [ #(map { [ $_ => $vertex_that_does_not_exist ] } @final_vertices),
               map { [ @$_[0,1] ] }
               grep { $_->[2] =~ /^(between)$/ } @edges ]
  );

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, @start_ids) = $automata->subgraph_automaton($subgraph, @start_vertices);

  my $vertex_to_states = $d->_dbh->selectall_hashref(q{
    SELECT
      vertex,
      json_group_array(state) AS states
    FROM
      Configuration
    GROUP BY
      vertex
  }, 'vertex');

  my %state_to_vertex = $automata->_insert_dfa($d);
}

1;

__END__

