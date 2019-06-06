package Grammar::Graph2;
use strict;
use warnings;
use 5.024000;
use Moo;
use Log::Any qw//;
use Types::Standard qw/:all/;
use List::Util qw/min max/;
use List::MoreUtils qw/uniq/;
use List::OrderBy;
use List::StackBy;
use List::UtilsBy qw/uniq_by nsort_by/;

use Graph::Feather;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use Grammar::Graph2;
# use Grammar::Graph2::TestParser::MatchEnumerator;
use Grammar::Graph2::Conditionals;
use Grammar::Graph2::Topology;
use Grammar::Graph2::Automata;
use Grammar::Graph2::Megamata;
use Grammar::Graph2::UTF8;
use Acme::Partitioner;

use Memoize;
use YAML::XS;

sub _cover_input_input_edges {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_input_input_edges
  });

  $self->_dbh->do(q{
    CREATE VIEW view_input_input_edges AS
    SELECT
      Edge.rowid AS rowid,
      Edge.src AS src,
      Edge.dst AS dst
    FROM
      Edge
        INNER JOIN vertex_property src_p
          ON (src_p.vertex = Edge.src)
        INNER JOIN vertex_property dst_p
          ON (dst_p.vertex = Edge.dst)
    WHERE
      src_p.type = 'Input'
      AND
      dst_p.type = 'Input'
  });

  my @new_epsilons = $self->_dbh->selectall_array(q{
    SELECT
      max_vertex.vertex + ii.rowid AS vertex,
      ii.src,
      ii.dst
    FROM
      view_input_input_edges ii
        INNER JOIN (SELECT
                      MAX(vertex_name+0) AS vertex
                    FROM
                      vertex) max_vertex
  });

  $self->vp_type($_->[0], 'empty') for @new_epsilons;
  $self->g->add_edges(map {
    [ $_->[1], $_->[0] ],
    [ $_->[0], $_->[2] ],
  } @new_epsilons);

  $self->g->feather_delete_edges($self->_dbh->selectall_array(q{
    SELECT src, dst FROM view_input_input_edges
  }));

}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################

sub _cover_epsilons {
  my ($g2) = @_;

  $g2->_log->debug('begin _cover_epsilons');
#  $g2->_dbh->sqlite_backup_to_file('cover_epsilons.before.sqlite');

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  # TODO: split this VIEW into several?

  my ($data) = $g2->_dbh->selectrow_array(q{

    WITH
    -----------------------------------------------------------------
    -- Arguments used in this CTE
    -----------------------------------------------------------------
    args AS (
      SELECT
        (SELECT MAX(vertex+0) FROM vertex_property) AS base
    ),
    -----------------------------------------------------------------
    -- Epsilon vertices
    -----------------------------------------------------------------
    epsilon_vertices AS (
      SELECT
        vertex
      FROM
        vertex_property
      WHERE
        type <> 'Input'
    ),
    -----------------------------------------------------------------
    -- Epsilon vertices except (grammar graph) start and final vertex
    -----------------------------------------------------------------
    interior_epsilon_vertices AS (
      SELECT
        vertex
      FROM
        epsilon_vertices
      WHERE
        vertex NOT IN (SELECT vertex FROM view_start_vertex)
        AND
        vertex NOT IN (SELECT vertex FROM view_final_vertex)
    ),
    -----------------------------------------------------------------
    -- Edges between interior epsilon vertices
    -----------------------------------------------------------------
    interior_epsilon_edges AS (
      SELECT
        Edge.src AS src,
        Edge.dst AS dst
      FROM
        Edge
          INNER JOIN interior_epsilon_vertices src_r
            ON (src_r.vertex = Edge.src) 
          INNER JOIN interior_epsilon_vertices dst_r
            ON (dst_r.vertex = Edge.dst)
    ),
    -----------------------------------------------------------------
    -- All (interior epsilon) edges both ways
    -----------------------------------------------------------------
    undirected_edges AS (
      SELECT * FROM interior_epsilon_edges
      UNION
      SELECT dst, src FROM interior_epsilon_edges
    ),
    -----------------------------------------------------------------
    -- Transitive closure over interior epsilon edges
    -----------------------------------------------------------------
    interior_epsilon_closure AS (
      SELECT
        vertex AS root,
        vertex AS reachable
      FROM
        interior_epsilon_vertices
      UNION
      SELECT
        interior_epsilon_closure.root AS root,
        undirected_edges.dst AS reachable
      FROM
        undirected_edges
          INNER JOIN interior_epsilon_closure
            ON (undirected_edges.src = interior_epsilon_closure.reachable)
    ),
    -----------------------------------------------------------------
    -- Distinct groups of interior epsilon closures
    -----------------------------------------------------------------
    regions AS (
      SELECT DISTINCT
        JSON_GROUP_ARRAY(reachable) OVER w AS json
      FROM
        interior_epsilon_closure
      WINDOW
        w AS (PARTITION BY root
              ORDER BY root, reachable
              ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING)
    ),
    -----------------------------------------------------------------
    -- Add numbers to regions
    -----------------------------------------------------------------
    numbered AS (
      SELECT
        ROW_NUMBER() OVER (ORDER BY json) AS id,
        json
      FROM
        regions
    ),
    -----------------------------------------------------------------
    -- Relate each vertex to its region
    -----------------------------------------------------------------
    vertex_region AS (
      SELECT
        each.value AS vertex,
        numbered.id AS region
      FROM
        numbered
          INNER JOIN json_each(numbered.json) each
    ),
    -----------------------------------------------------------------
    -- New vertices taking the place of old vertices
    -----------------------------------------------------------------
    vertex_map AS (
      SELECT
        CAST(args.base + region AS TEXT) AS vertex,
        vertex AS shadows
      FROM
        args
          INNER JOIN vertex_region
    ),
    -----------------------------------------------------------------
    -- Distinct new vertices
    -----------------------------------------------------------------
    new_vertices AS (
      SELECT DISTINCT vertex FROM vertex_map
    ),
    -----------------------------------------------------------------
    -- Edges not replaced here
    -----------------------------------------------------------------
    keep_edges AS (
      SELECT * FROM Edge
      EXCEPT
      SELECT * FROM interior_epsilon_edges
    ),
    -----------------------------------------------------------------
    -- Edges going into the subgraphs we are replacing
    -----------------------------------------------------------------
    new_edges_lhs AS (
      SELECT
        keep_edges.src AS src,
        vertex_map.vertex AS dst
      FROM
        keep_edges
          INNER JOIN vertex_map
            ON (vertex_map.shadows = keep_edges.dst)
    ),
    -----------------------------------------------------------------
    -- Edges coming out of the subgraphs we are replacing
    -----------------------------------------------------------------
    new_edges_rhs AS (
      SELECT
        vertex_map.vertex AS src,
        keep_edges.dst AS dst
      FROM
        keep_edges
          INNER JOIN vertex_map
            ON (vertex_map.shadows = keep_edges.src)
    ),
    -----------------------------------------------------------------
    -- New edges linking shadowed subgraphs back into the graph
    -----------------------------------------------------------------
    new_edges AS (
      SELECT * FROM (
        SELECT * FROM new_edges_lhs
        UNION
        SELECT * FROM new_edges_rhs
      )
      WHERE src <> dst
    ),
    -----------------------------------------------------------------
    -- JSONify
    -----------------------------------------------------------------
    json_new_edges AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(src, dst)) AS data
      FROM
        new_edges
      GROUP BY
        NULL
    ),
    json_obsolete_edges AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(src, dst)) AS data
      FROM
        interior_epsilon_edges
      GROUP BY
        NULL
    ),
    json_new_vertices AS (
      SELECT
        JSON_GROUP_ARRAY(vertex) AS data
      FROM
        new_vertices
      GROUP BY
        NULL
    ),
    json_new_shadowings AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(vertex, shadows)) AS data
      FROM
        vertex_map
      GROUP BY
        NULL
    ),
    json_regions AS (
      SELECT
        JSON_GROUP_ARRAY(JSON(json)) AS data
      FROM
        regions
      GROUP BY
        NULL
    )
    -----------------------------------------------------------------
    -- Group everything into a 1x1 JSON table
    -----------------------------------------------------------------
    SELECT
      JSON_GROUP_OBJECT(name, JSON(data)) AS obj
    FROM (
      SELECT 'regions' AS name, * FROM json_regions
      UNION ALL
      SELECT 'new_edges' AS name, * FROM json_new_edges
      UNION ALL
      SELECT 'new_shadowings' AS name, * FROM json_new_shadowings
      UNION ALL
      SELECT 'new_vertices' AS name, * FROM json_new_vertices
      UNION ALL
      SELECT 'obsolete_edges' AS name, * FROM json_obsolete_edges
    )
    GROUP BY
      NULL

  });

  if (!$data) {
    $g2->_log->debug('no epsilons to cover?');
    return;
  }

  my $decoded = $g2->_json->decode($data);

  my $subgraph = Graph::Feather->new(
    vertices => [map {
      $_->[1]
    } @{ $decoded->{new_shadowings} }],
    edges => $decoded->{obsolete_edges},
  );

  my ($d, @start_ids) = $automata->subgraph_automaton(
    $subgraph,
    @{ $decoded->{regions} }
  );

  my %state_to_vertex = $automata->_insert_dfa($d, @start_ids);

  $g2->_log->debug('end _cover_epsilons');
#  $g2->_dbh->sqlite_backup_to_file('cover_epsilons.after.sqlite');

}

sub _cover_root {
  my ($g2) = @_;

  my $subgraph = _shadowed_subgraph_between($g2,
    $g2->gp_start_vertex, $g2->gp_final_vertex);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph,
    [ $g2->gp_start_vertex ]);

  $d->{_dbh}->sqlite_backup_to_file('cover_root.sqlite');

  my %state_to_vertex = $automata->_insert_dfa($d, $start_id);
}

1;

__END__

