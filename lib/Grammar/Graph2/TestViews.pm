package Grammar::Graph2::TestViews;
use strict;
use warnings;
use 5.024000;
use Moo;
use Log::Any qw//;
use Types::Standard qw/:all/;
use List::Util qw/min max/;
use List::OrderBy;
use List::StackBy;

use Graph::Feather;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use Grammar::Graph2;
use Grammar::Graph2::TestParser::MatchEnumerator;
use Grammar::Graph2::Automata;
use Grammar::Graph2::Topology;

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

  # Testparser VIEWs
  $self->_dbh->do(q{
    -----------------------------------------------------------------
    -- view_sibling_signature
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_sibling_signature;
    CREATE VIEW view_sibling_signature AS 
    SELECT DISTINCT
      v_pc.id                   AS id,

      sibling.mid_src_pos       AS lhs_final_pos,
      mid1_p.name               AS lhs_final_name,
      sibling.mid_dst_pos       AS rhs_start_pos,
      mid2_p.name               AS rhs_start_name

    FROM
      view_top_down_reachable v_pc
        INNER JOIN t sibling
          ON (sibling.rowid = v_pc.id)
        INNER JOIN view_vp_plus mid1_p
          ON (mid1_p.vertex = sibling.mid_src_vertex
            AND mid1_p.is_pop)
        INNER JOIN view_vp_plus mid2_p
          ON (mid2_p.vertex = sibling.mid_dst_vertex)

    ORDER BY
      lhs_final_pos ASC,
      lhs_final_name,
      rhs_start_pos DESC,
      rhs_start_name
    ;

    -----------------------------------------------------------------
    -- view_parent_child_signature
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_parent_child_signature;
    CREATE VIEW view_parent_child_signature AS 
    SELECT DISTINCT
      v_pc.id                   AS id,

      parent_child.src_pos      AS parent_start_pos,
      src_p.name                AS parent_start_name,
      parent_child.mid_src_pos  AS first_child_pos,
      mid1_p.name               AS first_child_name,

      parent_child.mid_dst_pos  AS last_child_pos,
      mid2_p.name               AS last_child_name,
      parent_child.dst_pos      AS parent_final_pos,
      dst_p.name                AS parent_final_name

    FROM
      view_top_down_reachable v_pc
        INNER JOIN t parent_child
          ON (parent_child.rowid = v_pc.id)
        INNER JOIN view_vp_plus src_p
          ON (src_p.vertex = parent_child.src_vertex)
        INNER JOIN view_vp_plus mid1_p
          ON (mid1_p.vertex = parent_child.mid_src_vertex
            AND mid1_p.is_push)
        INNER JOIN view_vp_plus mid2_p
          ON (mid2_p.vertex = parent_child.mid_dst_vertex)
        INNER JOIN view_vp_plus dst_p
          ON (dst_p.vertex = parent_child.dst_vertex)

    UNION

    -- TODO(bh): this can probably be merged with the part above

    SELECT
      t.rowid                   AS id,

      t.src_pos                 AS parent_start_pos,
      src_p.name                AS parent_start_name,
      NULL                      AS first_child_pos,
      NULL                      AS first_child_name,

      NULL                      AS last_child_pos,
      NULL                      AS last_child_name,
      t.dst_pos                 AS parent_final_pos,
      dst_p.name                AS parent_final_name
    FROM
      -- TODO used to be t
      view_top_down_reachable v_pc
        INNER JOIN t 
          ON (t.rowid = v_pc.id)
        INNER JOIN vertex_property src_p
          ON (src_p.vertex = t.src_vertex)
        INNER JOIN vertex_property dst_p
          ON (dst_p.vertex = t.dst_vertex)
    WHERE
      t.mid_dst_pos IS NULL
      AND src_p.partner = dst_p.vertex

    ORDER BY
      parent_start_pos ASC,
      parent_final_pos DESC,
      first_child_pos ASC,
      last_child_pos DESC,
      parent_start_name,
      first_child_name,
      last_child_name
    ;

    -----------------------------------------------------------------
    -- view_parent_child_signature_normalised
    -----------------------------------------------------------------
/*
    DROP VIEW IF EXISTS view_parent_child_signature_normalised;
    CREATE VIEW view_parent_child_signature_normalised AS
    WITH RECURSIVE
    normalised AS (
      SELECT
        *
      FROM
        view_parent_child_signature
      UNION
      SELECT

-- When inner is #anonymous
--   return inner.inner



      FROM
        normalised
          LEFT JOIN t normalised_t
            ON (normalised_t.rowid = normalised.id)

    )
    SELECT
      *
    FROM 
      normalised
    WHERE
      COALESCE(parent_start_name, '') NOT LIKE '#%'
      AND
      COALESCE(first_child_name, '') NOT LIKE '#%'
      AND
      COALESCE(last_child_name, '') NOT LIKE '#%'
      AND
      COALESCE(parent_final_name, '') NOT LIKE '#%'
    ;
*/

    -----------------------------------------------------------------
    -- view_top_down_reachable
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_top_down_reachable;
    CREATE VIEW view_top_down_reachable AS
    WITH RECURSIVE top_down_reachable(id) AS (
      SELECT
        t.rowid AS id
      FROM
        t
      WHERE
        src_pos = (SELECT MIN(rowid) FROM testparser_input)
        AND dst_pos = (SELECT 1 + MAX(rowid) FROM testparser_input)
        AND src_vertex = (SELECT vertex FROM view_start_vertex)
        AND dst_vertex = (SELECT vertex FROM view_final_vertex)

      UNION

      SELECT
        t.rowid AS id
      FROM
        top_down_reachable
          INNER JOIN t p
            ON (p.rowid = top_down_reachable.id)
          INNER JOIN t 
            ON ((1=1 -- lhs
                AND p.src_pos = t.src_pos
                AND p.src_vertex = t.src_vertex
                AND p.mid_src_pos = t.dst_pos
                AND p.mid_src_vertex = t.dst_vertex)
              OR (1=1 -- rhs
                AND p.mid_dst_pos = t.src_pos
                AND p.mid_dst_vertex = t.src_vertex
                AND p.dst_pos = t.dst_pos
                AND p.dst_vertex = t.dst_vertex)
              OR (1=1 -- child
                AND p.mid_src_pos = t.src_pos
                AND p.mid_src_vertex = t.src_vertex
                AND p.mid_dst_pos = t.dst_pos
                AND p.mid_dst_vertex = t.dst_vertex))
    )
    SELECT
      *
    FROM
      top_down_reachable
    ;
  });


}

1;

__END__

