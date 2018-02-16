package Grammar::Graph2::TestParser;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use Grammar::Graph2::TestParser::MatchEnumerator;
use List::Util qw/min max/;

has 'input_path' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
);

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

has '_input_length' => (
  is       => 'rw',
  isa      => Int,
);

has '_dbh' => (
  is       => 'rw',
);

sub BUILD {
  my ($self) = @_;

  # FIXME(bh): stealing other module's dbh is bad
  $self->_dbh( $self->g->g->{dbh} );
}


# TODO: rename to compute_t or whatever
sub create_t {
  my ($self) = @_;

  $self->_create_vertex_property_table();

  $self->_recompute_stack_properties();

  $self->_file_to_table();
  $self->_create_grammar_input_cross_product();
  $self->_create_without_unreachable_vertices();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_collapsed_to_stack_vertices();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_trees_bottom_up();

  $self->_create_top_down_reachable();

  $self->_create_parent_child_signature();

  $self->_create_sibling_signature();
}

sub create_match_enumerator {
  my ($self) = @_;

  # FIXME: dbh passing, g
  return Grammar::Graph2::TestParser::MatchEnumerator->new(
    _dbh => $self->_dbh,
    g => undef,

    src_pos => 1,
    src_vertex => $self->g->gp_start_vertex(),
    dst_pos => $self->_input_length + 1,
    dst_vertex => $self->g->gp_final_vertex(),
  );
}

sub _file_to_ords {
  my ($input_path) = @_;

  open my $f, '<:utf8', $input_path;
  my $chars = do { local $/; binmode $f; <$f> };
  my @input = map { ord } split//, $chars;

  return @input;
}

sub _file_to_table {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_input
  });

  $self->_dbh->do(q{
    CREATE TABLE testparser_input(
      pos INTEGER PRIMARY KEY,
      ord INTEGER
    )
  });

  my $sth = $self->_dbh->prepare(q{
    INSERT INTO testparser_input(ord) VALUES (?)
  });

  my @ords = _file_to_ords($self->input_path);

  $self->_dbh->begin_work();
  $sth->execute($_) for @ords;
  $self->_dbh->commit();

  $self->_input_length( scalar @ords );
}

sub _create_grammar_input_cross_product {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_all_edges
  });

  $self->_dbh->do(q{
    CREATE TABLE testparser_all_edges AS

    WITH
    terminal_edges(src_pos, src_vertex, dst_pos, dst_vertex) AS (
      SELECT
        i.pos     AS src_pos,
        e.src     AS src_vertex,
        i.pos + 1 AS dst_pos,
        e.dst     AS dst_vertex
      FROM
        testparser_input i
          INNER JOIN vertex_span s
            ON (i.ord >= s.min AND i.ord <= s.max)
          INNER JOIN edge e
            ON (s.vertex = e.src)
    ),

    epsilon_edges(src_pos, src_vertex, dst_pos, dst_vertex) AS (
      SELECT
        i.pos     AS src_pos,
        e.src     AS src_vertex,
        i.pos     AS dst_pos,
        e.dst     AS dst_vertex
      FROM
        (SELECT * FROM testparser_input
         UNION ALL
         SELECT
           COALESCE(MAX(pos), 0) + 1 AS pos,
           -1 AS ord
         FROM
           testparser_input) i,
        edge e
      WHERE
        e.src IN (SELECT vertex
                  FROM vertex_attribute
                  WHERE attribute_name = 'type'
                    AND attribute_value NOT IN ('Input'))
    )

    SELECT * FROM terminal_edges
    UNION ALL
    SELECT * FROM epsilon_edges
    ORDER BY src_pos, src_vertex, dst_pos, dst_vertex
  });

  $self->_dbh->do(q{
    CREATE UNIQUE INDEX
      idx_uniq_testparser_all_edges
    ON testparser_all_edges(
      src_pos,
      src_vertex,
      dst_pos,
      dst_vertex
    )
  });
}

sub _create_without_unreachable_vertices {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS result
  });

  # FIXME(bh): rename result table

  $self->_dbh->do(q{
    CREATE TABLE result AS
    WITH RECURSIVE
    forward(src_pos, src_vertex, dst_pos, dst_vertex) AS (
      SELECT
        e.*
      FROM
        testparser_all_edges e
      WHERE
        1 = 1
        AND e.src_pos = CAST(1 AS INT)
        AND e.src_vertex = CAST(? AS TEXT)

      UNION 
      
      SELECT
        e.*
      FROM
        forward f
          INNER JOIN testparser_all_edges e
            ON (f.dst_pos = e.src_pos
              AND f.dst_vertex = e.src_vertex)
    ),

    backward(src_pos, src_vertex, dst_pos, dst_vertex) AS (
      SELECT
        e.*
      FROM
        testparser_all_edges e
      WHERE
        1 = 1
        AND e.dst_pos = CAST(? AS INT)
        AND e.dst_vertex = CAST(? AS TEXT)

      UNION
      
      SELECT
        f.*
      FROM
        backward b
          INNER JOIN forward f
            ON (b.src_pos = f.dst_pos
              AND b.src_vertex = f.dst_vertex)
    )

    SELECT
      *
    FROM
      backward
    ORDER BY
      src_pos,
      src_vertex,
      dst_pos,
      dst_vertex

  }, {}, $self->g->gp_start_vertex(),
         $self->_input_length + 1,
         $self->g->gp_final_vertex(),
  );
}

sub _create_collapsed_to_stack_vertices {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t
  });

  $self->_dbh->do(q{
    CREATE TABLE t(
      src_pos INT,
      src_vertex,
      mid_src_pos INT,
      mid_src_vertex,
      mid_dst_pos INT,
      mid_dst_vertex,
      dst_pos INT,
      dst_vertex,
      UNIQUE(
        src_pos,
        src_vertex,

        mid_src_pos,
        mid_src_vertex,
        mid_dst_pos,
        mid_dst_vertex,

        dst_pos,
        dst_vertex
      )
    )
  });

  $self->_dbh->do(q{
    CREATE INDEX idx_t_src ON t(src_pos, src_vertex)
  });

  $self->_dbh->do(q{
  INSERT INTO t
  WITH RECURSIVE planar(src_pos,
                        src_vertex,
                        mid_src_pos,
                        mid_src_vertex,
                        mid_dst_pos,
                        mid_dst_vertex,
                        dst_pos,
                        dst_vertex) AS (

    SELECT
      src_pos,
      src_vertex,
      NULL AS mid_src_pos,
      NULL AS mid_src_vertex,
      NULL AS mid_dst_pos,
      NULL AS mid_dst_vertex,
      dst_pos,
      dst_vertex
    FROM
      result

  UNION 

    SELECT
      left_.src_pos     AS src_pos,
      left_.src_vertex  AS src_vertex,
      left_.dst_pos     AS mid_src_pos,
      left_.dst_vertex  AS mid_src_vertex,
      NULL              AS mid_dst_pos,
      NULL              AS mid_dst_vertex,
      right_.dst_pos    AS dst_pos,
      right_.dst_vertex AS dst_vertex
    FROM
      result left_
        INNER JOIN planar right_
          ON (left_.dst_vertex = right_.src_vertex
            AND left_.dst_pos = right_.src_pos)
        INNER JOIN vertex_property mid_p
          ON (mid_p.vertex = left_.dst_vertex)
    WHERE
      mid_p.is_stack IS NULL
  )
  SELECT
    p.*
  FROM
    planar p
      INNER JOIN vertex_property src_p
        ON (src_p.vertex = p.src_vertex)
      INNER JOIN vertex_property dst_p
        ON (dst_p.vertex = p.dst_vertex)
      LEFT JOIN vertex_property mid_src_p
        ON (mid_src_p.vertex = p.mid_src_vertex)
  WHERE
    1 = 1
    AND (src_p.is_stack AND dst_p.is_stack)
    AND (
      COALESCE(NOT(src_p.is_push
        AND dst_p.is_pop
        AND src_p.partner <> dst_p.vertex), 1)
    )
  });
  
}

sub _create_trees_bottom_up {
  my ($self) = @_;

  my $max_rowid = 0;
  my $min_distance = 0;

  while (1) {

    my ($prev_max_rowid) = $self->_dbh->selectrow_array(q{
      SELECT MAX(rowid) FROM t
    });

    my $result = $self->_dbh->do(q{
      INSERT OR IGNORE INTO t
      SELECT
        left_.src_pos      AS src_pos,
        left_.src_vertex   AS src_vertex,
        left_.dst_pos      AS mid_src_pos,
        left_.dst_vertex   AS mid_src_vertex,
        right_.src_pos     AS mid_dst_pos,
        right_.src_vertex  AS mid_dst_vertex,
        right_.dst_pos     AS dst_pos,
        right_.dst_vertex  AS dst_vertex
      FROM
        t middle_
          INNER JOIN t left_
            ON (left_.dst_pos = middle_.src_pos
              AND left_.dst_vertex = middle_.src_vertex)
          INNER JOIN t right_
            ON (middle_.dst_pos = right_.src_pos
              AND middle_.dst_vertex = right_.src_vertex)

          INNER JOIN vertex_property src_p
            ON (src_p.vertex = left_.src_vertex)
          INNER JOIN vertex_property mid1_p
            ON (mid1_p.vertex = left_.dst_vertex)
          INNER JOIN vertex_property mid2_p
            ON (mid2_p.vertex = right_.src_vertex)
          INNER JOIN vertex_property dst_p
            ON (dst_p.vertex = right_.dst_vertex)

          LEFT JOIN t if1fi
            ON (src_p.type = "If" 
              AND src_p.p1 = if1fi.src_vertex
              AND left_.src_pos = if1fi.src_pos
              AND right_.dst_pos = if1fi.dst_pos
              /*AND left_p.p2fi = if1fi.dst_vertex*/)

          LEFT JOIN t if2fi
            ON (src_p.type = "If"
              AND src_p.p2 = if2fi.src_vertex
              AND left_.src_pos = if2fi.src_pos
              AND right_.dst_pos = if2fi.dst_pos
              /*AND left_p.p2fi = if2fi.dst_vertex*/)

          LEFT JOIN t pog -- parent of group
            ON (pog.dst_pos = left_.src_pos
              AND pog.dst_vertex = left_.src_vertex)

          LEFT JOIN vertex_property pog_p
            ON (pog_p.vertex = pog.src_vertex
              AND pog_p.is_push)

      WHERE
--          (right_.dst_pos - left_.src_pos >= CAST(? AS INT)) AND

        (
          (
            -- push1 pushX popY pop1
            mid2_p.is_pop
            AND mid1_p.is_push
--             AND mid1_p.partner = mid2_p.vertex 
            AND src_p.is_push
            AND src_p.partner = dst_p.vertex
          )
        OR
          (
            -- pushX popY pushM popN
            src_p.is_push
--            AND src_p.partner = mid1_p.vertex
            AND dst_p.is_pop
            AND mid1_p.is_pop
            AND mid2_p.is_push -- NEW NEW NEW
--            AND dst_p.partner = mid2_p.vertex
            AND pog_p.rowid IS NOT NULL
          )
        )
        

    AND (
      src_p.type <> 'If' OR 

      -- TODO: what if 'If' goes from start to end

      CASE src_p.name

      WHEN "#exclusion" THEN
        if1fi.rowid IS NOT NULL
        AND (right_.dst_pos - left_.src_pos) < CAST(? AS INT) -- OR: regular
        AND if2fi.rowid IS NULL

      WHEN "#ordered_choice" THEN
        middle_.src_vertex = src_p.p1
        OR (
          (right_.dst_pos - left_.src_pos) < CAST(? AS INT) -- OR: regular
          AND if1fi.rowid IS NULL
        )

      WHEN "#conjunction" THEN
        if1fi.rowid IS NOT NULL
        AND
        if2fi.rowid IS NOT NULL

      WHEN "#ordered_conjunction" THEN
        middle_.src_vertex = src_p.p1
        AND if1fi.rowid IS NOT NULL
        AND if2fi.rowid IS NOT NULL

      ELSE
        0

      END
    )


    }, {}, ($min_distance) x 4);

    # A Rule like "A but not B" requires proving that there is no
    # match for "B" for the rule as a whole to match. TODO: finish

    my ($new_min_distance) = $self->_dbh->selectrow_array(q{
      SELECT
        MIN(dst_pos - src_pos) AS min_distance
      FROM
        t
      WHERE
        t.rowid > ?
    }, {}, $max_rowid);

    if (not defined $new_min_distance) {

      ($new_min_distance) = $self->_dbh->selectrow_array(q{
        SELECT
          MIN(dst_pos - src_pos) AS min_distance
        FROM
          t
            INNER JOIN vertex_property src_p
              ON (src_p.vertex = t.src_vertex)
        WHERE
          src_p.type IN ("If", "If1", "If2")
          AND dst_pos - src_pos > CAST(? AS INT)
      }, {}, $min_distance);

#      warn "no distance past $min_distance" unless defined $new_min_distance;
    }

    if (not defined $new_min_distance) {
      $new_min_distance =
        max($min_distance + 1, $self->_input_length + 1)
    }

    my $old_min_distance = $min_distance;

    $min_distance = $new_min_distance;

    $max_rowid = $prev_max_rowid;

#    say "max_rowid $max_rowid result $result old_min_distance $old_min_distance new_min_distance $new_min_distance";

    last if $min_distance > $self->_input_length + 1;
  #  last if $result == 6;
  #  last if $result == 0;

  }
}


#####################################################################
# ...
#####################################################################

sub _create_top_down_reachable {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_top_down_reachable
  });

  $self->_dbh->do(q{
    CREATE VIEW view_top_down_reachable AS
    WITH RECURSIVE top_down_reachable(id) AS (
      SELECT
        t.rowid AS id
      FROM
        t
      WHERE
        src_pos = (SELECT MIN(rowid) FROM testparser_input)
        AND dst_pos = (SELECT 1 + MAX(rowid) FROM testparser_input)
        AND src_vertex = (SELECT attribute_value
                          FROM graph_attribute
                          WHERE attribute_name = 'start_vertex')
        AND dst_vertex = (SELECT attribute_value
                          FROM graph_attribute
                          WHERE attribute_name = 'final_vertex')

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
  
  });
}

sub _create_parent_child_signature {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_parent_child_signature
  });

  $self->_dbh->do(q{
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
        INNER JOIN vertex_property src_p
          ON (src_p.vertex = parent_child.src_vertex)
        INNER JOIN vertex_property mid1_p
          ON (mid1_p.vertex = parent_child.mid_src_vertex
            AND mid1_p.is_push)
        INNER JOIN vertex_property mid2_p
          ON (mid2_p.vertex = parent_child.mid_dst_vertex)
        INNER JOIN vertex_property dst_p
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
  });
}

sub _create_sibling_signature {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_sibling_signature
  });

  $self->_dbh->do(q{
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
        INNER JOIN vertex_property mid1_p
          ON (mid1_p.vertex = sibling.mid_src_vertex
            AND mid1_p.is_pop)
        INNER JOIN vertex_property mid2_p
          ON (mid2_p.vertex = sibling.mid_dst_vertex)

    ORDER BY
      lhs_final_pos ASC,
      lhs_final_name,
      rhs_start_pos DESC,
      rhs_start_name
  });
}

#####################################################################
# This stuff does not really belong here:
#####################################################################

sub _create_vertex_property_table {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_vertex_property
  });

  $self->_dbh->do(q{
    CREATE VIEW view_vertex_property AS
    WITH av AS (
      SELECT
        vertex,
        attribute_name AS an,
        attribute_value AS av
      FROM
        vertex_attribute
    )
    SELECT 
      vertex AS vertex,
      MAX(CASE WHEN an = 'type' THEN av END)    AS type,
      MAX(CASE WHEN an = 'name' THEN av END)    AS name,
      MAX(CASE WHEN an = 'p1' THEN av END)      AS p1,
      MAX(CASE WHEN an = 'p2' THEN av END)      AS p2,
      MAX(CASE WHEN an = 'partner' THEN av END) AS partner,
      MAX(CASE WHEN an = 'input' THEN av END)   AS input,
      MAX(
        CASE WHEN an = 'type' AND av IN ('Start',
          'Final', 'If', 'If1', 'If2', 'Fi', 'Fi1', 'Fi2') THEN 1 END
      ) AS is_stack,
      MAX(
        CASE WHEN an = 'type' AND av IN ('Start',
          'If', 'If1', 'If2') THEN 1 END
      ) AS is_push,
      MAX(
        CASE WHEN an = 'type' AND av IN ('Final',
          'Fi', 'Fi1', 'Fi2') THEN 1 END
      ) AS is_pop
          
    FROM
      av
    GROUP BY
      vertex
    ORDER BY
      vertex
  });

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS vertex_property
  });

  $self->_dbh->do(q{
    CREATE TABLE vertex_property AS
    SELECT * FROM view_vertex_property
  });

  $self->_dbh->do(q{
    CREATE UNIQUE INDEX
      idx_vertex_property_vertex
    ON vertex_property(vertex)
  });
}

sub _recompute_stack_properties {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_potential_stack_vertex
  });

  $self->_dbh->do(q{
    CREATE VIEW view_potential_stack_vertex AS
    WITH RECURSIVE all_successors_up_to_partner(root, v) AS (

      SELECT
        Edge.src AS root,
        Edge.dst AS v
      FROM
        Edge

      UNION

      SELECT
        r.root,
        Edge.dst
      FROM Edge
        INNER JOIN all_successors_up_to_partner AS r
          ON (Edge.src = r.v)
        INNER JOIN vertex_property AS src_p
          ON (Edge.src = src_p.vertex)
        INNER JOIN vertex_property AS dst_p
          ON (Edge.dst = dst_p.vertex)
        INNER JOIN vertex_property AS root_p
          ON (r.root = root_p.vertex)
      WHERE
        root_p.partner <> src_p.vertex
    )
    SELECT
      root AS vertex,
      v,
      vp.*
    FROM
      all_successors_up_to_partner r
        INNER JOIN vertex_property vp
          ON (vp.vertex = v)
    WHERE
      root = v AND vp.is_stack
  });

  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      is_push = NULL,
      is_pop = NULL,
      is_stack = NULL
    WHERE
      NOT EXISTS (SELECT 1
                  FROM view_potential_stack_vertex p
                  WHERE 1 OR p.vertex = vertex_property.vertex)
      AND
      NOT EXISTS (SELECT 1
                  FROM graph_attribute
                  WHERE
                    attribute_name IN ('start_vertex', 'final_vertex')
                    AND attribute_value = vertex_property.vertex)
      AND
      type NOT IN ('If', 'If1', 'If2', 'Fi', 'Fi1', 'Fi2')
  }) if 0;

  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      is_push = 1,
      is_pop = NULL,
      is_stack = 1
    WHERE
      vertex = ?
  }, {}, $self->g->gp_start_vertex) if 0;

  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      is_push = 0,
      is_pop = 1,
      is_stack = 1
    WHERE
      vertex = ?
  }, {}, $self->g->gp_final_vertex) if 0;


}



#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################



1;

__END__


/*
      WITH 
      edge_property(rowid, is_group) AS (
        SELECT
          t.rowid AS rowid,
          COALESCE(mid1_p.is_pop, 0) AS is_group
        FROM 
          t
            INNER JOIN vertex_property src_p
              ON (src_p.vertex = t.src_vertex)
            LEFT JOIN vertex_property mid1_p
              ON (mid1_p.vertex = t.mid_src_vertex)
            LEFT JOIN vertex_property mid2_p
              ON (mid2_p.vertex = t.mid_dst_vertex)
            INNER JOIN vertex_property dst_p
              ON (dst_p.vertex = t.dst_vertex)
      )
*/


/*
          INNER JOIN edge_property left_p
            ON (left_p.rowid = left_.rowid)
          INNER JOIN edge_property middle_p
            ON (middle_p.rowid = middle_.rowid)
          INNER JOIN edge_property right_p
            ON (right_p.rowid = right_.rowid)
*/

/*

        NOT(left_p.is_group AND right_p.is_group) AND
        NOT(left_p.is_group AND middle_p.is_group) AND
        NOT(middle_p.is_group AND right_p.is_group) AND
        NOT(right_p.is_group) AND

*/

