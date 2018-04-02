package Grammar::Graph2::TestParser;
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
use Grammar::Graph2::TestViews;

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

  local $self->g->g->{dbh}->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::TestViews->new( g => $self->g );
}

# TODO: rename to compute_t or whatever
sub create_t {
  my ($self) = @_;

  $self->_file_to_table();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_grammar_input_cross_product();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_without_unreachable_vertices();

  $self->_dbh->do(q{
    DELETE FROM testparser_all_edges;
  });
  $self->_dbh->do(q{
    INSERT INTO testparser_all_edges SELECT * FROM result;
  });

  # undoes _replace_conditionals
  $self->_update_shadowed_testparser_all_edges();
  $self->_create_without_unreachable_vertices();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_collapsed_to_stack_vertices();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_trees_bottom_up();

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

sub _create_grammar_input_cross_product_idea {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_all_edges
  });

  $self->_dbh->do(q{
    CREATE TABLE testparser_all_edges AS

    WITH RECURSIVE
    foo(src_pos, src_vertex, dst_pos, dst_vertex) AS (
      SELECT 
        (SELECT 0 + MIN(rowid) FROM testparser_input) AS src_pos,
        e.src,
        (SELECT 0 + MIN(rowid) FROM testparser_input) AS dst_pos,
        e.dst AS dst_vertex
      FROM
        Edge e
      WHERE
        e.src = (SELECT attribute_value
                 FROM graph_attribute
                 WHERE attribute_name = 'start_vertex')
      UNION
      SELECT
        foo.dst_pos AS src_pos,
--        foo.dst_vertex AS src_vertex,
        each.value AS src_vertex,
        CASE WHEN src_p.type <> 'Input' THEN dst_pos ELSE dst_pos + 1 END AS dst_pos,
        e.dst AS dst_vertex
      FROM
        Edge e
          INNER JOIN foo
            ON (e.src = foo.dst_vertex)
          INNER JOIN vertex_property src_p
            ON (e.src = src_p.vertex)
          INNER JOIN
            json_each(src_p.epsilon_group) each
          INNER JOIN (SELECT * FROM testparser_input
                      UNION ALL
                      SELECT
                        COALESCE(MAX(pos), 0) + 1 AS pos,
                        -1 AS ord
                      FROM
                        testparser_input) i
            ON (i.pos = foo.dst_pos)
          LEFT JOIN vertex_span s
            ON (i.ord >= s.min AND i.ord <= s.max)
      WHERE
        src_p.type <> 'Input' OR s.vertex = e.src
    )
    SELECT * FROM foo ORDER BY src_pos, src_vertex, dst_pos, dst_vertex
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

  $self->_dbh->do(q{
    ANALYZE testparser_all_edges
  });

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
                  FROM vertex_property
                  WHERE type NOT IN ('Input'))
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

sub _update_shadowed_testparser_all_edges {
  my ($self) = @_;

# return;

  $self->_dbh->do(q{
    CREATE TABLE vertex_shadows_or_self AS 
      SELECT 
        vertex_p.vertex AS vertex,
        CAST(each.value AS TEXT) AS shadows
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
      UNION
      SELECT 
        vertex_p.vertex AS vertex,
        vertex_p.vertex AS shadows
      FROM
        vertex_property vertex_p
  });

  $self->_dbh->do(q{
    CREATE UNIQUE INDEX idx_vertex_shadows_or_self
      ON vertex_shadows_or_self(vertex, shadows)
  });

  $self->_dbh->do(q{
    ANALYZE vertex_shadows_or_self;
  });


  $self->_dbh->do(q{
    ANALYZE testparser_all_edges;
  }) if 1;
  $self->_dbh->do(q{
    ANALYZE old_edge;
  }) if 1;
  $self->_dbh->do(q{
    CREATE UNIQUE INDEX IF NOT EXISTS idx_old_edge ON old_edge(src,dst);
  }) if 1;


  $self->_dbh->do(q{
    WITH RECURSIVE
    to_insert AS (
      SELECT * FROM testparser_all_edges
      UNION
      SELECT src_pos, src_vertex, src_pos, src_vertex FROM testparser_all_edges INNER JOIN vertex_property ON (vertex_property.vertex = testparser_all_edges.src_vertex AND vertex_property.type <> 'InputXXX')
/*
      UNION
      SELECT dst_pos, dst_vertex, dst_pos, dst_vertex FROM testparser_all_edges
*/
      UNION
      SELECT
        a.src_pos AS src_pos,
        src_shadow.shadows AS src_vertex,
        a.dst_pos AS dst_pos,
        old_edge.dst AS dst_vertex
      FROM
        to_insert a
          LEFT JOIN vertex_shadows_or_self src_shadow
            ON (src_shadow.vertex = a.src_vertex)

          LEFT JOIN old_edge
            ON (src_shadow.shadows = old_edge.src)
/*
          LEFT JOIN vertex_shadows_or_self dst_shadow
            ON (dst_shadow.vertex = a.dst_vertex)
*/
    )
/*
    SELECT * FROM to_insert WHERE src_pos = 3 AND src_vertex = '416' --AND dst_pos = 3 
*/
    INSERT OR IGNORE INTO testparser_all_edges(src_pos,
      src_vertex, dst_pos, dst_vertex)
    SELECT
      new.*
    FROM
      to_insert new
        INNER JOIN old_edge o
          ON (new.src_vertex = o.src AND new.dst_vertex = o.dst)
  });

  $self->_dbh->do(q{
    DELETE FROM testparser_all_edges
    WHERE
      src_pos = dst_pos AND EXISTS (SELECT 1 FROM vertex_property WHERE vertex = testparser_all_edges.src_vertex AND type = 'Input')
  }) if 1;

  $self->_dbh->do(q{
    DELETE FROM testparser_all_edges
    WHERE
      NOT EXISTS (SELECT 1
                  FROM old_edge o
                  WHERE o.src = testparser_all_edges.src_vertex
                    AND o.dst = testparser_all_edges.dst_vertex)
  }) if 1;

  $self->_dbh->do(q{
    WITH good_rowids AS (
      SELECT
        all_edges.rowid
      FROM
        old_edge o
          INNER JOIN testparser_all_edges all_edges
            ON (all_edges.src_vertex = o.src
              AND all_edges.dst_vertex = o.dst)
    )
    DELETE FROM testparser_all_edges
    WHERE
      rowid NOT IN (SELECT * FROM good_rowids)
  }) if 0;

  $self->_dbh->do(q{
    DELETE FROM testparser_all_edges
    WHERE
      src_vertex NOT IN (
        SELECT
          vertex
        FROM
          vertex_property vertex_p
        WHERE
          type <> 'Input'
        UNION ALL
        SELECT
          s.vertex
        FROM
          testparser_input i
            INNER JOIN vertex_span s
              ON (i.pos = testparser_all_edges.src_pos AND i.ord >= s.min AND i.ord <= s.max)

      )
  }) if 0;

  $self->_dbh->do(q{
    DROP TABLE vertex_shadows_or_self
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
        AND e.src_pos = (SELECT MIN(rowid) FROM testparser_input)
        AND e.src_vertex = (SELECT attribute_value
                            FROM graph_attribute
                            WHERE attribute_name = 'start_vertex')

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
        AND e.dst_pos = (SELECT 1 + MAX(rowid) FROM testparser_input)
        AND e.dst_vertex = (SELECT attribute_value
                            FROM graph_attribute
                            WHERE attribute_name = 'final_vertex')

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
      backward -- @@@@@
    ORDER BY
      src_pos,
      src_vertex,
      dst_pos,
      dst_vertex

  });

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

  # FIXME: convert to view

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
      NOT(COALESCE(mid_p.is_stack, 0))
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
    AND COALESCE(src_p.is_stack, 0)
    AND COALESCE(dst_p.is_stack, 0)
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

#warn join "\t", "min_distance", $min_distance;

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

    my @debug = $self->_dbh->selectall_array(q{
      SELECT
        *, dst_pos - src_pos
      FROM
        t
      WHERE
        t.rowid > ?
    }, {}, $max_rowid);

#    say join "\t", "min_distance", $min_distance, "max_rowid", $max_rowid, map { $_ // '' } @$_ for @debug;

    if (not defined $new_min_distance) {
      # @@@
      $new_min_distance = $min_distance + 1;
    }

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

1;

__END__
