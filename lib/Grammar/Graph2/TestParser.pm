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
use CBOR::XS qw//;

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
  weak_ref => 1,
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
  weak_ref => 1,
);

sub BUILD {
  my ($self) = @_;

  # FIXME(bh): stealing other module's dbh is bad
  $self->_dbh( $self->g->g->{dbh} );

  local $self->g->g->{dbh}->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::TestViews->new( g => $self->g );
}

sub create_t_perlsql {
  my ($self) = @_;

  $self->_file_to_table();

  $self->_dbh->do(q{ ANALYZE });

#  $self->_create_grammar_input_cross_product();
  $self->_create_forward();

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_without_unreachable_vertices();

#=pod

# =pod

  $self->_dbh->do(q{
    DELETE FROM testparser_all_edges;
  });
  $self->_dbh->do(q{
    INSERT INTO testparser_all_edges SELECT * FROM result;
  });

# =cut

  # undoes _replace_conditionals
  $self->_update_shadowed_testparser_all_edges();

  $self->_create_without_unreachable_vertices();

  $self->_log->debugf("removed unreachable edges: %s",
    $self->g->_json->encode($self->_dbh->selectall_arrayref(q{
      SELECT * FROM testparser_all_edges
      EXCEPT
      SELECT * FROM result
    })));

#=cut

  $self->_dbh->do(q{ ANALYZE });

  $self->_create_collapsed_to_stack_vertices();

  $self->_create_trees_bottom_up();

  $self->_dbh->do(q{ ANALYZE });

  $self->_cleanup_ordered_choice();

}

sub create_t_cxx {
  my ($self) = @_;

  $self->_file_to_table();

  my $path = $self->input_path;

#  warn "cxx $path";
  unlink '/dev/shm/testparser.sqlite';
  `/home/bjoern/parselov/alx/alx --in=$path --all-edges --out-db=/dev/shm/testparser.sqlite`;
#  `cp /home/bjoern/parselov/cxx.cbor $path.cbor`;
#   open my $fh, '<', '/home/bjoern/parselov/cxx.cbor';
#   my $cbor = do { local $/; <$fh>; };
# 
#   my $json = JSON->new->encode(
#     CBOR::XS->new->decode($cbor)
#   );
# 

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;
  $self->_dbh->do(q{
    DROP TABLE IF EXISTS result;
    DROP TABLE IF EXISTS testparser_all_edges;
    DROP TABLE IF EXISTS testparser_all_edges_shadowed;
  });

  $self->_log->debugf('attaching alx db');
  $self->_dbh->do(q{
    ATTACH DATABASE ? AS alx;
  }, {}, '/dev/shm/testparser.sqlite');

  $self->_create_t_empty();

  $self->_dbh->do(q{
    INSERT OR IGNORE INTO t 
    SELECT
      src_node.pos AS src_pos,
      CAST(src_node.vertex AS TEXT) AS src_vertex,
      mid_src_node.pos AS mid_src_pos,
      CAST(mid_src_node.vertex AS TEXT) AS mid_src_vertex,
      mid_dst_node.pos AS mid_dst_pos,
      CAST(mid_dst_node.vertex AS TEXT) AS mid_dst_vertex,
      dst_node.pos AS dst_pos,
      CAST(dst_node.vertex AS TEXT) AS dst_vertex
    FROM
      alx.graph_quads q
        LEFT JOIN alx.graph_nodes src_node
          ON (q.src_id = src_node.node_id)
        LEFT JOIN alx.graph_nodes mid_src_node
          ON (q.mid_src_id = mid_src_node.node_id)
        LEFT JOIN alx.graph_nodes mid_dst_node
          ON (q.mid_dst_id = mid_dst_node.node_id)
        LEFT JOIN alx.graph_nodes dst_node
          ON (q.dst_id = dst_node.node_id)
  });

  $self->_dbh->do(q{
    CREATE TABLE result AS
    SELECT
      src_pos,
      CAST(src_vertex AS TEXT) AS src_vertex,
      dst_pos,
      CAST(dst_vertex AS TEXT) AS dst_vertex
    FROM
      alx.planar_edges
  });

  $self->_dbh->do(q{
    CREATE TABLE testparser_all_edges AS
    SELECT * FROM result;
    CREATE TABLE testparser_all_edges_shadowed AS
    SELECT * FROM result;

    DETACH DATABASE 'alx'
  });

  # edges to result
  # 

#   $self->_dbh->do(q{
#     CREATE TABLE result AS 
#     SELECT
#       json_extract(each.value, '$[0]') AS src_pos,
#       CAST(json_extract(each.value, '$[1]') AS TEXT) AS src_vertex,
#       json_extract(each.value, '$[2]') AS dst_pos,
#       CAST(json_extract(each.value, '$[3]') AS TEXT) AS dst_vertex
#     FROM
#       json_each(json_extract(?, '$.edges')) each
# /*
#     UNION
#     SELECT
#       1,
#       view_start_vertex.vertex,
#       1,
#       old_edge.dst
#     FROM
#       view_start_vertex
#         INNER JOIN old_edge
#           ON (old_edge.src = view_start_vertex.vertex)
# */
#     ;
#     CREATE TABLE testparser_all_edges AS
#     SELECT * FROM result;
#     CREATE TABLE testparser_all_edges_shadowed AS
#     SELECT * FROM result;
#   }, {}, $json);


#   $self->_dbh->do(q{
#     WITH base AS (
#       SELECT
#         json_extract(each.value, '$[0]') AS src_pos,
#         CAST(json_extract(each.value, '$[1]') AS TEXT) AS src_vertex,
# 
#         json_extract(each.value, '$[2]') AS mid_src_pos,
#         CAST(json_extract(each.value, '$[3]') AS TEXT) AS mid_src_vertex,
#         json_extract(each.value, '$[4]') AS mid_dst_pos,
#         CAST(json_extract(each.value, '$[5]') AS TEXT) AS mid_dst_vertex,
# 
#         json_extract(each.value, '$[6]') AS dst_pos,
#         CAST(json_extract(each.value, '$[7]') AS TEXT) AS dst_vertex
#       FROM
#         json_each(json_extract(?, '$.graph')) each
#       /* TODO: missing WHERE clause to prevent false start -> final_but_not_partner edges */
#     )
#     INSERT OR IGNORE INTO t
#     SELECT
#       src_pos,
#       src_vertex,
#       NULLIF(mid_src_pos, 0),
#       NULLIF(mid_src_vertex, '0'),
#       NULLIF(mid_dst_pos, 0),
#       NULLIF(mid_dst_vertex, '0'),
#       dst_pos,
#       dst_vertex
#     FROM
#       base
#   }, {}, $json);

#  $self->_dbh->sqlite_backup_to_file('BUG.sqlite');

}

# TODO: rename to compute_t or whatever
sub create_t {
  my ($self) = @_;

#  $self->create_t_perlsql();
  $self->create_t_cxx();

  warn "done with cxx";

#  $self->_dbh->sqlite_backup_to_file('WONDER.sqlite');

  $self->_dbh->do(q{ ANALYZE });

  return;

# OBSOLETE CODE FOLLOWS

  $self->_dbh->do(q{
    DELETE FROM t
    WHERE rowid NOT IN (SELECT id FROM view_top_down_reachable)
  });

  # The following two calls ensure that `result` includes only 
  # edges that are part of some valid match, by taking into 
  # account the work of `create_trees_bottom_up`.

  $self->_update_testparser_all_edges_cleanup();
  $self->_create_without_unreachable_vertices();
}

sub _update_testparser_all_edges_cleanup {
  my ($self) = @_;

  # FIXME: as-is incompatible with hiding non-recs
  # ^ ?

  $self->_dbh->do(q{
    WITH
    in_t AS (
      SELECT
        t.src_pos AS pos,
        t.src_vertex AS vertex
      FROM
        t
          INNER JOIN view_top_down_reachable
            ON (t.rowid = view_top_down_reachable.id)
      UNION
      SELECT
        t.dst_pos AS pos,
        t.dst_vertex AS vertex
      FROM
        t
          INNER JOIN view_top_down_reachable
            ON (t.rowid = view_top_down_reachable.id)
    ),
    bad_edge AS (
      SELECT
        testparser_all_edges.rowid AS id
      FROM
        testparser_all_edges
          INNER JOIN view_vp_plus src_p 
            ON (src_p.vertex = testparser_all_edges.src_vertex)
          INNER JOIN view_vp_plus dst_p 
            ON (dst_p.vertex = testparser_all_edges.dst_vertex)
      WHERE
        (
          NOT(src_p.skippable)
          AND
          NOT EXISTS (
            SELECT 1
            FROM in_t
            WHERE testparser_all_edges.src_pos = in_t.pos
              AND testparser_all_edges.src_vertex = in_t.vertex
          )
        )
        OR
        (
          NOT(dst_p.skippable)
          AND
          NOT EXISTS (
            SELECT 1
            FROM in_t
            WHERE testparser_all_edges.dst_pos = in_t.pos
              AND testparser_all_edges.dst_vertex = in_t.vertex
          )
        )
    )
    DELETE
    FROM
      testparser_all_edges
    WHERE
      testparser_all_edges.rowid IN (SELECT id FROM bad_edge)
  });

  # FIXME: bad workaround
  $self->_dbh->do(q{
    DELETE
    FROM
      testparser_all_edges
    WHERE
      testparser_all_edges.rowid IN (
        SELECT
          if2.rowid
        FROM
          testparser_all_edges if1
            INNER JOIN testparser_all_edges if2
              ON (if1.src_vertex = if2.src_vertex 
                AND if1.src_pos = if2.src_pos)
            INNER JOIN view_vp_plus src_p
              ON (src_p.vertex = if1.src_vertex
                AND src_p.type = 'If'
                AND src_p.skippable
                AND src_p.name = '#ordered_choice')
            INNER JOIN vertex_property if2_p
              ON (if2.dst_vertex = if2_p.vertex
                AND if2_p.type = 'If2')
            INNER JOIN vertex_property if1_p
              ON (if1.dst_vertex = if1_p.vertex
                AND if1_p.type = 'If1')
      )
  });

  # FIXME: bad workaround
  $self->_dbh->do(q{
    DELETE
    FROM
      testparser_all_edges
    WHERE
      testparser_all_edges.rowid IN (
        SELECT
          e.rowid
        FROM
          view_vp_plus if_p
            INNER JOIN vertex_property if1_p
              ON (if1_p.vertex = if_p.p1
                AND if_p.name = '#exclusion'
                AND if_p.type = 'If'
                AND if_p.skippable)
            INNER JOIN vertex_property if2_p
              ON (if2_p.vertex = if_p.p2)
            INNER JOIN testparser_all_edges e
              ON (e.src_vertex = if_p.vertex)
            LEFT JOIN testparser_all_edges eif1
              ON (eif1.src_pos = e.src_pos
                AND eif1.src_vertex = e.src_vertex
                AND eif1.dst_vertex = if1_p.vertex)
            LEFT JOIN testparser_all_edges eif2
              ON (eif2.src_pos = e.src_pos
                AND eif2.src_vertex = e.src_vertex
                AND eif2.dst_vertex = if2_p.vertex)
        WHERE
          eif2.rowid IS NOT NULL
      )
  });


}

sub create_match_enumerator {
  my ($self) = @_;

  # FIXME: dbh passing, g
  return Grammar::Graph2::TestParser::MatchEnumerator->new(
    _dbh => $self->_dbh,
    g => $self->g,

    src_pos => 1,
    src_vertex => $self->g->gp_start_vertex(),
    dst_pos => $self->_input_length + 1,
    dst_vertex => $self->g->gp_final_vertex(),
  );
}

sub create_tree_match_enumerator {
  my ($self) = @_;

  # FIXME: dbh passing, g
  return Grammar::Graph2::TestParser::TreeMatchEnumerator->new(
    _dbh => $self->_dbh,
    g => $self->g,

    src_pos => 1,
    src_vertex => $self->g->gp_start_vertex(),
    dst_pos => $self->_input_length + 1,
    dst_vertex => $self->g->gp_final_vertex(),
  );
}

sub _file_to_byte_ords {
  my ($input_path) = @_;

  open my $f, '<:raw', $input_path;
  my $chars = do { local $/; <$f> };
  my @input = map { ord } split//, $chars;

  return @input;
}

sub _file_to_ords {
  my ($input_path) = @_;

  open my $f, '<:utf8', $input_path;
  my $chars = do { local $/; <$f> };
  my @input = map { ord } split//, $chars;

  return @input;
}

sub _file_to_bytes_table {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  my @ords = _file_to_byte_ords($self->input_path);
  my $ix = 1;
  my @data = map { [$ix++, $_] } @ords;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_input_bytes;
    CREATE TABLE testparser_input_bytes(
      pos INTEGER PRIMARY KEY,
      ord INTEGER
    );
    INSERT INTO testparser_input_bytes(pos, ord)
    SELECT
      json_extract(each.value, '$[0]') AS pos,
      json_extract(each.value, '$[1]') AS ord
    FROM
      json_each(?) each
    ;
  }, {}, $self->g->_json->encode(\@data));

  return;

  die if $self->_dbh->selectrow_array(q{

    WITH RECURSIVE
    start_state AS (
      SELECT CAST(attribute_value AS INT) AS state
      FROM graph_attribute
      WHERE attribute_name = 'utf8_start_state'
    ),
    start_pos AS (
      SELECT 1 AS pos
    ),
    foo AS (
      SELECT
        0 AS is_char,
        0 AS char_pos,
        start_pos.pos AS byte_pos,
        start_state.state AS state
      FROM
        start_pos
          INNER JOIN start_state
      UNION
      SELECT
        dst_class.class IS NOT NULL AS is_char,
        CASE
        WHEN dst_class.class IS NOT NULL THEN foo.char_pos + 1
        ELSE foo.char_pos END AS char_pos,
        foo.byte_pos + 1 AS byte_pos,
        utf8_dfa.dst AS state
      FROM
        foo
          INNER JOIN utf8_dfa 
            ON (foo.state = utf8_dfa.src)
          INNER JOIN testparser_input_bytes i
            ON (i.pos = foo.byte_pos
              AND i.ord >= utf8_dfa.min
              AND i.ord <= utf8_dfa.max)
          LEFT JOIN input_class src_class
            ON (src_class.class = utf8_dfa.src)
          LEFT JOIN input_class dst_class
            ON (dst_class.class = utf8_dfa.dst)
    )
    SELECT
      1
    FROM
      testparser_input
        INNER JOIN input_class
          ON (testparser_input.ord >= input_class.min
            AND testparser_input.ord <= input_class.max)
        INNER JOIN foo
          ON (foo.is_char AND foo.char_pos = testparser_input.pos
            AND input_class.class = foo.state)
        LEFT JOIN testparser_input ref
          ON (ref.pos = testparser_input.pos
            AND ref.ord = testparser_input.ord)
    WHERE
      ref.pos IS NULL
    ;

  });
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

  my @ords = _file_to_ords($self->input_path);
  $self->_input_length( scalar @ords );

#  warn "input insert";
  $self->_dbh->do(q{
    INSERT INTO testparser_input(ord)
    SELECT each.value
    FROM json_each(?) each
  }, {}, $self->g->_json->encode(\@ords));
#  warn "input insert done";

#  $self->_file_to_bytes_table();

  return;

  my $sth = $self->_dbh->prepare(q{
    INSERT INTO testparser_input(ord) VALUES (?)
  });


  $self->_dbh->begin_work();
  $sth->execute($_) for @ords;
  $self->_dbh->commit();

  $self->_file_to_bytes_table();
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
        e.src = (SELECT vertex FROM view_start_vertex)
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

#return;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_all_edges_shadowed;
    CREATE TABLE testparser_all_edges_shadowed AS
    SELECT * FROM testparser_all_edges;
    DELETE FROM testparser_all_edges;
    DROP TABLE testparser_all_edges;

    CREATE TABLE testparser_all_edges AS 
    WITH RECURSIVE
    start_pos AS (
      SELECT MIN(pos) AS pos FROM testparser_input
    ),
    final_pos AS (
      SELECT 1 + MAX(pos) AS pos FROM testparser_input
    ),
    forward_reachable AS (
      SELECT
        start_pos.pos AS pos,
        view_start_vertex.vertex AS vertex
      FROM
        start_pos
          INNER JOIN view_start_vertex
      UNION
      SELECT
        dst_pos AS pos,
        dst_vertex AS vertex
      FROM
        testparser_all_edges_shadowed t_shadowed
      UNION
      SELECT
        forward_reachable.pos AS pos,
        vs.shadows AS vertex
      FROM 
        forward_reachable
          INNER JOIN vertex_shadows vs
            ON (vs.vertex = forward_reachable.vertex)
          INNER JOIN vertex_property shadows_p
            ON (vs.shadows = shadows_p.vertex)
          LEFT JOIN testparser_input i
            ON (i.pos = forward_reachable.pos)
          LEFT JOIN vertex_span s
            ON (s.vertex = vs.shadows
              AND i.ord >= s.min
              AND i.ord <= s.max)
      WHERE

        -- Grammar::Graph2::Automata, when creating vertices
        -- representing DFA transitions, groups transitions sharing
        -- the same source and destination state, in order to save
        -- some space. That may group mutually exclusive Input
        -- vertices under one vertex. Those that do not actually
        -- match need to be filtered. See comments there.

        shadows_p.type <> 'Input' OR s.vertex IS NOT NULL
    ),
    backward_edge AS (
      SELECT
        final_pos.pos AS src_pos,
        old_edge.src AS src_vertex,
        final_pos.pos AS dst_pos,
        view_final_vertex.vertex AS dst_vertex
      FROM
        view_final_vertex
          INNER JOIN final_pos
          INNER JOIN forward_reachable
            ON (forward_reachable.pos = final_pos.pos
              AND view_final_vertex.vertex = forward_reachable.vertex)
          INNER JOIN old_edge
            ON (old_edge.dst = view_final_vertex.vertex)
      UNION
      SELECT
        backward_edge.src_pos - (old_edge_src_p.type = 'Input')
          AS src_pos,
        old_edge.src AS src_vertex,
        backward_edge.src_pos AS dst_pos,
        backward_edge.src_vertex AS dst_vertex
      FROM
        backward_edge
          INNER JOIN old_edge
            ON (backward_edge.src_vertex = old_edge.dst)
          INNER JOIN vertex_property old_edge_dst_p
            ON (old_edge_dst_p.vertex = old_edge.dst)
          INNER JOIN vertex_property old_edge_src_p
            ON (old_edge_src_p.vertex = old_edge.src)
          INNER JOIN forward_reachable
            ON (forward_reachable.vertex = old_edge.src
              AND forward_reachable.pos = backward_edge.src_pos
                -(old_edge_src_p.type = 'Input'))
    )
    SELECT * FROM backward_edge
    ;
  });

}

sub _create_forward {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS testparser_all_edges
  });

  $self->_dbh->do(q{
    CREATE TABLE testparser_all_edges AS

    WITH RECURSIVE
    start_pos AS (
      SELECT MIN(pos) AS pos FROM testparser_input
    ),
    final_pos AS (
      SELECT MAX(pos) AS pos FROM testparser_input
    ),
    base AS (
      SELECT
        Edge.*
      FROM
        Edge
          INNER JOIN view_start_vertex start_vertex
            ON (Edge.src = start_vertex.vertex)
/*
      UNION 
      SELECT
        n.*
      FROM
        Edge
          INNER JOIN view_start_vertex start_vertex
          INNER JOIN Edge n
            ON (Edge.src = start_vertex.vertex AND Edge.dst = n.src)
      UNION
      SELECT
        Edge.*
      FROM
        Edge
          INNER JOIN view_final_vertex final_vertex
            ON (Edge.dst = final_vertex.vertex)
      UNION 
      SELECT
        n.*
      FROM
        Edge
          INNER JOIN view_final_vertex final_vertex
          INNER JOIN Edge n
            ON (Edge.dst = final_vertex.vertex AND Edge.src = n.dst)
*/        
    ),
    fwd AS (
      SELECT
        start_pos.pos AS src_pos,
        base.src AS src_vertex,
        start_pos.pos AS dst_pos,
        base.dst AS dst_vertex
      FROM
        base
          INNER JOIN start_pos
      UNION
      SELECT
        fwd.dst_pos AS src_pos,
        fwd.dst_vertex AS src_vertex,
        CASE
        WHEN src_p.type <> 'Input' THEN fwd.dst_pos
        ELSE fwd.dst_pos + 1
        END AS dst_pos,
        edge.dst AS dst_vertex
      FROM
        fwd
          INNER JOIN vertex_property src_p
            ON (src_p.vertex = fwd.dst_vertex)
          INNER JOIN Edge 
            ON (Edge.src = fwd.dst_vertex)
          INNER JOIN vertex_property dst_p
            ON (dst_p.vertex = edge.dst)
          LEFT JOIN testparser_input i
            ON (
              (src_p.type <> 'Input' AND i.pos = fwd.dst_pos)
              OR
              (src_p.type = 'Input' AND i.pos = fwd.dst_pos + 1)
              ) 
          LEFT JOIN vertex_span s
            ON (i.ord >= s.min AND i.ord <= s.max
              AND s.vertex = edge.dst)
      WHERE
        dst_p.type <> 'Input' OR s.vertex is not null
        
    )
    SELECT
      *
    FROM
      fwd
    ORDER BY
      src_pos
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
        AND e.src_vertex = (SELECT vertex FROM view_start_vertex)

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
        AND e.dst_vertex = (SELECT vertex FROM view_final_vertex)

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

sub _create_t_empty {
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

}

sub _create_collapsed_to_stack_vertices {
  my ($self) = @_;

  $self->_create_t_empty();

  # FIXME: convert to view

  $self->_dbh->do(q{
  WITH
  skippable AS (
    SELECT
      vertex_p.vertex AS vertex
    FROM
      view_vp_plus vertex_p
    WHERE
--      not(vertex_p.is_stack)
      vertex_p.skippable
    EXCEPT SELECT vertex FROM view_start_vertex
    EXCEPT SELECT vertex FROM view_final_vertex
  )
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
        INNER JOIN view_vp_plus mid_p
          ON (mid_p.vertex = left_.dst_vertex)
    WHERE
      mid_p.vertex IN (SELECT vertex FROM skippable)
  )
  SELECT
    p.*
  FROM
    planar p
      INNER JOIN view_vp_plus src_p
        ON (src_p.vertex = p.src_vertex)
      INNER JOIN view_vp_plus dst_p
        ON (dst_p.vertex = p.dst_vertex)
      LEFT JOIN view_vp_plus mid_src_p
        ON (mid_src_p.vertex = p.mid_src_vertex)
  WHERE
    1 = 1
    AND src_p.vertex NOT IN (SELECT vertex FROM skippable)
    AND dst_p.vertex NOT IN (SELECT vertex FROM skippable)
    AND (
      NOT(src_p.is_push
        AND dst_p.is_pop
        AND src_p.partner <> dst_p.vertex)
    )
  });

  $self->_dbh->do(q{
    UPDATE t
    SET mid_src_pos = NULL, mid_src_vertex = NULL
    WHERE mid_dst_pos IS NULL
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

          INNER JOIN view_vp_plus src_p
            ON (src_p.vertex = left_.src_vertex)
          INNER JOIN view_vp_plus mid1_p
            ON (mid1_p.vertex = left_.dst_vertex)
          INNER JOIN view_vp_plus mid2_p
            ON (mid2_p.vertex = right_.src_vertex)
          INNER JOIN view_vp_plus dst_p
            ON (dst_p.vertex = right_.dst_vertex)

          LEFT JOIN t if1fi
            ON (src_p.type = "If" 
              AND src_p.p1 = if1fi.src_vertex
              AND left_.src_pos = if1fi.src_pos
              AND right_.dst_pos = if1fi.dst_pos
                    --  AND left_p.p2fi = if1fi.dst_vertex
--                        AND src_p.p2 = if1fi.dst_vertex
              )

          LEFT JOIN t if2fi
            ON (src_p.type = "If"
              AND src_p.p2 = if2fi.src_vertex
              AND left_.src_pos = if2fi.src_pos
              AND right_.dst_pos = if2fi.dst_pos
                    --  AND left_p.p2fi = if2fi.dst_vertex
--                        AND src_p.p2 = if2fi.dst_vertex
              )

          LEFT JOIN t pog -- parent of group
            ON (pog.dst_pos = left_.src_pos
              AND pog.dst_vertex = left_.src_vertex)

          LEFT JOIN view_vp_plus pog_p
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
            AND pog_p.vertex IS NOT NULL
          )
        )
        

    AND (
      src_p.type <> 'If'
      OR 
      NOT(mid1_p.is_push)
      OR

      -- TODO: what if 'If' goes from start to end

      CASE src_p.name

      WHEN "#exclusion" THEN
        if1fi.rowid IS NOT NULL
        AND
        (right_.dst_pos - left_.src_pos) < CAST(? AS INT) -- OR: regular
        AND
        if2fi.rowid IS NULL

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

# warn join "\t", "min_distance", $min_distance, "time", time;

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
      # @@@
      $new_min_distance = $min_distance + 1;
    }

=pod

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

=cut

    my $old_min_distance = $min_distance;

    $min_distance = $new_min_distance;

    $max_rowid = $prev_max_rowid;

    my ($new_max_rowid) = $self->_dbh->selectrow_array(q{
      SELECT MAX(rowid) FROM t
    });

    warn join "\t", "prev_max_rowid", $prev_max_rowid, "new_max_rowid", $new_max_rowid, "\n";

#    say "max_rowid $max_rowid result $result old_min_distance $old_min_distance new_min_distance $new_min_distance";

    last if $min_distance > $self->_input_length + 1;
  #  last if $result == 6;
  #  last if $result == 0;

  }

}

sub _cleanup_ordered_choice {
  my ($self) = @_;

  my $affected1 = $self->_dbh->do(q{
    WITH 
    failed AS (
      SELECT
        t.mid_src_pos AS pos,
        t.mid_src_vertex AS vertex
      FROM
        t
          INNER JOIN vertex_property src_p
            ON (src_p.vertex = t.src_vertex)
          INNER JOIN vertex_property mid_src_p
            ON (mid_src_p.vertex = t.mid_src_vertex)
      WHERE
        src_p.type = 'If'
        AND
        src_p.name = '#ordered_choice'
        AND
        mid_src_p.vertex = src_p.p2
        AND
        t.dst_vertex = src_p.partner
        AND
        EXISTS (
          SELECT 1
          FROM t inner_t
          WHERE inner_t.src_pos = t.src_pos
            AND inner_t.src_vertex = t.src_vertex
            AND inner_t.mid_src_vertex = src_p.p1
            -- 
            AND inner_t.dst_pos = t.dst_pos
        )
    )
    DELETE
    FROM 
      testparser_all_edges
    WHERE 
      EXISTS (
        SELECT 1
        FROM failed 
        WHERE 
          testparser_all_edges.src_pos = failed.pos
          AND
          testparser_all_edges.src_vertex = failed.vertex
      )
  });

  $self->_log->debugf("cleanup affected %u", $affected1);

  return unless $affected1 > 0;

  # Steps below probably no longer necessary for perl/sql

  $self->_create_without_unreachable_vertices();

# return; # @@@

  $self->_dbh->do(q{
    WITH
    planar_vertices AS (
      SELECT 
        rowid AS id,
        src_pos AS pos,
        src_vertex AS vertex
      FROM
        result
      UNION
      SELECT 
        rowid AS id,
        dst_pos AS pos,
        dst_vertex AS vertex
      FROM
        result
    ),
    t_vertices AS (
      SELECT
        rowid AS id,
        src_pos AS pos,
        src_vertex AS vertex
      FROM
        t
      UNION
      SELECT
        rowid AS id,
        mid_src_pos AS pos,
        mid_src_vertex AS vertex
      FROM
        t
      WHERE
        mid_dst_vertex IS NOT NULL
      UNION
      SELECT
        rowid AS id,
        mid_dst_pos AS pos,
        mid_dst_vertex AS vertex
      FROM
        t
      UNION
      SELECT
        rowid AS id,
        dst_pos AS pos,
        dst_vertex AS vertex
      FROM
        t
    ),
    t_filtered AS (
      SELECT
        *
      FROM
        t_vertices
      WHERE
        vertex IS NOT NULL
    )
    DELETE
    FROM
      t
    WHERE
      t.rowid IN (
        SELECT
          id
        FROM
          t_filtered
        WHERE
          NOT EXISTS (
            SELECT 1
            FROM planar_vertices p
            WHERE
              p.pos = t_filtered.pos
              AND
              p.vertex = t_filtered.vertex
          )
      )
    
  });

}

1;

__END__


delete from t
where src_vertex type is if and name is ordered_choice
  and mid_src_vertex is if2
where 
  exists 



sqlite> select t.rowid, t.*, src_p.topo, mid_src_p.topo, mid_dst_p.topo, dst_p.topo from t inner join vertex_property src_p on (src_p.vertex = t.src_vertex) inner join vertex_property dst_p on (dst_p.vertex = t.dst_vertex) left join vertex_property mid_src_p on (mid_src_p.vertex = t.mid_src_vertex) left join vertex_property mid_dst_p on (mid_dst_p.vertex = t.mid_dst_vertex);

