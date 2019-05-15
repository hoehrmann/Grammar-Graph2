package Grammar::Graph2::Automata;
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
use Grammar::Graph2::DBUtils;
use Graph::SomeUtils qw/:all/;
use Algorithm::ConstructDFA2;
use Set::IntSpan;
use YAML::XS;
use Memoize;

has 'alphabet' => (
  is       => 'ro',
  writer   => '_set_alphabet'
);

has 'base_graph' => (
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

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

sub BUILD {
  my ($self) = @_;

  $self->_log->debug("Computing alphabet");
  $self->_set_alphabet(Grammar::Graph2::Alphabet->new(
    g => $self->base_graph
  ));

  $self->_log->debug("Creating views");
  local $self->base_graph
    ->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->base_graph->_dbh->do(q{
    DROP VIEW IF EXISTS view_vertex_shadows;
    CREATE VIEW view_vertex_shadows AS
    SELECT * FROM vertex_shadows;

    DROP TABLE IF EXISTS m_view_vertex_shadows;
    CREATE TABLE  m_view_vertex_shadows AS
    SELECT * FROM view_vertex_shadows LIMIT 0;
    CREATE UNIQUE INDEX idx_m_view_vertex_shadows
      ON m_view_vertex_shadows(vertex, shadows);
  });

}

sub subgraph_automaton {
  my ($self, $subgraph, @start_vertex_sets) = @_;

#  my $db_name = ':memory:';
  my $db_name = ':memory:';
  unlink $db_name;

  my $intspan_for_runlist = memoize(sub {
    return Set::IntSpan->new(@_)
  });

  my $run_list_contains_ord = memoize(sub {
    my ($run_list, $ord) = @_;
    return $intspan_for_runlist->($run_list)->member($ord);
  });

  my $vertex_run_list = memoize(sub {
    my ($vertex) = @_;
    return $self->base_graph->vp_run_list($vertex);
  });

  my $d = Algorithm::ConstructDFA2->new(

    input_alphabet  => [ $self->alphabet->first_ords ],
    input_vertices  => [ $subgraph->vertices ],
    input_edges     => [ $subgraph->edges ],

    vertex_nullable => sub {
      my ($v) = @_;
      # FIXME: prelude/postlude
      not $self->base_graph->is_input_vertex($v)
    },
    vertex_matches  => sub {
      my ($vertex, $input) = @_;

      return $run_list_contains_ord->(
        $vertex_run_list->($vertex), $input
      );
    },

    storage_dsn     => "dbi:SQLite:dbname=$db_name",
  );

  my @start_ids = map {
    $d->find_or_create_state_id( @$_ )
  } @start_vertex_sets;

  $self->_log->debugf("About to start computing transitions, start_ids %s", "@start_ids");

  while (my $count = $d->compute_some_transitions(2**17)) {
    $self->_log->debugf("Computed %u transitions", $count);
  }

  $self->_log->debugf("Done computing transitions");
  $d->_dbh->sqlite_backup_to_file('MATA-DFA.sqlite');

  return ($d, @start_ids);
}

sub _insert_dfa {
  my ($self, $d, @start_ids) = @_;

  my $guid = sprintf '%08x', int(rand( 2**31 ));

  $self->base_graph->_dbh->sqlite_backup_to_file(
    $guid . '-before.sqlite'
  );

  my ($base_id) = $self->base_graph->_dbh->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  my @args = (
    $base_id,
    $self->base_graph->gp_start_vertex,
    $self->base_graph->gp_final_vertex,
  );

  $self->_log->debug("new style transplantation");

  $d->{_dbh}->sqlite_create_function('fo2str', 1, sub {
    my ($list) = @_;
    my @ords = split/,/, $list;
    my @lists = map { $self->alphabet->_ord_to_list()->{$_} } @ords;
    my $span = Set::IntSpan->new(@lists);
    # $self->_log->debugf("%s turned into %s", "@lists", "$span");
    return $span->run_list;
  });

  my ($data) = $d->{_dbh}->selectrow_array(q{
    WITH

    -----------------------------------------------------------------
    -- NOTE: This query makes several assumptions:
    -- 
    --   * All edges in the automaton are reachable from the starts
    --   * The start vertices are never terminal vertices
    --   * There are no terminal->terminal edges
    --
    -- TODO: verify these assumptions
    -----------------------------------------------------------------

    -----------------------------------------------------------------
    -- Input arguments used throughout this CTE.
    -----------------------------------------------------------------
    args AS (
      SELECT
        CAST(? AS INT) AS base,
        CAST(? AS INT) AS start_vertex,
        CAST(? AS INT) AS final_vertex
    ),
    -----------------------------------------------------------------
    -- New vertices representing DFA states
    -----------------------------------------------------------------
    vertex_for_state AS (
      SELECT
        'empty' AS type,
        '#dfaState' AS name,
        NULL AS run_list,
        NULL AS shadow_group,
        JSON_GROUP_ARRAY(DISTINCT vertex) AS shadows,
        state AS state_id,
        NULL as trans_id,
        NULL AS src,
        NULL AS dst
      FROM
        Configuration
      GROUP BY
        state
    ),
    -----------------------------------------------------------------
    -- New vertices representing transitions
    -----------------------------------------------------------------
    vertex_for_trans AS (
      SELECT
        'Input' AS type,
        '#dfaTransition' AS name,
        fo2str(GROUP_CONCAT(DISTINCT tr.input)) AS run_list,
        NULL as shadow_group,
        JSON_GROUP_ARRAY(DISTINCT m.vertex) as shadows,
        NULL as state_id,
        MIN(tr.rowid) AS trans_id,
        src,
        dst
      FROM
        Transition tr
          INNER JOIN Configuration src_cfg
            ON (tr.src = src_cfg.state)
          INNER JOIN Match m
            ON (m.input = tr.input AND m.vertex = src_cfg.vertex)
      GROUP BY
        tr.src,
        tr.dst
    ),
    -----------------------------------------------------------------
    -- Unreachable vertices
    -----------------------------------------------------------------
    unreachable AS (
      SELECT
        value AS vertex
      FROM
        Vertex
      EXCEPT
      SELECT
        vertex
      FROM
        Configuration
    ),
    -----------------------------------------------------------------
    -- Vertex from dead state
    -----------------------------------------------------------------
    vertex_for_dead_state AS (
      SELECT
        'empty' AS type,
        '#dfaDead' AS name,
        NULL AS run_list,
        NULL AS shadow_group,
        JSON_GROUP_ARRAY(unreachable.vertex) AS shadows,
        state_id AS state_id,
        NULL as trans_id,
        NULL AS src,
        NULL AS dst
      FROM
        State
          LEFT JOIN unreachable
      WHERE
        State.state_id = 1
      GROUP BY
        State.state_id
    ),
    -----------------------------------------------------------------
    -- All new vertices combined
    -----------------------------------------------------------------
    new_vertices_numberless AS (
      SELECT * FROM vertex_for_state
      UNION
      SELECT * FROM vertex_for_trans
      UNION
      SELECT * FROM vertex_for_dead_state
    ),
    -----------------------------------------------------------------
    -- Add vertex id for each new vertex based on MAX(existing)
    -----------------------------------------------------------------
    new_vertices AS (
      SELECT
        row_number() OVER(ORDER BY state_id, trans_id) + args.base AS id,
        new_vertices_numberless.*
      FROM
        new_vertices_numberless
          INNER JOIN args
    ),
    -----------------------------------------------------------------
    -- Resolve `src` and `dst` with newly determined vertex numbers
    -----------------------------------------------------------------
    new_interior_triples AS (
      SELECT
        src_v.id AS src_id,
        vt.id AS via_id,
        dst_v.id AS dst_id
      FROM
        new_vertices vt
          INNER JOIN new_vertices src_v
            ON (src_v.state_id = vt.src)
          INNER JOIN new_vertices dst_v
            ON (dst_v.state_id = vt.dst)
    ),
    -----------------------------------------------------------------
    -- Convert transition triples to edges (vertex pairs)
    -----------------------------------------------------------------
    new_interior_edges AS (
      SELECT src_id AS src, via_id AS dst FROM new_interior_triples
      UNION
      SELECT via_id AS src, dst_id AS dst FROM new_interior_triples
    ),
    -----------------------------------------------------------------
    -- Unpack the `shadows` property for later insertion
    -----------------------------------------------------------------
    new_shadowings AS (
      SELECT
        new_vertices.id AS vertex,
        each.value AS shadows
      FROM
        new_vertices
          INNER JOIN JSON_EACH(new_vertices.shadows) each
          INNER JOIN args
      WHERE
        CAST(each.value AS TEXT) NOT IN (
          args.start_vertex, args.final_vertex
        )
    ),
    -----------------------------------------------------------------
    -- Edges covered by automata can be removed unless they are edges
    -- leaving the `start_vertex` or arriving at the `final_vertex`.
    -- 
    -- NOTE: this assumes the automata have been computed so that all
    -- edges can actually be reached from the start vertex sets.
    -----------------------------------------------------------------
    obsolete_edges AS (
      SELECT
        src,
        dst
      FROM
        Edge
          INNER JOIN args
      WHERE
        src <> args.start_vertex
        AND
        dst <> args.final_vertex
    ),
    -----------------------------------------------------------------
    -- JSON encoding
    -----------------------------------------------------------------
    json_obsolete_edges AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(src, dst)) AS data
      FROM
        obsolete_edges
      GROUP BY
        NULL
    ),
    json_new_shadowings AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(vertex, shadows)) AS data
      FROM
        new_shadowings
      GROUP BY
        NULL
    ),
    json_new_interior_edges AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(src, dst)) AS data
      FROM
        new_interior_edges
      GROUP BY
        NULL
    ),
    json_new_vertices AS (
      SELECT
        JSON_GROUP_ARRAY(JSON_ARRAY(
          id, type, name, run_list, shadow_group,
          JSON(shadows), state_id, trans_id, src, dst
        )) AS data
      FROM
        new_vertices
      GROUP BY
        NULL
    )
    -----------------------------------------------------------------
    -- Group everything into a 1x1 JSON table
    -----------------------------------------------------------------
    SELECT
      JSON_GROUP_OBJECT(name, JSON(data)) AS obj
    FROM (
      SELECT 'new_interior_edges' AS name, * FROM json_new_interior_edges
      UNION ALL
      SELECT 'new_shadowings' AS name, * FROM json_new_shadowings
      UNION ALL
      SELECT 'new_vertices' AS name, * FROM json_new_vertices
      UNION ALL
      SELECT 'obsolete_edges' AS name, * FROM json_obsolete_edges
    )
    GROUP BY
      NULL
  }, {}, @args);

  $self->_log->debug("new style transplantation done");

  unless ($data and length $data) {
    warn "!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
    return;
  }

  my $decoded = $self->_json->decode($data);

  do {
    open my $f, '>', $guid . '.json';
    print $f $data;
    close $f;
  };

#  return _insert_dfa_old($self, $d, @start_ids);

  $self->base_graph->g->add_vertices(map {
    $_->[0] . ''
  } @{ $decoded->{new_vertices} });

  $self->base_graph->_dbh->do(q{
    INSERT OR IGNORE INTO vertex_property(
      vertex,
      type,
      name,
      run_list
    )
    SELECT
      CAST(JSON_EXTRACT(each.value, '$[0]') AS TEXT) AS vertex,
      CAST(JSON_EXTRACT(each.value, '$[1]') AS TEXT) AS type,
      CAST(JSON_EXTRACT(each.value, '$[2]') AS TEXT) AS name,
      CAST(JSON_EXTRACT(each.value, '$[3]') AS TEXT) AS run_list
    FROM
      JSON_EACH(JSON_EXTRACT(?, '$.new_vertices')) each
  }, {}, $data);

  $self->base_graph->_dbh->do(q{
    INSERT OR IGNORE INTO vertex_shadows(vertex, shadows)
    SELECT
      CAST(JSON_EXTRACT(each.value, '$[0]') AS TEXT) AS vertex,
      CAST(JSON_EXTRACT(each.value, '$[1]') AS TEXT) AS shadows
    FROM
      JSON_EACH(JSON_EXTRACT(?, '$.new_shadowings')) each
    WHERE
      JSON_EXTRACT(each.value, '$[1]') IS NOT NULL
  }, {}, $data);

  # convert to strings and delete edges
  $self->base_graph->g->feather_delete_edges(
    map { [ map { $_ . '' } @$_ ] }
      @{ $decoded->{obsolete_edges} }
  );

  # ...

  $self->_log->debug("edge insertion");
  $self->base_graph->_dbh->do(q{
    INSERT OR IGNORE INTO Edge(src, dst)
    WITH
    lhs AS (
      SELECT
        Edge.src AS src,
        xxx.vertex AS dst
      FROM
        Edge
          INNER JOIN vertex_shadows xxx
            ON (Edge.dst = xxx.shadows)
          LEFT JOIN vertex_shadows yyy
            ON (Edge.src = yyy.shadows)
      WHERE
        yyy.vertex IS NULL
    ),
    rhs AS (
      SELECT
        xxx.vertex AS src,
        Edge.dst AS dst
      FROM
        Edge
          INNER JOIN vertex_shadows xxx
            ON (Edge.src = xxx.shadows)
          LEFT JOIN vertex_shadows yyy
            ON (Edge.dst = yyy.shadows)
      WHERE
        yyy.vertex IS NULL
    )
    SELECT * FROM lhs
    UNION
    SELECT * FROM rhs
  });
  $self->_log->debug("edge insertion done");

  # convert to strings and add interior edges
  $self->base_graph->g->add_edges(
    map { [ map { $_ . '' } @$_ ] }
      @{ $decoded->{new_interior_edges} }
  );

  $self->base_graph->_dbh->sqlite_backup_to_file(
    $guid . '-after.sqlite'
  );

  my %state_to_vertex = map {

    $_->[6], $_->[0] . ''

  } grep {

    defined $_->[6]

  } @{ $decoded->{new_vertices} };

  $self->_log->debugf('state_to_vertex: %s', Dump(\%state_to_vertex));

  return %state_to_vertex;

}

1;

__END__
