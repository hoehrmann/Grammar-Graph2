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

}

sub subgraph_automaton {
  my ($self, $subgraph, @start_vertices) = @_;

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
    $d->find_or_create_state_id( $_ )
  } @start_vertices;

  $self->_log->debugf("About to start computing transitions, start_ids %s", "@start_ids");

  while (my $count = $d->compute_some_transitions(2**17)) {
    $self->_log->debugf("Computed %u transitions", $count);
  }

  $self->_log->debugf("Done computing transitions");
  $d->_dbh->sqlite_backup_to_file('MATA-DFA.sqlite');

  return ($d, @start_ids);
}

sub _insert_dfa {
  my ($self, $d) = @_;

  my $guid = sprintf '%08x', int(rand( 2**31 ));

  $d->_dbh->sqlite_backup_to_file($guid . '.sqlite');

  $self->_log->debugf('Inserting DFA, guid %s', $guid);

  my ($base_id) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  $d->_dbh->do(q{
    DROP TABLE IF EXISTS TConfiguration;
  });
  $d->_dbh->do(q{
    CREATE TABLE TConfiguration AS
      SELECT * FROM Configuration ORDER BY vertex;
  });
  $d->_dbh->do(q{
    CREATE INDEX idx_tconfiguration_vertex ON TConfiguration(vertex);
  });

  my $tr_sth = $d->_dbh->prepare(q{
    SELECT
      (SELECT MAX(rowid) FROM state) * tr.src + tr.dst AS vertex,
      tr.src AS src_state,
      json_group_array(m.input) AS first_ords,
      json_group_array(m.vertex) AS vertices,
      tr.dst AS dst_state
    FROM
      Transition tr
        INNER JOIN TConfiguration src_cfg
          ON (tr.src = src_cfg.state)
        INNER JOIN TConfiguration dst_cfg
          ON (tr.dst = dst_cfg.state)
        INNER JOIN Edge e
          ON (e.src = src_cfg.vertex AND e.dst = dst_cfg.vertex)
        INNER JOIN Match m
          ON (m.input = tr.input AND m.vertex = src_cfg.vertex)
    GROUP BY
      tr.src,
--      m.vertex,
      tr.dst
  });

  $tr_sth->execute();

  my %cache;
  while (my $row = $tr_sth->fetchrow_arrayref) {
    my ($via, $src, $first_ords, $vertices, $dst) = @$row;

    $self->_log->debugf('#dfaTransition: %s', join ' ',
      $base_id + $via, $base_id + $src, $vertices, $base_id + $dst );

    $vertices = $self->_json->decode( $vertices );
    $first_ords = $self->_json->decode( $first_ords );

    $self->base_graph->g->add_edges(
      [ $base_id + $src, $base_id + $via ],
      [ $base_id + $via, $base_id + $dst ],
    );

    $self->base_graph->vp_type($base_id + $via, 'Input');
    $self->base_graph->vp_name($base_id + $via, "#dfaTransition:$guid");
    $self->base_graph->vp_shadow_group($base_id + $via, "$base_id");
    $self->base_graph->add_shadows($base_id + $via,
      @$vertices);

    my @run_lists = uniq(map {
      $self->alphabet->_ord_to_list()->{$_}
    } uniq( @$first_ords ));

    my $encoded = $self->_json->encode(\@run_lists);
    $cache{ $encoded } //= Set::IntSpan->new(@run_lists);
    my $combined = $cache{ $encoded };

    $self->base_graph->vp_run_list($base_id + $via, $combined);
  }

  my $st_sth = $d->_dbh->prepare(q{
    WITH base AS (
      SELECT
        c1.state AS state,
        json_group_array(c1.vertex) AS vertices
      FROM
        Configuration c1
          INNER JOIN Vertex vertex_p
            ON (c1.vertex = vertex_p.value
              AND vertex_p.is_nullable
              )
      GROUP BY
        c1.state
    )
    SELECT
      s.state_id,
      base.vertices
    FROM
      State s
        LEFT JOIN base
          ON (base.state = s.state_id)
  });

  $st_sth->execute();

  while (my $row = $st_sth->fetchrow_arrayref) {
    my ($state_id, $shadowed) = @$row;
    $shadowed //= '[]';
    $self->_log->debugf("creating dfa state %u vertex %u shadowing %s", $state_id, $base_id + $state_id, $shadowed);
    $self->base_graph->vp_type($base_id + $state_id, 'empty');
    $self->base_graph->vp_name($base_id + $state_id, "#dfaState:$state_id:$guid");
    $self->base_graph->vp_shadow_group($base_id + $state_id, "$base_id");

#die "TRYING TO SHADOW INPUT VERTEX" if grep { $self->base_graph->is_input_vertex($_) } @{ $self->_json->decode($shadowed) };

    $self->base_graph->add_shadows($base_id + $state_id,
        @{ $self->_json->decode($shadowed) });

    $self->base_graph->vp_shadows($base_id + $state_id, '[]')
      unless defined $self->base_graph->vp_shadows($base_id + $state_id);

  }

  my @unreachable = map { @$_ } $d->_dbh->selectall_array(q{
    SELECT
      value
    FROM
      Vertex
    WHERE
      1 OR Vertex.is_nullable
    EXCEPT
    SELECT
      vertex
    FROM
      TConfiguration
  });

  $self->_log->debugf("%s", Dump { unreachable => \@unreachable });

  $self->base_graph->add_shadows($base_id + $d->dead_state_id,
    @unreachable);

  my ($max_state) = $d->_dbh->selectrow_array(q{
    SELECT MAX(state_id) FROM State;
  });

  return map {
    $_ => $base_id + $_
  } 1 .. $max_state;
}

sub _shadow_subgraph_under_automaton {
  my ($self, $subgraph, $d, $start_vertex, $final_vertex, $start_id, $accepting) = @_;

  my %state_to_vertex = $self->_insert_dfa($d);

  my ($base_id) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  my $new_final_vertex = ++$base_id;

  $self->base_graph->vp_name($new_final_vertex, 'NEW_FINAL');

  $self->base_graph->g->add_edges(
    map { [ $state_to_vertex{$_}, $new_final_vertex ] } @$accepting
  );

  # FIXME: needs to add, not replace:
...;
  $self->base_graph
    ->vp_shadows($state_to_vertex{$start_id}, $start_vertex);
  $self->base_graph
    ->vp_shadows($new_final_vertex, $final_vertex);


  $self->base_graph->vp_shadowed_edges($new_final_vertex, '[]');

  $self->base_graph->add_shadowed_edges($new_final_vertex,
    $self->base_graph->g->edges_from($final_vertex),
  );

  $self->base_graph->add_shadowed_edges($state_to_vertex{$start_id},
    $self->base_graph->g->edges_to($start_vertex),
  );

}

1;

__END__
