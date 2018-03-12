package Grammar::Graph2::Automata2;
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
  my ($self, $subgraph, $start_vertex) = @_;

  # TODO: allow multiple start vertices

#  my $db_name = ':memory:';
  my $db_name = 'MATA-DFA.sqlite';
  unlink $db_name;

  my $intspan_for_runlist = memoize(sub {
    return Set::IntSpan->new(@_)
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

      return $intspan_for_runlist->(
        $self->base_graph->vp_run_list($vertex)
      )->member($input);
    },

    storage_dsn     => "dbi:SQLite:dbname=$db_name",
  );

  my $start_id = $d->find_or_create_state_id( $start_vertex );

  while (my $count = $d->compute_some_transitions(2**17)) {
    $self->_log->debugf("Computed %u transitions", $count);
  }

  $self->_log->debugf("Done computing transitions");

  return ($d, $start_id);
}

sub _shadow_subgraph_under_automaton {
  my ($self, $subgraph, $d, $start_vertex, $final_vertex, $start_id, $accepting) = @_;

  my ($base_id) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  my $final_id = ++$base_id;

  $self->base_graph->vp_name($final_id, 'NEW_FINAL');

  my $tr_sth = $d->_dbh->prepare(q{
    SELECT
      (SELECT MAX(rowid) FROM state) + MIN(tr.rowid) AS vertex,
      tr.src AS src_state,
      json_group_array(tr.input) as first_ords,
      tr.dst AS dst_state,
      json_group_array(json_array(
        CAST(e.src AS TEXT),
        CAST(e.dst AS TEXT)
      )) AS shadow_edges
    FROM
      Transition tr
        INNER JOIN Configuration src_cfg
          ON (tr.src = src_cfg.state)
        INNER JOIN Configuration dst_cfg
          ON (tr.dst = dst_cfg.state)
        INNER JOIN Edge e
          ON (e.src = src_cfg.vertex AND e.dst = dst_cfg.vertex)
        INNER JOIN Match m
          ON (m.input = tr.input AND m.vertex = src_cfg.vertex)
    GROUP BY
      tr.src,
      tr.dst
  });

  $tr_sth->execute();

  my %cache;
  while (my $row = $tr_sth->fetchrow_arrayref) {
    my ($via, $src, $ords, $dst, $shadowed) = @$row;

    $self->base_graph->g->add_edges(
      [ $base_id + $src, $base_id + $via ],
      [ $base_id + $via, $base_id + $dst ],
    );

    $self->base_graph->vp_shadowed_edges($base_id + $via, $shadowed);
    $self->base_graph->vp_type($base_id + $via, 'Input');

    # TODO: this could be nicer:

    my $items = $self->_json->decode( $ords );

    my @run_lists = uniq(map {
      $self->alphabet->_ord_to_list->{ $_ }
    } uniq( @$items ));

    my $encoded = $self->_json->encode(\@run_lists);
    $cache{ $encoded } //= Set::IntSpan->new(@run_lists);
    my $combined = $cache{ $encoded };

    $self->base_graph->vp_run_list($base_id + $via, $combined);
  }

  my $st_sth = $d->_dbh->prepare(q{
    SELECT
      s.state_id AS src_state,
      json_group_array(json_array(
        CAST(e.src AS TEXT),
        CAST(e.dst AS TEXT)
      )) AS shadow_edges
    FROM
      State s
        INNER JOIN Configuration c1
          ON (s.state_id = c1.state)
        INNER JOIN Vertex src_p
          ON (c1.vertex = src_p.value)
        LEFT JOIN Edge e
          ON (c1.vertex = e.src
            AND src_p.is_nullable)
        LEFT JOIN Configuration c2
          ON (c2.state = c1.state AND
            c2.vertex = e.dst)
    GROUP BY
      s.state_id
  });

  $st_sth->execute();

  while (my $row = $st_sth->fetchrow_arrayref) {
    my ($state_id, $shadowed) = @$row;
    $self->base_graph->vp_type($base_id + $state_id, 'empty');
    $self->base_graph
      ->vp_shadowed_edges($base_id + $state_id, $shadowed);
  }

  $self->base_graph->g->add_edges(
    map { [ $base_id + $_, $final_id ] } @$accepting
  );

  $self->base_graph
    ->vp_shadowed_by($start_vertex, $base_id + $start_id);
  $self->base_graph
    ->vp_shadowed_by($final_vertex, $final_id);

  $self->base_graph->vp_shadowed_edges($final_id, '[]');
}

1;

__END__
