package Grammar::Graph2::Automata;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by uniq_by/;
use Grammar::Graph2::Alphabet;
use Algorithm::ConstructDFA2;

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

sub BUILD {
  my ($self) = @_;

  $self->_log->debug("Computing alphabet");
  $self->_set_alphabet(Grammar::Graph2::Alphabet->new(
    g => $self->base_graph
  ));

}

sub subgraph_automaton {
  my ($self, $subgraph, $start_vertex) = @_;

  my $db_name = 'MATA-DFA.sqlite';
  unlink $db_name;

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

      return Set::IntSpan
        ->new($self->base_graph->vp_run_list($vertex))
        ->member($input);
    },

    storage_dsn     => "dbi:SQLite:dbname=$db_name",
  );

  my $start_id = $d->find_or_create_state_id( $start_vertex );

  while (my $count = $d->compute_some_transitions(1000)) {
    $self->_log->debugf("Computed %u transitions", $count);
  }

  return $d;
}

sub _shadow_subgraph_under_automaton {
  my ($self, $subgraph, $d) = @_;

  my ($base_id) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  my $sth_config = $d->_dbh->prepare(q{
    SELECT rowid, state, vertex FROM Configuration
  });

  $sth_config->execute();
  while (my ($id, $s, $v) = $sth_config->fetchrow_array) {
    _copy_to_indirect($self->base_graph, $subgraph, $v, $base_id + $id);
  }

  my $sth_pairs = $d->_dbh->prepare(q{
    SELECT src_id, dst_id
    FROM view_transitions_as_configuration_pair
  });

  $sth_pairs->execute();
  while (my ($src, $dst) = $sth_pairs->fetchrow_array()) {
    $self->base_graph->g->add_edge($src + $base_id, $dst + $base_id);
  }

#  $self->base_graph->g->delete_edges($subgraph->edges);
  $self->base_graph->g->delete_edges(map {
    $self->base_graph->g->edges_at($_)
  } $subgraph->vertices);
}

sub _copy_to_indirect {
  my ($g2, $subgraph, $v, $id) = @_;

  die unless defined $v;

  if ($g2->is_input_vertex($v)) {
    $g2->vp_type($id, 'Input');
    $g2->vp_shadows($id, $g2->vp_shadows($v) // $v);
    $g2->vp_run_list($id, $g2->vp_run_list($v));

  } else {
    $g2->vp_type($id, '');
    $g2->vp_shadows($id, $g2->vp_shadows($v) // $v);
  }

  $g2->g->add_edge($id, $_)
    for grep {
#      not $subgraph->has_vertex($_);
       1
        }
      $g2->g->successors($v);

  $g2->g->add_edge($_, $id)
    for grep { 
#      not $subgraph->has_vertex($_);
       1
        }
      $g2->g->predecessors($v);

}

1;

__END__


