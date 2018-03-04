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
use List::MoreUtils qw/uniq/;
use Grammar::Graph2::Alphabet;
use Graph::SomeUtils qw/:all/;
use Algorithm::ConstructDFA2;
use Set::IntSpan;
use YAML::XS;

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

#  my $db_name = ':memory:';
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

  my $next_vertex = $base_id;

  $d->_dbh->begin_work();

  $d->_dbh->do(q{
    DROP TABLE IF EXISTS shadow_tree
  });

  $d->_dbh->do(q{
    CREATE TEMPORARY TABLE shadow_tree AS 
    SELECT
      s.state_id AS src_state,
      NULL as run_list,
      NULL as dst_state,
      'DFAState:' || s.state_id AS type,
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
    UNION ALL
    SELECT
      tr.src AS src_state,
      json_group_array(tr.input) as run_list,
      tr.dst AS dst_state,
      'Input' AS type,
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

  my $sth_new_vertices = $d->_dbh->prepare(q{
    SELECT
      rowid,
      src_state,
      run_list,
      dst_state,
      type,
      shadow_edges
    FROM
      shadow_tree
  });

  $sth_new_vertices->execute();

  my $json = JSON->new->canonical(1)->ascii(1)->indent(0);

  my %cache;

  while (my $row = $sth_new_vertices->fetchrow_arrayref) {
    my ($rowid, $src_state, $run_list, $dst_state, $type, $shadow_edges) =
      @$row;

    $shadow_edges = $json->encode([ grep {
      defined $_->[0]
    } @{ $json->decode($shadow_edges) } ]);

    $self->base_graph->vp_type($base_id + $rowid, $type);
    $self->base_graph->vp_shadow_edges($base_id + $rowid, $shadow_edges);
    next unless $run_list;

    my $items = $json->decode( $run_list );

    my @run_lists = uniq(map {
      $self->alphabet->_ord_to_list->{ $_ }
    } uniq( @$items ));

    my $encoded = $json->encode(\@run_lists);
    $cache{ $encoded } //= Set::IntSpan->new(@run_lists);
    my $combined = $cache{ $encoded };

    $self->base_graph->vp_run_list($base_id + $rowid, $combined);
  }

  my $sth_new_edges = $d->_dbh->prepare(q{
    SELECT
      rowid AS src,
      (SELECT s.rowid
       FROM shadow_tree s
       WHERE s.src_state = shadow_tree.dst_state
         AND s.dst_state IS NULL) AS dst
    FROM
      shadow_tree
    WHERE
      dst_state IS NOT NULL
    UNION ALL
    SELECT
      (SELECT s.rowid
       FROM shadow_tree s
       WHERE s.src_state = shadow_tree.src_state
         AND s.dst_state IS NULL) AS src,
      rowid AS dst
    FROM
      shadow_tree
    WHERE
      dst_state IS NOT NULL
  });

  $sth_new_edges->execute();

  while (my $row = $sth_new_edges->fetchrow_arrayref()) {
    $self->base_graph->g->add_edge(
      $base_id + $row->[0],
      $base_id + $row->[1],
    );
  }

  my ($base_id2) = $d->_dbh->selectrow_array(q{
    SELECT MAX(rowid) FROM shadow_tree
  });

  $base_id2 += $base_id;

  my $new_start_vertex = $base_id2 + 1;
  my $new_final_vertex = $base_id2 + 2;

  $self->base_graph->vp_shadows($new_start_vertex, $start_vertex);
  $self->base_graph->vp_shadows($new_final_vertex, $final_vertex);

  $self->base_graph->vp_type($new_start_vertex, '');
  $self->base_graph->vp_type($new_final_vertex, '');

  ###################################################################
  # Move start_vertex edges from outside subgraph

  my @incoming = grep { not $subgraph->has_vertex($_) }
    $self->base_graph->g->predecessors($start_vertex);

  $self->base_graph->g->add_edge($_, $new_start_vertex)
    for @incoming;

  $self->base_graph->g->delete_edge($_, $start_vertex)
    for @incoming;

  ###################################################################
  # Move final_vertex edges from outside subgraph

  my @outgoing = grep { not $subgraph->has_vertex($_) }
    $self->base_graph->g->successors($final_vertex);

  $self->base_graph->g->add_edge($new_final_vertex, $_)
    for @outgoing;

  $self->base_graph->g->delete_edge($final_vertex, $_)
    for @outgoing;

  ###################################################################
  # Connect DFA vertices

  my $sth_rowid_for_state_id = $d->_dbh->prepare(q{
    SELECT rowid
    FROM shadow_tree
    WHERE dst_state IS NULL
      AND src_state = ?
  });

  my ($dfa_start_rowid) = $d->_dbh->selectrow_array(
    $sth_rowid_for_state_id, {}, $start_id
  );

  $self->base_graph->g->add_edge($new_start_vertex,
    $base_id + $dfa_start_rowid);

  for my $state_id (@$accepting) {
    my ($dfa_rowid) = $d->_dbh->selectrow_array(
      $sth_rowid_for_state_id, {}, $state_id
    );

    if (not defined $dfa_rowid) {
      warn "Unable to find DFA state $state_id in shadow_tree table";
      next;
    }

    $self->base_graph->g->add_edge($base_id + $dfa_rowid,
      $new_final_vertex);
  }

# UNEXPECTED
$self->base_graph->g->delete_edges( graph_edges_between($self->base_graph->g, $start_vertex, $final_vertex) );

  $self->base_graph->g->delete_edges( 
    map {
      $subgraph->edges_at($_)
    } grep { 
      $_ ne $start_vertex and $_ ne $final_vertex
    } $subgraph->vertices
  ) if 1;

#  $self->base_graph->g->delete_edges(map {
#    $self->base_graph->g->edges_at($_)
#  } $subgraph->vertices);

  $d->_dbh->rollback();
}

sub _shadow_subgraph_under_automaton_old {
  my ($self, $subgraph, $d, $start_vertex, $final_vertex, $start_id, $accepting) = @_;

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

  # TODO: unclear why this did not have to return anything
  # Theory: _copy_to_indirect did too much
  # NOTE: _copy_to_indirect now filters out edges in subgraph
  # That's a bit more than it used to do
  return (undef, undef);
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

  $g2->g->add_edge($id, $_) for grep { not $subgraph->has_edge($v, $_) } $g2->g->successors($v);
  $g2->g->add_edge($_, $id) for grep { not $subgraph->has_edge($_, $v) } $g2->g->predecessors($v);

}

1;

__END__


