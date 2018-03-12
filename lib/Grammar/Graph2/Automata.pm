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
  my ($self, $subgraph, $start_vertex) = @_;

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

  ###################################################################
  # Replacement start/final vertices

  my $new_start_vertex = ++$base_id;
  my $new_final_vertex = ++$base_id;

  $self->base_graph->vp_shadows($new_start_vertex, $start_vertex);
  $self->base_graph->vp_shadows($new_final_vertex, $final_vertex);

  $self->base_graph->vp_type($new_start_vertex, 'new_start');
  $self->base_graph->vp_type($new_final_vertex, 'new_final');

  ###################################################################
  # ...

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
      printf('empty', s.state_id) AS type,
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

  my $cleanup_shadow_edges = sub {

    # DO THIS PROJECTION EARLIER EG AS PART OF QUERY ABOVE

    my @edges = @_;
    my @result;

    while (@edges) {
      my $current = shift @edges;

      next unless defined $current;

      my ($src, $dst) = @$current;

      next unless defined $src;

      if (defined $self->base_graph->vp_shadows($src)) {
        $src = $self->base_graph->vp_shadows($src);
      }

      if (defined $self->base_graph->vp_shadows($dst)) {
        $dst = $self->base_graph->vp_shadows($dst);
      }

      my $src_shadows = $self->base_graph->vp_shadow_edges($src);
      my $dst_shadows = $self->base_graph->vp_shadow_edges($dst);

      if (defined $src_shadows) {
        push @result, @{ $self->_json->decode( $src_shadows ) };
        next;
      }
      
      if (defined $dst_shadows) {
        next;
      }

      push @result, [$src, $dst]
    }

    return nsort_by { $_->[0] } @result;
  };

  my %cache;

  while (my $row = $sth_new_vertices->fetchrow_arrayref) {
    my ($rowid, $src_state, $run_list, $dst_state, $type, $shadow_edges) =
      @$row;

    $shadow_edges = $self->_json->encode([
      $cleanup_shadow_edges->(@{ $self->_json->decode($shadow_edges) })
    ]);

    $self->base_graph->vp_type($base_id + $rowid, $type);
    $self->base_graph->vp_shadow_edges($base_id + $rowid, $shadow_edges);
    next unless $run_list;

    my $items = $self->_json->decode( $run_list );

    my @run_lists = uniq(map {
      $self->alphabet->_ord_to_list->{ $_ }
    } uniq( @$items ));

    my $encoded = $self->_json->encode(\@run_lists);
    $cache{ $encoded } //= Set::IntSpan->new(@run_lists);
    my $combined = $cache{ $encoded };

    $self->base_graph->vp_run_list($base_id + $rowid, $combined);
  }

  ###################################################################
  # Edges between (vertices for states) and (vertices for transitions)

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

  ###################################################################
  # Add start_vertex edges from outside subgraph

  $self->base_graph->g->add_edges(
    map { [ $_->[0], $new_start_vertex ] }
      $self->base_graph->g->edges_to($start_vertex)
  );

  ###################################################################
  # Add final_vertex edges from outside subgraph

  $self->base_graph->g->add_edges(
    map { [ $new_final_vertex, $_->[1] ] }
      $self->base_graph->g->edges_from($final_vertex)
  );

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

  warn 'dfa_start_rowid undefined??' unless defined $dfa_start_rowid;
  $self->base_graph->g->add_edge($new_start_vertex,
    $base_id + $dfa_start_rowid) if defined $dfa_start_rowid;

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

  # FIXME: shouldn't this remove edges *FROM* start_vertex?
  # other edges are not necessarily between. If changed, is
  # a corresponding change needed elsewhere?

  $self->base_graph->g->feather_delete_edges(
    $self->base_graph->g->edges_to($start_vertex)
  );

  $self->base_graph->g->feather_delete_edges(
    grep { not grep {
      $_ eq $start_vertex or $_ eq $final_vertex
    } @$_ } $subgraph->edges
  ) if 0;

  $d->_dbh->rollback();
}

sub _shadow_subgraph_under_automaton_oldest {
  my ($self, $subgraph, $d, $start_vertex, $final_vertex, $start_id, $accepting) = @_;

  my @old_edges_to_start = $self->base_graph->g->edges_to($start_vertex);
  my @old_edges_from_final = $self->base_graph->g->edges_from($final_vertex);
  my %is_accepting = map { $_ => 1 } @$accepting;

  my ($base_id) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT 1 + MAX(0 + vertex_name) FROM Vertex;
  });

  $d->_dbh->begin_work();

  $d->_dbh->do(q{
    CREATE TEMPORARY TABLE TConfiguration AS
    SELECT * FROM Configuration
    ORDER BY state, vertex
  });

  my $sth_config = $d->_dbh->prepare(q{
    SELECT rowid, state, vertex FROM TConfiguration
  });

  $sth_config->execute();
  while (my ($id, $s, $v) = $sth_config->fetchrow_array) {
    _copy_to_indirect($self->base_graph, $subgraph, $v, $base_id + $id);
    
    if ($s eq $start_id and $v eq $start_vertex) {
      $self->base_graph->vp_name($base_id + $id, $self->base_graph->vp_name($v));
      $self->base_graph->g->add_edge($_, $base_id + $id)
        for $self->base_graph->g->predecessors($start_vertex);
    }

    if ($is_accepting{$s} and $v eq $final_vertex) {
      $self->base_graph->vp_name($base_id + $id, 'Final' . $self->base_graph->vp_name($v));
      $self->base_graph->g->add_edge($base_id + $id, $_)
        for $self->base_graph->g->successors($final_vertex);
    }
  }

  my $sth_pairs = $d->_dbh->prepare(q{
    SELECT
      c1.rowid AS src_id,
      c2.rowid AS dst_id
    FROM
      view_transitions_as_5tuples t
        INNER JOIN TConfiguration c1
          ON (c1.state = t.src_state
            AND c1.vertex = t.src_vertex)
        INNER JOIN TConfiguration c2
          ON (c2.state = t.dst_state
            AND c2.vertex = t.dst_vertex);
  });

  $sth_pairs->execute();
  while (my ($src, $dst) = $sth_pairs->fetchrow_array()) {
    $self->base_graph->g->add_edge($src + $base_id, $dst + $base_id);
  }

  $self->base_graph->g->feather_delete_edges(
#    $subgraph->edges,
    @old_edges_to_start,
#    @old_edges_from_final,
  );

  $d->_dbh->rollback();

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
    $g2->vp_type($id, 'empty');
    $g2->vp_name($id, $g2->vp_name($v) // $g2->vp_type($v) // '');
    $g2->vp_shadows($id, $g2->vp_shadows($v) // $v);
  }

return;

  $g2->g->add_edge($id, $_) for
    grep { not $subgraph->has_edge($v, $_) }
    $g2->g->successors($v);
  $g2->g->add_edge($_, $id) for
    grep { not $subgraph->has_edge($_, $v) }
    $g2->g->predecessors($v);

}

1;

__END__


=pod

  my ($json_shadows) = $self->base_graph->g->{dbh}->selectrow_array(q{
    SELECT
      json_group_array(
        json_array(vertex, COALESCE(shadows, vertex))
      )
    FROM
      vertex_property
    GROUP BY
      NULL
  });

  $d->_dbh->do(q{
    CREATE TABLE shadows AS
    SELECT
      json_extract(value, '$[0]') AS vertex,
      json_extract(value, '$[1]') AS shadows,
    FROM
      json_each(?)
  }, {}, $json_shadows);

=cut

