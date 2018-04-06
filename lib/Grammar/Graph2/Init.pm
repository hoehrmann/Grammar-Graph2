package Grammar::Graph2;
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
use Grammar::Graph2::Topology;
use Grammar::Graph2::Automata;
use Grammar::Graph2::Megamata;

use Memoize;
use YAML::XS;

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::Topology->new(
    g => $self,
  );

#  $dbh->sqlite_backup_to_file('BEFORE-MEGA.sqlite');

  $self->_dbh->do(q{
    CREATE TABLE old_edge AS SELECT * FROM edge
  });

  Grammar::Graph2::Megamata->new(
    base_graph => $self,
  )->mega if 0;

  $self->flatten_shadows();

  $self->_log->debug('done mega');

  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

#  $self->g->feather_delete_edges(map { $self->g->edges_at($_) } grep {
#    $self->is_fi2_vertex($_) and $self->vp_name($_) eq '#exclusion'
#  } $self->g->vertices);

#$self->_create_vertex_spans();
#$self->_log->debug('done creating spans');
#return;

#  $self->_cover_root();
  $self->flatten_shadows();
  $self->_log->debug('done cover root');

  my @new_edges = _shadowed_subgraph_between($self,
    $self->gp_start_vertex, $self->gp_final_vertex)->edges;

#  $g2->flatten_shadows();

  $self->_log->debug('done computing new edges');

#  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@new_edges);
  $self->g->feather_delete_edges(map { $self->g->edges_at($_) } grep { $self->is_shadowed($_) } $self->g->vertices);

  # unsure about this:
  my @good = graph_edges_between($self->g, $self->gp_start_vertex, $self->gp_final_vertex);
  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@good);

  # TODO: ought to clean up shadows, otherwise joins break?
  $self->_dbh->do(q{
    DELETE FROM vertex_property
    where vertex not in (select src from edge
                         union select dst from edge
                         union select src from old_edge
                         union select dst from old_edge)
  }) if 0;

  $self->_dbh->do(q{
    DELETE FROM vertex
    where vertex_name not in (select src from edge
                              union select dst from edge
                              union select src from old_edge
                              union select dst from old_edge)
  }) if 0;

  $self->_create_vertex_spans();
  $self->_log->debug('done creating spans');

  $self->_dbh->do(q{ ANALYZE });
}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################
sub _cover_root_new {
  my ($g2) = @_;

  my ($start_vertex) = $g2->g->successors($g2->gp_start_vertex);
  my ($final_vertex) = $g2->g->predecessors($g2->gp_final_vertex);

die unless $g2->is_prelude_vertex($start_vertex);
die unless $g2->is_postlude_vertex($final_vertex);

  my $subgraph = _shadowed_subgraph_between($g2,
    $start_vertex, $final_vertex);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph,
    $start_vertex);

  my %state_to_vertex = $automata->_insert_dfa($d);
}

sub _cover_root {
  my ($g2) = @_;

  my $subgraph = _shadowed_subgraph_between($g2,
    $g2->gp_start_vertex, $g2->gp_final_vertex);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph,
    $g2->gp_start_vertex);

  my %state_to_vertex = $automata->_insert_dfa($d);
}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################

sub _replace_conditionals {
  my ($self) = @_;

  my $p = $self;
  my $g2 = $self;

  my @parent_child_edges = $p->_dbh->selectall_array(q{
    SELECT parent, child FROM view_parent_child
  });

  my $gx = Graph::Directed->new(
    edges => \@parent_child_edges,
  );

  my $scg = $gx->strongly_connected_graph;

  for my $scc (reverse $scg->toposort) {
    my @ifs = grep { $g2->is_if_vertex($_) } split/\+/, $scc;

    warn 'HELL!' if 1 < @ifs;

    next unless @ifs;
    next if @ifs > 1;

    $self->_log->debugf('Pre-computing If %s', @ifs);

    _new_cond($g2, @ifs);

    $g2->flatten_shadows();

#    warn "replacing only once" and last;

  }

}

sub _new_cond {
  my ($g2, $if) = @_;

  die unless $g2->is_if_vertex($if);

  my (undef, $if1, $if2, $fi2, $fi1, $fi) =
    $g2->conditionals_from_if($if);

  $g2->_log->debugf('Pre-computing If structure %s', join " ", $if, $if1, $if2, $fi2, $fi1, $fi);

  my $op = $g2->vp_name($if);

  my $subgraph = _shadowed_subgraph_between($g2, $if, $fi);

  $g2->_log->debugf('  involving vertices %s', join " ", $subgraph->vertices);

#warn join " -> ", @$_ for $subgraph->edges;

  for my $v ($subgraph->vertices) {
    next unless $g2->is_if_vertex($v);
    next if $v eq $if;
    warn "FIXME: hmm if in if? found $v between $if and $fi";
#    return;
  }

  my $if1_regular = not grep {
    ($g2->vp_self_loop($_) // '') eq 'irregular'
  } graph_vertices_between($subgraph, $if1, $fi1);

  my $if2_regular = not grep {
    ($g2->vp_self_loop($_) // '') eq 'irregular'
  } graph_vertices_between($subgraph, $if2, $fi2);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph, $if);

  $d->_dbh->sqlite_backup_to_file("COND.$if.sqlite");

  my @accepting = $d->cleanup_dead_states(sub {

    my %set = map { $_ => 1 } @_;

    if ($op eq '#ordered_choice') {
      return $set{$fi1} || $set{$fi2};
    }

    if ($op eq '#ordered_conjunction') {
      return $set{$fi1} && $set{$fi2};
    }

    if ($op eq '#conjunction') {
      return $set{$fi1} && $set{$fi2};
    }

    if ($op eq '#exclusion') {
      if ($if2_regular) {
        return ($set{$fi1} and not $set{$fi2});
      }
      return $set{$fi1};
    }

    return $set{$fi};
  }) if 1;

  my %state_to_vertex = $automata->_insert_dfa($d);

  $g2->_log->debugf("state_to_vertex: " . Dump \%state_to_vertex);

  # dubious
  if ($op eq '#exclusion' and $if2_regular) {
#    $g2->add_shadows($g2->gp_dead_vertex(), $fi2);
#    $g2->add_shadows($g2->gp_dead_vertex(), $fi1);
  }

  # dubious
  if ($op eq '#ordered_choice' and $if1_regular) {
#    $g2->add_shadows($g2->gp_dead_vertex(), $fi2);
  }

  # TODO: don't understand this
  if (0 and $if1_regular and $if2_regular) {
    $g2->add_shadows($g2->gp_dead_vertex(), $_)
      for $if, $if1, $if2, $fi2, $fi1, $fi;
  }

  for my $v (values %state_to_vertex) {

    # TODO: would this work?
    last;

    last unless $if1_regular;
    last unless $op eq '#ordered_choice';
    my $shadows = $g2->vp_shadows($v);
    next unless defined $shadows;
    my @shadows = @{ $g2->_json->decode($shadows) };
    next unless grep { $_ eq $fi1 } @shadows;
    $g2->vp_shadows($v, $g2->_json->encode([
      grep { $_ ne $fi2 } @shadows
    ]));
  }

  # TODO: makes no sense, wrong shadow direction
  if (0 and not ($if1_regular and $if2_regular)) {
    $g2->vp_shadows($_, undef)
      for $if, $if1, $if2, $fi2, $fi1, $fi
  }

}

sub _shadowed_subgraph_between {
  my ($g2, $start_vertex, $final_vertex) = @_;

  die if $g2->is_shadowed($start_vertex);
  die if $g2->is_shadowed($final_vertex);

  my @edges = graph_edges_between($g2->g,
    $start_vertex, $final_vertex);

=pod

warn "+inputs:";
warn "input v $_" for grep { $g2->is_input_vertex($_) } map { @$_ } @edges;
warn "-inputs";

warn "+edges:";
warn "edge @$_" for @edges;
warn "-edges";

=cut

  my @todo_edges = @edges;
  my %seen_edge;
  my @new_edges;
  while (@todo_edges) {
    my ($src, $dst) = @{ shift @todo_edges };
    next if $seen_edge{$src}{$dst}++;

    for my $s ($g2->shadowed_by_or_self($src)) {

push @todo_edges, [ $s, $_ ] for $g2->g->successors($s);

      for my $d ($g2->shadowed_by_or_self($dst)) {

# FIXME: this takes vertices it should not
push @todo_edges, [ $_, $d ] for $g2->g->predecessors($d);

        push @todo_edges, [ $s, $d ];

=pod

        my $debug = sprintf "Considering %u,%s,%s,%u -> %u,%s,%s,%u\n",
          0,
          $g2->vp_type($s),
          ($g2->vp_name($s) // ''),
          $s,
          0,
          $g2->vp_type($d),
          ($g2->vp_name($d) // ''),
          $d,
        ;

        warn $debug;

        if ($debug =~ /PITarget.*dfa/) {
          print Dump {
            'has_edge(s, d)' => $g2->g->has_edge($s, $d),
          };
        }



=cut

        my $same_shadow_group = ($g2->vp_shadow_group($d) // '') eq ($g2->vp_shadow_group($s) // '');
        next if $same_shadow_group and not $g2->g->has_edge($s, $d);

        next if ( $g2->vp_name($s) // '') =~ /^#dfaTransition/
            and ( $g2->vp_name($d) // '') !~ /^#dfaState/;

        next unless $g2->g->has_edge($s, $d)
#or $g2->g->has_edge($src, $dst)
#          or (
#            not($g2->is_shadowed($src))
#            and
#            not(defined $g2->vp_shadows($d)))
#          or (
#            not($g2->is_shadowed($dst))
#            and
#            not(defined $g2->vp_shadows($s)))
#          or (($g2->vp_shadow_group($s) // '') ne ($g2->vp_shadow_group($d) // ''))
          or (not $same_shadow_group)
        ;

        push @new_edges, [ $s, $d ];
        next;
      }
    }
  }

#warn "onput v $_" for grep { $g2->is_input_vertex($_) } map { @$_ } @new_edges;

  my $subgraph = Graph::Feather->new(
#    edges => \@edges,
    edges => \@new_edges
  );

#  $subgraph->feather_delete_edges($subgraph->edges_at(
#    $g2->gp_dead_vertex
#  ));

  return $subgraph;
    
}

#####################################################################
# This stuff does not really belong here:
#####################################################################

sub _create_vertex_spans {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  $dbh->do(q{
    DROP TABLE IF EXISTS vertex_span;

    CREATE TABLE vertex_span(
      vertex,
      min INTEGER,
      max INTEGER
    );

    CREATE INDEX idx_vertex_span_vertex
      ON vertex_span(vertex)
  });

  my $span_insert_sth = $dbh->prepare(q{
    INSERT INTO vertex_span(vertex, min, max) VALUES (?, ?, ?)
  });

  my $spans_for_run_list = memoize(sub{
    my ($run_list) = @_;
    return Set::IntSpan->new($run_list)->spans;
  });

  for my $v ($self->g->vertices) {

    my $type = $self->vp_type($v);

    if ($self->is_terminal_vertex($v)) {
      next if $type eq 'Prelude';
      next if $type eq 'Postlude';

      $dbh->begin_work();
      $span_insert_sth->execute($v, @$_)
        for $spans_for_run_list->( $self->vp_run_list($v) );
      $dbh->commit();
    }
  }

}


1;

__END__

