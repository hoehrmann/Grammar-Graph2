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

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::Topology->new(
    g => $self,
  );

#  $dbh->sqlite_backup_to_file('BEFORE-MEGA.sqlite');

  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

  Grammar::Graph2::Megamata->new(
    base_graph => $self,
  )->mega if 1;
  $self->_log->debug('done mega');

#  $self->_cover_root();
  $self->_log->debug('done cover root');

  my @new_edges = $self->_dbh->selectall_array(q{
    WITH
    vertex_shadowed_by AS (
      SELECT 
        CAST(each.value AS TEXT) AS vertex,
        vertex_p.vertex AS by
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
    ),
    edge_selector AS (
      SELECT * FROM Edge
    ),
    edge_shadowed_by_or_self AS (
      SELECT
        COALESCE(src_shadow.by, e.src) AS src,
        COALESCE(dst_shadow.by, e.dst) AS dst
      FROM
        edge_selector e
          LEFT JOIN vertex_shadowed_by src_shadow
            ON (src_shadow.vertex = e.src)
          LEFT JOIN vertex_shadowed_by dst_shadow
            ON (dst_shadow.vertex = e.dst)
    )
    SELECT
      *
    FROM
      edge_shadowed_by_or_self
  });

  # TODO: use this ^ below when subgraphing

  $self->_log->debug('done computing new edges');

  $self->_dbh->do(q{
    CREATE TABLE old_edge AS SELECT * FROM edge
  });

  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@new_edges);

  $self->g->feather_delete_edges($self->g->edges_at(
    $self->gp_dead_vertex
  ));

  # unsure about this:
  my @good = graph_edges_between($self->g, $self->gp_start_vertex, $self->gp_final_vertex);
  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@good);

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

    _new_cond($g2, @ifs);
#    warn "replacing only once" and last;
  }

}

sub _new_cond {
  my ($g2, $if) = @_;

  die unless $g2->is_if_vertex($if);

  my (undef, $if1, $if2, $fi2, $fi1, $fi) =
    $g2->conditionals_from_if($if);

  my $op = $g2->vp_name($if);

  my $subgraph = _shadowed_subgraph_between($g2, $if, $fi);

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
    }

    return $set{$fi};
  });

  my %state_to_vertex = $automata->_insert_dfa($d);

  if ($op eq '#exclusion' and $if2_regular) {
    $g2->add_shadows($g2->gp_dead_vertex(), $fi2);
  }

  if ($op eq '#ordered_choice' and $if1_regular) {
    $g2->add_shadows($g2->gp_dead_vertex(), $fi2);
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
  if (not ($if1_regular and $if2_regular)) {
    $g2->vp_shadows($_, undef)
      for $if, $if1, $if2, $fi2, $fi1, $fi
  }

}

sub _shadowed_subgraph_between {
  my ($g2, $start_vertex, $final_vertex) = @_;

  my @edges = graph_edges_between($g2->g,
    $start_vertex, $final_vertex);

  my @new_edges = $g2->_dbh->selectall_array(q{
    WITH
    vertex_shadowed_by AS (
      SELECT 
        CAST(each.value AS TEXT) AS vertex,
        vertex_p.vertex AS by
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
    ),
    edge_selector AS (
      SELECT
        json_extract(each.value, '$[0]') AS src,
        json_extract(each.value, '$[1]') AS dst
      FROM
        json_each(?) each
    )
    SELECT
      COALESCE(src_shadow.by, e.src) AS src,
      COALESCE(dst_shadow.by, e.dst) AS dst
    FROM
      edge_selector e
        LEFT JOIN vertex_shadowed_by src_shadow
          ON (src_shadow.vertex = e.src)
        LEFT JOIN vertex_shadowed_by dst_shadow
          ON (dst_shadow.vertex = e.dst)

  }, {}, $g2->_json->encode(\@edges));

  my $subgraph = Graph::Feather->new(
    edges => \@new_edges
  );

  $subgraph->feather_delete_edges($subgraph->edges_at(
    $g2->gp_dead_vertex
  ));

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

