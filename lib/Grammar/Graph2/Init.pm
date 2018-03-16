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

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::Topology->new(
    g => $self,
  );

  $dbh->sqlite_backup_to_file('BEFORE-MEGA.sqlite');

  Grammar::Graph2::Megamata->new(
    base_graph => $self,
  )->mega if 1;

#  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

  my @new_edges = $self->_dbh->selectall_array(q{
    WITH vertex_shadowed_by AS (
      SELECT 
        vertex_p.vertex AS vertex,
        CAST(each.value AS TEXT) AS by
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
    )
    SELECT
      COALESCE(src_shadow.by, Edge.src) AS src,
      COALESCE(dst_shadow.by, Edge.dst) AS dst
    FROM
      Edge
        LEFT JOIN vertex_shadowed_by src_shadow
          ON (src_shadow.vertex = Edge.src)
        LEFT JOIN vertex_shadowed_by dst_shadow
          ON (dst_shadow.vertex = Edge.dst)
  });

  $self->_log->debug('done computing new edges');

  $self->_dbh->do(q{
    CREATE TABLE old_edge AS SELECT * FROM edge
  });

  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@new_edges);

  # unsure about this:
#  my @good = graph_edges_between($self->g, $self->gp_start_vertex, $self->gp_final_vertex);
#  $self->g->feather_delete_edges($self->g->edges);
#  $self->g->add_edges(@good);

  $self->_create_vertex_spans();
  $self->_log->debug('done creating spans');

  $self->_dbh->do(q{ ANALYZE });
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
    warn 'HELL!' if $scc =~ /\+/ and 1 < grep { $g2->is_if_vertex($_) } split/\+/, $scc;
#    last;
    next unless $g2->is_if_vertex($scc);
    _replace_if_fi_by_unmodified_dfa_vertices($g2, $scc);
#    warn "replacing only once" and last;
  }

}

sub _find_subgraph_between {
  my ($g2, $start_vertex, $final_vertex) = @_;
  my $subgraph = Graph::Feather->new();

  my @todo = ($start_vertex);

  my %seen;
  my @edges;

  while (@todo) {
    my $current = shift @todo;

# warn $current; 

    next if $seen{ $current }++;
    next if $current eq $final_vertex;

    my @shadowed_by = $g2->shadowed_by_or_self($current);

    push @todo, @shadowed_by;

    push @edges, $g2->g->edges_from($current);
    push @todo, $g2->g->successors($current);
  }

  my @new_edges;

  for (@edges) {
    for my $src ($g2->shadowed_by_or_self($_->[0])) {
      for my $dst ($g2->shadowed_by_or_self($_->[1])) {
        push @new_edges, [ $src, $dst ];
      }
    }
  }

  $subgraph->add_edges(
    @new_edges
  );

  return $subgraph;
}

sub _replace_if_fi_by_unmodified_dfa_vertices {
  my ($g2, $if) = @_;

  die unless $g2->is_if_vertex($if);

  my (undef, $if1, $if2, $fi2, $fi1, $fi) =
    $g2->conditionals_from_if($if);

  my $subgraph = _find_subgraph_between($g2, $if, $fi);

  my $json = JSON->new->canonical(1)->ascii(1)->indent(0);

  for my $v ($subgraph->vertices) {
    next unless $g2->is_if_vertex($v);
    next if $v eq $if;
    warn "FIXME: hmm if in if? found $v between $if and $fi";
    return;

    $g2->g->{dbh}->do(q{
      CREATE TABLE IF NOT EXISTS _debug AS
      SELECT
        0 AS src_pos,
        json_extract(each.value, '$[0]') AS src_vertex,
        0 AS dst_pos,
        json_extract(each.value, '$[1]') AS dst_vertex
      FROM
        json_each(?) each
    }, {}, $json->encode([ $subgraph->edges ]));

    return;
  }

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph, $if);

  my $op = $g2->vp_name($if);

  # TODO: ...

  my $if1_regular = not grep {
    $g2->vp_self_loop($_) eq 'irregular'
  } graph_vertices_between($subgraph, $if1, $fi1);

  my $if2_regular = not grep {
    $g2->vp_self_loop($_) eq 'irregular'
  } graph_vertices_between($subgraph, $if2, $fi2);

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

  my ($src, $dst) = $automata
    ->_shadow_subgraph_under_automaton($subgraph, $d,
      $if, $fi, $start_id, \@accepting);

  for my $v ($g2->g->vertices) {
    last unless $if1_regular;
    last unless $op eq '#ordered_choice';

    my $shadow_edges = $g2->vp_shadowed_edges($v);
    next unless defined $shadow_edges;

    my $decoded = [ grep {
      defined $_->[0]
    } @{ $json->decode($shadow_edges) } ];

    next unless grep {
      $_->[0] eq $fi1 and $_->[1] eq $fi
    } @$decoded;

    my @filtered = grep {
      not($_->[0] eq $fi2 and $_->[1] eq $fi)
      and
      not($_->[1] eq $fi2)
    } @$decoded;

    next if @filtered == @$decoded;

    $g2->vp_shadowed_edges($v, $json->encode(\@filtered))
  }

  return 1;
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

  for my $v ($self->g->vertices) {

    my $type = $self->vp_type($v);

    if ($self->is_terminal_vertex($v)) {
      next if $type eq 'Prelude';
      next if $type eq 'Postlude';

      my $char_obj = Set::IntSpan->new(
        $self->vp_run_list($v)
      );

#      $self->g->vp_type($v, 'Input');
      die unless UNIVERSAL::can($char_obj, 'spans');
      $dbh->begin_work();
      $span_insert_sth->execute($v, @$_)
        for $char_obj->spans;
      $dbh->commit();
    }
  }

}


1;

__END__

