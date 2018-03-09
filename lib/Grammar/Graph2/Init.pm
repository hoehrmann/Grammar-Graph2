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
use Grammar::Graph2::Automata;
use Grammar::Graph2::Topology;

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::Topology->new(
    g => $self,
  );

  $self->_replace_conditionals();
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
    next unless $g2->is_if_vertex($scc);
    _replace_if_fi_by_unmodified_dfa_vertices($g2, $scc);
  }

}

sub _replace_if_fi_by_unmodified_dfa_vertices {
  my ($g2, $if) = @_;

  die unless $g2->is_if_vertex($if);

  my (undef, $if1, $if2, $fi2, $fi1, $fi) =
    $g2->conditionals_from_if($if);

  my $subgraph = Graph::Feather->new(
    vertices => [ graph_vertices_between($g2->g, $if, $fi) ],
    edges    => [    graph_edges_between($g2->g, $if, $fi) ],
  );

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

    my $shadow_edges = $g2->vp_shadow_edges($v);
    next unless defined $shadow_edges;

    my $decoded = $json->decode($shadow_edges);
    next unless grep {
      $_->[0] eq $fi1 and $_->[1] eq $fi
    } @$decoded;

    my @filtered = grep {
      not($_->[0] eq $fi2 and $_->[1] eq $fi)
      and
      not($_->[1] eq $fi2)
    } @$decoded;

    $g2->vp_shadow_edges($v, $json->encode(\@filtered))
      if @filtered != @$decoded;
  }

  return 1;
}



1;

__END__

