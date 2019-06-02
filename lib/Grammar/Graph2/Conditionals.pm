package Grammar::Graph2;
use strict;
use warnings;
use 5.024000;
use Moo;
use Log::Any qw//;
use Types::Standard qw/:all/;
use List::Util qw/min max/;
use List::MoreUtils qw/uniq/;
use List::OrderBy;
use List::StackBy;
use List::UtilsBy qw/uniq_by nsort_by/;

use Graph::Feather;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use Grammar::Graph2;
# use Grammar::Graph2::TestParser::MatchEnumerator;
use Grammar::Graph2::Topology;
use Grammar::Graph2::Automata;
use Grammar::Graph2::Megamata;
use Grammar::Graph2::UTF8;
use Acme::Partitioner;

use Memoize;
use YAML::XS;

sub _replace_conditionals {
  my ($self) = @_;

  my $p = $self;
  my $g2 = $self;

  # Maybe this should be computed before mega?

  my $db_utils = Grammar::Graph2::DBUtils->new(
    g => $self);

  $db_utils->views_to_tables(
    'view_parent_child',
  );

  my @parent_child_edges = $p->_dbh->selectall_array(q{
    SELECT parent, child FROM m_view_parent_child
  });

  # TODO: after mega parent_child_edges is very large
  # but we don't need most of the data, find some improvement

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

#    $g2->flatten_shadows();

#    warn "replacing only once" and last;

  }

}

sub _new_cond {
  my ($g2, $if) = @_;

  die unless $g2->is_if_vertex($if);

  my (undef, $if1, $if2, $fi2, $fi1, $fi) =
    $g2->conditionals_from_if($if);


  my $overlap =
    graph_vertices_between($g2->g, $if1, $fi2)
    ||
    graph_vertices_between($g2->g, $if2, $fi1)
    ;

  # If the subgraph from if1 to fi1 has any vertex in common with
  # the subgraph from if2 to fi2 then a DFA state may be created
  # that contains fi1 and fi2 even though only one of them matched.
  # That can conflict with the later attempt to resolve the If 
  # structure completely. TODO: this needs to be addressed in a
  # greater refactoring that also handles "skippable" setting.
  # TODO: this has been addressed below, rephrase comment ^
  warn "if1..fi1 and if2..fi2 overlap" if $overlap;

  $g2->_log->debugf('Pre-computing If structure %s', join " ", $if, $if1, $if2, $fi2, $fi1, $fi);

  my $op = $g2->vp_name($if);

  my $subgraph = Grammar::Graph2::_shadowed_subgraph_between($g2, $if, $fi);

  $g2->_log->debugf('  involving vertices %s', join " ", $subgraph->vertices);

#warn join " -> ", @$_ for $subgraph->edges;

  for my $v ($subgraph->vertices) {
    next unless $g2->is_if_vertex($v);
    next if $v eq $if;
    warn "FIXME: hmm if in if? found $v between $if and $fi";
#    return;
  }

  # TODO: This should check the contents of If1/If2 for "irregular"
  # and If1/If2 themselves for "linear" but the VIEW does not make
  # it easy at the moment to distinguish between the two cases.

  # TODO: is this still the case? ^

  # TODO: It is probably necessary to mark if/fi irregular if they
  # have irregular contents, or at least mark them non-skippable.
  # TODO: don't we do that ^ now?

  my $if1_regular;
  my $if2_regular;

if (0) {

  my $db_utils = Grammar::Graph2::DBUtils->new(
    g => $g2);

  # TODO: view access the view instead of asking vertex_property?

  $db_utils->views_to_tables(
    'view_contents_self_loop',
  );

  ($if1_regular) = map { $_ eq 'no' } $g2->_dbh->selectrow_array(q{
    SELECT self_loop
    FROM m_view_contents_self_loop
    WHERE vertex = ?
  }, {}, $if1);

  ($if2_regular) = map { $_ eq 'no' } $g2->_dbh->selectrow_array(q{
    SELECT self_loop
    FROM m_view_contents_self_loop
    WHERE vertex = ?
  }, {}, $if2);

  # Those ^ make no sense, for one thing, self_loop is tri-state,
  # and the code produces the same result for 'no' and 'irregular'
  # TODO: Is that ^ still true and relevant? Does it affect `else`?

} else {

  ($if1_regular) = map { $_ eq 'no' } $g2->_dbh->selectrow_array(q{
    SELECT contents_self_loop
    FROM vertex_property
    WHERE vertex = ?
  }, {}, $if1);

  ($if2_regular) = map { $_ eq 'no' } $g2->_dbh->selectrow_array(q{
    SELECT contents_self_loop
    FROM vertex_property
    WHERE vertex = ?
  }, {}, $if2);

}

  $g2->_log->debugf("if1_regular: %s", $if1_regular);
  $g2->_log->debugf("if2_regular: %s", $if2_regular);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph, [ $if ]);

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
        $g2->_log->debugf("FOO %u{%u,%u} %u %u ergo %u", $if, $fi1, $fi2, $set{$fi1}, $set{$fi2}, ($set{$fi1} && !$set{$fi2}));
        return ($set{$fi1} and not $set{$fi2});
      }
      $g2->_log->debugf("FOO2 %u %u %u", $if, $set{$fi1}, $set{$fi2});
      return $set{$fi1};
    }

    return $set{$fi};

  }) if 1;

#  $d->_dbh->sqlite_backup_to_file($if . ".dfa.sqlite");

  $g2->_log->debugf("ACCEPTING: %s", "@accepting");

  my %state_to_vertex = $automata->_insert_dfa($d, $start_id);

  $g2->_log->debugf("state_to_vertex: " . Dump \%state_to_vertex);

  if ($op eq '#exclusion' and $if2_regular) {

    $g2->_dbh->do(
      q{
        DELETE
        FROM
          vertex_shadows
        WHERE
          vertex IN (SELECT CAST(value AS TEXT) FROM json_each(?))
          AND
          shadows = CAST(? AS TEXT)
          AND
          EXISTS (
            SELECT 1
            FROM vertex_shadows vs
            WHERE vertex_shadows.vertex = vs.vertex
              AND vs.shadows = CAST(? AS TEXT)
          )
      },
      {},
      $g2->_json->encode([ values %state_to_vertex ]),
      $fi,
      $fi2
    );

  }

  # If there is no irregular recursion between If1 and Fi1, and
  # there is no path from If1 to itself that does not go over Fi1,
  # then any path from If1 to Fi1 is a proper match and there is
  # no point in offering the Fi2 to later stages, so when a DFA
  # state represents both Fi1 and Fi2 the Fi2 vertex is removed.

  # TODO: analogous cleanup logic for #ordered_conjunction

  if ($if1_regular and $op eq '#ordered_choice') {
    my @candidates = map { @$_ } $g2->_dbh->selectall_array(q{
      SELECT
        vs1.vertex AS vertex
      FROM
        view_vertex_shadows vs1
          INNER JOIN vertex_property fi1_p
            ON (vs1.shadows = fi1_p.vertex
              AND fi1_p.type = 'Fi1')
          INNER JOIN view_vertex_shadows vs2
            ON (vs1.vertex = vs2.vertex)
          INNER JOIN vertex_property fi2_p
            ON (vs2.shadows = fi2_p.vertex
              AND fi2_p.type = 'Fi2')
      WHERE
        fi1_p.vertex = ?
        AND
        fi2_p.vertex = ?
        AND
        vs1.vertex IN (
          SELECT CAST(value AS TEXT)
          FROM json_each(?)
        )
    }, {}, $fi1, $fi2,
      $g2->_json->encode([ values %state_to_vertex ]));

    for my $v (@candidates) {

      # TODO: limit to vertices in @accepting

      $g2->_log->debugf("Removing If2 vertex %u from vertex %u",
        $fi2, $v);

      $g2->_dbh->do(q{
        DELETE
        FROM vertex_shadows
        WHERE vertex = CAST(? AS TEXT)
          AND shadows = CAST(? AS TEXT)
      }, {}, $v, $fi2)
    }
  }

  # Always add Fi2 to the vertex that shadows the dead state,
  # mainly to ensure that for #ordered_choice with a regular
  # If1 structure, the Fi2 vertex does not end up unshadowed.
  $g2->add_shadows($state_to_vertex{ $d->dead_state_id }, $fi2);

  # TODO: cover more cases, #exclusion just needs if2 etc.
  if (not($overlap) and $if1_regular and $if2_regular) {
    $g2->vp_skippable($_, 1)
      for $if, $if1, $if2, $fi2, $fi1, $fi;
  }

}

1;

__END__

