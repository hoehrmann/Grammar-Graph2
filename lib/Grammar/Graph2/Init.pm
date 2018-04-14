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

  my $old_edges = Graph::Feather->new(
    edges => [ $self->g->edges ]
  );

  $self->_dbh->do(q{
    CREATE TABLE old_edge AS SELECT * FROM edge
  });

  Grammar::Graph2::Megamata->new(
    base_graph => $self,
  )->mega if 1;

  $self->_log->debug('done mega');

  $self->_log->debug('starting _replace_conditionals');
#  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

#  $self->flatten_shadows();

#  $self->_cover_root();
  $self->_log->debug('done cover root');

  $self->_cover_epsilons();
  $self->_log->debug('done cover epsilons');

  # TODO: What about displacement table?
  $self->flatten_shadows();

  my $subgraph = _shadowed_subgraph_between($self,
    $self->gp_start_vertex, $self->gp_final_vertex);

  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges( $subgraph->edges );

  $self->_dbh->do(q{
    WITH good_vertex AS (
      SELECT src AS vertex FROM old_edge
      UNION
      SELECT dst FROM old_edge
      UNION
      SELECT src FROM edge
      UNION
      SELECT dst FROM edge
    )
    DELETE FROM
      vertex_property
    WHERE
      vertex NOT IN (SELECT vertex FROM good_vertex)
  }) if 0;

  $self->_create_vertex_spans();
  $self->_log->debug('done creating spans');

  $self->_cover_input_input_edges();

  $self->_dbh->do(q{ ANALYZE });
  return;
}

sub _cover_input_input_edges {
  my ($self) = @_;

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_input_input_edges
  });

  $self->_dbh->do(q{
    CREATE VIEW view_input_input_edges AS
    SELECT
      Edge.rowid AS rowid,
      Edge.src AS src,
      Edge.dst AS dst
    FROM
      Edge
        INNER JOIN vertex_property src_p
          ON (src_p.vertex = Edge.src)
        INNER JOIN vertex_property dst_p
          ON (dst_p.vertex = Edge.dst)
    WHERE
      src_p.type = 'Input'
      AND
      dst_p.type = 'Input'
  });

  my @new_epsilons = $self->_dbh->selectall_array(q{
    SELECT
      max_vertex.vertex + ii.rowid AS vertex,
      ii.src,
      ii.dst
    FROM
      view_input_input_edges ii
        INNER JOIN (SELECT
                      MAX(vertex_name) AS vertex
                    FROM
                      vertex) max_vertex
  });

  $self->vp_type($_->[0], 'empty') for @new_epsilons;
  $self->g->add_edges(map {
    [ $_->[1], $_->[0] ],
    [ $_->[0], $_->[2] ],
  } @new_epsilons);

  $self->g->feather_delete_edges($self->_dbh->selectall_array(q{
    SELECT src, dst FROM view_input_input_edges
  }));

}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################
sub _back_subst {
  my ($self) = @_;

  # v src dst

  $self->_dbh->do(q{
    CREATE TABLE back_substitution AS 
    WITH RECURSIVE
    foo AS (
      SELECT
        e.src AS vertex,
        e.src AS src,
        e.dst AS dst
      FROM
        (SELECT * FROM edge UNION SELECT * FROM old_edge) e
      UNION
      SELECT
        vertex_s.shadows,
        src_s.shadows,
        dst_s.shadows
      FROM
        foo
          INNER JOIN view_vertex_shadows_or_self vertex_s
            ON (foo.vertex = vertex_s.vertex)
          INNER JOIN view_vertex_shadows_or_self src_s
            ON (foo.src = src_s.vertex)
          INNER JOIN view_vertex_shadows_or_self dst_s
            ON (foo.dst = dst_s.vertex)
    )
    SELECT DISTINCT
      foo.*
    FROM
      foo
        INNER JOIN old_edge
          ON (old_edge.src = foo.src
            AND old_edge.dst = foo.dst)
        INNER JOIN edge
          ON (edge.src = foo.vertex
            OR edge.dst = foo.vertex)
    WHERE
      NOT EXISTS (SELECT 1 FROM Edge WHERE foo.src = Edge.src AND foo.dst = Edge.dst)
  });

}

sub _cover_epsilons {
  my ($g2) = @_;

#  my $subgraph = _shadowed_subgraph_between($g2,
#    $g2->gp_start_vertex, $g2->gp_final_vertex);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my @foo = $g2->_dbh->selectall_array(q{
    WITH
    start_vertex AS (
      SELECT attribute_value AS vertex
      FROM graph_attribute
      WHERE attribute_name = 'start_vertex'
    )
    SELECT DISTINCT
      json_group_array(lhs_e.e_reachable) AS epsilons
--    ,  src_p.vertex AS root
    FROM
      vertex_property src_p
        INNER JOIN Edge 
          ON (src_p.vertex = Edge.src)
        INNER JOIN view_epsilon_closure lhs_e
          ON (Edge.dst = lhs_e.vertex)
        INNER JOIN vertex_property dst_p
          ON (lhs_e.e_reachable = dst_p.vertex)
        LEFT JOIN start_vertex
          ON (src_p.vertex = start_vertex.vertex)
    WHERE
      (src_p.type = 'Input' OR start_vertex.vertex IS NOT NULL)
      AND
      dst_p.type <> 'Input'
    GROUP BY
      src_p.vertex
  });

  my $subgraph = Graph::Feather->new(
    vertices => [
      map { @{ $g2->_json->decode($_->[0]) } } @foo
    ]
  );

  my ($d, @start_ids) = $automata->subgraph_automaton($subgraph,
    map { $g2->_json->decode($_->[0]) } @foo );

  my %state_to_vertex = $automata->_insert_dfa($d, @start_ids);
}

sub _cover_root {
  my ($g2) = @_;

  my $subgraph = _shadowed_subgraph_between($g2,
    $g2->gp_start_vertex, $g2->gp_final_vertex);

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $g2,
  );

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph,
    [ $g2->gp_start_vertex ]);

  my %state_to_vertex = $automata->_insert_dfa($d, $start_id);
}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################

sub _replace_conditionals {
  my ($self) = @_;

  my $p = $self;
  my $g2 = $self;

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

  my ($d, $start_id) = $automata->subgraph_automaton($subgraph, [ $if ]);

#  $d->_dbh->sqlite_backup_to_file("COND.$if.sqlite");

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

  $g2->_log->debugf("ACCEPTING: %s", "@accepting");

  my %state_to_vertex = $automata->_insert_dfa($d, $start_id);

  $g2->_log->debugf("state_to_vertex: " . Dump \%state_to_vertex);

  # dubious
  if ($op eq '#exclusion' and $if2_regular) {
#    $g2->add_shadows( $state_to_vertex{ $d->dead_state_id() }, $fi2 );
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

  # TODO: ultimately this should not result in failure
  die if $g2->is_shadowed($start_vertex);
  die if $g2->is_shadowed($final_vertex);

  return Graph::Feather->new(
    edges => [ graph_edges_between($g2->g, $start_vertex, $final_vertex) ],
  );
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

