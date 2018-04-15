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
    DROP TABLE IF EXISTS old_edge;
    CREATE TABLE old_edge(
      src REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      dst REFERENCES Vertex(vertex_name) ON UPDATE CASCADE
    );
    INSERT INTO old_edge SELECT * FROM edge;
  });

  Grammar::Graph2::Megamata->new(
    base_graph => $self,
  )->mega if 0;

  $self->_log->debug('done mega');

  $self->_log->debug('starting _replace_conditionals');
  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

#  $self->flatten_shadows();

  $self->_cover_root();
  $self->_log->debug('done cover root');

#  $self->_cover_epsilons();
  $self->_log->debug('done cover epsilons');

  # TODO: What about displacement table?
  $self->flatten_shadows();

  my $subgraph = _shadowed_subgraph_between($self,
    $self->gp_start_vertex, $self->gp_final_vertex);

  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges( $subgraph->edges );

  $self->_dbh->do(q{
    WITH good AS (
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
      vertex NOT IN (SELECT vertex FROM good)
  }) if 1;

  $self->_cover_input_input_edges();

  $self->_rename_vertices();

  $self->_create_vertex_spans();
  $self->_log->debug('done creating spans');

  $self->_create_input_classes();
  $self->_log->debug('done creating input_classes');

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

  # TODO: This should check the contents of If1/If2 for "irregular"
  # and If1/If2 themselves for "linear" but the VIEW does not make
  # it easy at the moment to distinguish between the two cases.

  my ($if1_regular) = map { $_ ne 'linear' } $g2->_dbh->selectrow_array(q{
    SELECT self_loop
    FROM view_contents_self_loop
    WHERE vertex = ?
  }, {}, $if1);

  my ($if2_regular) = map { $_ ne 'linear' } $g2->_dbh->selectrow_array(q{
    SELECT self_loop
    FROM view_contents_self_loop
    WHERE vertex = ?
  }, {}, $if2);

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
        return ($set{$fi1} and not $set{$fi2});
      }
      return $set{$fi1};
    }

    return $set{$fi};
  }) if 1;

  $g2->_log->debugf("ACCEPTING: %s", "@accepting");

  my %state_to_vertex = $automata->_insert_dfa($d, $start_id);

  $g2->_log->debugf("state_to_vertex: " . Dump \%state_to_vertex);

  # If there is no irregular recursion between If1 and Fi1, and
  # there is no path from If1 to itself that does not go over Fi1,
  # then any path from If1 to Fi1 is a proper match and there is
  # no point in offering the Fi2 to later stages, so when a DFA
  # state represents both Fi1 and Fi2 the Fi2 vertex is removed.

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
    }, {}, $fi1, $fi2);

    for my $v (@candidates) {

      my @cleaned = grep {
        $_ ne $fi2
      } @{ $g2->_json->decode( $g2->vp_shadows($v) ) };

      $g2->_log->debugf("Removing If2 vertex %u from vertex %u",
        $fi2, $v);

#      next;

      $g2->vp_shadows($v, $g2->_json->encode(\@cleaned));
    }
  }

  # Always add Fi2 to the vertex that shadows the dead state,
  # mainly to ensure that for #ordered_choice with a regular
  # If1 structure, the Fi2 vertex does not end up unshadowed.
  $g2->add_shadows($state_to_vertex{ $d->dead_state_id }, $fi2);
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

sub _create_input_classes {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;
  
  my $alphabet = Grammar::Graph2::Alphabet->new(
    g => $self
  );

  my %h = %{ $alphabet->_ord_to_list };

  my @list_of_spans = map {
    $self->_json->encode([ Set::IntSpan->new($h{$_})->spans ])
  } sort { $a <=> $b } keys %h;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS input_class;
    CREATE TABLE input_class AS 
    SELECT
      CAST(1 + class.key AS INT) AS class,
      CAST(json_extract(span.value, '$[0]') AS INT) AS 'min',
      CAST(json_extract(span.value, '$[1]') AS INT) AS 'max'
    FROM
      json_each(?) class
        INNER JOIN json_each(class.value) span
  }, {}, $self->_json->encode(\@list_of_spans));
}

sub _create_vertex_spans {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  $dbh->do(q{
    DROP TABLE IF EXISTS vertex_span;

    CREATE TABLE vertex_span(
      vertex REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
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

sub _rename_vertices {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS rename_vertex;
    CREATE TABLE rename_vertex AS
    SELECT
      Vertex.vertex_name AS vertex
    FROM
      Vertex
        LEFT JOIN vertex_property vertex_p
          ON (vertex_p.vertex = Vertex.vertex_name)
    ORDER BY
      1
  });

  my %map = %{ $self->_dbh->selectall_hashref(q{
    SELECT
      vertex,
      rowid
    FROM
      rename_vertex
  }, 'vertex') };

#die Dump \%map;

  for my $meth (qw/vp_shadows vp_epsilon_group/) {
    for my $v ($self->g->vertices) {
      my $encoded = $self->$meth($v);
      next unless defined $encoded;
      $self->$meth($v, $self->_json->encode([
        map { '' . $map{$_}->{rowid} }
          @{ $self->_json->decode($encoded) }
      ]));
#      warn $self->$meth($v);
    }
  }

  $self->gp_start_vertex('' . $map{$self->gp_start_vertex()}->{rowid});
  $self->gp_final_vertex('' . $map{$self->gp_final_vertex()}->{rowid});
#  $self->gp_dead_vertex('' . $map{$self->gp_dead_vertex()}->{rowid})
#    if defined $self->gp_dead_vertex();

  $self->_dbh->do(q{
    UPDATE
      vertex
    SET
      vertex_name = (SELECT CAST(rowid AS TEXT)
                     FROM rename_vertex
                     WHERE vertex = vertex.vertex_name)
  });

}

1;

__END__
