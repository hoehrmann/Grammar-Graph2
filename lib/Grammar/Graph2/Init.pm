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
#use Grammar::Graph2::Automata;
use Grammar::Graph2::Topology;
use Grammar::Graph2::Automata2;

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  Grammar::Graph2::Topology->new(
    g => $self,
  );

  $self->_dbh->do(q{
    DROP VIEW IF EXISTS view_shadowed_leafs;

    CREATE VIEW view_shadowed_leafs AS
    WITH RECURSIVE shadowed(root, src, dst) AS (

      SELECT
        vertex_p.vertex AS root,
        json_extract(each.value, '$[0]') AS src,
        json_extract(each.value, '$[1]') AS dst
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadowed_edges) each

      UNION

      SELECT
        vertex_p.vertex AS root,
        shadowed.src AS src,
        shadowed.dst AS dst
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadowed_edges) each
          INNER JOIN shadowed
            ON (shadowed.src = json_extract(each.value, '$[0]')
              OR shadowed.dst =  json_extract(each.value, '$[1]'))

      ORDER BY
        1, 2, 3
    )
    SELECT
      root_p.vertex,
      json_group_array(
        json_array(shadowed.src, shadowed.dst)
      ) AS shadowed_edges
    FROM
      vertex_property root_p
        LEFT JOIN shadowed
          ON (shadowed.root = root_p.vertex)
        LEFT JOIN vertex_property src_p
          ON (shadowed.src = src_p.vertex)
        LEFT JOIN vertex_property dst_p
          ON (shadowed.dst = dst_p.vertex)
    WHERE
      src_p.shadowed_edges IS NULL
      AND
      dst_p.shadowed_edges IS NULL
      AND
      root_p.shadowed_edges IS NOT NULL
      AND
      shadowed.src IS NOT NULL
      AND
      shadowed.dst IS NOT NULL
    GROUP BY
      root_p.vertex
    ORDER BY
      root_p.vertex

  });

  $self->_replace_conditionals();

  $self->_dbh->do(q{
    UPDATE
      vertex_property
    SET
      shadowed_edges = (SELECT shadowed_edges
                        FROM view_shadowed_leafs v
                        WHERE v.vertex = vertex_property.vertex)
  });

  my @replace = grep {
    defined $self->vp_shadowed_by($_->[0]) 
    or
    defined $self->vp_shadowed_by($_->[1])
  } $self->g->edges;

  $self->g->add_edges(map {
    [ map { $self->vp_shadowed_by($_) // $_ } @$_ ]
  } @replace);

use YAML::XS;
#warn Dump \@replace;

  # NOTE: leaves if1/if2 etc. vertices not connected to If 

  $self->_dbh->do(q{
    DELETE FROM edge
    WHERE
      src IN (SELECT vertex FROM vertex_property WHERE type = 'If')
      AND
      dst NOT IN (SELECT vertex FROM vertex_property WHERE type = 'If1' OR type = 'If2')
  });

  $self->_dbh->do(q{
    DELETE FROM edge
    WHERE
      src NOT IN (SELECT vertex FROM vertex_property WHERE type = 'If')
      AND
      dst IN (SELECT vertex FROM vertex_property WHERE type = 'If1' OR type = 'If2')
  });


  $self->g->feather_delete_edges(@replace);

  # NEW

=pod

  my @good = graph_edges_between($self->g, $self->gp_start_vertex, $self->gp_final_vertex);
  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges(@good);

=cut

  $self->_create_vertex_spans();

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

warn if $g2->vp_shadowed_by($start_vertex);

  my @todo = ($start_vertex);

  my %seen;
  my @edges;

  while (@todo) {
    my $current = shift @todo;

# warn $current; 

    next if $seen{ $current }++;
    next if $current eq $final_vertex;

    if (defined $g2->vp_shadowed_by($current)) {
      push @todo, $g2->vp_shadowed_by($current);
    } 

    push @edges, $g2->g->edges_from($current);
    push @todo, $g2->g->successors($current);
  }

use YAML::XS;

  $subgraph->add_edges(
    map { [ map { $g2->vp_shadowed_by($_) // $_ } @$_ ] } @edges
  );

#die;

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

  my $automata = Grammar::Graph2::Automata2->new(
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

