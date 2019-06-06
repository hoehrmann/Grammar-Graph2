package Grammar::Graph2::Ordering;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by uniq_by nsort_by/;
use Set::IntSpan;
use Set::IntSpan::Partition;
use List::Util qw/uniq/;
use JSON;
use List::OrderBy;
use List::StackBy;
use Acme::Partitioner;

has 'g' => (
  is       => 'ro',
  required => 1,
  weak_ref => 1,
);

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

has '_dbh' => (
  is       => 'rw',
  weak_ref => 1,
);

sub BUILD {
  my ($self) = @_;

  # FIXME(bh): stealing other module's dbh is bad
  $self->_dbh( $self->g->g->{dbh} );

  local $self->g->g->{dbh}->{sqlite_allow_multiple_statements} = 1;

  $self->_add_topological_attributes();
  $self->_log->debugf("done _add_topological_attributes");

  $self->_dbh->do(q{ ANALYZE });
}

local $Storable::canonical = 1;

sub _strongly_connected_graph_feather {
  my ($g) = @_;

  my @sccs = $g->strongly_connected_components;

  @$_ = sort @$_ for @sccs;

  my %v_to_id;
  my %h;
  
  for (my $ix = 0; $ix < @sccs; ++$ix) {
    $v_to_id{ $_ } = $ix for @{ $sccs[$ix] };
    $h{ $ix } = $sccs[$ix];
  }

  my $scg2 = Graph::Feather->new(
    vertices => [ map { join '+', @$_ } values %h ],
    edges    => [
      grep {
        $_->[0] ne $_->[1]
      }
      map {
        [ map { join '+', @{ $h{ $v_to_id{$_} } } } @$_ ]
      }
      $g->edges
    ],
  );

  return $scg2;
}

sub _scg_topological_depth {
  my ($d) = @_;

  my $scgf = _strongly_connected_graph_feather($d);

  # TOOD: make into VIEW

  my $result = $scgf->{dbh}->selectall_hashref(q{
    WITH RECURSIVE
    roots(vertex) AS (
      SELECT DISTINCT
        v.vertex_name AS vertex
      FROM
        vertex v
          LEFT JOIN Edge successors
            ON (successors.src = v.vertex_name)
          LEFT JOIN Edge predecessors
            ON (predecessors.dst = v.vertex_name)
      WHERE
        predecessors.src IS NULL
    ),
    dfs(vertex, depth) AS (
      SELECT
        vertex,
        0 AS depth
      FROM roots
      UNION ALL
      SELECT
        e.dst AS vertex,
        depth + 1 AS depth
      FROM dfs
        INNER JOIN Edge e
          ON (e.src = dfs.vertex)
    ),
    topology(vertex, max_depth, min_depth) AS (
      SELECT vertex, MAX(depth), MIN(depth) FROM dfs
      GROUP BY vertex
    )
    SELECT * FROM topology ORDER BY max_depth DESC
  }, 'vertex');

  for my $k (keys %$result) {
    next unless $k =~ /\+/;
    for my $v (split/\+/, $k) {
      # FIXME: clone?
      $result->{$v} = $result->{$k};
    }
  }

  return $result;
}

sub _topo_parent_child {
  my ($self) = @_;

  my $d = Graph::Directed->new;

  $d->add_vertices(
    map { @$_ } $self->_dbh->selectall_array(q{
      SELECT
        src_p.vertex
      FROM
        vertex_property src_p
    })
  );

  $d->add_edges(
    $self->_dbh->selectall_array(q{
      SELECT
        pc.parent AS parent,
        pc.child AS child
      FROM
        view_parent_child pc
          -- FIXME: no join needed here
          INNER JOIN vertex_property parent_p
            ON (pc.parent = parent_p.vertex)
          INNER JOIN vertex_property child_p
            ON (pc.child = child_p.vertex)

    })
  );

  return _scg_topological_depth($d);
}

sub _topo_epsilon {
  my ($self) = @_;

  my $d = Graph::Directed->new;

  $d->add_vertices(
    map { @$_ } $self->_dbh->selectall_array(q{
      SELECT
        src_p.vertex
      FROM
        vertex_property src_p
    })
  );

  $d->add_edges(
    $self->_dbh->selectall_array(q{
      SELECT
        src,
        dst
      FROM
        Edge
          INNER JOIN vertex_property src_p
            ON (src_p.vertex = Edge.src)
      WHERE
        src_p.type <> 'Input'
    })
  );

  return _scg_topological_depth($d)
}

sub _add_topological_attributes {
  my ($self) = @_;

  my $json = JSON->new
    ->canonical(1)
    ->ascii(1)
    ->indent(0);

  $self->_log->debugf("done _topo_epsilon");
  my $t1 = $self->_topo_epsilon();

  my $t2 = $self->_topo_parent_child();
  $self->_log->debugf("done _topo_parent_child");

  # FIXME: something to do with unreachable vertices?

  # TODO: instead of storing the whole epsilon_group,
  # associate the one_in_loop here.

  for ($self->g->g->vertices) {
    warn $_ unless defined $t1->{$_}{vertex};
    my @vertices = split/\+/, $t1->{$_}{vertex};
    next if @vertices == 1;
    $self->g->vp_epsilon_group($_,
      $json->encode([ @vertices ])
    );
  }

  my $helper = sub {
    my ($v) = @_;
    my @pred = $self->g->g->predecessors($v);
    my @succ = $self->g->g->successors($v);

    # TODO: simplify this code

    if ($self->g->is_if1_vertex($v)) {
      die unless @pred == 1;
      die unless $self->g->is_if_vertex(@pred);
      return $self->g->vp_name(@pred) eq '#ordered_choice';
    }

    if ($self->g->is_if2_vertex($v)) {
      die unless @pred == 1;
      die unless $self->g->is_if_vertex(@pred);
      return $self->g->vp_name(@pred) eq '#exclusion';
    }

    if ($self->g->is_fi1_vertex($v)) {
      die unless @succ == 1;
      die unless $self->g->is_fi_vertex(@succ);
      return $self->g->vp_name(@succ) eq '#ordered_choice';
    }

    if ($self->g->is_fi2_vertex($v)) {
      die unless @succ == 1;
      die unless $self->g->is_fi_vertex(@succ);
      return $self->g->vp_name(@succ) eq '#exclusion';
    }

    return 0;
  };

  my @order = order_by_desc {
    $t1->{$_}{max_depth} // warn
  } then_by_desc {
    $t2->{$_}{max_depth} // warn
  } then_by_desc {
    $t1->{$_}{min_depth} // warn
  } then_by_desc {
    $t2->{$_}{min_depth} // warn
  } then_by_desc {
    0 + $helper->($_)
  } $self->g->g->vertices();

#  @order = order_by_desc { rand() } @order;

  my @stacks = stack_by {
    join ',', $t1->{$_}{max_depth},
              $t1->{$_}{min_depth},
              $t2->{$_}{max_depth},
              $t2->{$_}{min_depth},
              0 + $helper->($_)
  } @order;

  while (@stacks) {
    my $current = shift @stacks;
    $self->g->vp_topo($_, 2 + $#stacks)
      for @$current
  }

}

1;

__END__
