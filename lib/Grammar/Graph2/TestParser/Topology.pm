package Grammar::Graph2::TestParser;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by uniq_by/;
use Set::IntSpan;
use Set::IntSpan::Partition;
use List::Util qw/uniq/;

local $Storable::canonical = 1;

sub _add_self_loop_attributes {
  my ($self) = @_;

  my @self_loop = $self->_dbh->selectall_array(q{
    SELECT vertex, self_loop
    FROM view_self_loop
  });

  $self->g->vp_self_loop(@$_)
    for @self_loop;
}

sub _scg_topological_depth {
  my ($d) = @_;

  my $scg = $d->strongly_connected_graph;
  my $scgf = Graph::Feather->new(
    vertices => [ $scg->vertices ],
    edges => [ $scg->edges ],
  );

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

  my $scg = $d->strongly_connected_graph;
  my $scgf = Graph::Feather->new(
    vertices => [ $scg->vertices ],
    edges => [ $scg->edges ],
  );

  return _scg_topological_depth($d)
}

sub _add_topological_attributes {
  my ($self) = @_;

  my $json = JSON->new
    ->canonical(1)
    ->ascii(1)
    ->indent(0);

  my $t1 = $self->_topo_epsilon();
  my $t2 = $self->_topo_parent_child();

  # FIXME: something to do with unreachable vertices?

  for ($self->g->g->vertices) {
    warn $_ unless defined $t1->{$_}{vertex};
    $self->g->vp_epsilon_group($_,
      $json->encode([ split/\+/, $t1->{$_}{vertex}])
    );
  }

  my @order = order_by_desc {
    $t1->{$_}{max_depth} // warn
  } then_by_desc {
    $t2->{$_}{max_depth} // warn
  } then_by_desc {
    $t1->{$_}{min_depth} // warn
  } then_by_desc {
    $t2->{$_}{min_depth} // warn
  } $self->g->g->vertices();

  my @stacks = stack_by {
    join ',', $t1->{$_}{max_depth},
              $t1->{$_}{min_depth},
              $t2->{$_}{max_depth},
              $t2->{$_}{min_depth}
  } @order;

  while (@stacks) {
    my $current = shift @stacks;
    $self->g->vp_topo($_, 2 + $#stacks)
      for @$current
  }

}

1;

__END__

