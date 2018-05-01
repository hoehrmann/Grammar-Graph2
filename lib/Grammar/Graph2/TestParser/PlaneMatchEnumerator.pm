package Grammar::Graph2::TestParser::PlaneMatchEnumerator;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Graph::SomeUtils qw/:all/;
use Log::Any qw//;
use Types::Standard qw/:all/;
use Grammar::Graph2::TestParser::PlaneMatchEnumerator::Match;
use YAML::XS;

has 'g' => (
  is       => 'ro',
  required => 1,
);

has 'src_pos' => (
  is       => 'ro',
  required => 1,
);

has 'src_vertex' => (
  is       => 'ro',
  required => 1,
);

has 'dst_pos' => (
  is       => 'ro',
  required => 1,
);

has 'dst_vertex' => (
  is       => 'ro',
  required => 1,
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
);

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

has '_subgraph' => (
  is => 'rw', # FIXME
);

sub BUILD {
  my ($self) = @_;

#  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  # FIXME: interior vertices must not be irregular

  my @foo = $self->g->_dbh->selectall_array(q{
    WITH
    args AS (
      SELECT
        CAST(? AS INT) AS src_pos,
        CAST(? AS TEXT) AS src_vertex,
        CAST(? AS INT) AS dst_pos,
        CAST(? AS TEXT) AS dst_vertex
    )
    SELECT
      printf('[%u,"%u"]', result.src_pos, result.src_vertex) AS src,
      printf('[%u,"%u"]', result.dst_pos, result.dst_vertex) AS dst
    FROM
      result
        INNER JOIN args
        INNER JOIN view_vp_plus src_p
          ON (result.src_vertex = src_p.vertex)
        INNER JOIN view_vp_plus dst_p
          ON (result.dst_vertex = dst_p.vertex)
    WHERE
      result.src_pos BETWEEN args.src_pos AND args.dst_pos
      AND
      result.dst_pos BETWEEN args.src_pos AND args.dst_pos
      AND
      (result.src_vertex = args.src_vertex
        OR src_p.self_loop = 'no')
      AND
      (result.dst_vertex = args.dst_vertex
        OR dst_p.self_loop = 'no')
  }, {}, $self->src_pos, $self->src_vertex, $self->dst_pos, $self->dst_vertex);

  my $tmp = Graph::Feather->new(
    edges => [ @foo ],
  );

  my $src = sprintf('[%u,"%u"]', $self->src_pos, $self->src_vertex);
  my $dst = sprintf('[%u,"%u"]', $self->dst_pos, $self->dst_vertex);

  my @between = graph_vertices_between($tmp, $src, $dst);

  if (not @between) {
    warn "No vertices between $src and $dst";
  }

  # TODO(bh): check that `graph_vertices_between` returns
  # an empty list if there is no path between $src and $dst

  graph_delete_vertices_except($tmp, @between);
  $tmp->feather_delete_edges($tmp->edges_from($dst));

  $self->_subgraph($tmp);
}

sub _next_match {
  my ($self, $prev_match) = @_;
  return $self->_first_planar_path_between() unless defined $prev_match;
  return;
  ...
}

sub _first_planar_path_between {
  my ($self) = @_;

  my $tmp = $self->_subgraph;

  my $src = sprintf('[%u,"%u"]', $self->src_pos, $self->src_vertex);
  my $dst = sprintf('[%u,"%u"]', $self->dst_pos, $self->dst_vertex);

  my @match = $tmp->{dbh}->selectrow_array(q{
    SELECT
      Edge.rowid
    FROM
      Edge
    WHERE
      Edge.src = CAST(? AS TEXT)
    ORDER BY
      Edge.rowid
    LIMIT 1
  }, {}, $src);

  while (1) {
    # find first following Edge not yet in @match

    my ($next) = $self->_subgraph->{dbh}->selectrow_array(
      q{
        WITH
        args AS (
          SELECT
            CAST(? AS INT) AS last_rowid,
            CAST(? AS TEXT) AS all_rowids
        ),
        last AS (
          SELECT
            Edge.src AS src,
            Edge.dst AS dst
          FROM
            Edge
              INNER JOIN args
                ON (Edge.rowid = args.last_rowid)
        )
        SELECT
          Edge.rowid
        FROM
          Edge
            INNER JOIN last
        WHERE
          Edge.src = last.dst
          AND
          Edge.rowid NOT IN (
            SELECT
              CAST(each.value AS INT)
            FROM args
              INNER JOIN json_each(args.all_rowids) each
          )
        ORDER BY
          Edge.rowid
        LIMIT 1
      },
      {},
      $match[-1],
      $self->_json->encode(\@match)
    );

    last unless defined $next;
    push @match, $next;
  }

  my @tuples = $self->_subgraph->{dbh}->selectall_array(q{
    SELECT
      CAST(json_extract(Edge.src, '$[0]') AS INT) AS src_pos,
      CAST(json_extract(Edge.src, '$[1]') AS TEXT) AS src_vertex,
      CAST(json_extract(Edge.dst, '$[0]') AS INT) AS dst_pos,
      CAST(json_extract(Edge.dst, '$[1]') AS TEXT) AS dst_vertex
    FROM
      Edge
        INNER JOIN json_each(?) each
          ON (Edge.rowid = each.value)
  }, {}, $self->g->_json->encode(\@match));

  return Grammar::Graph2::TestParser::PlaneMatchEnumerator::Match->new(
    flat_path => [ @match ],
    tuples => [ @tuples ],
  );
}

1;

__END__

/*
    t_row AS (
      SELECT * FROM t WHERE t.rowid = ?
    )
    foo AS (
      SELECT
        mid_src_pos AS src_pos,
        mid_src_vertex AS src_vertex,
        mid_dst_pos AS dst_pos,
        mid_dst_vertex AS dst_vertex
      FROM
        t_row t
          INNER JOIN view_vp_plus mid_src_p
            ON (mid_src_p.vertex = t.mid_src_vertex)
      WHERE
        mid_src_p.is_push
      UNION
        sibling1
      UNION
        sibling2
    )
    
*/


            CAST(json_extract(Edge.src, '$[0]') AS INT) AS src_pos,
            CAST(json_extract(Edge.src, '$[1]') AS TEXT) AS src_vertex,
            CAST(json_extract(Edge.dst, '$[0]') AS INT) AS dst_pos,
            CAST(json_extract(Edge.dst, '$[1]') AS TEXT) AS dst_vertex
