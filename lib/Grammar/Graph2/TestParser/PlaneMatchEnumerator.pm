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
  weak_ref => 1,
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
  weak_ref => 1,
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

sub _src {
  my ($self) = @_;
  return sprintf('[%u,"%u"]', $self->src_pos, $self->src_vertex);
}

sub _dst {
  my ($self) = @_;
  return sprintf('[%u,"%u"]', $self->dst_pos, $self->dst_vertex);
}

sub BUILD {
  my ($self) = @_;

#  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

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

  my @between = graph_vertices_between($tmp, $self->_src, $self->_dst);

  if (not @between) {
    warn "No vertices between src and dst";
  }

  # TODO(bh): check that `graph_vertices_between` returns
  # an empty list if there is no path between $src and $dst

  graph_delete_vertices_except($tmp, @between);

  # FIXME: unsure about this
  $tmp->feather_delete_edges($tmp->edges_from($self->_dst))
    unless $self->_dst eq $self->_src;

  $self->_subgraph($tmp);
}

sub _next_match {
  my ($self, $prev_match) = @_;

  return undef unless $self->_subgraph->has_vertex($self->_src);

  if (not defined $prev_match) {
    my @match = $self->_first_rowid();
    return $self->_next_planar_path_between(undef, @match);
  }

#  return;

  my @path = @{ $prev_match->flat_path };
  my @old_path = @path;

  while (@path) {

#    warn "trying to replace at $#path";

    my $last_rowid = pop @path;

    my $match = $self->_next_planar_path_between(
      $last_rowid, @path);

    if ($match) {
      my @new_path = @{ $match->flat_path };
#      warn "found match\n  old: @old_path\n  new: @new_path";
      return $match;
    }

  }

  return undef;
}

sub _first_rowid {
  # TODO: add parameter for "random/ordered"
  my ($self) = @_;

  my @match = $self->_subgraph->{dbh}->selectrow_array(q{
    WITH
    args AS (
      SELECT
        CAST(? AS TEXT) AS start
    )
    SELECT
      Edge.rowid
    FROM
      Edge
        INNER JOIN args
    WHERE
      Edge.src = args.start
    ORDER BY
      Edge.rowid ASC
    LIMIT 1
  }, {}, $self->_src);

  return @match;  
}

sub _next_planar_path_between {
  # TODO: add parameter for "random/ordered"
  my ($self, $first_must_not_be, @match) = @_;

  while (1) {
    # find first following Edge not yet in @match

    my ($next) = $self->_subgraph->{dbh}->selectrow_array(
      q{
        WITH
        args AS (
          SELECT
            CAST(? AS INT) AS blocked_rowid,
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
            INNER JOIN args
        WHERE
          Edge.src = last.dst
          AND
          Edge.rowid NOT IN (
            SELECT
              CAST(each.value AS INT)
            FROM args
              INNER JOIN json_each(args.all_rowids) each
          )
          AND (
            args.blocked_rowid IS NULL
            OR
            args.blocked_rowid < Edge.rowid
          )
        ORDER BY
          Edge.rowid ASC
        LIMIT 1
      },
      {},
      $first_must_not_be,
      $match[-1],
      $self->_json->encode(\@match)
    );

    last unless defined $next;

#    warn "adding $next to @match";

    push @match, $next;

    $first_must_not_be = undef;
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
    ORDER BY 
      each.key
  }, {}, $self->g->_json->encode(\@match));

#  warn "found tuples" if @tuples;

  # no match found
  return unless
    @tuples
    and
    $tuples[-1][2] == $self->dst_pos 
    and
    $tuples[-1][3] == $self->dst_vertex;

#  warn "found match";

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
