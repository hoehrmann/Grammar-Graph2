package Grammar::Graph2::TestParser::MatchEnumerator;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use Grammar::Graph2::TestParser::TreeMatchEnumerator;
use Grammar::Graph2::TestParser::PlaneMatchEnumerator;
use Grammar::Graph2::TestParser::TreeMatchEnumerator::Match;
use Grammar::Graph2::TestParser::MatchEnumerator::Match;
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

sub all_matches {
  my ($self) = @_;
  my @result;

  for (my $match; $match = $self->_next_match($match);) {

#warn $match->to_json_tree;

    push @result, $match;
  }

  return @result;
}

sub _first_match_from_tree_match {
  my ($self, $tree_enum, $tree_match) = @_;

  return unless $tree_match;

  my @tree_list = $tree_match->to_list;

  if (not @tree_list) {
    die;
    return;
  }

  my @plane_enums;

  for (my $ix = 1; $ix <= $#tree_list; ++$ix) {
    my $src = $tree_list[ $ix - 1 ];
    my $dst = $tree_list[ $ix - 0 ];
    
    my $plane_enum = Grammar::Graph2::TestParser::PlaneMatchEnumerator->new(
      g => $self->g,
      src_pos => $src->[0],
      src_vertex => $src->[1],
      dst_pos => $dst->[0],
      dst_vertex => $dst->[1],
    );

    push @plane_enums, $plane_enum;
  }

  my @plane_matches = map { scalar $_->_next_match() } @plane_enums;

  if (grep { not defined } @plane_matches) {
    warn Dump {
#      plane_matches => \@plane_matches,
#      plane_enums => \@plane_enums,
    } if 0;

    # Since #ordered_choice conditionals are not fully resolved by
    # the main parsing algorithm, and instead it removes some edges
    # in the result afterwards, it is possible that a tree match is
    # invalid, in which case matches in the plane will be absent 
    # and then we end up here. We then try with the next tree match.

    return; # Note above ^ should be obsolete now

    return $self->_first_match_from_tree_match($tree_enum,
      $tree_enum->_next_match($tree_match));
  }

  return Grammar::Graph2::TestParser::MatchEnumerator::Match->new(
    g => $self->g,
    tree_enumerator => $tree_enum,
    tree_match => $tree_match,
    plane_enumerators => [ @plane_enums ],
    plane_matches => [ @plane_matches ],
  );
}

sub _next_match {
  my ($self, $prev_match) = @_;

  if (not defined $prev_match) {
    my $tree_enum = Grammar::Graph2::TestParser::TreeMatchEnumerator->new(
      %$self,
    );

    my $tree_match = $tree_enum->_next_match();

    if (not $tree_match) {
      return;
    }

    return $self->_first_match_from_tree_match($tree_enum,
      $tree_match);
  }

  my @plane_matches = @{ $prev_match->plane_matches };
  my $tree_match = $prev_match->tree_match;

  for (my $ix = $#plane_matches; $ix >= 0; --$ix) {
    my $match = $plane_matches[ $ix ];
    $plane_matches[ $ix ] = $prev_match->plane_enumerators
      ->[ $ix ]->_next_match($match);
    
    last if defined $plane_matches[ $ix ];
    if ($ix == 0) {

      # cannot increment plane matches, so increment tree match

#      warn "#### tree next";
      $tree_match = $prev_match->tree_enumerator->_next_match(
        $prev_match->tree_match
      );
#      warn "### FOUND";

      return unless $tree_match;

=pod

      use YAML::XS;
      warn Dump {
        prev => $prev_match->tree_match,
        next => $tree_match,
      };

=cut

      return $self->_first_match_from_tree_match(
        $prev_match->tree_enumerator,
        $tree_match,
      );
    }

    $plane_matches[ $ix ] = $prev_match->plane_enumerators
      ->[ $ix ]->_next_match();
  }

  return Grammar::Graph2::TestParser::MatchEnumerator::Match->new(
    g => $self->g,
    tree_enumerator => $prev_match->tree_enumerator,
    tree_match => $tree_match,
    plane_enumerators => $prev_match->plane_enumerators,
    plane_matches => [ @plane_matches ],
  );
}

sub random_match {
  my ($self) = @_;

  return $self->_next_match(); # FIXME: not very random

#  Grammar::Graph2::TestParser::TreeMatchEnumerator->new(
#    %$self
#  )->random_match;
}

1;

__END__

sub BUILD {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

}

sub random_match {
  my ($self) = @_;

  return $self->_find_next_path_between(
    "random",
    $self->src_pos,
    $self->src_vertex,
    $self->dst_pos,
    $self->dst_vertex
  );
}

sub _first_match {
  my ($self) = @_;

  return $self->_find_next_path_between(
    "next",
    $self->src_pos,
    $self->src_vertex,
    $self->dst_pos,
    $self->dst_vertex
  );
}

sub _first_planar_path_between {
  my ($self, $src_pos, $src_vertex, $dst_pos, $dst_vertex) = @_;

  my @foo = $self->_dbh->selectall_array(q{
    WITH bounds AS (
      SELECT CAST(? AS INT) AS lower,
      SELECT CAST(? AS INT) AS upper
    )
    SELECT
      printf('[%u,"%u"]', src_pos, src_vertex) AS src,
      printf('[%u,"%u"]', dst_pos, dst_vertex) AS dst
    FROM
      result
    WHERE
      src_pos BETWEEN bounds.lower AND bounds.upper
      AND
      dst_pos BETWEEN bounds.lower AND bounds.upper
  }, {}, $src_pos, $dst_pos);

  my $tmp = Graph::Feather->new(
    edges => [ @foo ],
  );

  my $src = sprintf('[%u,"%u"]', $src_pos, $src_vertex);
  my $dst = sprintf('[%u,"%u"]', $dst_pos, $dst_vertex);

  my @between = graph_vertices_between($tmp, $src, $dst);

  die unless @between;

  # TODO(bh): check that `graph_vertices_between` returns
  # an empty list if there is no path between $src and $dst

  graph_delete_vertices_except($tmp, @between);
  $tmp->feather_delete_edges($tmp->edges_from($dst));

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

    my ($next) = $self->_dbh->selectrow_array(
      q{
        WITH
        args AS (
          SELECT
            CAST(? AS INT) AS last_rowid,
            CAST(? AS TEXT) AS all_rowids
        ),
        last AS (
          SELECT
            Edge.src AS src
            Edge.dst AS dst,
          FROM
            args
              INNER JOIN Edge
                ON (args.last_rowid = Edge.rowid)
        )
        SELECT
          Edge.rowid
        FROM
          Edge
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
  }

  return @match;
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
