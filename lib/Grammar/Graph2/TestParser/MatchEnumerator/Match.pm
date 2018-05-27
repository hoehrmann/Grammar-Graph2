package Grammar::Graph2::TestParser::MatchEnumerator::Match;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use YAML::XS;

has 'g' => (
  is       => 'ro',
  required => 1,
);

has 'plane_enumerators' => (
  is       => 'ro',
  required => 1,
);

has 'plane_matches' => (
  is       => 'ro',
  required => 1,
);

has 'tree_enumerator' => (
  is       => 'ro',
  required => 1,
);

has 'tree_match' => (
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

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

sub flat_path { [] }

sub _build_tree_from_vertex_list {
  my ($g, $list, %o) = @_;

  my @augmented = $g->_dbh->selectall_array(q{
    WITH
    base AS (
      SELECT
        each.key AS sort_key,
        CAST(json_extract(each.value, '$[0]') AS INT) AS pos,
        CAST(json_extract(each.value, '$[1]') AS TEXT) AS vertex
      FROM
        json_each(?) each
    )
    SELECT
      base.pos AS src_pos,
      base.vertex AS src_vertex,
      vertex_p.is_push,
      vertex_p.is_pop,
      COALESCE(vertex_p.name, '') AS name
    FROM
      base
        INNER JOIN view_vp_plus vertex_p
          ON (vertex_p.vertex = base.vertex)
    ORDER BY
      base.sort_key
  }, {}, $g->_json->encode($list));

  my $result = [];
  my @stack = ($result);

  while (@augmented) {
    my $current = shift @augmented;
    if ($current->[2]) {
      push @{ $stack[-1][1] },
        [ $current->[4], [], $current->[0] ];
      push @stack, $stack[-1][1][-1];
    } elsif ($current->[3]) {
      $stack[-1][3] = $current->[0];
      die $stack[-1][0] . ' vs ' . $current->[4] . ' ' . Dump({
        list => $list,
      })
        unless $stack[-1][0] eq $current->[4];
      pop @stack;
    } else {

    }
  }

  return $result->[1]->[0];
}

sub _build_tree {
  my ($self, $todo, %o) = @_;
  my @list = $self->to_list;

  return _build_tree_from_vertex_list($self->g, \@list, %o);
}

sub to_list {
  my ($self) = @_;

  my @tree_list = $self->tree_match->to_list;
  my @plane_lists = map { [ $_->to_list ] } @{ $self->plane_matches };
  my @result;

=pod

    use YAML::XS;
    warn Dump {
      tree_list => \@tree_list,
      plane_lists => \@plane_lists,
      result => \@result
    };

=cut

  while (@plane_lists) {
    my @middle = @{ shift @plane_lists };
    shift @middle;
    pop @middle;
    push @result, shift(@tree_list), @middle;
  }

  push @result, shift(@tree_list);

  warn if grep { not defined } @result;

=pod

  if (@tree_list) {
    use YAML::XS;
    die Dump {
      tree_list => \@tree_list,
      result => \@result
    };
  }

=cut

  return @result;
}

sub to_tree {
  my ($self, %o) = @_;

  die if grep {
    $_ !~ /^(pruned)$/
  } keys %o;

  my $node = _build_tree($self, [ $self->to_list ], %o);

  if ($o{pruned}) {
    $node->[1] = [ map { _pruned($_) } @{ $node->[1] } ];
  }

  return $node;  
}

sub to_json_tree {
  my ($self, %o) = @_;

  my $node = $self->to_tree(%o);

  my $result = _to_json_tree($node, 0);

  $result =~ s/,$//;

  return $result;
}

sub tree_match_to_tree {
  my ($self, %o) = @_;

  my $node = _build_tree_from_vertex_list(
    $self->g, [ $self->tree_match->to_list ]);

  return $node;
}

sub tree_match_to_json_tree {
  my ($self, %o) = @_;

  my $node = _build_tree_from_vertex_list(
    $self->g, [ $self->tree_match->to_list ]);

  my $result = _to_json_tree($node, 0);

  $result =~ s/,$//;

  return $result;
}

sub _pruned {
  my ($node) = @_;

  # TODO: easier to filter match vertex list

  return $node unless @$node;

  return map { _pruned($_) } @{ $node->[1] }
    unless $node->[0] =~ /^[^:#]+/;

  return [
    $node->[0],
    [ map { _pruned($_) } @{ $node->[1] } ],
    $node->[2],
    $node->[3],
  ]
}

sub _to_json_tree {
  my ($tree, $depth) = @_;

  my ($name, $children, $src_pos, $dst_pos) = @$tree;

  return '' unless @$tree;

  my $result = sprintf qq{\n%*s["%s", [}, $depth*2, '', ($name // '');
  $result .= _to_json_tree($_, $depth+1) for @$children;
  $result .= sprintf qq{], %u, %u],}, $src_pos, $dst_pos;

  $result =~ s/,\]/]/sg;

  return $result;
}

1;

