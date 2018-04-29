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

has '_dbh' => (
  is       => 'rw',
  required => 1,
);

has 'flat_path' => (
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

sub _build_list {
  my ($self, $todo, %o) = @_;

  my $e = shift @$todo;

  return unless defined $e;

  my $item = $self->_dbh->selectrow_hashref(q{
    SELECT
      t.rowid AS rowid,
      -- mid_src_p.is_push AS mid_src_is_push,
      mid_src_p.is_pop AS mid_src_is_pop,
      t.src_pos AS src_pos,
      t.src_vertex AS src_vertex,
      t.dst_pos AS dst_pos,
      t.dst_vertex AS dst_vertex
    FROM
      t
        INNER JOIN view_vp_plus src_p
          ON (src_p.vertex = t.src_vertex)
        INNER JOIN view_vp_plus dst_p
          ON (dst_p.vertex = t.dst_vertex)
        LEFT JOIN view_vp_plus mid_src_p
          ON (mid_src_p.vertex = t.mid_src_vertex)
    WHERE
      t.rowid = ?
  }, {}, $e);

  my @children = (
    _build_list($self, $todo, %o),
    _build_list($self, $todo, %o),
  );

  if ($item->{mid_src_is_pop}) {
    return @children;
  }

  return
    [ $item->{src_pos}, $item->{src_vertex} ],
    @children,
    [ $item->{dst_pos}, $item->{dst_vertex} ],
  ;
    
}

sub _build_tree_from_vertex_list {
  my ($self, $list, %o) = @_;

  my @augmented = $self->_dbh->selectall_array(q{
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
  }, {}, $self->_json->encode($list));

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
      die $stack[-1][0] . ' vs ' . $current->[4]
        unless $stack[-1][0] eq $current->[4];
      pop @stack;
    } else {

    }
  }

  return $result->[1]->[0];
}

sub _build_tree {
  my ($self, $todo, %o) = @_;
  my @list = $self->_build_list($todo);

  return $self->_build_tree_from_vertex_list(\@list, %o);
}

sub to_tree {
  my ($self, %o) = @_;

  die if grep {
    $_ !~ /^(pruned|rowids)$/
  } keys %o;

  my $node = _build_tree($self, [ @{ $self->flat_path } ], %o);

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

__END__

