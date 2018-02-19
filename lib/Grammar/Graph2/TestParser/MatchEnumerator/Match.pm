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

sub _build_tree {
  my ($self, $todo, %o) = @_;

  my $e = shift @$todo;

  return unless defined $e;

  my $item = $self->_dbh->selectrow_hashref(q{
    SELECT
      t.rowid AS rowid,
      mid_src_p.is_push AS mid_src_is_push,
      mid_src_p.is_pop AS mid_src_is_pop,
      src_p.name AS src_name,
      t.*
    FROM
      t
        INNER JOIN vertex_property src_p
          ON (src_p.vertex = t.src_vertex)
        LEFT JOIN vertex_property mid_src_p
          ON (mid_src_p.vertex = t.mid_src_vertex)
    WHERE
      t.rowid = ?
  }, {}, $e);

  my @children = (
    _build_tree($self, $todo, %o),
    _build_tree($self, $todo, %o),
  );

  return [
    (!$item->{mid_src_is_pop}
      ? ($item->{src_name} // '')
      : '') . ( $o{rowids} ? (':' . $e) : '' ),

    \@children,
    $item->{src_pos},
    $item->{dst_pos},
  ];
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

