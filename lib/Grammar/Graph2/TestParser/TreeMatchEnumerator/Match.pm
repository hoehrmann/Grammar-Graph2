package Grammar::Graph2::TestParser::TreeMatchEnumerator::Match;
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

sub to_list {
  my ($self) = @_;

  return $self->_build_list([ @{ $self->flat_path } ]);
}


1;

__END__

