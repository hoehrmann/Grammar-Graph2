package Grammar::Graph2::TestParser::PlaneMatchEnumerator::Match;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;

has 'flat_path' => (
  is       => 'ro',
  required => 1,
);

has 'tuples' => (
  is       => 'ro',
  required => 1,
);

sub to_list {
  my ($self) = @_;
  
  my @list = @{ $self->tuples };

  return unless @list;

  my @result = map {
    [ $_->[0], $_->[1] ],
  } @list;

  return @result, [ $list[-1]->[2], $list[-1]->[3] ];
}

1;

__END__
