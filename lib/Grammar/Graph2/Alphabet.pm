package Grammar::Graph2::Alphabet;
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
use List::Util qw/uniq first/;

local $Storable::canonical = 1;

has 'g' => (
  is       => 'ro',
  required => 1,
);

has '_ord_to_list' => (
  is       => 'ro',
  writer   => '_set_ord_to_list',
);

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

sub BUILD {
  my ($self) = @_;

  my @spans = 
    map { Set::IntSpan->new($_) }
    uniq_by { $_ }
    grep { defined }
    map {
      $self->g->vp_run_list($_)
    } $self->g->g->vertices;

  my $first = sub {
    my ($set) = @_;
    return if $set->empty;
    my ($span) = $set->spans;
    return first { defined } @$span, 0;
  };

  my %h;

  $self->_set_ord_to_list(\%h);

  for (map { @$_ } values %{ { intspan_partition_map( @spans ) } }) {
    $h{ $first->($_) } = $_->run_list;
  }

}

sub first_ords {
  my ($self) = @_;

  return keys %{ $self->_ord_to_list };
}

1;

__END__

