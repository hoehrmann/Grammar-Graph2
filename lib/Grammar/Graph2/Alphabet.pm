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
use List::Util qw/uniq/;

local $Storable::canonical = 1;

has 'g' => (
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

sub first_ords {
  my ($self) = @_;

  my @spans = 
    map { Set::IntSpan->new($_) }
    grep { defined }
    map {
      $self->g->vp_run_list($_)
    } $self->g->g->vertices;

  return
    uniq
    map { $_->first }
    map { @$_ }
    values %{{ intspan_partition_map( @spans ) }};
}

1;

__END__

