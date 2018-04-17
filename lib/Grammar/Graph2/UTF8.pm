package Grammar::Graph2::UTF8;
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
use JSON;
use List::OrderBy;
use List::StackBy;
use Unicode::SetAutomaton;

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

sub BUILD {
  my ($self) = @_;

  my @sets = $self->g->_dbh->selectall_array(q{
    SELECT
      class,
      group_concat((min || '-' || max), ',') AS ranges
    FROM
      input_class
    GROUP BY
      class
  });

  my $dfa = Unicode::SetAutomaton->new(classes => [
    Set::IntSpan->new(), # empty
    map { Set::IntSpan->new($_->[1]) } @sets
  ]);

  # With empty alphabets, @sets might be empty aswell.
  die if @sets and $sets[0]->[0] ne '1';

  # FIXME: make Unicode::SetAutomaton guarantee this
  die unless $dfa->{start_state} eq '0';

  my %renumbering;
  for my $state (keys %{ $dfa->{state_to_disjoint} }) {
    my $dset = $dfa->{state_to_disjoint}->{$state};
    my $sets = $dfa->{disjoint_to_input}->[$dset];
    die if 1 != @$sets;
    my ($set) = @$sets;
    $renumbering{$state} = $set;
  }

  my @transitions;
  for (@{ $dfa->{transitions} }) {
    $renumbering{ $_->[3] } //= keys %renumbering;
    $renumbering{ $_->[0] } //= keys %renumbering;
    push @transitions, [
      $renumbering{ $_->[0] },
      $_->[1],
      $_->[2],
      $renumbering{ $_->[3] }
    ];
  }

  $self->g->_dbh->do(q{
    DROP TABLE IF EXISTS utf8_dfa;
  });

  $self->g->_dbh->do(q{
    CREATE TABLE utf8_dfa AS 
    SELECT
      CAST( json_extract(e.value, '$[0]') AS INT ) AS 'src',
      CAST( json_extract(e.value, '$[1]') AS INT ) AS 'min',
      CAST( json_extract(e.value, '$[2]') AS INT ) AS 'max',
      CAST( json_extract(e.value, '$[3]') AS INT ) AS 'dst'
    FROM
      json_each(?) e
  }, {}, $self->g->_json->encode(\@transitions));

  $self->g->_dbh->do(q{
    CREATE UNIQUE INDEX idx_utf8_dfa
      ON utf8_dfa(src, min, max, dst)
  });

  # In utf8_dfa MIN(src) is the start_state and each state with a
  # lesser value is equal to the corresponding input_class.class.
  # Such states do not have outgoing transitions by convention of
  # Unicode::SetAutomaton, but to use it in a loop or recursion,
  # it is useful to have them, so copy them from the start_state.
  $self->g->_dbh->do(q{
    WITH
    start_state AS (
      SELECT MIN(src) AS state
      FROM utf8_dfa AS state
    ),
    start_transitions AS (
      SELECT
        utf8_dfa.src AS src,
        utf8_dfa.min AS min,
        utf8_dfa.max AS max,
        utf8_dfa.dst AS dst
      FROM utf8_dfa
        INNER JOIN start_state
          ON (start_state.state = utf8_dfa.src)
    )
    INSERT INTO utf8_dfa(src, min, max, dst)
    SELECT
      foo.dst,
      start_transitions.min,
      start_transitions.max,
      start_transitions.dst
    FROM
      (SELECT DISTINCT dst FROM utf8_dfa) foo
        INNER JOIN start_transitions
          ON (foo.dst < start_transitions.src)
  });

  return;

  use YAML::XS;
  warn Dump [
    map { $self->g->_json->encode($_) } @transitions
  ];

}

1;

__END__

