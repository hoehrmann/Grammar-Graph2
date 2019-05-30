package Grammar::Graph2::TestCase;
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
use File::Spec qw//;
use Parse::ABNF;
use File::Find::Rule;
use List::UtilsBy qw/partition_by sort_by uniq_by/;
use File::Basename qw//;

use Grammar::Graph2::TestParser;
use Grammar::Graph2::TestParser::MatchEnumerator;

local $Storable::canonical = 1;

has 'series' => (
  is       => 'ro',
  required => 1,
  weak_ref => 1,
);

has 'input_path' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
);

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

sub basename {
  my ($self) = @_;

  return File::Basename::basename($self->input_path, '.input');
}

sub parse_to_ref_data {
  my ($self) = @_;

  my $p = Grammar::Graph2::TestParser->new(
    g => $self->series->g,
    input_path => $self->input_path,
  );

  $p->create_t();

#  $p->_dbh->sqlite_backup_to_file('TEST.sqlite');

  my $e = $p->create_match_enumerator();

  my @all_matches =
    grep { defined } $self->series->options->{enumerate_all_paths} ?
      $e->all_matches() : ();

  my @random_matches = map {
    $e->random_match()
  } 1 .. 32;

  return {
    p => $p,
    random_matches => [
      sort_by {
        Storable::freeze(\$_)
      } uniq_by {
        Storable::freeze(\$_)
      } map {
        $_->to_tree(pruned => 1)
      } grep {
        defined
      } @random_matches
    ],
    all_matches => [
      sort_by {
        Storable::freeze(\$_)
      } uniq_by {
        Storable::freeze(\$_)
      } map {
        $_->to_tree(pruned => 1)
      } grep {
        defined
      } @all_matches
    ],
    random_matches_signatures => [
      sort_by {
        Storable::freeze(\$_)
      } uniq_by {
        Storable::freeze(\$_)
      } map {
        $_->signature_from_vertex_list()
      } grep {
        defined
      } @random_matches
    ],
    all_matches_signatures => [
      sort_by {
        Storable::freeze(\$_)
      } uniq_by {
        Storable::freeze(\$_)
      } map {
        $_->signature_from_vertex_list()
      } grep {
        defined
      } @all_matches
    ],
    grammar_self_loops => $p->_dbh->selectall_arrayref(q{
      SELECT 
        name,
        MIN(self_loop)
      FROM
        vertex_property
      WHERE
        type in ('Start', 'Final')
        AND
        name <> ''
      GROUP BY
        name
      ORDER BY
        name
    }),
  };
}

1;

__END__

