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

  return {
    parent_child_signature => $p->_dbh->selectall_arrayref(q{
      SELECT 
        parent_start_pos,
        parent_start_name,
        first_child_pos,
        first_child_name,
        last_child_pos,
        last_child_name,
        parent_final_pos,
        parent_final_name
      FROM
        view_parent_child_signature
    }),
    sibling_signature => $p->_dbh->selectall_arrayref(q{
      SELECT 
        lhs_final_pos,
        lhs_final_name,
        rhs_start_pos,
        rhs_start_name
      FROM
        view_sibling_signature
    }),
    random_matches => [
      sort_by {
        Storable::freeze(\$_)
      } uniq_by {
        Storable::freeze(\$_)
      } map {
        $_->to_tree(pruned => 1)
      } grep {
        defined
      } map {
        $e->random_match()
      } 1 .. 32
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
    }),
  };
}

1;

__END__

