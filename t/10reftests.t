BEGIN {
  use lib '/home/bjoern/parselov/Grammar-Graph/lib';
  use lib '/home/bjoern/parselov/Grammar-Formal/lib';
  use lib '/home/bjoern/parselov/Parse-ABNF/lib';
  use lib '/home/bjoern/parselov/Graph-SomeUtils/lib';
  use lib '/home/bjoern/parselov/Graph-Feather/lib';
  use lib '/home/bjoern/parselov/Grammar-Graph2/lib';
  use lib '/home/bjoern/parselov/Algorithm-ConstructDFA2/lib';

};

package main;
use strict;
use warnings;
use 5.024000;

use Parse::ABNF 0.20;
use Grammar::Formal 0.20;
use Grammar::Graph 0.20;
use Grammar::Graph::Simplify;
use List::Util qw/min max shuffle/;
use List::MoreUtils qw/uniq/;
use List::UtilsBy qw/partition_by sort_by/;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve/;
use YAML::XS;
use JSON;

use File::Basename;
use File::Spec;

use Grammar::Graph2::TestParser;
use Grammar::Graph2::TestSeries;
use Grammar::Graph2::TestCase;
use JSON;

use Test::More;

use Log::Log4perl;
use Log::Any::Adapter;
Log::Log4perl::init(\'

log4perl.category = DEBUG, Screen
log4perl.appender.Screen        = Log::Log4perl::Appender::Screen
log4perl.appender.Screen.layout = \
  Log::Log4perl::Layout::PatternLayout
log4perl.appender.Screen.layout.ConversionPattern = \
  %d{yyyy-MM-ddTHH:mm:ss.SSS} %-50M %m{indent}%n

');
Log::Any::Adapter->set('Log4perl');

my (@filter) = @ARGV;

my @dirs = File::Find::Rule
    ->directory()
    ->name('*')
    ->in( File::Basename::dirname($0) . '/../data/reftests/' );

for my $dir (sort @dirs) {

  next unless not(@filter) or grep { $dir =~ /\Q$_\E/ } @filter;

  my $ts = Grammar::Graph2::TestSeries->new(
    base_path => $dir,
  );

  $ts->g->_dbh->sqlite_backup_to_file( $ts->basename . '.sqlite' );

  for my $input_path ( sort $ts->input_file_paths ) {

    eval {
      my $case = Grammar::Graph2::TestCase->new(
        series => $ts,
        input_path => $input_path,
      );

      my $path_prefix = $ts->base_path . '/' . $case->basename;

      my $got = $case->parse_to_ref_data();

      my $expected = do {
        open my $f, '<', $path_prefix . '.outref';
        local $/;
        JSON->new->decode(<$f>);
      };

      for my $set (qw/all_matches_signatures random_matches_signatures/) {

        my $mix = 0;

        for my $m (@{ $expected->{$set} }) {

          my ($is_subset) = $got->{p}->_dbh->selectrow_array(q{
            WITH
            args AS (
              SELECT ? AS sig
            ),
            decoded AS (
              SELECT
                JSON_EXTRACT(d.value, '$[0]') AS src_pos,
                JSON_EXTRACT(d.value, '$[1]') AS src_type,
                JSON_EXTRACT(d.value, '$[2]') AS src_name,
                JSON_EXTRACT(d.value, '$[3]') AS dst_pos,
                JSON_EXTRACT(d.value, '$[4]') AS dst_type,
                JSON_EXTRACT(d.value, '$[5]') AS dst_name
              FROM
                args  
                  INNER JOIN json_each(args.sig) d
            ),
            only_sig AS (
              SELECT 
                *
              FROM
                decoded
              EXCEPT
              SELECT
                *
              FROM
                alx_all_edges_signature
            )
            SELECT
              COUNT(*) = 0 AS is_subset
            FROM
              only_sig
          }, {}, JSON->new->encode($m));

          is( $is_subset, 0, "$path_prefix $set $mix signature is subset" );

          $mix += 1;

        }

      }

      is_deeply(
        $got->{all_matches_signatures},
        $expected->{all_matches_signatures} // [], 
        $path_prefix . ' all_matches_signatures'
      ) or diag(
        Dump {
          got => $got->{all_matches_signatures},
          expected => $expected->{all_matches_signatures}
        }
      );

      is_deeply $got->{all_matches},
        $expected->{all_matches},
        $path_prefix . ' all_matches' or diag(
          Dump {
            got => $got->{all_matches},
            expected => $expected->{all_matches}
          }
        );
  #
  #    is_deeply $got->{grammar_self_loops},
  #      $expected->{grammar_self_loops},
  #      $path_prefix . ' grammar_self_loops' or diag(
  #        Dump {
  #          expected => $expected->{grammar_self_loops},
  #          got => $got->{grammar_self_loops},
  #        }
  #      );

    };

    fail("exception in $input_path: $@") if $@;

  }

}

done_testing();

__END__

Grammar::Graph2::Test::RefTestRunner

