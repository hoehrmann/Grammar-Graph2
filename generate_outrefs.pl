BEGIN {
  use lib '../Grammar-Graph/lib';
  use lib '../Grammar-Formal/lib';
  use lib '../Parse-ABNF/lib';
  use lib '../Graph-SomeUtils/lib';
  use lib '../Graph-Feather/lib';
  use lib '../Grammar-Graph2/lib';
  use lib '../Algorithm-ConstructDFA2/lib';
};

package main;
use strict;
use warnings;
use 5.024;
use List::Util qw/min max shuffle/;
use List::MoreUtils qw/uniq/;
use List::UtilsBy qw/partition_by sort_by/;
use Modern::Perl;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve/;
use YAML::XS;
use JSON;
use Encode;
use Digest::MD5 qw/md5_hex/;
use Data::Dumper;
use File::Basename;
use File::Copy;
use File::Spec;

use Grammar::Graph2::TestParser;
use Grammar::Graph2::TestSeries;
use Grammar::Graph2::TestCase;

local $Storable::canonical = 1;

# my @dirs = <./data/reftests/alxbug>;
my @dirs = <./data/reftests/*>;

for my $dir (@dirs) {

  my @files = File::Find::Rule
    ->file()
    ->name( qr/^.*\.input$/ )
    ->in( $dir );

  for my $input_path (@files) {

    my $contents = do {
      local $/;
      open my $f, '<', $input_path;
      <$f>;
    };

    my $md5 = md5_hex($contents);

    my $old_basename =
      File::Basename::basename($input_path, '.input');

    my $old_dirname = File::Basename::dirname($input_path);

    my $new_path = $old_dirname . '/' . 't' . $md5 . '.input';

    next if $new_path eq $input_path;

    say "moving $input_path to $new_path";

    File::Copy::move( $input_path, $new_path );

    next;

    die Dumper {
      input_path => $input_path,
      dir => $dir,
      old_basename => $old_basename,
      old_dirname => $old_dirname,
      new_path => $new_path,
    };



  }

}

for my $dir (@dirs) {

  my $ts = Grammar::Graph2::TestSeries->new(
    base_path => $dir,
  );

  $ts->g->g->{dbh}->sqlite_backup_to_file('TEST.sqlite');

#  say $ts->options->{startrule};

  for my $input_path ( $ts->input_file_paths ) {
    say "Reading $input_path";

    my $case = Grammar::Graph2::TestCase->new(
      series => $ts,
      input_path => $input_path,
    );

    # TODO(bh): find .outref files with no corresponding .input

    my $ref = $case->parse_to_ref_data();

    my $out_path = $ts->base_path . '/' . $case->basename . '.outref';

    say "generating $out_path";

    open my $outref, '>', $out_path;
    print $outref JSON->new->canonical(1)->ascii(1)->indent(1)->encode($ref);
    close $outref;

  }
}

__END__
