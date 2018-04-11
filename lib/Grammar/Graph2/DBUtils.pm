package Grammar::Graph2::DBUtils;
use strict;
use warnings;
use 5.024000;
use Moo;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use File::Spec qw//;
use List::UtilsBy qw/partition_by sort_by nsort_by uniq_by/;
use List::MoreUtils qw/uniq/;
use YAML::XS;
use Memoize;

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

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

has 'table_prefix' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    'm_'
  },
);

sub BUILD {
  my ($self) = @_;
}

sub views_to_tables {
  my ($self, @views) = @_;
  my $seen = {};
  $self->_view_to_table($_, $seen) for @views;
}

sub _view_to_table {
  my ($self, $view_name, $seen) = @_;

  my $prefix = $self->table_prefix;

  my $table_name = $prefix . $view_name;

  $self->_log->debugf("materialising %s as %s",
    $view_name, $table_name);

  my $quoted_table_name = $self->g->_dbh->quote_identifier(undef,
    'main', $table_name);

  my $quoted_view_name = $self->g->_dbh->quote_identifier(undef,
    'main', $view_name);

  local $self->g
    ->_dbh->{sqlite_allow_multiple_statements} = 1;

  my @view_names = map { @$_ } $self->g->_dbh->selectall_array(q{
    SELECT
      name
    FROM
      sqlite_master
    WHERE
      type = 'view'
  });

  my $view_regex = join '|', map { quotemeta } @view_names;

  my ($view_sql) = $self->g->_dbh->selectrow_array(q{
    SELECT
      sql
    FROM
      sqlite_master
    WHERE
      type = 'view' AND name = ?
  }, {}, $view_name);

  die unless defined $view_sql;

  die unless $view_sql =~ s/^\s*CREATE\s+VIEW\s+\S+\s+AS//i;

  # TODO: recursion detection

  while ($view_sql =~ s/\b($view_regex)\b/$prefix$1/) {
    next if $seen->{$1}++; # only once
    $self->_view_to_table($1, $seen);
  }

  $self->_log->debugf('selecting now for %s, sql: %s',
    $view_name, '...');

#  $self->g->_dbh->sqlite_backup_to_file($view_name . '.sqlite');

  $self->g->_dbh->do(qq{
    CREATE TABLE IF NOT EXISTS $quoted_table_name AS
    SELECT * FROM $quoted_view_name LIMIT 0;

    DELETE FROM $quoted_table_name;

    INSERT INTO $quoted_table_name 
    $view_sql
    ;

    ANALYZE $quoted_table_name;
  });

  my ($row_count) = $self->g->_dbh->selectrow_array(qq{
    SELECT COUNT(*) FROM $quoted_table_name
  });

  $self->_log->debugf('done materialising view %s (%u rows)',
    $view_name, $row_count);
}

1;

__END__
