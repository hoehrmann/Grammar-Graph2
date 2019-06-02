package Grammar::Graph2;
use strict;
use warnings;
use 5.024000;
use Moo;
use Log::Any qw//;
use Types::Standard qw/:all/;
use List::Util qw/min max/;
use List::MoreUtils qw/uniq/;
use List::OrderBy;
use List::StackBy;
use List::UtilsBy qw/uniq_by nsort_by/;

use Graph::Feather;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use Grammar::Graph2;
# use Grammar::Graph2::TestParser::MatchEnumerator;
use Grammar::Graph2::Conditionals;
use Grammar::Graph2::Cover;
use Grammar::Graph2::Topology;
use Grammar::Graph2::Automata;
use Grammar::Graph2::Megamata;
use Grammar::Graph2::UTF8;
use Acme::Partitioner;

use Memoize;
use YAML::XS;

sub _vertex_references {

  my ($self) = @_;

  my @tables = map { @$_ } $self->_dbh->selectall_array(q{
    SELECT
      name
    FROM
      sqlite_master
    WHERE
      type = 'table'
  });

  my @result;

  for my $table (@tables) {

    # quote_identifier and bind values do not seem to work here
    my $table_quoted = $self->_dbh->quote($table);

    my @cols = map {
      $_->{from}
    } grep {
      $_->{table} eq 'Vertex'
      and
      $_->{to} eq 'vertex_name'
    } values %{ $self->_dbh->selectall_hashref(qq{
      PRAGMA foreign_key_list( $table_quoted )
    }, 'id') };

    push @result, [ $table, @cols ] if @cols;

  }

  # TODO: maybe better to return a hash
  # TODO: move to DBUtils.pm?

  return @result;

}

#####################################################################
# Duplicate merging
#####################################################################

sub _merge_duplicates {

  my ($self) = @_;

#  return; # unfinished

  my $f = Graph::Feather->new(
    edges => $self->_dbh->selectall_arrayref(q{
      SELECT * FROM old_edge
    }),
  );

  # TODO: maybe add partner vertices? those can get lost...

  my @vertices = uniq grep {
    1; # $self->g->edges_at($_)
  } ($self->g->vertices, $f->vertices,
#  map { @$_ } $self->_dbh->selectall_array(q{
#    SELECT vertex FROM vertex_property
#  })
  );

  my $p = Acme::Partitioner->using(@vertices);

  my $partitioner =
    $p
      ->once_by(sub {
        my $v = $_;
        return ($self->gp_start_vertex eq $v);
      })
      ->once_by(sub {
        my $v = $_;
        return ($self->gp_final_vertex eq $v);
      })
      ->once_by(sub {
        my $v = $_;
        return ($self->vp_type($v) // '');
      })
      ->once_by(sub {
        my $v = $_;
        return '' if $self->vp_type($v) eq 'empty';
        return ($self->vp_name($v) // '');
      })
      ->once_by(sub {
        my $v = $_;
        # do not merge in true grammar graph. It would be nice to
        # do that there aswell, but strange bugs happen in `zoo`.
        # TODO: might have something to do with `epsilon_group`.
        return $v if defined $self->vp_topo($v);
        return '';
      })
      ->once_by(sub {
        my $v = $_;
        # safeguard
        return ($self->vp_skippable($v) // '');
      })
      ->once_by(sub {
        my $v = $_;
        # unclear if this is needed, but if such vertices are
        # merged, the run lists would have to be merged aswell.
        return ($self->vp_run_list($v) // '');
      })
      ->then_by(sub {
        my $v = $_;

        my @shadows = map { @$_ } $self->_dbh->selectall_array(q{
          SELECT shadows
          FROM vertex_shadows
          WHERE vertex = ?
          ORDER BY shadows
        }, {}, $v);

        return join ' ', sort { $a cmp $b } uniq map {
          $p->partition_of( $_ )
        } @shadows;

      })
      ->then_by(sub {
        my $v = $_;

        return '' unless $self->vp_partner( $v );
        return $p->partition_of( $self->vp_partner( $v ) );

      })
      ->then_by(sub {
        my $v = $_;

        return join ' ', sort { $a cmp $b } uniq map {
          $p->partition_of( $_ )
        } $f->successors( $v );

      })
      ->then_by(sub {
        my $v = $_;

        return join ' ', sort { $a cmp $b } uniq map {
          $p->partition_of( $_ )
        } $self->g->successors( $v );

      })
      ;

  while ($partitioner->refine) {
    $self->_log->debugf("duplicates p size = %u", $p->size());
  }

  # TODO: slow
  my $map_function = sub {
    my ($v) = @_;
    return [nsort_by {
      $self->vp_topo($_) // 0
    } $p->items_in( $p->partition_of($v) )]->[0]
  };

  my %map = map { $_, $map_function->($_) } @vertices;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t_merge;
  });

  $self->_dbh->do(q{
    CREATE TABLE t_merge AS
    SELECT 
      CAST(json_extract(each.value, '$[0]') AS TEXT) AS v1,
      CAST(json_extract(each.value, '$[1]') AS TEXT) AS v2
    FROM
      json_each(?) each
  }, {}, $self->_json->encode([
    map { [ $_, $map{$_} ] } keys %map
  ]));

  $self->_dbh->do(q{
    CREATE UNIQUE INDEX idx_t_merge ON t_merge(v1, v2)
  });

# return;

  # table, col1, col2, ...
  my @refs = $self->_vertex_references();

  $self->_dbh->begin_work();

  # TODO: would be nicer to have a better, more generic function
  # with more checks for odd cases 

  for my $ref (@refs) {

    # TODO: table/column name quoting

    my $table = shift @$ref;

    # TODO: IGNORE rather than ... REPLACE or something?

    my $sql = sprintf q{
      UPDATE OR IGNORE %s SET 
    }, $table;

    $sql .= join ", ", map {
      sprintf q{
        %s = (
          SELECT v2
          FROM t_merge
          WHERE t_merge.v1 = %s.%s
        )
      }, $_, $table, $_;
    } @$ref;

    $self->_log->debugf("merge sql = %s", $sql);

    $self->_dbh->do($sql);

  }

  $self->_dbh->commit;  

  # TODO: redundant with deleting in `_rename_vertices`?
  $self->_dbh->do(q{
    DELETE
    FROM Vertex
    WHERE vertex_name NOT IN (
      SELECT CAST(each.value AS TEXT) FROM json_each(?) each
    )
  }, {}, $self->_json->encode([ values %map ]));

  for my $v (@vertices) {
    my $eg = $self->vp_epsilon_group($v);
    next unless $eg;
    my @mapped = sort { $a <=> $b } uniq map { $map{$_} } @{ $self->_json->decode($eg) };
    $self->vp_epsilon_group($self->_json->encode(\@mapped));
  }

}



1;

__END__

