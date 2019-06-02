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

sub _init {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_log->debug('starting topology');

  Grammar::Graph2::Topology->new(
    g => $self,
  );

  $self->_log->debug('done topology');

  my $automata = Grammar::Graph2::Automata->new(
    base_graph => $self,
  );

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS old_edge;
    CREATE TABLE old_edge(
      src REFERENCES Vertex(vertex_name) ON UPDATE CASCADE ON DELETE CASCADE,
      dst REFERENCES Vertex(vertex_name) ON UPDATE CASCADE ON DELETE CASCADE
    );
    INSERT INTO old_edge SELECT * FROM edge;
    ANALYZE old_edge;
    CREATE UNIQUE INDEX idx_old_edge ON old_edge(src,dst);
  });

  if (0) {

    # used to come before replace_conditionals 

    $self->_log->debug('starting mega');

    Grammar::Graph2::Megamata->new(
      base_graph => $self,
    )->mega;

    $self->_log->debug('done mega');
  }

  # used to be called much later
  $self->_cover_input_input_edges();
  $self->_log->debug('done _cover_input_input_edges');

  #  new call (earlier)
#  $self->_cover_epsilons();

  do {
    die "still has terminal->terminal edge";
  } if $self->_dbh->selectall_array(q{
    SELECT
      1
    FROM
      edge
        inner join vertex_property src_p
          on (src_p.vertex = edge.src)
        inner join vertex_property dst_p
          on (dst_p.vertex = edge.dst)
    WHERE
      src_p.type = 'Input'
      AND
      dst_p.type = 'Input'
  });

  $self->_log->debug('starting _replace_conditionals');
  $self->_replace_conditionals();
  $self->_log->debug('done _replace_conditionals');

#  $self->_dbh->sqlite_backup_to_file('post-conditionals.sqlite');

  $self->_cover_root();
  $self->_log->debug('done cover root');

  # old call
  $self->_cover_epsilons();
  $self->_log->debug('done cover epsilons');

  $self->flatten_shadows();
  $self->_log->debug('done flatten_shadows');

  my $subgraph = _shadowed_subgraph_between($self,
    $self->gp_start_vertex, $self->gp_final_vertex);

  $self->g->feather_delete_edges($self->g->edges);
  $self->g->add_edges( $subgraph->edges );

  # Note: this is the most recent addition, if odd bugs occur, 
  # comment this out
  $self->_merge_duplicates();
  $self->_log->debug('done _merge_duplicates');

  # $self->_dbh->sqlite_backup_to_file('Slow.sqlite');

  $self->_log->debug('starting _rename_vertices');
  $self->_rename_vertices();
  $self->_log->debug('done _rename_vertices');

  $self->_create_vertex_spans();
  $self->_log->debug('done creating spans');

  $self->_create_input_classes();
  $self->_log->debug('done creating input_classes');

  $self->_create_utf8();
  $self->_log->debug('done _create_utf8');

  $self->_dbh->do(q{ ANALYZE });
  return;
}

#####################################################################
# This stuff does not really belong here, and not with the other part
#####################################################################

sub _shadowed_subgraph_between {
  my ($g2, $start_vertex, $final_vertex) = @_;

  # TODO: ultimately this should not result in failure
  die if $g2->is_shadowed($start_vertex);
  die if $g2->is_shadowed($final_vertex);

  return Graph::Feather->new(
    edges => [ graph_edges_between($g2->g, $start_vertex, $final_vertex) ],
  );
}

#####################################################################
# This stuff does not really belong here:
#####################################################################

sub _create_input_classes {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;
  
  my $alphabet = Grammar::Graph2::Alphabet->new(
    g => $self
  );

  my %h = %{ $alphabet->_ord_to_list };

  my @list_of_spans = map {
    $self->_json->encode([ Set::IntSpan->new($h{$_})->spans ])
  } sort { $a <=> $b } keys %h;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS input_class;
    CREATE TABLE input_class AS 
    SELECT
      CAST(1 + class.key AS INT) AS class,
      CAST(json_extract(span.value, '$[0]') AS INT) AS 'min',
      CAST(json_extract(span.value, '$[1]') AS INT) AS 'max'
    FROM
      json_each(?) class
        INNER JOIN json_each(class.value) span
  }, {}, $self->_json->encode(\@list_of_spans));
}

sub _create_vertex_spans {
  my ($self) = @_;

  my $dbh = $self->g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  $dbh->do(q{
    DROP TABLE IF EXISTS vertex_span;

    CREATE TABLE vertex_span(
      vertex REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      min INTEGER,
      max INTEGER
    );

    CREATE INDEX idx_vertex_span_vertex
      ON vertex_span(vertex)
  });

  my $span_insert_sth = $dbh->prepare(q{
    INSERT INTO vertex_span(vertex, min, max) VALUES (?, ?, ?)
  });

  my $spans_for_run_list = memoize(sub{
    my ($run_list) = @_;
    return Set::IntSpan->new($run_list)->spans;
  });

  for my $v ($self->g->vertices) {

    my $type = $self->vp_type($v);

    if ($self->is_terminal_vertex($v)) {
      next if $type eq 'Prelude';
      next if $type eq 'Postlude';

      $dbh->begin_work();
      $span_insert_sth->execute($v, @$_)
        for $spans_for_run_list->( $self->vp_run_list($v) );
      $dbh->commit();
    }
  }

}

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

sub _rename_vertices {
  my ($self) = @_;

  # move to ::Ordering?

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  # NOTE: this does not cover vertex_span but this method
  # is not called after creating the vertex_span table. 
  # It should not be difficult to make this more generic.
  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t_has_neighbours;
    CREATE TABLE t_has_neighbours AS
    WITH RECURSIVE 
    has_neighbours AS (
      SELECT src AS vertex FROM old_edge
      UNION
      SELECT dst FROM old_edge
      UNION
      SELECT src FROM edge
      UNION
      SELECT dst FROM edge
      UNION
      SELECT vertex FROM view_start_vertex
      UNION
      SELECT vertex FROM view_final_vertex
      UNION
      SELECT
        vertex_p.vertex 
      FROM
        has_neighbours
          INNER JOIN vertex_property vertex_p
            ON (has_neighbours.vertex IN 
              (vertex_p.p1, vertex_p.p2, vertex_p.partner))
    )
    SELECT * FROM has_neighbours
    ;
    CREATE INDEX idx_t_has_neighbours ON t_has_neighbours(vertex)
    ;
    DELETE FROM
      vertex
    WHERE
      vertex_name NOT IN (SELECT vertex FROM t_has_neighbours)
  }) if 1;

=pod 

  # old

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t_rename_vertex;
    CREATE TABLE t_rename_vertex AS
    SELECT
      Vertex.vertex_name AS vertex
    FROM
      Vertex
        LEFT JOIN vertex_property vertex_p
          ON (vertex_p.vertex = Vertex.vertex_name)
    ORDER BY
      vertex_p.topo IS NULL ASC,
      vertex_p.topo,
      vertex_p.run_list IS NULL DESC,
      vertex_p.type,
      vertex_p.name
  });

=cut

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t_rename_vertex;
    CREATE TABLE t_rename_vertex AS
    SELECT
      Vertex.vertex_name AS vertex
    FROM
      Vertex
        LEFT JOIN vertex_property vertex_p
          ON (vertex_p.vertex = Vertex.vertex_name)
    ORDER BY
      vertex_p.topo IS NULL ASC,
      vertex_p.topo,
      vertex_p.skippable IS NULL ASC,
      vertex_p.skippable DESC,
      vertex_p.type,
      vertex_p.name
    ;
    CREATE UNIQUE INDEX idx_t_rename_vertex
      ON t_rename_vertex(vertex)
    ;
  });

  $self->_dbh->begin_work();
  
  $self->_dbh->do(q{
    -- PRAGMA defer_foreign_keys = 1;
    UPDATE
      vertex
    SET
      vertex_name = (SELECT CAST(-rowid AS TEXT)
                     FROM t_rename_vertex
                     WHERE vertex = vertex.vertex_name)
    ;
    UPDATE
      vertex
    SET
      vertex_name = (SELECT CAST(-vertex_name AS TEXT))
    ;
  }) or die;

  $self->_dbh->commit;

  my %map = %{ $self->_dbh->selectall_hashref(q{
    SELECT
      vertex,
      rowid
    FROM
      t_rename_vertex
  }, 'vertex') };

  for my $meth (qw/vp_epsilon_group/) {
    for my $v ($self->g->vertices) {
      my $encoded = $self->$meth($v);
      next unless defined $encoded;
      # NOTE: automatically removes unreferenced vertices
      $self->$meth($v, $self->_json->encode([
        map { $map{$_}->{rowid} // () }
          @{ $self->_json->decode($encoded) }
      ]));
    }
  }

  $self->gp_start_vertex('' . $map{$self->gp_start_vertex()}->{rowid});
  $self->gp_final_vertex('' . $map{$self->gp_final_vertex()}->{rowid});
#  $self->gp_dead_vertex('' . $map{$self->gp_dead_vertex()}->{rowid})
#    if defined $self->gp_dead_vertex();

}

sub _create_utf8 {
  my ($self) = @_;

  my $utf8 = Grammar::Graph2::UTF8->new(
    g => $self,
  );
}

1;

__END__
