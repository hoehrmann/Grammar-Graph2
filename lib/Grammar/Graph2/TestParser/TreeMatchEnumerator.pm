package Grammar::Graph2::TestParser::TreeMatchEnumerator;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use Grammar::Graph2::TestParser::TreeMatchEnumerator::Match;
use YAML::XS;

has 'g' => (
  is       => 'ro',
  required => 1,
  weak_ref => 1,
);

has 'src_pos' => (
  is       => 'ro',
  required => 1,
);

has 'src_vertex' => (
  is       => 'ro',
  required => 1,
);

has 'dst_pos' => (
  is       => 'ro',
  required => 1,
);

has 'dst_vertex' => (
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

has '_dbh' => (
  is       => 'rw',
  weak_ref => 1,
);

has '_json' => (
  is       => 'ro',
  required => 0,
  default  => sub {
    JSON->new->canonical(1)->ascii(1)->indent(0)
  },
);

sub BUILD {
  my ($self) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS old_path;
    CREATE TABLE old_path(
      row INT UNIQUE
    );

    DROP TABLE IF EXISTS new_path;
    CREATE TABLE new_path
    AS SELECT * FROM old_path LIMIT 0;
  });

}

sub _subtree_length {
  my ($match, $start_ix) = @_;

  my @list = @{ $match->flat_path };
  my $goal = $start_ix;

  return 1 unless defined $list[$start_ix];

  for (my $ix = $start_ix; $ix <= $goal; ++$ix) {
    next unless defined $list[$ix];
    $goal += 2;
  }

  return 1 + $goal - ($start_ix);
}

sub all_matches {
  my ($self) = @_;
  my @result;

  for (my $match; $match = $self->_next_match($match);) {
    push @result, $match;
  }

  return @result;
}

sub random_match {
  my ($self) = @_;

  return $self->_find_next_path_between(
    "random",
    $self->src_pos,
    $self->src_vertex,
    $self->dst_pos,
    $self->dst_vertex
  );
}

sub _first_match {
  my ($self) = @_;

  return $self->_find_next_path_between(
    "next",
    $self->src_pos,
    $self->src_vertex,
    $self->dst_pos,
    $self->dst_vertex
  );
}

sub _next_match {
  my ($self, $prev_match) = @_;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{
    DELETE FROM old_path;
  });

  return $self->_first_match unless defined $prev_match;

  if (defined $prev_match and not ref $prev_match) {
    use YAML::XS;
    die Dump $prev_match;
  }

  my @old_path = @{ $prev_match->flat_path };

  $self->_dbh->do(q{
    INSERT INTO old_path(row)
    SELECT each.value AS row
    FROM json_each(?) each
    ;
  }, {}, $self->_json->encode(\@old_path));

  my $sth_tuple_from_rowid = $self->_dbh->prepare_cached(q{
    SELECT
      src_pos,
      src_vertex,
      dst_pos,
      dst_vertex
    FROM
      t
    WHERE
      t.rowid = ?
  });

  for (my $ix = @old_path - 1; $ix >= 0; --$ix) {

    next unless defined $old_path[$ix];

    my $old = $self->_dbh->selectrow_hashref(
      $sth_tuple_from_rowid, {}, $old_path[$ix]);

    die unless defined $old;

    my $len = _subtree_length($prev_match, $ix);

    my $new_match = $self->_find_next_path_between(
      "next",
      $old->{src_pos},
      $old->{src_vertex},
      $old->{dst_pos},
      $old->{dst_vertex},
      $old_path[ $ix ],
      $ix + 1, # NOTE: relies on sqlite auto increment
      $len,
    );

    next unless $new_match;

    my @subtree = @old_path[ $ix .. ($ix + $len - 1) ];

    splice @old_path,
           $ix,
           $len,
           @{ $new_match->flat_path };

    my $result = Grammar::Graph2::TestParser::TreeMatchEnumerator::Match->new(
      _dbh => $self->_dbh,
      flat_path => \@old_path
    );

    return $result;
  }

}

sub _find_next_path_between {
  my ($self,
    $random_or_next,
    $src_pos, $src_vertex, $dst_pos, $dst_vertex,
    $old_root, $ix, $len) = @_;

  $self->_dbh->do(q{
    DELETE FROM new_path
  });

  my $sth = $self->_dbh->prepare(q{
    INSERT INTO new_path(row) VALUES(?)
  });

  $self->_find_next_path_between_step(
    $random_or_next,
    $sth,
    $src_pos,
    $src_vertex,
    $dst_pos,
    $dst_vertex,
    $old_root,
    $ix,
    $len
  );

  my @flat_path = map { $_->[0] } $self->_dbh->selectall_array(q{
    SELECT * FROM new_path ORDER BY rowid ASC
  });

  return unless grep { defined } @flat_path;

  return Grammar::Graph2::TestParser::TreeMatchEnumerator::Match->new(
    _dbh => $self->_dbh,
    flat_path => \@flat_path
  );
}

sub _find_next_path_between_step {
  my ($self, $random_or_next, $sth,
    $src_pos, $src_vertex, $dst_pos, $dst_vertex,
    $old_root, $ix, $len) = @_;

#warn "src_pos not defined" unless defined $src_pos;
#warn "dst_pos not defined" unless defined $dst_pos;

  my $root = $self->_dbh->selectrow_hashref(q{
    WITH
    args AS (
      SELECT
        CAST(? AS INT) AS src_pos,
        CAST(? AS TEXT) AS src_vertex,
        CAST(? AS INT) AS dst_pos,
        CAST(? AS TEXT) AS dst_vertex
    )
    SELECT
      t.rowid AS rowid,
      mid_src_p.is_push AS mid_src_is_push,
      src_p.name AS src_name,
      t.*
    FROM
      t
        INNER JOIN view_vp_plus src_p
          ON (src_p.vertex = t.src_vertex)
        LEFT JOIN view_vp_plus mid_src_p
          ON (mid_src_p.vertex = t.mid_src_vertex)

        -- to filter duplicates in the new path
        LEFT JOIN new_path c
          ON (t.rowid = c.row)

        -- to reference the item we are trying to replace
        LEFT JOIN old_path r
          ON (r.rowid = ?)

        -- to filter duplicates in the "outer" path
        LEFT JOIN old_path o
          ON (t.rowid = o.row
            AND o.rowid
              -- except items to be replaced
              NOT BETWEEN r.rowid AND r.rowid + CAST(? AS INT) - 1)
        LEFT JOIN args

    WHERE
      1 = 1
      AND t.src_pos = args.src_pos
      AND t.src_vertex = args.src_vertex
      AND t.dst_pos = args.dst_pos
      AND t.dst_vertex = args.dst_vertex
      AND c.row IS NULL -- no duplicates wrt to new_path
      AND o.row IS NULL -- no duplicates wrt to old_path

      -- work from the lowest rowid upwards
      AND COALESCE(t.rowid > ?, 1)

    ORDER BY
      COALESCE(?, RANDOM()),
      t.rowid ASC

    LIMIT
      1
  }, {},
         $src_pos,
         $src_vertex,
         $dst_pos,
         $dst_vertex,
         $ix,
         $len,
         $old_root,
         ($random_or_next eq 'random' ? undef : ''));

  if (not defined $root) {
    # warn;
    $sth->execute(undef) unless $root;
    return;
  }

  $sth->execute($root->{rowid});

  if ($root->{mid_src_is_push}) {
    $self->_find_next_path_between_step(
      $random_or_next,
      $sth,
      $root->{mid_src_pos},
      $root->{mid_src_vertex},
      $root->{mid_dst_pos},
      $root->{mid_dst_vertex},
      undef,
      $ix,
      $len
    );
    $sth->execute(undef);

  } else {
    $self->_find_next_path_between_step(
      $random_or_next,
      $sth,
      $root->{src_pos},
      $root->{src_vertex},
      $root->{mid_src_pos},
      $root->{mid_src_vertex},
      undef,
      $ix,
      $len,
    );
    $self->_find_next_path_between_step(
      $random_or_next,
      $sth,
      $root->{mid_dst_pos},
      $root->{mid_dst_vertex},
      $root->{dst_pos},
      $root->{dst_vertex},
      undef,
      $ix,
      $len,
    );
  }

}

1;

__END__
