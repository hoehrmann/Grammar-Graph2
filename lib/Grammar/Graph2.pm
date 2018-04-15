package Grammar::Graph2;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2::Init;
use List::MoreUtils qw/uniq/;

has 'g' => (
  is       => 'ro',
  required => 1,
);

has '_dbh' => (
  is       => 'ro',
  writer   => '_set_dbh',
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

sub BUILD {
  my ($self) = @_;
  $self->_set_dbh( $self->g->{dbh} );
}

#####################################################################
#
#####################################################################
sub gp_dead_vertex { 0 }

#####################################################################
#
#####################################################################

sub gp_start_vertex { _rw_graph_attribute('start_vertex', @_) }
sub gp_final_vertex { _rw_graph_attribute('final_vertex', @_) }

#####################################################################
#
#####################################################################

sub vp_type           { _rw_vertex_attribute('type',    @_) // '' }
sub vp_name           { _rw_vertex_attribute('name',          @_) }
sub vp_p1             { _rw_vertex_attribute('p1',            @_) }
sub vp_p2             { _rw_vertex_attribute('p2',            @_) }
sub vp_partner        { _rw_vertex_attribute('partner',       @_) }
sub vp_run_list       { _rw_vertex_attribute('run_list',      @_) }
sub vp_shadows        { _rw_vertex_attribute('shadows',       @_) }
sub vp_self_loop      { _rw_vertex_attribute('self_loop',     @_) }
sub vp_topo           { _rw_vertex_attribute('topo',          @_) }
sub vp_epsilon_group  { _rw_vertex_attribute('epsilon_group', @_) }
sub vp_stack_group    { _rw_vertex_attribute('stack_group',   @_) }
sub vp_shadow_group   { _rw_vertex_attribute('shadow_group',  @_) }

#####################################################################
#
#####################################################################

sub is_if_vertex       { vp_type(@_) eq 'If'       }
sub is_fi_vertex       { vp_type(@_) eq 'Fi'       }
sub is_if1_vertex      { vp_type(@_) eq 'If1'      }
sub is_if2_vertex      { vp_type(@_) eq 'If2'      }
sub is_fi1_vertex      { vp_type(@_) eq 'Fi1'      }
sub is_fi2_vertex      { vp_type(@_) eq 'Fi2'      }
sub is_start_vertex    { vp_type(@_) eq 'Start'    }
sub is_final_vertex    { vp_type(@_) eq 'Final'    }
sub is_input_vertex    { vp_type(@_) eq 'Input'    }
sub is_prelude_vertex  { vp_type(@_) eq 'Prelude'  }
sub is_postlude_vertex { vp_type(@_) eq 'Postlude' }

sub is_terminal_vertex {
  is_input_vertex(@_) or
#  is_prelude_vertex(@_) or
#  is_postlude_vertex(@_) or
  0
}

sub is_epsilon_vertex  { not is_terminal_vertex(@_) }

#####################################################################
#
#####################################################################
sub is_shadowed {
  my ($self, $v) = @_;
  return scalar grep { $_ ne $v } $self->shadowed_by_or_self($v);
}

sub shadowed_by_or_self {
  my ($self, $v) = @_;

  my @by = map { @$_ } $self->_dbh->selectall_array(q{
    SELECT
      vertex_p.vertex
    FROM
      vertex_property vertex_p
        INNER JOIN json_each(vertex_p.shadows) each
    WHERE
      each.value = CAST(? AS TEXT)
    }, {}, $v);

  return uniq $v, @by;
}

sub add_shadows {
  my ($self, $vertex, @vertices) = @_;

  # TODO: recursion?

  my (undef, $combined) = $self->_dbh->selectrow_array(q{
    WITH combined AS (
      SELECT
        vertex_p.vertex AS vertex,
        CAST(each.value AS TEXT) AS shadows
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
      WHERE
        vertex_p.vertex = ?
      UNION
      SELECT
        ? AS vertex,
        CAST(each.value AS TEXT) AS shadows
      FROM
        json_each(?) each
    )
    SELECT
      vertex,
      json_group_array(shadows) AS shadows
    FROM
      combined
    WHERE
      shadows NOT IN (SELECT attribute_value FROM graph_attribute WHERE attribute_name = 'start_vertex')
      AND
      shadows NOT IN (SELECT attribute_value FROM graph_attribute WHERE attribute_name = 'final_vertex')
    GROUP BY
      vertex
  }, {}, $vertex, $vertex, $self->_json->encode(\@vertices));

  $self->vp_shadows($vertex, $combined);

}

sub flatten_shadows {
  my ($self) = @_;

#return;

  $self->_dbh->do(q{
    WITH RECURSIVE
    vertex_shadows AS (
      SELECT
        vertex_p.vertex AS vertex,
        CAST(each.value AS TEXT) AS shadows
      FROM
        vertex_property vertex_p
          INNER JOIN json_each(vertex_p.shadows) each
    ),
    rec AS (
      SELECT
        *
      FROM
        vertex_shadows
      UNION
      SELECT
        rec.vertex AS vertex,
        vs.shadows AS shadows
      FROM
        rec
          INNER JOIN vertex_shadows vs
            ON (vs.vertex = rec.shadows)
    ),
    root_leaf AS (
      SELECT
        *
      FROM
        rec
      WHERE
        vertex NOT IN (SELECT shadows FROM vertex_shadows)
        AND
        shadows NOT IN (SELECT vertex FROM vertex_shadows)
    ),
    new_shadows AS (
      SELECT
        vertex,
        json_group_array(shadows) AS shadows
      FROM
        root_leaf
      GROUP BY
        vertex
    )
    UPDATE
      vertex_property
    SET
      shadows = (SELECT shadows
                 FROM new_shadows
                 WHERE vertex_property.vertex = new_shadows.vertex)
  });
}

#####################################################################
#
#####################################################################

sub conditionals_from_if {
  my ($self, $if) = @_;

  my $fi = $self->vp_partner($if);

  return (
    $if,
    $self->vp_p1($if),
    $self->vp_p2($if),
    $self->vp_p2($fi),
    $self->vp_p1($fi),
    $fi
  );
}

#####################################################################
#
#####################################################################

sub _rw_vertex_attribute_old {
  my ($name, $self, $vertex, $value) = @_;

  my $old = $self->g->get_vertex_attribute($vertex, $name);

  if (@_ > 3) {
    $self->g->set_vertex_attribute($vertex, $name, $value);
  }

  return $old;
}

sub _rw_vertex_attribute {
  my ($name, $self, $vertex, $value) = @_;

  my ($old) = $self->g->{dbh}->selectrow_array(sprintf(q{
    SELECT %s FROM vertex_property WHERE vertex = ?
  }, $name), {}, $vertex);

  if (@_ > 3) {

    $self->g->add_vertex($vertex);

    $self->g->{dbh}->do(q{
      INSERT OR IGNORE INTO vertex_property(vertex) VALUES(?)
    }, {}, $vertex);

    $self->g->{dbh}->do(sprintf(q{
      UPDATE vertex_property SET %s = %s WHERE vertex = %s
    }, $name, $self->g->{dbh}->quote($value),
              $self->g->{dbh}->quote($vertex)));

    if ($name eq 'type') {
      use Carp;
      confess unless length $value;
      my $is_push = 0 + ($value =~ /^(Start|If|If1|If2)$/);
      my $is_pop = 0 + ($value =~ /^(Final|Fi|Fi1|Fi2)$/);
      my $is_stack = 0 + ($is_push || $is_pop);
      $self->g->{dbh}->do(q{
        UPDATE vertex_property
        SET is_stack = ?, is_push = ?, is_pop = ?
        WHERE vertex = ?
      }, {}, $is_stack, $is_push, $is_pop, $vertex);
    }
  }

  return $old;
}

sub _rw_graph_attribute {
  my ($name, $self, $value) = @_;

  my $old = $self->g->get_graph_attribute($name);

  if (@_ > 2) {
    $self->g->set_graph_attribute($name, $value);
  }

  return $old;
}

#####################################################################
#
#####################################################################

sub _from_db {
  my ($class, $db_path) = @_;
  my $g = Graph::Feather->new;

  $g->_feather_restore_from_file($db_path);

  return $class->new(
    g => $g
  );
}

sub from_grammar_graph {
  my ($class, $old) = @_;

  my $g = Graph::Feather->new(
    vertices => [ $old->g->vertices ],
    edges    => [ $old->g->edges ],
  );

  my $dbh = $g->{dbh};

  local $dbh->{sqlite_allow_multiple_statements} = 1;

  $dbh->do(q{
    CREATE TABLE vertex_property (
      vertex PRIMARY KEY UNIQUE NOT NULL
        REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      type NOT NULL DEFAULT 'empty',
      name,
      p1 REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      p2 REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      partner REFERENCES Vertex(vertex_name) ON UPDATE CASCADE,
      is_stack NOT NULL DEFAULT 0,
      is_push NOT NULL DEFAULT 0,
      is_pop NOT NULL DEFAULT 0,
      run_list,
      shadows,
      self_loop DEFAULT 'no',
      topo,
      epsilon_group,
      stack_group,
      shadow_group
    );
  });

  my $self = $class->new(
    g => $g,
  );

  for my $v ($old->g->vertices) {

    if ($old->g->has_vertex_attribute($v, 'p1')) {
      $self->vp_p1($v, $old->vp_p1($v));
    }

    if ($old->g->has_vertex_attribute($v, 'p2')) {
      $self->vp_p2($v, $old->vp_p2($v));
    }

    if ($old->g->has_vertex_attribute($v, 'name')) {
      $self->vp_name($v, $old->vp_name($v));
    }      

    if ($old->g->has_vertex_attribute($v, 'partner')) {
      $self->vp_partner($v, $old->vp_partner($v));
    }

    if ($old->g->has_vertex_attribute($v, 'run_list')) {
      $self->vp_run_list($v, $old->vp_run_list($v));
    }

#    $self->vp_shadows($v, $old->vp_shadows($v))
#      if $old->g->has_vertex_attribute($v, 'shadows');

    my $type = $old->vp_type($v);

    if ($type eq 'charClass') {
      $self->vp_type($v, 'Input');
    } else {
      $self->vp_type($v, $type);
    }
  }

  $self->gp_start_vertex($old->start_vertex);
  $self->gp_final_vertex($old->final_vertex);

  unlink 'TEST.sqlite';
#  $dbh->sqlite_backup_to_file('TEST.sqlite');

  $self->_init();

  return $self;
}

1;

__END__

=head1 NAME

Grammar::Graph2 - ...

=head1 SYNOPSIS

  use Grammar::Graph2;

=head1 DESCRIPTION

=head1 CONSTRUCTORS

=over

=item Grammar::Graph2->from_grammar_graph($g)

...

=back

=head1 METHODS

=over

=item ...

=back

=head1 AUTHOR / COPYRIGHT / LICENSE

  Copyright (c) 2017-2018 Bjoern Hoehrmann <bjoern@hoehrmann.de>.
  This module is licensed under the same terms as Perl itself.

=cut
