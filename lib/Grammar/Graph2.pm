package Grammar::Graph2;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;

has 'g' => (
  is       => 'ro',
  required => 1,
);

#####################################################################
#
#####################################################################

sub gp_start_vertex { _rw_graph_attribute('start_vertex', @_) }
sub gp_final_vertex { _rw_graph_attribute('final_vertex', @_) }

#####################################################################
#
#####################################################################

sub vp_type          { _rw_vertex_attribute('type',    @_) // '' }
sub vp_name          { _rw_vertex_attribute('name',          @_) }
sub vp_p1            { _rw_vertex_attribute('p1',            @_) }
sub vp_p2            { _rw_vertex_attribute('p2',            @_) }
sub vp_partner       { _rw_vertex_attribute('partner',       @_) }
sub vp_run_list      { _rw_vertex_attribute('run_list',      @_) }
sub vp_shadows       { _rw_vertex_attribute('shadows',       @_) }
sub vp_shadow_edges  { _rw_vertex_attribute('shadow_edges',  @_) }
sub vp_self_loop     { _rw_vertex_attribute('self_loop',     @_) }
sub vp_topo          { _rw_vertex_attribute('topo',          @_) }
sub vp_epsilon_group { _rw_vertex_attribute('epsilon_group', @_) }

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
  is_prelude_vertex(@_) or
  is_postlude_vertex(@_) or
  0
}

sub is_epsilon_vertex  { not is_terminal_vertex(@_) }

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

    die if $name eq 'shadows' and defined $self->vp_shadows($value);

    # TODO: this could be nicer

    $self->g->{dbh}->do(sprintf(q{
      INSERT OR IGNORE INTO vertex_property(vertex) VALUES(%s)
    }, $self->g->{dbh}->quote($vertex)));

    $self->g->{dbh}->do(sprintf(q{
      UPDATE vertex_property SET %s = %s WHERE vertex = %s
    }, $name, $self->g->{dbh}->quote($value),
              $self->g->{dbh}->quote($vertex)));

    if ($name eq 'type' and $value =~ /^(Start|If|If1|If2)$/) {
      $self->g->{dbh}->do(sprintf(q{
        UPDATE vertex_property
        SET is_stack = 1, is_push = 1, is_pop = NULL
        WHERE vertex = %s
      }, $self->g->{dbh}->quote($vertex)));

    } elsif ($name eq 'type' and $value =~ /^(Final|Fi|Fi1|Fi2)$/) {
      $self->g->{dbh}->do(sprintf(q{
        UPDATE vertex_property
        SET is_stack = 1, is_push = NULL, is_pop = 1
        WHERE vertex = %s
      }, $self->g->{dbh}->quote($vertex)));
    } elsif ($name eq 'type') {
      $self->g->{dbh}->do(sprintf(q{
        UPDATE vertex_property
        SET is_stack = NULL, is_pop = NULL, is_pop = NULL
        WHERE vertex = %s
      }, $self->g->{dbh}->quote($vertex)));
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

  $dbh->do(q{
    CREATE TABLE vertex_property (
      vertex PRIMARY KEY,
      type,
      name,
      p1,
      p2,
      partner,
      is_stack,
      is_push,
      is_pop,
      run_list,
      shadows,
      shadow_edges,
      self_loop DEFAULT 'no',
      topo,
      epsilon_group
    )
  });

  my $self = $class->new(
    g => $g,
  );

  for my $v ($old->g->vertices) {

    $self->vp_p1($v, $old->vp_p1($v))
      if $old->g->has_vertex_attribute($v, 'p1');

    $self->vp_p2($v, $old->vp_p2($v))
      if $old->g->has_vertex_attribute($v, 'p2');

    $self->vp_name($v, $old->vp_name($v))
      if $old->g->has_vertex_attribute($v, 'name');

    $self->vp_partner($v, $old->vp_partner($v))
      if $old->g->has_vertex_attribute($v, 'partner');

    $self->vp_run_list($v, $old->vp_run_list($v))
      if $old->g->has_vertex_attribute($v, 'run_list');

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
