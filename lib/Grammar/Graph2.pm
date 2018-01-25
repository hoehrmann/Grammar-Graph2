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

sub vp_type     { _rw_vertex_attribute('type', @_)    }
sub vp_name     { _rw_vertex_attribute('name', @_)    }
sub vp_p1       { _rw_vertex_attribute('p1', @_)      }
sub vp_p2       { _rw_vertex_attribute('p2', @_)      }
sub vp_partner  { _rw_vertex_attribute('partner', @_) }
sub vp_input    { _rw_vertex_attribute('input', @_)   }

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

sub _rw_vertex_attribute {
  my ($name, $self, $vertex, $value) = @_;

  my $old = $self->g->get_vertex_attribute($vertex, $name);

  if (@_ > 3) {
    $self->g->set_vertex_attribute($vertex, $name, $value);
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

sub from_grammar_graph {
  my ($class, $old) = @_;

  my $g = Graph::Feather->new(
    vertices => [ $old->g->vertices ],
    edges    => [ $old->g->edges ],
  );

  my $dbh = $g->{dbh};

  $dbh->do(q{
    CREATE TABLE vertex_span(
      vertex,
      min INTEGER,
      max INTEGER
    );
  });

  $dbh->do(q{
    CREATE INDEX idx_vertex_span_vertex
      ON vertex_span(vertex)
  });

  my $span_insert_sth = $dbh->prepare(q{
    INSERT INTO vertex_span(vertex, min, max) VALUES (?, ?, ?)
  });

  my $self = $class->new(
    g => $g,
  );

  for my $v ($old->g->vertices) {
    my $label = $old->get_vertex_label($v);
    next unless $label;

    $self->vp_p1($v, $label->p1)
      if UNIVERSAL::can($label, 'p1');

    $self->vp_p2($v, $label->p2)
      if UNIVERSAL::can($label, 'p2');

    $self->vp_name($v, $label->name)
      if UNIVERSAL::can($label, 'name');

    $self->vp_partner($v, $label->partner)
      if UNIVERSAL::can($label, 'partner');

    my $type = ref($label) =~ s/.*:://r;

    $self->vp_type($v, $type);

    if ($old->is_terminal_vertex($v)) {
      next if $type eq 'Prelude';
      next if $type eq 'Postlude';
      $self->vp_type($v, 'Input');
      $self->vp_input($v, $label);
      die unless UNIVERSAL::can($label, 'spans');
      $dbh->begin_work();
      $span_insert_sth->execute($v, @$_)
        for $label->spans->spans;
      $dbh->commit();
    }

  }

  $self->gp_start_vertex($old->start_vertex);
  $self->gp_final_vertex($old->final_vertex);

  unlink 'TEST.sqlite';
  $dbh->sqlite_backup_to_file('TEST.sqlite');

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
