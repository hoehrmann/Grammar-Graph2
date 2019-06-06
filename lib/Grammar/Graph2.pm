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
sub vp_self_loop      { _rw_vertex_attribute('self_loop',     @_) }
sub vp_contents_self_loop      { _rw_vertex_attribute('contents_self_loop',     @_) }
sub vp_topo           { _rw_vertex_attribute('topo',          @_) }
sub vp_skippable      { _rw_vertex_attribute('skippable',     @_) }
sub vp_epsilon_group  { _rw_vertex_attribute('epsilon_group', @_) }

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

sub is_conditional_vertex {
  my ($self, $v) = @_;
  return ($self->vp_type($v) // '') =~ /^If|If1|If2|Fi|Fi1|Fi2$/;
}

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
  return scalar $self->_dbh->selectrow_array(q{
    SELECT 1
    FROM view_vertex_shadows
    WHERE shadows = CAST(? AS TEXT)
  }, {}, $v);
}

sub add_shadows {
  my ($self, $vertex, @vertices) = @_;

#  $self->g->add_vertices($vertex, @vertices);

  $self->_dbh->do(q{
    INSERT OR IGNORE INTO vertex_shadows(vertex, shadows)
    SELECT 
      CAST(? AS TEXT) AS vertex,
      CAST(each.value AS TEXT) AS shadows
    FROM
      json_each(?) each
    WHERE
      CAST(each.value AS TEXT) NOT IN (SELECT vertex FROM view_start_vertex
                                       UNION
                                       SELECT vertex FROM view_final_vertex)
  }, {}, $vertex, $self->_json->encode(\@vertices));
}

sub flatten_shadows {
  my ($self) = @_;

#return;

  local $self->_dbh->{sqlite_allow_multiple_statements} = 1;

  $self->_dbh->do(q{
    DROP TABLE IF EXISTS t_flatten_shadows;
    CREATE TABLE t_flatten_shadows AS 
    WITH RECURSIVE
    rec AS (
      SELECT
        vertex,
        shadows
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
        vertex,
        shadows
      FROM
        rec
      WHERE
        vertex NOT IN (SELECT shadows FROM vertex_shadows)
        AND
        shadows NOT IN (SELECT vertex FROM vertex_shadows)
    )
    SELECT vertex, shadows FROM root_leaf;

    DELETE FROM vertex_shadows;

    INSERT OR IGNORE INTO vertex_shadows(vertex, shadows)
    SELECT * FROM t_flatten_shadows;
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
  
  # @@@
  $dbh->{RaiseError} = 1;

  $dbh->do(q{
    CREATE TABLE vertex_property (
      vertex PRIMARY KEY UNIQUE NOT NULL
        REFERENCES Vertex(vertex_name)
          ON UPDATE CASCADE ON DELETE CASCADE,
      type NOT NULL DEFAULT 'empty',
      name,
      p1 REFERENCES Vertex(vertex_name) ON UPDATE CASCADE ON DELETE CASCADE,
      p2 REFERENCES Vertex(vertex_name) ON UPDATE CASCADE ON DELETE CASCADE,
      partner REFERENCES Vertex(vertex_name) ON UPDATE CASCADE ON DELETE CASCADE,
      run_list,
      self_loop DEFAULT 'no',
      contents_self_loop DEFAULT 'no',
      topo INT,
      skippable,
      epsilon_group
    );

    DROP VIEW IF EXISTS view_vp_plus;
    CREATE VIEW view_vp_plus AS 
    SELECT
      vertex,
      type,
      name,
      p1,
      p2,
      partner,
      run_list,
      self_loop,
      contents_self_loop,
      topo,
      skippable,
      epsilon_group,
      CAST( type IN (
        'Start', 'If', 'If1', 'If2',
        'Final', 'Fi', 'Fi1', 'Fi2'
      ) AS INT) AS is_stack,
      CAST(type IN ('Start', 'If', 'If1', 'If2') AS INT) AS is_push,
      CAST(type IN ('Final', 'Fi', 'Fi1', 'Fi2') AS INT) AS is_pop,
      CAST( type IN (
        'If', 'If1', 'If2',
        'Fi', 'Fi1', 'Fi2'
      ) AS INT) AS is_conditional
    FROM
      vertex_property
    ;

    CREATE TABLE vertex_shadows(
      vertex REFERENCES Vertex(vertex_name)
        ON UPDATE CASCADE ON DELETE CASCADE,
      shadows REFERENCES Vertex(vertex_name)
        ON UPDATE CASCADE ON DELETE CASCADE,
      UNIQUE(vertex, shadows)
    );

    CREATE INDEX idx_vertex_shadows_shadows
      ON vertex_shadows(shadows);

    DROP VIEW IF EXISTS view_start_vertex;
    CREATE VIEW view_start_vertex AS
    SELECT attribute_value AS vertex
    FROM graph_attribute
    WHERE attribute_name = 'start_vertex';

    DROP VIEW IF EXISTS view_final_vertex;
    CREATE VIEW view_final_vertex AS
    SELECT attribute_value AS vertex
    FROM graph_attribute
    WHERE attribute_name = 'final_vertex';
  });

  ###################################################################
  # VIEWs
  ###################################################################

  # Topology.pm
  $dbh->do(q{
    DROP VIEW IF EXISTS view_vertex_skippable;
    CREATE VIEW view_vertex_skippable AS
    WITH 
    conditionals AS (
      SELECT
        if_p.vertex AS 'If',
        json_array(
          if_p.vertex, if_p.p1, if_p.p2,
          fi_p.vertex, fi_p.p1, fi_p.p2) AS six_tuple
      FROM
        view_vp_plus if_p
          INNER JOIN view_vp_plus fi_p
            ON (if_p.partner = fi_p.vertex
              AND if_p.type = 'If')
    ),
    base AS (
      SELECT
        conditionals.If AS root,
        each.value AS related
      FROM
        conditionals
          INNER JOIN json_each(conditionals.six_tuple) each
    )
    SELECT
      vertex_p.vertex,
      (self_loop = 'no') AS skippable
    FROM
      vertex_property vertex_p
        INNER JOIN view_start_vertex
        INNER JOIN view_final_vertex
    WHERE
      vertex_p.vertex NOT IN (view_start_vertex.vertex,
        view_final_vertex.vertex)
      AND
      vertex_p.vertex NOT IN (SELECT related FROM base)
    UNION
    SELECT
      vertex,
      0
    FROM
      view_start_vertex
    UNION
    SELECT
      vertex,
      0
    FROM
      view_final_vertex
    UNION
    SELECT
      related,
      0
    FROM
      base
  });

  # Topology.pm
  $dbh->do(q{
    -----------------------------------------------------------------
    -- view_parent_child
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_parent_child;
    CREATE VIEW view_parent_child AS
    WITH RECURSIVE pc(parent, child) AS (

      SELECT
        Edge.src AS parent,
        Edge.dst AS child
      FROM
        Edge
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as src_p
            ON (src_p.vertex = Edge.src)
      WHERE
        src_p.is_push
        -- AND dst_p.vertex <> src_p.partner

      UNION

      SELECT
        r.parent AS parent,
        COALESCE(partner_edges.dst, Edge.dst) AS child
      FROM Edge
        INNER JOIN pc AS r
          ON (Edge.src = r.child)
        INNER JOIN view_vp_plus AS src_p
          ON (Edge.src = src_p.vertex)
        INNER JOIN view_vp_plus AS dst_p
          ON (Edge.dst = dst_p.vertex)
        INNER JOIN view_vp_plus AS parent_p
          ON (r.parent = parent_p.vertex)
        INNER JOIN view_vp_plus AS child_p
          ON (r.child = child_p.vertex)
        LEFT JOIN Edge partner_edges
          ON (src_p.partner = partner_edges.src
            and src_p.is_push)
      WHERE
        parent_p.partner <> src_p.vertex
        -- AND COALESCE(partner_edges.dst, Edge.dst) <> parent_p.partner
    )
    SELECT
      pc.*
    FROM
      pc
        INNER JOIN vertex_property AS parent_p
          ON (pc.parent = parent_p.vertex)
        INNER JOIN vertex_property AS child_p
          ON (pc.child = child_p.vertex)
    WHERE
      1
      -- OR child_p.is_push

    ;
    
    -----------------------------------------------------------------
    -- view_paradoxical
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_paradoxical;
    CREATE VIEW view_paradoxical(parent, child) AS
    WITH RECURSIVE
    paradoxical(parent, child) AS (
      SELECT parent, child
      FROM view_parent_child
      INTERSECT
      SELECT child, parent
      FROM view_parent_child
    )
    SELECT
      parent,
      child
    FROM
      paradoxical
    ;

    -----------------------------------------------------------------
    -- view_self_loop_linearity
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_self_loop_linearity;
    CREATE VIEW view_self_loop_linearity AS
    WITH RECURSIVE
    path(root, is_productive, dst) AS (
      SELECT
        src_p.vertex AS root,
        0 AS is_productive,
        dst_p.vertex AS dst
      FROM
        Edge
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as src_p
            ON (src_p.vertex = Edge.src)
          INNER JOIN view_vp_plus as src_partner_p
            ON (src_partner_p.vertex = src_p.partner)
      WHERE
        src_p.partner IS NOT NULL
        AND (
          src_partner_p.self_loop <> 'no'
          OR
          src_p.self_loop <> 'no'
        )

      UNION

      SELECT
        root_p.vertex AS root,
        r.is_productive
          OR src_p.type = 'Input' AS is_productive,
        dst_p.vertex AS dst
      FROM
        path r
          INNER JOIN Edge
            ON (Edge.src = r.dst)
          INNER JOIN view_vp_plus as src_p
            ON (src_p.vertex = Edge.src)
          INNER JOIN view_vp_plus as dst_p
            ON (dst_p.vertex = Edge.dst)
          INNER JOIN view_vp_plus as root_p
            ON (root_p.vertex = r.root)
            
      WHERE
        1 = 1
        AND src_p.vertex <> r.root
        AND src_p.vertex <> root_p.partner
    )
    SELECT
      root AS vertex
    FROM
      path
    WHERE
      root = dst
    GROUP BY
      root,
      dst
    HAVING
      MAX(is_productive) = 1

    ;

    -----------------------------------------------------------------
    -- view_epsilon_closure
    -----------------------------------------------------------------

    DROP VIEW IF EXISTS view_epsilon_closure;
    CREATE VIEW view_epsilon_closure(vertex, e_reachable) AS
    WITH RECURSIVE
    all_e_successors_and_self(root, v) AS (

      SELECT vertex AS root, vertex AS v FROM vertex_property

      UNION

      SELECT
        r.root,
        Edge.dst
      FROM
        Edge
          INNER JOIN all_e_successors_and_self AS r
            ON (Edge.src = r.v)
          INNER JOIN vertex_property AS src_p
            ON (Edge.src = src_p.vertex)
      WHERE
        src_p.type <> 'Input'
    )
    SELECT
      root AS vertex,
      v AS e_reachable
    FROM
      all_e_successors_and_self
    ;

    -----------------------------------------------------------------
    -- view_vertices_between_self_and_partner
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_vertices_between_self_and_partner;
    CREATE VIEW view_vertices_between_self_and_partner AS
    WITH RECURSIVE
    foo AS (
      SELECT
        vertex AS root,
        vertex AS reachable
      FROM
        vertex_property
      WHERE
        partner IS NOT NULL
      UNION
      SELECT
        foo.root AS root,
        Edge.dst AS reachable
      FROM
        foo
          INNER JOIN vertex_property root_p
            ON (root_p.vertex = foo.root)
          INNER JOIN Edge
            ON (Edge.src = foo.reachable)
      WHERE
        root_p.partner <> Edge.src
    )
    SELECT
      root,
      reachable
    FROM
      foo
    ;

    -----------------------------------------------------------------
    -- view_contents_self_loop
    -----------------------------------------------------------------
    DROP VIEW IF EXISTS view_contents_self_loop;
    CREATE VIEW view_contents_self_loop AS
    WITH RECURSIVE
    base AS (
      SELECT
        vertex,
        self_loop
      FROM
        vertex_property
      UNION
      SELECT
        vpc.parent AS vertex,
        base.self_loop AS self_loop
      FROM
        base 
          INNER JOIN view_parent_child vpc
            ON (base.vertex = vpc.child)
          INNER JOIN vertex_property parent_p
            ON (parent_p.vertex = vpc.parent)
          INNER JOIN vertex_property child_p
            ON (child_p.vertex = vpc.child)
    ),
    cond AS (
      -- ensures symmetry
      SELECT
        *
      FROM
        base
      UNION
      SELECT
        vertex_p.partner,
        base.self_loop
      FROM
        base
          INNER JOIN vertex_property vertex_p
            ON (vertex_p.vertex = base.vertex)
      WHERE
        vertex_p.partner IS NOT NULL
    )
    SELECT
      vertex,
      MIN(self_loop) AS self_loop
    FROM
      cond
    GROUP BY
      vertex
    ;
  });

  my $self = $class->new(
    g => $g,
  );

  $self->_log->debugf("converting vertices");

  for my $v ($old->g->vertices) {

    if ($old->g->has_vertex_attribute($v, 'p1')) {
      $self->vp_p1($v, $old->vp_p1($v));
    }

    if ($old->g->has_vertex_attribute($v, 'p2')) {
      $self->vp_p2($v, $old->vp_p2($v));
    }

    if ($old->g->has_vertex_attribute($v, 'name')) {
      my $name = $old->vp_name($v);
      $self->vp_name($v, $name);
      my $type = $old->vp_type($v) // 'empty';
      if ($type eq 'If' or $type eq 'Fi') {
        $self->vp_name( $self->vp_p1($v), $name );
        $self->vp_name( $self->vp_p2($v), $name );
      }
    }

    if ($old->g->has_vertex_attribute($v, 'partner')) {
      $self->vp_partner($v, $old->vp_partner($v));
    }

    if ($old->g->has_vertex_attribute($v, 'run_list')) {
      $self->vp_run_list($v, $old->vp_run_list($v));
    }

#    $self->vp_shadows($v, $old->vp_shadows($v))
#      if $old->g->has_vertex_attribute($v, 'shadows');

    my $type = $old->vp_type($v) // 'empty';

    if ($type eq 'charClass') {
      $self->vp_type($v, 'Input');
    } else {
      $self->vp_type($v, $type);
    }
  }

  $self->_log->debugf("done converting vertices");

  $self->gp_start_vertex($old->start_vertex);
  $self->gp_final_vertex($old->final_vertex);

  unlink 'TEST.sqlite';
#  $dbh->sqlite_backup_to_file('TEST.sqlite');

  $self->_dbh->sqlite_create_function(
    '_json_array_uniq_sorted',
    1,
    sub {
      my ($json_array) = @_;
      return $self->_json->encode([
        sort { $a cmp $b } uniq @{ $self->_json->decode($json_array) }
      ]);
    },
  );

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
