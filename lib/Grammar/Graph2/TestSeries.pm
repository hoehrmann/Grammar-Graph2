package Grammar::Graph2::TestSeries;
use strict;
use warnings;
use 5.024000;
use Moo;
use Graph::Feather;
use Graph::Directed;
use Grammar::Graph2;
use Log::Any qw//;
use Types::Standard qw/:all/;
use YAML::XS;
use File::Spec qw//;
use Parse::ABNF;
use File::Find::Rule;
use File::Basename qw//;

has 'base_path' => (
  is       => 'ro',
  required => 1,
);

has 'options' => (
  is       => 'ro',
  required => 0,
  writer   => '_set_options',
);

has 'g' => (
  is       => 'ro',
  required => 0,
  writer   => '_set_g',
);

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

sub BUILD {
  my ($self) = @_;

  $self->_log->debugf("Load options %s", $self->_options_path);

  my $options = YAML::XS::LoadFile( $self->_options_path );

  die unless ref $options eq 'HASH';

  $self->_set_options( $options );

  $self->_load_grammar_file();
}

sub basename {
  my ($self) = @_;

  return File::Basename::basename($self->base_path);
}

sub _grammar_path {
  my ($self) = @_;

  return File::Spec->rel2abs(
    File::Spec->catfile(
      $self->base_path, 'grammar.aabnf')
  );
}

sub _options_path {
  my ($self) = @_;

  return File::Spec->rel2abs(
    File::Spec->catfile(
      $self->base_path, 'options.yaml')
  );
}

sub _load_grammar_file {
  my ($self) = @_;

  my $path = $self->_grammar_path;
  my $shortname = $self->options->{startrule};

  $self->_log->debugf("Load grammar %s for %s",
    $self->_grammar_path, $shortname);

  my $formal = Parse::ABNF->new->parse_to_grammar_formal(do {
    local $/;
    die "There is no file $path" unless -f $path;
    open my $f, '<', $path;
    <$f> =~ s/\r\n/\n/gr;
  }, core => 1);

  my $g = Grammar::Graph->from_grammar_formal($formal, $shortname);

  $g->fa_drop_rules_not_needed_for($shortname);
  $g->fa_merge_character_classes();
#  $g->fa_separate_character_classes();

  $g->fa_expand_references();
  $g->fa_remove_useless_epsilons($g->g->vertices);
  $g->fa_truncate();

  my $g2 = Grammar::Graph2->from_grammar_graph($g);

  $self->_set_g( $g2 );
}

sub input_file_paths {
  my ($self) = @_;

  my @files = File::Find::Rule
    ->file()
    ->name( qr/^t[a-f0-9]+\.input$/ )
    ->in( $self->base_path );

  return sort map {
    File::Spec->rel2abs( $_ )
  } @files;
}

1;

__END__

