#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd); cd "$repo_root"
command -v perl >/dev/null || { echo 'perl is required by check-doc-links.sh' >&2; exit 1; }
perl <<'PERL'
use strict; use warnings; use utf8; use File::Find;
my (@documents,@failures);
{
  local $SIG{__WARN__}=sub { die @_ };
  find({ no_chdir=>1, wanted=>sub {
    my $p=$File::Find::name; $p =~ s!^\./!!; (my $leaf=$p) =~ s!.*/!!;
    if (-d $_ && ($leaf eq '.git' || $leaf eq '.lake' || $leaf eq '.claude')) { $File::Find::prune=1; return }
    return unless -f $_ && /\.md\z/;
    push @documents,$p;
  }}, '.');
}
for my $document (@documents) {
  open my $fh,'<:raw',$document or die "$document: $!\n"; local $/; my $text=<$fh>;
  while ($text =~ /!?\[[^\]]*\]\(([^)]+)\)/g) {
    my $target=$1; $target =~ s/^\s+|\s+$//g; $target =~ s/^<(.*)>$/$1/s;
    (my $path=$target) =~ s/#.*\z//s;
    next if $path !~ /\S/ || $path =~ /^[A-Za-z][A-Za-z0-9+.-]*:/;
    $path =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/eg;
    my $base=$document; $base =~ s![^/]+\z!!;
    push @failures, "$document: missing target '$target'" unless -e "$base$path";
  }
}
if (@failures) { warn "$_\n" for @failures; exit 1 }
print 'All relative links in '.scalar(@documents)." Markdown files resolve.\n";
PERL
