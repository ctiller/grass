#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd); cd "$repo_root"
command -v perl >/dev/null || { echo 'perl is required by check-spike-sources.sh' >&2; exit 1; }
spikes=()
while (($#)); do case $1 in
  -Spike|--spike) shift; (($#)) || { echo 'missing spike number' >&2; exit 2; }; spikes+=("$1") ;;
  1|2|3|4|5) spikes+=("$1") ;;
  *) echo "usage: $0 [--spike 1..5 ...]" >&2; exit 2 ;;
esac; shift; done
((${#spikes[@]})) || spikes=(1 2 3 4 5)
for spike in "${spikes[@]}"; do [[ $spike =~ ^[1-5]$ ]] || { echo "invalid spike: $spike" >&2; exit 2; }; done
perl - "${spikes[@]}" <<'PERL'
use strict; use warnings; use utf8; use File::Find;
my %dirs=(1=>'1_Hello_World',2=>'2_Sort',3=>'3_Gzip',4=>'4_Web_Server',5=>'5_Spinning_Cube'); my $failed=0;
sub normalized { my ($x)=@_; $x =~ s/\r\n?/\n/g; $x =~ s/\n+\z//; return $x }
for my $spike (@ARGV) {
  my $doc="docs/SPIKE_$spike.md"; my $root="Spikes/$dirs{$spike}";
  open my $fh,'<:raw',$doc or die "$doc: $!\n"; local $/; my $text=normalized(<$fh>); my @lines=split /\n/,$text,-1;
  my (%ids,%authored); my $blocks=0;
  for (my $i=0;$i<@lines;$i++) {
    next unless $lines[$i] =~ /^```/; ++$blocks; my $class;
    if ($i && $lines[$i-1] =~ /^<!-- grass-block: (.+) -->$/) { $class=$1 } else { warn "SPIKE_$spike: block $blocks has no immediate classification\n"; $failed=1 }
    my $end=$i+1; ++$end while $end<@lines && $lines[$end] ne '```';
    if ($end>=@lines) { warn "SPIKE_$spike: block $blocks is unterminated\n"; $failed=1; last }
    my $body=$end==$i+1 ? '' : normalized(join("\n",@lines[$i+1..$end-1]));
    if (defined $class) { my $identity;
      if ($class =~ /^authored file=([^ ]+)$/) { my $path=$1; $path =~ s!\\!/!g; $identity="authored:$path";
        if ($path =~ m!^(?:/|[A-Za-z]:|\.\.?/)! || $path =~ m!/(?:\.\.?)(?:/|\z)!) { warn "SPIKE_$spike: invalid authored path $path\n"; $failed=1 }
        if ($lines[$i] ne '```lean') { warn "SPIKE_$spike: authored $path is not a Lean block\n"; $failed=1 }
        if (exists $authored{$path}) { warn "SPIKE_$spike: duplicate authored path $path\n"; $failed=1 } else { $authored{$path}=$body }
      } elsif ($class =~ /^generated id=([^ ]+) derives=(.+)$/) { my ($id,$derives)=($1,$2); $identity="generated:$id"; if ($derives !~ /\S/) { warn "SPIKE_$spike: generated block lacks derives authority\n"; $failed=1 }
      } elsif ($class =~ /^(interface|proof-sketch) id=([^ ]+)$/) { $identity="$1:$2" }
      else { warn "SPIKE_$spike: invalid classification '$class'\n"; $failed=1 }
      if (defined $identity && $ids{$identity}++) { warn "SPIKE_$spike: duplicate block identity $identity\n"; $failed=1 }
    } $i=$end;
  }
  my %actual; find({no_chdir=>1,wanted=>sub { return unless -f $_ && /\.lean\z/; my $p=$File::Find::name; $p =~ s!^\Q$root\E/!!; open my $f,'<:raw',$File::Find::name or die "$File::Find::name: $!\n"; local $/; $actual{$p}=normalized(<$f>) }},$root);
  my @a=sort keys %actual; my @b=sort keys %authored;
  if (join("\n",@a) ne join("\n",@b)) { warn "SPIKE_$spike: authored file manifest differs\n"; $failed=1 }
  for my $path (@a) { next unless exists $authored{$path}; if ($actual{$path} ne $authored{$path}) { warn "SPIKE_$spike: $path differs from its authored block\n"; $failed=1 } }
}
exit($failed ? 1 : 0);
PERL
echo 'All selected spike blocks are classified, uniquely identified, and exact authored sources match their directories.'
