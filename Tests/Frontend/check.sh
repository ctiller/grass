#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
lake_exe=$(command -v lake || command -v lake.exe)
lake() { "$lake_exe" "$@"; }

# This is the current construction gate, not a completed VerifiedProgram gate.
lake build Grass.Assembly.X86 Grass.Platform.Win32 Grass.Spec.Console Grass.Spec.Resource Tests.Frontend.Source
mkdir -p .lake/build/lib/lean/Spikes/1_Hello_World
lake env lean Spikes/1_Hello_World/Spec.lean -o .lake/build/lib/lean/Spikes/1_Hello_World/Spec.olean

fixture=$(mktemp .lake/frontend-hello-XXXXXX.lean)
rejected=$(mktemp .lake/frontend-rejected-XXXXXX.lean)
diagnostic=$(mktemp .lake/frontend-rejected-XXXXXX.log)
audit=$(mktemp .lake/frontend-audit-XXXXXX.lean)
trap 'rm -f -- "$fixture" "$rejected" "$diagnostic" "$audit"' EXIT

# Preserve all authored declarations through helloSource verbatim. Only the
# unavailable emission import and certificate suffix are outside this gate.
perl -0777 -e '
  local $/; my $source = <>;
  my $cut = index($source, "def helloVerified");
  die "missing certificate boundary\n" if $cut < 0;
  my $prefix = substr($source, 0, $cut);
  $prefix =~ s/^import Grass\.Emit\r?\n//m or die "missing emission import\n";
  print $prefix;
  print "\nexample : helloSource.table = helloStatics := (MachineSource.ofHello?_inputs (Option.some_get _).symm).2\n";
  print "end Grass.Spikes.HelloWorld\n";
' Spikes/1_Hello_World/Program.lean > "$fixture"
lake env lean "$fixture"

# A source mutation must fail checked construction; parsing an assembly-shaped
# declaration alone must never produce a MachineSource.
perl -0777 -pe '
  s/mov transferred, 0/mov transferred, unsupported_value/g == 1
    or die "expected exactly one transferred initialization\n";
' "$fixture" > "$rejected"
if lake env lean "$rejected" > "$diagnostic" 2>&1; then
  printf "Unsupported source unexpectedly passed construction.\n" >&2
  exit 1
fi
if ! grep -q "decide" "$diagnostic"; then
  cat "$diagnostic" >&2
  printf "Mutation failed outside the expected checked-producer proof.\n" >&2
  exit 1
fi

# Reuse the repository audit's actual declaration/axiom/override checks over
# the frontend import closure. The full-tree coverage gate remains with whole
# certificate integration; its legacy public modules are not migrated yet.
perl -0777 -e '
  local $/; my $source = <>;
  my $start = index($source, "open Lean");
  die "missing audit body\n" if $start < 0;
  my $body = substr($source, $start);
  $body =~ s/let onDisk ← Grass\.Tools\.modulesOnDisk \(System\.FilePath\.mk "Grass"\) `Grass/let onDisk := imported.filter (fun name => (`Grass).isPrefixOf name)/
    or die "audit coverage declaration changed\n";
  # Full-repository documentation is not a claim made by this generated check.
  $body =~ s{/-.*?-/}{}sg;
  $body =~ s/^  -- Coverage first:.*\r?\n/  -- Inventory only the imported frontend closure.\n/mg;
  $body =~ s/axiom audit: \{audited\}/focused frontend import-closure declaration audit: {audited}/
    or die "audit result format changed\n";
  print "import Grass.Assembly.X86\nimport Grass.Platform.Win32\nimport Tests.Frontend.Source\n";
  print $body;
' Tools/AxiomAudit.lean > "$audit"
printf "Focused frontend import-closure declaration audit only; NOT a full repository census or audit-trust adversarial probes. Counts below are computed for this run.\n"
lake env lean "$audit"
printf "Unchanged Hello specification/source construction and focused import-closure audit pass; unsupported source rejected. Certificate suffix and full repository trust gates remain outside this check.\n"
