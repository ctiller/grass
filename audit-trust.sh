#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd); cd "$repo_root"
declarations=(
  'Grass.StableId.render_of_empty_namespace'
  'Grass.RequirementKind.extension_injective'
  'Grass.DemandFamily.identity_mem_identities'
  'Grass.DemandFamily.identities_nodup'
  'Grass.DerivedDemandFamily.prior_mem_allKeys'
  'Grass.DerivedDemandFamily.identity_mem_allKeys'
  'Grass.DerivedDemandFamily.allKeys_nodup'
  'Grass.DemandCertificateFamily.get'
  'Grass.ObservationProjection.ext'
  'Grass.ObservationProjection.identity_project'
  'Grass.ObservationProjection.comp_project'
  'Grass.ObservationProjection.identity_comp'
  'Grass.ObservationProjection.comp_identity'
  'Grass.ObservationProjection.comp_assoc'
  'Grass.RelationalSystem.Steps.trans'
  'Grass.RelationalSystem.Steps.graphExtends'
  'Grass.RelationalSystem.InfiniteContinuation.ext'
  'Grass.RelationalSystem.InfiniteContinuation.graphExtendsAt'
  'Grass.RelationalSystem.InfiniteContinuation.prefixSteps'
  'Grass.RelationalSystem.Runs.initialValid'
  'Grass.RelationalSystem.Runs.steps'
  'Grass.RelationalSystem.Runs.ofInitialSteps'
  'Grass.RelationalSystem.Runs.append'
  'Grass.RelationalSystem.Runs.graphExtends'
  'Grass.RelationalSystem.ExecutionPrefix.ext'
  'Grass.RelationalSystem.ExecutionPrefix.append_refl'
  'Grass.RelationalSystem.ExecutionPrefix.append_assoc'
  'Grass.RelationalSystem.ExecutionPrefix.step_eq_append'
  'Grass.BehaviorRefinement.ext'
  'Grass.BehaviorRefinement.refl_trans'
  'Grass.BehaviorRefinement.trans_refl'
  'Grass.BehaviorRefinement.trans_assoc'
  'Grass.BehaviorRefinement.mapSteps'
  'Grass.BehaviorRefinement.mapInfinite'
  'Grass.BehaviorRefinement.mapInfinite_prefixEvents'
  'Grass.BehaviorRefinement.mapInfinite_prefixSteps'
  'Grass.BehaviorRefinement.mapInfinite_refl'
  'Grass.BehaviorRefinement.mapInfinite_trans'
  'Grass.BehaviorRefinement.mapCompletion'
  'Grass.BehaviorRefinement.mapCompletion_refl'
  'Grass.BehaviorRefinement.mapCompletion_trans'
  'Grass.BehaviorRefinement.mapRuns'
  'Grass.BehaviorRefinement.mapPrefix_refl'
  'Grass.BehaviorRefinement.mapPrefix_initial'
  'Grass.BehaviorRefinement.mapPrefix_trans'
  'Grass.BehaviorRefinement.mapPrefix_step'
  'Grass.BehaviorRefinement.mapPrefix_append'
  'Grass.BehaviorRefinement.mapPrefix_events'
  'Grass.BehaviorRefinement.observe_mapPrefix'
  'Grass.BehaviorRefinement.inputOf_mapPrefix'
  'Grass.BehaviorRefinement.hasInput_mapPrefix'
  'Grass.BehaviorRefinement.terminal_mapPrefix'
  'Grass.BehaviorRefinement.mapCompletionAtPrefix'
  'Grass.BehaviorRefinement.mapCompletionAtPrefix_refl'
  'Grass.BehaviorRefinement.mapCompletionAtPrefix_trans'
  'Grass.BehaviorRefinement.preservesAcceptance'
  'Grass.ProjectedDriverCertificate.allKeys_nodup'
  'Grass.ProviderCertificate.allKeys_nodup'
  'Grass.MachineCertificate.allKeys_nodup'
  'Grass.ArtifactCertificate.allKeys_nodup'
  'Grass.VerifiedProgram.requirementKeys'
  'Grass.VerifiedProgram.requirementKeys_nodup'
  'Grass.VerifiedProgram.artifact_identity_mem_requirementKeys'
  'Grass.VerifiedProgram.driver_identity_mem_requirementKeys'
  'Grass.VerifiedProgram.machine_identity_mem_requirementKeys'
  'Grass.VerifiedProgram.portable_identity_mem_requirementKeys'
  'Grass.VerifiedProgram.provider_identity_mem_requirementKeys'
  'Grass.VerifiedProgram.loadedBehavior_exact'
  'Grass.VerifiedProgram.loadedAdequate'
  'Grass.VerifiedProgram.sound'
  'Grass.VerifiedProgram.execution_nonempty'
  'Grass.VerifiedProgram.execution_completes'
  'Grass.VerifiedProgram.CompletionRefinement'
  'Grass.VerifiedProgram.completion_refinement_nonempty'
  'Grass.emitProgram_parses'
)
allowed_axioms=('propext' 'Classical.choice' 'Quot.sound')
library_roots=('Grass'); test_roots=('Tests')
seen_library=0; seen_test=0; seen_declaration=0; seen_axiom=0
while (($#)); do
  option=$1; shift
  (($#)) || { echo "missing value for $option" >&2; exit 2; }
  value=$1; shift
  case $option in
    --library-source-root) ((seen_library++)) || library_roots=(); library_roots+=("$value") ;;
    --test-source-root) ((seen_test++)) || test_roots=(); test_roots+=("$value") ;;
    --declaration) ((seen_declaration++)) || declarations=(); declarations+=("$value") ;;
    --allowed-axiom) ((seen_axiom++)) || allowed_axioms=(); allowed_axioms+=("$value") ;;
    *) echo "unknown option: $option" >&2; exit 2 ;;
  esac
done
normalize_roots() {
  local -n roots=$1
  local index absolute relative
  for index in "${!roots[@]}"; do
    [[ -d ${roots[$index]} ]] || die "Configured source root '${roots[$index]}' does not exist."
    absolute=$(cd -- "${roots[$index]}" && pwd -P)
    if [[ $absolute == "$repo_root" ]]; then relative='.'
    elif [[ $absolute == "$repo_root"/* ]]; then relative=${absolute#"$repo_root"/}
    else die "Configured source root '${roots[$index]}' is outside the repository."
    fi
    roots[$index]=$relative
  done
}
die() { echo "$*" >&2; exit 1; }
contains_exact() { local needle=$1 item; shift; for item in "$@"; do [[ $item == "$needle" ]] && return 0; done; return 1; }
contains_exact Propext propext && die "Axiom allowlist comparison is not ordinal."
command -v perl >/dev/null || die "perl is required by the trust audit."
lake_exe=$(command -v lake || command -v lake.exe) || die 'lake is required by the trust audit.'
lake() { "$lake_exe" "$@"; }
((${#declarations[@]})) || die "At least one declaration must be audited."
normalize_roots library_roots
normalize_roots test_roots
mkdir -p .lake
work=$(mktemp -d '.lake/grass-trust-audit.XXXXXX')
trap 'rm -rf -- "$work"' EXIT
nonce=${work##*/}; nonce=${nonce//[^A-Za-z0-9]/}; token=$nonce
files="$work/files"; sorted="$work/sorted"; : >"$files"
modules=(); entrypoints=()
for root in "${library_roots[@]}" "${test_roots[@]}"; do
  [[ -d $root ]] || die "Configured source root '$root' does not exist."
  find "$root" -type f -name '*.lean' -print0 >>"$files" || die "Could not enumerate '$root'."
done
while IFS= read -r -d '' file; do
    root=${file%%/*}
    module=${file#./}; module=${module%.lean}; module=${module//\//.}
    is_test=0; for test_root in "${test_roots[@]}"; do [[ $file == "$test_root"/* ]] && is_test=1; done
    if ((is_test)); then
      set +e
      perl -0777 -ne 'exit(!/^[\t ]*(?:(?:unsafe|partial|noncomputable)[\t ]+)*def[\t ]+main(?:[\t ]|:)/m)' "$file"
      main_status=$?
      set -e
      if ((main_status == 0)); then entrypoints+=("$module")
      elif ((main_status == 1)); then modules+=("$module")
      else die "Could not inspect test module '$file'."
      fi
    else modules+=("$module")
    fi
done <"$files"
printf '%s\0' "${modules[@]}" | LC_ALL=C sort -zu >"$sorted" || die 'Could not sort module names.'
modules=(); while IFS= read -r -d '' module; do [[ -n $module ]] && modules+=("$module"); done <"$sorted"
: >"$sorted"
if ((${#entrypoints[@]})); then printf '%s\0' "${entrypoints[@]}" | LC_ALL=C sort -zu >"$sorted" || die 'Could not sort entrypoint module names.'; fi
entrypoints=(); while IFS= read -r -d '' module; do [[ -n $module ]] && entrypoints+=("$module"); done <"$sorted"
tmp="$work/audit.lean"
external_module="AuditExternalProbe$token"; internal_leaf="AuditInternalRootProbe$token"; internal_module="Grass.Trust.$internal_leaf"
runtime_module="AuditRuntimeProbe$token"; csimp_module="AuditScopedCSimpProbe$token"; consumer_module="AuditRuntimeConsumer$token"
external_path="$external_module.lean"; internal_path="$internal_leaf.lean"; runtime_path="$runtime_module.lean"; csimp_path="$csimp_module.lean"; consumer_path="$consumer_module.lean"
external_olean=".lake/build/lib/lean/$external_module.olean"; internal_olean=".lake/build/lib/lean/Grass/Trust/$internal_leaf.olean"
runtime_olean=".lake/build/lib/lean/$runtime_module.olean"; csimp_olean=".lake/build/lib/lean/$csimp_module.olean"; consumer_olean=".lake/build/lib/lean/$consumer_module.olean"
cleanup() { rm -rf -- "$work"; rm -f -- "$external_path" "$internal_path" "$runtime_path" "$csimp_path" "$consumer_path" "$external_olean" "$internal_olean" "$runtime_olean" "$csimp_olean" "$consumer_olean"; }
trap cleanup EXIT
marker="grass-trust-audit-complete:$nonce"; audit_command="grass_trust_audit_$token"
write_audit_invocation() { cat <<EOF
open Lean Elab Command
elab "#$audit_command" : command => do
  Grass.Trust.auditVerifiedPrograms
  logInfo "$marker"
#$audit_command
EOF
}
lean_output='' lean_status=0
run_lean() { set +e; lean_output=$(lake env lean "$@" 2>&1); lean_status=$?; set -e; }
require_success() { local context=$1; shift; run_lean "$@"; ((lean_status == 0)) || { printf '%s\n' "$lean_output" >&2; die "$context"; }; }
require_failure_matching() { local pattern=$1 context=$2; shift 2; run_lean "$@"; if ((lean_status == 0)) || ! grep -Eq "$pattern" <<<"$lean_output"; then printf '%s\n' "$lean_output" >&2; die "$context"; fi; }
{
  for module in "${modules[@]}"; do printf 'import %s\n' "$module"; done
  write_audit_invocation
  for declaration in "${declarations[@]}"; do printf '#print axioms %s\n' "$declaration"; done
} > "$tmp"
require_success "Lean could not audit the requested declaration closure." "$tmp"
grep -Fq "$marker" <<<"$lean_output" || die "Lean did not execute the generated trust-audit driver."
reported=0
while IFS= read -r line; do
  if [[ $line =~ ^\'[^\']+\'\ does\ not\ depend\ on\ any\ axioms$ ]]; then ((reported += 1)); continue; fi
  if [[ $line =~ ^\'[^\']+\'\ depends\ on\ axioms:\ \[(.*)\]$ ]]; then
    ((reported += 1)); IFS=',' read -ra used <<<"${BASH_REMATCH[1]}"
    for axiom in "${used[@]}"; do axiom=${axiom#"${axiom%%[![:space:]]*}"}; axiom=${axiom%"${axiom##*[![:space:]]}"}; contains_exact "$axiom" "${allowed_axioms[@]}" || die "Rejected transitive axiom: $axiom"; done
  else printf '%s\n' "$line"; fi
done <<<"$lean_output"
((reported == ${#declarations[@]})) || die "Expected ${#declarations[@]} axiom reports, received $reported."
for module in "${entrypoints[@]}"; do
  printf "Auditing executable test module '%s'.\n" "$module"
  { printf 'import Tests.Foundation\nimport %s\n' "$module"; write_audit_invocation; } > "$tmp"
  require_success "Trust audit failed for executable test module '$module'." "$tmp"
  grep -Fq "$marker" <<<"$lean_output" || die "Trust audit driver did not run for '$module'."
done

cat >"$tmp" <<'EOF'
import Grass.Trust.Audit
open Grass
def passthrough {spec : SpecProcess} (verified : VerifiedProgram spec) : VerifiedProgram spec := verified
#audit_verified_programs
EOF
require_failure_matching 'trust audit found no concrete VerifiedProgram declarations' 'Trust audit accepted generated machinery or a pass-through as a concrete root.' "$tmp"

cat >"$tmp" <<'EOF'
import Tests.Foundation
open Grass
@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec
def cleanHiddenVerifiedProgram : HiddenVerifiedProgram := by
  unfold HiddenVerifiedProgram
  exact Grass.Tests.Foundation.verified
#audit_verified_programs
EOF
require_success 'Trust audit did not accept the irreducible discovery probe.' "$tmp"
grep -q 'cleanHiddenVerifiedProgram' <<<"$lean_output" || die 'Trust audit did not discover a producer behind an irreducible result alias.'

cat >"$internal_path" <<'EOF'
import Tests.Foundation
open Grass
namespace InternalRootAuditProbe
@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec
def _hiddenVerifiedProgram : HiddenVerifiedProgram := by
  unfold HiddenVerifiedProgram
  exact Grass.Tests.Foundation.verified
def _flat_ctor : HiddenVerifiedProgram := by
  unfold HiddenVerifiedProgram
  exact Grass.Tests.Foundation.verified
inductive AuthoredContainer where | node
def AuthoredContainer.node._flat_ctor : HiddenVerifiedProgram := by
  unfold HiddenVerifiedProgram
  exact Grass.Tests.Foundation.verified
end InternalRootAuditProbe
EOF
require_success 'Could not compile the imported underscore-prefixed root probe.' "$internal_path" -o "$internal_olean"
printf 'import %s\n#audit_verified_programs\n' "$internal_module" >"$tmp"
require_success 'Trust audit rejected the imported underscore-prefixed root probe unexpectedly.' "$tmp"
for pattern in 'InternalRootAuditProbe\._hiddenVerifiedProgram' 'InternalRootAuditProbe\._flat_ctor' 'InternalRootAuditProbe\.AuthoredContainer\.node\._flat_ctor'; do grep -Eq "$pattern" <<<"$lean_output" || die 'Trust audit did not discover an imported authored underscore-prefixed root.'; done

cat >"$tmp" <<'EOF'
import Tests.Foundation
open Grass
namespace AuditProbe
axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)
noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)
end AuditProbe
#audit_verified_programs
EOF
require_failure_matching 'emittedBytes.*boxedVerifiedProgram' 'Trust audit did not reject a VerifiedProgram hidden in a container.' "$tmp"
cat >"$tmp" <<'EOF'
import Tests.Foundation
open Grass
axiom AuditProbe.Source._flat_ctor : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)
noncomputable def AuditProbe.Sink._flat_ctor : ByteArray := emitProgram (Classical.choice AuditProbe.Source._flat_ctor)
#audit_verified_programs
EOF
require_failure_matching 'AuditProbe.Sink._flat_ctor.*AuditProbe.Source._flat_ctor' 'Trust audit ignored a user declaration named _flat_ctor.' "$tmp"
cat >"$tmp" <<'EOF'
import Tests.Foundation
axiom Grass._unauditedFalse : False
#audit_verified_programs
EOF
require_failure_matching 'Grass\._unauditedFalse.*rejected axioms' 'Trust audit ignored an authored underscore-prefixed axiom.' "$tmp"

cat >"$internal_path" <<'EOF'
namespace OutsideGrassNamespace
@[extern "grass_trust_module_ownership_probe"]
def identityBytes (bytes : ByteArray) : ByteArray := bytes
end OutsideGrassNamespace
EOF
require_success 'Could not compile the module-ownership trust-audit probe.' "$internal_path" -o "$internal_olean"
printf 'import Tests.Foundation\nimport %s\n#audit_verified_programs\n' "$internal_module" >"$tmp"
require_failure_matching 'OutsideGrassNamespace\.identityBytes.*compiled override.*@\[extern\]' "Trust audit ignored a compiled override outside the owning Grass module's namespace." "$tmp"

cat >"$external_path" <<'EOF'
import Tests.Foundation
open Grass
namespace ExternalAuditProbe
axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)
noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)
end ExternalAuditProbe
EOF
require_success 'Could not compile the imported external trust-audit probe.' "$external_path" -o "$external_olean"
printf 'import %s\n#audit_verified_programs\n' "$external_module" >"$tmp"
require_failure_matching 'ExternalAuditProbe.emittedBytes.*ExternalAuditProbe.boxedVerifiedProgram' 'Trust audit ignored a wrapped producer from an imported external module.' "$tmp"

cat >"$runtime_path" <<'EOF'
namespace ExternalRuntimeAuditProbe
unsafe def replacement (_ : ByteArray) : ByteArray := ByteArray.empty
@[implemented_by replacement]
def identityBytes (bytes : ByteArray) : ByteArray := bytes
end ExternalRuntimeAuditProbe
EOF
require_success 'Could not compile the implemented_by trust-audit probe.' "$runtime_path" -o "$runtime_olean"
cat >"$tmp" <<EOF
import $runtime_module
import Tests.Foundation
open Grass
def ExternalRuntimeAuditProbe.emittedBytes (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :=
  ExternalRuntimeAuditProbe.identityBytes (emitProgram verified)
#audit_runtime_dependencies ExternalRuntimeAuditProbe.emittedBytes
EOF
require_failure_matching 'ExternalRuntimeAuditProbe.identityBytes.*implemented_by.*ExternalRuntimeAuditProbe.replacement' 'Trust audit ignored an implemented_by replacement in the runtime dependency closure.' "$tmp"

cat >"$runtime_path" <<'EOF'
namespace ExternalRuntimeAuditProbe
@[extern "grass_runtime_probe_identity"]
def identityBytes (bytes : ByteArray) : ByteArray := bytes
end ExternalRuntimeAuditProbe
EOF
require_success 'Could not compile the extern trust-audit probe.' "$runtime_path" -o "$runtime_olean"
cat >"$consumer_path" <<EOF
import $runtime_module
import Tests.Foundation
open Grass
def ExternalRuntimeAuditConsumer.emittedBytes (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray := emitProgram verified
EOF
require_success 'Could not compile the extern importing-module trust-audit probe.' "$consumer_path" -o "$consumer_olean"
printf 'import %s\n#audit_runtime_dependencies ExternalRuntimeAuditConsumer.emittedBytes\n' "$consumer_module" >"$tmp"
require_failure_matching 'ExternalRuntimeAuditProbe.identityBytes.*extern' 'Trust audit ignored an extern implementation in an ordinarily imported runtime module.' "$tmp"

cat >"$runtime_path" <<'EOF'
namespace ExternalRuntimeAuditSource
def identityBytes (bytes : ByteArray) : ByteArray := bytes
end ExternalRuntimeAuditSource
EOF
require_success 'Could not compile the scoped-csimp source probe.' "$runtime_path" -o "$runtime_olean"
cat >"$csimp_path" <<EOF
import $runtime_module
namespace ExternalScopedCSimpProbe
unsafe def runtimeReplacement (_ : ByteArray) : ByteArray := ByteArray.empty
@[implemented_by runtimeReplacement]
def replacement (bytes : ByteArray) : ByteArray := bytes
theorem replacement_eq : ExternalRuntimeAuditSource.identityBytes = replacement := rfl
end ExternalScopedCSimpProbe
EOF
require_success 'Could not compile the scoped-csimp replacement probe.' "$csimp_path" -o "$csimp_olean"
cat >"$consumer_path" <<EOF
import $runtime_module
import $csimp_module
import Tests.Foundation
open Grass
section
attribute [local csimp] ExternalScopedCSimpProbe.replacement_eq
def ExternalScopedCSimpProbe.emittedBytes (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :=
  ExternalRuntimeAuditSource.identityBytes (emitProgram verified)
end
EOF
require_success 'Could not compile the imported scoped-csimp consumer probe.' "$consumer_path" -o "$consumer_olean"
printf 'import %s\n#audit_runtime_dependencies ExternalScopedCSimpProbe.emittedBytes\n' "$consumer_module" >"$tmp"
require_failure_matching 'ExternalScopedCSimpProbe.(replacement.*implemented_by.*runtimeReplacement|runtimeReplacement.*unsafe)' 'Trust audit ignored a scoped csimp replacement after its attribute state expired.' "$tmp"

printf 'Trust audit passed for %d declaration(s) and %d executable test module(s).\n' "$reported" "${#entrypoints[@]}"
