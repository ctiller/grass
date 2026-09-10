# Validation command map

Run commands from the repository root. This map explains existing checks;
[CONTRIBUTING.md](../CONTRIBUTING.md) owns the contributor workflow and
[VALIDATION.md](VALIDATION.md) owns validation policy. It is not a report that
these commands passed, and introduces no new gate.

## Choose the evidence you need

| Question | Command and implementation | Scope and limits |
|---|---|---|
| Does the current library and test library compile? | `lake build`; [lakefile.toml](../lakefile.toml) | Default targets are `Grass` and `Tests`, with warnings as errors. Authored `Spikes/` files are not default targets. `lake build Tests` is a focused alternative, not a second required full build |
| Do project producers, runtime dependencies and configured theorem roots meet the trust audit? | `./audit-trust.sh`; [script](../audit-trust.sh), [Trust/Audit.lean](../Grass/Trust/Audit.lean) | Discovers project modules, audits producers and dependencies, and runs rejection probes. Use after building imports. The script exposes focused override options; an overridden population supports only that scope |
| Does the explicit axiom-audit import population cover the files now on disk? | `lake env lean Tools/AxiomAudit.lean`; [tool](../Tools/AxiomAudit.lean) | Re-executes the file census and declaration audit against its imported modules. Complements the root trust script; does not prove a concrete spike endpoint |
| Does the x86 ledger cover the current source population? | `lake env lean Tests/ISA/X86/LedgerAudit.lean`; [audit](../Tests/ISA/X86/LedgerAudit.lean) | Runs the current filesystem census and ledger checks afresh. A cached Lake build can reuse an earlier `run_cmd` result; it is not a fresh filesystem-coverage audit. Ledger coverage is not hardware correctness |
| Were authored source characters re-read by embedding fixtures? | `./check-source-input.sh`; [script](../check-source-input.sh) | Builds Tests and discovers/re-elaborates embedding fixtures. Needed because embedded source files are outside ordinary Lean import dependencies; not authored spike compilation |
| Do annotated and comment-free spike views agree? | `./check-spike-sources.sh`; [script](../check-spike-sources.sh) | Corpus consistency and source classification, not proof checking |
| Do relative Markdown targets exist? | `./check-doc-links.sh`; [script](../check-doc-links.sh) | Checks target paths across Markdown. Does not validate heading fragments, external URLs, or the truth of linked claims |

Bash scripts run in Git Bash on Windows or Bash on Linux. The corpus/trust
scripts also use Perl; Lean commands use the toolchain pinned in
[lean-toolchain](../lean-toolchain). Build imports before direct Lean audits.
The source-input script already performs its own Tests build.

## Find specialized validation

- [Corpus workflow](../.github/workflows/corpus.yml) and
  [library workflow](../.github/workflows/library.yml): exact CI steps and tool
  invocations. Inspect their current contents rather than assuming this map is
  a copy of every CI job.
- [Windows probes](../probes/windows/README.md): API observations and executable
  capture procedures.
- [Native x86 harness](../Tools/x86-native/README.md),
  [stack campaign](../Tools/x86-native/STACK.md), and
  [validation limits](../Tools/x86-native/VALIDATION.md): physical observations
  and bounded campaign evidence.
- [Disassembly tools](../Tools/disasm/README.md): imported-binary checks and
  fixture tooling.
- [Implementation ratchet](IMPLEMENTATION_RATCHET.md): future acceptance
  commands and evidence contracts; do not assume proposed commands exist today.

For a report, retain the command, revision, result and any narrowed population.
Use the [endpoint index](ENDPOINT_INDEX.md) to identify the connection a check
supports before describing it as whole-program evidence.
