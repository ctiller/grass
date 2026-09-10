# AArch64 control instruction slice

This bounded implementation starts from `8fc533af`. It supports the parallel
spike work through reusable instruction semantics, not a program-specific recipe.

`Grass/ISA/AArch64/Control.lean` models CBZ W/X word encoding, canonical decoding,
register testing and normal PC calculation. It preserves GPRs and NZCV, handles
Rt=31 as ZR, and sign-extends the scaled displacement relative to the instruction
PC. Round-trip theorems quantify every operand combination. SVC has an exact
word decoder and a request indexed by that word and the reached CPU projection.
`Request.register` reads the indexed CPU rather than reconstructing an ABI snapshot.

`Grass/ISA/AArch64/Source.lean` uses the existing shared four-byte little-endian
reader/writer. `SourceWord` retains the input and exact suffix equation;
`readSource` preserves parser refusal. `SourceBodyStep.cases` covers every outcome
admitted by this bounded body relation, retaining the actual decode and branch
condition or SVC request. This is not an all-machine-transition VC theorem.

## Explicit remaining obligations

- These CPU projections have no separate memory store. General reached-machine
  fetch, current-code binding and profile admission remain needed. The first-boot
  adapter below supplies a narrower actual physical execute-read connection.
- CBZ describes normal instruction-body control. Debug/interrupt outcomes,
  system effects of BranchTo and any later target-fetch fault are not modeled.
- SVC records a decoded exception request. The routing projection below covers
  selected `CheckForSVCTrap` predicates; configured exception entry remains
  unimplemented. Neither Linux dispatch nor return nor
  provider completion follows from this receipt.
- Linux must connect its selected ABI/personality, request/result and provider
  protocol to the actual machine exception occurrence. Bare-metal uses its own
  execution context; the instruction alone selects no provider.
- No AArch64 source frontend, executable artifact, hardware execution test,
  complete machine model or verified spike is claimed by this delta.

## Evidence

Run `lake build Tests.ISA.AArch64.Control`. The targeted build covers the new
modules and their dependencies; it is not a full repository build. Fixtures test
W/X disagreement on high-only values, register/flag preservation, ZR, signed
offset extrema, backward control, modular PC arithmetic, exact bytes/suffix,
short input and rejection of neighboring instruction families. Printed axioms
for the key round-trip/source/body/citation theorems are only `propext` and
`Quot.sound` (citation checks use `propext` alone).

Independent assembler input is `Tests/ISA/AArch64/control.s`. Clang's AArch64
integrated assembler produced the eight expected words:
`b4000040 34ffffe1 b4ffffff d4000001 d41fffe1 d4000002 d4000003 d4200000`.
The object `.text` was checked using ELF section extraction and `readelf -x .text`.
This tests encoding examples; it is not execution or proof authority.

`Grass/ISA/AArch64/Sources.lean` pins Arm DDI 0602 ID032025 and A64 Guide 1.3,
records declaration subjects and exact locators, and checks citation shape and
retrieval metadata. The instruction diagrams and operation entries were inspected
at PDF pages 142/1012 (printed 139/1009). PDFs are reference-only and are not
committed. The generic citation records currently reside under the X86 directory;
reusing them imports no x86 semantics or dual-vendor policy.

## First-boot execute-read connection

`Grass/ISA/AArch64/BootControl.lean` consumes the memory owner's
`AArch64BootFetch.Word` from `d95e4817` and `bf6e5d6e`. Its `run` checks CPU PC
against the admitted entry, invokes the existing fetch once, and decodes the
actual observed bytes under an explicit `a64LittleEndian` convention. Successful
decoding retains exact source parsing and the body outcome. Unsupported decoding
retains the same completed fetch and reached memory/event instead of returning
to the original snapshot. Width, alignment and access failures retain their
upstream classifications; `run_fetchFailure` and `run_fetched` prove transport.

This is restricted to the first instruction from an admitted fresh physical boot
snapshot. It is not an arbitrary later reached-state fetch, physical-to-virtual
translation, Linux admission, or proof that firmware selected the execution
regime. BootFetch uses a fixed no-fault access attempt; preservation of its
failures does not establish coverage of hardware fault executions. SVC remains
an unadmitted exception request. The completed fetch event is not a completed
exception occurrence or provider call.

`lake build Tests.ISA.AArch64.BootControl` passes (54 dependency/target jobs).
Separate one-read fixtures check taken/untaken CBZ, SVC request, unsupported NOP
with retained read event, PC mismatch, width and alignment refusals. They are
instruction partitions, not a per-spike CPU path. The five printed bridge axioms
are limited to `propext`, `Classical.choice` and `Quot.sound`. No native execution
claim or full-repository test result is attached to this adapter.

## Parametric SVC routing

`SvcRouting.lean` checks an explicit non-secure, non-VHE A64 EL0 routing
configuration. Feature flags and named EL2/EL3 register fields have no defaults.
FGT interception takes priority over ordinary TGE routing and retains the current
PC as preferred return; ordinary routing uses PC+4. Unsupported execution/security
regimes, VHE/RME features, and inconsistent non-secure SCR state return named
refusals. Supported EL1 routing is equivalent to neither interception nor TGE.
The resulting plan retains the original exact decoded request and configuration
check. This is general over explicit inputs and needs no physical snapshot to
compute or prove these laws.

A routing plan is not a machine transition or complete eligibility checker.
Other features are outside this projection, not declared absent. Actual reached
configuration, execute-read provenance, SSAdvance, full saved PSTATE, debug/error/
transaction alternatives, and TakeException remain obligations before admission.
No memory fault result or event is converted into successful exception entry.
Linux retains ownership of ABI conversion and ELF/load-to-user-context production.

`lake build Tests.ISA.AArch64.SvcRouting` checks feature/control gates, routing
priority, explicit unsupported cases, exact request registers and modular return
addresses. Source locators are recorded in `svcRoutingCitation`.

## Linux interface backfill

The ISA/Linux owners agreed to retire Linux's source-indexed request wrapper and
second ISA decode. Linux converts the existing `SupervisorCall.Request` directly
into its selected immediate-zero/native ABI interpretation. ISA owns the general
`SourceWord.bytes_exact` prefix law (using Linux's previously shared
`takeLittleEndian_done` from `3a3866f2`) and `BodyStep.supervisorRequest`, which
extracts existing SVC evidence without decoding again. BootControl retains its
original exact fetch/body receipt, whose step can supply that request. No new
execution adapter or duplicate reached-state structure is introduced. Linux owns
the consumer/test migration; actual exception entry remains a separate obligation.
