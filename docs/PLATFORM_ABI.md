# Platforms, effects, and ABIs

## 1. Effect demands and provider choice

High- and mid-level APIs use law-bearing typeclasses. An abstract class may name
console, filesystem, graphics, process, allocation, or synchronization effects;
a more specific class may demand Vulkan, Metal, Win32, or another provider.

Programs are parameterized by an explicit `ProviderEnv` owned by the
`PlatformPlan`. Effect classes are projections from that environment and are
indexed by a nominal provider key whose type-level identity includes the selected
profile. The exact dictionary/environment value used to elaborate and prove the
high-level program is retained through realization; Grass must not re-run ambient
instance search and obtain a second dictionary for the same key.

Realization proves dictionary identity, not merely equality of key names. An
alternative implementation may enforce uniqueness by construction, but two
instances with different operations or laws for one key must be unrepresentable
in one verified environment.

Intentional multi-provider use requires distinct keys and a compatibility or
noninteraction proof. Platform, ISA, and set of APIs used remain independent
axes joined by plan constraints.

Platform plans select platform APIs, ABI/calling conventions, ISA capability
profiles, loader/runtime context, and coherent provider dictionaries. They must
not absorb algorithmic tuning merely because one program uses it: codec search
depth, hash policy, buffer size, sort fanout, and similar heuristics belong to
reviewed implementation plans or authored assembly modules. Changing such a
heuristic must not change the platform-plan type or invalidate unrelated
provider proofs.

Provider selection also accumulates explicit initial execution-context
requirements. A `VerifiedProgram` closes them by exporting an
`AdmissibleExecutionContext` domain to its public theorem, proving that domain
independently inhabited, and threading the chosen context through loading and
initial-state construction. Requirements may instead be discharged by a proved
runtime check. They may never remain as an invisible premise or be made true by
defining admissibility in terms of successful execution.

## 2. API model

Each API operation exports a child process protocol. Request, pending,
intermediate effect, dependent response, callback, cancellation, fault,
violation, and terminal states are process transitions with exact occurrence
identities. A synchronous call suspends its parent until the child reaches a
terminal projection; an asynchronous call exposes child events. The ABI
call/return boundary realizes this protocol rather than defining its semantics.
See [PROCESS.md](PROCESS.md).

Every API operation declares:

- complete input domain and memory shape;
- all permitted return values and dependent output-memory states;
- partial completion, interruption, cancellation, and retry behavior;
- register/stack/hidden context requirements at its ABI boundary;
- allocation provenance, access rights, ownership, and lifetime of pointers;
- synchronization, scheduling, and observation events;
- obligations created, discharged, or transferred;
- progress and blocking assumptions;
- failure and environment-violation outcomes;
- citations and validation probes.

Each API profile also proves response adequacy. For every reachable well-formed
request, either at least one response is allowed or the contract explicitly
admits a pending/infinite blocking execution. Its `Allowed` relation covers every
behavior permitted by the cited external contract; it may restrict behavior only
when a cited stronger platform precondition justifies the restriction. A profile
with `Allowed q r := False` and no pending behavior is unusable.

Borrowed capabilities cross loops/calls only through a provider footprint and
stability theorem. It proves exact provider identity, handle/resource validity
and lifetime, non-close/non-transfer behavior, disjoint memory footprint,
obligation preservation, and capability reconstruction on every normal,
pending, cancellation, and narrow-violation exit used by the caller. Preserving
the register bits which carry a handle is necessary but never sufficient.

An API may classify narrowly malformed returned results and attach a
`ViolationReturnEnvelope`. The affine envelope is indexed by the pending
boundary occurrence, pre/post worlds, call ID, exact loan IDs, boundary-step
witness, result, exclusive violation class, and first-violation proof. It independently
proves every fact used by a containment tail; it never follows from the friendly
name of the violation. For Spike 1, `.excessWriteCount` may retain ordinary
Win64 control return, an initialized in-bounds `bytesWritten` slot, returned call
loans, and reconstructed frame authority while proving only that the reported
count exceeds the request. Memory-write, ABI, or control-transfer violations do
not receive that envelope.

External implementations are trusted relative to this contract, but the
boundary is always modeled and extensively tested.

Conditional liveness uses a separate bridge from provider vocabulary to the
fixed predicate owned by execution semantics:

```lean
structure ConcreteResponsiveStrategy (plan : PlatformPlan) where
  strategy : ConcreteEnvironmentStrategy plan
  adequate : ConcreteStrategyAdequate plan strategy
  resultComplete : ConcreteFrontierComplete plan strategy
  responsive : ConcreteResponsive plan strategy

structure ResponsivenessBridge (spec : SpecProcess) (plan : PlatformPlan) where
  concreteInhabited : Nonempty (ConcreteResponsiveStrategy plan)
  project : ConcreteResponsiveStrategy plan -> AbstractEnvironmentStrategy spec
  realizes : ∀ s, StrategyRefines plan spec s.strategy (project s)
  projectAdequate : ∀ s, StrategyAdequate (project s)
  projectComplete : ∀ s, FrontierComplete spec (project s)
  responsive : ∀ s, EnvironmentResponsive spec (project s)
```

`ConcreteStrategy` and `ConcreteResponsive plan s` may mention `WriteFile`,
scheduling, devices, or user actions; `EnvironmentResponsive spec` may not.
Both strategy types denote branching sets of compatible histories. `project`
selects the abstract branching strategy corresponding to the concrete one.
`realizes` couples their complete generated-history sets, provider/scheduler
events, choices, reachable frontiers, maximal continuations, and eventual
settlement; it cannot ignore `s` and return an unrelated responsive history.
`responsive` applies universally to that exact projection, from which
both the abstract predicate and its inhabitance follow. The bridge is not response adequacy:
adequacy supplies a response-or-pending behavior for each request, while this
witness supplies one coherent branching strategy under which every compatible
maximal continuation satisfies the eventual-settlement premises used by the
liveness theorem. Its inhabitant may not be derived from an
execution whose existence already consumes the conditional termination result.
`ConcreteStrategyAdequate` supplies prefix closure, the concrete root, continuation totality,
and maximal executions. The separate unrestricted `profileAdequacy`/response
domain supplies every permitted infinite-pending behavior; a responsive
strategy is allowed to exclude those branches under its named premise.
`StrategyRefines` preserves
and reflects root compatibility, continuation coverage, allowed-response
completeness, maximality, and every
concrete-to-abstract history projection; it cannot relate two empty trees.

## 3. ABI profile

An ABI profile is the complete contract between two systems. It includes calling
convention, argument/result placement, clobbers, stack and unwind shape, memory
shape, thread-local/hidden state, callbacks, ghost transfer, obligations,
faults, interruption, cancellation, and progress. Call sites prove the entry
contract; returns and exceptional exits prove their respective postconditions.

Over-approximating clobbers or resource use is acceptable. Omitting a permitted
behavior is unsound.

Win64 automatic unwind generation applies only after a decidable
`Win64UnwindEncodablePrologue` recognizer accepts the exact encoded prologue
prefix and its frame layout. It produces `.pdata/.xdata` plus a proof that the
metadata reverses that prefix. A semantically valid custom prologue outside the
Windows unwind language must supply a separately verified encodable unwind
description or is rejected locally; arbitrary assembly is never falsely claimed
to have derivable standard metadata.

Block and loop verification automatically frames a nonvolatile register or
disjoint stack/resource fact when it is established before the region, absent
from every body write-set, preserved by every called ABI, and unchanged on all
back edges. The resulting header contract remains inspectable. The author must
state transformed resources, unusual aliasing, registers intentionally clobbered
despite ABI convention, and any fact for which those mechanical frame
conditions cannot be proved.

Numeric `TerminalStatus` is an abstract observable capability, not intrinsically
a process exit. A platform realization proves how its physical protocol exposes
and normalizes the demanded value: for example Win32 `ExitProcess`, a Linux/WASI
exit interface, semihosting, or a hypervisor/test device. A platform without an
observable status channel cannot realize a specification that demands one.

The provider supplies a law-bearing terminal protocol for the exact status
subset demanded by the specification. It proves:

- realizability/preservation: requesting a status can produce a physical
  terminal observation that normalizes to exactly that status;
- reflection: every physical terminal event reachable from this program's
  demanded terminal requests arises from its declared status/outcome path,
  while other provider-supported statuses, abnormal termination, and unsupported
  termination remain outside that program-relative relation;
- distinguishability: statuses used to distinguish accepted outcomes remain
  injective through encoding and physical observation on the demanded subset;
- terminal/resource fidelity: pending versus terminal behavior, forbidden
  normal return, and outcome-indexed obligation disposition are preserved.

The platform plan rejects a provider if its physical range or channel cannot
construct these laws. A narrower physical encoding is acceptable when all
demanded values fit and remain distinguishable.

Conceptually the provider field is:

```lean
structure TerminalProtocolLaws
    (program : TerminalRequestGraph) (plan : PlatformPlan)
    (provider : TerminalProvider) where
  demanded := program.demandedStatuses
  demandedExact : demanded = SpecificationDemandedStatuses program.spec
  realize        : ∀ occurrence req,
      DeclaredTerminalRequest program occurrence req ->
      ∃ e, ConformingTerminalRun provider occurrence req e
  preserve       : ∀ occurrence req e,
      DeclaredTerminalRequest program occurrence req ->
      ConformingTerminalRun provider occurrence req e ->
      normalize e = req.status
  specEvent_iff  : ∀ occurrence req e,
      SpecTerminalEvent program plan occurrence req e ↔
        DeclaredTerminalRequest program occurrence req ∧
        RawTerminalReachable plan occurrence req e
  reflect        : ∀ occurrence req e,
      SpecTerminalEvent program plan occurrence req e ->
      ConformingTerminalRun provider occurrence req e ->
      normalize e = req.status ∧ DeclaredPath occurrence req e
  classify : ∀ occurrence req e,
      DeclaredTerminalRequest program occurrence req ->
      RawTerminalEvent program plan occurrence req e ->
      TerminalEventClass provider program occurrence req e
  distinguish    : ∀ a ∈ demanded, ∀ b ∈ demanded, a ≠ b ->
                      DistinguishablePhysicalObservations provider a b
  resourceFidelity : PreservesPendingTerminalAndDisposition provider demanded
```

`SpecTerminalEvent` is thus equivalent to operational reachability from the
exact program, plan, and declared request occurrence; it may not be defined using
`DeclaredPath` or `normalize`, which would make reflection circular or allow
events to be filtered away. The final Lean relation may
express nondeterministic physical runs differently, but the separately named
laws are mandatory. `TerminalEventClass` is an exhaustive exclusive dependent
sum with constructors for a conforming run of that exact occurrence/request,
the exact first environment violation, or a modeled fault. It is not a free
predicate or overlapping disjunction.

An assembly implementation need not contain defensive instructions for a
provider response excluded by `Allowed`: the full theorem already ends before
the first environment-contract violation. Containment after that boundary is an
explicit implementation policy. If selected, its instructions and pre-boundary
safety are verified normally; it must not be mistaken for a conforming
functional branch.

When containment is selected, the verifier accepts only a tail whose entry
contract is the exact `ViolationReturnEnvelope` for the named class.
`.trapExcessWriteCount` therefore verifies the read/compare/trap tail for the
narrow value-domain violation; it says nothing after an arbitrary provider
violation.

Coverage is mandatory for every selected class: each reachable matching first
violating boundary-step witness must construct its exact affine envelope and a
raw state at the literal tail entry. The tail theorem consumes that state, and
erasure/artifact loading compose it into a separately named emitted-byte
containment theorem. This result remains outside `AssuranceResult`; selecting no
containment yields no claim after the fundamental pre-violation boundary.

## 4. Initial Win32 x64 profile

The initial platform API baseline is Win32 x64 with Windows 10 as the minimum
profile. It uses documented Win32 APIs rather than direct system calls. The first
program imports `GetStdHandle`, `WriteFile`, and `ExitProcess` from the provider
set derived from its operations.

The profile includes:

- Microsoft x64 calling convention and complete stack/unwind requirements;
- PE32+ image loading with ASLR enabled;
- section-relative/abstract instruction addresses before layout;
- standard final section permissions;
- loader mapping, relocation, import resolution, IAT patching, and entry transfer;
- partial `WriteFile` results and all documented failure outcomes;
- a zero exit code for specified success and nonzero codes for failure.

The Windows version names the minimum API contract only. It does not assert a
deployment policy. Each API retains its own documented minimum and behavior
citations so later profiles can prove inclusion or restriction.

## 5. Provider families expected

Versioned extension points are intended for Windows, Linux, macOS, bare metal,
WASI, Vulkan, Metal, WebGPU, and SQL data providers. Known target sketches are
reviewed to avoid obvious blockers, but the Win32/x86 foundation is not claimed
permanently sufficient. A genuinely different target may add vocabulary through
a reviewed version and migration/refinement theorems preserving old profiles.
Global coherence constraints belong to the platform plan rather than ambient
instance search.

Profiles may export audited named plan values for common coherent provider sets,
such as `PlatformPlan.win10X64StandardConsole`. The value retains the exact
nominal provider dictionaries and has an inspectable `.provide` expansion;
defaults are never ambient instance search. Substituting one provider constructs
a distinct plan and rechecks coherence, requirements, responsiveness, and
terminal protocol laws.
