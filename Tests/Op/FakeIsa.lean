import Grass.Op.Step

/-!
# The seam fixture: two independent operation families

This file is the acceptance criterion for M1's facet seam. It lives outside
`Grass/Memory/`, defines two operation families that know nothing about each
other, and drives them through the generic transition relation.

Nine things it has to demonstrate, and does:

1. a new operation type introduced without editing a master sum or a registry;
2. that type packaged existentially as `SomeOperation`;
3. read, write, read-modify-write, allocate, release, and atomic facets declared;
4. fault and obligation facets declared;
5. the generic transition consuming those facets;
6. invalid provenance, ranges, and ledger effects rejected;
7. alias conflicts detected across *distinct* allocations naming the same bytes;
8. partial effects preserved when a compound operation faults;
9. a second, independently defined family coexisting with the first.

If any of these could not be written cleanly, the seam would not be real. The two
families below share no type, no registry entry, and no import of each other —
only `Grass.Op.Facets`.
-/

namespace Grass.Tests.FakeIsa

open Grass.Core Grass.Memory Grass.Obligation Grass.Op Grass.Std.Logical

/-! ## Shared setting -/

private def allocs₀ : FreshSupply AllocTag := .initial
private def allocs₁ := allocs₀.fresh.2
private def allocs₂ := allocs₁.fresh.2

/-- A data buffer. -/
def bufferAlloc : AllocId := allocs₀.fresh.1

/-- A second allocation that maps the *same bytes* as `bufferAlloc` — a
host-visible view of a device buffer, say. Distinct identity, same storage. -/
def viewAlloc : AllocId := allocs₁.fresh.1

/-- A read-only allocation. -/
def constAlloc : AllocId := allocs₂.fresh.1

/-- A stack reservation, used by the frame authority provider. -/
def stackAlloc : AllocId := allocs₂.fresh.2.fresh.1

/-- Storage reachable only through a borrow, used by the loan authority
provider. Separate from `bufferAlloc` so that guarding it does not put every
ordinary buffer access behind a loan — a loan provider guards what is borrowed,
not everything the program can name. -/
def borrowedAlloc : AllocId := allocs₂.fresh.2.fresh.2.fresh.1

private def epochs₀ : FreshSupply EpochTag := .initial
/-- The first epoch. -/
def epoch₀ : EpochId := epochs₀.fresh.1

private def contexts₀ : FreshSupply ContextTag := .initial
/-- The program thread. -/
def thread₀ : ContextId := contexts₀.fresh.1

/-- The device engine. A genuinely distinct execution context, which is what
makes its access to shared bytes a conflict rather than ordinary program order. -/
def engine₀ : ContextId := contexts₀.fresh.2.fresh.1

private def obligations₀ : FreshSupply ObligationTag := .initial
/-- The obligation an allocation creates. -/
def releaseObligationId : ObligationId := obligations₀.fresh.1

/-- An obligation identity that is never live. -/
def ghostObligationId : ObligationId := obligations₀.fresh.2.fresh.1

/-- A second identity that is never live. -/
def ghostObligationId₂ : ObligationId := obligations₀.fresh.2.fresh.2.fresh.1

/-- An identity a fabricating delta would install. -/
def fabricatedObligationId : ObligationId :=
  obligations₀.fresh.2.fresh.2.fresh.2.fresh.1

/-- An identity that is fresh before the effect runs, which two creates in one
effect both target. -/
def collidingObligationId : ObligationId :=
  obligations₀.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- Provenance of the buffer. -/
def bufferProv : Provenance :=
  { space := .cpuVirtual, root := bufferAlloc, epoch := epoch₀, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- Provenance of the aliasing view. Different allocation identity, same bytes. -/
def viewProv : Provenance := { bufferProv with root := viewAlloc, source := .mappedFile }

/-- Provenance of the read-only allocation. -/
def constProv : Provenance := { bufferProv with root := constAlloc, source := .imageMapping }

/-- Provenance of the stack reservation. -/
def frameProv : Provenance := { bufferProv with root := stackAlloc, source := .stack }

/-- Provenance of the borrowed storage. -/
def borrowedProv : Provenance := { bufferProv with root := borrowedAlloc }

/-- Provenance naming the buffer in an epoch it has moved past. Structurally
impeccable; the state is what refuses it. -/
def staleProv : Provenance := { bufferProv with epoch := epochs₀.fresh.2.fresh.1 }

/-- A descriptor builder, so the families below read as declarations. -/
def acc (prov : Provenance) (range : ByteRange) (addr : Nat) (intent : AccessIntent)
    (perm : Permission) (readsInit : Bool) (writesInit : Bool)
    (effect : LedgerEffect := []) (atomic : Bool := false)
    (context : ContextId := thread₀) : AccessDescriptor :=
  { context := context, address := .numeric (BitVec.ofNat 64 addr), space := .cpuVirtual
    provenance := prov, range := range
    intent := { intent with isAtomic := atomic }
    requiredPermission := perm, alignment := 1
    initialization := if readsInit then .allBytesInitialized else .readsNothing
    producesInitialized := writesInit
    ordering := if atomic then { atomicity := .atomic } else .plain
    admittedFaults := [.pageFault], ledgerEffect := effect }

/-! ## Family one: a small load/store machine

Introduced without editing anything below it. There is no master sum type to
extend and no registry to register with; the family declares an instance and is
done. -/

/-- The first family's operation type. -/
inductive Alpha where
  /-- Load eight bytes from the buffer. -/
  | load
  /-- Store eight bytes to the buffer. -/
  | store
  /-- Atomically read and modify the buffer. -/
  | atomicAdd
  /-- Reserve the buffer, creating a release obligation. -/
  | reserve
  /-- Release the buffer, discharging it. -/
  | release
  /-- Divide by a value loaded from the buffer, faulting after the load. -/
  | divide
  /-- Store through the aliasing view. -/
  | storeThroughView
  /-- A store that declares only read-only permission. -/
  | badPermission
  /-- A store naming a range past the end of its allocation. -/
  | badRange
  /-- A store whose ledger effect would destroy a duty without discharging it. -/
  | badLedger
  /-- A well-formed store presenting an epoch the allocation has moved past. -/
  | staleEpoch
  /-- A store split across two substeps under a profile-owned visibility rule. -/
  | splitStore
  /-- Discharges an obligation that was never live. -/
  | dischargeGhost
  /-- Joins two obligations that were never live into a new one. -/
  | joinGhosts
  /-- Splits a ghost obligation into two live-looking ones. -/
  | splitGhost
  /-- Two substeps, the first of which the state denies. -/
  | deniedThenStore
  /-- Discharges the release obligation while presenting authority under a
  protocol that does not govern it. -/
  | dischargeWithWrongAuthority
  /-- Writes the buffer through a borrowed slice, which requires a live loan. -/
  | writeThroughLoan
  /-- Writes a stack slot, which requires a live frame. -/
  | writeStackSlot
  /-- One effect containing two creates of the same initially-fresh identity,
  with distinguishable payloads. Each delta is individually applicable against
  the ledger as it stands before the effect runs. -/
  | createTwice
deriving DecidableEq, Repr

/-- The divide-error fault this family can raise. Named so the fixtures can
compare against the fault the transition recorded, rather than restating a
string. -/
def divideError : FaultClassId := ⟨⟨"divideError"⟩⟩

/-- The buffer protocol, and the authority this family holds under it. A real
family obtains this from its profile; the fixture mints one so the seam can be
exercised, which is exactly the gap `ProtocolAuthority`'s docstring records as an
M10 obligation. -/
def bufferProtocol : ObligationProtocolId := ⟨⟨"fake.buffer"⟩⟩

/-- Authority to act under `bufferProtocol`. -/
def bufferAuthority : ProtocolAuthority bufferProtocol := ⟨⟨"fake.isa"⟩⟩

/-- A different protocol, and authority under it. Used to show that authority for
one protocol does not authorize a duty governed by another. -/
def otherProtocol : ObligationProtocolId := ⟨⟨"fake.other"⟩⟩

/-- Authority to act under `otherProtocol`, which governs nothing here. -/
def otherAuthority : ProtocolAuthority otherProtocol := ⟨⟨"fake.isa"⟩⟩

/-- Two duties sharing one identity, distinguishable by kind. A single effect
creating both is the collision `LedgerEffectApplicable` must catch. -/
def collidingFirst : Obligation :=
  { id := collidingObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- The second, same identity and a different kind, so the two are telling
apart in the resulting ledger. -/
def collidingSecond : Obligation :=
  { id := collidingObligationId, kind := .closeHandle
    protocol := bufferProtocol, owner := thread₀ }

/-- The duty a fabricating delta would conjure. -/
def fabricatedObligation : Obligation :=
  { id := fabricatedObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- The release obligation `reserve` creates. -/
def releaseObligation : Obligation :=
  { id := releaseObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- The first family's facet declaration. This is the whole of what a family
supplies; nothing else in the tree changes. -/
instance : HasOperationFacets Alpha where
  facets
    | .load =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite
            true false))
          faults := some [.pageFault], restartability := some .restartable
          ordering := some .plain }
    | .store =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .atomicAdd =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .readWrite
            .readWrite true true [] true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { atomicity := .atomic, order := .acquireRelease } }
    | .reserve =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.create bufferProtocol bufferAuthority releaseObligation]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .release =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority releaseObligationId]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .divide =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false)
                  , .compute [divideError] ]
              onFault := .priorEffectsVisible }
          faults := some [divideError], restartability := some .notRestartable
          ordering := some .plain }
    | .storeThroughView =>
        { memoryEffects := some (.single (acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badPermission =>
        { memoryEffects := some (.single (acc constProv ⟨0, 8⟩ 0x1000 .write .readOnly
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .badRange =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 4096⟩ 0x1000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .badLedger =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority releaseObligationId []]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .staleEpoch =>
        { memoryEffects := some (.single (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority ghostObligationId]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .joinGhosts =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.join bufferProtocol bufferAuthority [ghostObligationId, ghostObligationId₂] fabricatedObligation]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .splitGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority ghostObligationId [fabricatedObligation]]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .writeThroughLoan =>
        { memoryEffects := some (.single (acc borrowedProv ⟨0, 8⟩ 0x3000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .writeStackSlot =>
        { memoryEffects := some (.single (acc frameProv ⟨0, 8⟩ 0x2000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .createTwice =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [ .create bufferProtocol bufferAuthority collidingFirst
            , .create bufferProtocol bufferAuthority collidingSecond ]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeWithWrongAuthority =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge otherProtocol otherAuthority releaseObligationId]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .deniedThenStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨8, 8⟩ 0x1008 .write .readWrite false true) ]
              onFault := .priorEffectsVisible }
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .splitStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .profileSpecific ⟨"fake.splitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }

/-! ## Family two: an independently defined device family

Written as if by a different author. It shares no type with `Alpha`, does not
import it, and is packaged the same way. -/

/-- The second family's operation type. -/
inductive Beta where
  /-- A device engine writes the buffer. -/
  | dmaWrite
  /-- An operation that declares no memory effects at all. -/
  | undeclared
deriving DecidableEq, Repr

instance : HasOperationFacets Beta where
  facets
    | .dmaWrite =>
        { memoryEffects := some (.single
            { acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true, isDevice := true } })
          faults := some [.deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .undeclared => {}

/-! ## The profile and the starting state -/

/-- The profile's address spaces, obligation kinds, and fault classes. -/
def vocabulary : AdmittedVocabulary :=
  { addressSpaces := .cpuOnly
    faultClasses := ⟨[.pageFault, .deviceFault, divideError]⟩
    allocationSources := ⟨[.virtualAlloc, .mappedFile, .imageMapping, .stack]⟩
    provenanceStepKinds := ⟨[]⟩
    auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[.releaseAllocation, .closeHandle]⟩ }

/-- A profile whose §10 package is explicitly unproved. It is a checklist of
propositions, not evidence for them, and this fixture does not pretend otherwise:
`RequiredProofPackage.Holds` is exactly what nothing here establishes. -/
def profile : MemoryProfile :=
  { id := ⟨"fake.isa"⟩, vocabularyVersion := 1, vocabulary := vocabulary
    package :=
      { accessDescriptorSoundness := True
        rangeProvenanceInitializationPreservation := True
        permissionEnforcementAndFaultFidelity := True
        loanMapLaws := True, consistencyGraphWellFormedness := True
        raceFreedomConsequences := True, synchronizationAndObligationTransfer := True
        allocatorFreshnessTeardownEpoch := True, callStackFrameLifetime := True
        erasurePreservation := True, validationMetadata := True } }

/-! ## Two authority providers, authored outside `Grass/`

This is the extension test. `docs/MEMORY_MODEL.md` has several kinds of authority
— loans in §3, pins in §5.1, frame lifetimes in §6, lock tokens in §7.4, device
queue ownership in §7.5 — and a memory profile cannot enumerate them ahead of
time. The question is whether adding one costs a redesign of how operations are
packaged.

It does not. Both providers below are defined in this file. Neither
`AccessDescriptor`, `OperationFacets`, `HasOperationFacets`, `SomeOperation`, nor
the shape of `step` changes to accommodate them, and the operations that need
them declare their accesses exactly as every other operation does.

What this does *not* demonstrate is a loan or frame **model**. There is no split,
join, freeze, exclusivity-iff-empty, pinning, rebasing, or call-framing theorem
here; those are M3 and M4. The claim is about the seam, not about borrowing. -/

/-- A borrowed slice must be covered by a live grant of kind `loan`. -/
def loanProvider : AuthorityProvider where
  id := ⟨"fake.loan"⟩
  violationClass := .authorityUnavailable
  refuses state d :=
    decide (d.provenance.root = borrowedAlloc) &&
    !decide (state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent)

/-- Stack storage must be covered by a live grant of kind `frame`. A distinct
provider over the same grant table, distinguished only by the grant kind it
demands — which is the point: two authority kinds, one mechanism. -/
def frameProvider : AuthorityProvider where
  id := ⟨"fake.frame"⟩
  violationClass := .authorityUnavailable
  refuses state d :=
    decide (d.provenance.root = stackAlloc) &&
    !decide (state.memory.GrantedOfKind .frame d.context d.provenance d.range d.intent)

/-- Every operation must declare its memory effects and its faults. -/
def policy : StepPolicy :=
  { profile := profile
    requiredFacets := [.memoryEffects, .faults, .restartability]
    oracle := .zeroed
    authorities := [loanProvider, frameProvider]
    violationClassesDeclared := by decide
    vocabularyWellFormed := by decide }

/-- A vocabulary that declares one address-space identity twice, with different
representations, is not well formed — so no `StepPolicy` can be built from it.
`find?` returns the first match, so without this check which version an access was
validated against would depend on list order. -/
theorem duplicate_space_vocabulary_is_rejected :
    ¬ ({ vocabulary with
          addressSpaces := ⟨[ { id := .cpuVirtual, repr := .symbolic
                                memoryType := .writeBack, coherence := .hostCoherent }
                            , AddressSpace.cpuVirtual64 ]⟩ } :
        AdmittedVocabulary).WellFormed := by decide

/-- The buffer, its aliasing view, and a read-only allocation. The alias is
declared here, in the state, because whether two allocations name the same bytes
is a fact about the machine and not about provenance. -/
def memory₀ : MemoryState :=
  (((MemoryState.empty.allocate bufferAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true
        initialized := (List.range 64) }).allocate viewAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true
        initialized := (List.range 64) }).allocate constAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readOnly, live := true
        initialized := (List.range 64) }).alias bufferAlloc viewAlloc

/-- The stack reservation the frame provider guards. -/
def memory₁ : MemoryState :=
  (memory₀.allocate stackAlloc
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      permission := .readWrite, live := true, initialized := List.range 64 }).allocate
    borrowedAlloc
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      permission := .readWrite, live := true, initialized := List.range 64 }

/-- The starting machine state: allocations exist, but no authority is held. -/
def state₀ : MachineState := .initial memory₁

private def grants₀ : FreshSupply GrantTag := .initial

/-- A loan over the buffer, held by the program thread. -/
def bufferLoan : GrantId := grants₀.fresh.1

/-- A live call frame over the stack reservation. -/
def liveFrame : GrantId := grants₀.fresh.2.fresh.1

/-- The same state with both grants live. -/
def stateWithAuthority : MachineState :=
  { state₀ with
    memory :=
      (state₀.memory.grant bufferLoan
        { kind := .loan, holder := thread₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).grant liveFrame
        { kind := .frame, holder := thread₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite } }

/-- Step one `Alpha` operation. -/
def stepAlpha (state : MachineState) (op : Alpha) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) thread₀ .thread ⟨⟨"alpha"⟩⟩

/-- Step one `Beta` operation. Same function, different family. -/
def stepBeta (state : MachineState) (op : Beta) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) engine₀ .dmaEngine ⟨⟨"beta"⟩⟩

/-! ## 1-5: the seam carries a new family end to end -/

/-- A load runs, records one event, and violates nothing. -/
theorem load_runs :
    ∃ s, (stepAlpha state₀ .load).state? = some s ∧ s.events.length = 1 ∧
      s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

/-- A store runs and violates nothing. -/
theorem store_runs :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧ s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_⟩; decide

/-- An atomic read-modify-write runs, and its event records both a read and a
write. -/
theorem atomicAdd_is_a_read_modify_write :
    ∃ s e, (stepAlpha state₀ .atomicAdd).state? = some s ∧ s.events = [e] ∧
      e.event.kind = .readModifyWrite ∧ e.event.ordering.atomicity = .atomic := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ## 4: obligations move through the same step -/

/-- Reserving creates the release obligation. -/
theorem reserve_creates_obligation :
    ∃ s, (stepAlpha state₀ .reserve).state? = some s ∧
      s.obligations.lookup releaseObligationId = some releaseObligation := by
  refine ⟨_, rfl, ?_⟩; decide

/-- Releasing after reserving discharges it, leaving nothing outstanding. -/
theorem reserve_then_release_discharges :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∃ t, (stepAlpha s .release).state? = some t ∧
        t.obligations.lookup releaseObligationId = Option.none := by
  intro s hs
  cases hs
  refine ⟨_, rfl, ?_⟩
  decide

/-! ## 6: invalid provenance, ranges, permissions, and ledger effects are rejected -/

/-- A store declaring read-only permission is not admitted: the profile refuses
the declaration before anything is attempted. -/
theorem badPermission_is_rejected :
    (stepAlpha state₀ .badPermission).rejection? = some .substepsNotWellFormed := by decide

/--
A range past the end of its allocation is caught at the declaration.

4096 bytes fit a 64-bit address space, so this is not the space check. It is
`rangeInProvenance`: the provenance declares a 64-byte root extent, and the range
escapes it. That condition used to be stated over an `Option` that was `none` for
a path-free provenance, which made it vacuous for exactly this shape — a
sixteen-exabyte access was well formed. This fixture is what keeps it closed.
-/
theorem badRange_is_rejected :
    (stepAlpha state₀ .badRange).rejection? = some .substepsNotWellFormed := by decide

/-- An access presenting a stale epoch is refused by the *state*, not by the
declaration: it is perfectly well formed, and the allocation it names has moved
on. The violation is recorded and nothing commits. -/
theorem staleEpoch_is_denied :
    ∃ s, (stepAlpha state₀ .staleEpoch).state? = some s ∧ ¬ s.violations.IsEmpty ∧
      s.events = [] := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

/-- A ledger effect that would destroy a duty without discharging it is not
admitted. This is what makes `LedgerDelta.WellFormed` a mechanism: it is a
premise of admission, not a theorem with no consumer. -/
theorem badLedger_is_rejected :
    (stepAlpha state₀ .badLedger).rejection? = some .accessNotAdmitted := by decide

/-! ## Obligations cannot be fabricated, dropped, or duplicated

`docs/OBLIGATIONS.md` §2 forbids all three, and `docs/FOUNDATION.md` law 7 states
the same rule as no obligation disappearance. Each of these was *performed* by an
earlier version of this transition: `LedgerDelta.WellFormed` checked only shape,
so a delta consuming an identity that was never live passed admission and the fold
applied it. -/

/-- Discharging a duty that is not live is refused. The earlier fold silently
no-opped, leaving no violation and no record. -/
theorem discharging_a_ghost_is_denied :
    ∀ s, (stepAlpha state₀ .dischargeGhost).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Joining duties that were never live is refused. The earlier fold erased two
nothings and installed a duty from nowhere. -/
theorem joining_ghosts_is_denied :
    ∀ s, (stepAlpha state₀ .joinGhosts).state? = some s →
      s.obligations.lookup fabricatedObligationId = Option.none ∧
        s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Splitting a duty that was never live is refused. -/
theorem splitting_a_ghost_is_denied :
    ∀ s, (stepAlpha state₀ .splitGhost).state? = some s →
      s.obligations.lookup fabricatedObligationId = Option.none ∧
        s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Creating a duty whose identity is already live is refused, so a second
`create` cannot silently overwrite the first. -/
theorem creating_a_live_identity_is_denied :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .reserve).state? = some t →
        t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs; cases ht
  decide

/-! ## Authority is typed, and claimed authority must match the live duty

`ProtocolAuthority` is indexed by its protocol, so a `ProtocolAuthority
otherProtocol` cannot be passed where a `ProtocolAuthority bufferProtocol` is
expected — that half is the elaborator's, and there is no fixture for it because
the mistake does not typecheck. What a fixture *can* show is the state-level
half: a delta may present well-typed authority under a protocol that does not
govern the obligation it names, and `LedgerDelta.Applicable` refuses it.

An earlier version compared protocol identities only, which is comparing strings
any caller could write down, and carried no authority at all. -/

theorem wrong_protocol_authority_is_refused :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .dischargeWithWrongAuthority).state? = some t →
        t.obligations.lookup releaseObligationId = some releaseObligation ∧
          t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The same discharge with the governing protocol's authority succeeds, so the
refusal above is about the protocol and not about the discharge. -/
theorem right_protocol_authority_succeeds :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .release).state? = some t →
        t.obligations.lookup releaseObligationId = Option.none ∧
          t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-! ## Authority evidence extends the seam without redesigning it

Each pair is the same operation against two states differing only in whether the
grant is held. The refusal and the success both come out of `step`, through
providers this file defines. -/

/-- Without a loan, the borrowed write is refused and nothing commits. -/
theorem write_through_loan_is_refused_without_the_loan :
    ∀ s, (stepAlpha state₀ .writeThroughLoan).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- With the loan held, the same write commits. -/
theorem write_through_loan_succeeds_with_the_loan :
    ∀ s, (stepAlpha stateWithAuthority .writeThroughLoan).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Without a live frame, the stack write is refused. -/
theorem stack_write_is_refused_without_a_frame :
    ∀ s, (stepAlpha state₀ .writeStackSlot).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- With the frame live, the same write commits. -/
theorem stack_write_succeeds_with_a_frame :
    ∀ s, (stepAlpha stateWithAuthority .writeStackSlot).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
The two kinds do not substitute for one another.

A grant of kind `loan` over the stack reservation does not satisfy the frame
provider, so the two providers are genuinely distinct authorities over one table
rather than one authority wearing two names.
-/
theorem a_loan_is_not_a_frame :
    ¬ (({ state₀.memory with
          grants := state₀.memory.grants.insert liveFrame
            { kind := .loan, holder := thread₀, provenance := frameProv
              range := ⟨0, 64⟩, rights := .readWrite } } : MemoryState).GrantedOfKind
        .frame thread₀ frameProv ⟨0, 8⟩ .write) := by decide

/-- Authority is not ambient: a grant held by the device engine does not
authorize the program thread. -/
theorem authority_is_not_ambient :
    ¬ (({ state₀.memory with
          grants := state₀.memory.grants.insert bufferLoan
            { kind := .loan, holder := engine₀, provenance := borrowedProv
              range := ⟨0, 64⟩, rights := .readWrite } } : MemoryState).GrantedOfKind
        .loan thread₀ borrowedProv ⟨0, 8⟩ .write) := by decide

/-! ## One effect cannot create the same identity twice

`LedgerDelta.Applicable` closes duplication per delta. That is not enough on its
own: an effect is a *sequence*, and checking every delta against the ledger as it
stood before the effect began lets two creates of one initially-fresh identity
both pass, after which the fold inserts one over the other and a duty is lost.
`docs/OBLIGATIONS.md` §2 forbids exactly that.

The two obligations below share an identity and differ in kind, so if the second
overwrote the first the resulting ledger would be observably wrong rather than
merely suspicious. -/

theorem both_creates_are_individually_applicable :
    LedgerDelta.Applicable ((FiniteMap.empty : FiniteMap ObligationId Obligation).domain)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.protocol)
      (.create bufferProtocol bufferAuthority collidingFirst) ∧
    LedgerDelta.Applicable ((FiniteMap.empty : FiniteMap ObligationId Obligation).domain)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.protocol)
      (.create bufferProtocol bufferAuthority collidingSecond) := by decide

/-- Together in one effect they are not applicable, because the second is checked
against the ledger the first left. -/
theorem the_pair_is_not_applicable :
    ¬ LedgerEffectApplicable (FiniteMap.empty : FiniteMap ObligationId Obligation)
      [ .create bufferProtocol bufferAuthority collidingFirst
      , .create bufferProtocol bufferAuthority collidingSecond ] := by decide

/-- The transition refuses the operation, leaves the obligations untouched, and
records the violation. -/
theorem create_twice_is_refused :
    ∀ s, (stepAlpha state₀ .createTwice).state? = some s →
      s.obligations.lookup collidingObligationId = Option.none ∧
        s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-! ## A denied access stops the operation

An earlier `runAccesses` folded over every access unconditionally, so an operation
whose first substep was denied still committed its second. That is a
continue-after-denial policy no operation declared. -/

theorem denial_stops_the_operation :
    ∀ s, (stepAlpha state₀ .deniedThenStore).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## A reported fault cannot be discarded

An out-of-range fault index used to mean "no fault at all": `visibleEffects?` took
the whole list, the substep lookup missed, and every access committed to
completion while `step` returned `.ran`. A fault turning into a success is the
law-8 failure running in the most dangerous direction.

There is no fixture for it any more, because `FaultPlan.before` carries a
`Fin sequence.substeps.length` and the bad case is **unrepresentable**. That is
the stronger repair: a negative fixture proves a check runs, while a type that
cannot express the mistake needs no check. The `if h : _ < _` guards in the
theorems above are how a caller obtains the `Fin`, and they are discharged
statically for a known sequence. -/

/-- The store sequence has exactly one substep, so index zero is the only fault
position that exists. -/
theorem store_has_one_substep :
    ∀ seq, (HasOperationFacets.facets Alpha.store).memoryEffects = some seq →
      seq.substeps.length = 1 := by
  intro seq h
  cases h
  rfl

/-! ## 7: alias conflicts across distinct allocations -/

/--
**The stepper denies it**, not merely a lemma about `Conflicts`.

A thread stores to the buffer; a device engine then stores to the *view*, a
different allocation naming the same bytes. The second access is refused, nothing
is committed for it, and a violation is recorded.

`Provenance.SameStorage` would have called these unrelated — the allocation
identities differ, which is exactly what distinct allocations mean — so the
conflict is found only because aliasing is recorded in the machine state and the
transition consults it.
-/
theorem aliased_cross_context_store_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The same two accesses, one context apart, are *not* denied: program order
sequences a context against itself, and refusing that would refuse ordinary
sequential code. -/
theorem same_context_stores_are_not_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepAlpha s .storeThroughView).state? = some t →
        t.events.length = 2 ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The same two stores are *not* related by `SameStorage`, so the conflict is
found only because the state records the alias. -/
theorem aliased_stores_are_not_sameStorage :
    ¬ bufferProv.SameStorage viewProv := by
  refine Provenance.not_sameStorage_of_root_ne ?_
  decide

/-! ## 8: partial effects survive a compound fault -/

/-- `divide` reads and then faults from a step that touches no memory. The read
survives, which is what `docs/MEMORY_MODEL.md` §1 requires a profile to be able to
state and what a sequence of accesses alone could not express. -/
theorem divide_preserves_its_read :
    ∀ seq, (HasOperationFacets.facets Alpha.divide).memoryEffects = some seq →
      seq.visibleEffects? 1 =
        some [acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false] := by
  intro seq h
  cases h
  rfl

/-! ## A partial read-modify-write retains its completed read

An `xadd` that observed its operand and then faulted before storing must record
the read it performed. One shared committed count made that unstateable: the
event had to claim it read as much as it wrote, so a faulted RMW with nothing
written had to claim it read nothing, while `readValuePresent` still demanded a
value. Reads and writes now count separately. -/

theorem faulted_rmw_keeps_its_read :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 8
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.kind = .readModifyWrite ∧
        e.event.readCommitted = 8 ∧ e.event.valueRead.isSome := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide, by decide⟩

/-- Truncated to three bytes, the read is three bytes and still present. The
count is the committed prefix, not the width the access named. -/
theorem partially_faulted_rmw_records_its_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 3
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 3 ∧ e.event.writeCommitted = 3 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-! ## 9: a second family coexists -/

/-- The device family steps through the same relation, with no shared type. -/
theorem dma_runs :
    ∃ s, (stepBeta state₀ .dmaWrite).state? = some s ∧ s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_⟩; decide

/-- An operation that declares no memory effects is rejected, not treated as
having none. This is `docs/FOUNDATION.md` law 8 at the seam. -/
theorem undeclared_is_rejected :
    (stepBeta state₀ .undeclared).rejection? = some (.facetsNotClosed .memoryEffects) := by
  decide

/-- Both families reach the same transition relation, and neither type appears in
the other's definition. -/
theorem two_families_one_relation :
    (stepAlpha state₀ .load).Ran ∧ (stepBeta state₀ .dmaWrite).Ran := by decide

/-! ## The transition invariant

Every step extends the violation ledger. This is the property
`docs/MEMORY_MODEL.md` §8 names, and it is a fact about transitions rather than
about the ledger type, which cannot enforce it. -/

theorem every_alpha_step_extends_violations (op : Alpha) :
    ∀ s, (stepAlpha state₀ op).state? = some s →
      s.violations.Extends state₀.violations := by
  intro s hs
  cases op <;> cases hs <;>
    first
      | exact AuditViolationLedger.Extends.refl _
      | exact AuditViolationLedger.extends_append _ _

/-! ## 8 again, through the transition rather than a lemma

The `divide_preserves_its_read` theorem above is a fact about the *facet*: it says
what `visibleEffects?` answers. That is not the same as saying the transition
honours it, and an earlier version of this fixture proved only the former while
the stepper committed every access unconditionally.

These drive the fault path through `step` itself. -/

/-- A compound operation that faults at its second substep. The read before it
committed, and the state shows one event. -/
theorem divide_fault_preserves_the_read :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then
            .before ⟨1, h⟩ divideError 0
          else .none)).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
Faulting at the *first* substep commits no bytes.

The event is still recorded — a faulted access is an event, and pretending
otherwise would lose it from the trace — but it committed nothing. An earlier
version of this theorem said "commits nothing" in its docstring and checked only
`events.length = 1`, which is compatible with an event that committed the whole
range.
-/
theorem divide_fault_at_zero_commits_no_bytes :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 0 ∧ e.event.writeCommitted = 0 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-- A faulting access commits the prefix it declares, and the event records it.
`docs/MEMORY_MODEL.md` §1 forbids assuming a faulted access did nothing. -/
theorem faulted_store_commits_its_declared_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 3
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.writeCommitted = 3 ∧ e.event.status = .faulted .pageFault 3 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-! ### The fault itself is recoverable from the step result

A compute substep produces no memory event, so before the state carried a fault
record a `divideError` left no trace at all: the theorems above could see that the
read survived, but nothing distinguished a faulting execution from a clean one.
That is the fault being discarded, which is what `Substep.compute` exists to
prevent. -/

/-- The divide error is present in the resulting state, with its class, its
context, and the substep it came from. -/
theorem divide_fault_is_recoverable :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then
            .before ⟨1, h⟩ divideError 0
          else .none)).state? = some s →
      s.faults = [{ fault := divideError, context := thread₀, cause := ⟨⟨"alpha"⟩⟩
                    substep := 1 }] := by
  intro s hs
  cases hs
  decide

/-- A clean run of the same operation records no fault, so the two are
distinguishable. -/
theorem clean_divide_records_no_fault :
    ∀ s, (stepAlpha state₀ .divide).state? = some s → s.faults = [] := by
  intro s hs
  cases hs
  decide

/-- A fault on an *access* substep is recorded too, so the record does not depend
on which kind of substep failed. -/
theorem access_fault_is_recorded :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 3
          else .none)).state? = some s →
      s.faults.length = 1 ∧ s.events.length = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- An operation whose visibility rule belongs to a profile cannot be stepped by
the generic relation. Refusing is the honest answer; guessing which effects
survive would be the permissive fallback law 8 forbids. -/
theorem profile_visibility_rule_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.splitStore) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0
        else .none)).rejection? = some .visibilityRuleUnknown := by decide

end Grass.Tests.FakeIsa
