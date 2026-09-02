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

open Grass.Core Grass.Memory Grass.Obligation Grass.Op

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

/-- Provenance of the buffer. -/
def bufferProv : Provenance :=
  { space := .cpuVirtual, root := bufferAlloc, epoch := epoch₀, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- Provenance of the aliasing view. Different allocation identity, same bytes. -/
def viewProv : Provenance := { bufferProv with root := viewAlloc, source := .mappedFile }

/-- Provenance of the read-only allocation. -/
def constProv : Provenance := { bufferProv with root := constAlloc, source := .imageMapping }

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
deriving DecidableEq, Repr

/-- The duty a fabricating delta would conjure. -/
def fabricatedObligation : Obligation :=
  { id := fabricatedObligationId, kind := .releaseAllocation
    protocol := ⟨⟨"fake.buffer"⟩⟩, owner := thread₀ }

/-- The release obligation `reserve` creates. -/
def releaseObligation : Obligation :=
  { id := releaseObligationId, kind := .releaseAllocation
    protocol := ⟨⟨"fake.buffer"⟩⟩, owner := thread₀ }

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
            false true [.create releaseObligation]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .release =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge releaseObligationId]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .divide =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false)
                  , .compute [⟨⟨"divideError"⟩⟩] ]
              onFault := .priorEffectsVisible }
          faults := some [⟨⟨"divideError"⟩⟩], restartability := some .notRestartable
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
            false true [.split releaseObligationId []]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .staleEpoch =>
        { memoryEffects := some (.single (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge ghostObligationId]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .joinGhosts =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.join [ghostObligationId, ghostObligationId₂] fabricatedObligation]))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .splitGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split ghostObligationId [fabricatedObligation]]))
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
    faultClasses := ⟨[.pageFault, .deviceFault, ⟨⟨"divideError"⟩⟩]⟩
    allocationSources := ⟨[.virtualAlloc, .mappedFile, .imageMapping]⟩
    provenanceStepKinds := ⟨[]⟩
    auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[.releaseAllocation]⟩ }

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

/-- Every operation must declare its memory effects and its faults. -/
def policy : StepPolicy :=
  { profile := profile, requiredFacets := [.memoryEffects, .faults]
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

/-- The starting machine state. -/
def state₀ : MachineState := .initial memory₀

/-- Step one `Alpha` operation. -/
def stepAlpha (state : MachineState) (op : Alpha) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) .thread ⟨⟨"alpha"⟩⟩

/-- Step one `Beta` operation. Same function, different family. -/
def stepBeta (state : MachineState) (op : Beta) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) .dmaEngine ⟨⟨"beta"⟩⟩

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
      e.kind = .readModifyWrite ∧ e.ordering.atomicity = .atomic := by
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

/-! ## A reported fault is never discarded

An out-of-range fault index used to mean "no fault at all": `visibleEffects?` took
the whole list, the substep lookup missed, and every access committed to
completion while `step` returned `.ran`. A fault turning into a success is the
law-8 failure running in the most dangerous direction. -/

theorem out_of_range_fault_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) .thread ⟨⟨"alpha"⟩⟩
      (some ⟨99, .pageFault, 0⟩)).rejection? = some .faultPointOutOfRange := by decide

theorem out_of_range_fault_on_compound_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) .thread ⟨⟨"alpha"⟩⟩
      (some ⟨99, .pageFault, 0⟩)).rejection? = some .faultPointOutOfRange := by decide

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
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) .thread
        ⟨⟨"alpha"⟩⟩ (some ⟨1, ⟨⟨"divideError"⟩⟩, 0⟩)).state? = some s →
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
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) .thread
        ⟨⟨"alpha"⟩⟩ (some ⟨0, .pageFault, 0⟩)).state? = some s →
      ∃ e, s.events = [e] ∧ e.readCommitted = 0 ∧ e.writeCommitted = 0 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-- A faulting access commits the prefix it declares, and the event records it.
`docs/MEMORY_MODEL.md` §1 forbids assuming a faulted access did nothing. -/
theorem faulted_store_commits_its_declared_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) .thread
        ⟨⟨"alpha"⟩⟩ (some ⟨0, .pageFault, 3⟩)).state? = some s →
      ∃ e, s.events = [e] ∧ e.writeCommitted = 3 ∧ e.status = .faulted .pageFault 3 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-- An operation whose visibility rule belongs to a profile cannot be stepped by
the generic relation. Refusing is the honest answer; guessing which effects
survive would be the permissive fallback law 8 forbids. -/
theorem profile_visibility_rule_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.splitStore) .thread
      ⟨⟨"alpha"⟩⟩ (some ⟨1, .pageFault, 0⟩)).rejection? =
        some .visibilityRuleUnknown := by decide

end Grass.Tests.FakeIsa
