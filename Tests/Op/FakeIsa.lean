import Grass.Memory.Loan
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

/-- A third allocation, aliased to `viewAlloc` rather than to `bufferAlloc`, so
reaching it from the buffer takes two declared hops. -/
def chainedAlloc : AllocId := allocs₂.fresh.2.fresh.2.fresh.2.fresh.1

/-- Provenance of the far end of the alias chain. -/
def chainedProv : Provenance := { bufferProv with root := chainedAlloc, source := .mappedFile }

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
  /-- The same split store, declared transactional. -/
  | atomicSplitStore
  /-- A device write that declares the program thread as its context, to defeat the
  race check. -/
  | impersonatingDmaWrite
  /-- A compute substep declaring a fault class the vocabulary never admitted. -/
  | computeWithPhantomFault
  /-- An operation declaring that it raises no faults, over an access that admits a
  page fault. Its two facets contradict each other. -/
  | faultsUnderdeclared
  /-- An operation declaring a fault class the vocabulary never admitted, with no
  compute substep to carry it — so `computeFaultNotRecognized` does not see it. -/
  | operationWithPhantomFault
  /-- An atomic store requesting an ordering mode this profile never registered. -/
  | unregisteredOrder
  /-- The same store requesting the mode the profile *does* register. -/
  | registeredOrder
  /-- A store claiming an ordering scope this profile never registered. -/
  | unregisteredScope
  /-- A sequence claiming a fault-visibility rule this profile never registered. -/
  | unregisteredVisibilityRule
  /-- A sequence claiming cross-substep atomicity under a target theorem this
  profile never registered. -/
  | unregisteredAtomicityClaim
  /-- A load reading uninitialized bytes under a rule this profile never
  registered. -/
  | unregisteredInitRule
  /-- The same load, under the rule the profile does register. -/
  | registeredInitRule
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
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .release =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority releaseObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .divide =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false)
                  , .compute [divideError] ]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault, divideError], restartability := some .notRestartable
          ordering := some .plain }
    | .storeThroughView =>
        { memoryEffects := some (.single (acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badPermission =>
        { memoryEffects := some (.single (acc constProv ⟨0, 8⟩ 0x1000 .write .readOnly
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badRange =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 4096⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badLedger =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority releaseObligationId []]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .staleEpoch =>
        { memoryEffects := some (.single (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority ghostObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .joinGhosts =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.join bufferProtocol bufferAuthority [ghostObligationId, ghostObligationId₂] fabricatedObligation]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .splitGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority ghostObligationId [fabricatedObligation]]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .writeThroughLoan =>
        { memoryEffects := some (.single (acc borrowedProv ⟨0, 8⟩ 0x3000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .writeStackSlot =>
        { memoryEffects := some (.single (acc frameProv ⟨0, 8⟩ 0x2000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .createTwice =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [ .create bufferProtocol bufferAuthority collidingFirst
            , .create bufferProtocol bufferAuthority collidingSecond ]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeWithWrongAuthority =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge otherProtocol otherAuthority releaseObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .deniedThenStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨8, 8⟩ 0x1008 .write .readWrite false true) ]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .splitStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .profileSpecific ⟨"fake.splitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .impersonatingDmaWrite =>
        { memoryEffects := some (.single (acc viewProv ⟨0, 8⟩ 0x2000 .write .readWrite
            false true [] false thread₀))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .faultsUnderdeclared =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .operationWithPhantomFault =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault, ⟨⟨"fake.neverDeclaredFault"⟩⟩]
          restartability := some .notRestartable, ordering := some .plain }
    | .unregisteredVisibilityRule =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .profileSpecific ⟨"fake.neverRegistered"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredAtomicityClaim =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .transactional ⟨"fake.neverRegistered"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredInitRule =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false with
              initialization := .permitsUninitialized ⟨"fake.neverRegistered"⟩ })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .registeredInitRule =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false with
              initialization := .permitsUninitialized ⟨"fake.zeroedByLoader"⟩ })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredOrder =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true [] true with
              ordering := { atomicity := .atomic
                            order := .profileSpecific ⟨"fake.neverRegistered"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .registeredOrder =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true [] true with
              ordering := { atomicity := .atomic
                            order := .profileSpecific ⟨"fake.deviceRelease"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredScope =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true with
              ordering := { scope := .profileSpecific ⟨"fake.neverRegistered"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .computeWithPhantomFault =>
        { memoryEffects := some
            { substeps := [ .compute [⟨⟨"fake.neverDeclaredFault"⟩⟩] ]
              onFault := .priorEffectsVisible }
          faults := some [⟨⟨"fake.neverDeclaredFault"⟩⟩]
          restartability := some .restartable, ordering := some .plain }
    | .atomicSplitStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .transactional ⟨"fake.atomicSplitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }

/-! ## Family two: an independently defined device family

Written as if by a different author. It shares no type with `Alpha`, does not
import it, and is packaged the same way. -/

/-- The second family's operation type. -/
inductive Beta where
  /-- A device engine writes the buffer. -/
  | dmaWrite
  /-- A device engine writes the far end of an alias chain: the same storage as
  the buffer, two declared hops away. -/
  | dmaWriteChained
  /-- A device engine discharges a duty the program thread holds. -/
  | dmaDischargesTheThreadsDuty
  /-- An operation that declares no memory effects at all. -/
  | undeclared
deriving DecidableEq, Repr

instance : HasOperationFacets Beta where
  facets
    | .dmaWrite =>
        { memoryEffects := some (.single
            { acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dmaWriteChained =>
        { memoryEffects := some (.single
            { acc chainedProv ⟨0, 8⟩ 0x4000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dmaDischargesTheThreadsDuty =>
        { memoryEffects := some (.single
            { acc borrowedProv ⟨0, 8⟩ 0x5000 .write .readWrite false true
                [.discharge bufferProtocol bufferAuthority releaseObligationId]
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .undeclared => {}

/-! ## The profile and the starting state -/

/--
A violation class this profile names for itself.

`AuthorityProvider.violationClass` is open nominal, so an authority a profile
adds can report a failure the generic transition has no name for: "there was no
live frame" is not "the loan state did not authorize this", and collapsing them
into `authorityUnavailable` would lose which authority was missing. Declaring it
below is what makes it usable — see `custom_violation_class_is_usable` and
`undeclared_provider_class_cannot_form_a_policy`.
-/
def frameAuthorityUnavailable : AuditViolationClass := ⟨⟨"fake.frameAuthorityUnavailable"⟩⟩

/-- The profile's address spaces, obligation kinds, and fault classes. -/
def vocabulary : AdmittedVocabulary :=
  { addressSpaces := .cpuOnly
    faultClasses := ⟨[.pageFault, .deviceFault, divideError]⟩
    allocationSources := ⟨[.virtualAlloc, .mappedFile, .imageMapping, .stack]⟩
    provenanceStepKinds := ⟨[]⟩
    auditViolationClasses :=
      ⟨AuditViolationClass.emittedByTransition ++ [frameAuthorityUnavailable]⟩
    obligationKinds := ⟨[.releaseAllocation, .closeHandle]⟩
    orderingModes := ⟨[⟨"fake.deviceRelease"⟩]⟩
    orderingScopes := ⟨[⟨"fake.queue"⟩]⟩
    initializationJustifications := ⟨[⟨"fake.zeroedByLoader"⟩]⟩
    atomicityJustifications := ⟨[⟨"fake.atomicSplitStore"⟩]⟩
    faultVisibilityRules := ⟨[⟨"fake.splitStore"⟩]⟩ }

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
  violationClass := frameAuthorityUnavailable
  refuses state d :=
    decide (d.provenance.root = stackAlloc) &&
    !decide (state.memory.GrantedOfKind .frame d.context d.provenance d.range d.intent)

/--
A provider whose violation class this profile never declared.

The adversary for `undeclared_provider_class_cannot_form_a_policy`. It is
well-typed and behaves like any other provider; the only thing wrong with it is
that its class is not in the vocabulary.
-/
def rogueProvider : AuthorityProvider where
  id := ⟨"fake.rogue"⟩
  violationClass := ⟨⟨"fake.undeclaredClass"⟩⟩
  refuses _ _ := true

/-! ## What this profile stores and what it would observe of the indeterminate

`Oracle.ofMemory` takes both as parameters rather than inventing either. -/

/-- What a store writes here: a pattern distinct from the zeros every allocation
starts with, so observing it after a store is evidence that the load read the
store's bytes rather than the initial contents. -/
def storedBytes : MachineState → AccessDescriptor → ByteSeq :=
  fun _ d => List.replicate d.range.size 0xAB

/-- What an indeterminate read would observe. No theorem below depends on its
value, but not for the reason an earlier version of this comment gave: every
allocation here starts fully initialized, so `byteAt?` never returns `none` and
the oracle never reaches this function at all. Nothing about denial ordering is
involved, and review corrected the claim. It is supplied because
`Oracle.ofMemory` requires it rather than defaulting it. -/
def indeterminateByte : MachineState → (d : AccessDescriptor) → Nat → Byte :=
  fun _ _ _ => 0xEE

/-- Every operation must declare its memory effects and its faults. -/
def policy : StepPolicy :=
  { profile := profile
    requiredFacets := [.memoryEffects, .faults, .restartability]
    oracle := .ofMemory storedBytes indeterminateByte
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

/-- Sixty-four initialized zero bytes: the starting contents of every allocation
in this fixture. Written through `ByteStore.write` with `initializes := true`
rather than assembled by hand, so the fixture's notion of initialized is the same
one `RangeInitialized` reads. -/
def zeroed64 : ByteStore := ByteStore.empty.write 0 (List.replicate 64 0) true

/-- The buffer, its aliasing view, and a read-only allocation. The alias is
declared here, in the state, because whether two allocations name the same bytes
is a fact about the machine and not about provenance. -/
def memory₀ : MemoryState :=
  (((MemoryState.empty.allocate bufferAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true
        bytes := zeroed64, base := some 0x1000 }).allocate viewAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true
        bytes := zeroed64, base := some 0x1000 }).allocate constAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readOnly, live := true
        bytes := zeroed64, base := some 0x2000 }).alias bufferAlloc viewAlloc

/-- The stack reservation the frame provider guards.

`viewAlloc` and `chainedAlloc` share `bufferAlloc`'s base, which is the point of
an alias: distinct allocation identities over the same storage. Placement does not
decide aliasing — `MemoryState.aliases` does, and `docs/MEMORY_MODEL.md` §2 makes
provenance rather than address the authority — so the two facts are declared
separately and agreeing here is the fixture being realistic rather than a rule. -/
def memory₁ : MemoryState :=
  ((((memory₀.allocate stackAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := zeroed64
        base := some 0x3000 }).allocate borrowedAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := zeroed64
        base := some 0x4000 }).allocate chainedAlloc
      { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := zeroed64
        base := some 0x1000 }).alias viewAlloc
    chainedAlloc)

/-- The starting machine state: allocations exist, but no authority is held. -/
def state₀ : MachineState := .initial memory₁

private def grants₀ : FreshSupply GrantTag := .initial

/-- A loan over the buffer, held by the program thread. -/
def bufferLoan : GrantId := grants₀.fresh.1

/-- A live call frame over the stack reservation. -/
def liveFrame : GrantId := grants₀.fresh.2.fresh.1

/-- A third identity, so a fixture can install two grants over one range. -/
def secondBufferLoan : GrantId := grants₀.fresh.2.fresh.2.fresh.1

/-- The same state with both grants live. -/
def stateWithAuthority : MachineState :=
  { state₀ with
    memory :=
      (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).issue? liveFrame
        { kind := .frame, holder := thread₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory }

/-- Both issues succeeded, so `getD` never fell back and the theorems below are
about a state that holds both grants. -/
theorem the_authority_issues_succeed :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, provenance := borrowedProv
        range := ⟨0, 64⟩, rights := .readWrite }).isSome ∧
    (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).issue? liveFrame
        { kind := .frame, holder := thread₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).isSome := by
  exact ⟨by decide, by decide⟩

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

/-! ## Reads observe writes

The M1 fixture ran against `Oracle.zeroed`, which reported the counts an intent
implied and supplied zero bytes of content. That was enough to exercise the
transition and not enough to say memory held anything. With `Oracle.ofMemory`
over `Grass/Memory/ByteStore.lean` the trace carries values that came from
somewhere. -/

/--
**A load observes the prior store.**

The store writes `0xAB` over bytes that began as `0x00`, and the load that
follows observes `0xAB`. Both facts are read off the recorded trace rather than
off memory, so this says the event model reports what the store committed and not
merely that the store changed a field.
-/
theorem a_load_observes_the_prior_store :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      ∃ t, (stepAlpha s .load).state? = some t ∧
        t.events.getLast?.bind (·.event.valueRead) = some (List.replicate 8 0xAB) :=
  ⟨_, rfl, _, rfl, by decide⟩

/-- Before the store, a load observes the zeros the allocation started with. The
control for the theorem above: without it, `0xAB` could have been what a load
always observes. -/
theorem a_load_before_the_store_observes_the_initial_bytes :
    ∃ s, (stepAlpha state₀ .load).state? = some s ∧
      s.events.getLast?.bind (·.event.valueRead) = some (List.replicate 8 0x00) :=
  ⟨_, rfl, by decide⟩

/-- A store leaves bytes outside its range alone. `MemoryState.write` goes
through `ByteStore.write`, and `ByteStore.cellAt?_write_of_not_covers` is the
framing law; this is that law observed through a real transition. -/
theorem a_store_leaves_neighbouring_bytes_alone :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      s.memory.byteAt? bufferAlloc 8 = some 0x00 ∧
      s.memory.byteAt? bufferAlloc 0 = some 0xAB :=
  ⟨_, rfl, by decide, by decide⟩

/-- A store to the buffer leaves the read-only allocation untouched, which is
`MemoryState.write_preserves_other_allocation` observed through a transition. -/
theorem a_store_leaves_other_allocations_alone :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      s.memory.byteAt? constAlloc 0 = some 0x00 :=
  ⟨_, rfl, by decide⟩

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

/-! ## An authority cannot smuggle in a violation class the profile never declared

`AuthorityProvider.violationClass` is open nominal so that a profile can name its
own failures, and `refusalOf` records it directly. That is a hole unless the
class is required to be declared: a profile could add a provider with a fresh
class, and the transition would record a class outside the admitted vocabulary
while `docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.11 claimed every emitted class was
declared. `docs/FOUNDATION.md` law 8 forbids exactly this shape of escape — the
open extension point is not permission to bypass the registry.

`StepPolicy.violationClassesDeclared` quantifies over
`AuthorityProvider.emittedClasses authorities`, which grows with the provider
list. The two theorems below are the two halves of the claim: a custom class that
is declared works, and one that is not cannot form a policy at all. -/

/--
A declared profile-specific class is usable.

`frameProvider` reports `frameAuthorityUnavailable`, which is not one of the
classes the generic transition emits. The vocabulary declares it, so `policy`
exists — this file would not compile otherwise. That the refusal actually
*records* the custom class rather than the generic `authorityUnavailable` is
`refused_stack_write_records_the_custom_class`, below.
-/
theorem custom_violation_class_is_usable :
    frameProvider.violationClass ∉ AuditViolationClass.emittedByTransition ∧
    frameProvider.violationClass ∈
      AuthorityProvider.emittedClasses policy.authorities ∧
    vocabulary.auditViolationClasses.Recognizes frameProvider.violationClass := by
  refine ⟨by decide, ?_, by decide⟩
  exact AuthorityProvider.mem_emittedClasses_of_provider (by simp [policy])

/--
**An undeclared provider class cannot form a `StepPolicy`.**

The `violationClassesDeclared` field is exactly this proposition, so a policy
whose providers include `rogueProvider` is unconstructible against this profile
— not merely ill-advised. Compare `custom_violation_class_is_usable`: the
difference between the two providers is declaration and nothing else.
-/
theorem undeclared_provider_class_cannot_form_a_policy :
    ¬ (∀ class_ ∈ AuthorityProvider.emittedClasses [loanProvider, rogueProvider],
        profile.vocabulary.auditViolationClasses.Recognizes class_) := by decide

/--
The refused stack write records the custom class.

Read off the ledger's public view, so this is the class an audit report would
show. Without it `custom_violation_class_is_usable` would only establish that the
class is *declarable*, not that anything ever emits it.
-/
theorem refused_stack_write_records_the_custom_class :
    ∀ s, (stepAlpha state₀ .writeStackSlot).state? = some s →
      s.violations.records?.map AuditViolation.class_ = [frameAuthorityUnavailable] := by
  intro s hs
  cases hs
  decide

/-- The rogue provider is rejected for its class alone. Its behaviour is
irrelevant — it never gets to run, because the policy that would consult it does
not exist. -/
theorem the_rogue_is_rejected_for_its_class_alone :
    ¬ vocabulary.auditViolationClasses.Recognizes rogueProvider.violationClass ∧
    (∀ class_ ∈ AuthorityProvider.emittedClasses [loanProvider],
      profile.vocabulary.auditViolationClasses.Recognizes class_) := by decide

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
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.owner) thread₀
      (.create bufferProtocol bufferAuthority collidingFirst) ∧
    LedgerDelta.Applicable ((FiniteMap.empty : FiniteMap ObligationId Obligation).domain)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.protocol)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.owner) thread₀
      (.create bufferProtocol bufferAuthority collidingSecond) := by decide

/-- Together in one effect they are not applicable, because the second is checked
against the ledger the first left. -/
theorem the_pair_is_not_applicable :
    ¬ LedgerEffectApplicable (FiniteMap.empty : FiniteMap ObligationId Obligation) thread₀
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

/--
**A denial stops the operation on the faulting path too.**

`denial_stops_the_operation` covers the clean run. It did not cover the faulting
run, and the faulting run was broken: `runStep` performed the faulting substep's
access whether or not a survivor had been refused, so the denied first substep was
followed by a committed second one. Local adversarial review built exactly this
case and it went the other way.

Reported at substep 1, the surviving prefix is substep 0, which is denied for a
stale epoch. Nothing after it commits, and the store's bytes are untouched — the
last conjunct is the one that failed before, because counting events alone would
not have noticed a write that recorded no event.
-/
theorem denial_stops_the_operation_on_the_fault_path :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.deniedThenStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 8
          else .none)).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.memory.byteAt? bufferAlloc 8 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- And no fault is recorded, because the faulting substep was never reached.
`Op.runStep_records_no_fault_after_refusal` is the general form; recording one
here would be inventing a fault for a substep that did not run. -/
theorem a_denial_before_the_fault_records_no_fault :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.deniedThenStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 8
          else .none)).state? = some s →
      s.faults = [] := by
  intro s hs
  cases hs
  decide

/-! ## A duty is discharged by its holder

`docs/OBLIGATIONS.md` opens by making an obligation a duty of "its holder" and §1
lists the owner as part of its form. `Obligation.owner` was carried, printed, and
consulted by nothing: `LedgerDelta.Applicable` checked liveness and protocol and
never ownership, so any context could discharge any duty. Local adversarial review
stepped a device engine through a discharge of the program thread's release
obligation and the duty vanished with no violation. -/

/-- The thread reserves, creating a duty it owns. -/
theorem the_thread_owns_what_it_reserved :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      (s.obligations.lookup releaseObligationId).map Obligation.owner = some thread₀ := by
  intro s hs
  cases hs
  decide

/-- **Another context cannot discharge it.** The duty survives and the attempt is
recorded, rather than the duty vanishing silently. -/
theorem another_context_cannot_discharge_it :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepBeta s .dmaDischargesTheThreadsDuty).state? = some t →
        (t.obligations.lookup releaseObligationId).isSome ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The holder still can, so the check is about ownership and not about refusing
every discharge. -/
theorem the_holder_can_discharge_it :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .release).state? = some t →
        t.obligations.lookup releaseObligationId = Option.none ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-! ## An access cannot declare a context other than the one running it

`MemoryEvent.ofOutcome` takes the event's context identity from
`AccessDescriptor.context` and its kind from `step`'s argument, and nothing
compared them. `ConflictsWithHistory` discriminates on that identity, so
`docs/MEMORY_MODEL.md` §7.3's race rule was defeated by one field: a device write
naming the program thread aliased the thread's bytes and committed, and the event
it minted carried thread identity with engine kind, an incoherent pair §7.1
forbids. Two sources of truth for one fact. -/

/-- The honest device write is denied, which is the existing behaviour. -/
theorem the_honest_device_write_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs
  cases ht
  decide

/-- The impersonating one is refused before it runs, rather than committing. -/
theorem an_impersonating_access_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.impersonatingDmaWrite) engine₀
      .dmaEngine ⟨⟨"alpha"⟩⟩ = .rejected (.contextMismatch thread₀ engine₀) := rfl

/-- The same descriptor run by the context it names is admitted *and commits*, so
the check compares rather than refusing anything unusual.

Asserting only that a state came back would not have said that: `staleEpoch_is_denied`
shows a denied access also produces a state. Review caught me reintroducing exactly
the weakness I had repaired two theorems earlier. -/
theorem the_named_context_may_run_it :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.impersonatingDmaWrite)
      thread₀ .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
**One identity cannot be two kinds.**

`contextMismatch` closed the identity half: an access may not name a context other
than the one running it. The *kind* came from a separate `step` argument with
nothing relating it to anything, so the same `ContextId` could be stepped as a
thread once and a device engine the next time, and each event carried whatever
pair the caller supplied. `docs/MEMORY_MODEL.md` §7.1 requires identity and kind
together. `MachineState.contexts` records the pairing the first time a context is
seen, and disagreement is refused.
-/
theorem a_context_cannot_change_kind :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      Grass.Op.step policy s (SomeOperation.of Alpha.load) thread₀ .dmaEngine
        ⟨⟨"alpha"⟩⟩ = .rejected (.contextKindMismatch thread₀ .dmaEngine .thread) := by
  intro s hs
  cases hs
  rfl

/-- The same context under its own kind still runs, so the check is about
disagreement and not about refusing a second step. -/
theorem the_same_kind_still_runs :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepAlpha s .load).state? = some t →
        t.events.length = 2 ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- And a fresh identity may take any kind, because the state has not seen it. -/
theorem a_fresh_context_may_take_any_kind :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        (t.contexts.lookup engine₀) = some ContextKind.dmaEngine := by
  intro s hs t ht
  cases hs; cases ht
  decide

/-! ## A compute substep's fault classes are checked too

`MemoryProfile.Admits` closes this for an access, quantifying over
`admittedFaults`. A compute substep has no descriptor, so `sequence.accesses`
never contains it and `Admits` never saw it: the only thing checked about one was
that its fault list is non-empty. `faultClassNotDeclared` then validated a plan
against a list that was itself unvalidated, and `.compute` is the constructor the
`div` case exists for. -/

theorem a_compute_substep_with_an_unrecognized_fault_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.computeWithPhantomFault) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.computeFaultNotRecognized ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-! ## A justification the profile never registered is rejected

`INSTRUCTIONS.md` §4 wants a target theorem behind a cross-substep atomicity claim,
`MEMORY_MODEL.md` §4 wants a profile rule behind an uninitialized read, and §7.1
wants a profile behind a fault-visibility rule it owns. All three were names and
nothing held them: a sequence got all-or-nothing fault semantics, and an access
read uninitialized bytes, by declaring a string.

Three registries rather than one. A rule permitting an uninitialized read is not a
proof that a two-substep store is all-or-nothing, and one namespace would let
either name satisfy the other — two facts in one carrier is what this layer removed
from `AccessIntent.isDevice`. -/

/-- **An unregistered fault-visibility rule is refused.** -/
theorem an_unregistered_visibility_rule_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredVisibilityRule) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.onFaultRuleNotRegistered ⟨"fake.neverRegistered"⟩) := rfl

/-- **An unregistered atomicity claim is refused**, and it is checked against a
*different* registry: the name below is registered as a visibility rule and still
does not satisfy a `transactional` claim. -/
theorem an_unregistered_atomicity_claim_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredAtomicityClaim) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.onFaultRuleNotRegistered ⟨"fake.neverRegistered"⟩) := rfl

/-- The registries really are separate: `fake.splitStore` is a visibility rule and
`fake.atomicSplitStore` an atomicity claim, and neither appears in the other's
registry. Without this the two theorems above would be consistent with one shared
namespace. -/
theorem the_justification_registries_are_separate :
    ¬ vocabulary.atomicityJustifications.Recognizes ⟨"fake.splitStore"⟩ ∧
    ¬ vocabulary.faultVisibilityRules.Recognizes ⟨"fake.atomicSplitStore"⟩ ∧
    (stepAlpha state₀ .splitStore).state?.isSome ∧
    (stepAlpha state₀ .atomicSplitStore).state?.isSome := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **An uninitialized read under an unregistered rule is not admitted.** -/
theorem an_unregistered_initialization_rule_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredInitRule) thread₀
      .thread ⟨⟨"alpha"⟩⟩ = .rejected .accessNotAdmitted := rfl

/-- And the registered rule is admitted, so the refusal is about the registry
rather than about `permitsUninitialized` being refused outright. -/
theorem the_registered_initialization_rule_is_admitted :
    (stepAlpha state₀ .registeredInitRule).state?.isSome := by decide

/-! ## An ordering mode the profile never registered is rejected

`docs/MEMORY_MODEL.md` §7.1 fixes five portable modes and four portable scopes and
allows a profile its own, and says an unsupported mapping is rejected. Nothing
rejected one: `MemoryOrder.IsPortable` had no consumer, `AdmittedVocabulary` had no
ordering registry, and an access declaring `profileSpecific` with any name at all
stepped and minted an event carrying it. -/

/-- **An unregistered ordering mode is not admitted.** -/
theorem an_unregistered_order_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredOrder) thread₀
      .thread ⟨⟨"alpha"⟩⟩ = .rejected .accessNotAdmitted := rfl

/-- **The registered mode is admitted**, so the rejection above is about the
registry rather than about profile-specific modes being refused outright. Without
this the theorem above would be consistent with rejecting every non-portable
mode. -/
theorem the_registered_order_is_admitted :
    (stepAlpha state₀ .registeredOrder).state?.isSome := by decide

/-- **An unregistered scope is not admitted either.** A device fence claiming a
scope nobody defined is not a weaker fence; it is an undefined one. -/
theorem an_unregistered_scope_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredScope) thread₀
      .thread ⟨⟨"alpha"⟩⟩ = .rejected .accessNotAdmitted := rfl

/-- And a portable mode needs no registration at all, which is what
`admitsOrder_of_isPortable` says: every other operation in this fixture requests
`relaxed` or `acquireRelease` and neither appears in `orderingModes`. -/
theorem a_portable_order_needs_no_registration :
    ¬ vocabulary.orderingModes.Recognizes ⟨"acquireRelease"⟩ ∧
    (stepAlpha state₀ .atomicAdd).state?.isSome := by
  exact ⟨by decide, by decide⟩

/-! ## And so is the operation's own fault declaration

`OperationFacets.faults` was consumed by nothing. `OperationFacets.supplied` reads
only `isSome`, so an operation declaring `faults := some []` closed the facet and
then page-faulted through a substep that admitted one — the substep-level list was
checked, the operation-level list above it was checked against nothing. That is a
fact the model carries and nothing consults, which is the shape this layer removed
from `AllocationRecord.initialized` and `AccessIntent.isDevice`.

Eighteen of this fixture's own operations were inconsistent when the check went in,
which is how little a declaration nobody reads constrains. -/

/-- **An operation that declares no faults, over an access that admits one, is
refused.** Refused statically, before any fault plan is supplied, because the two
declarations contradict each other and law 8's answer to that is not to pick one. -/
theorem an_underdeclared_operation_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.faultsUnderdeclared) thread₀
      .thread ⟨⟨"alpha"⟩⟩ = .rejected (.operationFaultsIncomplete .pageFault) := rfl

/-- And it is refused with no fault plan at all, so this is a check on the
declaration rather than on what the machine did. -/
theorem an_underdeclared_operation_is_refused_without_a_fault :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.faultsUnderdeclared) thread₀
      .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun _ => .none)).Ran = False := by
  decide

/-- **An operation declaring a fault class the vocabulary never admitted is
refused**, with no compute substep involved — that was the only other place an
unrecognized class was caught, and this operation has none. -/
theorem an_operation_with_a_phantom_fault_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.operationWithPhantomFault) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.operationFaultNotRecognized ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-- An operation may declare *more* than its substeps can raise: `store` declaring
`[.pageFault]` over one access that admits exactly that still runs, so the check is
containment rather than equality. Without this the two theorems above would be
consistent with refusing every operation that declares a fault. -/
theorem a_consistent_declaration_still_runs :
    (stepAlpha state₀ .store).state?.isSome := by decide

/-- `divide`'s compute substep declares `divideError`, which the vocabulary does
recognize, so it still runs *and commits its load*. Same reason as
`the_named_context_may_run_it`: "produced a state" is satisfied by a denial. -/
theorem a_recognized_compute_fault_still_runs :
    ∀ s, (stepAlpha state₀ .divide).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## What a fault plan may claim

Three things the transition took on trust from its caller and now checks. Each was
found by local adversarial review, and each is the shape law 8 targets: an
unchecked input is not rejected, it is modelled. -/

/-- A fault class no substep declares is refused, not recorded.

`Substep.faults` has always said what a step may raise and `MemoryProfile.Admits`
has always required an access's `admittedFaults` to be recognized. Nothing
consulted either, so a `FaultPlan` could name a class no registry admitted and the
transition recorded it -- into `RaisedFault`, and into a `ValidMemoryEvent`'s
status, since `MemoryEvent.WellFormed` constrains counts and lengths but not fault
identity. -/
theorem an_undeclared_fault_class_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then
          .before ⟨0, h⟩ ⟨⟨"fake.neverDeclaredFault"⟩⟩ 3 3
        else .none) =
      .rejected (.faultClassNotDeclared ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-- The declared class on the same substep still runs *and is recorded*, so the
check discriminates rather than refusing every fault. Asserting only that the step
produced a state would have passed with the guard deleted and with the fault
silently dropped; review pointed that out. -/
theorem a_declared_fault_class_still_runs :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
        else .none)).state? = some s →
      s.faults.map RaisedFault.fault = [FaultClassId.pageFault] := by
  intro s hs
  cases hs
  decide

/-- A fault on a substep carrying an obligation ledger effect is refused, because
nothing says what becomes of the effect. Before this, a `reserve` that faulted
having written zero bytes still created its release duty, and a `release` that
faulted having written nothing still discharged one -- the second is a leak. -/
theorem a_fault_on_a_ledger_bearing_substep_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.reserve) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none) =
      .rejected .faultWithUndeclaredLedgerEffect := rfl

/-! ## A machine that cannot fill an access is refused, not padded

`Oracle.answer` used to return a bare `Committed`, whose length obligations are
upper bounds. A profile supplying no write data for a nonempty store therefore
produced a `completed` outcome, `AccessOutcome.status` relabelled it
`partialCommit 0 0`, and the operation carried on to its later substeps having
committed nothing, with no fault and no denial. A malformed machine answer became
a successful execution, which is the shape `docs/FOUNDATION.md` law 8 names.
g-reviewer type-checked that counterexample against this fixture.

`CompleteCommitted` makes a short completion unrepresentable and the answer is an
`Option`, so an oracle that cannot fill an access says so rather than padding. -/

/-- A policy whose machine supplies no write data at all. Everything else matches
`policy`. -/
def starvedPolicy : StepPolicy :=
  { policy with oracle := .ofMemory (fun _ _ => []) indeterminateByte }

/-- **The store is refused, and refused before its later effects.**

`Alpha.reserve` writes eight bytes and creates a release obligation. Under the
starved machine nothing is written, the violation is recorded, and the obligation
is *not* created -- the operation stopped rather than reporting a successful
partial completion. -/
theorem a_machine_that_cannot_fill_a_store_is_refused :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.reserve) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.obligations.lookup releaseObligationId = Option.none ∧
      s.memory.byteAt? bufferAlloc 0 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- It reports `machineAnswerIncomplete` rather than a class that would read as a
program error: the program did nothing wrong, the machine description did. -/
theorem the_starved_store_records_the_right_class :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.reserve) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.violations.records?.map AuditViolation.class_ =
        [AuditViolationClass.machineAnswerIncomplete] := by
  intro s hs
  cases hs
  decide

/-- A read is unaffected: the starved machine supplies no *write* data, and
`observedBytes` builds a full-width read from the store itself. So the check
discriminates on what is actually missing. -/
theorem the_starved_machine_still_completes_a_load :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.load) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## A completed access reports that it completed

The completeness test demanded that reads *and* writes both cover the range,
unconditionally on intent. A write-only access has `readCount = 0` by
`Committed.observedAbsent`, so every ordinary load and store recorded
`partialCommit` -- whose docstring says "stopped early without faulting" -- and
`AccessStatus.IsComplete` was false for every access this model can perform except
a full-width read-modify-write.

The counts below are the second half of the same defect, found a round later: a
completed load reports `8 0` and a completed store `0 8`, where `completed`
previously carried no counts and both accessors answered "the whole range" — so a
completed load claimed to have written eight bytes. -/

theorem a_completed_load_reports_completed :
    ∀ s, (stepAlpha state₀ .load).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.completed 8 0] := by
  intro s hs
  cases hs
  decide

theorem a_completed_store_reports_completed :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.completed 0 8] := by
  intro s hs
  cases hs
  decide

/-- A genuinely partial access still reports its prefix, so the fix did not make
the status say "completed" unconditionally. The store read nothing, so its read
count is zero rather than the three the plan named -- which is the read/write
separation reaching the status, where it previously stopped at `Committed`. -/
theorem a_faulted_store_still_reports_its_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
          else .none)).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.faulted .pageFault 0 3] := by
  intro s hs
  cases hs
  decide

/-! ## A faulting read-modify-write can keep its read without its write

`Committed` counts reads and writes separately, and `Grass/Memory/Event.lean`
motivates that with an `xadd` which observed eight bytes and then faulted before
storing. The transition truncated both lists by one shared count, so that outcome
was the one thing the fault path could not express: a faulting RMW always reported
`readCommitted = writeCommitted`. `faulted_rmw_keeps_its_read` never checked the
write, so it passed while demonstrating the opposite of its own section header. -/

theorem faulted_rmw_keeps_its_read_without_its_write :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 8 0
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 8 ∧ e.event.writeCommitted = 0 ∧
        s.memory.byteAt? bufferAlloc 0 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide, by decide⟩

/-! ## A transactional sequence exposes nothing when it faults

`FaultVisibility.transactional` says "no step is visible unless all are".
`visibleEffects?` returned `[]` for it, which handles the substeps *before* the
failure — and `runStep` then committed the faulting substep's own partial write
anyway, because nothing asked whether that one was visible. So a transactional
sequence discarded its completed substep and kept the faulting one's prefix, which
is the reverse of what it declares. Local adversarial review built the case.
`SubstepSequence.faultingEffectVisible` is the missing question. -/

/-- With the fault at the second substep, neither half is visible: not the
completed first, and not the faulting second's prefix. Both bytes still read as
the zeros the allocation started with, rather than the `0xAB` a store writes. -/
theorem transactional_exposes_nothing :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicSplitStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 4
          else .none)).state? = some s →
      s.memory.byteAt? bufferAlloc 0 = some 0x00 ∧
      s.memory.byteAt? bufferAlloc 4 = some 0x00 ∧
      s.events = [] := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- The fault is still recorded. Nothing being *visible* is a statement about
committed effects, not about whether the machine faulted. -/
theorem transactional_still_records_its_fault :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicSplitStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 4
          else .none)).state? = some s →
      s.faults.map RaisedFault.fault = [FaultClassId.pageFault] := by
  intro s hs
  cases hs
  decide

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

/--
**An alias chain is followed, not just one hop.**

`state₀` declares the buffer aliased to the view and the view aliased to
`chainedAlloc`, so all three name the same bytes. `SharesBytes` compared a single
hop, so the two ends of the chain were declared non-conflicting and a
cross-context write to the far end committed with no violation — the same defect
`SharesBytes` was introduced to fix, one hop further out.
`docs/MEMORY_MODEL.md` §7.5 makes mapping and sharing typed transitions, and those
compose.
-/
theorem chained_alias_store_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWriteChained).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The chain really is two hops: the buffer and `chainedAlloc` are not directly
declared aliased, so the theorem above is about transitivity and not about a
declaration that was there all along. -/
theorem the_chain_is_two_hops :
    ¬ (state₀.memory.AliasHop bufferAlloc chainedAlloc) ∧
    state₀.memory.AliasHop bufferAlloc viewAlloc ∧
    state₀.memory.AliasHop viewAlloc chainedAlloc ∧
    state₀.memory.SharesBytes bufferAlloc chainedAlloc := by decide

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
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 8 8
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
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 3 3
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
            .before ⟨1, h⟩ divideError 0 0
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
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
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
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.writeCommitted = 3 ∧ e.event.status = .faulted .pageFault 0 3 := by
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
            .before ⟨1, h⟩ divideError 0 0
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
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
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
        if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 0
        else .none)).rejection? = some .visibilityRuleUnknown := by decide

end Grass.Tests.FakeIsa

