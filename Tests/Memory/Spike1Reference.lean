import Grass.Obligation.Disposition
import Grass.Memory.Facet
import Grass.Memory.Profile

/-!
# Spike 1 reference access declarations

This file is the M1 freeze evidence required by
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.2. It declares the memory effects of the
exact instruction mix in `Spikes/1_Hello_World/Program.lean`, against the sealed
access descriptor of `docs/MEMORY_MODEL.md` §1.

The point is not that these are correct x86-64 models — the ISA agent owns that,
and these deliberately do not claim a citation. The point is that each case is
**expressible without an escape hatch**. If one of them could not be written, the
descriptor is not sufficient and the freeze has not earned its name. That is the
one question §9 risk 1 says must be answered before ISA authoring begins, and it
is answered by elaboration rather than by assertion.

Four cases are here specifically because they are the ones a weaker descriptor
gets wrong:

- `lea` computes an address and performs **no access**. A descriptor that could
  not express "derives a pointer, touches nothing" would force a spurious read.
- `push` writes memory the instruction never names, through the stack pointer.
- `call` through the import table is *two* accesses in one instruction, with a
  visibility rule between them.
- `ud2` faults having touched nothing, and discharges no obligation.

Identities are minted through `FreshSupply`, not fabricated, because
`Grass.Core.Uid` has no public constructor. That is itself part of what this file
checks: the freshness mechanism has to be usable, not merely sound.
-/

namespace Grass.Tests.Spike1

open Grass.Core Grass.Memory Grass.Obligation

/-! ## Minted identities

Each identity comes from advancing a supply, exactly as an execution would. -/

private def allocSupply₀ : FreshSupply AllocTag := FreshSupply.initial
private def allocSupply₁ := allocSupply₀.fresh.2

/-- The process stack reservation. -/
def stackAlloc : AllocId := allocSupply₀.fresh.1

/-- The loaded image mapping holding `.rdata` and the import table. -/
def imageAlloc : AllocId := allocSupply₁.fresh.1

private def epochSupply₀ : FreshSupply EpochTag := FreshSupply.initial

/-- The first epoch of both allocations; nothing is reused in Spike 1. -/
def epoch₀ : EpochId := epochSupply₀.fresh.1

private def contextSupply₀ : FreshSupply ContextTag := FreshSupply.initial

/-- The single thread Spike 1 runs on. -/
def mainThread : ContextId := contextSupply₀.fresh.1

/-! ## Provenance

Two roots: the stack reservation, and the loaded image. The frame and its slots
descend from the first; sections and symbols from the second. -/

/-- Provenance of the whole stack reservation. -/
def stackProvenance : Provenance :=
  { space := .cpuVirtual, root := stackAlloc, epoch := epoch₀
    source := .stack, path := [] }

/-- The `HelloWorld` call frame, 64 bytes of the reservation. -/
def frameStep : ProvenanceStep :=
  { kind := .frame, label := ⟨"helloFrame"⟩, extent := ⟨0, 64⟩ }

/-- The `transferred : UInt32` slot the spike declares with `withStack`, at
offset 32 of the frame. -/
def transferredStep : ProvenanceStep :=
  { kind := .slot, label := ⟨"transferred"⟩, extent := ⟨32, 4⟩ }

/-- The eight bytes at the top of the frame that `push` and `call` write. -/
def savedSlotStep : ProvenanceStep :=
  { kind := .slot, label := ⟨"savedOrReturn"⟩, extent := ⟨0, 8⟩ }

/-- Provenance of the `transferred` slot. -/
def transferredProvenance : Provenance :=
  { stackProvenance with path := [frameStep, transferredStep] }

/-- Provenance of the eight-byte slot `push` and `call` write. -/
def savedSlotProvenance : Provenance :=
  { stackProvenance with path := [frameStep, savedSlotStep] }

/-- Provenance of the loaded image. -/
def imageProvenance : Provenance :=
  { space := .cpuVirtual, root := imageAlloc, epoch := epoch₀
    source := .imageMapping, path := [] }

/-- The `.rdata` section. -/
def rdataStep : ProvenanceStep :=
  { kind := .imageSection, label := ⟨".rdata"⟩, extent := ⟨0, 4096⟩ }

/-- The `payload` static object the spike emits. -/
def payloadStep : ProvenanceStep :=
  { kind := .symbol, label := ⟨"payload"⟩, extent := ⟨0, 14⟩ }

/-- The `__imp_WriteFile` import table entry. -/
def importStep : ProvenanceStep :=
  { kind := .symbol, label := ⟨"__imp_WriteFile"⟩, extent := ⟨2048, 8⟩ }

/-- Provenance of the `payload` bytes. -/
def payloadProvenance : Provenance :=
  { imageProvenance with path := [rdataStep, payloadStep] }

/-- Provenance of the import-table slot holding `WriteFile`'s address. -/
def importProvenance : Provenance :=
  { imageProvenance with path := [rdataStep, importStep] }

/-! ## A descriptor builder

Only to keep the cases below readable. Every field it defaults is one the cases
genuinely share, and none of them is a field whose default would weaken a check. -/

/-- The address spaces this fixture's profile declares: one 64-bit write-back CPU
space. The descriptors below name it; its properties come from here, not from
them. -/
def spaceTable : AddressSpaceTable := .cpuOnly

/-- Build a plain single-threaded access in the 64-bit CPU space. -/
def access (provenance : Provenance) (range : ByteRange) (address : MachineAddress)
    (intent : AccessIntent) (permission : Permission) (alignment : Nat)
    (requiresInitialized producesInitialized : Bool) : AccessDescriptor :=
  { context := mainThread
    address := .numeric address
    space := .cpuVirtual
    provenance := provenance
    range := range
    intent := intent
    requiredPermission := permission
    alignment := alignment
    initialization :=
      if requiresInitialized then .allBytesInitialized else .readsNothing
    producesInitialized := producesInitialized
    admittedFaults := [.pageFault, .generalProtection] }

/-! ## The eight reference cases -/

/--
`push r12` — writes eight bytes of stack the instruction never names.

The address comes from `rsp`, and the provenance is the frame slot it lands in.
Nothing about the instruction's operands mentions memory; a descriptor that could
only describe named operands could not express this.
-/
def pushR12 : SubstepSequence :=
  .single (access savedSlotProvenance ⟨0, 8⟩ 0x1000 .write .readWrite 8 false true)

/--
`mov ecx, STD_OUTPUT_HANDLE` — an operation with no memory effect at all.

`none_` is a real declaration, not an absent one. `docs/FOUNDATION.md` law 8
distinguishes "declared to touch nothing" from "did not say", and only the first
is expressible as a value.
-/
def movEcxImm : SubstepSequence := .none_

/--
`lea r13, [rip + payload]` — computes an address and performs **no access**.

This is the case that separates address computation from access. `lea` derives a
pointer with `payload`'s provenance; it does not read the bytes. The result is a
`PointerValue`, and it is worth noting that this value cannot be manufactured from
the address alone — constructing it demands the provenance, which is
`docs/MEMORY_MODEL.md` §2's rule that integer loads do not manufacture provenance.
-/
def leaPayload : SubstepSequence := .none_

/-- The pointer `lea r13, [rip + payload]` produces. -/
def payloadPointer : PointerValue :=
  { address := .numeric 0x2000, provenance := payloadProvenance }

/--
`mov transferred, 0` — a typed frame-slot write that produces initialization.

`producesInitialized` is a claim about the bytes this access *commits*, not the
bytes it names; `AccessDescriptor.committedRange` is what a later proof reads.
-/
def movTransferredZero : SubstepSequence :=
  .single (access transferredProvenance ⟨32, 4⟩ 0x1020 .write .readWrite 4 false true)

/--
`lea r9, transferred.addr` — takes the address of a frame slot to pass to a
callee.

No access, like any `lea`. The authority the callee receives is a loan, and loans
are M3, so this case fixes only that the address may be derived without reading
the slot. That matters: the spike takes this address *before* `WriteFile` writes
through it, when the slot's contents are whatever `mov transferred, 0` left.
-/
def leaTransferred : SubstepSequence := .none_

/--
`call qword ptr [rip + __imp_WriteFile]` — two accesses in one instruction.

First the import-table slot is read to obtain the target; then the return address
is written to the stack. They are ordered, and the visibility rule between them is
`priorEffectsVisible`: if the stack write faults, the import read has already
happened. Declaring this as one access with a byte count would lose both the
ordering and the fact that the two touch different allocations with different
permissions.
-/
def callImportWriteFile : SubstepSequence :=
  { substeps :=
      [ .access (access importProvenance ⟨2048, 8⟩ 0x3000 .read .readOnly 8 true false),
        .access (access savedSlotProvenance ⟨0, 8⟩ 0x0FF8 .write .readWrite 8 false true) ]
    onFault := .priorEffectsVisible }

/--
`mov eax, transferred` — reads a slot the environment wrote.

`requiresInitialized` is true, and the initialization it requires was produced by
`WriteFile`, not by this program. `docs/MEMORY_MODEL.md` §4 requires initialization
tracking "at the granularity required to justify every read", including reads of
bytes an external agent wrote, and the provider profile is what supplies that
justification.
-/
def movEaxTransferred : SubstepSequence :=
  .single (access transferredProvenance ⟨32, 4⟩ 0x1020 .read .readWrite 4 true false)

/--
`ud2 @containment_tail(.excessWriteCount)` — faults having touched nothing.

No access, and no ledger effect. `docs/OBLIGATIONS.md` §3 requires every
obligation at a terminal edge to receive a disposition, and reaching `ud2`
discharges none of them: this is the containment tail after an environment
contract violation, where `docs/SEMANTICS.md` §2 allows only the maximal safe
prefix. A declaration that quietly discharged outstanding obligations here would
be the "silently considering obligations discharged on process failure" shortcut
`docs/DECISIONS.md` rejects.
-/
def ud2Containment : SubstepSequence := .none_

/-! ## Two cases from outside Spike 1

Spike 1 does not contain either of these. They are here because an adversarial
review named them as the cases that would break the sealed descriptor, and a
freeze that has only been tested against instructions it was designed for has not
been tested. Both are declared with names the ISA agent will replace; the fault
taxonomy belongs to that profile, not to a fixture. -/

/-- The x86 divide-error fault. Named here only so the case below can be written;
the real taxonomy is the ISA profile's. -/
def divideError : FaultClassId := ⟨⟨"divideError"⟩⟩

/--
`div dword ptr [rbp - 8]` — reads its divisor, then faults from the division.

The `#DE` is raised by a step that performs no memory access, and the read before
it has already happened. This is the case a sequence of accesses alone cannot
state: there would be no index to name the faulting step. With `Substep.compute`
it is index 1, and the read survives.
-/
def divMem : SubstepSequence :=
  { substeps :=
      [ .access (access transferredProvenance ⟨32, 4⟩ 0x1020 .read .readWrite 4 true false),
        .compute [divideError] ]
    onFault := .priorEffectsVisible }

/--
An eight-byte store at `0x1FFF`, crossing a page boundary.

Two substeps, because permissions on x86-64 are per page and the second page may
carry different ones — the descriptor holds one `requiredPermission`, so one
descriptor cannot demand both. The visibility rule is `profileSpecific` because
Intel does not guarantee that a split store is all-or-nothing to other agents,
and this module has no business guessing what the profile says.
-/
def splitPageStore : SubstepSequence :=
  { substeps :=
      [ .access (access savedSlotProvenance ⟨0, 1⟩ 0x1FFF .write .readWrite 1 false true),
        .access (access savedSlotProvenance ⟨1, 7⟩ 0x2000 .write .readWrite 1 false true) ]
    onFault := .profileSpecific ⟨"x86.splitPageStore"⟩ }

/-- The divisor read survives the divide-error fault. -/
theorem div_read_survives_divide_error :
    divMem.visibleEffects? 1 =
      some [access transferredProvenance ⟨32, 4⟩ 0x1020 .read .readWrite 4 true false] :=
  rfl

/-- A compute step declares the fault it raises, so the fault is not floating
free of the sequence that can produce it. -/
theorem div_compute_step_declares_fault :
    divMem.substeps.map Substep.faults =
      [[FaultClassId.pageFault, FaultClassId.generalProtection], [divideError]] := rfl

/--
This module refuses to answer what survives a split-page store.

`none` is the honest result: the rule belongs to the profile. An earlier version
returned the `priorEffectsVisible` answer here, which is a plausible guess and
therefore the worst available behavior.
-/
theorem splitPage_visibility_is_not_answerable_here :
    splitPageStore.visibleEffects? 1 = Option.none := rfl

/-! ## The cases are well formed

Each proof is `by decide` or a direct structure, so a change to the descriptor's
`WellFormed` conditions that these cases no longer satisfy breaks the build. -/

/--
The reusable well-formedness lemma for a plain access in the 64-bit CPU space.

Every hypothesis is a condition that genuinely varies between the cases. Nothing
is discharged by a default: in particular `bound` must be supplied, because a
range fitting the address space is exactly the condition that stops a `Nat` range
from denoting addresses that wrap (`Grass/Memory/Range.lean`).
-/
theorem access_wellFormed {provenance : Provenance} {range : ByteRange}
    {addr : MachineAddress} {intent : AccessIntent} {perm : Permission} {align : Nat}
    {requiresInit producesInit : Bool}
    (space : provenance.space = AddressSpaceId.cpuVirtual)
    (permission : perm.Permits intent)
    (nested : provenance.Nested)
    (extent : ∀ e, provenance.extent? = some e → e.Contains range)
    (notInert : ¬ intent.IsInert)
    (bound : range.WithinBound (2 ^ 64))
    (aligned : IsAligned addr.toNat align)
    (readsInitialized : intent.reads = true ↔ requiresInit = true)
    (writesIfProduced : producesInit = true → intent.writes = true)
    (nonAtomic : intent.isAtomic = false) :
    (access provenance range addr intent perm align requiresInit
      producesInit).WellFormedIn AddressSpace.cpuVirtual64 where
  spaceResolved := rfl
  notInert := notInert
  spaceWellFormed := AddressSpace.wellFormed_cpuVirtual64
  addressRepresentable :=
    AddressSpace.representable_of_bits_eq_64 rfl addr
  spaceAgrees := space
  provenanceNested := nested
  rangeInProvenance := extent
  aligned := by
    intro value h
    simp only [access, Address.value?_numeric, Option.some.injEq] at h
    exact h ▸ aligned
  rangeFitsSpace := by
    intro bits h
    simp only [AddressSpace.cpuVirtual64, AddressRepr.numeric.injEq] at h
    exact h ▸ bound
  atomicityAgrees := by simp [access, nonAtomic, OrderingDemand.plain]
  permissionSufficient := permission
  initializationMatchesIntent := by
    cases requiresInit <;> simp [access, readsInitialized]
  producesInitializedOnlyIfWrites := writesIfProduced

theorem pushR12_wellFormed : pushR12.WellFormedIn spaceTable := by
  unfold pushR12
  refine SubstepSequence.wellFormedIn_single rfl
    (access_wellFormed rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first
    | (intro e h; cases h; decide)
    | exact ⟨by decide, trivial⟩
    | decide

theorem movTransferredZero_wellFormed :
    movTransferredZero.WellFormedIn spaceTable := by
  unfold movTransferredZero
  refine SubstepSequence.wellFormedIn_single rfl
    (access_wellFormed rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first
    | (intro e h; cases h; decide)
    | exact ⟨by decide, trivial⟩
    | decide

theorem movEaxTransferred_wellFormed :
    movEaxTransferred.WellFormedIn spaceTable := by
  unfold movEaxTransferred
  refine SubstepSequence.wellFormedIn_single rfl
    (access_wellFormed rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first
    | (intro e h; cases h; decide)
    | exact ⟨by decide, trivial⟩
    | decide

theorem callImportWriteFile_wellFormed :
    callImportWriteFile.WellFormedIn spaceTable := by
  intro step hstep
  simp only [callImportWriteFile, List.mem_cons, List.not_mem_nil, or_false] at hstep
  rcases hstep with rfl | rfl
  · refine ⟨AddressSpace.cpuVirtual64, rfl, ?_⟩
    refine access_wellFormed rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (intro e h; cases h; decide)
      | exact ⟨by decide, trivial⟩
      | decide
  · refine ⟨AddressSpace.cpuVirtual64, rfl, ?_⟩
    refine access_wellFormed rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (intro e h; cases h; decide)
      | exact ⟨by decide, trivial⟩
      | decide

theorem movEcxImm_wellFormed : movEcxImm.WellFormedIn spaceTable := by
  simp [movEcxImm, SubstepSequence.WellFormedIn, SubstepSequence.none_]

theorem leaPayload_wellFormed : leaPayload.WellFormedIn spaceTable := by
  simp [leaPayload, SubstepSequence.WellFormedIn, SubstepSequence.none_]

theorem leaTransferred_wellFormed : leaTransferred.WellFormedIn spaceTable := by
  simp [leaTransferred, SubstepSequence.WellFormedIn, SubstepSequence.none_]

theorem ud2Containment_wellFormed : ud2Containment.WellFormedIn spaceTable := by
  simp [ud2Containment, SubstepSequence.WellFormedIn, SubstepSequence.none_]

/-! ## Obligations across the `WriteFile` call

`docs/MEMORY_MODEL.md` §6 says an ABI call profile "constructs the pending
frontier state and completion obligation". The framing theorem that does so is
M4, but the *vocabulary* has to be able to express the ledger movement now, and
this section checks that it can.

The interesting question is whether `LedgerDelta` works with no `preserve`
constructor. Spike 1 holds a live obligation across the call — the console handle
from `GetStdHandle` must eventually reach process teardown — and the call must
not disturb it. With framing that is not something the call declares; it is
something the call's silence already says. -/

private def obligationSupply₀ : FreshSupply ObligationTag := FreshSupply.initial
private def obligationSupply₁ := obligationSupply₀.fresh.2

/-- The obligation created by `GetStdHandle`: the returned handle is a resource
with a lifecycle. -/
def handleObligationId : ObligationId := obligationSupply₀.fresh.1

/-- The obligation created by the `WriteFile` call: it must run to completion, or
its partial result must be accounted for. -/
def writeCompletionId : ObligationId := obligationSupply₁.fresh.1

/-- The Win32 handle protocol. -/
def win32HandleProtocol : ObligationProtocolId := ⟨⟨"win32.handle"⟩⟩

/-- The Win32 synchronous I/O protocol. -/
def win32WriteProtocol : ObligationProtocolId := ⟨⟨"win32.write"⟩⟩

/-- The obligation to account for the console handle. -/
def handleObligation : Obligation :=
  { id := handleObligationId, kind := .closeHandle, protocol := win32HandleProtocol
    owner := mainThread, payload := ⟨Unit, ()⟩ }

/-- The obligation to complete the write. -/
def writeCompletionObligation : Obligation :=
  { id := writeCompletionId, kind := .completePartialIo, protocol := win32WriteProtocol
    owner := mainThread, payload := ⟨Unit, ()⟩ }

/-- The ledger effect of entering the `WriteFile` call: one obligation created,
and nothing said about the handle obligation. -/
def callLedgerEffect : LedgerEffect := [.create writeCompletionObligation]

/-- The ledger effect of a returning call that wrote everything: the completion
obligation is discharged. -/
def returnLedgerEffect : LedgerEffect := [.discharge writeCompletionId]

/--
The call does not touch the handle obligation, and says so by not mentioning it.

This is the framing story `Grass/Obligation/Delta.lean` is built on. Had
`preserve` been a constructor, the call would have had to enumerate every
obligation it was leaving alone — and could have listed one it also discharged.
-/
theorem call_preserves_handle_obligation :
    callLedgerEffect.PreservesIdentity handleObligationId := by
  intro delta hd
  simp only [callLedgerEffect, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  refine ⟨by simp, ?_, by simp [LedgerDelta.reowns]⟩
  simp only [LedgerDelta.produces_create, List.mem_singleton]
  intro h
  exact absurd h.symm (FreshSupply.never_reissued (.refl _) (by decide))

/-- Returning discharges exactly the completion obligation. -/
theorem return_discharges_write_completion :
    returnLedgerEffect.consumes = [writeCompletionId] := rfl

/-- Returning does not touch the handle obligation either. -/
theorem return_preserves_handle_obligation :
    returnLedgerEffect.PreservesIdentity handleObligationId := by
  intro delta hd
  simp only [returnLedgerEffect, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  refine LedgerDelta.preservesIdentity_discharge_of_ne ?_
  intro h
  exact absurd h (FreshSupply.never_reissued (.refl _) (by decide)).symm

/--
The handle obligation reaches process exit and is adopted by teardown.

`docs/OBLIGATIONS.md` §3 permits this: "Process exit may transfer virtual memory,
handles, and similar resources to a modeled OS teardown contract." It is a normal
disposition, so successful exit is not left holding an abnormal one.
-/
def handleDisposition : TerminalOutcome :=
  { obligation := handleObligationId, disposition := .teardownAdopted ⟨"win32.processExit"⟩ }

theorem handleDisposition_isNormal : handleDisposition.disposition.IsNormal := trivial

/-- Teardown adoption needs no licence from the program's specification, unlike
an abandonment. -/
theorem handleDisposition_needs_no_specification_support :
    ¬ handleDisposition.disposition.RequiresSpecificationSupport := fun h => h

/-- Had the handle instead been abandoned, the specification would have had to
say so. This is the asymmetry `docs/OBLIGATIONS.md` §3 turns on, and the reason a
platform's permission to abandon is not by itself sufficient. -/
theorem abandonment_needs_specification_support :
    (Disposition.abandonedUnknown).RequiresSpecificationSupport := trivial

/-! ## Negative fixtures

Each of these was a descriptor an adversarial review constructed and *proved*
well formed against an earlier version of the predicate. They are kept as
fixtures so the holes stay closed: if a later change makes any of them well
formed again, this file stops building. -/

/-- A store that declares it needs only read-only permission. -/
def writeThroughReadOnly : AccessDescriptor :=
  access savedSlotProvenance ⟨0, 8⟩ 0x1000 .write .readOnly 8 false true

/--
It is not well formed, because `WellFormedIn` now demands
`requiredPermission.Permits intent`.

Without that clause `Permission.Permits` was dead code and
`docs/MEMORY_MODEL.md` §4's requirement that read, write, and execute be distinct
was unenforced at the chokepoint that exists to enforce it.
-/
theorem writeThroughReadOnly_not_wellFormed :
    ¬ writeThroughReadOnly.WellFormedIn AddressSpace.cpuVirtual64 := by
  intro h
  exact absurd h.permissionSufficient (by decide)

/-- A descriptor naming an address space this profile never declared. -/
def accessInUndeclaredSpace : AccessDescriptor :=
  { access savedSlotProvenance ⟨0, 8⟩ 0x1000 .write .readWrite 8 false true with
    space := .deviceLocal }

/--
It is not admitted, because the space cannot be resolved.

This is the structural half of the fix. When a descriptor carried its own
`AddressSpace` value, an author could pair the id `cpu.virtual` with
`repr := .symbolic` and make the alignment and range-bound clauses vacuous — both
are conditioned on the representation. Naming the space and resolving it through
the profile means the guards are checked against the profile's answer, not the
access's own.
-/
theorem accessInUndeclaredSpace_not_admitted (vocabulary : AdmittedVocabulary)
    (h : vocabulary.addressSpaces = .cpuOnly) :
    ¬ vocabulary.Admits accessInUndeclaredSpace := by
  refine AdmittedVocabulary.not_admits_of_undeclared_space ?_
  rw [h]
  decide

/-- An empty space table admits nothing at all, which is the safe failure. -/
theorem nothing_admitted_without_spaces (vocabulary : AdmittedVocabulary)
    (h : vocabulary.addressSpaces = .empty) (d : AccessDescriptor) :
    ¬ vocabulary.Admits d :=
  AdmittedVocabulary.not_admits_of_no_address_spaces h d

/-! ## What the cases establish -/

/-- `lea` performs no access. The declaration exists and says "nothing", which is
not the same as no declaration. -/
theorem lea_performs_no_access : leaPayload.substeps = [] := rfl

/-- The pointer `lea` produces carries `payload`'s provenance, not the image
root's. Descending is not free: it required the nesting the provenance records. -/
theorem payloadPointer_provenance :
    payloadPointer.provenance.extent? = some ⟨0, 14⟩ := rfl

/-- A `call` through the import table is two accesses, not one. -/
theorem call_has_two_substeps : callImportWriteFile.substeps.length = 2 := rfl

/-- If the return-address write faults, the import-table read has already
happened. This is the fact `docs/MEMORY_MODEL.md` §1 forbids assuming away. -/
theorem call_import_read_survives_stack_fault :
    callImportWriteFile.visibleEffects? 1 =
      some [access importProvenance ⟨2048, 8⟩ 0x3000 .read .readOnly 8 true false] := rfl

/-- The `call` claims no atomicity across its two accesses, so its profile owes
no justification for one. -/
theorem call_claims_no_atomicity : ¬ callImportWriteFile.ClaimsAtomicity := by
  rintro ⟨h, _⟩
  exact h

/-- Reaching the containment tail discharges nothing. -/
theorem ud2_discharges_nothing : ud2Containment.substeps = [] := rfl

/-- `push` and `call`'s stack write are the same slot in the same storage, so a
later proof must relate them rather than framing them apart. -/
theorem push_and_call_share_storage :
    savedSlotProvenance.SameStorage savedSlotProvenance :=
  Provenance.SameStorage.refl _

/-- The stack and the image are different allocations, so no offset coincidence
can make an access to one authorize an access to the other. -/
theorem stack_and_image_distinct :
    ¬ stackProvenance.SameStorage imageProvenance := by
  refine Provenance.not_sameStorage_of_root_ne ?_
  decide

end Grass.Tests.Spike1
