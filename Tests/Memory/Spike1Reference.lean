import Grass.Obligation.Disposition
import Grass.Op.Facets
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

private def allocSupply₂ : FreshSupply AllocTag := allocSupply₁.fresh.2

/-- A two-page reservation the split-store case straddles. -/
def pageCrossAlloc : AllocId := allocSupply₂.fresh.1

private def epochSupply₀ : FreshSupply EpochTag := FreshSupply.initial

/-- The first epoch of both allocations; nothing is reused in Spike 1. -/
def epoch₀ : EpochId := epochSupply₀.fresh.1

private def contextSupply₀ : FreshSupply ContextTag := FreshSupply.initial

private def grantSupply₀ : FreshSupply GrantTag := FreshSupply.initial

/-- The single thread Spike 1 runs on. -/
def mainThread : ContextId := contextSupply₀.fresh.1

/-- The external API agent `WriteFile` runs as. `docs/MEMORY_MODEL.md` §7.1 lists
"external API agent" among the execution context kinds, and Spike 1's whole point is
that one writes a slot the program lent it. -/
def apiAgent : ContextId := contextSupply₀.fresh.2.fresh.1

/-! ## Provenance

Two roots: the stack reservation, and the loaded image. The frame and its slots
descend from the first; sections and symbols from the second. -/

/-- Provenance of the whole stack reservation. -/
def stackProvenance : Provenance :=
  { space := .cpuVirtual, root := stackAlloc, epoch := epoch₀
    source := .stack, rootExtent := ⟨0, 4096⟩, path := [] }

/-- The `HelloWorld` call frame, 64 bytes of the reservation. -/
def frameStep : ProvenanceStep :=
  { kind := .frame, label := ⟨"helloFrame"⟩, extent := ⟨0, 64⟩ }

/-- The `transferred : UInt32` slot the spike declares with `withStack`, at
offset 32 of the frame. -/
def transferredStep : ProvenanceStep :=
  { kind := .slot, label := ⟨"transferred"⟩, extent := ⟨32, 4⟩ }

/-- The eight bytes `push r12` writes.

**One slot per push, and a separate one for the return address.** These were a
single `savedOrReturn` slot at `⟨0, 8⟩`, shared by `push r12` and by the `call`'s
return-address write — which on a real stack would put the return address on top of
a saved nonvolatile register. `Spikes/1_Hello_World/Program.lean` pushes `r12`,
`r13` and `r14` and then calls, so the return address is the fourth slot down, and
a theorem below presented the collision as a property of the model rather than a
defect in it. Review found it. -/
def savedR12Step : ProvenanceStep :=
  { kind := .slot, label := ⟨"savedR12"⟩, extent := ⟨0, 8⟩ }

/-- The return address the `call` writes: below the three saved registers. -/
def returnSlotStep : ProvenanceStep :=
  { kind := .slot, label := ⟨"returnAddress"⟩, extent := ⟨24, 8⟩ }

/-- Provenance of the `transferred` slot. -/
def transferredProvenance : Provenance :=
  { stackProvenance with path := [frameStep, transferredStep] }

/-- Provenance of the slot `push r12` writes. -/
def savedR12Provenance : Provenance :=
  { stackProvenance with path := [frameStep, savedR12Step] }

/-- Provenance of the slot the `call` writes the return address into. -/
def returnSlotProvenance : Provenance :=
  { stackProvenance with path := [frameStep, returnSlotStep] }

/-- A two-page reservation, so a store can straddle the boundary between them.

Its own allocation, because the split store is not the saved-register slot and the
one-page stack reservation cannot contain a store at offset 4095 of length 8 — using
it made the fixture's declared addresses contradict its own offsets, which review
found once the two were finally compared. -/
def pageCrossProvenance : Provenance :=
  { space := .cpuVirtual, root := pageCrossAlloc, epoch := epoch₀
    source := .virtualAlloc, rootExtent := ⟨0, 8192⟩, path := [] }

/-- Provenance of the loaded image. -/
def imageProvenance : Provenance :=
  { space := .cpuVirtual, root := imageAlloc, epoch := epoch₀
    source := .imageMapping, rootExtent := ⟨0, 8192⟩, path := [] }

/-- The `.rdata` section. -/
def rdataStep : ProvenanceStep :=
  { kind := .imageSection, label := ⟨".rdata"⟩, extent := ⟨0, 4096⟩ }

/-- The `payload` static object the spike emits.

Fifteen bytes: `docs/SPIKE_1.md` §1 says "the 15 UTF-8 bytes `Hello, World!
`",
which is thirteen characters plus the two-byte line ending. This said fourteen until
review counted, in the file whose mandate is the exact Spike 1 instruction mix. -/
def payloadStep : ProvenanceStep :=
  { kind := .symbol, label := ⟨"payload"⟩, extent := ⟨0, 15⟩ }

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
    (requiresInitialized producesInitialized : Bool)
    (authority : AuthorityEffect := []) : AccessDescriptor :=
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
    admittedFaults := [.pageFault, .generalProtection]
    authorityEffect := authority }

/-! ## The eight reference cases -/

/--
`push r12` — writes eight bytes of stack the instruction never names.

The address comes from `rsp`, and the provenance is the frame slot it lands in.
Nothing about the instruction's operands mentions memory; a descriptor that could
only describe named operands could not express this.
-/
def pushR12 : SubstepSequence :=
  .single (access savedR12Provenance ⟨0, 8⟩ 0x1000 .write .readWrite 8 false true)

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
bytes it names; `AccessDescriptor.committedWriteRange` is what a later proof reads.
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
        .access (access returnSlotProvenance ⟨24, 8⟩ 0x1018 .write .readWrite 8 false true) ]
    onFault := .priorEffectsVisible }

/-- The identity of the loan the call passes. -/
def slotLoan : GrantId := grantSupply₀.fresh.1

/--
`call qword ptr [rip + __imp_WriteFile]`, **with the loan §6 requires**.

§3.2's own table says what `lea r9, transferred.addr` is for: "taking the address of
a frame slot for a callee, *and the loan that authorizes it*". No reference case
carried one — `Spike1Policy`'s vocabulary declared `grantKinds := ⟨[.loan]⟩` for a
loan nothing issued, which is the registry-with-no-consumer shape this branch
condemns elsewhere. Review found it.

Modelling it changes the milestone conclusion, which is why it is here.
`the_reload_is_refused_by_the_loan_rule` below is the program's *own* reload refused,
by §3's rule, at a clause `refusalOf` reaches before `ConflictsWithHistory` — so M8's
happens-before is not the only thing M2's exit criterion waits on. What unblocks it is
§6's conforming return, which is M4's and which this reference set has no case for,
because `callImportWriteFile` covers both of the call's accesses in one sequence with
no return point.
-/
def callWithLoan : SubstepSequence :=
  { substeps :=
      [ .access (access importProvenance ⟨2048, 8⟩ 0x3000 .read .readOnly 8 true false),
        .access (access returnSlotProvenance ⟨24, 8⟩ 0x1018 .write .readWrite 8 false true
          [.issue slotLoan
            { kind := .loan, holder := apiAgent, lender := mainThread
              provenance := transferredProvenance, range := ⟨32, 4⟩
              rights := .readWrite }]) ]
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

/-- `#UD`, the invalid-opcode fault `ud2` exists to raise. -/
def invalidOpcode : FaultClassId := ⟨⟨"invalidOpcode"⟩⟩

/--
`ud2 @containment_tail(.excessWriteCount)` — faults having touched nothing.

No access, and no ledger effect. `docs/OBLIGATIONS.md` §3 requires every
obligation at a terminal edge to receive a disposition, and reaching `ud2`
discharges none of them: this is the containment tail after an environment
contract violation, where `docs/SEMANTICS.md` §2 allows only the maximal safe
prefix. A declaration that quietly discharged outstanding obligations here would
be the "silently considering obligations discharged on process failure" shortcut
`docs/DECISIONS.md` rejects.
**It is a `compute` substep, not `none_`.** It was `.none_`, whose own docstring is
"performs no access **and cannot fault**" — and `ud2`'s entire semantics is raising
`#UD`. `FaultPlan.before` indexes with `Fin substeps.length`, so with an empty
sequence no fault plan could point at anything and the instruction was
declared unable to do the one thing it does. A theorem below offered
`substeps = []` as the evidence that it discharges nothing, which is a fact about
emptiness standing in for a fault the declaration could not express. Review found
it.
-/
def ud2Containment : SubstepSequence :=
  { substeps := [.compute [invalidOpcode]], onFault := .priorEffectsVisible }

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
      [ .access (access pageCrossProvenance ⟨4095, 1⟩ 0x1FFF .write .readWrite 1 false true),
        .access (access pageCrossProvenance ⟨4096, 7⟩ 0x2000 .write .readWrite 1 false true) ]
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

/-!
Every case below is discharged by `decide`.

That is the point of the section, not a shortcut. `AccessDescriptor.WellFormedIn`
is decidable, so a declaration is checked by computation rather than by a
hand-assembled proof term — which is what an ISA author needs, and what the
descriptor could not offer while an existential obligation payload pushed it into
`Type 1` and cost it `DecidableEq` along with every decidable field.
-/

theorem pushR12_wellFormed : pushR12.WellFormedIn spaceTable := by decide

theorem movEcxImm_wellFormed : movEcxImm.WellFormedIn spaceTable := by decide

theorem leaPayload_wellFormed : leaPayload.WellFormedIn spaceTable := by decide

theorem leaTransferred_wellFormed : leaTransferred.WellFormedIn spaceTable := by decide

theorem ud2Containment_wellFormed : ud2Containment.WellFormedIn spaceTable := by decide

theorem movTransferredZero_wellFormed :
    movTransferredZero.WellFormedIn spaceTable := by decide

theorem movEaxTransferred_wellFormed :
    movEaxTransferred.WellFormedIn spaceTable := by decide

theorem callImportWriteFile_wellFormed :
    callImportWriteFile.WellFormedIn spaceTable := by decide

/-- The two cases added in response to review are checked too, not merely
declared. -/
theorem divMem_wellFormed : divMem.WellFormedIn spaceTable := by decide

theorem splitPageStore_wellFormed : splitPageStore.WellFormedIn spaceTable := by decide

/-! ## Negative fixtures

Each of these was a descriptor an adversarial review constructed and *proved*
well formed against an earlier version of the predicate. They are kept as
fixtures so the holes stay closed: if a later change makes any of them well
formed again, this file stops building. -/

/-- A store that declares it needs only read-only permission. -/
def writeThroughReadOnly : AccessDescriptor :=
  access savedR12Provenance ⟨0, 8⟩ 0x1000 .write .readOnly 8 false true

/--
It is not well formed, because `WellFormedIn` now demands
`requiredPermission.Permits intent`.

Without that clause `Permission.Permits` was dead code and
`docs/MEMORY_MODEL.md` §4's requirement that read, write, and execute be distinct
was unenforced at the chokepoint that exists to enforce it.
-/
theorem writeThroughReadOnly_not_wellFormed :
    ¬ writeThroughReadOnly.WellFormedIn AddressSpace.cpuVirtual64 := by decide

/-- A descriptor naming an address space this profile never declared. -/
def accessInUndeclaredSpace : AccessDescriptor :=
  { access savedR12Provenance ⟨0, 8⟩ 0x1000 .write .readWrite 8 false true with
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
    payloadPointer.provenance.extent = ⟨0, 15⟩ := rfl

/-- A `call` through the import table is two accesses, not one. -/
theorem call_has_two_substeps : callImportWriteFile.substeps.length = 2 := rfl

/-- If the return-address write faults, the import-table read has already
happened. This is the fact `docs/MEMORY_MODEL.md` §1 forbids assuming away. -/
theorem call_import_read_survives_stack_fault :
    callImportWriteFile.visibleEffects? 1 =
      some [access importProvenance ⟨2048, 8⟩ 0x3000 .read .readOnly 8 true false] := rfl

/-- The `call` claims no atomicity across its two accesses, so its profile owes
no justification for one. It declares `priorEffectsVisible`, which is what makes it
claimless — not its length, which `ClaimsAtomicity` used to consult and no longer
does. -/
theorem call_claims_no_atomicity : ¬ callImportWriteFile.ClaimsAtomicity := fun h => h

/-- **Reaching the containment tail discharges nothing, and it does fault.**

The first half was `substeps = []`, which was true of a declaration that could not
fault at all — an emptiness standing in for the `#UD` `ud2` exists to raise. Now the
sequence has a compute substep declaring that fault and no descriptor, so it touches
no memory and carries no ledger effect, and a fault plan can point at it. -/
theorem ud2_discharges_nothing :
    ud2Containment.accesses = [] ∧
    ud2Containment.substeps.length = 1 ∧
    ud2Containment.substeps.map Substep.faults = [[invalidOpcode]] := by
  exact ⟨by decide, by decide, rfl⟩

/-- **`push` and `call`'s stack writes are distinct slots in the same storage.**

They were one slot, `savedOrReturn` at `⟨0, 8⟩`, used by both — which puts the
return address on top of a saved nonvolatile register — and this theorem asserted
`SameStorage` of a provenance with itself, which is `refl` and says nothing. Review
found both. What is worth stating is that the two are the same *storage* and
different *ranges*: a framing argument must separate them by range, and the
allocation identity will not do it. -/
theorem push_and_call_share_storage :
    savedR12Provenance.SameStorage returnSlotProvenance ∧
    savedR12Provenance ≠ returnSlotProvenance ∧
    (ByteRange.mk 0 8).Disjoint ⟨24, 8⟩ := by
  exact ⟨⟨rfl, rfl, rfl⟩, by decide, by decide⟩

/-- The stack and the image are different allocations, so no offset coincidence
can make an access to one authorize an access to the other. -/
theorem stack_and_image_distinct :
    ¬ stackProvenance.SameStorage imageProvenance := by
  refine Provenance.not_sameStorage_of_root_ne ?_
  decide

end Grass.Tests.Spike1
