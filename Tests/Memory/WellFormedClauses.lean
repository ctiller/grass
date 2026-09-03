import Grass.Memory.Access

/-!
# Every clause of the declaration-time seal, refused

`AccessDescriptor.WellFormedIn` is the seal `docs/MEMORY_MODEL.md` §1 asks for: the
conditions a descriptor must satisfy before any question of whether the *state*
permits it. It has fourteen clauses.

Twelve of them were untested. Review mutated each clause's proposition to `True`,
one at a time, and rebuilt: only `rangeInProvenance` and `permissionSufficient` were
caught — by `Tests/Op/FakeIsa.lean`'s `badRange_is_rejected` and its permission
sibling. The other twelve could be deleted and nothing in the tree would notice, and
several carry docstrings arguing at length for their existence. `notInert` and
`rangeNonEmpty` each cite `docs/FOUNDATION.md` law 8 for why they must be there.

Nothing projects any clause outside the `Decidable` instance, so a fixture cannot
consume one directly; what it can do is exhibit a descriptor that fails exactly one
and check that `WellFormedIn` refuses it. That is what this file is: one baseline
that is well formed, and fourteen neighbours differing in a single field.

**The point is the pairing.** A refusal alone would not distinguish "this clause
caught it" from "some other clause did", so the baseline is proved well formed in the
same theorem — the two together say the difference is the clause.

**The pairing is only as good as the neighbour being one field away, and three were
not.** The inert intent, the over-wide range and the demandless read each failed a
*second* clause, so each theorem held with the clause it names deleted — which review
demonstrated by deciding all fourteen clauses separately and then rebuilding the tree
with `notInert`, `rangeFitsSpace` and `initializationMatchesIntent` replaced by `True`
in turn. Each of the three now carries its own control, because it is two fields from
the baseline and the baseline can no longer serve.
-/

namespace Tests.Memory.WellFormedClauses

open Grass.Core Grass.Memory

private def allocs : FreshSupply AllocTag := .initial
private def contexts : FreshSupply ContextTag := .initial
private def epochs : FreshSupply EpochTag := .initial

/-- The storage every descriptor below names. -/
def buffer : AllocId := allocs.fresh.1

/-- The accessing context. -/
def thread : ContextId := contexts.fresh.1

private def epoch : EpochId := epochs.fresh.1

/-- The space the descriptors resolve in: 64-bit, numerically addressed. -/
def space : AddressSpace := AddressSpace.cpuVirtual64

/-- Provenance of the buffer's first page, one step down from the root so that
`Nested` has something to hold of. -/
def prov : Provenance :=
  { space := .cpuVirtual, root := buffer, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 4096⟩
    path := [{ kind := .field, label := ⟨"page"⟩, extent := ⟨0, 64⟩ }] }

/-- **The baseline: a well-formed eight-byte store.** Every theorem below differs
from this in one field. -/
def store : AccessDescriptor :=
  { context := thread, address := .numeric 0x1000, space := .cpuVirtual
    provenance := prov, range := ⟨0, 8⟩, intent := .write
    requiredPermission := .readWrite, alignment := 8
    initialization := .readsNothing, producesInitialized := true }

/-- The baseline is well formed. Without this every refusal below would be
compatible with "this descriptor was malformed for some other reason". -/
theorem the_baseline_is_well_formed : store.WellFormedIn space := by decide

/-- `spaceResolved`: the space a descriptor names must be the one it is checked in.
A descriptor that named its own space could switch off its own guards. -/
theorem a_mismatched_space_is_refused :
    ¬ ({ store with space := .spirvPrivate, provenance :=
          { prov with space := .spirvPrivate } } : AccessDescriptor).WellFormedIn space := by
  decide

/-- The baseline with an intent that reads, writes and executes nothing, and with the
initialization claim dropped to match. -/
def inertStore : AccessDescriptor :=
  { store with
    intent := { reads := false, writes := false }
    producesInitialized := false }

/-- `notInert`: an access that neither reads nor writes is not an access.
`MemoryEvent.ofOutcome` mints nothing for one, so admitting it would put a committed
access with no event in the trace.

`producesInitialized := false` is not decoration and its absence was a defect: an
inert intent writes nothing, so the baseline's `producesInitialized := true` also
failed `producesInitializedOnlyIfWrites`, and this theorem held whether `notInert`
existed or not. Review found it by deciding every clause separately and then deleting
`notInert` with the tree green. Two fields now differ from the baseline, so the
baseline is no longer the control; `the_writing_non_producer_is_well_formed` below
is. -/
theorem an_inert_intent_is_refused : ¬ inertStore.WellFormedIn space := by decide

/-- The control for it: the same descriptor with a writing intent is well formed, so
the refusal above is the intent and not the initialization claim. -/
theorem the_writing_non_producer_is_well_formed :
    ({ store with producesInitialized := false } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `rangeNonEmpty`: `MemoryState.Granted` quantifies over a range's bytes and is
vacuously true on an empty one, so this clause is what keeps that vacuity out of the
authority rules two layers down. -/
theorem an_empty_range_is_refused :
    ¬ ({ store with range := ByteRange.empty 0 } : AccessDescriptor).WellFormedIn space := by
  decide

/-- `spaceWellFormed`: the space itself must be realizable. A space claiming more
than sixty-four address bits is not one. -/
theorem an_ill_formed_space_is_refused :
    ¬ store.WellFormedIn { space with repr := .numeric 65 } := by decide

private def symbols : FreshSupply SymbolicAddressTag := .initial

/-- A symbolic address, minted rather than fabricated. -/
def symbolicName : SymbolicAddressId := symbols.fresh.1

/-- `addressRepresentable`: a symbolic address in a numerically addressed space is
not an address of that space. -/
theorem an_unrepresentable_address_is_refused :
    ¬ ({ store with address := .symbolic symbolicName } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `spaceAgrees`: the provenance's space and the descriptor's must be the same one.
§7.5 makes the spaces non-interchangeable. -/
theorem a_provenance_from_another_space_is_refused :
    ¬ ({ store with provenance := { prov with space := .spirvPrivate } } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `provenanceNested`: each step must lie within the one above it. A path that
escapes its parent is a provenance that grants more than it descended from. -/
theorem an_unnested_provenance_is_refused :
    ¬ ({ store with provenance :=
          { prov with path := [{ kind := .field, label := ⟨"escape"⟩
                                 extent := ⟨0, 8192⟩ }] } } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `rangeInProvenance`: the bytes touched must lie within what the provenance
claims. -/
theorem a_range_outside_the_provenance_is_refused :
    ¬ ({ store with range := ⟨0, 4096⟩ } : AccessDescriptor).WellFormedIn space := by decide

/-- `aligned`: the declared address must satisfy the declared alignment. `1` means
"no demand" and is a deliberate declaration rather than a default. -/
theorem a_misaligned_address_is_refused :
    ¬ ({ store with address := .numeric 0x1004 } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `rangeFitsSpace`: the range must fit the space's own width.

The address is `0` rather than the baseline's `0x1000`, because `0x1000` is not
representable in two bits either — the neighbour failed `addressRepresentable` as well,
and the theorem held with `rangeFitsSpace` deleted. Review found it. `0` is
representable and still satisfies the declared alignment of eight, so the width of the
range is the only thing wrong with it. -/
theorem a_range_past_the_space_is_refused :
    ¬ ({ store with address := .numeric 0, range := ⟨0, 8⟩ } :
      AccessDescriptor).WellFormedIn { space with repr := .numeric 2 } := by decide

/-- The control for it: the same descriptor in the same two-bit space with a range
that fits is well formed, so the refusal above is the width and not the space. -/
theorem a_range_inside_the_space_is_admitted :
    ({ store with address := .numeric 0, range := ⟨0, 2⟩ } :
      AccessDescriptor).WellFormedIn { space with repr := .numeric 2 } := by decide

/-- `atomicityAgrees`: the intent's atomicity and the requested ordering's are two
records of one fact, and this is the clause tying them. §7.3's conflict rule reads
the ordering; the authority rules read the intent. -/
theorem a_disagreeing_atomicity_is_refused :
    ¬ ({ store with intent := { reads := false, writes := true, isAtomic := true } } :
      AccessDescriptor).WellFormedIn space := by decide

/-- `permissionSufficient`: the permission a descriptor declares must permit what it
declares it does. -/
theorem an_insufficient_permission_is_refused :
    ¬ ({ store with requiredPermission := .readOnly } :
      AccessDescriptor).WellFormedIn space := by decide

/-- A read that states no initialization demand, and claims to initialize nothing. -/
def demandlessRead : AccessDescriptor :=
  { store with
    intent := .read
    requiredPermission := .readOnly
    producesInitialized := false }

/-- `initializationMatchesIntent`: a reading access must state an initialization
demand and a non-reading one must not. Without it a read could declare
`readsNothing` and skip `denialOf`'s uninitialized clause entirely.

`producesInitialized := false` for the same reason as the inert case: a read writes
nothing, so without it the neighbour also failed `producesInitializedOnlyIfWrites` and
this theorem held with `initializationMatchesIntent` deleted. `readProducer` below is
the control, differing from this descriptor in the initialization demand alone. -/
theorem a_read_that_demands_nothing_is_refused :
    ¬ demandlessRead.WellFormedIn space := by decide

/-- The control for it: the same read that *does* state a demand is well formed. -/
theorem a_read_that_demands_initialization_is_admitted :
    ({ demandlessRead with initialization := .allBytesInitialized } :
      AccessDescriptor).WellFormedIn space := by decide

/-- A read that claims to have initialized what it read. -/
def readProducer : AccessDescriptor :=
  { store with
    intent := .read
    requiredPermission := .readOnly
    initialization := .allBytesInitialized
    producesInitialized := true }

/-- `producesInitializedOnlyIfWrites`: an access that writes nothing cannot claim to
have initialized anything. -/
theorem a_non_writing_producer_is_refused :
    ¬ (readProducer : AccessDescriptor).WellFormedIn space := by decide

end Tests.Memory.WellFormedClauses
