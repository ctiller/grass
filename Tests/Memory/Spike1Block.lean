import Grass.Memory.Apply
import Tests.Memory.Spike1Reference

/-!
# The Spike 1 straight-line block

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's exit criterion names a straight-line
Spike 1 block. `Tests/Memory/StraightLineBlock.lean` proves the discharge is
general — universally quantified state, arbitrary data, every step a single
application of an exported theorem. This file runs that discharge on the
descriptors `Tests/Memory/Spike1Reference.lean` declares for
`Spikes/1_Hello_World/Program.lean`.

**What this does not do.** It runs `Grass.Memory.runBlock`, which is a memory-level
executor over `applyAccess`. It does not run `Grass.Op.step`, and
`Spike1Reference.lean` wraps these same descriptors in `SubstepSequence`s for
`step` rather than as the list used here. The two write memory through the same
`MemoryState.commit`, and `Op.step_frames_untouched` is the framing law for a
whole operation; but the sequence executed below is not literally the one the
machine executes. Two review rounds corrected this paragraph, first for claiming it
ran the real mix and then for claiming a `step`-level law existed when it did
not — it does now.

The block is the one the spike's correctness argument turns on:

```text
  mov transferred, 0                 write  stack  [32, 4)
  call [rip + __imp_WriteFile]       read   image  [2048, 8)
                                     write  stack  [0, 8)
  mov eax, transferred               read   stack  [32, 4)
```

The claim is that the last instruction observes what the first wrote. Nothing in
between touches those four bytes: the import read is in a different allocation,
and the return-address write is at frame offset zero, thirty-two bytes below.

## What is decided and what is proved

The side conditions are `decide`d, because they are exactly what a front end
would compute: the allocation is live, the epoch and space match, the range is in
bounds, the permission allows the write, and no intervening step's declared range
covers the slot. Those are range and record checks, and deciding them is the
intended use.

The framing itself is not decided. It comes from
`Grass.Memory.byteAt?_write_survives_block`, applied once. A proof that closed the
whole thing by `decide` would compute the answer from this particular state and
say nothing about whether the lemma set discharges a block — and it would still
compile if every framing theorem were deleted.
-/

namespace Tests.Memory.Spike1Block

open Grass.Core Grass.Memory Grass.Std.Logical Grass.Tests.Spike1

/-! ## The machine the block runs on -/

/-- The stack reservation: four kilobytes, readable and writable, holding nothing
yet. A fresh frame is uninitialized; `docs/MEMORY_MODEL.md` §4 does not hand out
zeros, and starting from `ByteStore.empty` is what keeps `mov transferred, 0`
being the thing that initializes the slot. -/
def stackRecord : AllocationRecord :=
  { extent := ⟨0, 4096⟩, epoch := epoch₀, space := .cpuVirtual, source := .stack
    owners := [mainThread]
    permission := .readWrite, live := true, bytes := .empty
    base := some 0x1000 }

/-- The loaded image. Only the import-table slot is given contents, because it is
the only part of the image this block reads. -/
def imageRecord : AllocationRecord :=
  { extent := ⟨0, 8192⟩, epoch := epoch₀, space := .cpuVirtual
    source := .imageMapping, owners := [mainThread]
    permission := .readOnly, live := true
    bytes := ByteStore.empty.write 2048 (List.replicate 8 0x40) true
    base := some 0x2800 }

/-- The state at the top of the block. -/
def state₀ : MemoryState :=
  (MemoryState.empty.allocateAll?
    [(stackAlloc, stackRecord), (imageAlloc, imageRecord)]).getD .empty

/-- Both allocations happened, so `getD` did not fall back. -/
theorem the_allocations_succeed :
    (MemoryState.empty.allocateAll?
      [(stackAlloc, stackRecord), (imageAlloc, imageRecord)]).isSome := by decide

/-! ## The four accesses, as descriptors

Rebuilt through `Grass.Tests.Spike1.access` from the same provenances the
reference file uses, because that file wraps each one in a `SubstepSequence` and a
block is a list of accesses. -/

/-- `mov transferred, 0` — the store whose bytes must survive. -/
def transferredWrite : AccessDescriptor :=
  access transferredProvenance ⟨32, 4⟩ 0x1020 .write .readWrite 4 false true

/-- The import-table read inside `call`. -/
def importRead : AccessDescriptor :=
  access importProvenance ⟨2048, 8⟩ 0x3000 .read .readOnly 8 true false

/-- The return-address write inside `call`. -/
def returnAddressWrite : AccessDescriptor :=
  access returnSlotProvenance ⟨24, 8⟩ 0x1018 .write .readWrite 8 false true

/-- `mov eax, transferred` — the reload. -/
def transferredRead : AccessDescriptor :=
  access transferredProvenance ⟨32, 4⟩ 0x1020 .read .readWrite 4 true false

/-- Four zero bytes: what `mov transferred, 0` stores. -/
def zeros : ByteSeq := [0, 0, 0, 0]

/-- Eight bytes of return address. Its value is irrelevant to the claim, which is
the point — the block holds for any return address. -/
def returnAddress : ByteSeq := List.replicate 8 0x7F

/-- The API agent's write to the slot it was lent.

**The block was wrong without this, and the way it was wrong is worth recording.**
`betweenStoreAndReload` held the import read and the return-address write and
nothing else, so the block proved `mov eax, transferred` reads **zero** — the value
`mov transferred, 0` left. In `Spikes/1_Hello_World/Program.lean` the reload reads
the byte count `WriteFile` wrote, and the loop's correctness turns on it: it is
tested for zero at the program's no-progress exit, compared against `r14d` at its
provider-violation edge, and used to advance the cursor. So the one instruction whose
result matters was modelled as observing a value that means "no progress", and the
exit criterion "a straight-line Spike 1 block discharges" was met about a block that
is not Spike 1's. Review found it.

The agent's write is a *different context* — `ContextKind.externalAgent` — and that
is exactly why it appears here and not in a `Grass.Op.step` fixture:
`ConflictsWithHistory` refuses every cross-context conflict pending M8's
happens-before, which §4.2 records as making M8 a prerequisite for the first
acceptance program rather than the fourth. `runBlock` is the `applyAccess`-level
executor and asks no such question, so this block can say what the program does while
the transition cannot yet admit it. -/
def agentWrite : AccessDescriptor :=
  { access transferredProvenance ⟨32, 4⟩ 0x1020 .write .readWrite 4 false true with
    context := apiAgent }

/-- The thirteen bytes `WriteFile` reports having written. -/
def transferredCount : ByteSeq := [13, 0, 0, 0]

/-- The `call`'s own two accesses, in order. -/
def betweenStoreAndReload : List (AccessDescriptor × ByteSeq) :=
  [(importRead, []), (returnAddressWrite, returnAddress)]

/--
The state the reload runs against.

Written with a fixed `indeterminate` because the final state does not depend on
one: `Grass.Memory.applyAccess_state_indep` says what an indeterminate read would
have observed stays in the observation and never reaches memory.
`stateAtCall_eq` is that fact for this block.
-/
def stateAtCall : MemoryState :=
  (runBlock (applyAccess state₀ transferredWrite zeros (fun _ => 0)).2 (fun _ => 0)
    betweenStoreAndReload).2

/-- Any choice of `indeterminate` leaves the same state. -/
theorem stateAtCall_eq (indeterminate : Nat → Byte) :
    (runBlock (applyAccess state₀ transferredWrite zeros indeterminate).2 indeterminate
      betweenStoreAndReload).2 = stateAtCall := by
  rw [stateAtCall, runBlock_state_indep indeterminate (fun _ => 0),
    applyAccess_state_indep state₀ transferredWrite zeros indeterminate (fun _ => 0)]

/-- The state the reload runs against: after the agent has written the count.

The agent's write is applied separately rather than folded into the block above,
because the order matters and this is the order: the program stores zero, the `call`
transfers control, the agent writes through the pointer it was lent, and only then
does the program reload. -/
def stateAtReload : MemoryState :=
  (applyAccess stateAtCall agentWrite transferredCount (fun _ => 0)).2

/-! ## The side conditions a front end decides -/

/-- The store is not refused: live allocation, matching epoch and space, in
bounds, and the permission allows a write. -/
theorem the_store_is_not_refused : denialOf state₀ transferredWrite = Option.none := by decide

/-- Neither of the `call`'s steps touches the slot. The import read is in a
different allocation; the return-address write is eight bytes wide at offset 24. The
agent's write *does* touch it, which is the point, and it is applied after this
block rather than inside it. -/
theorem nothing_between_touches_the_slot :
    ∀ i < 4, ∀ step ∈ betweenStoreAndReload, ¬ Touches step stackAlloc (32 + i) := by decide

/-- The slot really is inside what the store wrote, so the theorem below is not
vacuous. -/
theorem the_slot_is_inside_the_store :
    ∀ i < 4, (ByteRange.mk transferredWrite.range.start
      (zeros.take transferredWrite.range.size).length).Covers (32 + i) := by decide

/-! ## The discharge -/

/--
**`mov eax, transferred` observes what `mov transferred, 0` wrote.**

One application of `byteAt?_write_survives_block`. The `call` in between reads a
different allocation and writes a disjoint part of this one, and neither fact
needed anything beyond its declared range.
-/
theorem the_slot_survives_the_call (indeterminate : Nat → Byte) (i : Nat) (hi : i < 4) :
    stateAtCall.byteAt? stackAlloc (32 + i) = some 0 := by
  have hfound : state₀.allocations.lookup transferredWrite.provenance.root =
      some stackRecord := by decide
  have hmain := byteAt?_write_survives_block state₀ transferredWrite zeros indeterminate
    betweenStoreAndReload hfound the_store_is_not_refused (by decide)
    (the_slot_is_inside_the_store i hi)
    (nothing_between_touches_the_slot i hi)
  rw [stateAtCall_eq indeterminate,
    show transferredWrite.provenance.root = stackAlloc from rfl] at hmain
  rw [hmain]
  have hidx : 32 + i - transferredWrite.range.start = i := by
    show 32 + i - 32 = i
    omega
  rw [hidx]
  have hz : ∀ j < 4, (zeros.take transferredWrite.range.size)[j]? = some 0 := by decide
  exact hz i hi

/--
**And the reload observes what the *agent* wrote, not what the program stored.**

This is Spike 1's data flow, and the fixture asserted the opposite for as long as it
existed: `the_slot_survives_the_call` was the whole discharge, so the block proved
`mov eax, transferred` reads zero — the value that means "no progress" — while in
the program it reads the byte count `WriteFile` wrote and the loop's correctness
turns on it. Review found it by reading `Program.lean` beside the fixture.
-/
theorem the_reload_observes_the_agents_count (i : Nat) (hi : i < 4) :
    stateAtReload.byteAt? stackAlloc (32 + i) = transferredCount[i]? := by
  have h : ∀ j < 4, stateAtReload.byteAt? stackAlloc (32 + j) = transferredCount[j]? := by
    decide
  exact h i hi

/-- And the count is not zero, so the theorem above distinguishes the agent's write
from the program's store. Without this it would hold of a block in which the agent
wrote zeros and nothing would have been shown. -/
theorem the_agents_count_is_not_the_stored_zero :
    stateAtReload.byteAt? stackAlloc 32 ≠ stateAtCall.byteAt? stackAlloc 32 := by decide

/-- The agent's write is not refused: the slot is live, in bounds, writable, and the
agent's own context is not something `denialOf` reads — authority is the loan rule's
question and `Grass/Op/Step.lean`'s `refusalOf` answers it. -/
theorem the_agent_write_is_not_refused :
    denialOf stateAtCall agentWrite = Option.none := by decide

/--
The reload is not refused either, which is the other half of "the program works":
the slot is initialized because the store initialized it, so
`AccessDescriptor.initialization`'s `.allBytesInitialized` demand is met rather
than merely not checked.
-/
theorem the_reload_is_not_refused :
    denialOf stateAtReload transferredRead = Option.none := by decide

/-- **And the initialization the reload demands came from the agent, not from the
program.** `Spike1Reference.lean`'s `movEaxTransferred` says its
`allBytesInitialized` demand is met by what `WriteFile` wrote — and until the agent's
write was in this block, the only thing that had initialized the slot was the
program's own store, so the declared justification and the discharged one were
different facts. Review found that too. -/
theorem the_initialization_came_from_the_agent :
    stateAtReload.RangeInitialized stackAlloc ⟨32, 4⟩ ∧
    stateAtReload.byteAt? stackAlloc 32 = some 13 := by
  exact ⟨by decide, by decide⟩

/--
Before the store, the same reload *is* refused, as an uninitialized read.

The control. Without it, `the_reload_is_not_refused` would be consistent with the
initialization check never running.
-/
theorem the_reload_before_the_store_is_refused :
    denialOf state₀ transferredRead = some .uninitializedRead := by decide

end Tests.Memory.Spike1Block
