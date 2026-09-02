import Grass.Memory.Apply

/-!
# A straight-line block, discharged from the framing set alone

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's exit criterion is that the framing
lemma set suffices to discharge a straight-line block **without a bespoke local
lemma**. This file is the check, and it is deliberately not a `decide` over a
concrete state.

A fixture that fixed the allocation, the data, and the offsets and closed
everything by `decide` would prove the arithmetic and say nothing about the lemma
set: the kernel would be doing the work the theorems are supposed to do. So the
state here is universally quantified, the data is arbitrary, and every step is
closed by a named exported theorem.

Every proof below is a single application of a named exported theorem:

- `Grass.Memory.byteAt?_write_survives_block`
- `Grass.Memory.cellAt?_runBlock_of_untouched`
- `Grass.Memory.applyAccess_refused_preserves_state`

with `List.mem_singleton` used once to unpack a one-element block. There is one
local declaration, `untouched_of_disjoint_range`, and it is a wrapper rather than
content: its proof is one application of `ByteRange.Disjoint.not_covers`, and it
exists because a caller holds a disjointness fact where `Touches` wants a
non-coverage one. No proof here runs `decide`, `omega`, `simp`, an induction, or
a case split.

If one of those three theorems disappeared, this file would stop compiling. That
is the property the exit criterion is asking for, and it is why the block is
symbolic: a concrete one closed by `decide` would still compile.
-/

namespace Tests.Memory.StraightLineBlock

open Grass.Core Grass.Memory Grass.Std.Logical

/-!
## The block

Three steps over one allocation, in the shape a compiled basic block has: spill a
value, do unrelated work at a disjoint range, reload the spill.

```text
  step 0   store  data      at spill
  step 1   store  scratch   at other      (disjoint from spill)
  step 2   load             at spill      -- must observe step 0's bytes
```

The claim is about steps 0 and 1: what step 0 wrote is still there when step 2
runs. Step 2's own observation is `Grass/Op/Step.lean`'s `Oracle.ofMemory` reading
through `byteAt?`, so establishing the byte is establishing the load.
-/

variable (state : MemoryState) (spill scratch : AccessDescriptor)
  (spillData scratchData : ByteSeq) (indeterminate : Nat → Byte)

/--
**The spilled bytes survive the intervening store.**

Every hypothesis is something a compiler front end knows from the descriptors:
the allocation exists, the spill store was not refused, it is a write, the offset
is inside what it wrote, and the intervening step's declared range does not cover
that offset. No hypothesis is about the byte store.
-/
theorem spill_survives_the_intervening_store {record : AllocationRecord}
    (hfound : state.allocations.lookup spill.provenance.root = some record)
    (hden : denialOf state spill = Option.none)
    (hwrites : spill.intent.writes = true)
    {offset : Nat}
    (hcov : (ByteRange.mk spill.range.start
      (spillData.take spill.range.size).length).Covers offset)
    (hdisjoint : ¬ (scratch.provenance.root = spill.provenance.root ∧
      scratch.range.Covers offset)) :
    (runBlock (applyAccess state spill spillData indeterminate).2 indeterminate
        [(scratch, scratchData)]).2.byteAt? spill.provenance.root offset =
      (spillData.take spill.range.size)[offset - spill.range.start]? :=
  byteAt?_write_survives_block state spill spillData indeterminate
    [(scratch, scratchData)] hfound hden hwrites hcov
    (fun step hstep => by
      rw [List.mem_singleton] at hstep
      subst hstep
      exact hdisjoint)

/--
The same claim for a block of any length.

The two-step version above is the shape a reader recognizes; this is the one that
says the framing set scales. A block is discharged by checking each step's
declared range, which is decidable, and nothing else.
-/
theorem spill_survives_any_block {record : AllocationRecord} (rest : List (AccessDescriptor × ByteSeq))
    (hfound : state.allocations.lookup spill.provenance.root = some record)
    (hden : denialOf state spill = Option.none)
    (hwrites : spill.intent.writes = true)
    {offset : Nat}
    (hcov : (ByteRange.mk spill.range.start
      (spillData.take spill.range.size).length).Covers offset)
    (hall : ∀ step ∈ rest, ¬ Touches step spill.provenance.root offset) :
    (runBlock (applyAccess state spill spillData indeterminate).2 indeterminate
        rest).2.byteAt? spill.provenance.root offset =
      (spillData.take spill.range.size)[offset - spill.range.start]? :=
  byteAt?_write_survives_block state spill spillData indeterminate rest hfound hden
    hwrites hcov hall

/--
Disjoint ranges are what a caller actually has, so this is the hypothesis in the
form a front end supplies it: two ranges the layout proved disjoint, rather than
a pointwise non-coverage fact.
-/
theorem untouched_of_disjoint_range {step : AccessDescriptor × ByteSeq} {id : AllocId}
    {range : ByteRange} (hd : step.1.range.Disjoint range) {offset : Nat}
    (hcov : range.Covers offset) : ¬ Touches step id offset :=
  fun htouch => hd.not_covers htouch.2 hcov

/--
**A refused step changes nothing**, so a block containing one is discharged the
same way.

`docs/MEMORY_MODEL.md` §1 requires the check to run before anything commits, and
this is what that buys a straight-line argument: a step that might be refused
needs no case split, because both outcomes frame everything outside its range and
the refused outcome frames everything.
-/
theorem a_refused_step_frames_everything {class_ : AuditViolationClass}
    (h : denialOf state scratch = some class_) (id : AllocId) (offset : Nat) :
    (applyAccess state scratch scratchData indeterminate).2.cellAt? id offset =
      state.cellAt? id offset := by
  rw [applyAccess_refused_preserves_state state scratch scratchData indeterminate h]

/--
Nothing above assumed the block committed.

`cellAt?_runBlock_of_untouched` holds whether each step wrote, read, or was
refused, so the discharge does not need to know which. That is what makes it
usable before the front end has proved anything about the steps it is skipping
over.
-/
theorem untouched_bytes_survive_regardless (block : List (AccessDescriptor × ByteSeq))
    (id : AllocId) (offset : Nat)
    (hall : ∀ step ∈ block, ¬ Touches step id offset) :
    (runBlock state indeterminate block).2.cellAt? id offset = state.cellAt? id offset :=
  cellAt?_runBlock_of_untouched indeterminate block state hall

end Tests.Memory.StraightLineBlock
