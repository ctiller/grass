import Grass.Memory.Range
import Grass.Std.Logical.Byte

/-!
# The byte store

What an allocation's bytes are, and the framing lemmas `applyAccess` needs.

## Why not a map from offset to byte

The obvious representation is `FiniteMap Nat Byte`, and it is the wrong engine. A
lookup is a linear scan and an insert rebuilds, so a four-kilobyte frame write is
quadratic list surgery — and `docs/INSTRUCTIONS.md` §5's bounded decidable forward
fragment needs `applyAccess` to be *executable*, not merely total, while
`docs/FOUNDATION.md` law 12 asks that routine builds stay light. Accesses are
range-shaped; the store should be too.

## The representation is a journal, and that is a deliberate trade

A write prepends a run. Nothing is merged, split, or rewritten, so a write is
constant time and the *proofs* are short: framing is "the run I just prepended
does not cover this offset, so the lookup skips it", which is a one-line case
split rather than an argument about maintained sortedness.

The cost is that a read scans runs, so a long-running program's reads degrade.
That is a real cost and it is **not** paid off here. What makes it acceptable is
that every lemma below is stated over `byteAt?` rather than over `runs`: a
compacting store that agrees pointwise satisfies all of them unchanged, and
`docs/OLEAN_SHARDING.md` §1 asks for exactly that — facts crossing the boundary as
exported theorems rather than as a representation consumers unfold. Compaction is
owed, and is recorded as owed in `docs/MEMORY_IMPLEMENTATION_PLAN.md`.

## Initialization is a consequence, not a field

A byte is initialized exactly when the store has a value for it. An earlier
placeholder carried a separate list of initialized offsets, which is a second
source of truth that can disagree with the first; `docs/MEMORY_MODEL.md` §4 says
"a write initializes only the bytes it actually completes", and reading that off
the store is the way to keep those two facts from drifting apart.
-/

namespace Grass.Memory

open Grass.Std.Logical

/-- One contiguous run of bytes at an offset. -/
structure Run where
  /-- The offset of the run's first byte. -/
  start : Nat
  /-- The bytes, in order. -/
  bytes : ByteSeq
deriving DecidableEq, Repr

namespace Run

/-- The byte this run holds at `offset`, if it covers it. -/
def byteAt? (run : Run) (offset : Nat) : Option Byte :=
  if run.start ≤ offset then run.bytes[offset - run.start]? else Option.none

/-- The range this run covers. -/
def range (run : Run) : ByteRange := ⟨run.start, run.bytes.length⟩

@[simp] theorem byteAt?_of_lt {run : Run} {offset : Nat} (h : offset < run.start) :
    run.byteAt? offset = Option.none := by simp [byteAt?, Nat.not_le.mpr h]

/-- A run holds nothing past its end. -/
@[simp] theorem byteAt?_of_ge {run : Run} {offset : Nat}
    (h : run.start + run.bytes.length ≤ offset) : run.byteAt? offset = Option.none := by
  simp only [byteAt?]
  split
  · exact List.getElem?_eq_none (by omega)
  · rfl

/-- A run holds a byte exactly where its range covers. -/
theorem byteAt?_isSome_iff {run : Run} {offset : Nat} :
    (run.byteAt? offset).isSome ↔ run.range.Covers offset := by
  simp only [byteAt?, range, ByteRange.covers_def]
  by_cases hlow : run.start ≤ offset
  · rw [if_pos hlow]
    simp only [hlow, true_and]
    constructor
    · intro hsome
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb
      omega
    · intro hlt
      exact Option.isSome_iff_exists.mpr
        ⟨run.bytes[offset - run.start], List.getElem?_eq_getElem (by omega)⟩
  · rw [if_neg hlow]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro hle
    exact absurd hle hlow

end Run

/--
An allocation's bytes.

The runs are a journal, newest first; see the module comment. Consumers should
reason through `byteAt?` and the lemmas below rather than through `runs`.
-/
structure ByteStore where
  /-- Write runs, most recent first. -/
  runs : List Run
deriving DecidableEq, Repr

namespace ByteStore

/-- A store holding nothing. Every byte is uninitialized. -/
def empty : ByteStore := ⟨[]⟩

/--
The byte at `offset`, if any run holds one.

Newest run wins, which is what makes a prepending write a real overwrite.
-/
def byteAt? (store : ByteStore) (offset : Nat) : Option Byte :=
  store.runs.findSome? (·.byteAt? offset)

/-- Write `bytes` starting at `start`. Constant time; see the module comment. -/
def write (store : ByteStore) (start : Nat) (bytes : ByteSeq) : ByteStore :=
  ⟨⟨start, bytes⟩ :: store.runs⟩

/-- `store.Initialized range` holds when every byte of `range` has a value. -/
def Initialized (store : ByteStore) (range : ByteRange) : Prop :=
  ∀ offset, range.Covers offset → (store.byteAt? offset).isSome

@[simp] theorem byteAt?_empty (offset : Nat) : empty.byteAt? offset = Option.none := rfl

theorem not_initialized_empty {range : ByteRange} (h : ¬ range.IsEmpty) :
    ¬ empty.Initialized range := by
  intro hinit
  rw [ByteRange.isEmpty_def] at h
  exact absurd (hinit range.start (ByteRange.covers_of (Nat.le_refl _) (by omega)))
    (by simp)

/-- Every store initializes the empty range, vacuously. -/
@[simp] theorem initialized_empty_range (store : ByteStore) (start : Nat) :
    store.Initialized (ByteRange.empty start) := by
  intro offset hcov
  exact absurd hcov (by simp)

theorem byteAt?_write (store : ByteStore) (start : Nat) (bytes : ByteSeq) (offset : Nat) :
    (store.write start bytes).byteAt? offset =
      ((Run.mk start bytes).byteAt? offset).or (store.byteAt? offset) := by
  simp only [write, byteAt?, List.findSome?_cons]
  cases (Run.mk start bytes).byteAt? offset <;> simp

/--
**The framing law.**

A write outside `offset` leaves the byte at `offset` exactly as it was. This is
the base case of every disjointness argument `applyAccess` makes, and it is one
case split because the journal never rewrites what is already there.
-/
theorem byteAt?_write_of_not_covers (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {offset : Nat} (h : ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (store.write start bytes).byteAt? offset = store.byteAt? offset := by
  rw [byteAt?_write]
  have hnone : (Run.mk start bytes).byteAt? offset = Option.none := by
    cases hrun : (Run.mk start bytes).byteAt? offset with
    | none => rfl
    | some b =>
      have hcov : (Run.mk start bytes).range.Covers offset :=
        Run.byteAt?_isSome_iff.mp (by rw [hrun]; simp)
      exact absurd (show (ByteRange.mk start bytes.length).Covers offset from hcov) h
  rw [hnone]
  simp

/--
A write frames every disjoint range: reading anywhere in `other` is unaffected by
a write confined to a disjoint range.

The range-level form the memory layer uses, derived from the pointwise one.
-/
theorem byteAt?_write_of_disjoint (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {other : ByteRange} (hd : (ByteRange.mk start bytes.length).Disjoint other)
    {offset : Nat} (hcov : other.Covers offset) :
    (store.write start bytes).byteAt? offset = store.byteAt? offset :=
  byteAt?_write_of_not_covers store (fun hin => hd.not_covers hin hcov)

/-- Initialization of a disjoint range survives a write. -/
theorem initialized_write_of_disjoint (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {other : ByteRange} (hd : (ByteRange.mk start bytes.length).Disjoint other)
    (hinit : store.Initialized other) :
    (store.write start bytes).Initialized other := by
  intro offset hcov
  rw [byteAt?_write_of_disjoint store hd hcov]
  exact hinit offset hcov

/-- A write initializes exactly the bytes it wrote. `docs/MEMORY_MODEL.md` §4:
"A write initializes only the bytes it actually completes." -/
theorem initialized_write (store : ByteStore) (start : Nat) (bytes : ByteSeq) :
    (store.write start bytes).Initialized ⟨start, bytes.length⟩ := by
  intro offset hcov
  rw [byteAt?_write]
  have hsome : ((Run.mk start bytes).byteAt? offset).isSome :=
    Run.byteAt?_isSome_iff.mpr hcov
  cases h : (Run.mk start bytes).byteAt? offset with
  | none => rw [h] at hsome; simp at hsome
  | some b => simp

end ByteStore

end Grass.Memory
