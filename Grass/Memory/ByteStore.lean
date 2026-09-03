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
What makes that acceptable is that the *named* surface is `cellAt?`, `byteAt?`,
`InitializedAt`, `Initialized`, `empty`, `write`, `compact`, and theorems over
those: `runs`, `Run`, and every lemma mentioning either are `private`, so a consumer
cannot name a run **directly** — see the next section for what it can still do. A store agreeing pointwise satisfies every exported
theorem unchanged, and `docs/OLEAN_SHARDING.md` §1 asks for exactly that — facts
crossing the boundary as exported theorems rather than as a representation
consumers unfold.

**That is a convention, not a seal, and the difference was found the hard way.**
`ByteStore.rec` is generated with the type's own visibility and is not private, and
unification supplies `Run` without the caller ever naming it — so a consumer can
recurse to the list and count it. Review wrote

    noncomputable def runCount (s : ByteStore) : Nat :=
      ByteStore.rec (motive := fun _ => Nat) (fun rs => rs.length) s

outside this module, and it compiles. Two stores that `cellAt?_compact` proves
agree at every offset have different run counts, so compaction *is* observable
through an exported name. An earlier version of this comment said nothing outside
the module could mention a run and that a consumer could not count them; both were
false.

What survives is the claim that matters and no more: every exported *theorem* here
is stated over `cellAt?` or its projections, so a compacting store satisfies them
unchanged. Structural observation — `=`, `DecidableEq`, `Repr`, and now the
recursor — sees the journal, and nothing in the memory layer's reasoning depends on
it.

`compact` is that argument discharged rather than promised: `cellAt?_compact`
proves the compacted store answers every offset identically, so it is a drop-in by
theorem and not by intention. **It is partial.** It drops a run every byte of which
a newer run covers, which is the degenerate case — a loop storing to one slot — and
it does not merge adjacent runs or clip partially overlapping ones, because that
needs splitting a run against a range. Reads are therefore bounded by the number of
distinct live regions plus unnormalised partial overlaps, not by the number of
writes. The remainder is recorded in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2.

Nothing calls `compact` automatically. Calling it on every write would restore the
cost it exists to avoid, so when to call it is a policy an owner of the allocation
lifecycle should set, not something this module should decide.

That is a claim about the exported *theorems*, and it needs both halves of that
qualification. It was not true of the theorems when first written: `cellAt?_write`
and three `Run` lemmas were public and stated over the representation, so a
compacting store could not have satisfied them. They are private now.

The same goes for the derived `DecidableEq` and `Repr` instances, and review
demonstrated that with a machine-checked pair: `empty.write 0 [7] true` and
`(empty.write 0 [7] true).write 0 [7] true` agree at every offset and are provably
distinct, using only exported names. `Repr` prints the runs. So structural
equality on `ByteStore` observes the journal, and a compacting store would be a
drop-in for every theorem here and *not* for `=`.

That is a real limit and it is stated rather than argued away. The instances exist
because `AllocationRecord` derives `DecidableEq`, which is what lets fixtures close
concrete goals by `decide` — `MemoryState` does not derive it, which an earlier
version of this sentence claimed. Nothing in the memory layer's reasoning depends
on `ByteStore` equality meaning agreement: the framing and commutation laws are all
stated over `AgreesOn` or `cellAt?` precisely because it does not.

The exported lemmas are stated over `cellAt?` rather than `byteAt?`, and that
matters: framing over values alone would let a non-initializing write outside a
range change whether a byte inside it counted as initialized.

## Initialization is a consequence, not a field

A byte is initialized exactly when the newest run covering it says so. An earlier
placeholder carried a separate list of initialized offsets, which is a second
source of truth that can disagree with the first; `docs/MEMORY_MODEL.md` §4 says
"a write initializes only the bytes it actually completes", and reading that off
the store is the way to keep those two facts from drifting apart.

Which is why a run carries `initializes` rather than the store being pure bytes.
`AccessDescriptor.producesInitialized` exists precisely because a write can
complete without its bytes counting as initialized afterwards, and a value-only
store would report those bytes as initialized because it had a value for them.
That is the permissive direction `docs/FOUNDATION.md` law 8 forbids, so the flag
travels with the run.

Newest wins for initialization as it does for value, so a non-initializing write
over initialized bytes leaves them uninitialized. The corpus does not settle that
case; it is the conservative reading, and it is the one that cannot admit a
program a stricter model would refuse.
-/

namespace Grass.Memory

open Grass.Std.Logical

/-- One contiguous run of bytes at an offset.

Representation. `ByteStore.runs` and every lemma about `Run` below are private, so
no consumer can *name* a run — but see the module comment: `ByteStore.rec` is not
private and reaches the list anyway, so this is a strong convention rather than a
seal. -/
private structure Run where
  /-- The offset of the run's first byte. -/
  start : Nat
  /-- The bytes, in order. -/
  bytes : ByteSeq
  /-- Whether these bytes count as initialized afterwards. Carried per run rather
  than assumed, because `AccessDescriptor.producesInitialized` lets a completed
  write decline to initialize; see the module comment. -/
  initializes : Bool
deriving DecidableEq, Repr

namespace Run

/-- The byte this run holds at `offset`, if it covers it. -/
private def byteAt? (run : Run) (offset : Nat) : Option Byte :=
  if run.start ≤ offset then run.bytes[offset - run.start]? else Option.none

/-- The range this run covers. -/
private def range (run : Run) : ByteRange := ⟨run.start, run.bytes.length⟩

@[simp] private theorem byteAt?_of_lt {run : Run} {offset : Nat} (h : offset < run.start) :
    run.byteAt? offset = Option.none := by simp [byteAt?, Nat.not_le.mpr h]

/-- A run holds nothing past its end. -/
@[simp] private theorem byteAt?_of_ge {run : Run} {offset : Nat}
    (h : run.start + run.bytes.length ≤ offset) : run.byteAt? offset = Option.none := by
  simp only [byteAt?]
  split
  · exact List.getElem?_eq_none (by omega)
  · rfl

/-- A run holds a byte exactly where its range covers. -/
private theorem byteAt?_isSome_iff {run : Run} {offset : Nat} :
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
  private mk ::
  /-- Write runs, most recent first. Private: see `Run`. -/
  private runs : List Run
deriving DecidableEq, Repr

namespace ByteStore

/-- A store holding nothing. Every byte is uninitialized. -/
def empty : ByteStore := ⟨[]⟩

/--
What the store holds at `offset`: the byte, and whether it counts as initialized.

Newest run wins, which is what makes a prepending write a real overwrite. Both
facts come from the same run: `byteAt?` and `InitializedAt` are projections of
this, and `initializedAt_iff_cellAt?` is the statement that a byte and its
initialization status cannot come from different writes.
-/
def cellAt? (store : ByteStore) (offset : Nat) : Option (Byte × Bool) :=
  store.runs.findSome? fun run => (run.byteAt? offset).map (·, run.initializes)

/-- The byte at `offset`, if the store holds one. -/
def byteAt? (store : ByteStore) (offset : Nat) : Option Byte :=
  (store.cellAt? offset).map Prod.fst

/--
Write `bytes` starting at `start`. Constant time; see the module comment.

`initializes` says whether the written bytes count as initialized afterwards,
which is `AccessDescriptor.producesInitialized`. It is not defaulted: a write
that does not initialize is a real case rather than an oversight, and a default
here would pick one silently.
-/
def write (store : ByteStore) (start : Nat) (bytes : ByteSeq) (initializes : Bool) :
    ByteStore :=
  ⟨⟨start, bytes, initializes⟩ :: store.runs⟩

/-- `store.InitializedAt offset` holds when the newest run covering `offset`
initialized it. -/
def InitializedAt (store : ByteStore) (offset : Nat) : Prop :=
  (store.cellAt? offset).map Prod.snd = some true

instance (store : ByteStore) (offset : Nat) : Decidable (store.InitializedAt offset) :=
  inferInstanceAs (Decidable (_ = _))

/-- `store.Initialized range` holds when every byte of `range` is initialized. -/
def Initialized (store : ByteStore) (range : ByteRange) : Prop :=
  ∀ offset, range.Covers offset → store.InitializedAt offset

/--
A byte and its initialization status come from one run.

`byteAt?` and `InitializedAt` are both projections of `cellAt?`, so where the
store holds byte `b`, being initialized is exactly that same cell carrying
`true`. Had the two been independent lookups they could have disagreed about
which write a byte came from, which is why the store is defined this way round.
-/
theorem initializedAt_iff_cellAt? (store : ByteStore) {offset : Nat} {b : Byte}
    (h : store.byteAt? offset = some b) :
    store.InitializedAt offset ↔ store.cellAt? offset = some (b, true) := by
  unfold byteAt? at h
  unfold InitializedAt
  cases hc : store.cellAt? offset with
  | none => rw [hc] at h; simp at h
  | some cell =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨value, initializes⟩ := cell
    simp only [Option.map_some, Option.some.injEq] at h ⊢
    subst h
    cases initializes <;> simp

/-- `Initialized` quantifies over every `Nat`, which is not decidable as stated;
this bounds it to the range's own offsets so that the transition can run the
check rather than merely state it. -/
theorem initialized_iff (store : ByteStore) (range : ByteRange) :
    store.Initialized range ↔
      ∀ i ∈ List.range range.size, store.InitializedAt (range.start + i) := by
  constructor
  · intro h i hi
    rw [List.mem_range] at hi
    exact h _ (ByteRange.covers_of (Nat.le_add_right _ _) (by omega))
  · intro h offset hcov
    rw [ByteRange.covers_def] at hcov
    have hmem : offset - range.start ∈ List.range range.size := by
      rw [List.mem_range]; omega
    have := h (offset - range.start) hmem
    rwa [Nat.add_sub_cancel' hcov.1] at this

instance (store : ByteStore) (range : ByteRange) : Decidable (store.Initialized range) :=
  decidable_of_iff _ (initialized_iff store range).symm

@[simp] theorem cellAt?_empty (offset : Nat) : empty.cellAt? offset = Option.none := rfl

@[simp] theorem byteAt?_empty (offset : Nat) : empty.byteAt? offset = Option.none := rfl

@[simp] theorem not_initializedAt_empty (offset : Nat) : ¬ empty.InitializedAt offset := by
  simp [InitializedAt]

theorem not_initialized_empty {range : ByteRange} (h : ¬ range.IsEmpty) :
    ¬ empty.Initialized range := by
  intro hinit
  rw [ByteRange.isEmpty_def] at h
  exact not_initializedAt_empty range.start
    (hinit range.start (ByteRange.covers_of (Nat.le_refl _) (by omega)))

/-- Every store initializes the empty range, vacuously. -/
@[simp] theorem initialized_empty_range (store : ByteStore) (start : Nat) :
    store.Initialized (ByteRange.empty start) := by
  intro offset hcov
  exact absurd hcov (by simp)

private theorem cellAt?_write (store : ByteStore) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) (offset : Nat) :
    (store.write start bytes initializes).cellAt? offset =
      (((Run.mk start bytes initializes).byteAt? offset).map (·, initializes)).or
        (store.cellAt? offset) := by
  simp only [write, cellAt?, List.findSome?_cons]
  cases (Run.mk start bytes initializes).byteAt? offset <;> simp

/--
**The framing law.**

A write outside `offset` leaves both the byte at `offset` and its initialization
exactly as they were. This is the base case of every disjointness argument
`applyAccess` makes, and it is one case split because the journal never rewrites
what is already there.

Stated over `cellAt?` rather than over `byteAt?` so that it frames initialization
too: a lemma about values alone would let a non-initializing write outside the
range change whether a byte inside it counted as initialized.
-/
theorem cellAt?_write_of_not_covers (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {initializes : Bool} {offset : Nat}
    (h : ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (store.write start bytes initializes).cellAt? offset = store.cellAt? offset := by
  rw [cellAt?_write]
  have hnone : (Run.mk start bytes initializes).byteAt? offset = Option.none := by
    cases hrun : (Run.mk start bytes initializes).byteAt? offset with
    | none => rfl
    | some b =>
      have hcov : (Run.mk start bytes initializes).range.Covers offset :=
        Run.byteAt?_isSome_iff.mp (by rw [hrun]; simp)
      exact absurd (show (ByteRange.mk start bytes.length).Covers offset from hcov) h
  rw [hnone]
  simp

theorem byteAt?_write_of_not_covers (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {initializes : Bool} {offset : Nat}
    (h : ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (store.write start bytes initializes).byteAt? offset = store.byteAt? offset := by
  simp [byteAt?, cellAt?_write_of_not_covers store h]

/-- Inside the range it wrote, a write determines the cell outright: the newest
run covers the offset, so `cellAt?_write_of_covers` reports the written byte
whatever was underneath. -/
theorem cellAt?_write_of_covers (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {initializes : Bool} {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (store.write start bytes initializes).cellAt? offset =
      (bytes[offset - start]?).map (·, initializes) := by
  rw [cellAt?_write]
  have hsome : ((Run.mk start bytes initializes).byteAt? offset).isSome :=
    Run.byteAt?_isSome_iff.mpr
      (show ((Run.mk start bytes initializes).range).Covers offset from h)
  rw [ByteRange.covers_def] at h
  have hrun : (Run.mk start bytes initializes).byteAt? offset = bytes[offset - start]? := by
    simp [Run.byteAt?, h.1]
  rw [hrun]
  cases hb : bytes[offset - start]? with
  | none => rw [hrun, hb] at hsome; simp at hsome
  | some b => simp

/--
**Writes to disjoint ranges commute.**

Not as store equality — the journal records them in whichever order they arrived,
so `runs` differs — but as agreement at every offset, which is what every framing
argument actually uses. This is why the lemmas here are stated over `cellAt?`.
-/
theorem cellAt?_write_comm (store : ByteStore) {a b : Nat} {bytesA bytesB : ByteSeq}
    {initA initB : Bool}
    (hd : (ByteRange.mk a bytesA.length).Disjoint (ByteRange.mk b bytesB.length))
    (offset : Nat) :
    ((store.write a bytesA initA).write b bytesB initB).cellAt? offset =
      ((store.write b bytesB initB).write a bytesA initA).cellAt? offset := by
  by_cases hina : (ByteRange.mk a bytesA.length).Covers offset
  · have hinb : ¬ (ByteRange.mk b bytesB.length).Covers offset := fun hb => hd.not_covers hina hb
    rw [cellAt?_write_of_not_covers _ hinb, cellAt?_write_of_covers _ hina,
      cellAt?_write_of_covers _ hina]
  · by_cases hinb : (ByteRange.mk b bytesB.length).Covers offset
    · rw [cellAt?_write_of_covers _ hinb, cellAt?_write_of_not_covers _ hina,
        cellAt?_write_of_covers _ hinb]
    · rw [cellAt?_write_of_not_covers _ hinb, cellAt?_write_of_not_covers _ hina,
        cellAt?_write_of_not_covers _ hina, cellAt?_write_of_not_covers _ hinb]

/--
A write frames every disjoint range: reading anywhere in `other` is unaffected by
a write confined to a disjoint range.

The range-level form the memory layer uses, derived from the pointwise one.
-/
theorem cellAt?_write_of_disjoint (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {initializes : Bool} {other : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint other)
    {offset : Nat} (hcov : other.Covers offset) :
    (store.write start bytes initializes).cellAt? offset = store.cellAt? offset :=
  cellAt?_write_of_not_covers store (fun hin => hd.not_covers hin hcov)

/-- **A write neither creates nor destroys initialization outside its own range.**
The `iff`, not just the forward direction: a framing argument needs to carry a
*lack* of initialization across a write as well as its presence, or an
`uninitializedRead` could be laundered by writing somewhere else. -/
theorem initialized_write_iff_of_disjoint (store : ByteStore) {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {other : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint other) :
    (store.write start bytes initializes).Initialized other ↔ store.Initialized other := by
  constructor
  · intro h offset hcov
    have := h offset hcov
    unfold InitializedAt at this ⊢
    rwa [cellAt?_write_of_disjoint store hd hcov] at this
  · intro h offset hcov
    have := h offset hcov
    unfold InitializedAt at this ⊢
    rwa [cellAt?_write_of_disjoint store hd hcov]

/-- Initialization of a disjoint range survives a write, initializing or not. -/
theorem initialized_write_of_disjoint (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {initializes : Bool} {other : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint other)
    (hinit : store.Initialized other) :
    (store.write start bytes initializes).Initialized other := by
  intro offset hcov
  unfold InitializedAt
  rw [cellAt?_write_of_disjoint store hd hcov]
  exact hinit offset hcov

/-- An initializing write initializes exactly the bytes it wrote.
`docs/MEMORY_MODEL.md` §4: "A write initializes only the bytes it actually
completes." -/
theorem initialized_write (store : ByteStore) (start : Nat) (bytes : ByteSeq) :
    (store.write start bytes true).Initialized ⟨start, bytes.length⟩ := by
  intro offset hcov
  unfold InitializedAt
  rw [cellAt?_write]
  cases h : (Run.mk start bytes true).byteAt? offset with
  | none =>
    exact absurd (Run.byteAt?_isSome_iff.mpr
      (show ((Run.mk start bytes true).range).Covers offset from hcov)) (by rw [h]; simp)
  | some b => simp

/--
**A non-initializing write does not initialize.**

The reason `Run.initializes` exists. With a value-only store the bytes below
would report as initialized because the store had values for them, and an
`uninitializedRead` that `AccessDescriptor.initialization` demands be caught
would pass instead — a permissive fallback of exactly the kind
`docs/FOUNDATION.md` law 8 forbids.
-/
theorem not_initializedAt_write_false (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    {offset : Nat} (hcov : (ByteRange.mk start bytes.length).Covers offset) :
    ¬ (store.write start bytes false).InitializedAt offset := by
  unfold InitializedAt
  rw [cellAt?_write]
  cases h : (Run.mk start bytes false).byteAt? offset with
  | none =>
    exact absurd (Run.byteAt?_isSome_iff.mpr
      (show ((Run.mk start bytes false).range).Covers offset from hcov)) (by rw [h]; simp)
  | some b => simp

/-- A non-initializing write over initialized bytes leaves them uninitialized:
newest wins for initialization as it does for value. The conservative reading of
a case `docs/MEMORY_MODEL.md` §4 does not settle; see the module comment. -/
theorem not_initialized_write_false (store : ByteStore) {start : Nat} {bytes : ByteSeq}
    (h : ¬ (ByteRange.mk start bytes.length).IsEmpty) :
    ¬ (store.write start bytes false).Initialized ⟨start, bytes.length⟩ := by
  rw [ByteRange.isEmpty_def] at h
  have hlen : bytes.length ≠ 0 := h
  have hcov : (ByteRange.mk start bytes.length).Covers start :=
    ByteRange.covers_of (Nat.le_refl _) (by show start < start + bytes.length; omega)
  exact fun hinit => not_initializedAt_write_false store hcov (hinit start hcov)

/-!
## Compaction

The journal grows by one run per write and a read scans it, so a program that
stores to one slot in a loop pays for every past store on every later read. That
cost was recorded as owed from the day the store landed, on the argument that
every exported theorem is stated over `cellAt?` and so a compacting store agreeing
pointwise would satisfy them unchanged. `cellAt?_compact` is that argument
discharged rather than asserted: it is the same claim, proved.

What `compact` removes is a run every one of whose bytes a *newer* run already
covers. `findSome?` returns the first covering run and the newer one is earlier,
so such a run can never be the answer and dropping it is invisible. That is the
degenerate case exactly — repeated writes to one range — and it is the one worth
paying for.

What it does **not** do is merge or split runs. Two writes to adjacent ranges stay
two runs, and a write partially overlapping an older one leaves both. Normalising
those needs clipping a run against a range, which splits it, and that is a larger
piece of work than this. So compaction here bounds the degenerate case and does
not make reads generally cheap; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records
the remainder.
-/

/-- `runCoveredBy r seen` holds when every byte `r` holds is also held by some run in
`seen`. Bounded by the run's own length, so it is decidable. -/
private def runCoveredBy (r : Run) (seen : List Run) : Prop :=
  ∀ i, i < r.bytes.length → ∃ s ∈ seen, s.range.Covers (r.start + i)

private instance decRunCoveredBy (r : Run) (seen : List Run) :
    Decidable (runCoveredBy r seen) :=
  inferInstanceAs (Decidable (∀ i, i < r.bytes.length → ∃ s ∈ seen, s.range.Covers (r.start + i)))

/-- Drop every run all of whose bytes an already-scanned (newer) run covers.
`seen` is the runs kept so far, which are exactly the ones a reader meets first. -/
private def pruneFrom (seen : List Run) : List Run → List Run
  | [] => []
  | r :: rest =>
      if runCoveredBy r seen then pruneFrom seen rest
      else r :: pruneFrom (r :: seen) rest

/-- The cell a single run offers a reader at `offset`. -/
private def cellOf (offset : Nat) (run : Run) : Option (Byte × Bool) :=
  (run.byteAt? offset).map (·, run.initializes)

private theorem cellOf_isSome_iff {offset : Nat} {run : Run} :
    (cellOf offset run).isSome ↔ run.range.Covers offset := by
  unfold cellOf
  rw [← Run.byteAt?_isSome_iff]
  cases run.byteAt? offset <;> simp

/--
Pruning does not change what a reader finds.

`seen` holds the runs already scanned, so the hypothesis is the invariant a reader
carries: it has not yet found a covering run. A dropped run is covered everywhere
by runs in `seen`, which come earlier, so it was never the one `findSome?` would
have returned.
-/
private theorem findSome?_pruneFrom (offset : Nat) :
    ∀ (seen : List Run) (l : List Run),
      (∀ s ∈ seen, ¬ s.range.Covers offset) →
      (pruneFrom seen l).findSome? (cellOf offset) = l.findSome? (cellOf offset)
  | _, [], _ => rfl
  | seen, r :: rest, hseen => by
    unfold pruneFrom
    by_cases hcov : r.range.Covers offset
    · have hb : r.start ≤ offset ∧ offset < r.start + r.bytes.length := by
        have h := hcov
        rw [ByteRange.covers_def] at h
        exact ⟨h.1, h.2⟩
      have hnot : ¬ runCoveredBy r seen := by
        intro hcovered
        obtain ⟨s, hmem, hs⟩ := hcovered (offset - r.start) (by omega)
        rw [show r.start + (offset - r.start) = offset from by omega] at hs
        exact hseen s hmem hs
      rw [if_neg hnot]
      have hsome : (cellOf offset r).isSome := cellOf_isSome_iff.mpr hcov
      cases hc : cellOf offset r with
      | none => rw [hc] at hsome; simp at hsome
      | some v => simp [hc]
    · have hnone : cellOf offset r = Option.none := by
        cases hc : cellOf offset r with
        | none => rfl
        | some v => exact absurd (cellOf_isSome_iff.mp (by rw [hc]; simp)) hcov
      by_cases hcovered : runCoveredBy r seen
      · rw [if_pos hcovered, findSome?_pruneFrom offset seen rest hseen,
          List.findSome?_cons, hnone]
      · rw [if_neg hcovered, List.findSome?_cons, List.findSome?_cons, hnone]
        simp only []
        exact findSome?_pruneFrom offset (r :: seen) rest
          (fun s hs => by
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact hcov
            · exact hseen s hs')

/--
Drop the runs a reader can never reach.

**The compaction the module comment promised.** `cellAt?_compact` is the property
that makes it a drop-in: it agrees with the original at every offset, so every
exported theorem holds of it unchanged, because every exported theorem is stated
over `cellAt?`.
-/
def compact (store : ByteStore) : ByteStore := ⟨pruneFrom [] store.runs⟩

/-- **Compaction is invisible.** The store it produces answers every offset
exactly as the original does, in byte and in initialization. -/
@[simp] theorem cellAt?_compact (store : ByteStore) (offset : Nat) :
    store.compact.cellAt? offset = store.cellAt? offset :=
  findSome?_pruneFrom offset [] store.runs (by simp)

/-- The byte consequence. -/
@[simp] theorem byteAt?_compact (store : ByteStore) (offset : Nat) :
    store.compact.byteAt? offset = store.byteAt? offset := by
  unfold byteAt?; rw [cellAt?_compact]

/-- The initialization consequence, so a framing argument survives compaction. -/
@[simp] theorem initializedAt_compact (store : ByteStore) (offset : Nat) :
    store.compact.InitializedAt offset ↔ store.InitializedAt offset := by
  unfold InitializedAt; rw [cellAt?_compact]

/-! ### That it removes anything

`cellAt?_compact` would hold of a `compact` that did nothing, so these say it does
something and does not do too much. They live inside the module because `runs` is
private: a consumer cannot count runs, which is the point of sealing it. -/

/-- Two writes to one range leave two runs, and compaction leaves one. This is the
degenerate case the journal was worst at -- a loop storing to one slot. -/
example :
    ((empty.write 0 [1, 2] true).write 0 [3, 4] true).runs.length = 2 ∧
    (((empty.write 0 [1, 2] true).write 0 [3, 4] true).compact).runs.length = 1 := by
  decide

/-- Writes to disjoint ranges are both kept: neither shadows the other, so
compaction does not remove a run a reader can still reach. -/
example :
    (((empty.write 0 [1, 2] true).write 8 [3, 4] true).compact).runs.length = 2 := by
  decide

/-- A partial overlap keeps both, because the older run still answers the bytes the
newer one does not cover. This is the case compaction does *not* normalise. -/
example :
    (((empty.write 0 [1, 2, 3, 4] true).write 0 [9] true).compact).runs.length = 2 := by
  decide

/-- And the range form. -/
theorem initialized_compact (store : ByteStore) (range : ByteRange) :
    store.compact.Initialized range ↔ store.Initialized range := by
  constructor <;> intro h offset hcov
  · exact (initializedAt_compact store offset).mp (h offset hcov)
  · exact (initializedAt_compact store offset).mpr (h offset hcov)

end ByteStore

end Grass.Memory
