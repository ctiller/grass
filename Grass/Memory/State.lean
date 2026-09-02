import Grass.Memory.ByteStore
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Event
import Grass.Memory.Profile
import Grass.Std.Logical.FiniteMap

/-!
# The memory state a transition acts on

The minimum state needed to decide whether a declared access is permitted: what
allocations exist, how big they are, what permission they carry, which of their
bytes are initialized, and which of them alias each other.

This is deliberately not the full M2 state. It exists because the seam cannot be
demonstrated without it — an operation's facets have to be consumed *by something*
that checks provenance, ranges, and aliasing, or the facet interface is untested
prose. What is here is what the vertical needs; the byte-level store, the
representation choice, and the framing lemma set remain M2.

## Aliasing is state, not provenance

`docs/MEMORY_MODEL.md` §7.5 contemplates mapping and sharing: a host-visible
device buffer, a file view, and a physical/virtual pair are distinct allocations
over the same bytes. Provenance cannot tell you they alias — that is exactly what
distinct `AllocId`s mean — so the state carries the relation, and the conflict
test consults it.

Without this, `Conflicts` required `SameStorage` and declared every aliased pair
non-conflicting: a write through a mapped view and a write through the file it
maps would not conflict, and every race-freedom theorem downstream would have
inherited that.
-/

namespace Grass.Memory

open Grass.Core Grass.Obligation Grass.Std.Logical

/-- What the state records about one allocation. -/
structure AllocationRecord where
  /-- The allocation's extent, in bytes. -/
  extent : ByteRange
  /-- The current reuse generation of its storage. -/
  epoch : EpochId
  /-- The address space it lives in. -/
  space : AddressSpaceId
  /-- The permission its storage carries. -/
  permission : Permission
  /-- Whether it is live. A dead allocation authorizes nothing, whatever
  provenance is presented. -/
  live : Bool
  /-- The allocation's bytes.

  Initialization is read off this rather than tracked beside it: a separate list
  of initialized offsets was a second source of truth that could disagree with
  the values, and `RangeInitialized` now cannot drift from what was written. -/
  bytes : ByteStore
deriving DecidableEq, Repr

/--
The memory state.

`aliases` is symmetric by convention and `SharesBytes` closes it, so a profile
declares each aliased pair once.
-/
structure MemoryState where
  /-- The live and dead allocations. -/
  allocations : FiniteMap AllocId AllocationRecord
  /-- Pairs of allocations whose bytes are the same storage. -/
  aliases : List (AllocId × AllocId)
  /-- The authority grants currently live.

  `docs/MEMORY_MODEL.md` §3 makes this map the authoritative borrowing state.
  What is here is the map and nothing else: the split, join, freeze, and
  exclusivity-iff-empty laws are M3's, and the frame lifetime discipline is
  M4's. It exists a milestone early so that `Grass/Op/Step.lean`'s
  `AuthorityProvider` has a real table to check against, which is what shows a
  new authority kind needs no change to operation packaging. -/
  grants : FiniteMap GrantId AuthorityGrant

namespace MemoryState

/-- The state with nothing allocated. -/
def empty : MemoryState := { allocations := .empty, aliases := [], grants := .empty }

/-- Record a grant of authority. -/
def grant (state : MemoryState) (id : GrantId) (record : AuthorityGrant) : MemoryState :=
  { state with grants := state.grants.insert id record }

/--
`state.Granted context provenance range intent` holds when some live grant
authorizes that access.

Existentially quantified over the grant, because an access does not name the one
it relies on; see `Grass/Memory/Authority.lean`. Decidable because the grant table
is finite.
-/
def Granted (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grants.entries,
    entry.2.Authorizes context provenance range intent

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.Granted context provenance range intent) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `state.GrantedOfKind` additionally requires the authorizing grant to be of a
particular kind, which is how one provider distinguishes itself from another over
the same table. -/
def GrantedOfKind (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grants.entries,
    entry.2.kind = kind ∧ entry.2.Authorizes context provenance range intent

instance (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.GrantedOfKind kind context provenance range intent) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A state with no grants authorizes nothing. Authority is held, not assumed. -/
theorem not_granted_empty (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    ¬ empty.Granted context provenance range intent := by
  rintro ⟨entry, hmem, -⟩
  simp [empty, FiniteMap.empty] at hmem

/-- `state.SharesBytes a b` holds when two allocations name the same storage,
either because they are the same allocation or because the profile declared them
aliased. -/
def SharesBytes (state : MemoryState) (a b : AllocId) : Prop :=
  a = b ∨ (a, b) ∈ state.aliases ∨ (b, a) ∈ state.aliases

instance (state : MemoryState) (a b : AllocId) : Decidable (state.SharesBytes a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem sharesBytes_refl (state : MemoryState) (a : AllocId) : state.SharesBytes a a :=
  .inl rfl

theorem SharesBytes.symm {state : MemoryState} {a b : AllocId}
    (h : state.SharesBytes a b) : state.SharesBytes b a := by
  rcases h with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- Record a new allocation. -/
def allocate (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    MemoryState :=
  { state with allocations := state.allocations.insert id record }

/-- Declare that two allocations name the same storage. -/
def alias (state : MemoryState) (a b : AllocId) : MemoryState :=
  { state with aliases := (a, b) :: state.aliases }

/--
Write `bytes` at `start` in allocation `id`.

`initializes` is `AccessDescriptor.producesInitialized`: a completed write does
not always credit initialization, and `ByteStore` carries that per run so the two
facts cannot disagree. A write to an allocation that is not there changes
nothing; `performAccess` reaches this only after `denialOf` has found the record,
so the missing case is unreachable there rather than silently permissive.
-/
def write (state : MemoryState) (id : AllocId) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) : MemoryState :=
  match state.allocations.lookup id with
  | Option.none => state
  | some record =>
      { state with
        allocations := state.allocations.insert id
          { record with bytes := record.bytes.write start bytes initializes } }

/-- The byte allocation `id` holds at `offset`, if it holds one. -/
def byteAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option Byte :=
  (state.allocations.lookup id).bind (·.bytes.byteAt? offset)

/-- What allocation `id` holds at `offset`: the byte and whether it counts as
initialized. Both from one lookup, for the reason `ByteStore.cellAt?` gives. -/
def cellAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option (Byte × Bool) :=
  (state.allocations.lookup id).bind (·.bytes.cellAt? offset)

/-- The byte is the cell's first component. Both go through one lookup, so a
framing fact proved for cells is immediately a framing fact for bytes. -/
@[simp] theorem byteAt?_eq_map_cellAt? (state : MemoryState) (id : AllocId) (offset : Nat) :
    state.byteAt? id offset = (state.cellAt? id offset).map Prod.fst := by
  unfold byteAt? cellAt? ByteStore.byteAt?
  cases state.allocations.lookup id <;> simp

/-- `state.InitializedAt id offset` holds when that byte is initialized. The
pointwise form of `RangeInitialized`, which a padding argument needs because
padding is a set of offsets rather than a range. -/
def InitializedAt (state : MemoryState) (id : AllocId) (offset : Nat) : Prop :=
  (state.cellAt? id offset).map Prod.snd = some true

instance (state : MemoryState) (id : AllocId) (offset : Nat) :
    Decidable (state.InitializedAt id offset) :=
  inferInstanceAs (Decidable (_ = _))

/-- The bytes `id` holds over `range`, if every one of them has a value. Partial
coverage reads as `none` rather than as a shorter sequence, because a caller that
asked for `range` and received fewer bytes would have to decide which ones it
got. -/
def readBytes (state : MemoryState) (id : AllocId) (range : ByteRange) :
    Option ByteSeq :=
  match state.allocations.lookup id with
  | Option.none => Option.none
  | some record =>
      (List.range range.size).mapM fun i => record.bytes.byteAt? (range.start + i)

/-- `state.RangeInitialized id range` holds when every offset of `range` is
initialized in `id`. Read off the byte store, so it says what the writes said. -/
def RangeInitialized (state : MemoryState) (id : AllocId) (range : ByteRange) : Prop :=
  match state.allocations.lookup id with
  | Option.none => False
  | some record => record.bytes.Initialized range

instance (state : MemoryState) (id : AllocId) (range : ByteRange) :
    Decidable (state.RangeInitialized id range) := by
  unfold RangeInitialized; split <;> infer_instance

/-! ### Framing

What a write does *not* change. `applyAccess` reasons by disjointness, and
disjointness is only useful with lemmas saying that everything outside the
written range survives. `docs/MEMORY_MODEL.md` §2 makes provenance the authority,
so the two axes are "a different allocation" and "a disjoint range within the
same one"; both are below. -/

/-- A write changes no allocation's metadata: extent, epoch, space, permission,
and liveness come back unchanged. `denialOf` reads exactly those five fields, so
`write_preserves_metadata` is what says a write cannot quietly widen what a later
access may reach. -/
theorem write_preserves_metadata (state : MemoryState) (id : AllocId) (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) (other : AllocId) (record : AllocationRecord)
    (h : (state.write id start bytes initializes).allocations.lookup other = some record) :
    ∃ before, state.allocations.lookup other = some before ∧
      before.extent = record.extent ∧ before.epoch = record.epoch ∧
      before.space = record.space ∧ before.permission = record.permission ∧
      before.live = record.live := by
  unfold write at h
  split at h
  · exact ⟨record, h, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i found hfound
    by_cases hid : other = id
    · subst hid
      rw [FiniteMap.lookup_insert_self] at h
      cases h
      exact ⟨found, hfound, rfl, rfl, rfl, rfl, rfl⟩
    · rw [FiniteMap.lookup_insert_ne _ hid _] at h
      exact ⟨record, h, rfl, rfl, rfl, rfl, rfl⟩

/-- **A write to one allocation leaves every other allocation alone.**

Distinct `AllocId`s are distinct storage by construction, which is what
`docs/MEMORY_MODEL.md` §2 means by making provenance rather than address the
authority. -/
theorem write_preserves_other_allocation (state : MemoryState) {id other : AllocId}
    (hne : other ≠ id) (start : Nat) (bytes : ByteSeq) (initializes : Bool) :
    (state.write id start bytes initializes).allocations.lookup other =
      state.allocations.lookup other := by
  unfold write
  split
  · rfl
  · exact FiniteMap.lookup_insert_ne _ hne _

/-- Initialization of another allocation survives a write. -/
theorem rangeInitialized_write_of_other_allocation (state : MemoryState)
    {id other : AllocId} (hne : other ≠ id) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) {range : ByteRange} (h : state.RangeInitialized other range) :
    (state.write id start bytes initializes).RangeInitialized other range := by
  unfold RangeInitialized at h ⊢
  rw [write_preserves_other_allocation state hne start bytes initializes]
  exact h

/-- **Initialization of a disjoint range in the same allocation survives a
write.** The state-level form of `ByteStore.initialized_write_of_disjoint`, and
the one a framing argument about two fields of one object needs. -/
theorem rangeInitialized_write_of_disjoint (state : MemoryState) (id : AllocId)
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {range : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint range)
    (h : state.RangeInitialized id range) :
    (state.write id start bytes initializes).RangeInitialized id range := by
  unfold RangeInitialized at h ⊢
  unfold write
  cases hfound : state.allocations.lookup id with
  | none => rw [hfound] at h; exact absurd h (by simp)
  | some record =>
    rw [hfound] at h
    rw [FiniteMap.lookup_insert_self]
    exact ByteStore.initialized_write_of_disjoint record.bytes hd h

/--
Two memory states agree when every allocation holds the same *cell* — byte and
initialization — at every offset. This, and not structural equality, is what a
framing law can say about a journal-backed store.

Over `cellAt?` rather than `byteAt?`, and that is the whole point. An earlier
version compared bytes only, which made the commutation laws unable to carry the
refusal decision across: `denialOf` reads `RangeInitialized`, so two states
agreeing on every byte can still disagree about whether a later access is refused.
Review built exactly that pair. It is the same mistake `ByteStore`'s module
comment warns about, made one layer up.
-/
def AgreesOn (a b : MemoryState) : Prop :=
  ∀ id offset, a.cellAt? id offset = b.cellAt? id offset

/-- Agreeing states hold the same bytes. The `byteAt?` consequence, for callers
that only need values. -/
theorem AgreesOn.byteAt? {a b : MemoryState} (h : a.AgreesOn b) (id : AllocId)
    (offset : Nat) : a.byteAt? id offset = b.byteAt? id offset := by
  rw [byteAt?_eq_map_cellAt?, byteAt?_eq_map_cellAt?, h id offset]

/-- Agreeing states agree on what is initialized, which is what lets a
commutation argument carry the refusal decision. -/
theorem AgreesOn.initializedAt {a b : MemoryState} (h : a.AgreesOn b) (id : AllocId)
    (offset : Nat) : a.InitializedAt id offset ↔ b.InitializedAt id offset := by
  unfold InitializedAt
  rw [h id offset]

theorem AgreesOn.refl (state : MemoryState) : state.AgreesOn state := fun _ _ => rfl

theorem AgreesOn.symm {a b : MemoryState} (h : a.AgreesOn b) : b.AgreesOn a :=
  fun id offset => (h id offset).symm

theorem AgreesOn.trans {a b c : MemoryState} (hab : a.AgreesOn b) (hbc : b.AgreesOn c) :
    a.AgreesOn c := fun id offset => (hab id offset).trans (hbc id offset)

/-- A write to a missing allocation changes nothing. `performAccess` reaches
`write` only after `denialOf` has found the record, so this case does not arise
there; it is stated because `write` is total and a caller may not have checked. -/
theorem write_of_missing (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool)
    (h : state.allocations.lookup id = Option.none) :
    state.write id start bytes initializes = state := by
  unfold write; rw [h]

/-- A write leaves its own allocation present, with the written store. -/
theorem lookup_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) :
    (state.write id start bytes initializes).allocations.lookup id =
      some { record with bytes := record.bytes.write start bytes initializes } := by
  unfold write
  rw [h]
  exact FiniteMap.lookup_insert_self _ _ _

/-- The cell a write leaves at an offset, in terms of the store's own law. -/
theorem cellAt?_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) (offset : Nat) :
    (state.write id start bytes initializes).cellAt? id offset =
      (record.bytes.write start bytes initializes).cellAt? offset := by
  unfold cellAt?
  rw [lookup_write_self state start bytes initializes h]
  rfl

/-- The byte a write leaves at an offset, in terms of the store's own law. -/
theorem byteAt?_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) (offset : Nat) :
    (state.write id start bytes initializes).byteAt? id offset =
      (record.bytes.write start bytes initializes).byteAt? offset := by
  unfold byteAt?
  rw [lookup_write_self state start bytes initializes h]
  rfl

/-- Two states whose allocation records agree at `id` agree on what is
initialized there. -/
theorem rangeInitialized_congr_of_lookup {a b : MemoryState} {id : AllocId}
    {range : ByteRange} (h : a.allocations.lookup id = b.allocations.lookup id) :
    a.RangeInitialized id range ↔ b.RangeInitialized id range := by
  unfold RangeInitialized
  rw [h]

/-- **A write neither creates nor destroys initialization outside its own range.**
The `iff` rather than the forward direction alone: framing has to carry a *lack*
of initialization across a write too, or an `uninitializedRead` could be laundered
by writing somewhere else. -/
theorem rangeInitialized_write_iff_of_disjoint (state : MemoryState) {id : AllocId}
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {range : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint range) :
    (state.write id start bytes initializes).RangeInitialized id range ↔
      state.RangeInitialized id range := by
  unfold RangeInitialized
  cases hfound : state.allocations.lookup id with
  | none => rw [write_of_missing state _ _ _ hfound, hfound]
  | some record =>
    rw [lookup_write_self state start bytes initializes hfound]
    exact ByteStore.initialized_write_iff_of_disjoint record.bytes hd

/-- Inside the range it wrote, a write determines the cell: byte and
initialization both come from the run just prepended. -/
theorem cellAt?_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).cellAt? id offset =
      (bytes[offset - start]?).map (·, initializes) := by
  unfold cellAt?
  rw [lookup_write_self state start bytes initializes hfound]
  simp only [Option.bind_some]
  exact ByteStore.cellAt?_write_of_covers record.bytes h

/-- The byte a write leaves inside its own range. -/
theorem byteAt?_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).byteAt? id offset = bytes[offset - start]? := by
  unfold byteAt?
  rw [lookup_write_self state start bytes initializes hfound]
  simp only [Option.bind_some]
  unfold ByteStore.byteAt?
  rw [ByteStore.cellAt?_write_of_covers record.bytes h]
  cases bytes[offset - start]? <;> simp

/-- An initializing write initializes each byte it covered. -/
theorem initializedAt_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes true).InitializedAt id offset := by
  unfold InitializedAt
  rw [cellAt?_write_of_covers state hfound h]
  cases hb : bytes[offset - start]? with
  | none =>
    rw [ByteRange.covers_def] at h
    exact absurd (List.getElem?_eq_none_iff.mp hb) (by simp at h ⊢; omega)
  | some b => simp

/-- **A write frames every cell it did not write**, in the same allocation or in
another: byte and initialization together, so a framing argument can carry a lack
of initialization across a write as well as its presence. -/
theorem cellAt?_write_of_not_covers (state : MemoryState) (id : AllocId) {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {other : AllocId} {offset : Nat}
    (h : other ≠ id ∨ ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).cellAt? other offset =
      state.cellAt? other offset := by
  unfold cellAt?
  cases h with
  | inl hne => rw [write_preserves_other_allocation state hne]
  | inr hout =>
    by_cases hid : other = id
    · subst hid
      cases hfound : state.allocations.lookup other with
      | none =>
        rw [write_of_missing state start bytes initializes hfound, hfound]
      | some record =>
        rw [lookup_write_self state start bytes initializes hfound]
        simp only [Option.bind_some]
        exact ByteStore.cellAt?_write_of_not_covers record.bytes hout
    · rw [write_preserves_other_allocation state hid]

/-- The initialization half of `cellAt?_write_of_not_covers`, in the shape a
padding argument uses. -/
theorem initializedAt_write_iff_of_not_covers (state : MemoryState) (id : AllocId)
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {other : AllocId} {offset : Nat}
    (h : other ≠ id ∨ ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).InitializedAt other offset ↔
      state.InitializedAt other offset := by
  unfold InitializedAt
  rw [cellAt?_write_of_not_covers state id h]

/--
**Writes to disjoint ranges commute.**

Stated as `AgreesOn` rather than as state equality: the byte store is a journal,
so the two orders leave different write histories, and no proof will make those
equal. `AgreesOn` compares cells, so it carries initialization as well as values
and a caller can conclude both `AgreesOn.byteAt?` and `AgreesOn.initializedAt`.
`ByteStore.cellAt?_write_comm` is where the content is, and this wrapper no longer
throws away half of what it proves.
-/
theorem write_comm (state : MemoryState) (id : AllocId) {a b : Nat}
    {bytesA bytesB : ByteSeq} {initA initB : Bool}
    (hd : (ByteRange.mk a bytesA.length).Disjoint (ByteRange.mk b bytesB.length)) :
    ((state.write id a bytesA initA).write id b bytesB initB).AgreesOn
      ((state.write id b bytesB initB).write id a bytesA initA) := by
  intro other offset
  by_cases hid : other = id
  · subst hid
    cases hfound : state.allocations.lookup other with
    | none =>
      rw [write_of_missing state a bytesA initA hfound,
        write_of_missing state b bytesB initB hfound,
        write_of_missing state a bytesA initA hfound]
    | some record =>
      rw [cellAt?_write_self _ b bytesB initB
            (lookup_write_self state a bytesA initA hfound),
        cellAt?_write_self _ a bytesA initA
            (lookup_write_self state b bytesB initB hfound)]
      exact ByteStore.cellAt?_write_comm record.bytes hd offset
  · unfold cellAt?
    rw [write_preserves_other_allocation _ hid, write_preserves_other_allocation _ hid,
      write_preserves_other_allocation _ hid, write_preserves_other_allocation _ hid]

/-- An initializing write initializes what it wrote, provided the allocation is
there. The state-level form of `ByteStore.initialized_write`. -/
theorem rangeInitialized_write (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) :
    (state.write id start bytes true).RangeInitialized id ⟨start, bytes.length⟩ := by
  unfold RangeInitialized write
  simp only [hfound, FiniteMap.lookup_insert_self]
  exact ByteStore.initialized_write record.bytes start bytes


end MemoryState

/--
One architectural fault that was raised.

`docs/MEMORY_MODEL.md` §8: "Architectural faults are modeled events/transitions."
A faulting substep that performs no memory access — a divide error between two
operand reads, say — produces no `MemoryEvent`, so without this record the fault
leaves no trace and a faulting execution is indistinguishable from a clean one.
That was true of an earlier transition, which took the fault as an argument and
dropped it on the branch where the faulting substep was not an access.

This is not the fault *model*. It records that a fault of a named class was
raised by a named context at a named substep; the ISA profile owns what each
class means, and `docs/SEMANTICS.md` owns how a fault reaches the program result.
-/
structure RaisedFault where
  /-- Which fault was raised. -/
  fault : FaultClassId
  /-- The context it was raised in. -/
  context : ContextId
  /-- The instruction or API that raised it. -/
  cause : EventCause
  /-- The index of the substep that did not complete. -/
  substep : Nat
deriving DecidableEq, Repr

/--
The whole machine state a transition threads.

The three ledgers are separate because they answer different questions and have
different laws: memory is checked, obligations are transferred, and violations
only ever grow. `events` is the trace the consistency model of M8 will read.
-/
structure MachineState where
  /-- What is allocated and what is initialized. -/
  memory : MemoryState
  /-- The obligations currently outstanding, by identity. -/
  obligations : FiniteMap ObligationId Obligation
  /-- The append-only violation ledger. -/
  violations : AuditViolationLedger
  /-- The memory events performed so far, most recent last.

  `ValidMemoryEvent`, not `MemoryEvent`: the trace cannot contain a malformed
  event, so "every event in the trace is well formed" holds by construction rather
  than by a check something could forget. An earlier trace held bare events beside
  a predicate nothing consulted, and every event the transition minted violated
  it. -/
  events : List ValidMemoryEvent
  /-- The supply that mints event identities. -/
  eventSupply : FreshSupply EventTag
  /-- The architectural faults raised so far, most recent last.

  Separate from `events` because a fault is not a memory event: it may touch no
  bytes, and `MemoryEvent` requires a location. Separate from `violations`
  because `docs/MEMORY_MODEL.md` §8 draws exactly that line — a fault is
  behaviour a specification may permit, a violation is behaviour
  `VerifiedProgram` proves never happens. -/
  faults : List RaisedFault

namespace MachineState

/-- The state a program starts in. -/
def initial (memory : MemoryState) : MachineState :=
  { memory := memory, obligations := .empty, violations := .empty
    events := [], eventSupply := .initial, faults := [] }

/-- `state.OutstandingObligations` are the identities still owed. -/
def outstanding (state : MachineState) : List ObligationId := state.obligations.domain

/--
Every event in the trace is well formed.

A projection, not a check. `docs/MEMORY_MODEL.md` §7.1's field requirements hold
of the whole trace because `ValidMemoryEvent` carries the proof, and the only
producer is `MemoryEvent.ofOutcome`.
-/
theorem events_wellFormed (state : MachineState) :
    ∀ valid ∈ state.events, valid.event.WellFormed :=
  fun valid _ => valid.wellFormed

end MachineState

end Grass.Memory
