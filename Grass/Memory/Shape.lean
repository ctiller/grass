import Grass.Memory.State

/-!
# Aggregate footprints and the padding law

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4 requires that "typed shapes expand
soundly to byte facts for partial access, padding, and external writes", and
`docs/STDLIB.md` states the obligation the other way round: "Padding is never
silently treated as initialized semantic data."

This module is the byte-level half of that, and only that half.

## What this is not

It is not `StructLayout`. `docs/STDLIB.md` makes `StructLayout` a `Std.Owned`
facility — it chooses field order, widths, alignment, and padding policy, derives
offsets, and carries an ABI profile. None of that is here and none of it is the
memory layer's to decide.

What the memory layer owes is the other side of the interface: given *some*
aggregate's field ranges, what is true of the bytes. A `Footprint` is that and
nothing more — named disjoint sub-ranges inside an extent. A layout facility
produces one; this module says what follows.

## Padding is the whole point

A field write initializes the field. The question is what it does to the bytes
between fields, and the answer has to be "nothing", because the alternative is
that writing every field of a struct makes the struct read as fully initialized
when part of it was never written. That is the silent treatment `docs/STDLIB.md`
forbids, and it would let an `uninitializedRead` pass through a typed shape that
`Grass/Memory/Apply.lean`'s `denialOf` would have caught on the raw bytes.

`padding_uninitialized_after_writing_fields` is the theorem, and it is proved for
writing *any* list of the aggregate's fields, in any order, with any data — not
for one convenient schedule.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/-- One field's byte footprint, relative to the aggregate's base. -/
structure FieldFootprint where
  /-- The field's name. -/
  name : Name
  /-- Where its bytes sit, relative to the aggregate base. -/
  range : ByteRange
deriving DecidableEq, Repr

/--
An aggregate's byte footprint: where its fields sit, and how far it extends.

`extent` is not `fields.foldr`: `docs/ASSEMBLY_CONSTRUCTION.md` §3 has
`aggregateAligned : alignment ∣ size`, so trailing padding is real and the extent
is larger than the last field's end. Deriving it would erase exactly the padding
this module exists to reason about.
-/
structure Footprint where
  /-- The fields, in declaration order. -/
  fields : List FieldFootprint
  /-- The aggregate's whole extent, relative to its base. -/
  extent : ByteRange
deriving DecidableEq, Repr

namespace Footprint

/--
`f.WellFormed` holds when the footprint could describe a real aggregate.

The three conditions are `docs/ASSEMBLY_CONSTRUCTION.md` §3's `uniqueNames`,
`disjoint`, and `contained`, restated over byte ranges. A `StructLayout` carries
proofs of all three.

Only `fieldsDisjoint` is consumed here, by `cellAt?_writeField_of_other_field`.
The other two are carried because a footprint claiming to describe a real
aggregate should not be constructible without them: `namesUnique` is what makes
`field?` a function rather than a choice, and `fieldsContained` is what makes
`IsPadding`'s `extent` clause meaningful. Neither is load-bearing for the padding
theorem, and the padding theorem deliberately does not require `WellFormed` at
all.
-/
structure WellFormed (f : Footprint) : Prop where
  /-- No two fields share a name. -/
  namesUnique : f.fields.Pairwise (fun left right => left.name ≠ right.name)
  /-- No two fields share a byte. -/
  fieldsDisjoint : f.fields.Pairwise (fun left right => left.range.Disjoint right.range)
  /-- Every field lies inside the aggregate. -/
  fieldsContained : ∀ field ∈ f.fields, f.extent.Contains field.range

/--
Two distinct fields of a well-formed footprint are disjoint.

`List.Pairwise` relates each element to those *after* it, so getting the fact for
an arbitrary pair takes an induction. Disjointness is symmetric, which is what
makes the order not matter.
-/
theorem disjoint_of_pairwise :
    ∀ {fields : List FieldFootprint},
      fields.Pairwise (fun left right => left.range.Disjoint right.range) →
      ∀ {a b : FieldFootprint}, a ∈ fields → b ∈ fields → a ≠ b →
        a.range.Disjoint b.range
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | head :: rest, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact (hp.1 a ha').symm
      · exact disjoint_of_pairwise hp.2 ha' hb' hne

/-- Look a field up by name. -/
def field? (f : Footprint) (name : Name) : Option FieldFootprint :=
  f.fields.find? (fun field => field.name = name)

theorem mem_of_field? {f : Footprint} {name : Name} {field : FieldFootprint}
    (h : f.field? name = some field) : field ∈ f.fields :=
  List.mem_of_find?_eq_some h

/--
`f.IsPadding offset` holds when the aggregate covers `offset` and no field does.

Stated as "no field covers it" rather than as a computed complement range,
because padding need not be contiguous: `docs/ASSEMBLY_CONSTRUCTION.md` §3 admits
padding between fields as well as after the last one.
-/
def IsPadding (f : Footprint) (offset : Nat) : Prop :=
  f.extent.Covers offset ∧ ∀ field ∈ f.fields, ¬ field.range.Covers offset

instance (f : Footprint) (offset : Nat) : Decidable (f.IsPadding offset) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Padding is disjoint from every field, by definition. The direction the
framing proofs use. -/
theorem not_covers_of_isPadding {f : Footprint} {offset : Nat} {field : FieldFootprint}
    (hpad : f.IsPadding offset) (hmem : field ∈ f.fields) :
    ¬ field.range.Covers offset := hpad.2 field hmem

end Footprint

namespace MemoryState

/--
Write one field of an aggregate based at `base` in allocation `id`.

The write is confined to the field's own range: `bytes` longer than the field is
truncated, and `bytes` shorter initializes only what it covered, which is
`docs/MEMORY_MODEL.md` §4's "a write initializes only the bytes it actually
completes" applied to a field rather than an access.

`initializes := true`, because a field write is a semantic store. A profile whose
store does not credit initialization goes through `MemoryState.write` directly;
this is the typed-shape path, and a typed shape that wrote its field without
initializing it would be reporting a value it did not stand behind.
-/
def writeField (state : MemoryState) (id : AllocId) (base : Nat)
    (field : FieldFootprint) (bytes : ByteSeq) : MemoryState :=
  state.write id (base + field.range.start) (bytes.take field.range.size) true

/-- Write a list of fields in order. Later writes win where they overlap, which
for a well-formed footprint is nowhere. -/
def writeFields (state : MemoryState) (id : AllocId) (base : Nat) :
    List (FieldFootprint × ByteSeq) → MemoryState
  | [] => state
  | (field, bytes) :: rest => (state.writeField id base field bytes).writeFields id base rest

/-! ## The laws -/

/-- The byte range a field write actually touches, relative to the allocation. -/
theorem writeField_range (state : MemoryState) (id : AllocId) (base : Nat)
    (field : FieldFootprint) (bytes : ByteSeq) :
    state.writeField id base field bytes =
      state.write id (base + field.range.start) (bytes.take field.range.size) true := rfl

/--
A field write touches no offset outside that field.

The one arithmetic step in this module: an offset is inside the written run
exactly when its aggregate-relative position is inside the field's range, so
every framing fact about fields reduces to a framing fact about ranges.
-/
theorem writeField_covers_iff (base : Nat) (field : FieldFootprint) (bytes : ByteSeq)
    (offset : Nat) :
    (ByteRange.mk (base + field.range.start) (bytes.take field.range.size).length).Covers
        (base + offset) →
      field.range.Covers offset := by
  intro h
  simp only [ByteRange.covers_def, List.length_take] at h ⊢
  omega

/-- **A field write frames every offset outside that field**, byte and
initialization together. -/
theorem cellAt?_writeField_of_not_covers (state : MemoryState) (id : AllocId) (base : Nat)
    {field : FieldFootprint} {bytes : ByteSeq} {offset : Nat}
    (h : ¬ field.range.Covers offset) :
    (state.writeField id base field bytes).cellAt? id (base + offset) =
      state.cellAt? id (base + offset) :=
  cellAt?_write_of_not_covers state id
    (Or.inr fun hin => h (writeField_covers_iff base field bytes offset hin))

/-- **A field write frames every other field of a well-formed footprint.**

Disjointness is derived from `WellFormed.fieldsDisjoint` rather than taken as a
hypothesis: a caller holding a well-formed footprint should not have to supply
again what well-formedness already says. -/
theorem cellAt?_writeField_of_other_field {f : Footprint} (hwf : f.WellFormed)
    (state : MemoryState) (id : AllocId) (base : Nat) {written other : FieldFootprint}
    {bytes : ByteSeq} {offset : Nat} (hw : written ∈ f.fields) (ho : other ∈ f.fields)
    (hne : written ≠ other) (hcov : other.range.Covers offset) :
    (state.writeField id base written bytes).cellAt? id (base + offset) =
      state.cellAt? id (base + offset) := by
  have hd : written.range.Disjoint other.range :=
    Footprint.disjoint_of_pairwise hwf.fieldsDisjoint hw ho hne
  exact cellAt?_writeField_of_not_covers state id base (fun hin => hd.not_covers hin hcov)

/-- **A field write leaves padding exactly as it was.** The single-write case of
the theorem below, and the only place the argument does any work. -/
theorem cellAt?_writeField_of_padding {f : Footprint} (state : MemoryState) (id : AllocId)
    (base : Nat) {field : FieldFootprint} {bytes : ByteSeq} {offset : Nat}
    (hmem : field ∈ f.fields) (hpad : f.IsPadding offset) :
    (state.writeField id base field bytes).cellAt? id (base + offset) =
      state.cellAt? id (base + offset) :=
  cellAt?_writeField_of_not_covers state id base (Footprint.not_covers_of_isPadding hpad hmem)

/--
**Writing any set of an aggregate's fields leaves its padding exactly as it was.**

`docs/STDLIB.md`: "Padding is never silently treated as initialized semantic
data." Proved for any list of the aggregate's fields, in any order, with any
data, so it is not a fact about one convenient write schedule.
-/
theorem cellAt?_writeFields_of_padding {f : Footprint} (id : AllocId) (base : Nat)
    {offset : Nat} (hpad : f.IsPadding offset) :
    ∀ (writes : List (FieldFootprint × ByteSeq)) (state : MemoryState),
      (∀ write ∈ writes, write.1 ∈ f.fields) →
      (state.writeFields id base writes).cellAt? id (base + offset) =
        state.cellAt? id (base + offset)
  | [], _, _ => rfl
  | (field, bytes) :: rest, state, hall => by
    rw [MemoryState.writeFields,
      cellAt?_writeFields_of_padding id base hpad rest _
        (fun w hw => hall w (List.mem_cons_of_mem _ hw)),
      cellAt?_writeField_of_padding state id base (hall (field, bytes) List.mem_cons_self) hpad]

/--
**Padding stays uninitialized however many fields are written.**

The form the corpus obligation actually takes: an aggregate whose padding was
never written does not read as initialized just because every field was. Without
this, a typed shape could launder an `uninitializedRead` that
`Grass/Memory/Apply.lean`'s `denialOf` would have caught on the raw bytes.
-/
theorem padding_uninitialized_after_writing_fields {f : Footprint} (state : MemoryState)
    (id : AllocId) (base : Nat) {offset : Nat} (hpad : f.IsPadding offset)
    (writes : List (FieldFootprint × ByteSeq))
    (hall : ∀ write ∈ writes, write.1 ∈ f.fields)
    (hbefore : ¬ state.InitializedAt id (base + offset)) :
    ¬ (state.writeFields id base writes).InitializedAt id (base + offset) := by
  unfold MemoryState.InitializedAt at hbefore ⊢
  rw [cellAt?_writeFields_of_padding id base hpad writes state hall]
  exact hbefore

/-! ### The other side of the partition

Everything above says what a field write leaves alone. These say what it does, and
the pair is what makes the padding law a partition rather than a one-sided claim:
after writing a field, the field's own bytes read back and count as initialized,
while the padding does neither.
-/

/--
**A field reads back what was written to it**, byte for byte.

`docs/STDLIB.md`'s serialization law — "writing a represented value then reading
at the same layout returns it exactly" — at the byte level, which is the level
the memory layer owns. Stated pointwise rather than as a sequence: assembling the
bytes into a represented value is the layout facility's job, and this is the fact
it would assemble from.
-/
theorem byteAt?_writeField (state : MemoryState) {id : AllocId} (base : Nat)
    {field : FieldFootprint} {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {i : Nat}
    (hi : i < bytes.length) (hfit : i < field.range.size) :
    (state.writeField id base field bytes).byteAt? id (base + field.range.start + i) =
      bytes[i]? := by
  rw [writeField_range, byteAt?_write_of_covers state hfound
    (by simp only [ByteRange.covers_def, List.length_take]; omega)]
  have : base + field.range.start + i - (base + field.range.start) = i := by omega
  rw [this, List.getElem?_take]
  simp only [if_pos hfit]

/-- **A field write initializes the bytes it wrote**, and only those: compare
`padding_uninitialized_after_writing_fields`, which is the same write seen from
the padding. -/
theorem initializedAt_writeField (state : MemoryState) {id : AllocId} (base : Nat)
    {field : FieldFootprint} {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {i : Nat}
    (hi : i < bytes.length) (hfit : i < field.range.size) :
    (state.writeField id base field bytes).InitializedAt id (base + field.range.start + i) := by
  rw [writeField_range]
  exact initializedAt_write_of_covers state hfound
    (by simp only [ByteRange.covers_def, List.length_take]; omega)

end MemoryState

end Grass.Memory
