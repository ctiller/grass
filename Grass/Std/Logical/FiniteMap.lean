/-!
# Finite maps

A finite partial map with decidable keys, together with the framing lemmas the
memory and obligation layers consume: a lookup is unaffected by an update at a
distinct key.

Those framing lemmas are the point of the module. `docs/MEMORY_MODEL.md` §3
makes the loan map the authoritative representation of borrowing, and
`applyAccess` frames a per-allocation byte store across disjoint ranges, so
almost every proof in the memory layer reduces to "this update did not touch the
key I am reading".

Equality is extensional, per `docs/STDLIB.md` §1: two maps are `Equiv` when they
agree at every key. Representations are deliberately not normalized, so
propositional equality of the underlying entry list is finer than `Equiv` and is
never the right relation to use.

**Custody, settled.** This module was written under `c-mem`'s temporary custody
per `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2. That custody ended on 2026-09-07:
offered as `c-mem:47`, accepted as `c-stdlib:19`, and `Grass/Std/Logical/**` is
the `Std.Logical` owner's exclusive claim from `c-stdlib:21`. `coord1:32` asked
that the marker be replaced on acceptance rather than stripped before the offer,
and this is that replacement, late.

The note also predicted the wrong mechanism: it expected the transfer to happen
"by rename and re-export", and no rename was needed, because the module was
already sited where its owner wanted it. What did come with the handoff is
recorded in `c-mem:47` — the framing lemmas on `agent/c-mem/provider-cleanup`
reach this module through that branch's own review rather than through the
transfer.

Unchanged by any of that: the disjoint union and its split/join laws are
deliberately absent until a consumer needs them.
-/

namespace Grass.Std.Logical

universe u v

variable {K : Type u} {V : Type v}

/-!
## Association-list primitives

These operate on the raw entry list so that induction is available. The bundled
`FiniteMap` operations below are thin wrappers.
-/

/-- The value associated with `key`, taking the earliest matching entry. -/
def findValue [DecidableEq K] (entries : List (K × V)) (key : K) : Option V :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = key then some v else findValue rest key

/-- Remove every entry for `key`. -/
def eraseKey [DecidableEq K] (entries : List (K × V)) (key : K) : List (K × V) :=
  match entries with
  | [] => []
  | (k, v) :: rest => if k = key then eraseKey rest key else (k, v) :: eraseKey rest key

@[simp] theorem findValue_nil [DecidableEq K] (key : K) :
    findValue ([] : List (K × V)) key = none := rfl

@[simp] theorem findValue_cons_self [DecidableEq K] (key : K) (value : V)
    (rest : List (K × V)) : findValue ((key, value) :: rest) key = some value := by
  simp [findValue]

theorem findValue_cons_ne [DecidableEq K] {k key : K} (h : k ≠ key) (value : V)
    (rest : List (K × V)) : findValue ((k, value) :: rest) key = findValue rest key := by
  simp [findValue, h]

@[simp] theorem eraseKey_nil [DecidableEq K] (key : K) :
    eraseKey ([] : List (K × V)) key = [] := rfl

/-- Erasing removes the key outright: no shadowed entry survives. -/
@[simp] theorem findValue_eraseKey_self [DecidableEq K] (entries : List (K × V))
    (key : K) : findValue (eraseKey entries key) key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases h : k = key <;> simp [eraseKey, findValue, h, ih]

/-- Erasing frames: a lookup at a distinct key is untouched. -/
theorem findValue_eraseKey_ne [DecidableEq K] {key other : K} (h : other ≠ key)
    (entries : List (K × V)) :
    findValue (eraseKey entries key) other = findValue entries other := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = key
    · subst hk
      simp [eraseKey, findValue, Ne.symm h, ih]
    · by_cases ho : k = other <;> simp [eraseKey, findValue, hk, ho, h, ih]

/-!
## The bundled map
-/

/--
A finite partial map from `K` to `V`.

The entry list may contain shadowed duplicates; `findValue` takes the earliest,
and `insert` erases before consing, so maps built from `empty` by `insert` and
`erase` carry no shadowed entries. No proof depends on that, which is why the
invariant is not a field.
-/
structure FiniteMap (K : Type u) (V : Type v) where
  /-- The underlying entries, earliest match winning. -/
  entries : List (K × V)

namespace FiniteMap

variable [DecidableEq K]

/-- The map with no bindings. -/
def empty : FiniteMap K V := ⟨[]⟩

instance : EmptyCollection (FiniteMap K V) := ⟨empty⟩

omit [DecidableEq K] in
/--
`∅` and `FiniteMap.empty` are the same map.

Stated as `simp` because the `EmptyCollection` instance above makes the notation
*typecheck* without making it *rewrite*: `simp` does not see through the instance
projection, so a goal written with `∅` reaches neither `lookup_empty` nor
`isEmpty_empty`, which are the two laws a consumer wants the moment they write it.

Oriented towards `empty` because that is what this module's laws are stated
about. `Grass/Std/Logical/Bag.lean` orients the same bridge towards `0` instead,
for the same reason in its own module: the direction follows the theorems, not
the notation.
-/
@[simp] theorem emptyCollection_eq_empty : (∅ : FiniteMap K V) = empty := rfl

/-- The value bound to `key`, if any. -/
def lookup (m : FiniteMap K V) (key : K) : Option V := findValue m.entries key

/-- Bind `key` to `value`, replacing any existing binding. -/
def insert (m : FiniteMap K V) (key : K) (value : V) : FiniteMap K V :=
  ⟨(key, value) :: eraseKey m.entries key⟩

/-- Remove any binding for `key`. -/
def erase (m : FiniteMap K V) (key : K) : FiniteMap K V := ⟨eraseKey m.entries key⟩

/--
The keys this map binds, as they appear in the entry list.

**`domain.length` is not a count of bindings.** The entry list may contain
shadowed duplicates, and `domain` reports them: `⟨[(1,10),(1,20)]⟩` has domain
`[1,1]`. `docs/MEMORY_MODEL.md` §3 says counts are derived caches of the
authoritative map, so a derived count taken as `domain.length` would be wrong on
such a map. Use `Binds`, or `domain` only up to membership, until the
`Std.Logical` owner supplies a deduplicating count with its own law.
-/
def domain (m : FiniteMap K V) : List K := m.entries.map Prod.fst

/-- `m.Binds key` holds when `m` has a binding for `key`. -/
def Binds (m : FiniteMap K V) (key : K) : Prop := (m.lookup key).isSome

/-- `m.IsEmpty` holds when `m` binds nothing. -/
def IsEmpty (m : FiniteMap K V) : Prop := ∀ key, m.lookup key = none

/-- Extensional agreement. This, not equality of `entries`, is map equality. -/
def Equiv (m n : FiniteMap K V) : Prop := ∀ key, m.lookup key = n.lookup key

@[simp] theorem lookup_empty (key : K) : (empty : FiniteMap K V).lookup key = none := rfl

/-- A successful lookup identifies an entry in the map's finite presentation. -/
theorem mem_of_lookup {m : FiniteMap K V} {key : K} {value : V}
    (found : m.lookup key = some value) : (key, value) ∈ m.entries := by
  cases m with
  | mk entries =>
    induction entries with
    | nil => simp [lookup, findValue] at found
    | cons entry rest ih =>
      rcases entry with ⟨headKey, headValue⟩
      change (if headKey = key then some headValue else findValue rest key) = some value at found
      split at found
      · next same =>
        cases found
        subst headKey
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih found)

@[simp] theorem lookup_insert_self (m : FiniteMap K V) (key : K) (value : V) :
    (m.insert key value).lookup key = some value := by
  simp [lookup, insert]

/-- Insertion frames: a lookup at a distinct key is untouched. -/
theorem lookup_insert_ne (m : FiniteMap K V) {key other : K} (h : other ≠ key)
    (value : V) : (m.insert key value).lookup other = m.lookup other := by
  simp [lookup, insert, findValue_cons_ne (Ne.symm h), findValue_eraseKey_ne h]

@[simp] theorem lookup_erase_self (m : FiniteMap K V) (key : K) :
    (m.erase key).lookup key = none := by
  simp [lookup, erase]

/-- Erasure frames: a lookup at a distinct key is untouched. -/
theorem lookup_erase_ne (m : FiniteMap K V) {key other : K} (h : other ≠ key) :
    (m.erase key).lookup other = m.lookup other := by
  simp [lookup, erase, findValue_eraseKey_ne h]

/-- The combined framing law, in the shape memory proofs actually apply it. -/
@[simp] theorem lookup_insert (m : FiniteMap K V) (key other : K) (value : V) :
    (m.insert key value).lookup other =
      if other = key then some value else m.lookup other := by
  by_cases h : other = key
  · subst h; simp
  · simp [lookup_insert_ne m h, h]

@[simp] theorem lookup_erase (m : FiniteMap K V) (key other : K) :
    (m.erase key).lookup other = if other = key then none else m.lookup other := by
  by_cases h : other = key
  · subst h; simp
  · simp [lookup_erase_ne m h, h]

theorem mem_domain_iff_binds (m : FiniteMap K V) (key : K) :
    key ∈ m.domain ↔ m.Binds key := by
  obtain ⟨entries⟩ := m
  induction entries with
  | nil => simp [domain, Binds, lookup]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases h : k = key
    · subst h; simp [domain, Binds, lookup]
    · simpa [domain, Binds, lookup, findValue_cons_ne h, h, Ne.symm h] using ih

@[simp] theorem isEmpty_empty : (empty : FiniteMap K V).IsEmpty := fun _ => rfl

/-- A map that binds nothing has an empty domain. -/
theorem domain_eq_nil_of_isEmpty {m : FiniteMap K V} (h : m.IsEmpty) : m.domain = [] := by
  cases hd : m.domain with
  | nil => rfl
  | cons key rest =>
    exact absurd ((mem_domain_iff_binds m key).mp (hd ▸ List.mem_cons_self ..))
      (by simp [Binds, h key])

theorem Equiv.refl (m : FiniteMap K V) : m.Equiv m := fun _ => rfl

theorem Equiv.symm {m n : FiniteMap K V} (h : m.Equiv n) : n.Equiv m := fun key => (h key).symm

theorem Equiv.trans {m n p : FiniteMap K V} (h₁ : m.Equiv n) (h₂ : n.Equiv p) : m.Equiv p :=
  fun key => (h₁ key).trans (h₂ key)

/-- `insert` respects extensional equality, so it is usable under `Equiv`. -/
theorem Equiv.insert {m n : FiniteMap K V} (h : m.Equiv n) (key : K) (value : V) :
    (m.insert key value).Equiv (n.insert key value) := by
  intro other
  simp [lookup_insert, h other]

/-- `erase` respects extensional equality. -/
theorem Equiv.erase {m n : FiniteMap K V} (h : m.Equiv n) (key : K) :
    (m.erase key).Equiv (n.erase key) := by
  intro other
  simp [lookup_erase, h other]

/--
`IsEmpty` transports along `Equiv`.

This is the transport that matters most. `docs/MEMORY_MODEL.md` §3 restores
exclusive authority when the loan map is empty, so emptiness is the loan layer's
central predicate, and `Equiv.isEmpty` is what stops it depending on which
extensionally equal representation the map happens to have.
-/
theorem Equiv.isEmpty {m n : FiniteMap K V} (h : m.Equiv n) (hm : m.IsEmpty) :
    n.IsEmpty := fun key => (h key).symm.trans (hm key)

/-- `Binds` transports along `Equiv`. -/
theorem Equiv.binds {m n : FiniteMap K V} (h : m.Equiv n) {key : K} (hb : m.Binds key) :
    n.Binds key := by
  rw [Binds, ← h key]; exact hb

/-- Membership in the domain transports along `Equiv`, even though the domain
list itself does not: see the caveat on `domain`. -/
theorem Equiv.mem_domain {m n : FiniteMap K V} (h : m.Equiv n) {key : K}
    (hd : key ∈ m.domain) : key ∈ n.domain :=
  (mem_domain_iff_binds n key).mpr (h.binds ((mem_domain_iff_binds m key).mp hd))

/-- A map with no entries binds nothing. The converse needs `K` to be searchable
and is not available at this generality. -/
theorem isEmpty_of_entries_eq_nil {m : FiniteMap K V} (h : m.entries = []) : m.IsEmpty :=
  fun _ => by simp [lookup, h]

end FiniteMap

end Grass.Std.Logical
