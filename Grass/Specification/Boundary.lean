import Grass.Specification.Scope
import Std.Data.TreeSet.Lemmas

/-!
# The driver boundary

`DriverBoundary` is deliberately limited to the stable vocabulary shared by a
process realization and lower implementation layers. Its requirements use an
extensional finite-set identity: insertion order and duplicate insertion are
not observable, while `toCanonicalList` supplies the unique ordered form used
by storage and serialization.
-/

namespace Grass.Specification

universe u

/-- A nominal requirement key: what a realization demands of its platform. -/
structure RequirementKey where
  /-- The Core-owned scope responsible for the requirement. -/
  scope : ScopeId
  /-- The requirement name within that scope. -/
  name : String
  deriving DecidableEq, Repr

namespace RequirementKey

private abbrev Rep := List String × String

private def toRep (key : RequirementKey) : Rep :=
  (key.scope.path, key.name)

private def ofRep (rep : Rep) : RequirementKey :=
  ⟨⟨rep.1⟩, rep.2⟩

private theorem toRep_injective : Function.Injective toRep := by
  intro left right equal
  have pathEqual : left.scope.path = right.scope.path := congrArg Prod.fst equal
  have nameEqual : left.name = right.name := congrArg Prod.snd equal
  cases left with
  | mk leftScope leftName =>
      cases right with
      | mk rightScope rightName =>
          cases leftScope
          cases rightScope
          cases pathEqual
          cases nameEqual
          rfl

@[simp] private theorem ofRep_toRep (key : RequirementKey) :
    ofRep (toRep key) = key := by
  cases key
  rfl

@[simp] private theorem toRep_ofRep (rep : Rep) :
    toRep (ofRep rep) = rep := by
  cases rep
  rfl

local instance : Ord (List String × String) := lexOrd

/-- The stable lexicographic order used by requirement serialization: scope
path first, then the name within that scope. -/
def CanonicalBefore (left right : RequirementKey) : Prop :=
  compare (toRep left) (toRep right) = Ordering.lt

end RequirementKey

local instance : Ord (List String × String) := lexOrd

private abbrev RequirementTree := Std.TreeSet RequirementKey.Rep

private def requirementTreeSetoid : Setoid RequirementTree where
  r := Std.TreeSet.Equiv
  iseqv := {
    refl := fun _ => Std.TreeSet.Equiv.rfl
    symm := fun relation => relation.symm
    trans := fun left right => left.trans right
  }

/-- A finite, membership-extensional family of platform requirements. -/
def RequirementSet : Type := Quotient requirementTreeSetoid

namespace RequirementSet

/-- Construct a requirement set from arbitrary keys, discarding duplicates and
normalizing insertion order. -/
def ofList (keys : List RequirementKey) : RequirementSet :=
  Quotient.mk requirementTreeSetoid
    (Std.TreeSet.ofList (keys.map RequirementKey.toRep))

/-- The empty requirement set. -/
def empty : RequirementSet := ofList []

/-- The unique ordered representation used for storage and serialization. -/
def toCanonicalList (requirements : RequirementSet) : List RequirementKey :=
  Quotient.lift
    (fun tree => tree.toList.map RequirementKey.ofRep)
    (fun _ _ equivalent => congrArg (List.map RequirementKey.ofRep)
      (Std.TreeSet.equiv_iff_toList_eq.mp equivalent))
    requirements

/-- Canonical serialization is strictly ordered by scope path and name. -/
theorem toCanonicalList_ordered (requirements : RequirementSet) :
    requirements.toCanonicalList.Pairwise RequirementKey.CanonicalBefore := by
  induction requirements using Quotient.inductionOn with
  | _ tree =>
      change (tree.toList.map RequirementKey.ofRep).Pairwise
        RequirementKey.CanonicalBefore
      rw [List.pairwise_map]
      simpa [RequirementKey.CanonicalBefore] using
        (Std.TreeSet.ordered_toList (t := tree))

/-- `key` is demanded by this set. -/
def Demands (requirements : RequirementSet) (key : RequirementKey) : Prop :=
  Quotient.lift
    (fun tree => RequirementKey.toRep key ∈ tree)
    (fun _ _ equivalent => propext
      ((Std.TreeSet.equiv_iff_forall_mem_iff.mp equivalent)
        (RequirementKey.toRep key)))
    requirements

@[simp] theorem demands_ofList (keys : List RequirementKey)
    (key : RequirementKey) :
    (ofList keys).Demands key ↔ key ∈ keys := by
  change RequirementKey.toRep key ∈
      Std.TreeSet.ofList (keys.map RequirementKey.toRep) ↔ key ∈ keys
  rw [Std.TreeSet.mem_ofList, List.contains_iff_mem, List.mem_map]
  constructor
  · intro found
    obtain ⟨candidate, member, equal⟩ := found
    have keyEqual := RequirementKey.toRep_injective equal
    simpa [keyEqual] using member
  · intro member
    exact ⟨key, member, rfl⟩

/-- The canonical serialization contains exactly the demanded keys. -/
theorem mem_toCanonicalList (requirements : RequirementSet)
    (key : RequirementKey) :
    key ∈ requirements.toCanonicalList ↔ requirements.Demands key := by
  induction requirements using Quotient.inductionOn with
  | _ tree =>
      change key ∈ tree.toList.map RequirementKey.ofRep ↔
        RequirementKey.toRep key ∈ tree
      rw [List.mem_map]
      constructor
      · intro found
        obtain ⟨rep, member, equal⟩ := found
        cases equal
        simpa using member
      · intro member
        exact ⟨RequirementKey.toRep key,
          (Std.TreeSet.mem_toList).2 member, by simp⟩

/-- Insert a requirement. Quotient equality makes repeated insertion
unobservable. -/
def insert (requirements : RequirementSet) (key : RequirementKey) :
    RequirementSet :=
  Quotient.lift
    (fun tree => Quotient.mk requirementTreeSetoid
      (tree.insert (RequirementKey.toRep key)))
    (fun _ _ equivalent => Quotient.sound
      (Std.TreeSet.Equiv.insert equivalent (RequirementKey.toRep key)))
    requirements

/-- Membership determines public requirement-set identity. -/
@[ext]
theorem ext {left right : RequirementSet}
    (equal : ∀ key, left.Demands key ↔ right.Demands key) : left = right := by
  induction left using Quotient.inductionOn with
  | _ leftTree =>
      induction right using Quotient.inductionOn with
      | _ rightTree =>
          apply Quotient.sound
          apply Std.TreeSet.Equiv.of_forall_mem_iff
          intro rep
          have memberEqual := equal (RequirementKey.ofRep rep)
          change (rep ∈ leftTree ↔ rep ∈ rightTree) at memberEqual
          exact memberEqual

/-- Canonical serialization is injective and therefore a complete public
representation of requirement-set identity. -/
theorem eq_iff_toCanonicalList_eq {left right : RequirementSet} :
    left = right ↔ left.toCanonicalList = right.toCanonicalList := by
  constructor
  · intro equal
    cases equal
    rfl
  · intro listsEqual
    apply ext
    intro key
    rw [← mem_toCanonicalList, ← mem_toCanonicalList, listsEqual]

instance : DecidableEq RequirementSet := fun left right =>
  if equal : left.toCanonicalList = right.toCanonicalList then
    isTrue (eq_iff_toCanonicalList_eq.mpr equal)
  else
    isFalse (fun setsEqual => equal (eq_iff_toCanonicalList_eq.mp setsEqual))

/-- One set demands everything another does. -/
def Covers (larger smaller : RequirementSet) : Prop :=
  ∀ key, smaller.Demands key → larger.Demands key

theorem Covers.refl (requirements : RequirementSet) :
    requirements.Covers requirements := fun _ demanded => demanded

theorem Covers.trans {a b c : RequirementSet}
    (outer : a.Covers b) (inner : b.Covers c) : a.Covers c :=
  fun key demanded => outer key (inner key demanded)

@[simp] theorem not_empty_demands (key : RequirementKey) :
    ¬ empty.Demands key := by
  change ¬ RequirementKey.toRep key ∈ (Std.TreeSet.empty : RequirementTree)
  simp

@[simp] theorem demands_insert (requirements : RequirementSet)
    (inserted candidate : RequirementKey) :
    (requirements.insert inserted).Demands candidate ↔
      candidate = inserted ∨ requirements.Demands candidate := by
  induction requirements using Quotient.inductionOn with
  | _ tree =>
      change RequirementKey.toRep candidate ∈
          tree.insert (RequirementKey.toRep inserted) ↔
        candidate = inserted ∨ RequirementKey.toRep candidate ∈ tree
      rw [Std.TreeSet.mem_insert]
      rw [Std.LawfulEqCmp.compare_eq_iff_eq]
      constructor
      · intro found
        cases found with
        | inl equal =>
            exact .inl (RequirementKey.toRep_injective equal).symm
        | inr prior => exact .inr prior
      · intro demanded
        cases demanded with
        | inl equal =>
            subst candidate
            exact .inl rfl
        | inr prior => exact .inr prior

/-- `RequirementSet.insert_covers` states that insertion preserves every prior
demand. -/
theorem insert_covers (requirements : RequirementSet) (key : RequirementKey) :
    (requirements.insert key).Covers requirements := by
  intro candidate demanded
  exact demands_insert requirements key candidate |>.2 (.inr demanded)

/-- Inserting an already demanded key is unobservable. -/
@[simp] theorem insert_idempotent (requirements : RequirementSet)
    (key : RequirementKey) :
    (requirements.insert key).insert key = requirements.insert key := by
  apply ext
  intro candidate
  simp only [demands_insert]
  constructor
  · intro demanded
    cases demanded with
    | inl equal => exact .inl equal
    | inr demanded =>
        cases demanded with
        | inl equal => exact .inl equal
        | inr prior => exact .inr prior
  · intro demanded
    cases demanded with
    | inl equal => exact .inl equal
    | inr prior => exact .inr (.inr prior)

/-- Insertion order is unobservable. -/
theorem insert_comm (requirements : RequirementSet) (left right : RequirementKey) :
    (requirements.insert left).insert right =
      (requirements.insert right).insert left := by
  apply ext
  intro candidate
  simp only [demands_insert]
  constructor
  · intro demanded
    cases demanded with
    | inl rightEqual => exact .inr (.inl rightEqual)
    | inr demanded =>
        cases demanded with
        | inl leftEqual => exact .inl leftEqual
        | inr prior => exact .inr (.inr prior)
  · intro demanded
    cases demanded with
    | inl leftEqual => exact .inr (.inl leftEqual)
    | inr demanded =>
        cases demanded with
        | inl rightEqual => exact .inl rightEqual
        | inr prior => exact .inr (.inr prior)

end RequirementSet

/-- The stable interface a driver realizes. -/
structure DriverBoundary : Type (u + 1) where
  ExternalEvent : Type u
  Demand : Type u
  Result : Demand → Type u
  Observation : Type u
  requirements : RequirementSet

namespace DriverBoundary

/-- Replace a boundary's requirement set, leaving its interface alone. -/
def withRequirements (boundary : DriverBoundary.{u})
    (requirements : RequirementSet) : DriverBoundary.{u} :=
  { boundary with requirements := requirements }

@[simp] theorem withRequirements_requirements (boundary : DriverBoundary.{u})
    (requirements : RequirementSet) :
    (boundary.withRequirements requirements).requirements = requirements := rfl

/-- Demand one additional platform capability without exposing insertion order
or duplicate insertion. -/
def demandAlso (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    DriverBoundary.{u} :=
  boundary.withRequirements (boundary.requirements.insert key)

theorem demandAlso_covers (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    (boundary.demandAlso key).requirements.Covers boundary.requirements :=
  RequirementSet.insert_covers boundary.requirements key

theorem demandAlso_demands (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    (boundary.demandAlso key).requirements.Demands key := by
  simp [demandAlso]

/-- Demanding the same key twice is exactly the same boundary. -/
@[simp] theorem demandAlso_idempotent (boundary : DriverBoundary.{u})
    (key : RequirementKey) :
    (boundary.demandAlso key).demandAlso key = boundary.demandAlso key := by
  change {boundary with requirements :=
      (boundary.requirements.insert key).insert key} =
    {boundary with requirements := boundary.requirements.insert key}
  rw [RequirementSet.insert_idempotent]

/-- The order in which independent keys are demanded is unobservable. -/
theorem demandAlso_comm (boundary : DriverBoundary.{u})
    (left right : RequirementKey) :
    (boundary.demandAlso left).demandAlso right =
      (boundary.demandAlso right).demandAlso left := by
  change {boundary with requirements :=
      (boundary.requirements.insert left).insert right} =
    {boundary with requirements :=
      (boundary.requirements.insert right).insert left}
  rw [RequirementSet.insert_comm]

end DriverBoundary

end Grass.Specification
