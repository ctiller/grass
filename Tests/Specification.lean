import Grass.Core.Identifiers
import Grass.Specification.Boundary

/-!
# Neutral specification fixtures

These fixtures exercise decision 132 through only the public Core and
Specification interfaces.
-/

namespace Grass.Tests.Specification

open Grass.Specification

def scopeA : ScopeId := ⟨["A"]⟩
def scopeB : ScopeId := ⟨["B"]⟩

def keyA : PlatformRequirementKey := ⟨scopeA, "z"⟩
def keyB : PlatformRequirementKey := ⟨scopeB, "a"⟩

def requirementsA : RequirementSet := RequirementSet.ofList [keyA]
def requirementsB : RequirementSet := RequirementSet.ofList [keyB]

example : (scopeA : Grass.ScopeId) = ⟨["A"]⟩ := rfl

example : Grass.Specification.ScopeId.mk ["A"] = scopeA := rfl

example : Grass.Specification.ScopeId.path scopeA = ["A"] := rfl

example : ScopeId.root.Contains ((ScopeId.root.child "A").child "B") :=
  ScopeId.Contains.trans (ScopeId.contains_child ScopeId.root "A")
    (ScopeId.contains_child (ScopeId.root.child "A") "B")

example {left right : ScopeId} (leftRight : left.Contains right)
    (rightLeft : right.Contains left) : left = right :=
  ScopeId.Contains.antisymm leftRight rightLeft

example (key : Grass.RequirementKey) : key.id = key.id := rfl

example :
    RequirementSet.ofList [keyB, keyA, keyB] =
      RequirementSet.ofList [keyA, keyB] := by
  apply RequirementSet.ext
  intro key
  simp only [RequirementSet.demands_ofList, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · intro demanded
    cases demanded with
    | inl isB => exact .inr isB
    | inr demanded =>
        cases demanded with
        | inl isA => exact .inl isA
        | inr isB => exact .inr isB
  · intro demanded
    cases demanded with
    | inl isA => exact .inr (.inl isA)
    | inr isB => exact .inl isB

example :
    (RequirementSet.ofList [keyB, keyA, keyB]).toCanonicalList =
      [keyA, keyB] := by rfl

example (requirements : RequirementSet) :
    requirements.toCanonicalList.Nodup :=
  RequirementSet.toCanonicalList_nodup requirements

example : requirementsA.Demands keyA := by simp [requirementsA]

example : ¬ requirementsA.Demands keyB := by
  simp [requirementsA, keyA, keyB, scopeA, scopeB]

example : requirementsB.Demands keyB := by simp [requirementsB]

example : ¬ requirementsB.Demands keyA := by
  simp [requirementsB, keyA, keyB, scopeA, scopeB]

example : (requirementsA.union requirementsB).Demands keyA := by
  apply RequirementSet.demands_union requirementsA requirementsB keyA |>.2
  exact .inl (by simp [requirementsA])

example : (requirementsA.union requirementsB).Demands keyB := by
  apply RequirementSet.demands_union requirementsA requirementsB keyB |>.2
  exact .inr (by simp [requirementsB])

example : (requirementsA.union requirementsB).Covers requirementsA :=
  RequirementSet.union_covers_left requirementsA requirementsB

example : (requirementsA.union requirementsB).Covers requirementsB :=
  RequirementSet.union_covers_right requirementsA requirementsB

example (requirements : RequirementSet) :
    requirements.Covers (requirementsA.union requirementsB) ↔
      requirements.Covers requirementsA ∧ requirements.Covers requirementsB := by
  simp

example {left right : RequirementSet} (leftRight : left.Covers right)
    (rightLeft : right.Covers left) : left = right :=
  RequirementSet.Covers.antisymm leftRight rightLeft

example : requirementsA.union requirementsB =
    RequirementSet.ofList [keyA, keyB] := by
  apply RequirementSet.ext
  intro key
  simp [requirementsA, requirementsB]

example : requirementsA.union requirementsB =
    requirementsB.union requirementsA :=
  RequirementSet.union_comm requirementsA requirementsB

example :
    (requirementsA.union requirementsB).union RequirementSet.empty =
      requirementsA.union (requirementsB.union RequirementSet.empty) :=
  RequirementSet.union_assoc requirementsA requirementsB RequirementSet.empty

def boundary : DriverBoundary where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Unit
  Observation := Unit
  requirements := RequirementSet.empty

example : boundary.withRequirements boundary.requirements = boundary := by simp

example (first second : RequirementSet) :
    (boundary.withRequirements first).withRequirements second =
      boundary.withRequirements second := by simp

example : (boundary.demandAlso keyA).requirements.Demands keyA :=
  DriverBoundary.demandAlso_demands boundary keyA

example : (boundary.demandAlso keyA).demandAlso keyA =
    boundary.demandAlso keyA := by simp

example : (boundary.demandAlso keyA).demandAlso keyB =
    (boundary.demandAlso keyB).demandAlso keyA :=
  DriverBoundary.demandAlso_comm boundary keyA keyB

end Grass.Tests.Specification
