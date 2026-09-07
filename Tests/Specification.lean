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
      [keyA, keyB] := by native_decide

def boundary : DriverBoundary where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Unit
  Observation := Unit
  requirements := RequirementSet.empty

example : (boundary.demandAlso keyA).requirements.Demands keyA :=
  DriverBoundary.demandAlso_demands boundary keyA

example : (boundary.demandAlso keyA).demandAlso keyA =
    boundary.demandAlso keyA := by simp

example : (boundary.demandAlso keyA).demandAlso keyB =
    (boundary.demandAlso keyB).demandAlso keyA :=
  DriverBoundary.demandAlso_comm boundary keyA keyB

end Grass.Tests.Specification
