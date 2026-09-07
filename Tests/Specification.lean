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

def keyA : RequirementKey := ⟨scopeA, "z"⟩
def keyB : RequirementKey := ⟨scopeB, "a"⟩

example : (scopeA : Grass.ScopeId) = ⟨["A"]⟩ := rfl

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
