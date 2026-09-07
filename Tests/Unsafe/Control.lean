import Grass.Unsafe.Control

/-!
# Imported control-flow evidence fixtures

Fixtures pin exact flattened demand indices and reject every incomplete or
ambiguous direct/indirect target-evidence shape.
-/

namespace Grass.Tests.Unsafe.Control

open Grass.Unsafe

inductive Instruction where
  | plain
  | jump (target : Nat)
  | branch (site : String)
deriving Repr, DecidableEq

def model : ControlModel Instruction Nat String where
  project
    | .plain => []
    | .jump target => [.direct target]
    | .branch site => [.indirect site]

def raw : RawHierarchy Instruction := .append
  (.leaf [.plain, .jump 1])
  (.leaf [.branch "dispatch"])

example : raw.controlDemands model = [
    ⟨1, .direct 1⟩,
    ⟨2, .indirect "dispatch"⟩
  ] := by native_decide

def good : ControlEvidence raw model where
  admittedTargets := [1, 2]
  indirect := [⟨"dispatch", [1, 2]⟩]

example : good.WellFormed := by native_decide
example : good.unresolvedDirect = [] :=
  ControlEvidence.unresolvedDirect_eq_nil good (by native_decide)

def unknownDirect : ControlEvidence raw model where
  admittedTargets := [2]
  indirect := [⟨"dispatch", [2]⟩]

example : ¬ unknownDirect.WellFormed := by native_decide
example : unknownDirect.unresolvedDirect = [⟨1, .direct 1⟩] := by native_decide

def missingIndirect : ControlEvidence raw model where
  admittedTargets := [1, 2]
  indirect := []

example : ¬ missingIndirect.WellFormed := by native_decide

def emptyIndirect : ControlEvidence raw model where
  admittedTargets := [1, 2]
  indirect := [⟨"dispatch", []⟩]

example : ¬ emptyIndirect.WellFormed := by native_decide

def unknownIndirect : ControlEvidence raw model where
  admittedTargets := [1, 2]
  indirect := [⟨"dispatch", [3]⟩]

example : ¬ unknownIndirect.WellFormed := by native_decide

def duplicateSelection : ControlEvidence raw model where
  admittedTargets := [1, 2]
  indirect := [⟨"dispatch", [1]⟩, ⟨"dispatch", [2]⟩]

example : ¬ duplicateSelection.WellFormed := by native_decide

def duplicateSiteRaw : RawHierarchy Instruction :=
  .leaf [.branch "dispatch", .branch "dispatch"]

def duplicateSite : ControlEvidence duplicateSiteRaw model where
  admittedTargets := [1]
  indirect := [⟨"dispatch", [1]⟩, ⟨"dispatch", [1]⟩]

example : ¬ duplicateSite.WellFormed := by native_decide

def closed : ClosedImport model where
  raw := raw
  evidence := good
  closed := by native_decide

end Grass.Tests.Unsafe.Control
