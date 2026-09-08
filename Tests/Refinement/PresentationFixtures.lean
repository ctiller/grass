import Grass.Refinement.Presentation

namespace Grass.Tests.Refinement.PresentationFixtures

open Grass.Refinement

inductive Role
  | root
deriving DecidableEq

inductive NoDemand

def noDemands : DemandFamily where
  Key := NoDemand
  keys := []
  complete := fun key => nomatch key
  unique := List.nodup_nil
  identity := fun key => nomatch key
  identityInjective := fun key => nomatch key
  kind := fun key => nomatch key
  statement := fun key => nomatch key

def protocol : SpecProcess where
  Input := Unit
  AuditEvent := Unit
  Observation := Unit
  admits := fun _ => True
  observationProjection := .identity Unit
  accepts := fun _ _ => True
  requirements := noDemands

/-- The Refinement alias accepts the exact Process structural literal. -/
def network : ProcessPresentationNetwork where
  RoleSchema := Role
  schemas := [.root]
  schemasComplete := by intro schema; cases schema; simp
  schemasDistinct := by simp
  protocol := fun _ => protocol
  Instance := fun _ => Unit
  instanceOf := fun _ _ => ⟨(), trivial⟩

example : network.roleCount = 1 := rfl

/-- Refinement did not duplicate or wrap the Process-owned network. -/
example : ProcessPresentationNetwork =
    Grass.Process.StructuralProcessNetwork SpecProcess
      (fun selected => { input : selected.Input // selected.admits input }) := rfl

def rejectingProtocol : SpecProcess where
  Input := Unit
  AuditEvent := Unit
  Observation := Unit
  admits := fun _ => False
  observationProjection := .identity Unit
  accepts := fun _ _ => False
  requirements := noDemands

/-- A protocol rejecting every input has no possible protocol instance. -/
theorem rejectingProtocol_has_no_instance :
    ¬ Nonempty { input : rejectingProtocol.Input // rejectingProtocol.admits input } := by
  rintro ⟨selected⟩
  exact selected.property

end Grass.Tests.Refinement.PresentationFixtures
