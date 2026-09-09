import Grass.Console.CapturedProjection
import Grass.Specification.Boundary

/-! Computable target selection for the exact captured specification.
Construction data does not assert provider adequacy or certify executable code. -/

namespace Grass

inductive Target where
  | win10X64
deriving DecidableEq, Repr

/-- Authored status selection is data; constructing it needs no outcome equality. -/
inductive TargetOutcomeProjection (Outcome Status : Type) where
  | successOrFailure (success : Outcome) (successCode failureCode : Status)

namespace TargetOutcomeProjection
variable {Outcome Status : Type}

/-- Equality is used only in the semantic interpretation, never to build payloads. -/
noncomputable def encode (policy : TargetOutcomeProjection Outcome Status)
    (result : Outcome) : Status := by
  classical
  exact match policy with
    | .successOrFailure success successCode failureCode =>
      if result = success then successCode else failureCode

theorem encode_success (success : Outcome) (successCode failureCode : Status) :
    (successOrFailure success successCode failureCode).encode success = successCode := by
  simp [encode]

theorem encode_failure (success result : Outcome) (successCode failureCode : Status)
    (different : result ≠ success) :
    (successOrFailure success successCode failureCode).encode result = failureCode := by
  simp [encode, different]
end TargetOutcomeProjection

inductive TargetNewline where
  | crlf
deriving DecidableEq, Repr

inductive TargetEncoding where
  | utf8
deriving DecidableEq, Repr

/-- The supported target constructor retains a view of this exact root. -/
inductive TargetProjection {R : Type} [Resource.ResourceModel R] {resources : R}
    (spec : SpecProcess resources) : Target → Type 1 where
  | win10ConsoleText
      (newline : TargetNewline) (encoding : TargetEncoding)
      (outcome : TargetOutcomeProjection spec.Outcome UInt32)
      (view : Console.ContractView spec.contract := by apply Console.writeLineView) :
      TargetProjection spec .win10X64

namespace TargetProjection
variable {R : Type} [Resource.ResourceModel R] {resources : R}
    {spec : SpecProcess resources}

@[instance_reducible] def view (projection : TargetProjection spec .win10X64) :
    Console.ContractView spec.contract :=
  match projection with | .win10ConsoleText _ _ _ view => view

def outcome (projection : TargetProjection spec .win10X64) :
    TargetOutcomeProjection spec.Outcome UInt32 :=
  match projection with | .win10ConsoleText _ _ outcome _ => outcome

def rendering (projection : TargetProjection spec .win10X64) : Specification.LineRendering :=
  match projection with
  | .win10ConsoleText .crlf .utf8 _ _ => ⟨Specification.TextEncoding.utf8, Specification.crlf⟩

def encodeLine (projection : TargetProjection spec .win10X64)
    (line : Specification.TextLine) : Std.Logical.ByteArray :=
  projection.rendering.bytes line

/-- Semantic projection is derived from the stored view and selection data. -/
noncomputable def captured (projection : TargetProjection spec .win10X64) :
    Console.CapturedTargetProjection spec UInt32 :=
  ⟨projection.view, ⟨projection.rendering, projection.outcome.encode⟩⟩

theorem payload_exact (projection : TargetProjection spec .win10X64) :
    projection.captured.target.payload = projection.encodeLine projection.view.request.line := rfl

theorem encodeLine_exact (projection : TargetProjection spec .win10X64)
    (line : Specification.TextLine) :
    projection.encodeLine line = Std.Logical.Text.utf8 (line.text ++ Specification.crlf) := by
  cases projection with
  | win10ConsoleText newline encoding outcome view => cases newline; cases encoding; rfl

end TargetProjection

namespace Console
/-- A capability view of the selected captured console contract. This is not
a replacement grammar for its typed semantic transitions. -/
structure DriverBoundaryView {R : Type} [Resource.ResourceModel R] {resources : R}
    (spec : SpecProcess resources) where
  view : ContractView spec.contract

def writeLineCapability : Specification.RequirementKey :=
  ⟨⟨["Grass", "Console"]⟩, "writeLine"⟩

def DriverBoundaryView.requirements {R : Type} [Resource.ResourceModel R] {resources : R}
    {spec : SpecProcess resources} (_boundary : DriverBoundaryView spec) :
    Specification.RequirementSet := ⟨[writeLineCapability], by simp⟩
end Console

def SpecProcess.driverBoundary {R : Type} [Resource.ResourceModel R] {resources : R}
    (spec : SpecProcess resources)
    (view : Console.ContractView spec.contract := by apply Console.writeLineView) :
    Console.DriverBoundaryView spec := ⟨view⟩

/-- Closed plan selection retains the exact root and projection, even when
different roots require the same logical capability. -/
inductive PlatformPlan : Specification.RequirementSet → Type 2 where
  | win10X64SynchronousStdoutOnly
      {R : Type} [Resource.ResourceModel R] {resources : R}
      {spec : SpecProcess resources} (projection : TargetProjection spec .win10X64) :
      PlatformPlan (spec.driverBoundary projection.view).requirements

end Grass
