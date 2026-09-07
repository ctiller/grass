import Grass.Construct.Source.Containment

/-!
# Proof-only containment annotation fixtures

Fixtures pin exact edge/tail attachment, duplicate and unattached rejection,
and graph/instruction invariance under metadata erasure.
-/

namespace Grass.Tests.Construct.SourceContainment

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Instruction where
  | compare
  | branch
  | trap
deriving Repr, DecidableEq

private inductive Terminal where
  | violation
deriving Repr, DecidableEq

private inductive Violation where
  | excessWriteCount
deriving Repr, DecidableEq

private def blockId : BlockId := ⟨⟨"test.containment", "entry"⟩⟩
private def exitTag : ExitTag := ⟨⟨"test.containment", "violation"⟩⟩
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨exitTag, fun _ => True⟩]⟩
private def edge : Edge Terminal := ⟨exitTag, .terminal .violation⟩
private def cfg : CFG.Block Unit Terminal := ⟨blockId, contract, [edge]⟩
private def body : Source Instruction := .literal [.compare, .branch, .trap]
private def tailOrigin : SourceOrigin := ⟨[], [], 2⟩
private def envelope : AffineReturnEnvelope Int := ⟨0, 4, 8⟩
private def edgeAnnotation : ContainmentAnnotation Terminal Violation Int :=
  ⟨.edge exitTag (.terminal .violation), .excessWriteCount, envelope⟩
private def tailAnnotation : ContainmentAnnotation Terminal Violation Int :=
  ⟨.tail tailOrigin, .excessWriteCount, envelope⟩
private def block :
    Grass.Construct.Source.Block Unit Terminal Instruction
      (ContainmentAnnotation Terminal Violation Int) :=
  ⟨cfg, body, [edgeAnnotation, tailAnnotation]⟩
private def source :
    Ast Unit Terminal Instruction (ContainmentAnnotation Terminal Violation Int) :=
  ⟨blockId, [block]⟩

example : edgeAnnotation.site.attachedTo block = true := by decide
example : tailAnnotation.site.attachedTo block = true := by decide
example : source.ContainmentWellFormed := by decide
example : (checkContainment source).isOk = true := by decide
example : source.eraseContainment.toGraph = source.toGraph := by simp
example : source.eraseContainment.expandedBlocks = source.expandedBlocks := by simp
example : source.eraseContainment.instructionCount = source.instructionCount := by simp

private def duplicateBlock :
    Grass.Construct.Source.Block Unit Terminal Instruction
      (ContainmentAnnotation Terminal Violation Int) :=
  ⟨cfg, body, [edgeAnnotation, edgeAnnotation]⟩
private def duplicateSource :
    Ast Unit Terminal Instruction (ContainmentAnnotation Terminal Violation Int) :=
  ⟨blockId, [duplicateBlock]⟩
example : (checkContainment duplicateSource).map (fun _ => ()) =
    .error (.duplicateSites blockId [edgeAnnotation.site, edgeAnnotation.site]) := by
  rfl

private def wrongTail : ContainmentAnnotation Terminal Violation Int :=
  ⟨.tail ⟨[], [], 1⟩, .excessWriteCount, envelope⟩
private def unattachedBlock :
    Grass.Construct.Source.Block Unit Terminal Instruction
      (ContainmentAnnotation Terminal Violation Int) :=
  ⟨cfg, body, [wrongTail]⟩
private def unattachedSource :
    Ast Unit Terminal Instruction (ContainmentAnnotation Terminal Violation Int) :=
  ⟨blockId, [unattachedBlock]⟩
example : (checkContainment unattachedSource).map (fun _ => ()) =
    .error (.unattached blockId wrongTail.site) := by rfl

private def wrongEdge : ContainmentAnnotation Terminal Violation Int :=
  ⟨.edge exitTag (.block blockId), .excessWriteCount, envelope⟩
private def wrongEdgeBlock :
    Grass.Construct.Source.Block Unit Terminal Instruction
      (ContainmentAnnotation Terminal Violation Int) :=
  ⟨cfg, body, [wrongEdge]⟩
private def wrongEdgeSource :
    Ast Unit Terminal Instruction (ContainmentAnnotation Terminal Violation Int) :=
  ⟨blockId, [wrongEdgeBlock]⟩
example : (checkContainment wrongEdgeSource).map (fun _ => ()) =
    .error (.unattached blockId wrongEdge.site) := by rfl

end Grass.Tests.Construct.SourceContainment
