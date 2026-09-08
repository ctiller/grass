import Grass.Unsafe.Import

/-!
# Raw import fixtures

Fixtures pin exact byte consumption, structured decoder failure, progress
enforcement, and direct/indirect control-target rejection.
-/

namespace Grass.Tests.Unsafe.Import

open Grass Grass.Core Grass.CFG Grass.Unsafe

private inductive Instruction where
  | plain
  | jump (target : BlockId)
  | computed (site : Name)
deriving Repr, DecidableEq

private inductive DecodeFailure where
  | truncated
  | unknown (byte : Nat)
deriving Repr, DecidableEq

private def blockId (name : String) : BlockId := ⟨⟨"test.import", name⟩⟩
private def entry : BlockId := blockId "entry"
private def target : BlockId := blockId "target"
private def missing : BlockId := blockId "missing"
private def indirectSite : Name := ⟨"computed-jump"⟩

private def contract : BlockContract Nat where
  requires := fun _ => True
  exits := []

private def graph : CFG.Graph Nat String where
  entry := entry
  blocks := [⟨entry, contract, []⟩, ⟨target, contract, []⟩]

private def decoder : Decoder Nat Instruction DecodeFailure where
  decodeOne
    | [] => .error .truncated
    | 0 :: rest => .ok (.plain, rest)
    | 1 :: 0 :: rest => .ok (.jump target, rest)
    | 1 :: 1 :: rest => .ok (.jump missing, rest)
    | 2 :: rest => .ok (.computed indirectSite, rest)
    | byte :: _ => .error (.unknown byte)
  controlTargets
    | .plain => []
    | .jump block => [.direct block]
    | .computed site => [.indirect site]

private def indirectEvidence : IndirectTargetEvidence graph.blockIds where
  site := indirectSite
  targets := [target]
  targetsNonempty := by decide
  targetsUnique := by decide
  targetsAllowed := by decide

private def policy : TargetPolicy Nat String where
  graph := graph
  graphWellFormed := by decide
  indirect := [indirectEvidence]
  indirectSitesUnique := by decide

private def directOnlyPolicy : TargetPolicy Nat String where
  graph := graph
  graphWellFormed := by decide
  indirect := []
  indirectSitesUnique := by decide

example : policy.indirectEvidence? indirectSite = some indirectEvidence := rfl
example : directOnlyPolicy.indirectEvidence? indirectSite = none := rfl
example (evidence : IndirectTargetEvidence policy.graph.blockIds)
    (hfind : policy.indirectEvidence? indirectSite = some evidence) :
    evidence.site = indirectSite :=
  TargetPolicy.site_of_indirectEvidence? hfind
example (evidence : IndirectTargetEvidence policy.graph.blockIds)
    (hfind : policy.indirectEvidence? indirectSite = some evidence)
    (block : BlockId) (hblock : block ∈ evidence.targets) :
    block ∈ policy.graph.blockIds :=
  TargetPolicy.targetAllowed_of_indirectEvidence? hfind block hblock
example : policy.resolves (.indirect indirectSite) = true ↔
    (policy.indirectEvidence? indirectSite).isSome = true :=
  policy.resolves_indirect_iff indirectSite
example : (policy.resolution? (.direct target)).isSome = true := by decide
example : (policy.resolution? (.indirect indirectSite)).isSome = true := by decide
example (reported : ControlTarget) :
    (policy.resolution? reported).isSome = policy.resolves reported :=
  policy.resolution?_isSome_eq_resolves reported
example (resolution : TargetPolicy.ResolvedControlTarget policy (.direct target)) :
    target ∈ policy.graph.blockIds :=
  TargetPolicy.block_mem_of_resolution resolution
example (resolution : TargetPolicy.ResolvedControlTarget policy (.indirect indirectSite)) :
    ∃ evidence, policy.indirectEvidence? indirectSite = some evidence :=
  TargetPolicy.indirectEvidence_of_resolution resolution

private def summarize
    (result : Except (ImportError DecodeFailure)
      (ImportedProgram Nat String Nat Instruction)) :
    Except (ImportError DecodeFailure)
      (List Nat × List (ImportedInstruction Nat Instruction) × List BlockId × Taint) :=
  result.map fun imported =>
    (imported.sourceBytes, imported.instructions,
      imported.policy.graph.blockIds, imported.taint)

example : summarize (importBytes decoder policy [0, 1, 0, 2]) = .ok (
    [0, 1, 0, 2],
    [
      ⟨0, [0], .plain, []⟩,
      ⟨1, [1, 0], .jump target, [.direct target]⟩,
      ⟨3, [2], .computed indirectSite, [.indirect indirectSite]⟩],
    [entry, target],
    ⟨.importedBytes, "raw imported bytes"⟩) := by rfl
example : (importBytes decoder policy [0, 1, 0, 2]).map
    (fun imported => decide (ImportReadyFrom 0 imported.instructions)) =
    .ok true := by rfl

private def accepted : ImportedProgram Nat String Nat Instruction :=
  (importBytes decoder policy [0, 1, 0, 2]).toOption.get (by decide)

example : accepted.instructionAtByte? 0 =
    some ⟨0, [0], .plain, []⟩ := rfl
example : accepted.instructionAtByte? 2 =
    some ⟨1, [1, 0], .jump target, [.direct target]⟩ := rfl
example : accepted.instructionAtByte? 3 =
    some ⟨3, [2], .computed indirectSite, [.indirect indirectSite]⟩ := rfl
example : accepted.instructionAtByte? 4 = none := rfl

example (imported : ImportedProgram Nat String Nat Instruction) :
    ImportReadyFrom 0 imported.instructions := by
  exact imported.ready
example (imported : ImportedProgram Nat String Nat Instruction)
    (instruction : ImportedInstruction Nat Instruction)
    (hinstruction : instruction ∈ imported.instructions) :
    instruction.bytes ≠ [] :=
  imported.instructionBytesNonempty instruction hinstruction
example (imported : ImportedProgram Nat String Nat Instruction)
    (instruction : ImportedInstruction Nat Instruction)
    (hinstruction : instruction ∈ imported.instructions) :
    instruction.endOffset ≤ imported.sourceBytes.length :=
  imported.instructionBounded instruction hinstruction
example (imported : ImportedProgram Nat String Nat Instruction)
    (offset : Nat) (instruction : ImportedInstruction Nat Instruction) :
    imported.instructionAtByte? offset = some instruction ↔
      instruction ∈ imported.instructions ∧ instruction.offset ≤ offset ∧
        offset < instruction.endOffset :=
  imported.instructionAtByte?_eq_some_iff offset instruction
example (imported : ImportedProgram Nat String Nat Instruction)
    (offset : Nat) :
    imported.instructionAtByte? offset = none ↔
      imported.sourceBytes.length ≤ offset :=
  imported.instructionAtByte?_eq_none_iff offset
example (imported : ImportedProgram Nat String Nat Instruction)
    (instruction : ImportedInstruction Nat Instruction)
    (hinstruction : instruction ∈ imported.instructions)
    (reported : ControlTarget) (hreported : reported ∈ instruction.controlTargets) :
    imported.policy.resolves reported = true :=
  imported.controlTargetResolved instruction hinstruction reported hreported
example (imported : ImportedProgram Nat String Nat Instruction)
    (instruction : ImportedInstruction Nat Instruction)
    (hinstruction : instruction ∈ imported.instructions)
    (reported : ControlTarget) (hreported : reported ∈ instruction.controlTargets) :
    ∃ resolution, imported.policy.resolution? reported = some resolution :=
  imported.controlTargetResolution instruction hinstruction reported hreported

example : (importBytes decoder policy [1, 1]).map (fun _ => ()) =
    .error (.unresolvedControlTarget 0 (.direct missing)) := by rfl

example : (importBytes decoder directOnlyPolicy [2]).map (fun _ => ()) =
    .error (.unresolvedControlTarget 0 (.indirect indirectSite)) := by rfl

example : (importBytes decoder policy [9]).map (fun _ => ()) =
    .error (.decode 0 (.unknown 9)) := by rfl

private def stalled : Decoder Nat Instruction DecodeFailure where
  decodeOne bytes := .ok (.plain, bytes)
  controlTargets _ := []

example : (importBytes stalled policy [0]).map (fun _ => ()) =
    .error (.stalledDecoder 0) := by rfl

private def invalidRemainder : Decoder Nat Instruction DecodeFailure where
  decodeOne
    | [] => .error .truncated
    | _ :: _ => .ok (.plain, [9])
  controlTargets _ := []

example : (importBytes invalidRemainder policy [0, 1]).map (fun _ => ()) =
    .error (.invalidRemainder 0) := by rfl

end Grass.Tests.Unsafe.Import
