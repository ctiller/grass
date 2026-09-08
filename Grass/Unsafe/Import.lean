import Grass.CFG.Contract
import Grass.ISA.X86.Decode
import Grass.Unsafe.Construct

/-!
# Tainted instruction import

The existing x86 decoder supplies structured byte parsing. This adapter keeps
its result explicitly raw and records a caller-supplied control-target account.
An indirect account must be nonempty and duplicate-free and must say whether it
came from an annotation, relocation, or analysis. Those checks do not establish
that the decoded opcode has exactly those successors, so `.controlTargets`
remains in the result's `Taint`; only a later construction proof may remove it.
-/

namespace Grass.Unsafe.Import

open Grass Grass.CFG Grass.ISA.X86 Grass.Std.Logical Grass.Unsafe

/-- External basis from which an importer obtained an indirect target set. -/
inductive TargetBasis where
  | annotation
  | relocation
  | analysis
deriving Repr, DecidableEq

/-- Claimed finite destinations for one imported indirect transfer. -/
structure IndirectTargets where
  basis : TargetBasis
  targets : List BlockId
deriving Repr, DecidableEq

/-- Caller-supplied control-flow account retained beside the decoded instruction. -/
inductive TargetEvidence where
  | fallthrough
  | direct (target : BlockId)
  | indirect (evidence : IndirectTargets)
deriving Repr, DecidableEq

namespace TargetEvidence

/-- Destinations explicitly named by this account. -/
def declaredTargets : TargetEvidence → List BlockId
  | .fallthrough => []
  | .direct target => [target]
  | .indirect evidence => evidence.targets

/-- Structural check for target accounts; indirect sets must be nonempty and unique. -/
def wellFormed : TargetEvidence → Bool
  | .fallthrough => true
  | .direct _ => true
  | .indirect evidence =>
      decide (evidence.targets ≠ []) && decide evidence.targets.Nodup

/-- Proposition-level shape required of an imported target account. -/
def WellFormed : TargetEvidence → Prop
  | .fallthrough => True
  | .direct _ => True
  | .indirect evidence => evidence.targets ≠ [] ∧ evidence.targets.Nodup

instance (evidence : TargetEvidence) : Decidable evidence.WellFormed := by
  cases evidence <;> simp only [WellFormed] <;> infer_instance

@[simp] theorem wellFormed_eq_true_iff (evidence : TargetEvidence) :
    evidence.wellFormed = true ↔ evidence.WellFormed := by
  cases evidence <;> simp [wellFormed, WellFormed]

/-- Every well-formed indirect account contains at least one declared target. -/
theorem indirect_nonempty_of_wellFormed (evidence : IndirectTargets)
    (h : (TargetEvidence.indirect evidence).WellFormed) :
    evidence.targets ≠ [] := h.1

/-- Every well-formed indirect account names each target at most once. -/
theorem indirect_nodup_of_wellFormed (evidence : IndirectTargets)
    (h : (TargetEvidence.indirect evidence).WellFormed) :
    evidence.targets.Nodup := h.2

end TargetEvidence

/-- Structured failure from byte decoding or target-account validation. -/
inductive Error where
  | decode (cause : DecodeError)
  | invalidTargets (evidence : TargetEvidence)
deriving Repr, DecidableEq

/-- One decoded instruction that remains raw together with its import context. -/
structure ImportedInstruction where
  input : ByteSeq
  instruction : Unsafe.Construct.X86Instruction
  rest : ByteSeq
  targets : TargetEvidence

/-- Taint attached uniformly to every successfully decoded imported instruction. -/
def importedTaint : Taint :=
  ⟨.encodingShape,
    [.applicability, .semantics, .controlTargets, .relocations, .citations]⟩

/-- Decode one instruction and reject malformed indirect target accounts. -/
def importOne (input : ByteSeq) (targets : TargetEvidence) :
    Except Error ImportedInstruction :=
  match decodeInsn input with
  | .error cause => .error (.decode cause)
  | .ok (encoding, rest) =>
      if targets.wellFormed then
        .ok
          { input := input
            instruction := Unsafe.Construct.x86Instruction encoding importedTaint.primary
              importedTaint.additional
            rest := rest
            targets := targets }
      else .error (.invalidTargets targets)

/-- `importOne_of_decode` proves valid evidence preserves every decoder output exactly. -/
theorem importOne_of_decode {input : ByteSeq} {targets : TargetEvidence}
    {encoding : InsnEncoding} {rest : ByteSeq}
    (hdecode : decodeInsn input = .ok (encoding, rest))
    (hvalid : targets.WellFormed) :
    importOne input targets = .ok
      { input := input
        instruction := Unsafe.Construct.x86Instruction encoding importedTaint.primary
          importedTaint.additional
        rest := rest
        targets := targets } := by
  have checked := (TargetEvidence.wellFormed_eq_true_iff targets).mpr hvalid
  simp [importOne, hdecode, checked]

/-- `importOne_decode` exposes the exact decoder result behind a successful import. -/
theorem importOne_decode {input : ByteSeq} {targets : TargetEvidence}
    {imported : ImportedInstruction}
    (h : importOne input targets = .ok imported) :
    decodeInsn input = .ok (imported.instruction.value, imported.rest) := by
  cases decodedEq : decodeInsn input with
  | error cause => simp [importOne, decodedEq] at h
  | ok result =>
      rcases result with ⟨encoding, rest⟩
      by_cases valid : targets.wellFormed
      · simp [importOne, decodedEq, valid] at h
        cases h
        rw [Unsafe.Construct.x86Instruction_value]
      · simp [importOne, decodedEq, valid] at h

/-- `importOne_targets` proves every successful import retained the supplied account. -/
theorem importOne_targets {input : ByteSeq} {targets : TargetEvidence}
    {imported : ImportedInstruction}
    (h : importOne input targets = .ok imported) :
    imported.targets = targets := by
  cases decodedEq : decodeInsn input with
  | error cause => simp [importOne, decodedEq] at h
  | ok result =>
      rcases result with ⟨encoding, rest⟩
      by_cases valid : targets.wellFormed
      · simp [importOne, decodedEq, valid] at h
        cases h
        rfl
      · simp [importOne, decodedEq, valid] at h

/-- `importOne_targetEvidenceWellFormed` recovers the validated target-account shape. -/
theorem importOne_targetEvidenceWellFormed {input : ByteSeq}
    {targets : TargetEvidence} {imported : ImportedInstruction}
    (h : importOne input targets = .ok imported) :
    targets.WellFormed := by
  cases decodedEq : decodeInsn input with
  | error cause => simp [importOne, decodedEq] at h
  | ok result =>
      rcases result with ⟨encoding, rest⟩
      by_cases valid : targets.wellFormed
      · simp [importOne, decodedEq, valid] at h
        exact (TargetEvidence.wellFormed_eq_true_iff targets).mp valid
      · simp [importOne, decodedEq, valid] at h

/-- `importOne_taint` proves import never drops any unresolved proof class. -/
theorem importOne_taint {input : ByteSeq} {targets : TargetEvidence}
    {imported : ImportedInstruction}
    (h : importOne input targets = .ok imported) :
    imported.instruction.taint = importedTaint := by
  cases decodedEq : decodeInsn input with
  | error cause => simp [importOne, decodedEq] at h
  | ok result =>
      rcases result with ⟨encoding, rest⟩
      by_cases valid : targets.wellFormed
      · simp [importOne, decodedEq, valid] at h
        cases h
        rfl
      · simp [importOne, decodedEq, valid] at h

end Grass.Unsafe.Import
