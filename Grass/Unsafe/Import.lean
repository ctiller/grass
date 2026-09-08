import Grass.Core.Name
import Grass.Unsafe.Construct

/-!
# Raw byte import boundary

`Decoder` is a machine-owner-supplied one-instruction parser. `importBytes`
accepts its output only when each step consumes an exact nonempty prefix and
every reported control target resolves through an explicit `TargetPolicy`.
The resulting `ImportedProgram` proves exact byte coverage and remains tainted;
it carries no instruction semantics or verification certificate.
-/

namespace Grass.Unsafe

open Grass.Core Grass.CFG

universe u v w x y

/-- A raw control-flow target reported by a decoder. -/
inductive ControlTarget where
  | direct (block : BlockId)
  | indirect (site : Name)
deriving Repr, DecidableEq

/-- Finite evidence supplied for one indirect-control site. -/
structure IndirectTargetEvidence (allowed : List BlockId) where
  site : Name
  targets : List BlockId
  targetsNonempty : targets ≠ []
  targetsUnique : targets.Nodup
  targetsAllowed : ∀ target ∈ targets, target ∈ allowed

/-- Exact finite control-target policy for one structurally checked CFG. -/
structure TargetPolicy (State : Type u) (Terminal : Type v) where
  graph : CFG.Graph State Terminal
  graphWellFormed : graph.WellFormed
  indirect : List (IndirectTargetEvidence graph.blockIds)
  indirectSitesUnique : (indirect.map IndirectTargetEvidence.site).Nodup

namespace TargetPolicy

/-- Whether the policy resolves one decoder-reported control target. -/
def resolves {State : Type u} {Terminal : Type v}
    (policy : TargetPolicy State Terminal) : ControlTarget → Bool
  | .direct block => policy.graph.blockIds.contains block
  | .indirect site => policy.indirect.any fun evidence => evidence.site == site

end TargetPolicy

/-- Machine-parametric parser and control-target projection. -/
structure Decoder (Byte : Type w) (Instruction : Type x) (DecodeError : Type y) where
  decodeOne : List Byte → Except DecodeError (Instruction × List Byte)
  controlTargets : Instruction → List ControlTarget

/-- One decoded instruction paired with its exact input byte prefix and offset. -/
structure ImportedInstruction (Byte : Type w) (Instruction : Type x) where
  offset : Nat
  bytes : List Byte
  instruction : Instruction
  controlTargets : List ControlTarget
deriving Repr, DecidableEq

namespace ImportedInstruction

/-- First byte offset immediately after one imported instruction. -/
def endOffset {Byte : Type w} {Instruction : Type x}
    (instruction : ImportedInstruction Byte Instruction) : Nat :=
  instruction.offset + instruction.bytes.length

end ImportedInstruction

/-- Consecutive nonempty byte-slice invariant retained by imported programs. -/
def ImportReadyFrom {Byte : Type w} {Instruction : Type x} :
    Nat → List (ImportedInstruction Byte Instruction) → Prop
  | _, [] => True
  | expected, instruction :: rest =>
      instruction.offset = expected ∧ instruction.bytes ≠ [] ∧
        ImportReadyFrom instruction.endOffset rest

private def importReadyFromDecidable
    {Byte : Type w} {Instruction : Type x} [DecidableEq Byte] :
    (expected : Nat) →
      (instructions : List (ImportedInstruction Byte Instruction)) →
      Decidable (ImportReadyFrom expected instructions)
  | _, [] => isTrue trivial
  | expected, instruction :: rest =>
      if offsetExact : instruction.offset = expected then
        if bytesNonempty : instruction.bytes ≠ [] then
          match importReadyFromDecidable instruction.endOffset rest with
          | isTrue restReady =>
              isTrue ⟨offsetExact, bytesNonempty, restReady⟩
          | isFalse restNotReady =>
              isFalse fun ready => restNotReady ready.2.2
        else
          isFalse fun ready => bytesNonempty ready.2.1
      else
        isFalse fun ready => offsetExact ready.1

instance {Byte : Type w} {Instruction : Type x} [DecidableEq Byte]
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction)) :
    Decidable (ImportReadyFrom expected instructions) :=
  importReadyFromDecidable expected instructions

/-- Structured rejection from the generic byte importer. -/
inductive ImportError (DecodeError : Type y) where
  | decode (offset : Nat) (error : DecodeError)
  | stalledDecoder (offset : Nat)
  | invalidRemainder (offset : Nat)
  | unresolvedControlTarget (offset : Nat) (target : ControlTarget)
  | fuelExhausted (offset : Nat)
deriving Repr, DecidableEq

/-- Fully consumed raw bytes and their still-tainted decoded instructions. -/
structure ImportedProgram (State : Type u) (Terminal : Type v)
    (Byte : Type w) (Instruction : Type x) where
  sourceBytes : List Byte
  instructions : List (ImportedInstruction Byte Instruction)
  bytesExact : instructions.flatMap ImportedInstruction.bytes = sourceBytes
  ready : ImportReadyFrom 0 instructions
  policy : TargetPolicy State Terminal
  taint : Taint

private theorem importReady_bytesNonempty
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions) :
    ∀ instruction ∈ instructions, instruction.bytes ≠ [] := by
  induction instructions generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨_, bytesNonempty, restReady⟩
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · exact bytesNonempty
      · exact ih head.endOffset restReady instruction hinstruction

private theorem importReady_bounded
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions) :
    ∀ instruction ∈ instructions,
      instruction.endOffset ≤ expected +
        (instructions.flatMap ImportedInstruction.bytes).length := by
  induction instructions generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, _, restReady⟩
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · simp only [List.flatMap_cons, List.length_append,
          ImportedInstruction.endOffset]
        omega
      · have bound := ih head.endOffset restReady instruction hinstruction
        simp only [List.flatMap_cons, List.length_append,
          ImportedInstruction.endOffset] at bound ⊢
        omega

namespace ImportedProgram

/-- Every accepted imported instruction owns a nonempty source-byte slice. -/
theorem instructionBytesNonempty
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (instruction : ImportedInstruction Byte Instruction)
    (hinstruction : instruction ∈ program.instructions) :
    instruction.bytes ≠ [] :=
  importReady_bytesNonempty 0 program.instructions program.ready instruction
    hinstruction

/-- Every accepted imported instruction ends within the exact source bytes. -/
theorem instructionBounded
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (instruction : ImportedInstruction Byte Instruction)
    (hinstruction : instruction ∈ program.instructions) :
    instruction.endOffset ≤ program.sourceBytes.length := by
  rw [← program.bytesExact]
  simpa using
    importReady_bounded 0 program.instructions program.ready instruction
      hinstruction

end ImportedProgram

private structure DecodedAt (Byte : Type w) (Instruction : Type x)
    (offset : Nat) (bytes : List Byte) where
  instructions : List (ImportedInstruction Byte Instruction)
  bytesExact : instructions.flatMap ImportedInstruction.bytes = bytes
  ready : ImportReadyFrom offset instructions

private def decodeFuel {State : Type u} {Terminal : Type v}
    {Byte : Type w} {Instruction : Type x} {DecodeError : Type y}
    [DecidableEq Byte]
    (decoder : Decoder Byte Instruction DecodeError)
    (policy : TargetPolicy State Terminal) :
    Nat → (offset : Nat) → (bytes : List Byte) →
      Except (ImportError DecodeError)
        (DecodedAt Byte Instruction offset bytes)
  | _, _, [] => .ok ⟨[], rfl, trivial⟩
  | 0, offset, _ :: _ => .error (.fuelExhausted offset)
  | fuel + 1, offset, head :: tail =>
      let bytes := head :: tail
      match decoder.decodeOne bytes with
      | .error error => .error (.decode offset error)
      | .ok (instruction, rest) =>
          if _progress : rest.length < bytes.length then
            let consumed := bytes.take (bytes.length - rest.length)
            if exactRemainder : consumed ++ rest = bytes then
              let targets := decoder.controlTargets instruction
              match targets.find? fun target => !policy.resolves target with
              | some target => .error (.unresolvedControlTarget offset target)
              | none =>
                  match decodeFuel decoder policy fuel (offset + consumed.length) rest with
                  | .error error => .error error
                  | .ok tail =>
                      have consumedNonempty : consumed ≠ [] := by
                        intro consumedEmpty
                        have restExact : rest = bytes := by
                          simpa [consumedEmpty] using exactRemainder
                        rw [restExact] at _progress
                        omega
                      .ok ⟨
                        ⟨offset, consumed, instruction, targets⟩ ::
                          tail.instructions,
                        by
                          simp only [List.flatMap_cons]
                          rw [tail.bytesExact]
                          simpa [bytes] using exactRemainder,
                        ⟨rfl, consumedNonempty, tail.ready⟩⟩
            else .error (.invalidRemainder offset)
          else .error (.stalledDecoder offset)

/-- Decode an exact byte list under a finite control-target policy.

Success retains an `importedBytes` taint and proves that concatenating every
recorded instruction prefix reproduces the input byte-for-byte. -/
def importBytes {State : Type u} {Terminal : Type v}
    {Byte : Type w} {Instruction : Type x} {DecodeError : Type y}
    [DecidableEq Byte]
    (decoder : Decoder Byte Instruction DecodeError)
    (policy : TargetPolicy State Terminal)
    (bytes : List Byte) (detail : String := "raw imported bytes") :
    Except (ImportError DecodeError)
      (ImportedProgram State Terminal Byte Instruction) :=
  match decodeFuel decoder policy bytes.length 0 bytes with
  | .error error => .error error
  | .ok decoded => .ok ⟨bytes, decoded.instructions, decoded.bytesExact,
      decoded.ready, policy, ⟨.importedBytes, detail⟩⟩

end Grass.Unsafe
