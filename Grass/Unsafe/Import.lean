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
  policy : TargetPolicy State Terminal
  taint : Taint

private def decodeFuel {State : Type u} {Terminal : Type v}
    {Byte : Type w} {Instruction : Type x} {DecodeError : Type y}
    [DecidableEq Byte]
    (decoder : Decoder Byte Instruction DecodeError)
    (policy : TargetPolicy State Terminal) :
    Nat → Nat → (bytes : List Byte) →
      Except (ImportError DecodeError)
        { instructions : List (ImportedInstruction Byte Instruction) //
          instructions.flatMap ImportedInstruction.bytes = bytes }
  | _, _, [] => .ok ⟨[], rfl⟩
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
                      .ok ⟨⟨offset, consumed, instruction, targets⟩ :: tail.val, by
                        simp only [List.flatMap_cons]
                        rw [tail.property]
                        simpa [bytes] using exactRemainder⟩
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
  | .ok decoded => .ok ⟨bytes, decoded.val, decoded.property, policy,
      ⟨.importedBytes, detail⟩⟩

end Grass.Unsafe
