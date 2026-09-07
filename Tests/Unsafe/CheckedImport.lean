import Grass.Unsafe.CheckedImport

/-!
# Checked raw import fixtures

The one-byte decoder fixture pins successful decoding and control closure,
decoder byte offsets, and typed target-closure failure separation.
-/

namespace Grass.Tests.Unsafe.CheckedImport

open Grass.Unsafe

inductive Instruction where
  | plain
  | jump (target : Nat)
deriving Repr, DecidableEq

inductive DecodeError where
  | reserved
deriving Repr, DecidableEq

def decoder : Decoder UInt8 Instruction DecodeError where
  decode
    | [] => .error .reserved
    | 255 :: _ => .error .reserved
    | 0 :: rest => .ok {
        instruction := .plain
        consumed := [0]
        rest := rest
        consumedNonempty := by simp
        inputExact := by rfl
      }
    | byte :: rest => .ok {
        instruction := .jump byte.toNat
        consumed := [byte]
        rest := rest
        consumedNonempty := by simp
        inputExact := by rfl
      }

def model : ControlModel Instruction Nat Unit where
  project
    | .plain => []
    | .jump target => [.direct target]

def evidence (targets : List Nat) (raw : RawHierarchy Instruction) :
    ControlEvidence raw model where
  admittedTargets := targets
  indirect := []

def importedInstructions (bytes : List UInt8) (targets : List Nat) :
    Option (List Instruction) :=
  match decoder.importClosed bytes model (evidence targets) with
  | .ok closed => some closed.raw.flatten
  | .error _ => none

def importError (bytes : List UInt8) (targets : List Nat) :
    Option (CheckedImportError DecodeError Nat Unit) :=
  match decoder.importClosed bytes model (evidence targets) with
  | .ok _ => none
  | .error error => some error

example : importedInstructions [0, 1, 2] [1, 2] =
    some [.plain, .jump 1, .jump 2] := by native_decide

example : importError [0, 255, 2] [2] =
    some (.decode ⟨1, .reserved⟩) := by native_decide

example : importError [0, 1, 2] [1] =
    some (.control (.unresolvedDirect [⟨2, .direct 2⟩])) := by native_decide

end Grass.Tests.Unsafe.CheckedImport
