import Grass.Unsafe.Import

/-!
# Raw import fixtures

The fixture decoder consumes exactly one byte per instruction. Tests pin empty
input, exact order, and the byte offset of a later decoder failure.
-/

namespace Grass.Tests.Unsafe.Import

open Grass.Unsafe

inductive Error where
  | reserved
deriving Repr, DecidableEq

def decoder : Decoder UInt8 UInt8 Error where
  decode
    | [] => .error .reserved
    | 255 :: _ => .error .reserved
    | byte :: rest => .ok {
        instruction := byte
        consumed := [byte]
        rest := rest
        consumedNonempty := by simp
        inputExact := by rfl
      }

def importedInstructions (bytes : List UInt8) : Option (List UInt8) :=
  match decoder.importRaw bytes with
  | .ok raw => some raw.flatten
  | .error _ => none

def importedError (bytes : List UInt8) : Option (ImportError Error) :=
  match decoder.importRaw bytes with
  | .ok _ => none
  | .error error => some error

example : decoder.importRaw [] = .ok .empty := by simp
example : importedInstructions [1, 2, 3] = some [1, 2, 3] := by native_decide
example : importedError [1, 2, 255, 4] = some ⟨2, .reserved⟩ := by native_decide

example {input : List UInt8} (decoded : DecodedOne UInt8 input) :
    decoded.consumed ≠ [] ∧ input = decoded.consumed ++ decoded.rest :=
  ⟨decoded.consumedNonempty, decoded.inputExact⟩

end Grass.Tests.Unsafe.Import
