import Grass.Grammar.Core

/-!
# Generic grammar derivation fixtures
-/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

example (byte : Byte) (suffix : Std.Logical.ByteArray) :
    Derives (.byte (fun _ => True)) (Vec.singleton byte ++ suffix) byte suffix :=
  Derives.byte (fun _ => True) byte suffix trivial

def exactlyTwoBytes : Format (Vec Byte) :=
  .repeat 2 (.byte (fun _ => True))

example (first second : Byte) (suffix : Std.Logical.ByteArray) :
    Derives exactlyTwoBytes
      (Vec.singleton first ++ Vec.singleton second ++ suffix)
      (Vec.fromList [first, second]) suffix := by
  apply Derives.repeatSucc
  · exact Derives.byte (fun _ => True) first _ trivial
  · apply Derives.repeatSucc
    · exact Derives.byte (fun _ => True) second suffix trivial
    · exact Derives.repeatZero (.byte (fun _ => True)) suffix

example (byte : Byte) (suffix : Std.Logical.ByteArray) :
    Derives (.iso (.byte (fun _ => True)) (Isomorphism.refl Byte))
      (Vec.singleton byte ++ suffix) byte suffix :=
  Derives.iso (Derives.byte (fun _ => True) byte suffix trivial)

example (byte : Byte) (rest suffix : Std.Logical.ByteArray)
    (derivation : Derives (.byte (fun _ => True))
      (Vec.singleton byte ++ rest) byte rest) :
    Derives (.byte (fun _ => True))
      ((Vec.singleton byte ++ rest) ++ suffix) byte (rest ++ suffix) :=
  derivation.appendSuffix suffix

example (first second : Byte) (suffix : Std.Logical.ByteArray) :
    Derives (.seq (.byte fun _ => True) (fun _ => .byte fun _ => True))
      ((Vec.singleton first) ++ (Vec.singleton second ++ suffix))
      (first, second) suffix := by
  exact Derives.seqAppend
    (Derives.byte (fun _ => True) first Vec.empty trivial)
    (Derives.byte (fun _ => True) second suffix trivial)

example (value : Subtype (fun _ : Byte => True))
    (suffix : Std.Logical.ByteArray) :
    ∃ consumed,
      Vec.singleton value.1 ++ suffix = consumed ++ suffix := by
  have derivation :
      Derives (.lift (.byte fun _ => True) Subtype.val)
        (Vec.singleton value.1 ++ suffix) value suffix :=
    Derives.lift (Derives.byte (fun _ => True) value.1 suffix trivial)
  exact derivation.consumesPrefix

end Grass.Tests.Grammar
