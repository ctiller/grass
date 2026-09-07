import Grass.Grammar.Core

/-!
# Generic grammar derivation fixtures
-/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

example (byte : Byte) (suffix : Std.Logical.ByteArray) :
    Derives (.byte (fun _ => True)) (Vec.singleton byte ++ suffix) byte suffix :=
  Derives.byte (fun _ => True) byte suffix trivial

end Grass.Tests.Grammar
