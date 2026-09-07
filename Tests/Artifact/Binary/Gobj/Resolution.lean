import Grass.Artifact.Binary.Gobj.Resolution
import Tests.Artifact.Binary.Gobj.Schema

/-! # Exact `.gobj` resolution fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Resolution

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.Binary.Gobj.Schema

def bytes : Std.Logical.ByteArray := Vec.singleton (BitVec.ofNat 8 7)

def exactParser (input : Std.Logical.ByteArray) :
    ParseResult (GobjPayload RelocKind ImportIdentity Provenance) :=
  if input = bytes then .done bound.payload Vec.empty
  else .invalid (.malformed "fixture")

def trailingParser (_ : Std.Logical.ByteArray) :
    ParseResult (GobjPayload RelocKind ImportIdentity Provenance) :=
  .done bound.payload (Vec.singleton (BitVec.ofNat 8 0))

def wrongPayload : GobjPayload RelocKind ImportIdentity Provenance :=
  ⟨2, validFragment⟩

def wrongParser (_ : Std.Logical.ByteArray) :
    ParseResult (GobjPayload RelocKind ImportIdentity Provenance) :=
  .done wrongPayload Vec.empty

example : (resolveGobj? exactParser bound bytes).isSome = true := by
  rw [resolveGobj?_isSome_iff]
  simp [exactParser]

example : resolveGobj? trailingParser bound bytes = none := by
  rfl

example : resolveGobj? wrongParser bound bytes = none := by
  rfl

end Grass.Tests.Artifact.Binary.Gobj.Resolution
