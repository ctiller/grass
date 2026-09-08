import Grass.Artifact.Binary.Gobj.Resolved

/-! # Exact `.gobj` resolution fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Resolved

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def scope : StableScopeId := Grass.StableId.mk "owner" "local"
def otherScope : StableScopeId := Grass.StableId.mk "owner" "other"
def emptyBody : U32LengthPrefixedBytes := ⟨Vec.empty, by decide⟩

def payload : GobjPayload where
  formatVersion := .v1
  scope := scope
  sections := emptyBody
  symbols := emptyBody
  relocations := emptyBody
  imports := emptyBody
  sourceMap := emptyBody

def otherPayload : GobjPayload := { payload with scope := otherScope }

def dottedLeft : GobjPayload :=
  { payload with scope := Grass.StableId.mk "a.b" "c" }

def dottedRight : GobjPayload :=
  { payload with scope := Grass.StableId.mk "a" "b.c" }

example : resolveGobj payload (writeGobj payload) =
    .ok { bytes := writeGobj payload, parsed := parseGobj_write payload } := by
  exact resolveGobj_write payload

example : resolveGobj otherPayload (writeGobj payload) =
    .error (.malformed ".gobj payload does not match expected object") := by
  exact resolveGobj_mismatch (parseGobj_write payload) (by decide)

example : dottedLeft.scope.render = dottedRight.scope.render := by decide

example : resolveGobj dottedRight (writeGobj dottedLeft) =
    .error (.malformed ".gobj payload does not match expected object") := by
  exact resolveGobj_mismatch (parseGobj_write dottedLeft) (by decide)

example : resolveGobj payload Vec.empty =
    .error (.malformed "truncated .gobj payload") := by rfl

example (resolved : ResolvedGobj payload) :
    parseGobj resolved.bytes = .ok payload := by
  exact resolved.parseExact

end Grass.Tests.Artifact.Binary.Gobj.Resolved
