import Grass.Std.Logical.Vec

/-!
# Explicitly unverified raw artifact writing

This module is the artifact-side seam consumed by unchecked construction. It
accepts an arbitrary raw layout or link description through a supplied byte
writer and retains that exact input beside the resulting bytes. The result is
deliberately named `UnverifiedArtifact`: it contains no artifact certificate,
verified program, loader claim, or promotion operation.
-/

namespace Grass.Artifact.Binary

open Grass.Std.Logical

universe u

/-- An artifact byte writer over one caller-owned raw description type. -/
structure RawWriter (Raw : Type u) where
  write : Raw → Std.Logical.ByteArray

/-- Raw writer output retaining both the exact input and its serialized bytes.
Possession of this value carries no semantic or loader assurance. -/
structure UnverifiedArtifact (Raw : Type u) where
  input : Raw
  bytes : Std.Logical.ByteArray

/-- Apply a raw writer without manufacturing any certificate-bearing value. -/
def writeRaw {Raw : Type u} (writer : RawWriter Raw) (input : Raw) :
    UnverifiedArtifact Raw where
  input := input
  bytes := writer.write input

namespace writeRaw

/-- `writeRaw.inputExact` states that raw writing retains the caller's exact
input identity. -/
@[simp] theorem inputExact {Raw : Type u} (writer : RawWriter Raw) (input : Raw) :
    (writeRaw writer input).input = input := rfl

/-- `writeRaw.bytesExact` states that raw writing returns exactly the supplied
writer's bytes. -/
@[simp] theorem bytesExact {Raw : Type u} (writer : RawWriter Raw) (input : Raw) :
    (writeRaw writer input).bytes = writer.write input := rfl

end writeRaw

end Grass.Artifact.Binary
