import Grass.Artifact.Binary.Gobj.ImportManifest

/-! # Typed `.gobj` import-manifest fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.ImportManifest

open Grass.Artifact.Binary Grass.Artifact.Binary.Gobj Grass.Grammar
  Grass.Std.Logical

def oneByte (value : Byte) : U32LengthPrefixedBytes :=
  ⟨Vec.singleton value, by simp⟩

def localTarget : GobjNominalId := ⟨oneByte 0x6f, oneByte 0x66⟩
def signature : GobjNominalId := ⟨oneByte 0x70, oneByte 0x73⟩
def callable : GobjNominalId := ⟨oneByte 0x70, oneByte 0x63⟩
def abi : GobjNominalId := ⟨oneByte 0x61, oneByte 0x62⟩

def callableImport : GobjImportEntry where
  localTarget := localTarget
  subject := .callable signature callable
  abiContract := abi

def providerImport : GobjImportEntry where
  localTarget := ⟨oneByte 0x7a, oneByte 0x7a⟩
  subject := .provider signature callable
  abiContract := abi

def manifest : GobjImportManifest where
  entries := Vec.fromList [callableImport, providerImport]
  countFits := by decide
  localTargetsUnique := by decide
  canonicallyOrdered := by decide

example : manifest.entries.length = 2 := by decide
example : callableImport.subject = .callable signature callable := rfl
example : providerImport.subject = .provider signature callable := rfl

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : readGobjNominalId (writeGobjNominalId localTarget ++ suffix) =
    .done localTarget suffix := by
  exact readGobjNominalId_write_append localTarget suffix

example : readGobjImportEntry (writeGobjImportEntry callableImport ++ suffix) =
    .done callableImport suffix := by
  exact readGobjImportEntry_write_append callableImport suffix

example : readGobjImportSubject (Vec.singleton 2) =
    .invalid (.malformed "invalid .gobj import subject tag") := by rfl

example : readGobjImportManifest (writeGobjImportManifest manifest ++ suffix) =
    .done manifest suffix := by
  exact readGobjImportManifest_write_append manifest suffix

def duplicateManifestBytes : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (2 : BitVec 32) ++
    writeGobjImportEntryList [callableImport, callableImport]

def isDuplicateTargetError : ParseResult GobjImportManifest → Bool
  | .invalid (.malformed message) =>
    message == "duplicate .gobj import local target"
  | _ => false

example : isDuplicateTargetError
    (readGobjImportManifest duplicateManifestBytes) = true := by decide

def outOfOrderManifestBytes : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (2 : BitVec 32) ++
    writeGobjImportEntryList [providerImport, callableImport]

def isOrderingError : ParseResult GobjImportManifest → Bool
  | .invalid (.malformed message) =>
    message == ".gobj imports are not canonically ordered"
  | _ => false

example : isOrderingError
    (readGobjImportManifest outOfOrderManifestBytes) = true := by decide

end Grass.Tests.Artifact.Binary.Gobj.ImportManifest
