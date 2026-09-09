import Tests.Assembly.SourceLinkedImage

namespace Grass.Tests.Assembly.SourceLinkedImageErrors
open Grass.Assembly Grass.Artifact.PE Grass.Std.Logical
open Grass.Assembly.SourceLinkedImage (BuildError)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

private def requireSome {α : Type} : Option α → Except BuildError α
  | none => .error .sourceResolution
  | some value => .ok value

def missingPayload : StaticObjects.Table := StaticObjects.checked
  [⟨"unrelated", 1, .rodata, SourceLinkedImage.payload⟩]
  (by simp [StaticObjects.Valid]; decide)

def run (codeCharacteristics : BitVec 32) (missing : Bool) : Except BuildError Nat := do
  let body ← requireSome (SourceInput.extractHelloSourceChars SourceResolve.authored).toOption
  let frame ← requireSome (SourceFrame.derive? body)
  let splice ← requireSome (SourceSplice.derive? frame 0)
  let table := if missing then missingPayload else
    SourceLinkedImage.staticTable SourceLinkedImage.payload
  let statics ← requireSome (StaticSection.layout? table SourceLinkedImage.staticName 0x40000040)
  let requests ← requireSome (SourceImportRequests.resolve? splice "kernel32.dll")
  let result ← Grass.Assembly.SourceLinkedImage.buildExcept splice statics
    ⟨SourceLinkedImage.codeName, codeCharacteristics,
      SourceLinkedImage.pdataName, SourceLinkedImage.xdataName⟩ requests
  pure result.source.outputs.length

inductive Outcome where
  | failed (error : BuildError)
  | succeeded (count : Nat)
deriving Repr, DecidableEq

def outcome (codeCharacteristics : BitVec 32) (missing : Bool) : Outcome :=
  match run codeCharacteristics missing with
  | .error error => .failed error
  | .ok count => .succeeded count

example : outcome 0x60000020 false = .succeeded 44 := by decide +kernel

-- Final exception validation rejects the code permissions, retaining its cause.
example : outcome 0 false = .failed (.finalImage
    "PE image layout, imports or exception table fail the supported profile") := by decide +kernel

-- A missing source symbol is distinguished from the later image-profile failure.
example : outcome 0x60000020 true = .failed .sourceResolution := by decide +kernel

example {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Grass.Assembly.SourceLinkedImage.Sections)
    (requests : SourceImportRequests.Result splice) :
    Grass.Assembly.SourceLinkedImage.build? splice statics sections requests =
      (Grass.Assembly.SourceLinkedImage.buildExcept splice statics sections requests).toOption := rfl

end Grass.Tests.Assembly.SourceLinkedImageErrors
