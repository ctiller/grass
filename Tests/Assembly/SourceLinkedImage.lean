import Grass.Assembly.SourceLinkedImage
import Tests.Assembly.SourceResolve

/-! Generic artifact composition fixtures with explicitly supplied static bytes. -/

namespace Grass.Tests.Assembly.SourceLinkedImage
open Grass.Assembly Grass.Artifact.PE Grass.Std.Logical
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def blob : Grass.Std.Logical.ByteArray := Vec.fromList [12, 34, 56]
def staticTable (blob : Grass.Std.Logical.ByteArray) : StaticObjects.Table := StaticObjects.checked
  [⟨"blob", 1, .rodata, blob⟩] (by simp [StaticObjects.Valid]; decide)
def codeName : SectionName := ⟨Text.utf8 ".text", by decide⟩
def staticName : SectionName := ⟨Text.utf8 ".rdata", by decide⟩
def pdataName : SectionName := ⟨Text.utf8 ".pdata", by decide⟩
def xdataName : SectionName := ⟨Text.utf8 ".xdata", by decide⟩

def linkedView (blob : Grass.Std.Logical.ByteArray) :
    Option (Nat × Bool × Bool × Bool × Bool × Bool) := do
  let body ← (SourceInput.extractSourceChars SourceResolve.source).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let statics ← StaticSection.layout? (SourceLinkedImage.staticTable blob)
    SourceLinkedImage.staticName 0x40000040
  let requests ← SourceImportRequests.resolve? splice "kernel32.dll"
  let linked ← SourceLinkedImage.build? splice statics
    { codeName := SourceLinkedImage.codeName
      codeCharacteristics := 0x60000020
      pdataName
      xdataName } requests
  let functions ← resolveRuntimeFunctions? linked.plan.layout.placed
    linked.exceptionTable.functions.toList
  let function ← functions[0]?
  pure (linked.source.outputs.length,
    linked.plan.layout.requested.exceptionTable == some linked.exceptionTable,
    linked.pdata.source.contents == linked.tableBytes,
    linked.xdata.source.contents == linked.unwind.bytes,
    linked.source.bytes.toList.take linked.unwind.info.layout.sizeOfProlog.toNat ==
      ByteLayout.emitted splice.prologue.generated,
    functions.length == 1 && function.beginRva == linked.source.codeBase &&
      function.endRva == linked.source.codeBase + linked.source.bytes.length &&
      function.codeBytes == linked.source.bytes && function.unwindBytes == linked.unwind.bytes)

example : linkedView SourceLinkedImage.blob = some (4, true, true, true, true, true) := by
  decide +kernel

/-- Section growth changes only derived placement inputs; unwind attachment uses
the same source and PE algorithms without a new offset literal. -/
example : linkedView (Vec.replicate 4097 65) = some (4, true, true, true, true, true) := by
  decide +kernel

end Grass.Tests.Assembly.SourceLinkedImage
