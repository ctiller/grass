import Grass.Assembly.SourceLinkedImage
import Tests.Assembly.SourceResolve

/-! Artifact composition fixtures using actual authored assembly and explicitly
supplied static bytes. These do not elaborate the authored specification or
claim complete executable-image acceptance. -/

namespace Grass.Tests.Assembly.SourceLinkedImage
open Grass.Assembly Grass.Artifact.PE Grass.Std.Logical
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def payload : Grass.Std.Logical.ByteArray := Text.utf8 "Hello, World!\r\n"
def staticTable (payload : Grass.Std.Logical.ByteArray) : StaticObjects.Table := StaticObjects.checked
  [⟨"payload", 1, .rodata, payload⟩] (by simp [StaticObjects.Valid]; decide)
def codeName : SectionName := ⟨Text.utf8 ".text", by decide⟩
def staticName : SectionName := ⟨Text.utf8 ".rdata", by decide⟩
def linkedView (payload : Grass.Std.Logical.ByteArray) : Option (Nat × Bool) := do
  let body ← (SourceInput.extractHelloSourceChars SourceResolve.authored).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let statics ← StaticSection.layout? (staticTable payload) staticName 0x40000040
  let requests ← SourceImportRequests.resolve? splice "kernel32.dll"
  let linked ← SourceLinkedImage.build? splice statics ⟨codeName, 0x60000020⟩ requests
  pure (linked.source.outputs.length, linked.source.codeBase == linked.plan.layout.entryPointRva)
example : linkedView payload = some (44, true) := by decide +kernel

/-- Growing the static payload beyond a section-alignment interval still resolves
all source references from the new image layout without new offset inputs. -/
example : linkedView (Vec.replicate 4097 65) = some (44, true) := by decide +kernel
end Grass.Tests.Assembly.SourceLinkedImage
