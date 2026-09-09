import Grass.Assembly.SourceLinkedImage
import Grass.Std.Logical.HostBytes

/-! Export a structural fixture from the Hello assembly projection and explicit
payload bytes. Surrounding Lean declarations are not elaborated. This is not
the complete source program or the VerifiedProgram emission gate. -/
namespace DisasmHello
open Grass.Assembly Grass.Artifact.PE Grass.Std.Logical

private def require {α : Type} (stage : String) : Option α → Except String α
  | none => .error stage
  | some value => .ok value

def statics (payload : Grass.Std.Logical.ByteArray) : StaticObjects.Table := StaticObjects.checked
  [⟨"payload", 1, .rodata, payload⟩]
  (by simp [StaticObjects.Valid]; decide)

def name (text : String) (fits : (Text.utf8 text).length ≤ 8) : SectionName := ⟨Text.utf8 text, fits⟩

def produce (source : List Char) (payload : Grass.Std.Logical.ByteArray) :
    Except String Grass.Std.Logical.ByteArray := do
  let body ← require "extractHelloSourceChars" (SourceInput.extractHelloSourceChars source).toOption
  let frame ← require "SourceFrame.derive?" (SourceFrame.derive? body)
  let splice ← require "SourceSplice.derive?" (SourceSplice.derive? frame 0)
  let data ← require "StaticSection.layout?"
    (StaticSection.layout? (statics payload) (name ".rdata" (by decide)) 0x40000040)
  let requests ← require "SourceImportRequests.resolve?"
    (SourceImportRequests.resolve? splice "kernel32.dll")
  let result ← (SourceLinkedImage.buildExcept splice data
    ⟨name ".text" (by decide), 0x60000020,
      name ".pdata" (by decide), name ".xdata" (by decide)⟩ requests).mapError reprStr
  return writeImage result.plan

end DisasmHello

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, payloadPath, outputPath] =>
      let source ← IO.FS.readFile sourcePath
      let payload ← IO.FS.readBinFile payloadPath
      match DisasmHello.produce source.toList (Grass.Std.Logical.Vec.ofHostBytes payload) with
      | .error error =>
          (← IO.getStderr).putStrLn s!"structural Hello export failed: {error}"
          return 2
      | .ok bytes =>
          IO.FS.writeBinFile outputPath bytes.toHostBytes
          (← IO.getStdout).putStrLn
            s!"Wrote {bytes.length} structural PE bytes: assembly projection of {sourcePath}, explicit payload {payloadPath}. Surrounding source declarations are not elaborated; no end-to-end safety certificate."
          return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: grass-disasm-hello SOURCE_ASSEMBLY_FILE PAYLOAD_BIN OUTPUT_PE"
      return 2
