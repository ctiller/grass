import Lean
import Grass.Disasm.Linear
import Grass.Disasm.Entry
import Grass.Disasm.CallerObject
import Grass.Disasm.Spatial
import Grass.ISA.X86.RegisterDecode
import Grass.ISA.X86.Execution.StackInstruction
import Grass.Artifact.PE.Imported
import Grass.Std.Logical.HostBytes

/-! Host ingress and diagnostic JSON for linear disassembly. This executable
does not issue a memory certificate or interpret a listing as reachable code. -/
open Lean Grass.Disasm Grass.Std.Logical Grass.ISA.X86

namespace DisasmTool


def byteHex (value : Grass.Std.Logical.Byte) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[value.toNat / 16]!, digits[value.toNat % 16]!]

def bytesHex (bytes : ByteSeq) : String := String.join (bytes.map byteHex)

def regName (width : BasicInstructions.Width) (reg : Gpr) : String :=
  let names := match width with
    | .w64 => #["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
    | .w32 => #["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
        "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
  names[reg.index.val]!

/-- Typed selectors determine assembly where supported. Otherwise retain the
decoder's diagnostic opcode family and encoded fields without inventing semantics. -/
def assembly (encoding : InsnEncoding) : String × String :=
  match Execution.StackInstruction.select encoding with
  | some selected =>
      match selected.instruction with
      | .push register => ("push " ++ regName .w64 register, "typed-stack-selection")
      | .subRsp immediate => (s!"sub rsp, {immediate.toInt}", "typed-stack-selection")
  | none =>
      match RegisterDecode.select encoding with
      | some selected =>
          let instruction := selected.instruction
          let name := match instruction.kind with
            | .mov => "mov" | .add => "add" | .sub => "sub"
            | .cmp => "cmp" | .test => "test" | .xor => "xor"
          (s!"{name} {regName instruction.width instruction.destination}, " ++
            regName instruction.width instruction.source, "typed-register-selection")
      | none =>
          ((findSpec encoding.escape encoding.opcode).map (·.mnemonic) |>.getD "unknown",
            "encoding-only")

def listingJson (pc : Nat) (fileOffset : Nat) (bytes : ByteSeq) : Json × Bool := Id.run do
  let listing := scan 4096 (BitVec.ofNat 64 pc) bytes
  let rows := listing.rows.map fun row =>
    let (text, selection) := assembly row.encoding
    Json.mkObj [
      ("address", toJson row.pc.toNat),
      ("fileOffset", toJson (fileOffset + row.pc.toNat - pc)),
      ("bytes", toJson (bytesHex row.encoding.toBytes)),
      ("assembly", toJson text), ("selection", toJson selection),
      ("encoding", toJson (reprStr row.encoding))]
  return (Json.mkObj [
    ("scope", toJson "linear bytes; no reachability or fetch claim"),
    ("byteLength", toJson bytes.length),
    ("consumedBytes", toJson listing.consumed.length),
    ("rows", toJson rows),
    ("remainingBytes", toJson (bytesHex listing.remaining)),
    ("stop", match listing.stop with | none => Json.null | some reason => toJson (reprStr reason))],
    listing.stop.isNone)

def directoryStatus (rva size : Nat) : Json :=
  Json.mkObj [("rva", toJson rva), ("size", toJson size),
    ("status", toJson (if rva = 0 && size = 0 then "absent" else "present-not-resolved"))]

def peReport (input : _root_.ByteArray) : Json × UInt32 :=
  match Grass.Artifact.PE.checkImportedImage (Vec.ofHostBytes input) with
  | .needMore minimum => (Json.mkObj [("parse", toJson "incomplete"),
      ("minimumAdditional", toJson minimum)], 2)
  | .invalid error => (Json.mkObj [("parse", toJson "refused-by-selected-container-profile"),
      ("error", toJson (reprStr error))], 2)
  | .done checked _ => Id.run do
      let imported := checked.result
      let image := imported.image
      let mut complete := true
      let mut sections := []
      for parsedSection in image.sections do
        let header := parsedSection.header
        let executable := header.characteristics.getLsbD 29
        let count := min header.virtualSize.toNat parsedSection.rawData.length
        let bytes := parsedSection.rawData.toList.take count
        let (listing, accepted) := if executable then
          listingJson header.virtualAddress.toNat header.rawOffset.toNat bytes
          else (Json.null, true)
        complete := complete && accepted
        sections := sections ++ [Json.mkObj [
          ("nameBytes", toJson (bytesHex header.name.toList)),
          ("fileOffset", toJson header.rawOffset.toNat), ("rawSize", toJson header.rawSize.toNat),
          ("rva", toJson header.virtualAddress.toNat), ("virtualSize", toJson header.virtualSize.toNat),
          ("characteristics", toJson header.characteristics.toNat),
          ("executable", toJson executable),
          ("unlistedRawTail", toJson (bytesHex (parsedSection.rawData.toList.drop count))),
          ("zeroFillSize", toJson (header.virtualSize.toNat - parsedSection.rawData.length)),
          ("listing", listing)]]
      return (Json.mkObj [
        ("parse", toJson "accepted-bounded-imported-container"),
        ("ntHeaderOffset", toJson image.header.ntOffset.toNat),
        ("dosStub", toJson (bytesHex imported.dosStub.toList)),
        ("addressSpace", toJson "image-relative; no load base applied"),
        ("machine", toJson image.header.machine.toNat),
        ("entryRva", toJson image.optional.entryPointRva.toNat),
        ("preferredImageBase", toJson image.optional.imageBase.toNat),
        ("imports", directoryStatus image.optional.importRva.toNat image.optional.importSize.toNat),
        ("remainingDirectories", toJson (bytesHex image.optional.remainingDirectories.toList)),
        ("relocations", toJson "directory bytes retained; not interpreted"),
        ("sections", toJson sections)], if complete then 0 else 3)

def storeReport (input : _root_.ByteArray) (rva imageBase objectBase objectSize rootSize : Nat) :
    Json × UInt32 := Id.run do
  let refuse := fun stage reason => (Json.mkObj [
    ("status", toJson "unresolved"), ("stage", toJson stage), ("reason", toJson reason)], 2)
  if imageBase + rva ≥ 2^64 || objectBase ≥ 2^64 then
    return refuse "arguments" "declared address does not fit 64 bits"
  match Grass.Artifact.PE.checkImportedImage (Vec.ofHostBytes input) with
  | .needMore _ => return refuse "container" "incomplete input"
  | .invalid error => return refuse "container" (reprStr error)
  | .done parsed _ =>
    match Entry.selectEntry parsed rva with
    | .error error => return refuse "entry-bytes" (reprStr error)
    | .ok entry =>
      let rip := BitVec.ofNat 64 (imageBase + rva)
      match CallerObject.check (BitVec.ofNat 64 objectBase) objectSize rootSize rip with
      | .error error => return refuse "declared-caller-model" (reprStr error)
      | .ok caller =>
        match StoreAttempt.check rip entry.bytes caller.state with
        | .error error => return refuse "decoded-store-candidate" (reprStr error)
        | .ok decoded =>
          let (verdict, excluded) := match Spatial.assess decoded caller.object with
            | .within _ => ("within-declared-object", Json.null)
            | .outside index _ => ("outside-declared-object", toJson index)
          return (Json.mkObj [
            ("status", toJson "conditional-spatial-assessment"),
            ("assessment", toJson verdict), ("outsideByteIndex", excluded),
            ("rva", toJson entry.rva), ("fileOffset", toJson entry.fileOffset),
            ("instructionBytes", toJson (bytesHex decoded.site.encoding.toBytes)),
            ("remainingBytes", toJson (bytesHex decoded.site.rest)),
            ("candidateAddress", toJson decoded.address.toNat), ("width", toJson decoded.width),
            ("declaredImageBase", toJson imageBase), ("declaredObjectBase", toJson objectBase),
            ("declaredObjectSize", toJson objectSize), ("declaredRootSize", toJson rootSize),
            ("callerModel", toJson "RCX at object start; synthetic live writable virtualAlloc root"),
            ("remainingObligations", toJson ["loaded bytes and instruction fetch",
              "entry applicability and reachability", "history-consistent caller object association",
              "x86 attempted transition semantics"])], 0)

def run (args : List String) : IO UInt32 := do
  if let ["store", path, rva, imageBase, objectBase, objectSize, rootSize] := args then
    let numbers ← [rva, imageBase, objectBase, objectSize, rootSize].mapM fun value =>
      match value.toNat? with
      | some number => pure number
      | none => throw (IO.userError "store parameters must be decimal unsigned integers")
    let input ← IO.FS.readBinFile path
    let (report, code) := storeReport input numbers[0]! numbers[1]! numbers[2]! numbers[3]! numbers[4]!
    (← IO.getStdout).putStrLn (Json.mkObj [
      ("schema", toJson "grass.disasm.store.v1"), ("input", toJson path),
      ("inputLength", toJson input.size),
      ("assurance", toJson "conditional decoded footprint only; binary memory safety unresolved"),
      ("report", report)]).pretty
    return code
  let (mode, path, base) ← match args with
    | ["pe", path] => pure ("pe", path, 0)
    | ["raw", path, base] =>
        match base.toNat? with
        | some base =>
            if base < 2^64 then pure ("raw", path, base)
            else throw (IO.userError "base must fit an unsigned 64-bit address")
        | none => throw (IO.userError "base must be a decimal unsigned address")
    | _ => throw (IO.userError "usage: grass-disasm pe FILE | raw FILE BASE | store FILE RVA IMAGE_BASE OBJECT_BASE OBJECT_SIZE ROOT_SIZE (decimal)")
  let input ← IO.FS.readBinFile path
  let (report, code) := if mode = "pe" then peReport input else
    let (report, complete) := listingJson base 0 (Vec.ofHostBytes input).toList
    (report, if complete then 0 else 3)
  let envelope := Json.mkObj [
    ("schema", toJson "grass.disasm.linear.v1"), ("input", toJson path),
    ("inputLength", toJson input.size),
    ("profile", toJson "x86-64 canonical Grass decoder subset"),
    ("assurance", toJson "decode evidence only; memory safety unresolved"),
    ("report", report)]
  (← IO.getStdout).putStrLn envelope.pretty
  return code

end DisasmTool

def main (args : List String) : IO UInt32 := do
  try DisasmTool.run args catch error =>
    (← IO.getStderr).putStrLn s!"grass-disasm: {error}"
    return 2
