import Grass.ISA.SPIRV.SourceModule
import Tests.Assembly.SourceSelection

/-! External validator input, produced from the same checked source witness.
This executable is test tooling and supplies no proof authority. -/

private def bytes (words : Array (BitVec 32)) : ByteArray :=
  words.foldl (fun acc word =>
    let n := word.toNat
    ((acc.push (UInt8.ofNat n)).push (UInt8.ofNat (n / 256))).push
      (UInt8.ofNat (n / 65536)) |>.push (UInt8.ofNat (n / 16777216))) ByteArray.empty

def main (args : List String) : IO UInt32 := do
  let [sourcePath, name, outputPath] := args
    | throw (IO.userError "usage: ExportSource.lean SOURCE DECLARATION OUTPUT.spv")
  let source ← IO.FS.readFile sourcePath
  let some selection := Grass.Tests.Assembly.SourceSelection.selectCommand?
      "spirv_asm" name source.toList
    | throw (IO.userError "source declaration selection failed")
  let .ok checked := Grass.ISA.SPIRV.SourceModule.check selection.chars
    | throw (IO.userError "source module check failed")
  IO.FS.writeBinFile outputPath (bytes checked.output.words)
  IO.println s!"{name}: {checked.output.words.size} words, bound {checked.output.idBound}"
  return 0
