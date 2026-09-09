import Grass.Platform.Win32.ApiDispatch
import Tests.Platform.Win32LoaderEntry
import Tests.Artifact.PE.ImageWriter

/-! Computed logical import-binding regressions.  These fixtures initialize the
model image and inspect its actual layout; they do not probe native DLLs or
claim that a target is a physical Windows export. -/

namespace Grass.Tests.Win32ApiDispatch

open Grass.Std.Logical Grass.Artifact
open Grass.Platform.Win32 Grass.Platform.Win32.Loader
open Grass.Platform.Win32.ApiDispatch

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def kernelSymbols : Vec PE.ImportSymbol := .fromList [
  { name := Text.utf8 "GetStdHandle" },
  { name := Text.utf8 "WriteFile" },
  { name := Text.utf8 "ExitProcess" },
  { name := Text.utf8 "UnknownApi" },
  { name := Text.utf8 "writefile" }]

def kernelLibrary : PE.ImportLibrary :=
  { name := Tests.Artifact.PE.ImageWriter.kernel32.name, symbols := kernelSymbols }

def customLibrary : PE.ImportLibrary :=
  { name := Text.utf8 "fixture-provider.bin"
    symbols := .fromList [{ name := Text.utf8 "WriteFile" }] }

def description : PE.ExecutableImageDescription :=
  { Tests.Artifact.PE.ImageWriter.description with
    imports := .fromList [kernelLibrary, customLibrary] }

def targets : ImportTargets := .fromList [
  .fromList [0x7ff01010, 0x7ff02020, 0x7ff03030, 0x7ff04040, 0x7ff05050],
  .fromList [0x6ee06060]]

theorem api_bytes_getStdHandle : apiForBytes? (Text.utf8 "GetStdHandle") =
    some .getStdHandle := by decide
theorem api_bytes_writeFile : apiForBytes? (Text.utf8 "WriteFile") =
    some .writeFile := by decide
theorem api_bytes_exitProcess : apiForBytes? (Text.utf8 "ExitProcess") =
    some .exitProcess := by decide
theorem api_bytes_unknown : apiForBytes? (Text.utf8 "UnknownApi") = none := by decide
theorem api_bytes_lowercase_refused : apiForBytes? (Text.utf8 "writefile") = none := by decide

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("API dispatch fixture failed: " ++ label))

/- One initialization feeds all selections.  Each positive result is checked
against values freshly obtained from `importAddressRva?` and `inputs.targets`. -/
#eval do
  let some plan := (PE.prepareImage description).toOption
    | throw (IO.userError "dispatch image plan refused")
  let image : ImageInput := ⟨plan, (PE.writeImage plan).toHostBytes, rfl⟩
  let inputs := Grass.Tests.Win32LoaderEntry.inputsFor plan targets
  let some loaded := initialize? image inputs
    | throw (IO.userError "dispatch image initialization refused")
  let base := (preferredBase image).toNat

  let checkPositive (libraryIndex symbolIndex : Nat) (expectedApi : Signatures.Api)
      (expectedLibrary : Grass.Std.Logical.ByteArray) (expectedTarget : BitVec 64) : IO Unit := do
    let some rva := plan.layout.importAddressRva? libraryIndex symbolIndex
      | throw (IO.userError "expected IAT coordinate absent")
    let ea := BitVec.ofNat 64 (base + rva)
    let some binding := select? loaded ea expectedTarget
      | throw (IO.userError "expected dispatch selection absent")
    check "API" (binding.api == expectedApi)
    check "library index" (binding.libraryIndex == libraryIndex)
    check "symbol index" (binding.symbolIndex == symbolIndex)
    check "library bytes" (binding.libraryName == expectedLibrary)
    check "symbol bytes"
      (binding.symbol.name == Text.utf8 (Signatures.apiName expectedApi))
    check "RVA" (binding.rva == rva)
    check "target" (binding.target == expectedTarget)

  checkPositive 0 0 .getStdHandle kernelLibrary.name 0x7ff01010
  checkPositive 0 1 .writeFile kernelLibrary.name 0x7ff02020
  checkPositive 0 2 .exitProcess kernelLibrary.name 0x7ff03030
  checkPositive 1 0 .writeFile customLibrary.name 0x6ee06060

  let some writeRva := plan.layout.importAddressRva? 0 1
    | throw (IO.userError "WriteFile IAT coordinate absent")
  let writeEA := BitVec.ofNat 64 (base + writeRva)
  check "target mismatch refused" (!(select? loaded writeEA 0x7ff02021).isSome)
  check "EA plus one refused" (!(select? loaded (writeEA + 1) 0x7ff02020).isSome)
  check "wrong candidate indices refused"
    (!(candidateAt? loaded writeEA 0x7ff02020 1 1).isSome)

  let some unknownRva := plan.layout.importAddressRva? 0 3
    | throw (IO.userError "unknown-symbol IAT coordinate absent")
  check "unknown native bytes refused"
    (!(candidateAt? loaded (BitVec.ofNat 64 (base + unknownRva)) 0x7ff04040 0 3).isSome)
  let some lowerRva := plan.layout.importAddressRva? 0 4
    | throw (IO.userError "lowercase-symbol IAT coordinate absent")
  check "lowercase native bytes refused"
    (!(candidateAt? loaded (BitVec.ofNat 64 (base + lowerRva)) 0x7ff05050 0 4).isSome)

  let some writeBinding := select? loaded writeEA 0x7ff02020
    | throw (IO.userError "WriteFile request-match selection absent")
  check "request helper pins WriteFile"
    (requestApi (.exitProcess 0) != writeBinding.api)

theorem exit_request_does_not_match_writeFile
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {ea target : BitVec 64} (binding : Binding loaded ea target)
    (isWriteFile : binding.api = .writeFile) :
    ¬ binding.MatchesRequest (.exitProcess 0) := by
  simp [Binding.MatchesRequest, requestApi, isWriteFile]

end Grass.Tests.Win32ApiDispatch
