import Grass.Assembly.Win32Constants
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.Win32Constants

open Grass.Assembly Grass.ISA.X86 Grass.Platform.Win32

def fromChars? (chars : List Char) : Option (List Grass.Assembly.Win32Constants.Result) := do
  let body ← (SourceInput.extractSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  let results := frame.program.collected.code.filterMap
    (Grass.Assembly.Win32Constants.resolve? frame)
  if results.length = 2 then some results else none

def view (result : Grass.Assembly.Win32Constants.Result) :=
  (result.constant, result.destination, result.constant.value, result.encoding.toBytes)

-- The canonical selector chooses the smaller signed representation whenever
-- it recovers the same 64-bit value.
example : Grass.Assembly.Win32Constants.selectSignedImmediate?
    GetStdHandleResult.invalidHandleValue =
      some (.i8 (BitVec.ofNat 8 GetStdHandleResult.invalidHandleValue.toNat)) := by
  decide +kernel

-- A value just above the signed imm8 range takes the checked imm32 fallback.
example : Grass.Assembly.Win32Constants.selectSignedImmediate? (128 : BitVec 64) =
    some (.i32 (128 : BitVec 32)) := by
  decide +kernel

-- A 64-bit value outside both signed immediate ranges is rejected rather than
-- truncated to its low 32 bits.
example : Grass.Assembly.Win32Constants.selectSignedImmediate?
    (0x0000000080000000 : BitVec 64) = none := by
  decide +kernel

def sample (body : List Char) : List Char :=
  (source_chars "def constantSample : MachineSource plan := ") ++
    (source_chars "withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    body ++ (source_chars "\nud2\n}")

-- Register choice is source-derived rather than fixed by the constant.
example : (fromChars? (sample (source_chars
    "mov r10d, STD_OUTPUT_HANDLE\ncmp r11, INVALID_HANDLE_VALUE"))).map
      (List.map fun result => (result.destination, result.encoding.toBytes)) =
    some [(.r10, [0x41, 0xBA, 0xF5, 0xFF, 0xFF, 0xFF]),
      (.r11, [0x49, 0x83, 0xFB, 0xFF])] := by
  decide +kernel

-- Unknown names and width/operand forms outside the two declarations reject.
example : fromChars? (sample (source_chars
    "mov ecx, UNKNOWN\ncmp rax, INVALID_HANDLE_VALUE")) = none := by
  decide +kernel
example : fromChars? (sample (source_chars
    "mov rcx, STD_OUTPUT_HANDLE\ncmp rax, INVALID_HANDLE_VALUE")) = none := by
  decide +kernel
example : fromChars? (sample (source_chars
    "mov ecx, STD_OUTPUT_HANDLE\ncmp eax, INVALID_HANDLE_VALUE")) = none := by
  decide +kernel
example : fromChars? (sample (source_chars
    "mov ecx, STD_OUTPUT_HANDLE\nmov rax, INVALID_HANDLE_VALUE")) = none := by
  decide +kernel

end Grass.Tests.Assembly.Win32Constants
