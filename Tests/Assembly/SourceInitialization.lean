import Grass.Assembly.SourceInitialization
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceInitialization

open Grass.Assembly Grass.ISA.X86

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def fromChars? (chars : List Char) (rootOffset : Nat := 0) :
    Option Grass.Assembly.SourceInitialization.Result := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  Grass.Assembly.SourceInitialization.resolve? frame rootOffset

-- The initializer is generated from the exact authored header declaration.
example : (fromChars? authored).map (fun result => result.entries.map
    (fun entry => (entry.declaration.name, entry.declaration.initialValue.toNat,
      entry.store.displacement))) = some [("transferred", 0, 40)] := by
  decide +kernel
example : (fromChars? authored).map (fun result => result.entries.map
    (fun entry => (entry.store.input.slot, entry.store.input.value,
      entry.store.writeBytes))) = some [("transferred", (0 : BitVec 32), [0, 0, 0, 0])] := by
  decide +kernel

def sample (locals : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := ") ++ locals ++
    (source_chars " withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    (source_chars "ud2\n}")

-- Nonzero UInt32 values flow into little-endian stores without a body line.
example : (fromChars? (sample (source_chars
    "withStack (value : UInt32 := 305419896)"))).map
      (fun result => result.entries.map
        (fun entry => (entry.declaration.initialValue.toNat, entry.store.writeBytes))) =
    some [(305419896, [0x78, 0x56, 0x34, 0x12])] := by
  decide +kernel

-- Declaration order is output order, and changing it changes the resolver's
-- slot assignment rather than dropping or sorting initializers.
example : (fromChars? (sample (source_chars
    "withStack (second : UInt32 := 2) withStack (first : UInt32 := 1)")) 16).map
      (fun result => (result.rootOffset, result.entries.map
        (fun entry => (entry.declaration.name, entry.declaration.initialValue.toNat,
          entry.store.displacement)))) =
    some (16, [("second", 2, 40), ("first", 1, 44)]) := by
  decide +kernel

-- Every returned entry retains the shared resolver equation and therefore the
-- width, range, value bytes, and decoder laws.
example : ∀ result entry,
    fromChars? authored = some result → entry ∈ result.entries →
      entry.store.range.size = 4 ∧
      (result.frame.layout.frameRange.shift result.rootOffset).Contains entry.store.range ∧
      entry.store.writeBytes = le32
        (BitVec.ofNat 32 entry.declaration.initialValue.toNat) ∧
      decodeInsn entry.store.encoding.toBytes = .ok (entry.store.encoding, []) := by
  intro result entry _ member
  exact ⟨result.entry_width member, result.entry_range_in_frame member,
    result.entry_writeBytes member, by
      simpa using result.entry_encoding_decodes member []⟩

end Grass.Tests.Assembly.SourceInitialization
