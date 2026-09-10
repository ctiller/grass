import Grass.ISA.AArch64.Control
import Grass.Artifact.Binary.Endian

/-!
The shared binary codec connects an exact four-byte source prefix to the A64
instruction word. These are source/body relations, not executable-memory fetch
receipts. A downstream machine proof must establish code provenance, current PC,
fetch access and profile admission; parser success supplies none of those facts.
-/
namespace Grass.ISA.AArch64

open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- Use the existing endian writer rather than another ISA byte implementation. -/
def emitWord (word : BitVec 32) : Std.Logical.ByteArray := writeLittleEndian (count := 4) word

@[simp] theorem emitWord_length (word : BitVec 32) : (emitWord word).length = 4 :=
  @length_writeLittleEndian 4 word

@[simp] theorem parse_emitWord (word : BitVec 32) :
    takeLittleEndian 4 (emitWord word) = .done word Vec.empty :=
  @takeLittleEndian_writeLittleEndian 4 word

/-- Retain the original source and the exact parser suffix in the result type. -/
structure SourceWord (bytes : Std.Logical.ByteArray) where
  word : BitVec 32
  rest : Std.Logical.ByteArray
  parsed : takeLittleEndian 4 bytes = .done word rest

/-- Pack successful parses into `SourceWord`, whose `SourceWord.parsed` field
records the exact suffix equation; forward the parser's refusal constructors.
`readSource_needMore` proves forwarding of the short-input result. -/
def readSource (bytes : Std.Logical.ByteArray) : ParseResult (SourceWord bytes) :=
  match h : takeLittleEndian 4 bytes with
  | .done word rest => .done ⟨word, rest, h⟩ rest
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

theorem readSource_needMore {bytes : Std.Logical.ByteArray} {hint : Option Nat}
    (h : takeLittleEndian 4 bytes = .needMore hint) : readSource bytes = .needMore hint := by
  unfold readSource
  split <;> simp_all

/-- A source prefix and any admitted outcome of the fixed body relation. -/
structure SourceBodyStep (bytes : Std.Logical.ByteArray) (before : Cpu)
    (outcome : BodyOutcome) where
  source : SourceWord bytes
  step : BodyStep source.word before outcome

/-- Emitting a CBZ establishes a source/body step for every CPU, not a machine
execution theorem or an assertion that a target instruction fetch will succeed. -/
def CompareZero.sourceStep (instruction : CompareZero) (before : Cpu) :
    SourceBodyStep (emitWord instruction.encode) before (.next (instruction.execute before)) :=
  ⟨⟨instruction.encode, Vec.empty, parse_emitWord instruction.encode⟩,
    .cbz instruction (CompareZero.decode_encode instruction)⟩

def SupervisorCall.sourceStep (immediate : BitVec 16) (before : Cpu) :
    SourceBodyStep (emitWord (SupervisorCall.encode immediate)) before (.supervisor immediate) :=
  ⟨⟨SupervisorCall.encode immediate, Vec.empty, parse_emitWord (SupervisorCall.encode immediate)⟩,
    .svc immediate (SupervisorCall.decode_encode immediate)⟩

/-- All admitted source/body transitions preserve exact parsing and branch or
exception-request evidence. This theorem does not erase unsupported full-machine
outcomes: they remain an explicit obligation outside this body projection. -/
theorem SourceBodyStep.cases {bytes : Std.Logical.ByteArray} {before : Cpu}
    {outcome : BodyOutcome} (execution : SourceBodyStep bytes before outcome) :
    (∃ instruction : CompareZero, instruction.encode = execution.source.word ∧
      outcome = .next (instruction.execute before) ∧
      ((instruction.isZero before = true ∧
        (instruction.execute before).pc = before.pc + instruction.offset) ∨
       (instruction.isZero before = false ∧
        (instruction.execute before).pc = before.pc + 4))) ∨
    (∃ immediate, SupervisorCall.encode immediate = execution.source.word ∧
      outcome = .supervisor immediate) := by
  rcases bodyStep_cases execution.step with ⟨instruction, decoded, result, control⟩ |
      ⟨immediate, decoded, result⟩
  · exact .inl ⟨instruction, CompareZero.decode_sound decoded, result, control⟩
  · exact .inr ⟨immediate, SupervisorCall.decode_sound decoded, result⟩

end Grass.ISA.AArch64
