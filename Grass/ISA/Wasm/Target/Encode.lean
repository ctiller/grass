import Grass.ISA.Wasm.Target.Instr
import Grass.ISA.Wasm.Target.LEB128

/-!
# Binary encoding of one Wasm instruction

Canonical `encode`/`decode` for `Instr`: an opcode byte followed by LEB128
immediates, matching the WebAssembly Core 2.0 binary instruction encoding
(§Binary/Instructions) for this MVP integer subset. `decode` is built from a
"remainder" style `decodeAux` (mirroring `Target.LEB128`'s `...Aux`
decoders) so the per-case round-trip proof composes with the LEB128
round-trip lemmas by rewriting; the public `decode` derives the
`Grass.Target.ISA` shape (value, bytes consumed) from it by a length
subtraction, once, instead of every case tracking its own byte count.
-/
namespace Grass.ISA.Wasm.Target

open Grass.ISA.Wasm (ValType)

-- `Instr` has well over a hundred constructors (the whole MVP integer opcode
-- table); the equation-lemma bookkeeping `simp`/`rfl` need to reason about
-- `encode`/`decodeAux` on it is correspondingly larger than the default
-- elaboration budget, not because any proof step here is looping.
set_option maxHeartbeats 4000000

/-! ## Immediate encodings shared by several instructions -/

def encodeBlockType : BlockType → List UInt8
  | .empty => [0x40]
  | .val .i32 => [0x7F]
  | .val .i64 => [0x7E]

def decodeBlockTypeAux : List UInt8 → Option (BlockType × List UInt8)
  | 0x40 :: rest => some (.empty, rest)
  | 0x7F :: rest => some (.val .i32, rest)
  | 0x7E :: rest => some (.val .i64, rest)
  | _ => none

theorem decodeBlockTypeAux_encodeBlockType (bt : BlockType) (rest : List UInt8) :
    decodeBlockTypeAux (encodeBlockType bt ++ rest) = some (bt, rest) := by
  cases bt with
  | empty => rfl
  | val t => cases t <;> rfl

def encodeMemArg (m : MemArg) : List UInt8 := encodeU m.align ++ encodeU m.offset

def decodeMemArgAux (bytes : List UInt8) : Option (MemArg × List UInt8) :=
  match decodeUAux bytes with
  | none => none
  | some (align, rest) =>
      match decodeUAux rest with
      | none => none
      | some (offset, rest') => some (⟨align, offset⟩, rest')

theorem decodeMemArgAux_encodeMemArg (m : MemArg) (rest : List UInt8) :
    decodeMemArgAux (encodeMemArg m ++ rest) = some (m, rest) := by
  unfold encodeMemArg decodeMemArgAux
  rw [List.append_assoc]
  simp only [decodeUAux_encodeU]

/-- Decode one immediate, then build the instruction from it. The generic
round-trip lemma below (`withImm_encode`) discharges every single-immediate
case of `decodeAux_encode` by supplying the immediate's own round-trip lemma,
instead of one bespoke proof per instruction. -/
def withImm {α : Type} (mk : α → Instr) (dec : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Instr × List UInt8) :=
  match dec bytes with
  | none => none
  | some (v, rest) => some (mk v, rest)

theorem withImm_encode {α : Type} (mk : α → Instr) (dec : List UInt8 → Option (α × List UInt8))
    (enc : α → List UInt8)
    (roundtrip : ∀ (v : α) (rest : List UInt8), dec (enc v ++ rest) = some (v, rest))
    (v : α) (rest : List UInt8) :
    withImm mk dec (enc v ++ rest) = some (mk v, rest) := by
  unfold withImm
  rw [roundtrip v rest]

/-! ## The instruction codec -/

/-- Canonical encoding of one instruction. -/
def encode : Instr → List UInt8
  -- Control
  | .unreachable => [0x00]
  | .nop => [0x01]
  | .block bt => 0x02 :: encodeBlockType bt
  | .loop bt => 0x03 :: encodeBlockType bt
  | .if_ bt => 0x04 :: encodeBlockType bt
  | .else_ => [0x05]
  | .end_ => [0x0B]
  | .br label => 0x0C :: encodeU label
  | .brIf label => 0x0D :: encodeU label
  | .brTable labels default =>
      0x0E :: encodeU labels.length ++ (labels.map encodeU).flatten ++ encodeU default
  | .return_ => [0x0F]
  | .call func => 0x10 :: encodeU func
  | .callIndirect type table => 0x11 :: (encodeU type ++ encodeU table)
  -- Parametric
  | .drop => [0x1A]
  | .select => [0x1B]
  -- Variable
  | .localGet index => 0x20 :: encodeU index
  | .localSet index => 0x21 :: encodeU index
  | .localTee index => 0x22 :: encodeU index
  | .globalGet index => 0x23 :: encodeU index
  | .globalSet index => 0x24 :: encodeU index
  -- Memory
  | .i32Load m => 0x28 :: encodeMemArg m
  | .i64Load m => 0x29 :: encodeMemArg m
  | .i32Load8S m => 0x2C :: encodeMemArg m
  | .i32Load8U m => 0x2D :: encodeMemArg m
  | .i32Load16S m => 0x2E :: encodeMemArg m
  | .i32Load16U m => 0x2F :: encodeMemArg m
  | .i64Load8S m => 0x30 :: encodeMemArg m
  | .i64Load8U m => 0x31 :: encodeMemArg m
  | .i64Load16S m => 0x32 :: encodeMemArg m
  | .i64Load16U m => 0x33 :: encodeMemArg m
  | .i64Load32S m => 0x34 :: encodeMemArg m
  | .i64Load32U m => 0x35 :: encodeMemArg m
  | .i32Store m => 0x36 :: encodeMemArg m
  | .i64Store m => 0x37 :: encodeMemArg m
  | .i32Store8 m => 0x3A :: encodeMemArg m
  | .i32Store16 m => 0x3B :: encodeMemArg m
  | .i64Store8 m => 0x3C :: encodeMemArg m
  | .i64Store16 m => 0x3D :: encodeMemArg m
  | .i64Store32 m => 0x3E :: encodeMemArg m
  | .memorySize => [0x3F, 0x00]
  | .memoryGrow => [0x40, 0x00]
  -- Numeric constants
  | .i32Const v => 0x41 :: encodeS v.toInt
  | .i64Const v => 0x42 :: encodeS v.toInt
  -- i32 comparisons
  | .i32Eqz => [0x45]
  | .i32Eq => [0x46]
  | .i32Ne => [0x47]
  | .i32LtS => [0x48]
  | .i32LtU => [0x49]
  | .i32GtS => [0x4A]
  | .i32GtU => [0x4B]
  | .i32LeS => [0x4C]
  | .i32LeU => [0x4D]
  | .i32GeS => [0x4E]
  | .i32GeU => [0x4F]
  -- i64 comparisons
  | .i64Eqz => [0x50]
  | .i64Eq => [0x51]
  | .i64Ne => [0x52]
  | .i64LtS => [0x53]
  | .i64LtU => [0x54]
  | .i64GtS => [0x55]
  | .i64GtU => [0x56]
  | .i64LeS => [0x57]
  | .i64LeU => [0x58]
  | .i64GeS => [0x59]
  | .i64GeU => [0x5A]
  -- i32 arithmetic
  | .i32Clz => [0x67]
  | .i32Ctz => [0x68]
  | .i32Popcnt => [0x69]
  | .i32Add => [0x6A]
  | .i32Sub => [0x6B]
  | .i32Mul => [0x6C]
  | .i32DivS => [0x6D]
  | .i32DivU => [0x6E]
  | .i32RemS => [0x6F]
  | .i32RemU => [0x70]
  | .i32And => [0x71]
  | .i32Or => [0x72]
  | .i32Xor => [0x73]
  | .i32Shl => [0x74]
  | .i32ShrS => [0x75]
  | .i32ShrU => [0x76]
  | .i32Rotl => [0x77]
  | .i32Rotr => [0x78]
  -- i64 arithmetic
  | .i64Clz => [0x79]
  | .i64Ctz => [0x7A]
  | .i64Popcnt => [0x7B]
  | .i64Add => [0x7C]
  | .i64Sub => [0x7D]
  | .i64Mul => [0x7E]
  | .i64DivS => [0x7F]
  | .i64DivU => [0x80]
  | .i64RemS => [0x81]
  | .i64RemU => [0x82]
  | .i64And => [0x83]
  | .i64Or => [0x84]
  | .i64Xor => [0x85]
  | .i64Shl => [0x86]
  | .i64ShrS => [0x87]
  | .i64ShrU => [0x88]
  | .i64Rotl => [0x89]
  | .i64Rotr => [0x8A]
  -- Conversions
  | .i32WrapI64 => [0xA7]
  | .i64ExtendI32S => [0xAC]
  | .i64ExtendI32U => [0xAD]

/-- Decode one instruction from the head of `bytes`, returning it and the
unconsumed remainder. Any byte sequence this codec did not itself produce
(an opcode outside the MVP integer subset, or a truncated immediate) decodes
to `none`. -/
def decodeAux : List UInt8 → Option (Instr × List UInt8)
  -- Control
  | 0x00 :: rest => some (.unreachable, rest)
  | 0x01 :: rest => some (.nop, rest)
  | 0x02 :: rest => withImm .block decodeBlockTypeAux rest
  | 0x03 :: rest => withImm .loop decodeBlockTypeAux rest
  | 0x04 :: rest => withImm .if_ decodeBlockTypeAux rest
  | 0x05 :: rest => some (.else_, rest)
  | 0x0B :: rest => some (.end_, rest)
  | 0x0C :: rest => withImm .br decodeUAux rest
  | 0x0D :: rest => withImm .brIf decodeUAux rest
  | 0x0E :: rest =>
      match decodeUAux rest with
      | none => none
      | some (count, rest1) =>
          match decodeUVec count rest1 with
          | none => none
          | some (labels, rest2) =>
              match decodeUAux rest2 with
              | none => none
              | some (default, rest3) => some (.brTable labels default, rest3)
  | 0x0F :: rest => some (.return_, rest)
  | 0x10 :: rest => withImm .call decodeUAux rest
  | 0x11 :: rest =>
      match decodeUAux rest with
      | none => none
      | some (type, rest1) =>
          match decodeUAux rest1 with
          | none => none
          | some (table, rest2) => some (.callIndirect type table, rest2)
  -- Parametric
  | 0x1A :: rest => some (.drop, rest)
  | 0x1B :: rest => some (.select, rest)
  -- Variable
  | 0x20 :: rest => withImm .localGet decodeUAux rest
  | 0x21 :: rest => withImm .localSet decodeUAux rest
  | 0x22 :: rest => withImm .localTee decodeUAux rest
  | 0x23 :: rest => withImm .globalGet decodeUAux rest
  | 0x24 :: rest => withImm .globalSet decodeUAux rest
  -- Memory
  | 0x28 :: rest => withImm .i32Load decodeMemArgAux rest
  | 0x29 :: rest => withImm .i64Load decodeMemArgAux rest
  | 0x2C :: rest => withImm .i32Load8S decodeMemArgAux rest
  | 0x2D :: rest => withImm .i32Load8U decodeMemArgAux rest
  | 0x2E :: rest => withImm .i32Load16S decodeMemArgAux rest
  | 0x2F :: rest => withImm .i32Load16U decodeMemArgAux rest
  | 0x30 :: rest => withImm .i64Load8S decodeMemArgAux rest
  | 0x31 :: rest => withImm .i64Load8U decodeMemArgAux rest
  | 0x32 :: rest => withImm .i64Load16S decodeMemArgAux rest
  | 0x33 :: rest => withImm .i64Load16U decodeMemArgAux rest
  | 0x34 :: rest => withImm .i64Load32S decodeMemArgAux rest
  | 0x35 :: rest => withImm .i64Load32U decodeMemArgAux rest
  | 0x36 :: rest => withImm .i32Store decodeMemArgAux rest
  | 0x37 :: rest => withImm .i64Store decodeMemArgAux rest
  | 0x3A :: rest => withImm .i32Store8 decodeMemArgAux rest
  | 0x3B :: rest => withImm .i32Store16 decodeMemArgAux rest
  | 0x3C :: rest => withImm .i64Store8 decodeMemArgAux rest
  | 0x3D :: rest => withImm .i64Store16 decodeMemArgAux rest
  | 0x3E :: rest => withImm .i64Store32 decodeMemArgAux rest
  | 0x3F :: 0x00 :: rest => some (.memorySize, rest)
  | 0x40 :: 0x00 :: rest => some (.memoryGrow, rest)
  -- Numeric constants
  | 0x41 :: rest => withImm (fun v => Instr.i32Const (BitVec.ofInt 32 v)) decodeSAux rest
  | 0x42 :: rest => withImm (fun v => Instr.i64Const (BitVec.ofInt 64 v)) decodeSAux rest
  -- i32 comparisons
  | 0x45 :: rest => some (.i32Eqz, rest)
  | 0x46 :: rest => some (.i32Eq, rest)
  | 0x47 :: rest => some (.i32Ne, rest)
  | 0x48 :: rest => some (.i32LtS, rest)
  | 0x49 :: rest => some (.i32LtU, rest)
  | 0x4A :: rest => some (.i32GtS, rest)
  | 0x4B :: rest => some (.i32GtU, rest)
  | 0x4C :: rest => some (.i32LeS, rest)
  | 0x4D :: rest => some (.i32LeU, rest)
  | 0x4E :: rest => some (.i32GeS, rest)
  | 0x4F :: rest => some (.i32GeU, rest)
  -- i64 comparisons
  | 0x50 :: rest => some (.i64Eqz, rest)
  | 0x51 :: rest => some (.i64Eq, rest)
  | 0x52 :: rest => some (.i64Ne, rest)
  | 0x53 :: rest => some (.i64LtS, rest)
  | 0x54 :: rest => some (.i64LtU, rest)
  | 0x55 :: rest => some (.i64GtS, rest)
  | 0x56 :: rest => some (.i64GtU, rest)
  | 0x57 :: rest => some (.i64LeS, rest)
  | 0x58 :: rest => some (.i64LeU, rest)
  | 0x59 :: rest => some (.i64GeS, rest)
  | 0x5A :: rest => some (.i64GeU, rest)
  -- i32 arithmetic
  | 0x67 :: rest => some (.i32Clz, rest)
  | 0x68 :: rest => some (.i32Ctz, rest)
  | 0x69 :: rest => some (.i32Popcnt, rest)
  | 0x6A :: rest => some (.i32Add, rest)
  | 0x6B :: rest => some (.i32Sub, rest)
  | 0x6C :: rest => some (.i32Mul, rest)
  | 0x6D :: rest => some (.i32DivS, rest)
  | 0x6E :: rest => some (.i32DivU, rest)
  | 0x6F :: rest => some (.i32RemS, rest)
  | 0x70 :: rest => some (.i32RemU, rest)
  | 0x71 :: rest => some (.i32And, rest)
  | 0x72 :: rest => some (.i32Or, rest)
  | 0x73 :: rest => some (.i32Xor, rest)
  | 0x74 :: rest => some (.i32Shl, rest)
  | 0x75 :: rest => some (.i32ShrS, rest)
  | 0x76 :: rest => some (.i32ShrU, rest)
  | 0x77 :: rest => some (.i32Rotl, rest)
  | 0x78 :: rest => some (.i32Rotr, rest)
  -- i64 arithmetic
  | 0x79 :: rest => some (.i64Clz, rest)
  | 0x7A :: rest => some (.i64Ctz, rest)
  | 0x7B :: rest => some (.i64Popcnt, rest)
  | 0x7C :: rest => some (.i64Add, rest)
  | 0x7D :: rest => some (.i64Sub, rest)
  | 0x7E :: rest => some (.i64Mul, rest)
  | 0x7F :: rest => some (.i64DivS, rest)
  | 0x80 :: rest => some (.i64DivU, rest)
  | 0x81 :: rest => some (.i64RemS, rest)
  | 0x82 :: rest => some (.i64RemU, rest)
  | 0x83 :: rest => some (.i64And, rest)
  | 0x84 :: rest => some (.i64Or, rest)
  | 0x85 :: rest => some (.i64Xor, rest)
  | 0x86 :: rest => some (.i64Shl, rest)
  | 0x87 :: rest => some (.i64ShrS, rest)
  | 0x88 :: rest => some (.i64ShrU, rest)
  | 0x89 :: rest => some (.i64Rotl, rest)
  | 0x8A :: rest => some (.i64Rotr, rest)
  -- Conversions
  | 0xA7 :: rest => some (.i32WrapI64, rest)
  | 0xAC :: rest => some (.i64ExtendI32S, rest)
  | 0xAD :: rest => some (.i64ExtendI32U, rest)
  | _ => none

/-- Every case is one of: no immediate (`rfl` computes both sides), a single
immediate decoded by `withImm` (closed by `withImm_encode` instantiated at
that immediate's own round-trip lemma), or one of the two multi-immediate
instructions (`brTable`, `callIndirect`) closed by chaining `decodeUAux`
round trips directly. Combining these as `first` alternatives under one
`cases instr <;>`, rather than one named `case` per constructor, is what
keeps this tractable for a 100-plus constructor `Instr`: a named `case` has
to search the whole goal list by tag, which is quadratic in the constructor
count and times out here, while `<;>` applies the same alternative list to
every goal in one pass. -/
theorem decodeAux_encode (instr : Instr) (rest : List UInt8) :
    decodeAux (encode instr ++ rest) = some (instr, rest) := by
  cases instr <;>
    first
      | rfl
      | (simp only [encode, decodeAux, List.cons_append,
            withImm_encode _ _ _ decodeBlockTypeAux_encodeBlockType]
         done)
      | (simp only [encode, decodeAux, List.cons_append,
            withImm_encode _ _ _ decodeUAux_encodeU]
         done)
      | (simp only [encode, decodeAux, List.cons_append,
            withImm_encode _ _ _ decodeMemArgAux_encodeMemArg]
         done)
      | (simp only [encode, decodeAux, List.append_assoc, List.cons_append]
         rw [decodeUAux_encodeU]
         simp only [decodeUVec_encode]
         rw [decodeUAux_encodeU]
         done)
      | (simp only [encode, decodeAux, List.cons_append]
         rw [decodeUAux_encodeU]
         simp only
         rw [decodeUAux_encodeU]
         done)
      | (simp only [encode, decodeAux, List.cons_append]
         rw [withImm, decodeSAux_encodeS]
         simp only [BitVec.ofInt_toInt]
         done)

/-- Decode one instruction from the head of `bytes`, returning it and the
number of bytes consumed, matching `Grass.Target.ISA.decode`'s shape. -/
def decode (bytes : List UInt8) : Option (Instr × Nat) :=
  match decodeAux bytes with
  | none => none
  | some (instr, rest) => some (instr, bytes.length - rest.length)

theorem decode_encode (instr : Instr) (rest : List UInt8) :
    decode (encode instr ++ rest) = some (instr, (encode instr).length) := by
  unfold decode
  rw [decodeAux_encode]
  have h : (encode instr ++ rest).length = (encode instr).length + rest.length :=
    List.length_append ..
  simp only [h, Nat.add_sub_cancel]

/-- Case-free: if `encode instr` were `[]`, `decodeAux_encode` at `rest := []`
would give `decodeAux [] = some (instr, [])`, but `decodeAux []` computes to
`none`. This sidesteps re-splitting on all of `Instr` a second time. -/
theorem encode_pos (instr : Instr) : 0 < (encode instr).length := by
  rcases he : encode instr with _ | ⟨b, t⟩
  · exfalso
    have round := decodeAux_encode instr []
    rw [he, List.nil_append] at round
    simp [decodeAux] at round
  · simp

end Grass.ISA.Wasm.Target
