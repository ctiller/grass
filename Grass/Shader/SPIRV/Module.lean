import Std.Tactic.BVDecide

/-!
# A SPIR-V module: words, instructions, and their byte encoding

This module gives `Grass.Target.ShaderLanguage.Module` a concrete shape for
SPIR-V: a header plus a flat list of instructions, each a typed constructor
over the opcode vocabulary a Vulkan/SPIR-V shading pipeline needs (entry
points, types, constants, variables, and the arithmetic/composite/control
instructions a small shader body uses). It proves the encode/decode round
trip the seam requires; it is not a validator, a control-flow model, or an
execution semantics for any of these instructions.

Opcode and word-layout facts are from the Khronos SPIR-V 1.5 unified
specification: https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html

## Where this diverges from the Khronos physical binary

Two choices below are Grass's own and are not literally the Khronos wire
format, because the universally-quantified round trip this file proves
(`decode (encode m) = some m`, for every `m : Module`, with no side
condition) has to hold for pathological values of the type, not just for
modules a real compiler would emit:

* Every instruction's total operand-word count is capped at `maxOperandWords`
  (65534, i.e. instruction word count ≤ 65535) so the leading word's 16-bit
  length field never wraps. This is not an invented restriction — it is the
  real SPIR-V physical limit — but here it is enforced by a subtype
  (`Instr` bundles an `InstrData` with a decidable proof of the bound)
  instead of being merely conventional, because nothing else makes the
  round trip a theorem instead of a convention.
* `OpEntryPoint`'s name is length-prefixed (one `Word` holding the UTF-8
  byte count, then the padded bytes) rather than Khronos's NUL-terminated
  literal string. A NUL-terminated encoding round-trips only for names
  without an embedded NUL byte, which would need the same kind of bound;
  length-prefixing gets an unconditional round trip for free from the same
  operand-count cap, at the cost of not being byte-identical to a real
  `OpEntryPoint`. A `spirv-val` differential writer, if one is ever built,
  owns closing this gap; it is out of scope this round.

Every other instruction word matches the real physical layout exactly
(opcode in the low 16 bits, word count in the high 16 bits of the first
word; `resultType` before `result` where both are present; operands in
Khronos operand order).
-/

namespace Grass.Shader.SPIRV.Module

/-! ## Words and bytes -/

/-- A 32-bit SPIR-V word. -/
abbrev Word := UInt32

/-- A SPIR-V `<id>`: a result or reference into the module's ID space. -/
abbrev Id := Word

def Word.b0 (w : Word) : UInt8 := UInt8.ofBitVec (w.toBitVec.extractLsb' 0 8)
def Word.b1 (w : Word) : UInt8 := UInt8.ofBitVec (w.toBitVec.extractLsb' 8 8)
def Word.b2 (w : Word) : UInt8 := UInt8.ofBitVec (w.toBitVec.extractLsb' 16 8)
def Word.b3 (w : Word) : UInt8 := UInt8.ofBitVec (w.toBitVec.extractLsb' 24 8)

/-- A word's bytes, least significant first. -/
def Word.toBytes (w : Word) : List UInt8 := [w.b0, w.b1, w.b2, w.b3]

/-- Reassemble a word from four little-endian bytes. -/
def Word.ofBytes (byte0 byte1 byte2 byte3 : UInt8) : Word :=
  UInt32.ofBitVec (byte3.toBitVec ++ byte2.toBitVec ++ byte1.toBitVec ++ byte0.toBitVec)

theorem Word.ofBytes_toBytes (w : Word) : Word.ofBytes w.b0 w.b1 w.b2 w.b3 = w := by
  simp only [Word.ofBytes, Word.b0, Word.b1, Word.b2, Word.b3]
  cases w with
  | ofBitVec w' => congr 1; bv_decide

theorem Word.toBytes_ofBytes (a b c d : UInt8) : Word.toBytes (Word.ofBytes a b c d) = [a, b, c, d] := by
  have h0 : Word.b0 (Word.ofBytes a b c d) = a := by
    simp only [Word.b0, Word.ofBytes]
    cases a with | ofBitVec a' => cases b with | ofBitVec b' => cases c with | ofBitVec c' =>
      cases d with | ofBitVec d' => congr 1; bv_decide
  have h1 : Word.b1 (Word.ofBytes a b c d) = b := by
    simp only [Word.b1, Word.ofBytes]
    cases a with | ofBitVec a' => cases b with | ofBitVec b' => cases c with | ofBitVec c' =>
      cases d with | ofBitVec d' => congr 1; bv_decide
  have h2 : Word.b2 (Word.ofBytes a b c d) = c := by
    simp only [Word.b2, Word.ofBytes]
    cases a with | ofBitVec a' => cases b with | ofBitVec b' => cases c with | ofBitVec c' =>
      cases d with | ofBitVec d' => congr 1; bv_decide
  have h3 : Word.b3 (Word.ofBytes a b c d) = d := by
    simp only [Word.b3, Word.ofBytes]
    cases a with | ofBitVec a' => cases b with | ofBitVec b' => cases c with | ofBitVec c' =>
      cases d with | ofBitVec d' => congr 1; bv_decide
  simp only [Word.toBytes, h0, h1, h2, h3]

/-- A word list as little-endian bytes. -/
def wordsToBytes (ws : List Word) : List UInt8 := ws.flatMap Word.toBytes

/-- Bytes grouped back into words, four at a time. Drops a non-multiple-of-4
remainder rather than failing; callers that need to reject malformed input
check `bytes.length % 4` first. -/
def bytesToWords : List UInt8 → List Word
  | a :: b :: c :: d :: rest => Word.ofBytes a b c d :: bytesToWords rest
  | _ => []

theorem bytesToWords_wordsToBytes (ws : List Word) : bytesToWords (wordsToBytes ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      show bytesToWords (w.b0 :: w.b1 :: w.b2 :: w.b3 :: wordsToBytes ws) = w :: ws
      rw [bytesToWords, Word.ofBytes_toBytes, ih]

theorem wordsToBytes_bytesToWords : ∀ bytes : List UInt8, bytes.length % 4 = 0 →
    wordsToBytes (bytesToWords bytes) = bytes
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | a :: b :: c :: d :: rest, h => by
      have hrest : rest.length % 4 = 0 := by
        simp only [List.length_cons] at h; omega
      have ih := wordsToBytes_bytesToWords rest hrest
      show Word.toBytes (Word.ofBytes a b c d) ++ wordsToBytes (bytesToWords rest) = a :: b :: c :: d :: rest
      rw [ih, Word.toBytes_ofBytes]; rfl

theorem length_bytesToWords : ∀ bytes : List UInt8, bytes.length % 4 = 0 →
    4 * (bytesToWords bytes).length = bytes.length
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | a :: b :: c :: d :: rest, h => by
      have hrest : rest.length % 4 = 0 := by
        simp only [List.length_cons] at h; omega
      have ih := length_bytesToWords rest hrest
      show 4 * (Word.ofBytes a b c d :: bytesToWords rest).length = (a :: b :: c :: d :: rest).length
      simp only [List.length_cons]; omega

/-- `UInt32.ofNat` reduces modulo `2^32`, stated once here since core states
it only for the numeral-literal spelling `OfNat.ofNat`. -/
theorem Word.toNat_ofNat' (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  simp [UInt32.ofNat, UInt32.toNat]

/-! ## A bounded, unsigned 32-bit count field

Every place a length is written into one `Word` (an instruction's operand
count, a string's byte count) needs `n < 2 ^ 32` to read back exactly. -/

theorem packCount_unpackCount (n : Nat) (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  rw [Word.toNat_ofNat']; omega

/-! ## Strings, length-prefixed and word-padded

Encoded as one length word (the UTF-8 byte count) followed by the UTF-8 bytes
padded with zero bytes to a word boundary. See the module docstring for why
this is length-prefixed rather than NUL-terminated. -/

def stringBytes (s : String) : List UInt8 := s.toUTF8.data.toList

def bytesToString? (bytes : List UInt8) : Option String :=
  String.fromUTF8? (ByteArray.mk bytes.toArray)

theorem bytesToString?_stringBytes (s : String) : bytesToString? (stringBytes s) = some s := by
  show String.fromUTF8? (ByteArray.mk s.toUTF8.data.toList.toArray) = some s
  rw [show ByteArray.mk s.toUTF8.data.toList.toArray = s.toUTF8 from by simp]
  unfold String.fromUTF8?
  rw [String.toUTF8_eq_toByteArray, dif_pos s.isValidUTF8]
  rfl

/-- Pad a byte list with zero bytes to the next multiple of 4. -/
def padTo4 (bytes : List UInt8) : List UInt8 :=
  bytes ++ List.replicate ((4 - bytes.length % 4) % 4) 0

theorem length_padTo4 (bytes : List UInt8) : (padTo4 bytes).length % 4 = 0 := by
  simp only [padTo4, List.length_append, List.length_replicate]; omega

theorem take_padTo4 (bytes : List UInt8) : (padTo4 bytes).take bytes.length = bytes := by
  simp [padTo4]

/-- A string's wire words: one length word, then its padded UTF-8 bytes. -/
def packString (s : String) : List Word :=
  UInt32.ofNat (stringBytes s).length :: bytesToWords (padTo4 (stringBytes s))

/-- Recover a string and the unconsumed words from the front of a word list. -/
def unpackString? (ws : List Word) : Option (String × List Word) :=
  match ws with
  | [] => none
  | lenWord :: rest =>
      let byteLen := lenWord.toNat
      let wordCount := (byteLen + 3) / 4
      let strBytes := (wordsToBytes (rest.take wordCount)).take byteLen
      match bytesToString? strBytes with
      | none => none
      | some s => some (s, rest.drop wordCount)

theorem unpackString?_packString (s : String) (tail : List Word)
    (hbound : (stringBytes s).length < 2 ^ 32) :
    unpackString? (packString s ++ tail) = some (s, tail) := by
  have hlen : (UInt32.ofNat (stringBytes s).length).toNat = (stringBytes s).length :=
    packCount_unpackCount _ hbound
  have hmod : (padTo4 (stringBytes s)).length % 4 = 0 := length_padTo4 _
  have hwc : ((stringBytes s).length + 3) / 4 = (bytesToWords (padTo4 (stringBytes s))).length := by
    have := length_bytesToWords (padTo4 (stringBytes s)) hmod
    have hpad : (padTo4 (stringBytes s)).length = (stringBytes s).length +
        (4 - (stringBytes s).length % 4) % 4 := by simp [padTo4]
    omega
  show unpackString?
      (UInt32.ofNat (stringBytes s).length :: (bytesToWords (padTo4 (stringBytes s)) ++ tail)) =
      some (s, tail)
  simp only [unpackString?, hlen]
  rw [show ((stringBytes s).length + 3) / 4 = (bytesToWords (padTo4 (stringBytes s))).length from hwc]
  rw [List.take_left, wordsToBytes_bytesToWords _ hmod, take_padTo4, bytesToString?_stringBytes]
  simp

/-! ## The instruction word count field

Instruction word count is a 16-bit field packed with the opcode in a single
leading word (`highWord ||| lowByte`, here computed over `Nat` since a plain
multiply-and-mod is `omega`-closable, unlike the bit-shift spelling of the
same fact). Grass caps operand-word count at `maxOperandWords` so a
`Instr` (below) can never describe an instruction that would overflow this
field: the round trip is unconditional because no over-long instruction is a
value of the type. -/

/-- Every instruction's operand-word count is capped so the leading word's
16-bit length field (`operandWords.length + 1`) never wraps. -/
def maxOperandWords : Nat := 65534

def packHeader (opcode totalWordCount : Nat) : Word := UInt32.ofNat (totalWordCount * 65536 + opcode)
def unpackHeaderOpcode (w : Word) : Nat := w.toNat % 65536
def unpackHeaderCount (w : Word) : Nat := w.toNat / 65536

theorem decodeOne_header (opcode : Nat) (hopcode : opcode < 65536) (operands rest : List Word)
    (hbound : operands.length ≤ maxOperandWords) :
    unpackHeaderOpcode (packHeader opcode (operands.length + 1)) = opcode ∧
    unpackHeaderCount (packHeader opcode (operands.length + 1)) = operands.length + 1 ∧
    (operands ++ rest).take operands.length = operands ∧
    (operands ++ rest).drop operands.length = rest := by
  refine ⟨?_, ?_, by simp, by simp⟩ <;>
  · simp only [packHeader, unpackHeaderOpcode, unpackHeaderCount, Word.toNat_ofNat']
    have : (operands.length + 1) * 65536 + opcode < 2 ^ 32 := by unfold maxOperandWords at hbound; omega
    rw [Nat.mod_eq_of_lt this]; omega

/-! ## Instructions

The opcode vocabulary Spike 5's vertex and fragment shaders need: entry
points, the scalar/vector/matrix/pointer/function/struct type declarations,
constants, variables, the single-block function shape (`OpFunction` /
`OpLabel` / body / `OpReturn` / `OpFunctionEnd`), memory access
(`OpLoad`/`OpStore`/`OpAccessChain`), the two composite instructions from
`Grass.ISA.SPIRV.Composite`'s bounded family, the vector/matrix and
floating-point arithmetic the cube's rotation needs, and `OpExtInst` for the
GLSL.std.450 `Sin`/`Cos` extended instructions. Opcode numbers are the
Khronos SPIR-V 1.5 unified grammar's. -/

inductive InstrData where
  | opCapability (capability : Word)
  | opMemoryModel (addressing : Word) (memoryModel : Word)
  | opEntryPoint (model : Word) (function : Id) (name : String) (interface : List Id)
  | opExecutionMode (function : Id) (mode : Word) (literals : List Word)
  | opDecorate (target : Id) (decoration : Word) (extra : List Word)
  | opMemberDecorate (structType : Id) (member : Word) (decoration : Word) (extra : List Word)
  | opTypeVoid (result : Id)
  | opTypeBool (result : Id)
  | opTypeInt (result : Id) (width : Word) (signed : Word)
  | opTypeFloat (result : Id) (width : Word)
  | opTypeVector (result : Id) (component : Id) (count : Word)
  | opTypeMatrix (result : Id) (column : Id) (count : Word)
  | opTypePointer (result : Id) (storage : Word) (pointee : Id)
  | opTypeFunction (result : Id) (returnType : Id) (params : List Id)
  | opTypeStruct (result : Id) (members : List Id)
  | opConstant (resultType : Id) (result : Id) (value : Word)
  | opVariable (resultType : Id) (result : Id) (storage : Word) (initializer : Option Id)
  | opFunction (resultType : Id) (result : Id) (control : Word) (functionType : Id)
  | opLabel (result : Id)
  | opLoad (resultType : Id) (result : Id) (pointer : Id)
  | opStore (pointer : Id) (object : Id)
  | opAccessChain (resultType : Id) (result : Id) (base : Id) (indices : List Id)
  | opCompositeExtract (resultType : Id) (result : Id) (composite : Id) (indices : List Word)
  | opCompositeConstruct (resultType : Id) (result : Id) (constituents : List Id)
  | opVectorTimesMatrix (resultType : Id) (result : Id) (vector : Id) (matrix : Id)
  | opMatrixTimesVector (resultType : Id) (result : Id) (matrix : Id) (vector : Id)
  | opFMul (resultType : Id) (result : Id) (a : Id) (b : Id)
  | opFAdd (resultType : Id) (result : Id) (a : Id) (b : Id)
  | opFSub (resultType : Id) (result : Id) (a : Id) (b : Id)
  | opExtInst (resultType : Id) (result : Id) (set : Id) (instruction : Word) (operands : List Id)
  | opReturn
  | opFunctionEnd
deriving DecidableEq, Repr

/-- The Khronos SPIR-V 1.5 opcode number of an instruction. -/
def InstrData.opcode : InstrData → Nat
  | .opCapability .. => 17
  | .opMemoryModel .. => 14
  | .opEntryPoint .. => 15
  | .opExecutionMode .. => 16
  | .opDecorate .. => 71
  | .opMemberDecorate .. => 72
  | .opTypeVoid .. => 19
  | .opTypeBool .. => 20
  | .opTypeInt .. => 21
  | .opTypeFloat .. => 22
  | .opTypeVector .. => 23
  | .opTypeMatrix .. => 24
  | .opTypePointer .. => 32
  | .opTypeFunction .. => 33
  | .opTypeStruct .. => 30
  | .opConstant .. => 43
  | .opVariable .. => 59
  | .opFunction .. => 54
  | .opLabel .. => 248
  | .opLoad .. => 61
  | .opStore .. => 62
  | .opAccessChain .. => 65
  | .opCompositeExtract .. => 81
  | .opCompositeConstruct .. => 80
  | .opVectorTimesMatrix .. => 144
  | .opMatrixTimesVector .. => 145
  | .opFMul .. => 133
  | .opFAdd .. => 129
  | .opFSub .. => 131
  | .opExtInst .. => 12
  | .opReturn => 253
  | .opFunctionEnd => 56

theorem InstrData.opcode_lt (data : InstrData) : data.opcode < 65536 := by
  cases data <;> simp only [InstrData.opcode] <;> omega

/-- The instruction's operand words, in Khronos physical operand order,
excluding the leading opcode/word-count word. -/
def InstrData.operandWords : InstrData → List Word
  | .opCapability capability => [capability]
  | .opMemoryModel addressing memoryModel => [addressing, memoryModel]
  | .opEntryPoint model function name interface => model :: function :: (packString name ++ interface)
  | .opExecutionMode function mode literals => function :: mode :: literals
  | .opDecorate target decoration extra => target :: decoration :: extra
  | .opMemberDecorate structType member decoration extra => structType :: member :: decoration :: extra
  | .opTypeVoid result => [result]
  | .opTypeBool result => [result]
  | .opTypeInt result width signed => [result, width, signed]
  | .opTypeFloat result width => [result, width]
  | .opTypeVector result component count => [result, component, count]
  | .opTypeMatrix result column count => [result, column, count]
  | .opTypePointer result storage pointee => [result, storage, pointee]
  | .opTypeFunction result returnType params => result :: returnType :: params
  | .opTypeStruct result members => result :: members
  | .opConstant resultType result value => [resultType, result, value]
  | .opVariable resultType result storage initializer => resultType :: result :: storage :: initializer.toList
  | .opFunction resultType result control functionType => [resultType, result, control, functionType]
  | .opLabel result => [result]
  | .opLoad resultType result pointer => [resultType, result, pointer]
  | .opStore pointer object => [pointer, object]
  | .opAccessChain resultType result base indices => resultType :: result :: base :: indices
  | .opCompositeExtract resultType result composite indices => resultType :: result :: composite :: indices
  | .opCompositeConstruct resultType result constituents => resultType :: result :: constituents
  | .opVectorTimesMatrix resultType result vector matrix => [resultType, result, vector, matrix]
  | .opMatrixTimesVector resultType result matrix vector => [resultType, result, matrix, vector]
  | .opFMul resultType result a b => [resultType, result, a, b]
  | .opFAdd resultType result a b => [resultType, result, a, b]
  | .opFSub resultType result a b => [resultType, result, a, b]
  | .opExtInst resultType result set instruction operands =>
      resultType :: result :: set :: instruction :: operands
  | .opReturn => []
  | .opFunctionEnd => []

/-- An instruction is well formed exactly when its total encoded word count
(the leading word plus its operands) fits SPIR-V's 16-bit length field. -/
def InstrData.wellFormed (data : InstrData) : Bool := decide (data.operandWords.length ≤ maxOperandWords)

/-- A SPIR-V instruction: typed data bundled with the proof that it encodes
to a physically representable word count. -/
abbrev Instr := { data : InstrData // data.wellFormed = true }

/-- The instruction's exact wire words: the packed opcode/length word,
followed by its operands. -/
def Instr.toWords (i : Instr) : List Word :=
  packHeader i.val.opcode (i.val.operandWords.length + 1) :: i.val.operandWords

/-- Reconstruct one instruction's data from its opcode and its (already
length-bounded) operand words. `none` for any opcode/shape this vocabulary
does not cover. -/
def dispatch (opcode : Nat) (operands : List Word) : Option InstrData :=
  match opcode with
  | 17 => match operands with | [capability] => some (.opCapability capability) | _ => none
  | 14 => match operands with | [addressing, memoryModel] => some (.opMemoryModel addressing memoryModel) | _ => none
  | 15 => match operands with
      | model :: function :: rest =>
          (unpackString? rest).map (fun (name, interface) => .opEntryPoint model function name interface)
      | _ => none
  | 16 => match operands with
      | function :: mode :: literals => some (.opExecutionMode function mode literals)
      | _ => none
  | 71 => match operands with
      | target :: decoration :: extra => some (.opDecorate target decoration extra)
      | _ => none
  | 72 => match operands with
      | structType :: member :: decoration :: extra => some (.opMemberDecorate structType member decoration extra)
      | _ => none
  | 19 => match operands with | [result] => some (.opTypeVoid result) | _ => none
  | 20 => match operands with | [result] => some (.opTypeBool result) | _ => none
  | 21 => match operands with | [result, width, signed] => some (.opTypeInt result width signed) | _ => none
  | 22 => match operands with | [result, width] => some (.opTypeFloat result width) | _ => none
  | 23 => match operands with
      | [result, component, count] => some (.opTypeVector result component count) | _ => none
  | 24 => match operands with | [result, column, count] => some (.opTypeMatrix result column count) | _ => none
  | 32 => match operands with | [result, storage, pointee] => some (.opTypePointer result storage pointee) | _ => none
  | 33 => match operands with
      | result :: returnType :: params => some (.opTypeFunction result returnType params)
      | _ => none
  | 30 => match operands with | result :: members => some (.opTypeStruct result members) | _ => none
  | 43 => match operands with | [resultType, result, value] => some (.opConstant resultType result value) | _ => none
  | 59 => match operands with
      | [resultType, result, storage] => some (.opVariable resultType result storage none)
      | [resultType, result, storage, initializer] => some (.opVariable resultType result storage (some initializer))
      | _ => none
  | 54 => match operands with
      | [resultType, result, control, functionType] => some (.opFunction resultType result control functionType)
      | _ => none
  | 248 => match operands with | [result] => some (.opLabel result) | _ => none
  | 61 => match operands with | [resultType, result, pointer] => some (.opLoad resultType result pointer) | _ => none
  | 62 => match operands with | [pointer, object] => some (.opStore pointer object) | _ => none
  | 65 => match operands with
      | resultType :: result :: base :: indices => some (.opAccessChain resultType result base indices)
      | _ => none
  | 81 => match operands with
      | resultType :: result :: composite :: indices => some (.opCompositeExtract resultType result composite indices)
      | _ => none
  | 80 => match operands with
      | resultType :: result :: constituents => some (.opCompositeConstruct resultType result constituents)
      | _ => none
  | 144 => match operands with
      | [resultType, result, vector, matrix] => some (.opVectorTimesMatrix resultType result vector matrix)
      | _ => none
  | 145 => match operands with
      | [resultType, result, matrix, vector] => some (.opMatrixTimesVector resultType result matrix vector)
      | _ => none
  | 133 => match operands with | [resultType, result, a, b] => some (.opFMul resultType result a b) | _ => none
  | 129 => match operands with | [resultType, result, a, b] => some (.opFAdd resultType result a b) | _ => none
  | 131 => match operands with | [resultType, result, a, b] => some (.opFSub resultType result a b) | _ => none
  | 12 => match operands with
      | resultType :: result :: set :: instruction :: rest =>
          some (.opExtInst resultType result set instruction rest)
      | _ => none
  | 253 => match operands with | [] => some .opReturn | _ => none
  | 56 => match operands with | [] => some .opFunctionEnd | _ => none
  | _ => none

/-- Decode exactly one instruction from the front of a word list, returning
its data and the unconsumed suffix. -/
def decodeOne (words : List Word) : Option (Instr × List Word) :=
  match words with
  | [] => none
  | header :: tail =>
      let opcode := unpackHeaderOpcode header
      let totalCount := unpackHeaderCount header
      if totalCount = 0 then none else
      let operandCount := totalCount - 1
      if tail.length < operandCount then none else
      let operands := tail.take operandCount
      let rest := tail.drop operandCount
      match dispatch opcode operands with
      | none => none
      | some data => if hwf : data.wellFormed = true then some (⟨data, hwf⟩, rest) else none

/-- The generic plumbing of `decodeOne` (header round trip, then operand
framing) closes uniformly for every opcode; only the opcode-specific
`dispatch opcode operands = some data` step differs per instruction. -/
theorem decodeOne_general (opcode : Nat) (hopcode : opcode < 65536) (operands rest : List Word)
    (hbound : operands.length ≤ maxOperandWords) (data : InstrData)
    (hdispatch : dispatch opcode operands = some data) (hwf : data.wellFormed = true) :
    decodeOne (packHeader opcode (operands.length + 1) :: (operands ++ rest)) = some (⟨data, hwf⟩, rest) := by
  have hb := decodeOne_header opcode hopcode operands rest hbound
  show (
    let header := packHeader opcode (operands.length + 1)
    let tail := operands ++ rest
    let opcode' := unpackHeaderOpcode header
    let totalCount := unpackHeaderCount header
    if totalCount = 0 then (none : Option (Instr × List Word)) else
    let operandCount := totalCount - 1
    if tail.length < operandCount then none else
    let operands' := tail.take operandCount
    let rest' := tail.drop operandCount
    match dispatch opcode' operands' with
    | none => none
    | some data' => if hwf' : data'.wellFormed = true then some (⟨data', hwf'⟩, rest') else none
  ) = some (⟨data, hwf⟩, rest)
  simp only [hb.1, hb.2.1]
  rw [if_neg (by omega : ¬ operands.length + 1 = 0)]
  have htail : ¬ (operands ++ rest).length < operands.length + 1 - 1 := by simp
  rw [if_neg htail]
  have hopeq : operands.length + 1 - 1 = operands.length := by omega
  rw [hopeq, hb.2.2.1, hb.2.2.2, hdispatch]
  simp only [dif_pos hwf]

/-- The seam's word-level round trip, one instruction at a time: decoding an
encoded instruction followed by any suffix recovers exactly that instruction
and that suffix. -/
theorem Instr.decode_encode (i : Instr) (rest : List Word) :
    decodeOne (Instr.toWords i ++ rest) = some (i, rest) := by
  obtain ⟨data, hwf⟩ := i
  have hbound : data.operandWords.length ≤ maxOperandWords := by
    simpa [InstrData.wellFormed] using hwf
  show decodeOne (packHeader data.opcode (data.operandWords.length + 1) :: (data.operandWords ++ rest)) =
    some (⟨data, hwf⟩, rest)
  cases data with
  | opCapability capability => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opMemoryModel addressing memoryModel => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opExecutionMode function mode literals => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opDecorate target decoration extra => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opMemberDecorate structType member decoration extra =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeVoid result => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeBool result => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeInt result width signed => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeFloat result width => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeVector result component count => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeMatrix result column count => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypePointer result storage pointee => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeFunction result returnType params => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opTypeStruct result members => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opConstant resultType result value => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opVariable resultType result storage initializer =>
      cases initializer with
      | none => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
      | some initializer => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opFunction resultType result control functionType => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opLabel result => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opLoad resultType result pointer => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opStore pointer object => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opAccessChain resultType result base indices => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opCompositeExtract resultType result composite indices =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opCompositeConstruct resultType result constituents =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opVectorTimesMatrix resultType result vector matrix =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opMatrixTimesVector resultType result matrix vector =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opFMul resultType result a b => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opFAdd resultType result a b => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opFSub resultType result a b => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opExtInst resultType result set instruction operands =>
      exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opReturn => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opFunctionEnd => exact decodeOne_general _ (InstrData.opcode_lt _) _ rest hbound _ rfl hwf
  | opEntryPoint model function name interface =>
      have heq : (InstrData.opEntryPoint model function name interface).operandWords.length =
          2 + (1 + (bytesToWords (padTo4 (stringBytes name))).length) + interface.length := by
        simp [InstrData.operandWords, packString]; omega
      have hb2 : 2 + (1 + (bytesToWords (padTo4 (stringBytes name))).length) + interface.length ≤
          maxOperandWords := heq ▸ hbound
      have hle : (stringBytes name).length ≤ (padTo4 (stringBytes name)).length := by
        simp [padTo4]
      have hwcmul : 4 * (bytesToWords (padTo4 (stringBytes name))).length =
          (padTo4 (stringBytes name)).length :=
        length_bytesToWords (padTo4 (stringBytes name)) (length_padTo4 _)
      unfold maxOperandWords at hb2
      have hstrbound : (stringBytes name).length < 2 ^ 32 := by omega
      apply decodeOne_general 15 (by decide) _ rest hbound _ ?_ hwf
      show dispatch 15 (model :: function :: (packString name ++ interface)) =
        some (.opEntryPoint model function name interface)
      simp only [dispatch]
      rw [unpackString?_packString name interface hstrbound]
      rfl

/-! ## Whole modules

A module is a header plus its flat instruction stream, decoded by repeatedly
peeling one instruction (`decodeOne`) off the front until the word list is
exhausted. -/

theorem decodeOne_rest_lt (words : List Word) (i : Instr) (rest : List Word)
    (h : decodeOne words = some (i, rest)) : rest.length < words.length := by
  cases words with
  | nil => simp [decodeOne] at h
  | cons header tail =>
      simp only [decodeOne] at h
      by_cases htc : unpackHeaderCount header = 0
      · simp [htc] at h
      · simp only [htc, if_false] at h
        by_cases htl : tail.length < unpackHeaderCount header - 1
        · simp [htl] at h
        · simp only [htl, if_false] at h
          cases hd : dispatch (unpackHeaderOpcode header) (tail.take (unpackHeaderCount header - 1)) with
          | none => simp [hd] at h
          | some data =>
              simp only [hd] at h
              by_cases hwf : data.wellFormed = true
              · simp only [hwf, dif_pos] at h
                obtain ⟨_, hr⟩ := h
                simp only [List.length_cons, List.length_drop]
                omega
              · simp only [hwf] at h; simp at h

/-- Decode a fixed number of instructions (`fuel` is an upper bound on how
many remain, not a claim that exactly that many are present); consuming the
whole word list is what `decodeInstrs` below asks of it. Plain structural
recursion on `fuel`, so it needs no termination proof; `decodeInstrs_flatMap`
below is where `fuel := words.length` is shown to be enough for anything this
file encodes. -/
def decodeInstrsFuel : Nat → List Word → Option (List Instr)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, header :: tail =>
      match decodeOne (header :: tail) with
      | none => none
      | some (i, rest) => (decodeInstrsFuel fuel rest).map (i :: ·)

/-- Decode every instruction in a word list. -/
def decodeInstrs (words : List Word) : Option (List Instr) := decodeInstrsFuel words.length words

theorem decodeInstrsFuel_flatMap (instrs : List Instr) (fuel : Nat) (hfuel : instrs.length ≤ fuel) :
    decodeInstrsFuel fuel (instrs.flatMap Instr.toWords) = some instrs := by
  induction instrs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons i instrs ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          show decodeInstrsFuel (fuel + 1) (i.toWords ++ instrs.flatMap Instr.toWords) = some (i :: instrs)
          have htw : i.toWords = packHeader i.val.opcode (i.val.operandWords.length + 1) :: i.val.operandWords := rfl
          have hd : decodeOne (i.toWords ++ instrs.flatMap Instr.toWords) =
              some (i, instrs.flatMap Instr.toWords) := Instr.decode_encode i (instrs.flatMap Instr.toWords)
          rw [htw] at hd ⊢
          rw [List.cons_append] at hd ⊢
          have hfuel' : instrs.length ≤ fuel := by simp only [List.length_cons] at hfuel; omega
          simp only [decodeInstrsFuel, hd, ih fuel hfuel', Option.map_some]

/-- The seam's word-level round trip lifted from one instruction to a whole
stream: decoding an encoded instruction list recovers exactly that list. -/
theorem decodeInstrs_flatMap (instrs : List Instr) :
    decodeInstrs (instrs.flatMap Instr.toWords) = some instrs := by
  have hlen : instrs.length ≤ (instrs.flatMap Instr.toWords).length := by
    induction instrs with
    | nil => simp
    | cons i instrs ih =>
        show (i :: instrs).length ≤ (i.toWords ++ instrs.flatMap Instr.toWords).length
        have h1 : 1 ≤ i.toWords.length := by simp [Instr.toWords]
        simp only [List.length_cons, List.length_append]
        omega
  exact decodeInstrsFuel_flatMap instrs (instrs.flatMap Instr.toWords).length hlen

theorem length_wordsToBytes (ws : List Word) : (wordsToBytes ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      show (Word.toBytes w ++ wordsToBytes ws).length = 4 * (w :: ws).length
      simp only [Word.toBytes, List.length_append, List.length_cons, List.length_nil]; omega

/-- The fixed SPIR-V 1.5 header fields: magic number, version 1.5, and schema 0. -/
def spirvMagic : Word := UInt32.ofNat 0x07230203
def spirvVersion : Word := UInt32.ofNat 0x00010500
def spirvSchema : Word := 0

/-- A whole SPIR-V module: the mutable header fields (`generator`, `bound`)
and its flat instruction stream. `magic`, `version 1.5`, and `schema 0` are
fixed by `encode`, not carried as data. -/
structure Module where
  generator : Word
  bound : Word
  instructions : List Instr
deriving DecidableEq

def Module.headerWords (m : Module) : List Word :=
  [spirvMagic, spirvVersion, m.generator, m.bound, spirvSchema]

def Module.wordsOf (m : Module) : List Word := m.headerWords ++ m.instructions.flatMap Instr.toWords

/-- Canonical encoding: the module's words as little-endian bytes. -/
def Module.encode (m : Module) : List UInt8 := wordsToBytes m.wordsOf

/-- Recover a module from its bytes. -/
def Module.decode (bytes : List UInt8) : Option Module :=
  if bytes.length % 4 = 0 then
    match bytesToWords bytes with
    | magic :: version :: generator :: bound :: schema :: rest =>
        if magic = spirvMagic ∧ version = spirvVersion ∧ schema = spirvSchema then
          (decodeInstrs rest).map (fun instructions => { generator, bound, instructions })
        else none
    | _ => none
  else none

/-- `Grass.Target.ShaderLanguage.decode_encode` for SPIR-V. -/
theorem Module.decode_encode (m : Module) : Module.decode (Module.encode m) = some m := by
  have hlenmod : (Module.encode m).length % 4 = 0 := by
    show (wordsToBytes m.wordsOf).length % 4 = 0
    rw [length_wordsToBytes]; omega
  unfold Module.decode
  rw [if_pos hlenmod]
  show (match bytesToWords (wordsToBytes m.wordsOf) with
    | magic :: version :: generator :: bound :: schema :: rest =>
        if magic = spirvMagic ∧ version = spirvVersion ∧ schema = spirvSchema then
          (decodeInstrs rest).map (fun instructions => Module.mk generator bound instructions)
        else none
    | _ => none) = some m
  rw [bytesToWords_wordsToBytes]
  show (if spirvMagic = spirvMagic ∧ spirvVersion = spirvVersion ∧ spirvSchema = spirvSchema then
      (decodeInstrs (m.instructions.flatMap Instr.toWords)).map
        (fun instructions => Module.mk m.generator m.bound instructions)
    else none) = some m
  rw [if_pos (by simp)]
  rw [decodeInstrs_flatMap]
  rfl

/-! ## Entry points and stages -/

/-- The pipeline stage a shader entry point runs in. -/
inductive Stage where
  | vertex
  | fragment
  | compute
deriving DecidableEq, Repr

/-- The Khronos SPIR-V `ExecutionModel` word for a stage. -/
def Stage.executionModel : Stage → Word
  | .vertex => 0
  | .fragment => 4
  | .compute => 5

/-- The stage an `ExecutionModel` word names, when it is one this vocabulary
supports. -/
def executionModel? (w : Word) : Option Stage :=
  if w = Stage.vertex.executionModel then some .vertex
  else if w = Stage.fragment.executionModel then some .fragment
  else if w = Stage.compute.executionModel then some .compute
  else none

/-- An entry point: its name, pipeline stage, and defining function. -/
structure Entry where
  name : String
  stage : Stage
  function : Id
deriving DecidableEq, Repr

/-- The entry points an `OpEntryPoint` instruction in the module declares. -/
def Module.entries (m : Module) : List Entry :=
  m.instructions.filterMap fun i => match i.val with
    | .opEntryPoint model function name _interface =>
        (executionModel? model).map fun stage => { name, stage, function }
    | _ => none

end Grass.Shader.SPIRV.Module
