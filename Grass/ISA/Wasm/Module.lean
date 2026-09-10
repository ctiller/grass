import Grass.ISA.Wasm.Types
import Grass.Std.Logical.Byte

/-!
One authored module carrier and a bounded canonical Core 2.0 binary producer.
This integer/local/direct-call family is intentionally extensible. No duplicate
instruction list is accepted as evidence for emitted bytes. Encoding success
checks representable binary lengths/indices, NOT whole-module validation or
behavioral correctness. See docs/WASM_ISA.md for the remaining proof boundary.
-/
namespace Grass.ISA.Wasm
open Grass.Std.Logical

inductive Instruction where
  | unreachable | nop | drop | return_
  | i32Const (value : BitVec 32)
  | i64Const (value : BitVec 64)
  | localGet (index : Nat)
  | localSet (index : Nat)
  | call (index : Nat)
  | i32Add | i32Sub | i32Eqz
deriving DecidableEq, Repr

structure Import where
  moduleName : String
  fieldName : String
  type : FuncType
deriving DecidableEq, Repr

structure Function where
  type : FuncType
  locals : List ValType
  body : List Instruction
deriving DecidableEq, Repr

structure Export where
  name : String
  functionIndex : Nat
deriving DecidableEq, Repr

structure Module where
  imports : List Import
  functions : List Function
  exports : List Export
deriving DecidableEq, Repr

namespace Binary

/-- Fuel bounds the binary format width; exhaustion is refusal, never truncation. -/
def unsigned : Nat → Nat → Option ByteSeq
  | 0, _ => none
  | fuel + 1, n =>
      if n < 128 then some [BitVec.ofNat 8 n]
      else do
        let rest ← unsigned fuel (n / 128)
        return BitVec.ofNat 8 (n % 128 + 128) :: rest

def u32 (n : Nat) : Option ByteSeq :=
  if n < 2 ^ 32 then unsigned 5 n else none

/-- Arithmetic division retains the sign; termination requires a valid sign bit. -/
def signed : Nat → Int → Option ByteSeq
  | 0, _ => none
  | fuel + 1, n =>
      let low := (n % 128).toNat
      let next := n / 128
      if (next = 0 ∧ low < 64) ∨ (next = -1 ∧ 64 ≤ low) then
        some [BitVec.ofNat 8 low]
      else do
        let rest ← signed fuel next
        return BitVec.ofNat 8 (low + 128) :: rest

def vec {α : Type} (encode : α → Option ByteSeq) (items : List α) : Option ByteSeq := do
  let count ← u32 items.length
  let chunks ← items.mapM encode
  return count ++ chunks.flatten

def name (s : String) : Option ByteSeq := do
  let bytes := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)
  let count ← u32 bytes.length
  return count ++ bytes

def valType : ValType → Byte
  | .i32 => 0x7f
  | .i64 => 0x7e

def funcType (t : FuncType) : Option ByteSeq := do
  let params ← vec (fun p => some [valType p]) t.params
  let results ← vec (fun r => some [valType r]) t.results
  return [0x60] ++ params ++ results

def instruction : Instruction → Option ByteSeq
  | .unreachable => some [0x00]
  | .nop => some [0x01]
  | .drop => some [0x1a]
  | .return_ => some [0x0f]
  | .i32Const v => ([0x41] ++ ·) <$> signed 5 v.toInt
  | .i64Const v => ([0x42] ++ ·) <$> signed 10 v.toInt
  | .localGet i => ([0x20] ++ ·) <$> u32 i
  | .localSet i => ([0x21] ++ ·) <$> u32 i
  | .call i => ([0x10] ++ ·) <$> u32 i
  | .i32Eqz => some [0x45]
  | .i32Add => some [0x6a]
  | .i32Sub => some [0x6b]

def function (f : Function) : Option ByteSeq := do
  let locals ← vec (fun t => some [0x01, valType t]) f.locals
  let instructions ← f.body.mapM instruction
  let body := locals ++ instructions.flatten ++ [0x0b]
  let size ← u32 body.length
  return size ++ body

def sectionBytes (id : Byte) (payload : ByteSeq) : Option ByteSeq := do
  let size ← u32 payload.length
  return [id] ++ size ++ payload

end Binary

/-- Production raw emitter for this family. A type entry is emitted per function
occurrence, avoiding an independent type-table assignment. Empty sections are
legal; the emitted function indices put imports before defined functions. -/
def Module.encode (m : Module) : Option ByteSeq := do
  let types ← Binary.vec Binary.funcType
    (m.imports.map Import.type ++ m.functions.map Function.type)
  let imports ← Binary.vec (fun (entry : Nat × Import) => do
    let namespaceBytes ← Binary.name entry.2.moduleName
    let fieldBytes ← Binary.name entry.2.fieldName
    let typeIndex ← Binary.u32 entry.1
    return namespaceBytes ++ fieldBytes ++ [0x00] ++ typeIndex)
      (m.imports.zipIdx.map (fun (imp, idx) => (idx, imp)))
  let functions ← Binary.vec (fun i => Binary.u32 (m.imports.length + i))
    (List.range m.functions.length)
  let exports ← Binary.vec (fun e => do
    let exportName ← Binary.name e.name
    let index ← Binary.u32 e.functionIndex
    return exportName ++ [0x00] ++ index) m.exports
  let code ← Binary.vec Binary.function m.functions
  let ts ← Binary.sectionBytes 1 types
  let is ← Binary.sectionBytes 2 imports
  let fs ← Binary.sectionBytes 3 functions
  let es ← Binary.sectionBytes 7 exports
  let cs ← Binary.sectionBytes 10 code
  return [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++ ts ++ is ++ fs ++ es ++ cs

/-- Exact original-source/production-byte binding. This is not a validation,
decoder, loader or VerifiedProgram certificate. -/
structure Artifact where
  private mk ::
  source : Module
  bytes : ByteSeq
  emitted : source.encode = some bytes

def Artifact.emit (source : Module) : Option Artifact :=
  match h : source.encode with
  | none => none
  | some bytes => some ⟨source, bytes, h⟩

/-- `Artifact.check` returns an artifact when `Module.encode` matches the supplied
bytes, retaining that equality in `Artifact.emitted`. -/
def Artifact.check (source : Module) (bytes : ByteSeq) : Option Artifact :=
  if h : source.encode = some bytes then some ⟨source, bytes, h⟩ else none

theorem Artifact.bytes_unique (a b : Artifact) (h : a.source = b.source) :
    a.bytes = b.bytes := by
  have same := a.emitted.symm.trans (h ▸ b.emitted)
  exact Option.some.inj same

end Grass.ISA.Wasm
