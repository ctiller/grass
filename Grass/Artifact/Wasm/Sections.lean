import Grass.Artifact.Wasm.Expr
import Grass.Artifact.Wasm.Section
import Grass.Artifact.Wasm.Strings
import Grass.ISA.Wasm.Target.Native

/-!
# Element codecs for every Wasm section

One canonical encode/decode pair and its round-trip law per element type a
Wasm section vector carries: `ValType`, `FuncType` (the type section), a
function import, a memory limits record, a global (type, mutability, and a
one-instruction constant initializer expression), an export, a data segment,
and one code-section entry (a function's locals and body, size-prefixed).
Every reader/writer composes `Grass.Artifact.Wasm.{writeVec,readVec}` and the
LEB128/name primitives; the module-level sections in
`Grass.Artifact.Wasm.Target` compose these once more with
`Grass.Artifact.Wasm.{writeSection,readSection}`.
-/
namespace Grass.Artifact.Wasm

open Grass.Artifact.Binary
open Grass.ISA.Wasm (ValType Value FuncType)
open Grass.ISA.Wasm.Target (Instr Global Import Export Data Function encode decodeAux
  decodeAux_encode)

/-! ## Value types -/

def encodeValType : ValType → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E

def decodeValType : List UInt8 → Option (ValType × List UInt8)
  | 0x7F :: rest => some (.i32, rest)
  | 0x7E :: rest => some (.i64, rest)
  | _ => none

theorem decodeValType_encodeValType (t : ValType) (rest : List UInt8) :
    decodeValType (encodeValType t :: rest) = some (t, rest) := by
  cases t <;> rfl

theorem decodeValType_encodeValType_singleton (t : ValType) (rest : List UInt8) :
    decodeValType ([encodeValType t] ++ rest) = some (t, rest) :=
  decodeValType_encodeValType t rest

/-! ## Function types (the type section, id 1) -/

/-- `0x60 vec(valtype) vec(valtype)`: params then results. -/
def encodeFuncType (ft : FuncType) : List UInt8 :=
  0x60 :: (writeVec (fun t => [encodeValType t]) ft.params ++
    writeVec (fun t => [encodeValType t]) ft.results)

def decodeFuncType : List UInt8 → Option (FuncType × List UInt8)
  | 0x60 :: rest =>
      match readVec decodeValType rest with
      | none => none
      | some (params, rest) =>
          match readVec decodeValType rest with
          | none => none
          | some (results, rest) => some (⟨params, results⟩, rest)
  | _ => none

theorem decodeFuncType_encodeFuncType (ft : FuncType) (rest : List UInt8) :
    decodeFuncType (encodeFuncType ft ++ rest) = some (ft, rest) := by
  unfold encodeFuncType decodeFuncType
  simp only [List.cons_append, List.append_assoc,
    readVec_writeVec decodeValType (fun t => [encodeValType t]) decodeValType_encodeValType_singleton]

/-! ## Imports (id 2) -/

/-- `name name 0x00 typeidx`: only function imports exist in this family, so
the import-kind byte is always `0x00`. -/
def encodeImport (imp : Import) : List UInt8 :=
  encodeName imp.moduleName ++ encodeName imp.fieldName ++ (0x00 :: natToLEB128 imp.typeIndex)

def decodeImport (bytes : List UInt8) : Option (Import × List UInt8) :=
  match decodeName bytes with
  | none => none
  | some (moduleName, bytes) =>
      match decodeName bytes with
      | none => none
      | some (fieldName, bytes) =>
          match bytes with
          | 0x00 :: bytes =>
              match readLEB128 bytes with
              | none => none
              | some (typeIndex, rest) => some (⟨moduleName, fieldName, typeIndex⟩, rest)
          | _ => none

theorem decodeImport_encodeImport (imp : Import) (rest : List UInt8) :
    decodeImport (encodeImport imp ++ rest) = some (imp, rest) := by
  unfold encodeImport decodeImport
  simp only [List.append_assoc, decodeName_encodeName, List.cons_append,
    readLEB128_natToLEB128_append]

/-! ## Memory (id 5): exactly one `memtype`, `min`-only limits. -/

def encodeMemType (pages : Nat) : List UInt8 := 0x00 :: natToLEB128 pages

def decodeMemType : List UInt8 → Option (Nat × List UInt8)
  | 0x00 :: rest => readLEB128 rest
  | _ => none

theorem decodeMemType_encodeMemType (pages : Nat) (rest : List UInt8) :
    decodeMemType (encodeMemType pages ++ rest) = some (pages, rest) := by
  unfold encodeMemType decodeMemType
  simp only [List.cons_append, readLEB128_natToLEB128_append]

/-! ## Globals (id 6): type, mutability, one constant initializer expression -/

/-- The one-instruction constant initializer expression a global's `init`
value is (no `global.get`-relative initializers in this family — see
`Grass.ISA.Wasm.Target.Global`'s docstring). -/
def encodeConstExpr : Value → List UInt8
  | .i32 bits => encode (Instr.i32Const bits)
  | .i64 bits => encode (Instr.i64Const bits)

/-- Decode a constant expression of the declared type `t`; a decoded constant
of the other width, or any other instruction, is rejected (this format never
writes either). -/
def decodeConstExpr (t : ValType) (bytes : List UInt8) : Option (Value × List UInt8) :=
  match decodeAux bytes with
  | some (.i32Const v, rest) => if t = .i32 then some (.i32 v, rest) else none
  | some (.i64Const v, rest) => if t = .i64 then some (.i64 v, rest) else none
  | _ => none

theorem decodeConstExpr_encodeConstExpr (v : Value) (rest : List UInt8) :
    decodeConstExpr v.type (encodeConstExpr v ++ rest) = some (v, rest) := by
  cases v with
  | i32 bits =>
      show decodeConstExpr .i32 (encode (Instr.i32Const bits) ++ rest) = some (Value.i32 bits, rest)
      unfold decodeConstExpr
      rw [decodeAux_encode]
      simp
  | i64 bits =>
      show decodeConstExpr .i64 (encode (Instr.i64Const bits) ++ rest) = some (Value.i64 bits, rest)
      unfold decodeConstExpr
      rw [decodeAux_encode]
      simp

/-- `valtype mutbyte constexpr 0x0B`. This format's own artifact-level global
entry is `(mutable, init)`, never a separately-stored declared type: the
valtype byte written is always `init.type`, so there is no way to represent
a mismatch and no side condition for the round trip below to need. A general
`Grass.ISA.Wasm.Target.Global` (whose `type` field is independent of `init`)
still owes that agreement to convert into one — `Grass.Artifact.Wasm.Target.
Eligible` requires it of every module `assemble` accepts. -/
def encodeGlobalEntry (entry : Bool × Value) : List UInt8 :=
  encodeValType entry.2.type :: (if entry.1 then (1 : UInt8) else 0) ::
    (encodeConstExpr entry.2 ++ [0x0B])

def decodeGlobalEntry (bytes : List UInt8) : Option ((Bool × Value) × List UInt8) :=
  match decodeValType bytes with
  | none => none
  | some (t, bytes) =>
      match bytes with
      | [] => none
      | mutByte :: bytes =>
          match decodeConstExpr t bytes with
          | none => none
          | some (v, bytes) =>
              match bytes with
              | 0x0B :: rest =>
                  if mutByte = (1 : UInt8) then some ((true, v), rest)
                  else if mutByte = (0 : UInt8) then some ((false, v), rest)
                  else none
              | _ => none

theorem decodeGlobalEntry_encodeGlobalEntry (entry : Bool × Value) (rest : List UInt8) :
    decodeGlobalEntry (encodeGlobalEntry entry ++ rest) = some (entry, rest) := by
  unfold encodeGlobalEntry decodeGlobalEntry
  simp only [List.cons_append, List.append_assoc]
  rw [decodeValType_encodeValType]
  simp only
  rw [decodeConstExpr_encodeConstExpr]
  obtain ⟨mutable, v⟩ := entry
  cases mutable <;> simp

/-! ## Exports (id 7): only function exports exist in this family. -/

def encodeExport (e : Export) : List UInt8 :=
  encodeName e.name ++ (0x00 :: natToLEB128 e.funcIndex)

def decodeExport (bytes : List UInt8) : Option (Export × List UInt8) :=
  match decodeName bytes with
  | none => none
  | some (name, bytes) =>
      match bytes with
      | 0x00 :: bytes =>
          match readLEB128 bytes with
          | none => none
          | some (funcIndex, rest) => some (⟨name, funcIndex⟩, rest)
      | _ => none

theorem decodeExport_encodeExport (e : Export) (rest : List UInt8) :
    decodeExport (encodeExport e ++ rest) = some (e, rest) := by
  unfold encodeExport decodeExport
  simp only [List.append_assoc, decodeName_encodeName, List.cons_append,
    readLEB128_natToLEB128_append]

/-! ## Data segments (id 11): active, memory 0, a constant `i32` offset. -/

/-- This format's own artifact-level data entry: `offset` is a `UInt32`
(exactly the width an `i32.const` offset carries), not the unbounded `Nat`
`Grass.ISA.Wasm.Target.Data.offset` is, so the round trip below needs no
width-fits side condition — unconditionally exact, the same reason
`Grass.Artifact.ELF`'s fixed-width header fields are. `Eligible` still owes
`assemble` the `Nat → UInt32` bound when converting a general `Module`'s
`Data.offset`. -/
structure DataEntry where
  offset : UInt32
  bytes : List UInt8
deriving Repr, DecidableEq

/-- `0x00 i32.const offset end vec(byte)`: the active-segment, memory-0 form
(no passive segments, no multi-memory). -/
def encodeDataEntry (d : DataEntry) : List UInt8 :=
  0x00 :: (encode (Instr.i32Const d.offset.toBitVec) ++ [0x0B]) ++
    (natToLEB128 d.bytes.length ++ d.bytes)

def decodeDataEntry (bytes : List UInt8) : Option (DataEntry × List UInt8) :=
  match bytes with
  | 0x00 :: bytes =>
      match decodeAux bytes with
      | some (.i32Const v, bytes) =>
          match bytes with
          | 0x0B :: bytes =>
              match readLEB128 bytes with
              | none => none
              | some (len, bytes) =>
                  match takeBytes len bytes with
                  | none => none
                  | some (dataBytes, rest) => some (⟨UInt32.ofBitVec v, dataBytes⟩, rest)
          | _ => none
      | _ => none
  | _ => none

theorem decodeDataEntry_encodeDataEntry (d : DataEntry) (rest : List UInt8) :
    decodeDataEntry (encodeDataEntry d ++ rest) = some (d, rest) := by
  unfold encodeDataEntry decodeDataEntry
  simp only [List.cons_append, List.append_assoc]
  rw [decodeAux_encode]
  simp only [List.nil_append, readLEB128_natToLEB128_append, takeBytes_append_of_eq rfl]

/-! ## Code entries (id 10): size-prefixed locals-vector plus expression -/

/-- One local, as a group of exactly one: the count is always `1`, so a
`Function.locals` list becomes one group per local rather than the
run-length-compressed groups a size-optimizing producer would emit. This is
still a spec-legal `vec(locals)` — the grammar puts no lower bound on how
finely a producer groups identical types — just not a maximally compact one;
`read` accordingly only accepts a count of exactly `1`, since that is all
this writer ever emits. -/
def encodeLocalGroup (t : ValType) : List UInt8 := natToLEB128 1 ++ [encodeValType t]

def decodeLocalGroup (bytes : List UInt8) : Option (ValType × List UInt8) :=
  match readLEB128 bytes with
  | some (1, bytes) => decodeValType bytes
  | _ => none

theorem decodeLocalGroup_encodeLocalGroup (t : ValType) (rest : List UInt8) :
    decodeLocalGroup (encodeLocalGroup t ++ rest) = some (t, rest) := by
  unfold encodeLocalGroup decodeLocalGroup
  simp only [List.append_assoc, readLEB128_natToLEB128_append]
  exact decodeValType_encodeValType_singleton t rest

/-- `size:u32 vec(locals) expr`, where `expr` is `Grass.Artifact.Wasm.
encodeInstrs body ++ [0x0B]` (`Grass.Artifact.Wasm.decodeExpr` strips the
terminator back off). -/
def encodeCodeEntry (locals : List ValType) (body : List Instr) : List UInt8 :=
  let content := writeVec encodeLocalGroup locals ++ (encodeInstrs body ++ [0x0B])
  natToLEB128 content.length ++ content

def decodeCodeEntry (bytes : List UInt8) : Option ((List ValType × List Instr) × List UInt8) :=
  match readLEB128 bytes with
  | none => none
  | some (size, bytes) =>
      match takeBytes size bytes with
      | none => none
      | some (content, rest) =>
          match readVec decodeLocalGroup content with
          | none => none
          | some (locals, exprBytes) =>
              match decodeExpr exprBytes.length exprBytes with
              | none => none
              | some body => some ((locals, body), rest)

theorem decodeCodeEntry_encodeCodeEntry (locals : List ValType) (body : List Instr)
    (rest : List UInt8) :
    decodeCodeEntry (encodeCodeEntry locals body ++ rest) = some ((locals, body), rest) := by
  have shape : encodeCodeEntry locals body ++ rest =
      natToLEB128 (writeVec encodeLocalGroup locals ++ (encodeInstrs body ++ [0x0B])).length ++
        ((writeVec encodeLocalGroup locals ++ (encodeInstrs body ++ [0x0B])) ++ rest) := by
    simp [encodeCodeEntry, List.append_assoc]
  rw [shape]
  unfold decodeCodeEntry
  rw [readLEB128_natToLEB128_append]
  simp only
  rw [takeBytes_append_of_eq rfl]
  simp only
  rw [readVec_writeVec decodeLocalGroup encodeLocalGroup decodeLocalGroup_encodeLocalGroup]
  simp only
  rw [decodeExpr_encodeInstrs body _ (length_lt_length_encodeInstrs_append body)]

end Grass.Artifact.Wasm
