import Grass.Artifact.Wasm.Sections
import Grass.ISA.Wasm.Target
import Grass.Target.Artifact

/-!
# The WebAssembly 1.0 binary module format

`Grass.Artifact.Wasm.format` instantiates `Grass.Target.Format
Grass.ISA.Wasm.Target.Module`: the standard `\0asm` magic and version-1
header followed by the type (1), import (2), function (3), memory (5),
global (6), export (7), code (10) and data (11) sections, each a
`Grass.Artifact.Wasm.vec` (an LEB128 count then that many elements), framed
by `Grass.Artifact.Wasm.{writeSection,readSection}`. Section ids 4 (table)
and 8 (start) never appear — this MVP family has no table section
(`Grass.ISA.Wasm.Target.Fault.undecodable`'s docstring), and `Eligible`
below refuses any module naming a start function.

`Artifact`'s own fields are deliberately not `Grass.ISA.Wasm.Target.Module`
verbatim: `globals : List (Bool × Value)` and `DataEntry.offset : UInt32`
(`Sections.lean`) each remove a side condition a `Module`'s more general
shape would otherwise put on `read_write` — see those files' docstrings.
`funcTypeIndices`/`code` likewise keep the function (3) and code (10)
sections' element lists separate, matching the wire format exactly: a
module's `functions : List Function` (typeIndex, locals, body together) is
one list, but the two *sections* it produces are independent vectors that
`assemble` happens to always build to equal length, and `read` independently
recovers to a possibly-*unequal* length — Wasm's actual "function count ≠
code count" ill-formedness, which is exactly what `Grass.Artifact.Wasm.
readSectionVec`'s exact-consumption check cannot see (each section is
well-formed on its own) but the reassembly below can and does check.
-/
namespace Grass.Artifact.Wasm

open Grass.Artifact.Binary Grass.Target
open Grass.ISA.Wasm (ValType Value FuncType)
open Grass.ISA.Wasm.Target (Instr Import Export Function Module)

/-- `\0asm`. -/
def MAGIC : List UInt8 := [0x00, 0x61, 0x73, 0x6D]

/-- Version 1, little-endian. -/
def VERSION : List UInt8 := [0x01, 0x00, 0x00, 0x00]

@[simp] theorem length_MAGIC : MAGIC.length = 4 := rfl
@[simp] theorem length_VERSION : VERSION.length = 4 := rfl

def TYPE_ID : UInt8 := 1
def IMPORT_ID : UInt8 := 2
def FUNCTION_ID : UInt8 := 3
def MEMORY_ID : UInt8 := 5
def GLOBAL_ID : UInt8 := 6
def EXPORT_ID : UInt8 := 7
def CODE_ID : UInt8 := 10
def DATA_ID : UInt8 := 11

/-- The Wasm module container: every section's own element list, kept in the
wire format's own shape (see the file docstring for why `globals`/`data`/the
split function-and-code lists are not `Grass.ISA.Wasm.Target.Module`
verbatim). -/
structure Artifact where
  types : List FuncType
  imports : List Import
  funcTypeIndices : List Nat
  memoryMinPages : Nat
  globals : List (Bool × Value)
  exports : List Export
  code : List (List ValType × List Instr)
  /-- The function (3) and code (10) sections agree in length: Wasm's actual
  "function count ≠ code count" ill-formedness (the file docstring), carried
  as a proof so an `Artifact` cannot represent it at all, rather than as a
  `read`-time check that a mismatched value could still slip past. -/
  codeLengthEq : funcTypeIndices.length = code.length
  data : List DataEntry
deriving Repr

/-- The complete binary module: header, then the eight sections in ascending
id order. -/
def write (a : Artifact) : List UInt8 :=
  MAGIC ++ VERSION ++
    writeSectionVec TYPE_ID encodeFuncType a.types ++
    writeSectionVec IMPORT_ID encodeImport a.imports ++
    writeSectionVec FUNCTION_ID natToLEB128 a.funcTypeIndices ++
    writeSectionVec MEMORY_ID encodeMemType [a.memoryMinPages] ++
    writeSectionVec GLOBAL_ID encodeGlobalEntry a.globals ++
    writeSectionVec EXPORT_ID encodeExport a.exports ++
    writeSectionVec CODE_ID (fun (lb : List ValType × List Instr) => encodeCodeEntry lb.1 lb.2)
      a.code ++
    writeSectionVec DATA_ID encodeDataEntry a.data

/-- Recover a module from bytes: the exact magic and version, then the eight
sections in exactly that order, with nothing left over. Any other section
id, ordering, or trailing byte — anywhere, including inside one section's
own content — is refused (`Grass.Artifact.Wasm.readSectionVec`'s exact
consumption, plus the final `[]` check below). -/
def read (bytes : List UInt8) : Option Artifact :=
  match takeBytes 4 bytes with
  | none => none
  | some (magic, bytes) =>
      if magic = MAGIC then
        match takeBytes 4 bytes with
        | none => none
        | some (version, bytes) =>
            if version = VERSION then
              match readSectionVec TYPE_ID decodeFuncType bytes with
              | none => none
              | some (types, bytes) =>
              match readSectionVec IMPORT_ID decodeImport bytes with
              | none => none
              | some (imports, bytes) =>
              match readSectionVec FUNCTION_ID readLEB128 bytes with
              | none => none
              | some (funcTypeIndices, bytes) =>
              match readSectionVec MEMORY_ID decodeMemType bytes with
              | none => none
              | some (memoryPages, bytes) =>
              match memoryPages with
              | [] => none
              | _ :: _ :: _ => none
              | [memoryMinPages] =>
              match readSectionVec GLOBAL_ID decodeGlobalEntry bytes with
              | none => none
              | some (globals, bytes) =>
              match readSectionVec EXPORT_ID decodeExport bytes with
              | none => none
              | some (exports, bytes) =>
              match readSectionVec CODE_ID decodeCodeEntry bytes with
              | none => none
              | some (code, bytes) =>
              if h : funcTypeIndices.length = code.length then
              match readSectionVec DATA_ID decodeDataEntry bytes with
              | none => none
              | some (data, tail) =>
              match tail with
              | _ :: _ => none
              | [] =>
                  some
                    { types, imports, funcTypeIndices, memoryMinPages, globals, exports, code,
                      codeLengthEq := h, data }
              else none
            else none
      else none

theorem read_write (a : Artifact) : read (write a) = some a := by
  have shape : write a =
      MAGIC ++ (VERSION ++
        (writeSectionVec TYPE_ID encodeFuncType a.types ++
          (writeSectionVec IMPORT_ID encodeImport a.imports ++
            (writeSectionVec FUNCTION_ID natToLEB128 a.funcTypeIndices ++
              (writeSectionVec MEMORY_ID encodeMemType [a.memoryMinPages] ++
                (writeSectionVec GLOBAL_ID encodeGlobalEntry a.globals ++
                  (writeSectionVec EXPORT_ID encodeExport a.exports ++
                    (writeSectionVec CODE_ID
                        (fun (lb : List ValType × List Instr) => encodeCodeEntry lb.1 lb.2) a.code ++
                      writeSectionVec DATA_ID encodeDataEntry a.data)))))))) := by
    simp [write, List.append_assoc]
  unfold read
  rw [shape]
  simp only [takeBytes_append_of_eq length_MAGIC, ↓reduceIte,
    takeBytes_append_of_eq length_VERSION,
    readSectionVec_writeSectionVec TYPE_ID decodeFuncType encodeFuncType
      decodeFuncType_encodeFuncType,
    readSectionVec_writeSectionVec IMPORT_ID decodeImport encodeImport decodeImport_encodeImport,
    readSectionVec_writeSectionVec FUNCTION_ID readLEB128 natToLEB128
      readLEB128_natToLEB128_append,
    readSectionVec_writeSectionVec MEMORY_ID decodeMemType encodeMemType
      decodeMemType_encodeMemType,
    readSectionVec_writeSectionVec GLOBAL_ID decodeGlobalEntry encodeGlobalEntry
      decodeGlobalEntry_encodeGlobalEntry,
    readSectionVec_writeSectionVec EXPORT_ID decodeExport encodeExport decodeExport_encodeExport,
    readSectionVec_writeSectionVec CODE_ID decodeCodeEntry
      (fun (lb : List ValType × List Instr) => encodeCodeEntry lb.1 lb.2)
      (fun lb rest => decodeCodeEntry_encodeCodeEntry lb.1 lb.2 rest),
    readSectionVec_writeSectionVec_nil DATA_ID decodeDataEntry encodeDataEntry
      decodeDataEntry_encodeDataEntry, a.codeLengthEq, ↓reduceDIte]

/-! ## `assemble`/`rawOf`: crossing to and from `Grass.ISA.Wasm.Target.Module` -/

/-- What `assemble` accepts: no start function (this format writes no start
section), every global's declared type agreeing with its initializer's
actual type (`Sections.lean`'s `encodeGlobalEntry` has no way to represent a
mismatch), every export naming a function Wasm's shared import/function
index space actually has, and every data segment's offset both fitting the
32-bit `i32.const` its encoding rides on and landing inside the declared
linear memory. -/
def Eligible (program : Module) : Prop :=
  program.start = none ∧
    (∀ g ∈ program.globals, g.type = g.init.type) ∧
    (∀ e ∈ program.exports, e.funcIndex < program.imports.length + program.functions.length) ∧
    (∀ d ∈ program.data, d.offset < 4294967296) ∧
    (∀ d ∈ program.data, d.offset + d.bytes.length ≤ program.memoryBytes)

instance : DecidablePred Eligible := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Assemble a module, refusing one that is not `Eligible`. The function (3)
and code (10) sections are both built from `program.functions` by `List.map`,
so they always come out the same length — `Artifact.codeLengthEq` — which is
exactly why the "function count ≠ code count" ill-formedness the file
docstring describes cannot arise from `assemble` at all, only from bytes
`read` independently recovers. -/
def assemble (program : Module) : Option Artifact :=
  if _ : Eligible program then
    some
      { types := program.types
        imports := program.imports
        funcTypeIndices := program.functions.map (·.typeIndex)
        memoryMinPages := program.memoryMinPages
        globals := program.globals.map (fun g => (g.mutable, g.init))
        exports := program.exports
        code := program.functions.map (fun f => (f.locals, f.body))
        codeLengthEq := by simp
        data := program.data.map (fun d => (⟨UInt32.ofNat d.offset, d.bytes⟩ : DataEntry)) }
  else none

/-- The program a module artifact carries: the function (3) and code (10)
section lists are zipped back into `Function` records — exact, never
truncating, since `Artifact.codeLengthEq` rules out the two lists disagreeing
in length — every global regains a declared type equal to its initializer's
own, every data offset returns to a plain `Nat`, and there is no start
function. -/
def rawOf (artifact : Artifact) : Module :=
  { types := artifact.types
    imports := artifact.imports
    functions := (List.zip artifact.funcTypeIndices artifact.code).map
      (fun (ti, lb) => (⟨ti, lb.1, lb.2⟩ : Function))
    memoryMinPages := artifact.memoryMinPages
    globals := artifact.globals.map (fun (mutable, v) => (⟨v.type, mutable, v⟩ : Grass.ISA.Wasm.Target.Global))
    exports := artifact.exports
    data := artifact.data.map (fun d => (⟨d.offset.toNat, d.bytes⟩ : Grass.ISA.Wasm.Target.Data))
    start := none }

/-- Zipping a list's own two projections back together, then reassembling
`Function` from the zipped pair, recovers the list exactly. -/
theorem functions_rawOf_assemble (functions : List Function) :
    (List.zip (functions.map (·.typeIndex)) (functions.map (fun f => (f.locals, f.body)))).map
        (fun (ti, lb) => (⟨ti, lb.1, lb.2⟩ : Function)) = functions := by
  induction functions with
  | nil => rfl
  | cons f functions ih => simp [List.zip_cons_cons, ih]

/-- Reassembling every global's forgotten declared type from its
initializer's own recovers it exactly, because `Eligible` already required
them equal. -/
theorem globals_rawOf_assemble (globals : List Grass.ISA.Wasm.Target.Global)
    (typesAgree : ∀ g ∈ globals, g.type = g.init.type) :
    (globals.map (fun g => (g.mutable, g.init))).map
        (fun (mutable, v) => (⟨v.type, mutable, v⟩ : Grass.ISA.Wasm.Target.Global)) = globals := by
  induction globals with
  | nil => rfl
  | cons g globals ih =>
      have headEq : g.type = g.init.type := typesAgree g (by simp)
      have tailAgree : ∀ h ∈ globals, h.type = h.init.type :=
        fun h member => typesAgree h (by simp [member])
      simp only [List.map_cons, ih tailAgree]
      rw [← headEq]

/-- Reassembling every data segment's truncated `UInt32` offset back to a
`Nat` recovers it exactly, because `Eligible` already required it to fit. -/
theorem data_rawOf_assemble (data : List Grass.ISA.Wasm.Target.Data)
    (offsetBound : ∀ d ∈ data, d.offset < 4294967296) :
    (data.map (fun d => (⟨UInt32.ofNat d.offset, d.bytes⟩ : DataEntry))).map
        (fun d => (⟨d.offset.toNat, d.bytes⟩ : Grass.ISA.Wasm.Target.Data)) = data := by
  induction data with
  | nil => rfl
  | cons d data ih =>
      have headBound : d.offset < 4294967296 := offsetBound d (by simp)
      have tailBound : ∀ e ∈ data, e.offset < 4294967296 :=
        fun e member => offsetBound e (by simp [member])
      have offsetEq : (UInt32.ofNat d.offset).toNat = d.offset := by
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt headBound
      simp only [List.map_cons, ih tailBound, offsetEq]

/-- Assembling preserves the program exactly. -/
theorem rawOf_assemble (program : Module) (artifact : Artifact) :
    assemble program = some artifact → rawOf artifact = program := by
  intro success
  unfold assemble at success
  split at success
  next elig =>
    obtain ⟨startNone, globalTypes, _exportBound, offsetBound, _memBound⟩ := elig
    injection success with success
    subst success
    unfold rawOf
    simp only [functions_rawOf_assemble, globals_rawOf_assemble program.globals globalTypes,
      data_rawOf_assemble program.data offsetBound]
    rw [← startNone]
  next => simp at success

/-- The WebAssembly 1.0 binary module `Format`. -/
def format : Format Grass.ISA.Wasm.isa.Raw where
  Artifact := Artifact
  assemble := assemble
  write := write
  read := read
  read_write := read_write
  rawOf := rawOf
  rawOf_assemble := rawOf_assemble

end Grass.Artifact.Wasm
