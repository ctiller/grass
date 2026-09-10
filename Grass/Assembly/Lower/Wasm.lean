import Grass.Assembly.Syntax.AST
import Grass.ISA.Wasm.Target.Instr
import Grass.ISA.Wasm.Target.Native
import Grass.ISA.Wasm.Types
import Grass.Artifact.Binary.LittleEndian

/-!
# The Wasm assembler

An assembler from the target-generic authored surface
(`Grass.Assembly.Syntax.Source`, `Grass/Assembly/Syntax/AST.lean`) to
`Grass.ISA.Wasm.Target.Module`. Wasm is not byte-addressed the way a native
ISA is: `block`/`loop`/`if` are structured control carried by a run-time
label stack (`Grass/ISA/Wasm/Target/State.lean`'s `scanControl`), and `br`/
`brIf`/`brTable` name their target by a small relative *label depth*, an
ordinary authored immediate, never a byte offset computed from where
anything "lands". There is therefore no two-pass size/layout problem for
this ISA the way `Grass.Assembly.Lower.Lowering`/`Layout` solve one for a
byte-addressed target: this file is a sibling of that machinery, not an
instance of it, and does not import either.

## Directive grammar

Five directive keywords, recognized by name alone (`directiveNames`) so they
work whether the front end's `Parser.lean` classifies the line as
`Line.instruction` or `Line.directive` — today's `Parser.directiveNames`
list only contains `arg`, so these five currently parse as `Line.instruction`
lines, which this file does not need changed (see the closing report):

* `import MODULE, FIELD, P1, P2, ..., results, R1, R2, ...` — one imported
  function's module/field name and signature. `wasi_snapshot_preview1
  fd_write (i32 i32 i32 i32) -> (i32)` is spelled
  `import wasi_snapshot_preview1, fd_write, i32, i32, i32, i32, results, i32`.
* `func NAME, P1, ..., results, R1, ...` — one defined function's name and
  signature; `_start () -> ()` is `func _start, results`. The function's
  body is every non-label, non-directive line between the `NAME:` label
  (declared separately, as an ordinary source label) and the next label, or
  the end of the source if `NAME` is the last declared function.
* `export NAME` — export the function named `NAME` (an import or a `func`)
  under that same name.
* `memory PAGES` — linear memory size at instantiation, in 64 KiB pages.
  Exactly one `memory` directive is required.
* `data ADDR, NAME` — install the named static's bytes at `ADDR` in linear
  memory. `NAME` is resolved through the caller-supplied `Directives.statics`
  table, not through the source.

`results` is a bare marker symbol separating a signature's parameter types
from its result types, adopted because the generic `asmOperand` grammar
(`Grass/Assembly/Syntax/Parser.lean`) has no `(...) -> (...)` production —
see the closing report.

## Mnemonic coverage

Every one of `Instr`'s 104 constructors has exactly one authored mnemonic
form below (`zeroOperandTable` for the 70 that carry no data, `lowerMnemonic`
for the other 34): the full table is reproduced in the closing report.
-/
namespace Grass.Assembly.Lower.Wasm

open Grass.Assembly.Syntax
open Grass.ISA.Wasm (ValType FuncType)
open Grass.ISA.Wasm.Target (Instr MemArg BlockType Module Import Function Export Data)

/-! ## Generic association-list lookup

Like `Grass.Assembly.Lower.lookup`, but not specialized to `Nat` values:
this file also looks up a function's body (`List Line`) by its declared
name, which that specialized version cannot carry. -/
def assocLookup {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (key, value) :: rest, name => if key = name then some value else assocLookup rest name

/-- The position of the first occurrence of `name` in `names`, `none` if
absent. Used for the joint import/function index space (`Directives.
jointNames`) and for export resolution. -/
def indexOf : List String → String → Option Nat
  | [], _ => none
  | name :: rest, target => if name = target then some 0 else (indexOf rest target).map (· + 1)

/-! ## Operand parsing helpers, shared by directives and mnemonics -/

def valTypeOf (name : String) : Except String ValType :=
  if name = "i32" then .ok .i32
  else if name = "i64" then .ok .i64
  else .error s!"unsupported value type '{name}' (expected 'i32' or 'i64')"

def symbolName : Operand → Except String String
  | .symbol name => .ok name
  | _ => .error "expected a bare name operand"

def isResultsMarker : Operand → Bool
  | .symbol "results" => true
  | _ => false

/-- Split an operand list at the bare marker symbol `results`: everything
before it is the parameter type list, everything after is the result type
list (the marker itself dropped). See the file docstring for why this
sentinel stands in for `(...) -> (...)`. -/
def splitAtResults (operands : List Operand) : List Operand × List Operand :=
  let (before, after) := operands.span (fun o => !isResultsMarker o)
  (before, after.drop 1)

def typesOf (operands : List Operand) : Except String (List ValType) :=
  operands.mapM (fun o => symbolName o >>= valTypeOf)

/-- A directive's `P1, ..., results, R1, ...` tail, as a parameter/result
signature. -/
def signatureOf (operands : List Operand) : Except String (List ValType × List ValType) :=
  let (paramOps, resultOps) := splitAtResults operands
  match typesOf paramOps with
  | .error msg => .error msg
  | .ok params =>
      match typesOf resultOps with
      | .error msg => .error msg
      | .ok results => .ok (params, results)

def natImm : Operand → Except String Nat
  | .imm n => if n < 0 then .error "expected a non-negative immediate" else .ok n.toNat
  | _ => .error "expected an immediate operand"

def intImm : Operand → Except String Int
  | .imm n => .ok n
  | _ => .error "expected an immediate operand"

def oneOperand (mnemonic : String) : List Operand → Except String Operand
  | [op] => .ok op
  | _ => .error s!"'{mnemonic}' takes exactly one operand"

def noOperands (mnemonic : String) : List Operand → Except String Unit
  | [] => .ok ()
  | _ => .error s!"'{mnemonic}' takes no operands"

/-- A memory instruction's optional byte offset: `[]` defaults to offset 0,
one immediate operand is the offset. `align` is fixed at `natural` (the
access width's natural alignment in log2 bytes): `align` is only a
validation hint in the Wasm spec (never observable at run time in this
family — `Grass.ISA.Wasm.Target.doLoad`/`doStore` do not read it), and the
generic `asmOperand` grammar has no `key=value` production to spell the
standard text's `offset=N` keyword argument — see the closing report. -/
def memArgOf (mnemonic : String) (natural : Nat) : List Operand → Except String MemArg
  | [] => .ok { align := natural, offset := 0 }
  | [op] =>
      match natImm op with
      | .error msg => .error msg
      | .ok n => .ok { align := natural, offset := n }
  | _ => .error s!"'{mnemonic}' takes at most one immediate offset operand"

/-- A `block`/`loop`/`if`'s optional single-result block type. -/
def blockTypeOf (mnemonic : String) : List Operand → Except String BlockType
  | [] => .ok .empty
  | [.symbol "i32"] => .ok (.val .i32)
  | [.symbol "i64"] => .ok (.val .i64)
  | _ => .error s!"'{mnemonic}' takes at most one result-type operand ('i32' or 'i64')"

/-! ## `lowerLine`

Every mnemonic this MVP integer family's 104-constructor `Instr` can
express. Mnemonics with no data at all (comparisons, arithmetic,
conversions, and the zero-immediate control/parametric/memory-size forms)
are a lookup table; the rest are one case each below. -/

/-- The zero-operand mnemonics: one entry per `Instr` constructor that
carries no immediate, block type, or memory argument. 70 entries: 9 control/
parametric/memory-size + 22 comparisons + 36 arithmetic + 3 conversions. -/
def zeroOperandTable : List (String × Instr) :=
  [ ("unreachable", .unreachable), ("nop", .nop), ("else", .else_), ("end", .end_)
  , ("return", .return_), ("drop", .drop), ("select", .select)
  , ("memory.size", .memorySize), ("memory.grow", .memoryGrow)
  -- i32 comparisons
  , ("i32.eqz", .i32Eqz), ("i32.eq", .i32Eq), ("i32.ne", .i32Ne)
  , ("i32.lt_s", .i32LtS), ("i32.lt_u", .i32LtU), ("i32.gt_s", .i32GtS), ("i32.gt_u", .i32GtU)
  , ("i32.le_s", .i32LeS), ("i32.le_u", .i32LeU), ("i32.ge_s", .i32GeS), ("i32.ge_u", .i32GeU)
  -- i64 comparisons
  , ("i64.eqz", .i64Eqz), ("i64.eq", .i64Eq), ("i64.ne", .i64Ne)
  , ("i64.lt_s", .i64LtS), ("i64.lt_u", .i64LtU), ("i64.gt_s", .i64GtS), ("i64.gt_u", .i64GtU)
  , ("i64.le_s", .i64LeS), ("i64.le_u", .i64LeU), ("i64.ge_s", .i64GeS), ("i64.ge_u", .i64GeU)
  -- i32 arithmetic
  , ("i32.clz", .i32Clz), ("i32.ctz", .i32Ctz), ("i32.popcnt", .i32Popcnt)
  , ("i32.add", .i32Add), ("i32.sub", .i32Sub), ("i32.mul", .i32Mul)
  , ("i32.div_s", .i32DivS), ("i32.div_u", .i32DivU)
  , ("i32.rem_s", .i32RemS), ("i32.rem_u", .i32RemU)
  , ("i32.and", .i32And), ("i32.or", .i32Or), ("i32.xor", .i32Xor)
  , ("i32.shl", .i32Shl), ("i32.shr_s", .i32ShrS), ("i32.shr_u", .i32ShrU)
  , ("i32.rotl", .i32Rotl), ("i32.rotr", .i32Rotr)
  -- i64 arithmetic
  , ("i64.clz", .i64Clz), ("i64.ctz", .i64Ctz), ("i64.popcnt", .i64Popcnt)
  , ("i64.add", .i64Add), ("i64.sub", .i64Sub), ("i64.mul", .i64Mul)
  , ("i64.div_s", .i64DivS), ("i64.div_u", .i64DivU)
  , ("i64.rem_s", .i64RemS), ("i64.rem_u", .i64RemU)
  , ("i64.and", .i64And), ("i64.or", .i64Or), ("i64.xor", .i64Xor)
  , ("i64.shl", .i64Shl), ("i64.shr_s", .i64ShrS), ("i64.shr_u", .i64ShrU)
  , ("i64.rotl", .i64Rotl), ("i64.rotr", .i64Rotr)
  -- conversions
  , ("i32.wrap_i64", .i32WrapI64)
  , ("i64.extend_i32_s", .i64ExtendI32S), ("i64.extend_i32_u", .i64ExtendI32U) ]

/-- What `lowerLine` may read to resolve a symbolic name: the function
index a `call NAME` reaches, in the joint import/function index space
(`Directives.envOf`). Everything else this mnemonic family needs is either
a literal immediate already (`i32.const N`, `local.get N`, `br N`, ...) or a
`MemArg`/`BlockType` parsed off the instruction's own operands. -/
structure Env where
  funcIndex : String → Option Nat

/-- The five directive keywords: recognized by name only, so a directive
line lowers to no instructions regardless of which `Line` constructor the
parser used to build it (see the file docstring). -/
def directiveNames : List String := ["import", "func", "export", "memory", "data"]

/-- One authored mnemonic, resolved to the `Instr` (or two, for `br_table`'s
labels-then-default shape — still exactly one `Instr` here) it denotes.
Covers every `Instr` constructor; any other name is a refusal. -/
def lowerMnemonic (mnemonic : String) (operands : List Operand) (env : Env) :
    Except String (List Instr) :=
  if directiveNames.contains mnemonic then .ok [] else
  match zeroOperandTable.lookup mnemonic with
  | some instr =>
      match noOperands mnemonic operands with
      | .error msg => .error msg
      | .ok () => .ok [instr]
  | none =>
    match mnemonic with
    | "i32.const" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op =>
            match intImm op with
            | .error msg => .error msg
            | .ok n => .ok [.i32Const (BitVec.ofInt 32 n)]
    | "i64.const" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op =>
            match intImm op with
            | .error msg => .error msg
            | .ok n => .ok [.i64Const (BitVec.ofInt 64 n)]
    | "local.get" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.localGet n]
    | "local.set" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.localSet n]
    | "local.tee" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.localTee n]
    | "global.get" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.globalGet n]
    | "global.set" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.globalSet n]
    | "br" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.br n]
    | "br_if" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op => match natImm op with
          | .error msg => .error msg
          | .ok n => .ok [.brIf n]
    | "br_table" =>
        match operands.mapM natImm with
        | .error msg => .error msg
        | .ok ns =>
            match ns.reverse with
            | [] => .error "'br_table' requires at least a default label"
            | default :: revLabels => .ok [.brTable revLabels.reverse default]
    | "call" =>
        match oneOperand mnemonic operands with
        | .error msg => .error msg
        | .ok op =>
            match symbolName op with
            | .error msg => .error msg
            | .ok name =>
                match env.funcIndex name with
                | some idx => .ok [.call idx]
                | none => .error s!"'call' target '{name}' does not name a declared import or function"
    | "call_indirect" =>
        match operands with
        | [a, b] =>
            match natImm a with
            | .error msg => .error msg
            | .ok ty =>
                match natImm b with
                | .error msg => .error msg
                | .ok table => .ok [.callIndirect ty table]
        | _ => .error "'call_indirect' takes exactly two immediate operands: type, table"
    | "block" =>
        match blockTypeOf mnemonic operands with
        | .error msg => .error msg
        | .ok bt => .ok [.block bt]
    | "loop" =>
        match blockTypeOf mnemonic operands with
        | .error msg => .error msg
        | .ok bt => .ok [.loop bt]
    | "if" =>
        match blockTypeOf mnemonic operands with
        | .error msg => .error msg
        | .ok bt => .ok [.if_ bt]
    | "i32.load" => (memArgOf mnemonic 2 operands).map (fun m => [.i32Load m])
    | "i64.load" => (memArgOf mnemonic 3 operands).map (fun m => [.i64Load m])
    | "i32.load8_s" => (memArgOf mnemonic 0 operands).map (fun m => [.i32Load8S m])
    | "i32.load8_u" => (memArgOf mnemonic 0 operands).map (fun m => [.i32Load8U m])
    | "i32.load16_s" => (memArgOf mnemonic 1 operands).map (fun m => [.i32Load16S m])
    | "i32.load16_u" => (memArgOf mnemonic 1 operands).map (fun m => [.i32Load16U m])
    | "i64.load8_s" => (memArgOf mnemonic 0 operands).map (fun m => [.i64Load8S m])
    | "i64.load8_u" => (memArgOf mnemonic 0 operands).map (fun m => [.i64Load8U m])
    | "i64.load16_s" => (memArgOf mnemonic 1 operands).map (fun m => [.i64Load16S m])
    | "i64.load16_u" => (memArgOf mnemonic 1 operands).map (fun m => [.i64Load16U m])
    | "i64.load32_s" => (memArgOf mnemonic 2 operands).map (fun m => [.i64Load32S m])
    | "i64.load32_u" => (memArgOf mnemonic 2 operands).map (fun m => [.i64Load32U m])
    | "i32.store" => (memArgOf mnemonic 2 operands).map (fun m => [.i32Store m])
    | "i64.store" => (memArgOf mnemonic 3 operands).map (fun m => [.i64Store m])
    | "i32.store8" => (memArgOf mnemonic 0 operands).map (fun m => [.i32Store8 m])
    | "i32.store16" => (memArgOf mnemonic 1 operands).map (fun m => [.i32Store16 m])
    | "i64.store8" => (memArgOf mnemonic 0 operands).map (fun m => [.i64Store8 m])
    | "i64.store16" => (memArgOf mnemonic 1 operands).map (fun m => [.i64Store16 m])
    | "i64.store32" => (memArgOf mnemonic 2 operands).map (fun m => [.i64Store32 m])
    | _ => .error s!"unsupported mnemonic '{mnemonic}'"

/-- One authored line: a label emits nothing (purely structural, see
`labelBodies`), an instruction or directive line lowers by mnemonic name. -/
def lowerLine (line : Line) (env : Env) : Except String (List Instr) :=
  match line with
  | .label _ _ => .ok []
  | .instruction mnemonic operands _ => lowerMnemonic mnemonic operands env
  | .directive mnemonic operands _ => lowerMnemonic mnemonic operands env

/-- A run of lines lowered and concatenated in order: one function's whole
body. -/
def lowerBody : List Line → Env → Except String (List Instr)
  | [], _ => .ok []
  | line :: rest, env =>
      match lowerLine line env with
      | .error msg => .error msg
      | .ok here =>
          match lowerBody rest env with
          | .error msg => .error msg
          | .ok later => .ok (here ++ later)

/-- Concatenating a lowered run over `before ++ rest` splits at the same
point: the line-order counterpart of `Grass.Assembly.Lower.Lowering.
emit_append` for this ISA, and the content of `assemble_functions_encode`
below once specialized to one function's body. -/
theorem lowerBody_append (env : Env) :
    ∀ (before rest : List Line) (out : List Instr),
      lowerBody (before ++ rest) env = .ok out →
      ∃ head tail, out = head ++ tail ∧
        lowerBody before env = .ok head ∧ lowerBody rest env = .ok tail := by
  intro before
  induction before with
  | nil =>
      intro rest out lowered
      simp only [List.nil_append] at lowered
      exact ⟨[], out, by simp, by rw [lowerBody], lowered⟩
  | cons line before ih =>
      intro rest out lowered
      rw [List.cons_append, lowerBody] at lowered
      split at lowered
      · simp at lowered
      · rename_i here headLowered
        split at lowered
        · simp at lowered
        · rename_i later tailLowered
          cases lowered
          obtain ⟨head, tail, splitOut, headEq, tailEq⟩ := ih rest later tailLowered
          refine ⟨here ++ head, tail, ?_, ?_, tailEq⟩
          · rw [splitOut, List.append_assoc]
          · rw [lowerBody, headLowered, headEq]

/-! ## Splitting a source into function bodies by label

A function's body is every line between its declared label and the next
label (or the end of the source): purely structural, so it needs no `Env`
and cannot fail. -/

private def stepLabelBodies :
    List Line → Option String → List Line → List (String × List Line) →
      List (String × List Line)
  | [], current, body, acc =>
      match current with
      | some name => acc ++ [(name, body.reverse)]
      | none => acc
  | .label name _ :: rest, current, body, acc =>
      let acc' := match current with
        | some prevName => acc ++ [(prevName, body.reverse)]
        | none => acc
      stepLabelBodies rest (some name) [] acc'
  | line :: rest, current, body, acc =>
      stepLabelBodies rest current (line :: body) acc

/-- Every declared label paired with the lines from just after it up to
(not including) the next label, in source order. Lines before the first
label (the directive header) contribute no entry. -/
def labelBodies (lines : List Line) : List (String × List Line) :=
  stepLabelBodies lines none [] []

/-! ## Directives -/

/-- One parsed directive line. `import_`/`func` carry the two-part
signature `signatureOf` produces (see the file docstring's `results`
marker); `export_` names a function to export under its own name;
`memory` is the linear memory size in pages; `data` is a byte-content
directive naming a static resolved elsewhere (`Directives.statics`). -/
inductive Directive where
  | import_ (moduleName field : String) (params results : List ValType)
  | func (name : String) (params results : List ValType)
  | export_ (name : String)
  | memory (pages : Nat)
  | data (addr : Nat) (name : String)
deriving Repr

/-- Parse one directive line's name and operands, `none` for a line whose
name is not one of the five directive keywords. -/
def directiveOf (mnemonic : String) (operands : List Operand) : Except String (Option Directive) :=
  match mnemonic, operands with
  | "import", m :: f :: rest =>
      match symbolName m with
      | .error msg => .error msg
      | .ok moduleName =>
          match symbolName f with
          | .error msg => .error msg
          | .ok field =>
              match signatureOf rest with
              | .error msg => .error msg
              | .ok (params, results) => .ok (some (.import_ moduleName field params results))
  | "import", _ => .error "malformed 'import' directive: expected module, field, ..."
  | "func", n :: rest =>
      match symbolName n with
      | .error msg => .error msg
      | .ok name =>
          match signatureOf rest with
          | .error msg => .error msg
          | .ok (params, results) => .ok (some (.func name params results))
  | "func", [] => .error "malformed 'func' directive: missing name"
  | "export", [n] =>
      match symbolName n with
      | .error msg => .error msg
      | .ok name => .ok (some (.export_ name))
  | "export", _ => .error "malformed 'export' directive: expected exactly one name"
  | "memory", [op] =>
      match natImm op with
      | .error msg => .error msg
      | .ok pages => .ok (some (.memory pages))
  | "memory", _ => .error "malformed 'memory' directive: expected exactly one immediate"
  | "data", [a, n] =>
      match natImm a with
      | .error msg => .error msg
      | .ok addr =>
          match symbolName n with
          | .error msg => .error msg
          | .ok name => .ok (some (.data addr name))
  | "data", _ => .error "malformed 'data' directive: expected addr, name"
  | _, _ => .ok none

def Line.directiveOf : Line → Except String (Option Directive)
  | .label _ _ => .ok none
  | .instruction mnemonic operands _ => Grass.Assembly.Lower.Wasm.directiveOf mnemonic operands
  | .directive mnemonic operands _ => Grass.Assembly.Lower.Wasm.directiveOf mnemonic operands

/-- Every directive parsed from `source`'s lines, in source order, plus the
byte content of every static a `data` directive may name (see the file
docstring on why `statics` cannot itself be parsed from the source). -/
structure Directives where
  imports : List (String × String × List ValType × List ValType)
  funcs : List (String × List ValType × List ValType)
  exportNames : List String
  memoryPages : Nat
  data : List (Nat × String)
  statics : String → Option (List UInt8)

/-- Parse every directive line of `source`, and split them by keyword.
Exactly one `memory` directive is required. -/
def parseDirectives (source : Source) (statics : String → Option (List UInt8)) :
    Except String Directives :=
  match source.lines.mapM Line.directiveOf with
  | .error msg => .error msg
  | .ok found =>
      let ds := found.filterMap id
      let imports := ds.filterMap fun
        | .import_ m f p r => some (m, f, p, r)
        | _ => none
      let funcs := ds.filterMap fun
        | .func n p r => some (n, p, r)
        | _ => none
      let exportNames := ds.filterMap fun
        | .export_ n => some n
        | _ => none
      let memories := ds.filterMap fun
        | .memory n => some n
        | _ => none
      let dataEntries := ds.filterMap fun
        | .data a n => some (a, n)
        | _ => none
      match memories with
      | [pages] => .ok { imports, funcs, exportNames, memoryPages := pages, data := dataEntries, statics }
      | [] => .error "missing 'memory' directive"
      | _ => .error "multiple 'memory' directives"

/-- The joint import/function index space: imports first, then functions,
each in declaration order — WebAssembly Core 2.0 §2.5.3 "Indices" ("the
index space for functions ... starts with an initial section of indices for
the imports ..., followed by an index for each function ... defined within
the module itself"). This is the space `call`'s numeric encoding
(`Grass.ISA.Wasm.Target.Module.funcTypeOf`/`functionBody`) always resolves
against. -/
def Directives.jointNames (directives : Directives) : List String :=
  (directives.imports.map (fun i => i.2.1)) ++ (directives.funcs.map (fun f => f.1))

/-- The environment `lowerLine`'s `call` case reads: `NAME` resolves to its
position in the joint index space. -/
def Directives.envOf (directives : Directives) : Env :=
  { funcIndex := indexOf directives.jointNames }

/-! ## Building the module -/

/-- One `Function` per declared `func`, in order, starting at type index
`base` (the caller passes `directives.imports.length`, since import types
occupy the front of `types`): its body is `lowerBody` of the lines its
declared label demarcates. No `local` directive is implemented (see the
closing report), so every function's `locals` is empty; `local.get`/`set`/
`tee` can still reach its declared parameters, which `Grass.ISA.Wasm.Target.
beginCall` installs as the first locals regardless. -/
def buildFunctions (bodies : List (String × List Line)) (env : Env) :
    Nat → List (String × List ValType × List ValType) → Except String (List Function)
  | _, [] => .ok []
  | base, (name, _, _) :: rest =>
      match assocLookup bodies name with
      | none => .error s!"function '{name}' has no matching label"
      | some lines =>
          match lowerBody lines env with
          | .error msg => .error msg
          | .ok body =>
              match buildFunctions bodies env (base + 1) rest with
              | .error msg => .error msg
              | .ok restOut => .ok ({ typeIndex := base, locals := [], body := body } :: restOut)

/-- One `Export` per `export` directive, in order, resolving each name
through the joint index space. -/
def buildExports (nameIndex : List String) : List String → Except String (List Export)
  | [] => .ok []
  | name :: rest =>
      match indexOf nameIndex name with
      | none => .error s!"export '{name}' does not name a declared import or function"
      | some idx =>
          match buildExports nameIndex rest with
          | .error msg => .error msg
          | .ok restOut => .ok ({ name := name, funcIndex := idx } :: restOut)

/-- One `Data` segment per `data` directive, in order, resolving each name
through `statics`. -/
def buildData (statics : String → Option (List UInt8)) :
    List (Nat × String) → Except String (List Data)
  | [] => .ok []
  | (addr, name) :: rest =>
      match statics name with
      | none => .error s!"data directive names unknown static '{name}'"
      | some bytes =>
          match buildData statics rest with
          | .error msg => .error msg
          | .ok restOut => .ok ({ offset := addr, bytes := bytes } :: restOut)

/-- Assemble a source against its already-parsed directives: the module's
`types` is the imports' signatures followed by the functions' (matching
`jointNames`'s ordering exactly, so a function's `typeIndex` and its
position in the call index space are both `imports.length + i`), `imports`/
`functions`/`exports`/`data` are built by the three functions above, and
`start` is always `none` (no directive declares one). -/
def assemble (source : Source) (directives : Directives) : Except String Module :=
  let env := directives.envOf
  let bodies := labelBodies source.lines
  let importTypes := directives.imports.map (fun p => (⟨p.2.2.1, p.2.2.2⟩ : FuncType))
  let funcTypes := directives.funcs.map (fun f => (⟨f.2.1, f.2.2⟩ : FuncType))
  let importRecords : List Import :=
    (directives.imports.zip (List.range directives.imports.length)).map
      (fun (imp, i) => (⟨imp.1, imp.2.1, i⟩ : Import))
  match buildFunctions bodies env directives.imports.length directives.funcs with
  | .error msg => .error msg
  | .ok functionRecords =>
    match buildExports directives.jointNames directives.exportNames with
    | .error msg => .error msg
    | .ok exportRecords =>
      match buildData directives.statics directives.data with
      | .error msg => .error msg
      | .ok dataRecords =>
        .ok
          { types := importTypes ++ funcTypes
            imports := importRecords
            functions := functionRecords
            memoryMinPages := directives.memoryPages
            globals := []
            exports := exportRecords
            data := dataRecords
            start := none }

/-! ## Theorems -/

/-- Building one function per declared `func`, in order, from `base`: the
`i`-th output function sits at type index `base + i` and its body is
exactly the concatenated `lowerLine` output of the lines its label
demarcates — the line-order lemma `emit_append`/`lowerBody_append` gives for
a whole run, specialized here to one selected function. -/
theorem buildFunctions_getElem (bodies : List (String × List Line)) (env : Env) :
    ∀ (base : Nat) (funcs : List (String × List ValType × List ValType))
      (out : List Function) (i : Nat) (name : String) (params results : List ValType)
      (lines : List Line) (body : List Instr),
      buildFunctions bodies env base funcs = .ok out →
      funcs[i]? = some (name, params, results) →
      assocLookup bodies name = some lines →
      lowerBody lines env = .ok body →
      out[i]? = some { typeIndex := base + i, locals := [], body := body } := by
  intro base funcs
  induction funcs generalizing base with
  | nil =>
      intro out i name params results lines body _ idx _ _
      simp at idx
  | cons head rest ih =>
      obtain ⟨name0, params0, results0⟩ := head
      intro out i name params results lines body built idx foundBody lowered
      rw [buildFunctions] at built
      split at built
      · simp at built
      · rename_i ls foundLs
        split at built
        · simp at built
        · rename_i bd loweredBd
          split at built
          · simp at built
          · rename_i restOut restBuilt
            cases built
            cases i with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at idx
                obtain ⟨rfl, rfl, rfl⟩ := idx
                rw [foundLs] at foundBody
                cases foundBody
                rw [loweredBd] at lowered
                cases lowered
                simp
            | succ n =>
                simp only [List.getElem?_cons_succ] at idx
                have step := ih (base + 1) restOut n name params results lines body restBuilt idx
                  foundBody lowered
                have arith : base + 1 + n = base + (n + 1) := by omega
                rwa [arith] at step

/-- **`assemble_functions_encode`.** For an assembled module, the `i`-th
function's body is exactly the line-order concatenation of `lowerLine`
across the lines its `func` directive's label demarcates. -/
theorem assemble_functions_encode (source : Source) (directives : Directives) (module : Module)
    (built : assemble source directives = .ok module)
    (i : Nat) (name : String) (params results : List ValType) (lines : List Line)
    (body : List Instr)
    (declared : directives.funcs[i]? = some (name, params, results))
    (foundBody : assocLookup (labelBodies source.lines) name = some lines)
    (lowered : lowerBody lines directives.envOf = .ok body) :
    module.functions[i]? =
      some { typeIndex := directives.imports.length + i, locals := [], body := body } := by
  rw [assemble] at built
  split at built
  · simp at built
  · rename_i functionRecords buildOk
    split at built
    · simp at built
    · split at built
      · simp at built
      · cases built
        exact buildFunctions_getElem (labelBodies source.lines) directives.envOf
          directives.imports.length directives.funcs functionRecords i name params results
          lines body buildOk declared foundBody lowered

/-- The first occurrence of `name` in a duplicate-free list sits exactly at
`indexOf`'s answer: the whole content of the joint-index-space claim. -/
theorem indexOf_getElem (names : List String) (nodup : names.Nodup) :
    ∀ (i : Nat) (name : String), names[i]? = some name → indexOf names name = some i := by
  induction names with
  | nil => intro i name h; simp at h
  | cons head tail ih =>
      intro i name h
      rw [List.nodup_cons] at nodup
      obtain ⟨notMem, tailNodup⟩ := nodup
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp [indexOf]
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          have neq : head ≠ name := by
            intro heq
            subst heq
            exact notMem (List.mem_of_getElem? h)
          simp only [indexOf, if_neg neq]
          rw [ih tailNodup n name h]
          rfl

/-- **`assemble_import_index`.** In the joint import/function index space
(imports first, then functions, both in declaration order — the section
cited on `Directives.jointNames`), the index a `call NAME` resolves to
(`Directives.envOf`, read by `lowerLine`'s `call` case) is exactly `NAME`'s
position. -/
theorem assemble_import_index (directives : Directives) (nodup : directives.jointNames.Nodup)
    (i : Nat) (name : String) (found : directives.jointNames[i]? = some name) :
    directives.envOf.funcIndex name = some i :=
  indexOf_getElem directives.jointNames nodup i name found

/-- Building one `Export` per directive name, in order: the `i`-th output
export's name is exactly the `i`-th declared name, and its `funcIndex` is
exactly what `indexOf` resolves that name to. -/
theorem buildExports_getElem (nameIndex : List String) :
    ∀ (names : List String) (out : List Export) (i : Nat) (name : String) (idx : Nat),
      buildExports nameIndex names = .ok out →
      names[i]? = some name →
      indexOf nameIndex name = some idx →
      out[i]? = some { name := name, funcIndex := idx } := by
  intro names
  induction names with
  | nil =>
      intro out i name idx _ h _
      simp at h
  | cons head rest ih =>
      intro out i name idx built h resolved
      rw [buildExports] at built
      split at built
      · simp at built
      · rename_i idx0 foundIdx0
        split at built
        · simp at built
        · rename_i restOut restBuilt
          cases built
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              rw [foundIdx0] at resolved
              cases resolved
              simp
          | succ n =>
              simp only [List.getElem?_cons_succ] at h
              exact ih restOut n name idx restBuilt h resolved

/-- **What `Grass.ISA.Wasm.Target.initial` needs to find `_start`.** Every
declared export, at its own position, resolves to the function index
`Directives.envOf` gives its target name — exactly the pair `Module.
exportedFunc`/`entryIndex` must recover to start a program at the right
function without guessing index `0`. -/
theorem assemble_export_index (source : Source) (directives : Directives) (module : Module)
    (built : assemble source directives = .ok module)
    (i : Nat) (name : String) (idx : Nat)
    (declared : directives.exportNames[i]? = some name)
    (resolved : directives.envOf.funcIndex name = some idx) :
    module.exports[i]? = some { name := name, funcIndex := idx } := by
  rw [assemble] at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · rename_i exportRecords buildOk
      split at built
      · simp at built
      · cases built
        exact buildExports_getElem directives.jointNames directives.exportNames exportRecords i
          name idx buildOk declared resolved

/-! ## Worked example: Hello World's `_start`

The module the deleted spike built by hand
(`git show b4910fdc:Spikes/1_Hello_World/Wasi.lean` — an uncompiled citation
only, nothing here imports a spike): one `(i32 i32 i32 i32) -> i32` import
(`fd_write`), one `i32 -> ()` import (`proc_exit`), a single zero-arg
zero-result function `_start` exported under its own name, one page of
linear memory, and two data segments — the `iov` ciovec entry at address 0
and the message bytes at address 16 (`nwritten`, address 8, is scratch: no
data segment initializes it). This assembles that exact module from ordinary
text mnemonics and the five directives above instead of `Instr`/`Module`
literals. -/

open Grass.Artifact.Binary (writeU32LE) in
/-- The two data statics this source's `data` directives name: `Operand`
has no byte-literal production (the file docstring's `data` bullet), so
these are registered here rather than spelled inline. -/
def helloStatics : String → Option (List UInt8)
  | "iov" => some (writeU32LE (UInt32.ofNat 16) ++ writeU32LE (UInt32.ofNat 14))
  | "message" => some [72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33, 10]
  | _ => none

def helloSource : Source :=
  { locals := []
    callFrame := []
    lines :=
      [ .directive "import"
          [.symbol "wasi_snapshot_preview1", .symbol "fd_write",
            .symbol "i32", .symbol "i32", .symbol "i32", .symbol "i32",
            .symbol "results", .symbol "i32"] []
      , .directive "import"
          [.symbol "wasi_snapshot_preview1", .symbol "proc_exit", .symbol "i32", .symbol "results"] []
      , .directive "func" [.symbol "_start", .symbol "results"] []
      , .directive "export" [.symbol "_start"] []
      , .directive "memory" [.imm 1] []
      , .directive "data" [.imm 0, .symbol "iov"] []
      , .directive "data" [.imm 16, .symbol "message"] []
      , .label "_start" []
      , .instruction "i32.const" [.imm 1] []
      , .instruction "i32.const" [.imm 0] []
      , .instruction "i32.const" [.imm 1] []
      , .instruction "i32.const" [.imm 8] []
      , .instruction "call" [.symbol "fd_write"] []
      , .instruction "drop" [] []
      , .instruction "i32.const" [.imm 0] []
      , .instruction "call" [.symbol "proc_exit"] []
      ] }

def helloModule : Except String Module :=
  match parseDirectives helloSource helloStatics with
  | .error msg => .error msg
  | .ok directives => assemble helloSource directives

/-- `_start`'s body: exactly the 8-instruction sequence the deleted spike
authored as `Instr` literals (`startBody`), here produced by lowering
ordinary text mnemonics instead. -/
def helloStartBody : List Instr :=
  [.i32Const 1, .i32Const 0, .i32Const 1, .i32Const 8, .call 0, .drop, .i32Const 0, .call 1]

/-- The whole assembled module matches the deleted spike's hand-built one
field for field. -/
theorem helloModule_eq : helloModule = .ok
    { types := [⟨[.i32, .i32, .i32, .i32], [.i32]⟩, ⟨[.i32], []⟩, ⟨[], []⟩]
      imports :=
        [⟨"wasi_snapshot_preview1", "fd_write", 0⟩, ⟨"wasi_snapshot_preview1", "proc_exit", 1⟩]
      functions := [⟨2, [], helloStartBody⟩]
      memoryMinPages := 1
      globals := []
      exports := [⟨"_start", 2⟩]
      data :=
        [⟨0, [16, 0, 0, 0, 14, 0, 0, 0]⟩,
          ⟨16, [72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33, 10]⟩]
      start := none } := by
  rfl

/-- The four fields the task asks to check, read off `helloModule_eq` by
`simp` alone -- no `rfl` needed a second time and no `decide`. -/
example : (helloModule.map Module.exports = .ok [⟨"_start", 2⟩]) ∧
    (helloModule.map Module.imports = .ok
      [⟨"wasi_snapshot_preview1", "fd_write", 0⟩, ⟨"wasi_snapshot_preview1", "proc_exit", 1⟩]) ∧
    (helloModule.map Module.data = .ok
      [⟨0, [16, 0, 0, 0, 14, 0, 0, 0]⟩,
        ⟨16, [72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33, 10]⟩]) ∧
    (helloModule.map Module.functions = .ok [⟨2, [], helloStartBody⟩]) := by
  rw [helloModule_eq]
  refine ⟨rfl, rfl, rfl, rfl⟩

end Grass.Assembly.Lower.Wasm
