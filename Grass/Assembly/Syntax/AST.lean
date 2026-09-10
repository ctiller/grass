import Lean

/-! Target-generic authored-assembly AST. This is the elaboration target of
the `asm_source { ... }` front end (`Grass/Assembly/Syntax/Parser.lean`): a
plain ordered list of lines, with operands and annotations kept in a form
that names no ISA. Lowering a `Source` to a concrete ISA `Instr` is a later,
separate module; nothing here interprets a mnemonic, a register name, or an
annotation tag. No program's label names, register choices, or instruction
sequence may appear in this file. -/
namespace Grass.Assembly.Syntax

/-- The explicit operand size written before a memory reference
(`byte ptr`, `word ptr`, `dword ptr`, `qword ptr`). Absent when the source
left the size to be inferred from the other operand. -/
inductive MemSize where
  | byte | word | dword | qword
deriving Repr, DecidableEq, Inhabited

/-- The displacement carried by a memory operand. -/
inductive Displacement where
  /-- A literal integer displacement, e.g. the `-1` in `[r14-1]`. -/
  | int (value : Int)
  /-- A named displacement resolved elsewhere, e.g. `LineDesc.offset` in
  `[left + LineDesc.offset]` or a frame field in `[rsp+SortFrame.flushPtr]`. -/
  | symbol (name : String)
  /-- `[rip + name]`: a RIP-relative reference to a named object. No base or
  index register accompanies this form. -/
  | ripRelative (name : String)
deriving Repr, DecidableEq, Inhabited

/-- One operand of an authored instruction or directive, target-generic:
nothing here is specific to x86-64 or to any other ISA beyond the operand
*shapes* the Intel-syntax front end accepts. -/
inductive Operand where
  /-- A bare register name as written, e.g. `rax`, `r14d`, `al`. -/
  | reg (name : String)
  /-- A literal integer immediate. -/
  | imm (value : Int)
  /-- A bare symbolic name that is neither a known register nor a declared
  frame local: an imported/static/platform constant (e.g. a well-known
  handle or status value), a label used as a jump target, or a qualified
  field name such as `owner.field`. -/
  | symbol (name : String)
  /-- `sizeof(name)`. -/
  | sizeOf (name : String)
  /-- A memory reference `[...]`, optionally prefixed by an explicit size. -/
  | mem (size : Option MemSize) (base : Option String)
      (index : Option (String × Nat)) (disp : Displacement)
  /-- A frame local declared by `withStack`, used by value (`mov name, 0`). -/
  | local (name : String)
  /-- The address of a frame local declared by `withStack` (`name.addr`). -/
  | localAddress (name : String)
deriving Repr, DecidableEq, Inhabited

/-- One authored annotation attached to a label or to an instruction. The
`Lean.Name` arguments are opaque tags: this front end never interprets or
constrains them, it only carries them for a later consumer. -/
inductive Annotation where
  /-- `@placement [key := operand, ...]`. -/
  | placement (bindings : List (String × Operand))
  /-- `@invariant name(arg, ...)`. -/
  | invariant (name : String) (args : List String)
  /-- `@terminal(.tag)`. -/
  | terminal (outcome : Lean.Name)
  /-- `@audit(.tag)`. -/
  | audit (tag : Lean.Name)
  /-- `@violation_edge(.tag)`. -/
  | violationEdge (tag : Lean.Name)
  /-- `@containment_tail(.tag)`. -/
  | containmentTail (tag : Lean.Name)
deriving Repr, DecidableEq, Inhabited

/-- One line of an authored `asm_source` body. -/
inductive Line where
  /-- `name:`, with any annotations attached to it. -/
  | label (name : String) (annotations : List Annotation)
  /-- An ISA instruction, named only by its mnemonic spelling: this front end
  does not know which mnemonics exist or what shape their operands must take. -/
  | instruction (mnemonic : String) (operands : List Operand) (annotations : List Annotation)
  /-- A non-instruction directive, e.g. `arg callee.field, 0`. -/
  | directive (name : String) (operands : List Operand) (annotations : List Annotation)
deriving Repr, DecidableEq, Inhabited

/-- A named stack-frame local declared by `withStack (name : type := init)`. -/
structure Local where
  name : String
  type : String
  init : Int
deriving Repr, DecidableEq, Inhabited

/-- A fully parsed authored source: the `withStack`/`withCallFrame` header
(carried for a later frame-layout consumer; this front end never interprets
`type` beyond its spelling) together with the ordered body lines. -/
structure Source where
  locals : List Local
  callFrame : List String
  lines : List Line
deriving Repr, DecidableEq, Inhabited

deriving instance Lean.ToExpr for MemSize
deriving instance Lean.ToExpr for Displacement
deriving instance Lean.ToExpr for Operand
deriving instance Lean.ToExpr for Annotation
deriving instance Lean.ToExpr for Line
deriving instance Lean.ToExpr for Local
deriving instance Lean.ToExpr for Source

/-- The set of x86-64 general-purpose register spellings this front end
recognizes as `Operand.reg` rather than a bare symbol. This is ordinary ISA
register-naming knowledge (every width form of every GPR), not knowledge of
any particular program's register allocation. -/
def registerNames : List String :=
  ["rax","rbx","rcx","rdx","rsi","rdi","rbp","rsp",
    "r8","r9","r10","r11","r12","r13","r14","r15",
    "eax","ebx","ecx","edx","esi","edi","ebp","esp",
    "r8d","r9d","r10d","r11d","r12d","r13d","r14d","r15d",
    "ax","bx","cx","dx","si","di","bp","sp",
    "r8w","r9w","r10w","r11w","r12w","r13w","r14w","r15w",
    "al","bl","cl","dl","sil","dil","bpl","spl",
    "r8b","r9b","r10b","r11b","r12b","r13b","r14b","r15b",
    "ah","bh","ch","dh"]

/-- Whether `name` is a recognized x86-64 GPR spelling. -/
def isRegisterName (name : String) : Bool := registerNames.contains name

/-- Rewrite every bare-symbol operand whose name matches a declared local
into `Operand.local`. Parsing cannot tell a local apart from any other bare
symbolic name (a static constant, an imported symbol, a label used as a jump
target): only the header, once parsed, knows which names are locals. -/
def Operand.resolveLocals (locals : List String) : Operand → Operand
  | .symbol name => if locals.contains name then .local name else .symbol name
  | other => other

/-- Rewrite every `Operand.symbol` naming a declared local, throughout an
annotation, to `Operand.local`. -/
def Annotation.resolveLocals (locals : List String) : Annotation → Annotation
  | .placement bindings => .placement (bindings.map fun (k, v) => (k, v.resolveLocals locals))
  | other => other

/-- Rewrite every `Operand.symbol` naming a declared local, throughout a
line's operands and annotations, to `Operand.local`. -/
def Line.resolveLocals (locals : List String) : Line → Line
  | .label name annotations => .label name (annotations.map (·.resolveLocals locals))
  | .instruction mnemonic operands annotations =>
      .instruction mnemonic (operands.map (·.resolveLocals locals))
        (annotations.map (·.resolveLocals locals))
  | .directive name operands annotations =>
      .directive name (operands.map (·.resolveLocals locals))
        (annotations.map (·.resolveLocals locals))

/-- Resolve every bare-symbol operand that names one of `source.locals`
into `Operand.local`, throughout `source.lines`. Applied once, after the
header is parsed, so the per-line grammar never has to guess whether a bare
name is a local. -/
def Source.resolveLocals (source : Source) : Source :=
  { source with lines := source.lines.map (·.resolveLocals (source.locals.map Local.name)) }

end Grass.Assembly.Syntax
