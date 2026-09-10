import Lean
import Lean.Elab.Term
import Grass.Assembly.Syntax.AST

/-! The authored `asm_source { ... }` front end: an x86-64 Intel-syntax and
AArch64 operand grammar (registers, immediates, `[...]` memory references,
`sizeof(...)`, frame-local operands) elaborated to the target-generic
`Grass.Assembly.Syntax.Source` AST. Nothing here knows a program's label
names, register allocation, or instruction schedule; every keyword below is
ordinary Intel-syntax or A64 vocabulary (`ptr`, `qword`, `rip`, ...) or an
annotation name the spikes already use (`@placement`, `@invariant`, ...).
Every mnemonic, including a dotted A64 spelling such as `b.eq`, is accepted
uniformly through the ordinary `ident` grammar this front end already used
for x86 mnemonics: this front end supports every mnemonic spelling and does
not know which ones exist, so an A64-specific mnemonic needs no grammar
change, only operands and register spellings it did not previously
recognize. Lowering a `Source` to a concrete ISA `Instr` is a later, separate
module. -/
namespace Grass.Assembly.Syntax

open Lean Lean.Parser

/-! ## Non-reserving keyword tokens

Every word below can still be used as an ordinary identifier anywhere else
in the codebase: `nonReservedSymbol` only turns the word into that keyword
at the exact grammar position that names it, following the pattern already
used by `Grass.Assembly.StaticObjects`. -/

def asmSourceKw : Parser := nonReservedSymbol "asm_source" true
def withStackKw : Parser := nonReservedSymbol "withStack" true
def withCallFrameKw : Parser := nonReservedSymbol "withCallFrame" true
def ptrKw : Parser := nonReservedSymbol "ptr" true
def byteSizeKw : Parser := nonReservedSymbol "byte" true
def wordSizeKw : Parser := nonReservedSymbol "word" true
def dwordSizeKw : Parser := nonReservedSymbol "dword" true
def qwordSizeKw : Parser := nonReservedSymbol "qword" true
def ripKw : Parser := nonReservedSymbol "rip" true
def sizeofKw : Parser := nonReservedSymbol "sizeof" true
def placementKw : Parser := nonReservedSymbol "placement" true
def invariantKw : Parser := nonReservedSymbol "invariant" true
def terminalKw : Parser := nonReservedSymbol "terminal" true
def auditKw : Parser := nonReservedSymbol "audit" true
def violationEdgeKw : Parser := nonReservedSymbol "violation_edge" true
def containmentTailKw : Parser := nonReservedSymbol "containment_tail" true

/-! ## Memory-operand grammar -/

declare_syntax_cat asmMemSize
syntax (name := asmMemSizeByte) byteSizeKw : asmMemSize
syntax (name := asmMemSizeWord) wordSizeKw : asmMemSize
syntax (name := asmMemSizeDword) dwordSizeKw : asmMemSize
syntax (name := asmMemSizeQword) qwordSizeKw : asmMemSize

/-- One `+`/`-`-signed term following the base of a `[...]` memory
reference: a possibly-scaled register (the index) or a literal integer. A
non-register identifier term is disambiguated from an index by
`isRegisterName` once parsing is done, not by the grammar. -/
declare_syntax_cat asmMemTerm
syntax (name := asmMemTermAddIdent) "+" ident ("*" num)? : asmMemTerm
syntax (name := asmMemTermSubIdent) "-" ident ("*" num)? : asmMemTerm
syntax (name := asmMemTermAddNum) "+" num : asmMemTerm
syntax (name := asmMemTermSubNum) "-" num : asmMemTerm

declare_syntax_cat asmMemBody
/-- `rip + name`, tried before the general base form so that `rip` is never
mistaken for a base register. -/
syntax (name := asmMemBodyRip) (priority := high) ripKw "+" ident : asmMemBody
/-- AArch64 `[base, #disp]`, e.g. `[x1, #16]`, `[sp, #-8]`. Tried before the
general base form: the comma is not a token `asmMemBodyGeneral`'s
`asmMemTerm` repetition ever consumes, so without this dedicated production
`[x1, #16]` would parse `x1` as a zero-term general body and then fail to
find the closing `]` right after it. `[base]` alone (no comma) is already
covered by `asmMemBodyGeneral` with zero terms, giving the same zero
displacement this AArch64 form would. -/
syntax (name := asmMemBodyAArch64Offset) (priority := high)
  ident "," "#" ("-")? num : asmMemBody
/-- `base` followed by zero or more signed terms, e.g. `rax`, `rax+r9`,
`rbx+rax*2`, `r9+rdi*2+2`, `rsp+SortFrame.flushPtr`, `r14-1`, or a bare
AArch64 base with an implicit zero offset, e.g. `x1`. -/
syntax (name := asmMemBodyGeneral) ident (asmMemTerm)* : asmMemBody

/-! AArch64's `!` (pre-index) and `, #disp` (post-index) memory suffixes,
written after the closing `]` of an `asmOperandMem`. Declared as their own
category, rather than as two more sibling `asmOperand` productions, so the
choice between "no suffix", "!", and ", #disp" is one optional slot inside
the single existing `asmOperandMem` rule instead of three separately-
prioritized alternatives racing each other on the shared `[`/`]` prefix: a
plain `[base]` operand followed by a real next operand starting with `,`
(the ordinary x86 case, e.g. `mov [rsp+SortFrame.flushPtr], rax`) must fail
`asmMemSuffixPostIndex` and leave the `,` for the operand list's own
separator, exactly as before this addition. `atomic` on the `"," "#"` pair
is required for that: without it, a partial match (the `,` present, but not
followed by `#`) is a hard parse error rather than a clean "this alternative
does not apply", since Lean's `(asmMemSuffix)?` does not itself roll back a
failure that already consumed a token. -/
declare_syntax_cat asmMemSuffix
syntax (name := asmMemSuffixPreIndex) "!" : asmMemSuffix
syntax (name := asmMemSuffixPostIndex) atomic("," "#") ("-")? num : asmMemSuffix

/-! ## Operand grammar -/

declare_syntax_cat asmOperand

/-- `sizeof(name)`, tried before the bare-identifier form so `sizeof` is
never mistaken for a symbol operand. -/
syntax (name := asmOperandSizeOf) (priority := high) sizeofKw "(" ident ")" : asmOperand
/-- A memory reference, with or without an explicit size prefix, and with or
without an AArch64 pre-index or post-index suffix (`asmMemSuffix`):
`[base+disp]`, `[rip+name]`, `[base, #disp]`, `[base, #disp]!`, or
`[base], #disp`. -/
syntax (name := asmOperandMem) (priority := high)
  (asmMemSize ptrKw)? "[" asmMemBody "]" (asmMemSuffix)? : asmOperand
/-- A negative integer immediate. -/
syntax (name := asmOperandNegImm) (priority := high) "-" num : asmOperand
/-- A non-negative integer immediate. -/
syntax (name := asmOperandImm) num : asmOperand
/-- An AArch64 `#`-prefixed immediate, e.g. `#0`, `#64`, `#-16`. -/
syntax (name := asmOperandHashImm) "#" ("-")? num : asmOperand
/-- A bare name: a register, a declared frame local, `name.addr`, or any
other symbolic constant. Disambiguated after parsing. -/
syntax (name := asmOperandBare) ident : asmOperand

/-! ## Annotation grammar -/

declare_syntax_cat asmPlacementBinding
syntax (name := asmPlacementBindingDecl) ident ":=" asmOperand : asmPlacementBinding

declare_syntax_cat asmAnnotation
syntax (name := asmAnnotationPlacement)
  "@" placementKw "[" asmPlacementBinding,* "]" : asmAnnotation
syntax (name := asmAnnotationInvariant)
  "@" invariantKw ident "(" ident,* ")" : asmAnnotation
syntax (name := asmAnnotationTerminal)
  "@" terminalKw "(" "." ident ")" : asmAnnotation
syntax (name := asmAnnotationAudit)
  "@" auditKw "(" "." ident ")" : asmAnnotation
syntax (name := asmAnnotationViolationEdge)
  "@" violationEdgeKw "(" "." ident ")" : asmAnnotation
syntax (name := asmAnnotationContainmentTail)
  "@" containmentTailKw "(" "." ident ")" : asmAnnotation

/-! ## Line grammar -/

declare_syntax_cat asmLine
/-- `name: @annotation ...`, tried before the instruction form so a label's
trailing `:` is never left for the instruction form to choke on. -/
syntax (name := asmLineLabel) (priority := high)
  ident ":" (asmAnnotation)* : asmLine
/-- `mnemonic operand, ... @annotation ...`. The mnemonic is captured as a
bare string: this front end supports every mnemonic spelling uniformly and
does not know which ones exist. A directive such as `arg` uses the identical
shape and is told apart afterwards, by name, not by grammar. Operands are
required to stay on the mnemonic's own source line (`checkLineEq`, inside
`withPosition`): without that guard a zero- or short-operand instruction
(`ud2`, `jmp loop_head`) would greedily swallow the next physical line's
label or mnemonic as if it were one more operand, since nothing else marks
the end of a statement in this newline-insensitive grammar. Annotations are
exempt: `label: @placement [...] \n @invariant name(...)` authors a second
annotation on its own continuation line. -/
syntax (name := asmLineInstruction)
  withPosition(ident (lineEq asmOperand),*) (asmAnnotation)* : asmLine

/-! ## Header and top-level `asm_source` grammar -/

declare_syntax_cat asmSourceArg
/-- `key := term`, e.g. `statics := someStaticObjectTable`. The term is
captured syntactically only: it is never elaborated by this front end, so a
name it mentions need not resolve here. Lowering/frame-construction
consumers that need the value belong to a later module. -/
syntax (name := asmSourceArgDecl) ident ":=" term : asmSourceArg

declare_syntax_cat asmWithStackClause
syntax (name := asmWithStackClauseDecl)
  withStackKw "(" ident ":" ident ":=" ("-")? num ")" : asmWithStackClause

syntax (name := asmSourceTerm)
  (asmWithStackClause)* (withCallFrameKw ident,*)?
  asmSourceKw ("(" asmSourceArg,* ")")? "{" (asmLine)* "}" : term

/-! ## From concrete syntax to the `Source` AST

Every production above is turned into `Source`/`Line`/`Operand` data by plain
(non-monadic-in-`Expr`) functions over `Syntax`, using the exact argument
layout each `syntax` declaration produces. The `asm_source (statics := t)`
argument term `t` is captured only so the grammar accepts it: it is never
elaborated here (no name it mentions is looked up), so it need not resolve
until a later lowering module chooses to use it. -/

private def identText (stx : Syntax) : String := stx.getId.toString

private def natOf (stx : Syntax) : Except String Nat :=
  match stx.isNatLit? with
  | some n => .ok n
  | none => .error s!"expected a numeral, got '{stx}'"

/-- A numeral preceded by an optional `-` group (the shape every
`("-")? num` production above uses: `asmWithStackClauseDecl`'s init,
`asmOperandNegImm`, `asmOperandHashImm`, `asmMemBodyAArch64Offset`,
`asmMemSuffixPostIndex`), as a signed `Int`. `negGroup` is the optional
node itself (empty when `-` was absent), not the `-` token. -/
private def signedNumOf (negGroup : Syntax) (numStx : Syntax) : Except String Int := do
  let n ← natOf numStx
  pure <| if negGroup.getArgs.isEmpty then Int.ofNat n else -(Int.ofNat n)

/-- The result of classifying one signed term following a memory operand's
base register: a possibly-scaled index register, a symbolic displacement, or
a literal integer contribution to the displacement. -/
private inductive MemTermResult where
  | index (name : String) (scale : Nat)
  | symbolDisp (name : String)
  | intDisp (value : Int)

private def memScaleOf (group : Syntax) : Except String Nat :=
  if group.getArgs.isEmpty then pure 1 else natOf (group.getArg 1)

private def memTermOf (stx : Syntax) : Except String MemTermResult :=
  match stx.getKind with
  | ``asmMemTermAddIdent | ``asmMemTermSubIdent => do
    let name := identText (stx.getArg 1)
    let scale ← memScaleOf (stx.getArg 2)
    pure <| if isRegisterName name then .index name scale else .symbolDisp name
  | ``asmMemTermAddNum => do
    let n ← natOf (stx.getArg 1)
    pure (.intDisp (Int.ofNat n))
  | ``asmMemTermSubNum => do
    let n ← natOf (stx.getArg 1)
    pure (.intDisp (-(Int.ofNat n)))
  | k => .error s!"unsupported memory operand term '{k}'"

/-- Combine the signed terms following a memory operand's base into an
optional scaled index and a displacement. At most one index register and at
most one displacement symbol are supported; every literal integer term adds
into a single accumulated displacement. -/
private abbrev MemTermAcc := Option (String × Nat) × Option String × Int

private def stepMemTerm (acc : MemTermAcc) (term : MemTermResult) : Except String MemTermAcc :=
  let (index, symbolDisp, intDisp) := acc
  match term with
  | .index name scale =>
    if index.isSome then
      .error "at most one index register is supported in a memory operand"
    else .ok (some (name, scale), symbolDisp, intDisp)
  | .symbolDisp name =>
    if symbolDisp.isSome then
      .error "at most one displacement symbol is supported in a memory operand"
    else .ok (index, some name, intDisp)
  | .intDisp value => .ok (index, symbolDisp, intDisp + value)

private def combineMemTerms (terms : List MemTermResult) :
    Except String (Option (String × Nat) × Displacement) := do
  let (index, symbolDisp, intDisp) ←
    terms.foldlM stepMemTerm ((none : Option (String × Nat)), (none : Option String), (0 : Int))
  pure (index, match symbolDisp with
    | some name => .symbol name
    | none => .int intDisp)

private def memBodyOf (stx : Syntax) :
    Except String (Option String × Option (String × Nat) × Displacement) :=
  match stx.getKind with
  | ``asmMemBodyRip => do
    let name := identText (stx.getArg 2)
    pure (none, none, .ripRelative name)
  | ``asmMemBodyGeneral => do
    let base := identText (stx.getArg 0)
    if !isRegisterName base then
      throw s!"'{base}' is not a recognized register and cannot be a memory base"
    let terms ← (stx.getArg 1).getArgs.toList.mapM memTermOf
    let (index, disp) ← combineMemTerms terms
    pure (some base, index, disp)
  | ``asmMemBodyAArch64Offset => do
    let base := identText (stx.getArg 0)
    if !isRegisterName base then
      throw s!"'{base}' is not a recognized register and cannot be a memory base"
    let value ← signedNumOf (stx.getArg 3) (stx.getArg 4)
    pure (some base, none, .int value)
  | k => .error s!"unsupported memory operand '{k}'"

private def memSizeOf (stx : Syntax) : Except String MemSize :=
  match stx.getKind with
  | ``asmMemSizeByte => .ok .byte
  | ``asmMemSizeWord => .ok .word
  | ``asmMemSizeDword => .ok .dword
  | ``asmMemSizeQword => .ok .qword
  | k => .error s!"unsupported memory operand size '{k}'"

/-- A bare name that is not a register: `name.addr` is the address of a
frame local, everything else is a symbolic constant (a static/import name,
or a label used as a jump target) until `Source.resolveLocals` rewrites the
ones that name a declared local into `Operand.local`. -/
private def bareNameOperand (name : String) : Operand :=
  match name.splitOn "." with
  | [prefix_, "addr"] => .localAddress prefix_
  | _ => .symbol name

private partial def operandOf (stx : Syntax) : Except String Operand :=
  match stx.getKind with
  | ``asmOperandBare =>
    let name := identText (stx.getArg 0)
    .ok <| if isRegisterName name then .reg name else bareNameOperand name
  | ``asmOperandImm => do
    let n ← natOf (stx.getArg 0)
    pure (.imm (Int.ofNat n))
  | ``asmOperandNegImm => do
    let n ← natOf (stx.getArg 1)
    pure (.imm (-(Int.ofNat n)))
  | ``asmOperandHashImm => do
    let value ← signedNumOf (stx.getArg 1) (stx.getArg 2)
    pure (.imm value)
  | ``asmOperandSizeOf =>
    .ok (.sizeOf (identText (stx.getArg 2)))
  | ``asmOperandMem => do
    let sizeGroup := stx.getArg 0
    let size ← if sizeGroup.getArgs.isEmpty then pure none
      else some <$> memSizeOf (sizeGroup.getArg 0)
    let (base, index, disp) ← memBodyOf (stx.getArg 2)
    let suffixGroup := stx.getArg 4
    if suffixGroup.getArgs.isEmpty then
      pure (.mem size base index disp .offset)
    else
      let suffix := suffixGroup.getArg 0
      match suffix.getKind with
      | ``asmMemSuffixPreIndex => pure (.mem size base index disp .preIndex)
      | ``asmMemSuffixPostIndex => do
          let value ← signedNumOf (suffix.getArg 2) (suffix.getArg 3)
          pure (.mem size base index (.int value) .postIndex)
      | k => .error s!"unsupported memory operand suffix '{k}'"
  | k => .error s!"unsupported operand '{k}'"

private def annotationOf (stx : Syntax) : Except String Annotation :=
  match stx.getKind with
  | ``asmAnnotationPlacement => do
    let bindings ← (stx.getArg 3).getSepArgs.toList.mapM fun binding => do
      let key := identText (binding.getArg 0)
      let value ← operandOf (binding.getArg 2)
      pure (key, value)
    pure (.placement bindings)
  | ``asmAnnotationInvariant => do
    let name := identText (stx.getArg 2)
    let args := ((stx.getArg 4).getSepArgs.toList.map identText)
    pure (.invariant name args)
  | ``asmAnnotationTerminal => .ok (.terminal (stx.getArg 4).getId)
  | ``asmAnnotationAudit => .ok (.audit (stx.getArg 4).getId)
  | ``asmAnnotationViolationEdge => .ok (.violationEdge (stx.getArg 4).getId)
  | ``asmAnnotationContainmentTail => .ok (.containmentTail (stx.getArg 4).getId)
  | k => .error s!"unsupported annotation '{k}'"

/-- Mnemonic spellings that are directives rather than ISA instructions. Only
`arg` is authored today; `.align` is a future directive, not a mnemonic, so
adding it here extends this list without touching instruction handling. -/
private def directiveNames : List String := ["arg"]

private def lineOf (stx : Syntax) : Except String Line :=
  match stx.getKind with
  | ``asmLineLabel => do
    let name := identText (stx.getArg 0)
    let annotations ← (stx.getArg 2).getArgs.toList.mapM annotationOf
    pure (.label name annotations)
  | ``asmLineInstruction => do
    let mnemonic := identText (stx.getArg 0)
    let operands ← (stx.getArg 1).getSepArgs.toList.mapM operandOf
    let annotations ← (stx.getArg 2).getArgs.toList.mapM annotationOf
    pure <| if directiveNames.contains mnemonic
      then .directive mnemonic operands annotations
      else .instruction mnemonic operands annotations
  | k => .error s!"unsupported source line '{k}'"

private def localOf (stx : Syntax) : Except String Local := do
  let name := identText (stx.getArg 2)
  let type := identText (stx.getArg 4)
  let n ← natOf (stx.getArg 7)
  let negative := !(stx.getArg 6).getArgs.isEmpty
  pure { name, type, init := if negative then -(Int.ofNat n) else Int.ofNat n }

/-- Parse a whole `asmSourceTerm` node (with or without the `withStack`/
`withCallFrame` prefix, with or without an `asm_source (...)` argument
group) into a `Source`, resolving declared locals in the same pass. -/
def sourceOf (stx : Syntax) : Except String Source := do
  let locals ← (stx.getArg 0).getArgs.toList.mapM localOf
  let callFrameGroup := stx.getArg 1
  let callFrame ← if callFrameGroup.getArgs.isEmpty then pure []
    else pure ((callFrameGroup.getArg 1).getSepArgs.toList.map identText)
  let lines ← (stx.getArg 5).getArgs.toList.mapM lineOf
  pure (Source.mk locals callFrame lines).resolveLocals

open Lean.Elab Lean.Elab.Term in
/-- Elaborate `asm_source { ... }` (with its optional `withStack`/
`withCallFrame` prefix and `asm_source (...)` argument group) directly to a
`Grass.Assembly.Syntax.Source` value, via `sourceOf` and `ToExpr`. -/
@[term_elab asmSourceTerm] def elabAsmSourceTerm : TermElab := fun stx _expectedType? =>
  match sourceOf stx with
  | .ok source => return Lean.toExpr source
  | .error msg => throwErrorAt stx msg

end Grass.Assembly.Syntax
