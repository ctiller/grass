import Grass.Assembly.Syntax.AST

/-! Decidable well-formedness of a parsed `Grass.Assembly.Syntax.Source`.
This checks only what the target-generic AST itself can see: label
uniqueness, that every operand this front end can recognize as a
control-transfer target names a declared label, that every frame-local
operand names a declared `withStack` local, and that every `@placement`
binding names something a placement can legally bind. It does not know
mnemonic semantics (which mnemonics branch, call, or read memory), ISA
register validity beyond the grammar's own register-name table, or anything
about a concrete lowering; those belong to a later module. -/
namespace Grass.Assembly.Syntax

/-- The names of every label declared in `source`, in source order
(duplicates included, so uniqueness can be checked against this list). -/
def Source.labelNames (source : Source) : List String :=
  source.lines.filterMap fun
    | .label name _ => some name
    | .instruction .. | .directive .. => none

/-- The names of every `withStack`-declared frame local. -/
def Source.localNames (source : Source) : List String :=
  source.locals.map Local.name

/-- The local name an operand refers to, if it is a frame-local operand
(`local` by value or `localAddress` by address). -/
def Operand.localRefs : Operand → List String
  | .local name | .localAddress name => [name]
  | .reg _ | .imm _ | .symbol _ | .sizeOf _ | .mem .. => []

def Annotation.localRefs : Annotation → List String
  | .placement bindings => bindings.flatMap fun (_, value) => value.localRefs
  | .invariant .. | .terminal _ | .audit _ | .violationEdge _ | .containmentTail _ => []

def Line.annotations : Line → List Annotation
  | .label _ annotations | .instruction _ _ annotations | .directive _ _ annotations => annotations

def Line.operands : Line → List Operand
  | .label _ _ => []
  | .instruction _ operands _ | .directive _ operands _ => operands

/-- Every frame-local name an operand or an annotation of `line` refers to. -/
def Line.localRefs (line : Line) : List String :=
  (line.operands.flatMap Operand.localRefs) ++ (line.annotations.flatMap Annotation.localRefs)

/-- Every frame-local name referenced anywhere in `source`. -/
def Source.localRefs (source : Source) : List String :=
  source.lines.flatMap Line.localRefs

/-- The label name a line's single symbolic operand names, when that is the
line's entire operand list. This is the only shape a mnemonic-agnostic front
end can recognize as a control-transfer target without knowing which
mnemonics branch: `jz exit`, `jmp loop_head`, and similar single-bare-symbol
instructions all take this shape, while a `call qword ptr [rip + name]`
(a memory operand, not a bare symbol) is deliberately not one, since that
name is an imported symbol, not a label. -/
def Line.branchTarget : Line → Option String
  | .instruction _ [.symbol name] _ => some name
  | .instruction _ _ _ | .directive .. | .label .. => none

/-- Every branch/call target this front end can recognize, across `source`. -/
def Source.branchTargets (source : Source) : List String :=
  source.lines.filterMap Line.branchTarget

/-- Whether `operand` is something an `@placement` binding may legally name:
a register, or a frame local (by value or by address) declared in
`locals`. -/
def ValidPlacementOperand (locals : List String) : Operand → Prop
  | .reg _ => True
  | .local name | .localAddress name => name ∈ locals
  | .imm _ | .symbol _ | .sizeOf _ | .mem .. => False

instance (locals : List String) (operand : Operand) :
    Decidable (ValidPlacementOperand locals operand) := by
  cases operand <;> unfold ValidPlacementOperand <;> infer_instance

/-- The `@placement` bindings an annotation carries, empty for every other
annotation kind. -/
def Annotation.placementBindings : Annotation → List (String × Operand)
  | .placement bindings => bindings
  | .invariant .. | .terminal _ | .audit _ | .violationEdge _ | .containmentTail _ => []

/-- Whether every `@placement` binding on `line` names a register or a
declared local. -/
def LinePlacementsValid (locals : List String) (line : Line) : Prop :=
  ∀ annotation ∈ line.annotations, ∀ binding ∈ annotation.placementBindings,
    ValidPlacementOperand locals binding.2

instance (locals : List String) (line : Line) :
    Decidable (LinePlacementsValid locals line) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/-- Well-formedness of a parsed authored source: distinct labels, every
recognized branch/call target resolves to a declared label, every
frame-local operand names a declared local, and every `@placement` binding
names a register or a declared local. -/
def WellFormed (source : Source) : Prop :=
  source.labelNames.Nodup ∧
    (∀ target ∈ source.branchTargets, target ∈ source.labelNames) ∧
    (∀ name ∈ source.localRefs, name ∈ source.localNames) ∧
    (∀ line ∈ source.lines, LinePlacementsValid source.localNames line)

instance (source : Source) : Decidable (WellFormed source) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Check `source` for well-formedness, reporting the first violation found
(in the order `WellFormed` states them) as a human-readable message. -/
def check (source : Source) : Except String Unit := do
  let labels := source.labelNames
  match labels.filter (fun name => labels.count name ≥ 2) with
  | duplicate :: _ => throw s!"duplicate label '{duplicate}'"
  | [] => pure ()
  match source.branchTargets.find? (fun target => !labels.contains target) with
  | some target => throw s!"branch/call target '{target}' does not name a declared label"
  | none => pure ()
  let locals := source.localNames
  match source.localRefs.find? (fun name => !locals.contains name) with
  | some name => throw s!"'{name}' is used as a frame local but is not declared by 'withStack'"
  | none => pure ()
  match source.lines.find? (fun line => !decide (LinePlacementsValid locals line)) with
  | some _ =>
      throw "an '@placement' binding does not name a register or a declared local"
  | none => pure ()

end Grass.Assembly.Syntax
