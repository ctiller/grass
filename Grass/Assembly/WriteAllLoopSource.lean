import Grass.Assembly.SourceResolve

/-! Checked selection of the authored write-all head and update back edge.
Indices come from parsed labels and resolved source origins, including the
existing prologue/initializer translation. This supplies no execution witness.
-/

namespace Grass.Assembly.WriteAllLoopSource

open Grass.ISA.X86 Grass.Std.Logical X86Source

variable {frame : SourceFrame.Result} {rootOffset : Nat}

def originInstruction {splice : SourceSplice.Result frame rootOffset}
    {symbols : SourceResolve.Symbols} {codeBase : Nat}
    (output : SourceResolve.Output splice symbols codeBase) : Option Instruction :=
  output.origin.source?.map (fun original => original.origin.instruction)

def headInstruction : Instruction :=
  ⟨.test, [.register ⟨.r14, .w32⟩, .register ⟨.r14, .w32⟩]⟩

def addInstruction : Instruction :=
  ⟨.add, [.register ⟨.r13, .w64⟩, .register ⟨.rax, .w64⟩]⟩

def subInstruction : Instruction :=
  ⟨.sub, [.register ⟨.r14, .w32⟩, .register ⟨.rax, .w32⟩]⟩

def jumpInstruction : Instruction := ⟨.jmp, [.symbol "write_head"]⟩

def headAnnotations : List Annotation :=
  [⟨.placement, ["handle", "r12", "cursor", "r13", "remaining", "r14d"]⟩,
   ⟨.invariant, ["write_all_loop", "payload"]⟩]

structure OutputAt (source : SourceResolve.Result frame rootOffset) (index : Nat) where
  output : SourceResolve.Output source.splice source.symbols source.codeBase
  found : source.outputs[index]? = some output

def outputAt? (source : SourceResolve.Result frame rootOffset) (index : Nat) :
    Option (OutputAt source index) :=
  match found : source.outputs[index]? with
  | none => none
  | some output => some ⟨output, found⟩

def branchTarget {splice : SourceSplice.Result frame rootOffset}
    {symbols : SourceResolve.Symbols} {codeBase : Nat}
    (output : SourceResolve.Output splice symbols codeBase) : Option Nat :=
  match output.detail with
  | .branch .jump target _ => some target
  | _ => none

structure Candidate (source : SourceResolve.Result frame rootOffset) where
  headSourceIndex : Nat
  headIndex : Nat
  addIndex : Nat
  head : OutputAt source headIndex
  add : OutputAt source addIndex
  subtract : OutputAt source (addIndex + 1)
  jump : OutputAt source (addIndex + 2)

def Candidate.Valid {source : SourceResolve.Result frame rootOffset} (candidate : Candidate source) : Prop :=
  findValue frame.program.collected.labels "write_head" = some candidate.headSourceIndex ∧
  candidate.headIndex = SourceSplice.sourceFinalIndex frame.saved.savedItems.length
    source.splice.initialization.entries.length candidate.headSourceIndex ∧
  frame.statements.any (fun statement => statement.statement == .label "write_head" headAnnotations) = true ∧
  originInstruction candidate.head.output = some headInstruction ∧
  originInstruction candidate.add.output = some addInstruction ∧
  originInstruction candidate.subtract.output = some subInstruction ∧
  originInstruction candidate.jump.output = some jumpInstruction ∧
  branchTarget candidate.jump.output = some candidate.headIndex ∧
  candidate.head.output.index = candidate.headIndex ∧
  candidate.add.output.index = candidate.addIndex ∧
  candidate.subtract.output.index = candidate.addIndex + 1 ∧
  candidate.jump.output.index = candidate.addIndex + 2

instance {source : SourceResolve.Result frame rootOffset} (candidate : Candidate source) :
    Decidable candidate.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure Selection (source : SourceResolve.Result frame rootOffset) where
  private mk ::
  candidate : Candidate source
  valid : candidate.Valid

/-- Refuse missing/changed annotations, wrong origins, or ambiguous back edges. -/
def select? (source : SourceResolve.Result frame rootOffset) : Option (Selection source) := do
  let headSourceIndex ← findValue frame.program.collected.labels "write_head"
  let headIndex := SourceSplice.sourceFinalIndex frame.saved.savedItems.length
    source.splice.initialization.entries.length headSourceIndex
  let jumps := (List.range source.outputs.length).filter fun index =>
    ((source.outputs[index]?).bind originInstruction) == some jumpInstruction
  let [jumpIndex] := jumps | none
  if jumpIndex < 2 then none else do
    let addIndex := jumpIndex - 2
    let head ← outputAt? source headIndex
    let add ← outputAt? source addIndex
    let subtract ← outputAt? source (addIndex + 1)
    let jump ← outputAt? source (addIndex + 2)
    let candidate : Candidate source := ⟨headSourceIndex, headIndex, addIndex, head, add, subtract, jump⟩
    if valid : candidate.Valid then some ⟨candidate, valid⟩ else none

end Grass.Assembly.WriteAllLoopSource
