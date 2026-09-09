import Grass.Assembly.X86Source
import Grass.Std.Logical.FiniteMap

/-!
# Control-flow positions derived from symbolic assembly

These positions count source instructions, not encoded bytes. Calls retain a
potential return continuation; this module does not prove that a provider returns.
`check?_valid` and `check?_derived` expose the structural checks and the exact
source-derived code, labels, and flows. No block contracts or machine semantics
are supplied by this check.
-/

namespace Grass.Assembly.X86ControlFlow

open X86Source Grass.Std.Logical

structure CodeItem where
  lineNumber : Nat
  text : String
  instruction : Instruction
  annotations : List Annotation
deriving Repr, DecidableEq

structure Collected where
  code : List CodeItem
  labels : List (String × Nat)
deriving Repr, DecidableEq

def collectFrom : List LocatedStatement → Nat → Collected
  | [], _ => ⟨[], []⟩
  | source :: rest, position =>
    match source.statement with
    | .label name _ =>
      let tail := collectFrom rest position
      { tail with labels := (name, position) :: tail.labels }
    | .instruction instruction annotations =>
      let tail := collectFrom rest (position + 1)
      { tail with code := ⟨source.lineNumber, source.text, instruction, annotations⟩ :: tail.code }

def collect (source : List LocatedStatement) : Collected := collectFrom source 0

inductive Condition where
  | equal
  | above
deriving Repr, DecidableEq

inductive Flow where
  | next (continuation : Nat)
  | jump (target : Nat)
  | conditional (condition : Condition) (taken continuation : Nat)
  | externalCall (symbol : String) (continuation : Nat)
  | trap
deriving Repr, DecidableEq

def Flow.targets : Flow → List Nat
  | .next n | .jump n | .externalCall _ n => [n]
  | .conditional _ taken continuation => [taken, continuation]
  | .trap => []

def Flow.Valid (size : Nat) (flow : Flow) : Prop :=
  ∀ target ∈ flow.targets, target < size

instance (size : Nat) (flow : Flow) : Decidable (flow.Valid size) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

def classify? (labels : List (String × Nat)) (position : Nat)
    (instruction : Instruction) : Option Flow :=
  match instruction.mnemonic, instruction.operands with
  | .jmp, [.symbol name] => (findValue labels name).map Flow.jump
  | .jz, [.symbol name] | .je, [.symbol name] =>
    (findValue labels name).map fun target => .conditional .equal target (position + 1)
  | .ja, [.symbol name] =>
    (findValue labels name).map fun target => .conditional .above target (position + 1)
  | .call, [.ripMemory symbol] => some (.externalCall symbol (position + 1))
  | .ud2, [] => some .trap
  | .push, _ | .mov, _ | .test, _ | .cmp, _ | .lea, _ | .add, _ | .sub, _ |
      .xor, _ | .arg, _ => some (.next (position + 1))
  | .jmp, _ | .jz, _ | .je, _ | .ja, _ | .call, _ | .ud2, _ => none

def deriveFlowsFrom? (labels : List (String × Nat)) : List CodeItem → Nat → Option (List Flow)
  | [], _ => some []
  | item :: rest, position => do
    let flow ← classify? labels position item.instruction
    let tail ← deriveFlowsFrom? labels rest (position + 1)
    pure (flow :: tail)

def FlowsMatch (labels : List (String × Nat)) : List CodeItem → List Flow → Nat → Prop
  | [], [], _ => True
  | item :: code, flow :: flows, position =>
    classify? labels position item.instruction = some flow ∧
      FlowsMatch labels code flows (position + 1)
  | _, _, _ => False

theorem deriveFlowsFrom?_matches (labels : List (String × Nat)) (code : List CodeItem)
    (position : Nat) (flows : List Flow)
    (h : deriveFlowsFrom? labels code position = some flows) :
    FlowsMatch labels code flows position := by
  induction code generalizing position flows with
  | nil => simp [deriveFlowsFrom?] at h; cases h; trivial
  | cons item rest ih =>
    cases hc : classify? labels position item.instruction with
    | none => simp [deriveFlowsFrom?, hc] at h
    | some flow =>
      cases ht : deriveFlowsFrom? labels rest (position + 1) with
      | none => simp [deriveFlowsFrom?, hc, ht] at h
      | some tail =>
        simp [deriveFlowsFrom?, hc, ht] at h
        cases h
        exact ⟨hc, ih (position + 1) tail ht⟩

def Valid (collected : Collected) (flows : List Flow) : Prop :=
  collected.code ≠ [] ∧ (collected.labels.map Prod.fst).Nodup ∧
    (∀ label ∈ collected.labels, label.2 < collected.code.length) ∧
    flows.length = collected.code.length ∧ (∀ flow ∈ flows, flow.Valid collected.code.length) ∧
    ∀ item ∈ collected.code, WellShaped item.instruction.mnemonic item.instruction.operands = true

instance (collected : Collected) (flows : List Flow) : Decidable (Valid collected flows) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure CheckedProgram where
  private mk ::
  source : List LocatedStatement
  collected : Collected
  flows : List Flow
  sourceExact : collected = collect source
  flowsExact : deriveFlowsFrom? collected.labels collected.code 0 = some flows
  valid : Valid collected flows

def check? (source : List LocatedStatement) : Option CheckedProgram := do
  let collected := collect source
  match hf : deriveFlowsFrom? collected.labels collected.code 0 with
  | none => none
  | some flows =>
    if hv : Valid collected flows then some ⟨source, collected, flows, rfl, hf, hv⟩
    else none

theorem check?_valid {source : List LocatedStatement} {program : CheckedProgram}
    (_h : check? source = some program) : Valid program.collected program.flows := program.valid

theorem check?_derived {source : List LocatedStatement} {program : CheckedProgram}
    (h : check? source = some program) :
    program.source = source ∧ program.collected = collect source ∧
      deriveFlowsFrom? program.collected.labels program.collected.code 0 = some program.flows := by
  dsimp only [check?] at h
  split at h
  · simp at h
  · split at h
    · cases h
      exact ⟨rfl, rfl, by assumption⟩
    · simp at h
theorem CheckedProgram.target_bounded (program : CheckedProgram)
    (flow : Flow) (member : flow ∈ program.flows) (target : Nat)
    (edge : target ∈ flow.targets) : target < program.collected.code.length :=
  program.valid.2.2.2.2.1 flow member target edge

theorem CheckedProgram.flows_match (program : CheckedProgram) :
    FlowsMatch program.collected.labels program.collected.code program.flows 0 :=
  deriveFlowsFrom?_matches _ _ _ _ program.flowsExact

end Grass.Assembly.X86ControlFlow
