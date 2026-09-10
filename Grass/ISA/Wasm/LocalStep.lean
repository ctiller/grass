import Grass.ISA.Wasm.Invocation

/-! Executable operand-local steps for the integer/local Wasm family.
Refusal is an adapter/validation failure; `trap` is an architectural outcome.
These steps neither access linear memory nor invoke a provider. Direct calls
use HostInvocation; return/control-stack execution remains outside this leaf. -/
namespace Grass.ISA.Wasm

inductive LocalError where
  | stackUnderflow | typeMismatch | missingLocal | needsControl
deriving DecidableEq, Repr

inductive LocalOutcome where
  | next (after : State)
  | trap
deriving DecidableEq, Repr

def State.advance (before : State) (stack : List Value) : State :=
  { before with pc := before.pc + 1, stack := stack }

/-- Top-of-stack is the second arithmetic operand. BitVec arithmetic wraps. -/
def localStep (instruction : Instruction) (before : State) : Except LocalError LocalOutcome :=
  match instruction with
  | .unreachable => .ok .trap
  | .nop => .ok (.next (before.advance before.stack))
  | .i32Const v => .ok (.next (before.advance (.i32 v :: before.stack)))
  | .i64Const v => .ok (.next (before.advance (.i64 v :: before.stack)))
  | .drop => match before.stack with
    | [] => .error .stackUnderflow
    | _ :: rest => .ok (.next (before.advance rest))
  | .localGet index => match before.locals[index]? with
    | none => .error .missingLocal
    | some value => .ok (.next (before.advance (value :: before.stack)))
  | .localSet index => match before.locals[index]?, before.stack with
    | none, _ => .error .missingLocal
    | _, [] => .error .stackUnderflow
    | some old, value :: rest =>
      if old.type = value.type then
        .ok (.next { before.advance rest with locals := before.locals.set index value })
      else .error .typeMismatch
  | .i32Eqz => match before.stack with
    | [] => .error .stackUnderflow
    | .i32 v :: rest =>
      .ok (.next (before.advance (.i32 (if v = 0 then 1 else 0) :: rest)))
    | _ => .error .typeMismatch
  | .i32Add | .i32Sub => match before.stack with
    | [] | [_] => .error .stackUnderflow
    | .i32 rhs :: .i32 lhs :: rest =>
      let value := if instruction = .i32Add then lhs + rhs else lhs - rhs
      .ok (.next (before.advance (.i32 value :: rest)))
    | _ => .error .typeMismatch
  | .call _ | .return_ => .error .needsControl

/-- Checked execution of the actual source occurrence. The output is computed,
not selected by the caller; the endpoint is retained on the receipt. -/
structure LocalRun (store : Store) (before : State) where
  private mk ::
  site : Site store before
  outcome : LocalOutcome
  executed : localStep site.instruction before = .ok outcome

inductive RunError where
  | resolve (error : ResolveError)
  | local (error : LocalError)
deriving DecidableEq, Repr

def LocalRun.check (store : Store) (before : State) : Except RunError (LocalRun store before) := do
  let site ← (Site.check store before).mapError .resolve
  match h : localStep site.instruction before with
  | .error e => throw (.local e)
  | .ok outcome => return ⟨site, outcome, h⟩

/-- Universal arithmetic laws; no native evaluation supplies proof authority. -/
theorem localStep_i32Add (before : State) (lhs rhs : BitVec 32) (rest : List Value) :
    localStep .i32Add { before with stack := .i32 rhs :: .i32 lhs :: rest } =
      .ok (.next (before.advance (.i32 (lhs + rhs) :: rest))) := by
  simp [localStep, State.advance]

theorem localStep_i32Sub (before : State) (lhs rhs : BitVec 32) (rest : List Value) :
    localStep .i32Sub { before with stack := .i32 rhs :: .i32 lhs :: rest } =
      .ok (.next (before.advance (.i32 (lhs - rhs) :: rest))) := by
  simp [localStep, State.advance]

theorem localStep_unreachable (before : State) :
    localStep .unreachable before = .ok .trap := rfl

theorem LocalRun.source_instruction {store : Store} {before : State}
    (run : LocalRun store before) :
    run.site.definition.body[before.pc]? = some run.site.instruction := run.site.instructionLookup

end Grass.ISA.Wasm
