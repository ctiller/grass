import Grass.Process.Sequential.Machine

/-!
# Typed effects cost one constructor and no adapter proof

The fixture `agent-bus` disposition `coord1:8` requires:

> add a fixture showing an ordinary typed effect call requires no bespoke
> adapter proof while an ill-typed result continuation is rejected.

Both halves are here. `console` is a boundary whose demand family has two
constructors with *different* result types; `greet` issues both and consumes
their results. Nothing in it mentions an occurrence, a child binding, a pending
multiset, or an adapter — which is the disposition's substance: those are
generated from the decision structure, not authored.

The rejection half is `#guard_msgs` on an elaboration error, because that is the
only way to assert a negative about the type system without asserting it in
prose. A continuation typed against the wrong demand's result does not fail a
proof obligation; it fails to elaborate.
-/

namespace Grass.Process.Tests.SequentialEffects

open Grass.Process
open Grass.Specification

/-! ## A boundary with two effects that answer differently -/

/-- Two effects. `readLine` answers with text; `write` answers with a count. -/
inductive ConsoleDemand
  | readLine
  | write (line : String)
  deriving DecidableEq, Repr

/--
The dependent answer schema.

`readLine` and `write` have different result types, which is what makes the
rejection fixture below a type error rather than a wrong-but-typeable program.
-/
def ConsoleResult : ConsoleDemand → Type
  | .readLine => Option String
  | .write _ => Nat

/-- The boundary. Adding a third effect is one constructor above, nothing here. -/
@[reducible] def console : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := ConsoleDemand
  Result := ConsoleResult
  Observation := String
  requirements := RequirementSet.empty

/-! ## An ordinary program over it

`greet` reads a line, writes a greeting, and finishes. It is written with
`decide` returning `SequentialDecision` values and nothing else.
-/

/-- Where the program is. -/
inductive GreetState
  | start
  | awaitingName
  | wrote (bytes : Nat)
  deriving DecidableEq, Repr

/-- The rank: work remaining. Internal decisions decrease it. -/
def greetRank : GreetState → Nat
  | .start => 2
  | .awaitingName => 1
  | .wrote _ => 0

/--
The decision function, named so the progress obligation can refer to it.

Splitting it out is presentation only; `greet_decide_eq` below is `rfl`.
-/
def greetDecide : GreetState → SequentialDecision console GreetState Nat
| .start => .effect .readLine (fun answer =>
    match answer with
    | some _ => .awaitingName
    | none => .wrote 0)
| .awaitingName => .effect (.write "hello\n") (fun written => .wrote written)
| .wrote bytes => .terminal bytes

/--
The machine.

Note what an author writes: `initial`, `decide`, an invariant with two
preservation facts, and a rank with one decrease fact. No occurrence identity,
no child binding, no pending bag, no adapter proof. That is the claim
`coord1:8` asks this fixture to demonstrate.
-/
def greet : SequentialMachine console where
  State := GreetState
  Request := Unit
  Terminal := Nat
  initial := fun _ => .start
  decide := greetDecide
  invariant := fun _ => True
  initialInvariant := fun _ => trivial
  internalPreserves := by intros; trivial
  effectResumes := by intros; trivial
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rank := greetRank
  internalDecreases := by
    rintro state next observations decision
    cases state <;> simp [greetDecide] at decision

/-! ## What the author gets for free -/

/--
The frontier theorem applies with no further work: from any state, finitely many
internal steps reach an effect or a terminal.

`greet` has no internal decisions at all, so this is immediate — which is itself
the point. The obligation an author discharged was `internalDecreases`, and the
theorem they did not state is this one.
-/
theorem greet_reaches_frontier (state : GreetState) :
    ∃ frontier, greet.InternalSteps state frontier ∧
      (greet.decide frontier).AtFrontier :=
  greet.reachesFrontier state

/-- The first thing it does is ask the environment, not compute. -/
theorem greet_starts_at_an_effect : (greet.decide .start).AtFrontier := trivial

/-- `greetDecide` really is what the machine decides; the split is presentation. -/
theorem greet_decide_eq : greet.decide = greetDecide := rfl

/-- And it finishes: the terminal decision is a frontier too. -/
theorem greet_can_finish (bytes : Nat) :
    (greet.decide (.wrote bytes)).AtFrontier := trivial

/-! ## The rejection half

A continuation typed against the wrong demand's result is an elaboration error.
`readLine` answers `Option String`; a continuation expecting `Nat` does not
typecheck, and no proof obligation is involved.
-/

/--
error: Type mismatch
  written
has type
  EffectResult ConsoleDemand.readLine
but is expected to have type
  Nat
-/
#guard_msgs in
example : SequentialDecision console GreetState Nat :=
  .effect .readLine (fun written => GreetState.wrote (written : Nat))

end Grass.Process.Tests.SequentialEffects
