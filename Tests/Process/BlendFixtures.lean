import Grass.Process.Weave.Blend

/-!
# A woven pair, and what overlapping namespaces would cost

`Grass/Process/Weave/Blend.lean` argues that two of `docs/PROCESS.md` §8's six
weave obligations — routing, and whether irrelevant components stutter — are
consequences of the disjointness condition rather than things a weave proves.
This file is that at a concrete pair, plus the counterexample that says why the
condition is a condition.

`logger` and `timer` are two components with nothing in common. `combined` is
the obvious sum vocabulary, and `weave` embeds each side by its injection. The
routing theorems then read off with no routing table anywhere.

`overlapping_names_have_two_routings` is the negative: two components that both
claim one woven demand fail `demandsDisjoint`, and a result for that demand
answers a demand of each. §8 puts disjointness in the *premise* of `weave` for
exactly this reason.
-/

namespace Grass.Process.Tests.Blend

open Grass.Process
open Grass.Specification

/-! ## Two components -/

/-- What the logger asks for. -/
inductive LogDemand
  | write (line : String)
  deriving DecidableEq, Repr

/-- What the timer asks for. -/
inductive TimerDemand
  | sleep (millis : Nat)
  deriving DecidableEq, Repr

/-- The logger's vocabulary. -/
@[reducible] def logger : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := LogDemand
  Result := fun _ => Nat
  Observation := String
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

/-- The timer's. -/
@[reducible] def timer : ProcessVocabulary.{0} where
  ExternalEvent := Bool
  Demand := TimerDemand
  Result := fun _ => Unit
  Observation := Nat
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

/-- The woven demand namespace: each side's, tagged. -/
abbrev BothDemands : Type := LogDemand ⊕ TimerDemand

/-- And its dependent result schema, which dispatches on the tag. -/
def bothResults : BothDemands → Type
  | .inl _ => Nat
  | .inr _ => Unit

/-- The woven vocabulary. -/
@[reducible] def combined : ProcessVocabulary.{0} where
  ExternalEvent := Unit ⊕ Bool
  Demand := BothDemands
  Result := bothResults
  Observation := String ⊕ Nat
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

/-! ## The weave -/

/-- The logger's names inside the woven vocabulary. -/
def loggerIn : VocabularyEmbedding logger combined where
  externalEvent := .inl
  demand := .inl
  demandInjective := by
    rintro left right same
    injection same
  externalEventInjective := by
    rintro left right same
    injection same
  result := fun _ answer => answer
  observation := .inl
  observationInjective := by
    rintro left right same
    injection same
  interruptReason := fun reason => reason.elim
  logicalFault := fun fault => fault.elim
  environmentViolation := fun violation => violation.elim

/-- The timer's. -/
def timerIn : VocabularyEmbedding timer combined where
  externalEvent := .inr
  demand := .inr
  demandInjective := by
    rintro left right same
    injection same
  externalEventInjective := by
    rintro left right same
    injection same
  result := fun _ answer => answer
  observation := .inr
  observationInjective := by
    rintro left right same
    injection same
  interruptReason := fun reason => reason.elim
  logicalFault := fun fault => fault.elim
  environmentViolation := fun violation => violation.elim

/--
The weave.

All three disjointness fields are the same one-line fact about a sum, which is
the point: §8's condition is cheap to satisfy when the components really are
separate, and impossible when they are not.
-/
def weave : DisjointWeave logger timer combined where
  leftIn := loggerIn
  rightIn := timerIn
  demandsDisjoint := by
    rintro own other same
    have collides : (Sum.inl own : BothDemands) = Sum.inr other := same
    exact absurd collides (by simp)
  observationsDisjoint := by
    rintro own other same
    have collides : (Sum.inl own : String ⊕ Nat) = Sum.inr other := same
    exact absurd collides (by simp)
  externalEventsDisjoint := by
    rintro own other same
    have collides : (Sum.inl own : Unit ⊕ Bool) = Sum.inr other := same
    exact absurd collides (by simp)

/-! ## What it decides -/

/-- A `write` is the logger's demand. -/
theorem the_write_is_the_loggers :
    weave.FromLeft (.inl (.write "hello")) := ⟨.write "hello", rfl⟩

/--
**And its result routes to the logger, from exactly one of its demands, with the
timer stuttering.**

§8's routing bullet read off the disjointness. Nothing here consults a routing
table, because there is none to consult.
-/
theorem the_write_routes_to_the_logger :
    (∃ own : LogDemand, weave.leftIn.demand own = (.inl (.write "hello") : BothDemands) ∧
        ∀ other, weave.leftIn.demand other = (.inl (.write "hello") : BothDemands) →
          other = own) ∧
      ¬ weave.FromRight (.inl (.write "hello")) :=
  weave.routing_is_forced the_write_is_the_loggers

/-- And the timer has no demand that could have been answered instead. -/
theorem the_timer_stutters_on_it :
    ¬ ∃ other : TimerDemand,
      weave.rightIn.demand other = weave.leftIn.demand (.write "hello") :=
  weave.the_other_side_stutters

/-! ## And what overlapping namespaces would cost -/

/-- A component with exactly one demand. -/
inductive AlphaDemand | only
  deriving DecidableEq, Repr

/-- And another. -/
inductive BetaDemand | only
  deriving DecidableEq, Repr

@[reducible] def alpha : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := AlphaDemand
  Result := fun _ => Nat
  Observation := Unit
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

@[reducible] def beta : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := BetaDemand
  Result := fun _ => Nat
  Observation := Unit
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

/-- A woven vocabulary with one demand, which both components will claim. -/
@[reducible] def shared : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Nat
  Observation := Unit
  InterruptReason := Empty
  LogicalFault := Empty
  EnvironmentViolation := Empty

/--
A fully legal embedding of the first component.

Every field of `VocabularyEmbedding` including both injectivity laws — the
demand map is injective because `AlphaDemand` has one constructor. Nothing about
an embedding on its own is wrong here.
-/
def alphaIn : VocabularyEmbedding alpha shared where
  externalEvent := fun _ => ()
  demand := fun _ => ()
  demandInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  externalEventInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  result := fun _ answer => answer
  observation := fun _ => ()
  observationInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  interruptReason := fun reason => reason.elim
  logicalFault := fun fault => fault.elim
  environmentViolation := fun violation => violation.elim

/-- And of the second, into the same woven demand. -/
def betaIn : VocabularyEmbedding beta shared where
  externalEvent := fun _ => ()
  demand := fun _ => ()
  demandInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  externalEventInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  result := fun _ answer => answer
  observation := fun _ => ()
  observationInjective := by rintro ⟨⟩ ⟨⟩ _; rfl
  interruptReason := fun reason => reason.elim
  logicalFault := fun fault => fault.elim
  environmentViolation := fun violation => violation.elim

/-- **They claim the same woven demand.** -/
theorem the_real_overlap : alphaIn.demand .only = betaIn.demand .only := rfl

/--
**So one result answers a demand of each component, and there is no fact about
which.**

The counterexample §8 puts disjointness in the *premise* to exclude, built out
of two legal embeddings rather than out of two arbitrary functions. A first
version of this theorem took two unrelated functions and a hypothesis that was
the negated instance of its own conclusion — a tautology at any three types,
with the interesting content entirely in the docstring. Local adversarial review
gave the identical proof term at `{A B C : Type}`.

`alphaIn.result` and `betaIn.result` both accept the *same* `shared.Result ()`
and hand it to different components. That is what `demandsDisjoint` exists to
forbid.
-/
theorem one_result_answers_both (answer : shared.Result (alphaIn.demand .only)) :
    alphaIn.result .only answer = answer ∧ betaIn.result .only answer = answer :=
  ⟨rfl, rfl⟩

/-- **And no `DisjointWeave` can hold them**, which is the exclusion. -/
theorem the_overlap_is_not_a_weave (weave : DisjointWeave alpha beta shared)
    (isAlpha : weave.leftIn = alphaIn) (isBeta : weave.rightIn = betaIn) : False := by
  refine weave.demandsDisjoint .only .only ?_
  rw [isAlpha, isBeta]

end Grass.Process.Tests.Blend
