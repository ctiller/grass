import Grass.Target.Safety

/-!
# Adequacy from checkpoints

`Grass.Target.Machine.adequate_of_invariant` asks for one inductive invariant
that excludes stuck states. A block-structured assembly verifier does not
produce one: it produces a *set of checkpoints* — label entries carrying their
block contracts — and, for each checkpoint, a proof that every execution path
leaving it reaches another checkpoint (or halts) within a bounded number of
steps without ever getting stuck. This module turns that data into the
invariant, once, for every ISA and platform.

The construction is stated purely over `State`, `Step`, `system` and `Stuck`.
No program counter is visible at this seam: the ISA `State` is opaque, so a
checkpoint is just a predicate on machine states and the "bounded number of
steps" is a plain `Nat` fuel, not a distance in a control-flow graph.

`Safe Check n s` is the local obligation: from `s`, every path reaches a
`Check` state or a halted state within `n` steps and no state on the way is
stuck. Two facts make it non-vacuous:

- the `step` constructor demands a *witness* successor, so a state with no
  transition and no halt (a fault, an undecodable call, an unanswerable
  request) is never `Safe` at any fuel;
- the continuation is universally quantified over *every* successor. For an
  awaiting state the successors range over every response `Platform.Responds`
  allows, so a program that ignores a partial write or a failure code cannot
  be proved `Safe`.

`Safe` is defined mutually with `Resume`, which is literally
`Check s ∨ Safe Check n s`; the disjunction cannot be written inline because a
recursive occurrence under `Or` is a nested inductive the kernel rejects.
`Resume.elim` and `Resume.intro` convert, and every lemma below is stated in
the `∨` form.

The introduction lemmas at the end are the ones a per-program proof chains:
one per ISA step outcome, each discharging the "no other transition is
possible" side condition through the inversion lemmas `Step.inv_running` and
`Step.inv_awaiting`.

## What these definitions still allow

Three questions a reviewer should ask of `Safe` and `Checkpoints`, each
answered here by a theorem rather than by an argument.

- *Can a loop avoid the checkpoints?* No. `Safe.checkpoint_of_path`: along any
  infinite path out of a `Safe`-at-`n` state, some state within the first `n`
  steps satisfies `Check`. A non-halting program with no checkpoint on its
  cycle is not `Safe` at any fuel. What is still allowed, and intended, is a
  program that never terminates: adequacy does not require halting, only that
  checkpoints recur at least every `bound` steps.
- *Can an awaiting state with no allowed response be `Safe`?* No.
  `Safe.responds_of_awaiting`: an awaiting `Safe` state has at least one
  allowed response. More generally `Safe.not_stuck` rules out all three ways
  of getting stuck (`stuck_of_fault`, `stuck_of_undecoded`,
  `stuck_of_unanswered`), because the `step` constructor demands a witness
  transition. The corresponding trap in the *other* direction is closed by the
  universal quantifier in `continues`: `Safe.ofAwaiting` obliges the program
  for every response `Responds` allows, not only the witness one.
- *Can `bound := 0` prove anything?* Only vacuously.
  `Safe.halted_of_zero`: `Safe` at fuel `0` is `phase = .halted`, so a
  `Checkpoints` with `bound := 0` claims every checkpoint state is halted;
  with `initial` forcing every initial state to be a checkpoint, and an
  initial state always `running`, this is provable only when
  `(system platform raw).Initial` is uninhabited — that is, when
  `platform.Admits` holds of no environment. `adequate_of_checkpoints`'s
  `covers` premise then forces `spec.admits` to be empty too, so the vacuity
  is visible in the specification, not hidden in the machine tier.

What remains genuinely unconstrained, by design: `Check` is an arbitrary
`Prop` on states, so nothing here says a checkpoint set is finite,
enumerable, or tied to code addresses. The seam cannot say otherwise — the ISA
`State` is opaque and no program counter is visible — and a per-program proof
is free to use a coarse `Check`. A `Check` that is too coarse costs nothing in
soundness; it just makes `progress` unprovable.
-/

namespace Grass.Target.Machine

open Grass.Service

variable {isa : ISA} {D : Domain}

/-! ## Step inversion

The generic machine is deterministic in its *shape*: the phase of a state and,
for a running state, the ISA's step outcome determine which `Step` constructor
can fire. These two lemmas say so once. They are what every per-program proof
uses to discharge the universally quantified successor obligation.
-/

/-- Nothing steps out of a halted state. -/
theorem not_step_of_halted {platform : Platform isa D} {s : State isa D platform}
    {choice : Choice D} {event : Event D} {next : State isa D platform}
    (isHalted : s.phase = .halted) : ¬ Step platform s choice event next := by
  intro step
  cases step <;> simp at isHalted

/-- Every transition out of a running state is the one its ISA step outcome
selects, with the choice, event and successor that constructor fixes. -/
theorem Step.inv_running {platform : Platform isa D} {state : isa.State}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform}
    (step : Step platform ⟨env0, env, .running state⟩ choice event next) :
    (∃ after, isa.step state = .internal after ∧
        choice = .machine ∧ event = .silent ∧ next = ⟨env0, env, .running after⟩) ∨
    (isa.step state = .halted ∧
        choice = .machine ∧ event = .silent ∧ next = ⟨env0, env, .halted⟩) ∨
    (∃ call resume request, isa.step state = .external call resume ∧
        platform.decode call = some request ∧ ¬ D.Terminal request ∧
        choice = .machine ∧ event = .call request ∧
        next = ⟨env0, env, .awaiting call request resume⟩) ∨
    (∃ call resume request, isa.step state = .external call resume ∧
        platform.decode call = some request ∧ D.Terminal request ∧
        choice = .machine ∧ event = .call request ∧ next = ⟨env0, env, .halted⟩) := by
  cases step with
  | internal stepEq => exact Or.inl ⟨_, stepEq, rfl, rfl, rfl⟩
  | halt stepEq => exact Or.inr (Or.inl ⟨stepEq, rfl, rfl, rfl⟩)
  | call stepEq decoded continues =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, stepEq, decoded, continues, rfl, rfl, rfl⟩))
  | exit stepEq decoded ends =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, stepEq, decoded, ends, rfl, rfl, rfl⟩))

/-- Every transition out of an awaiting state is the environment answering the
pending request with some response `Responds` allows. -/
theorem Step.inv_awaiting {platform : Platform isa D} {call : isa.NativeCall}
    {request : D.Request} {resume : isa.NativeReturn → isa.State}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform}
    (step : Step platform ⟨env0, env, .awaiting call request resume⟩ choice event next) :
    ∃ (response : D.Response request) (env' : platform.Environment),
      platform.Responds env request response env' ∧
      choice = .respond request response ∧ event = .reply request response ∧
      next = ⟨env0, env', .running (resume (platform.encodeReturn call request response))⟩ := by
  cases step with
  | reply allowed => exact ⟨_, _, allowed, rfl, rfl, rfl⟩

/-- The successor of a running state whose ISA step is internal. -/
theorem Step.next_of_internal {platform : Platform isa D} {state after : isa.State}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform} (stepEq : isa.step state = .internal after)
    (step : Step platform ⟨env0, env, .running state⟩ choice event next) :
    next = ⟨env0, env, .running after⟩ := by
  rcases step.inv_running with ⟨_, stepEq', _, _, nextEq⟩ | ⟨stepEq', _⟩ |
      ⟨_, _, _, stepEq', _⟩ | ⟨_, _, _, stepEq', _⟩
  · cases stepEq'.symm.trans stepEq
    exact nextEq
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq

/-- The successor of a running state whose ISA step halts. -/
theorem Step.next_of_halt {platform : Platform isa D} {state : isa.State}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform} (stepEq : isa.step state = .halted)
    (step : Step platform ⟨env0, env, .running state⟩ choice event next) :
    next = ⟨env0, env, .halted⟩ := by
  rcases step.inv_running with ⟨_, stepEq', _⟩ | ⟨_, _, _, nextEq⟩ |
      ⟨_, _, _, stepEq', _⟩ | ⟨_, _, _, stepEq', _⟩
  · cases stepEq'.symm.trans stepEq
  · exact nextEq
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq

/-- The successor of a running state whose ISA step is a native call the
platform realizes as a non-terminal request. -/
theorem Step.next_of_call {platform : Platform isa D} {state : isa.State}
    {call : isa.NativeCall} {resume : isa.NativeReturn → isa.State} {request : D.Request}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform}
    (stepEq : isa.step state = .external call resume)
    (decoded : platform.decode call = some request)
    (continues : ¬ D.Terminal request)
    (step : Step platform ⟨env0, env, .running state⟩ choice event next) :
    next = ⟨env0, env, .awaiting call request resume⟩ := by
  rcases step.inv_running with ⟨_, stepEq', _⟩ | ⟨stepEq', _⟩ |
      ⟨_, _, _, stepEq', decoded', _, _, _, nextEq⟩ |
      ⟨_, _, _, stepEq', decoded', ends, _⟩
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq
    cases decoded'.symm.trans decoded
    exact nextEq
  · cases stepEq'.symm.trans stepEq
    cases decoded'.symm.trans decoded
    exact absurd ends continues

/-- The successor of a running state whose ISA step is a native call the
platform realizes as a terminal request: the machine halts and no response is
ever delivered. -/
theorem Step.next_of_exit {platform : Platform isa D} {state : isa.State}
    {call : isa.NativeCall} {resume : isa.NativeReturn → isa.State} {request : D.Request}
    {env0 env : platform.Environment} {choice : Choice D} {event : Event D}
    {next : State isa D platform}
    (stepEq : isa.step state = .external call resume)
    (decoded : platform.decode call = some request)
    (ends : D.Terminal request)
    (step : Step platform ⟨env0, env, .running state⟩ choice event next) :
    next = ⟨env0, env, .halted⟩ := by
  rcases step.inv_running with ⟨_, stepEq', _⟩ | ⟨stepEq', _⟩ |
      ⟨_, _, _, stepEq', decoded', continues, _⟩ |
      ⟨_, _, _, stepEq', decoded', _, _, _, nextEq⟩
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq
  · cases stepEq'.symm.trans stepEq
    cases decoded'.symm.trans decoded
    exact absurd ends continues
  · cases stepEq'.symm.trans stepEq
    cases decoded'.symm.trans decoded
    exact nextEq

/-! ## Bounded safety between checkpoints -/

mutual

/-- `Safe platform Check n s`: from `s`, every execution path reaches a state
satisfying `Check` or a halted state within `n` steps, and no state along the
way is stuck.

`halted` is the terminal base case. `step` requires a witness transition — so a
stuck state is never `Safe` — and constrains *every* transition, which for an
awaiting state means every response the platform's `Responds` allows. The fuel
strictly decreases on the `step` constructor, so a path that never reaches a
`Check` state and never halts cannot be `Safe` at any fuel. -/
inductive Safe (platform : Platform isa D) (Check : State isa D platform → Prop) :
    Nat → State isa D platform → Prop
  | halted {n : Nat} {s : State isa D platform} (isHalted : s.phase = .halted) :
      Safe platform Check n s
  | step {n : Nat} {s : State isa D platform}
      (progresses : ∃ choice event next, Step platform s choice event next)
      (continues : ∀ choice event next, Step platform s choice event next →
        Resume platform Check n next) :
      Safe platform Check (n + 1) s

/-- `Check s ∨ Safe platform Check n s`, spelled as an inductive because a
recursive occurrence of `Safe` underneath `Or` would be a nested inductive the
kernel rejects. `Resume.elim` and `Resume.intro` are the isomorphism. -/
inductive Resume (platform : Platform isa D) (Check : State isa D platform → Prop) :
    Nat → State isa D platform → Prop
  | checkpoint {n : Nat} {s : State isa D platform} (check : Check s) :
      Resume platform Check n s
  | later {n : Nat} {s : State isa D platform} (safe : Safe platform Check n s) :
      Resume platform Check n s

end

/-- `Resume` is the disjunction it is named after. -/
theorem Resume.elim {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform} (resume : Resume platform Check n s) :
    Check s ∨ Safe platform Check n s := by
  cases resume with
  | checkpoint check => exact Or.inl check
  | later safe => exact Or.inr safe

/-- `Resume` is the disjunction it is named after. -/
theorem Resume.intro {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform} (either : Check s ∨ Safe platform Check n s) :
    Resume platform Check n s :=
  either.elim .checkpoint .later

/-- The `step` constructor in its `∨` form: a witness successor plus, for every
successor, a checkpoint or one less fuel of safety. -/
theorem Safe.stepOr {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform}
    (progresses : ∃ choice event next, Step platform s choice event next)
    (continues : ∀ choice event next, Step platform s choice event next →
      Check next ∨ Safe platform Check n next) :
    Safe platform Check (n + 1) s :=
  .step progresses fun choice event next step => .intro (continues choice event next step)

/-- A `Safe` state is halted or has a successor: it is not stuck. -/
theorem Safe.haltedOrStep {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform} (safe : Safe platform Check n s) :
    s.phase = .halted ∨ ∃ choice event next, Step platform s choice event next := by
  cases safe with
  | halted isHalted => exact Or.inl isHalted
  | step progresses _ => exact Or.inr progresses

/-- A `Safe` state is never `Stuck`. -/
theorem Safe.not_stuck {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform} (safe : Safe platform Check n s) :
    ¬ Stuck platform s := by
  intro stuck
  rcases safe.haltedOrStep with isHalted | ⟨_, _, _, step⟩
  · exact stuck.1 isHalted
  · exact stuck.2 _ _ _ step

/-- Every successor of a `Safe` state is a checkpoint or itself `Safe`. -/
theorem Safe.preserved {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {s : State isa D platform} {choice : Choice D} {event : Event D}
    {next : State isa D platform} (safe : Safe platform Check n s)
    (step : Step platform s choice event next) :
    Check next ∨ ∃ m, Safe platform Check m next := by
  cases safe with
  | halted isHalted => exact absurd step (not_step_of_halted isHalted)
  | step _ continues =>
      rcases (continues _ _ _ step).elim with check | safe'
      · exact Or.inl check
      · exact Or.inr ⟨_, safe'⟩

/-- Zero fuel is not free: `Safe` at fuel `0` says the state is already halted.
A `Checkpoints` with `bound := 0` therefore claims every checkpoint is halted,
and since `initial` makes every initial state a checkpoint, it is provable only
when the platform admits no environment the program starts running in. -/
theorem Safe.halted_of_zero {platform : Platform isa D} {Check : State isa D platform → Prop}
    {s : State isa D platform} (safe : Safe platform Check 0 s) : s.phase = .halted := by
  cases safe with
  | halted isHalted => exact isHalted

/-- An awaiting state is `Safe` only if the environment is allowed at least one
response. A request the platform never answers leaves the machine stuck, and a
stuck state is `Safe` at no fuel. -/
theorem Safe.responds_of_awaiting {platform : Platform isa D}
    {Check : State isa D platform → Prop} {n : Nat} {call : isa.NativeCall}
    {request : D.Request} {resume : isa.NativeReturn → isa.State}
    {env0 env : platform.Environment}
    (safe : Safe platform Check n ⟨env0, env, .awaiting call request resume⟩) :
    ∃ (response : D.Response request) (env' : platform.Environment),
      platform.Responds env request response env' := by
  rcases safe.haltedOrStep with isHalted | ⟨_, _, _, step⟩
  · simp at isHalted
  · obtain ⟨response, env', allowed, _⟩ := step.inv_awaiting
    exact ⟨response, env', allowed⟩

/-- More fuel is weaker. -/
theorem Safe.mono {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n m : Nat} {s : State isa D platform} (le : n ≤ m)
    (safe : Safe platform Check n s) : Safe platform Check m s := by
  induction n generalizing m s with
  | zero =>
      cases safe with
      | halted isHalted => exact .halted isHalted
  | succ n ih =>
      cases safe with
      | halted isHalted => exact .halted isHalted
      | step progresses continues =>
          obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := by
            cases m with
            | zero => omega
            | succ k => exact ⟨k, rfl⟩
          refine .stepOr progresses ?_
          intro choice event next step
          rcases (continues choice event next step).elim with check | safe'
          · exact Or.inl check
          · exact Or.inr (ih (by omega) safe')

/-- No loop escapes the checkpoints. Along any infinite path out of a state
that is `Safe` at fuel `n` — and an infinite path is exactly a run that never
halts — some state within the first `n` steps is a checkpoint. This is the
theorem that stops `Check` from being satisfied only outside the reachable
part of a program: a program that spins forever between two labels must have
declared one of them a checkpoint. -/
theorem Safe.checkpoint_of_path {platform : Platform isa D}
    {Check : State isa D platform → Prop} {n : Nat}
    (path : Nat → State isa D platform) (choices : Nat → Choice D) (events : Nat → Event D)
    (steps : ∀ i, Step platform (path i) (choices i) (events i) (path (i + 1)))
    (safe : Safe platform Check n (path 0)) :
    ∃ i, i ≤ n ∧ Check (path i) := by
  induction n generalizing path choices events with
  | zero => exact absurd (steps 0) (not_step_of_halted safe.halted_of_zero)
  | succ n ih =>
      cases safe with
      | halted isHalted => exact absurd (steps 0) (not_step_of_halted isHalted)
      | step _ continues =>
          rcases (continues (choices 0) (events 0) (path 1) (steps 0)).elim with check | safe'
          · exact ⟨1, by omega, check⟩
          · obtain ⟨i, le, check⟩ :=
              ih (fun i => path (i + 1)) (fun i => choices (i + 1)) (fun i => events (i + 1))
                (fun i => steps (i + 1)) safe'
            exact ⟨i + 1, by omega, check⟩

/-! ## Checkpoints and the invariant they generate -/

variable (platform : Platform isa D) (raw : isa.Raw)

/-- What a block-structured assembly verifier produces: a predicate marking the
checkpoint states (label entries with their block contracts), a uniform step
bound, a proof that every initial state is a checkpoint, and a proof that every
checkpoint is `Safe` for that bound — every path out of it reaches another
checkpoint or halts within `bound` steps without getting stuck. -/
structure Checkpoints where
  /-- The checkpoint states. A per-program proof defines this as a disjunction
  of state shapes, one per label, each carrying its block contract. -/
  Check : State isa D platform → Prop
  /-- The uniform step budget between consecutive checkpoints. -/
  bound : Nat
  /-- Every initial state of the loaded program is a checkpoint. -/
  initial : ∀ state, (system platform raw).Initial state () → Check state
  /-- From a checkpoint, every path reaches a checkpoint or halts within
  `bound` steps and never gets stuck. -/
  progress : ∀ state, Check state → Safe platform Check bound state

variable {platform raw}

/-- A checkpoint is `Safe` for the declared bound. -/
theorem Checkpoints.safe (checkpoints : Checkpoints platform raw)
    {state : State isa D platform} (check : checkpoints.Check state) :
    Safe platform checkpoints.Check checkpoints.bound state :=
  checkpoints.progress state check

/-- The invariant a checkpoint set generates: be a checkpoint, or be somewhere
on a bounded path back to one. Preservation is exactly the `Safe` fuel counting
down and being reset by `progress` at each checkpoint; stuck-freedom is the
witness successor `Safe.step` demands. -/
def Checkpoints.toInvariant (checkpoints : Checkpoints platform raw) :
    Invariant platform raw where
  Inv state := checkpoints.Check state ∨ ∃ n, Safe platform checkpoints.Check n state
  initial state isInitial := Or.inl (checkpoints.initial state isInitial)
  preserved holds step := by
    rcases holds with check | ⟨_, safe⟩
    · exact (checkpoints.safe check).preserved step
    · exact safe.preserved step
  progress state holds := by
    rcases holds with check | ⟨_, safe⟩
    · exact (checkpoints.safe check).haltedOrStep
    · exact safe.haltedOrStep

/-- Adequacy of the generic machine from a checkpoint set and input coverage.
This is `adequate_of_invariant` in the form a block-structured assembly
verifier can actually discharge. -/
theorem adequate_of_checkpoints (checkpoints : Checkpoints platform raw) (spec : SpecRoot)
    (eventOf : Event D → spec.AuditEvent) (inputOf : platform.Environment → spec.Input)
    (covers : ∀ input, spec.admits input →
      ∃ env, platform.Admits env ∧ inputOf env = input) :
    (behavior platform raw spec eventOf inputOf).Adequate :=
  adequate_of_invariant checkpoints.toInvariant spec eventOf inputOf covers

/-! ## Introduction lemmas

One per ISA step outcome, for the deterministic shape of the generic machine.
A per-program proof walks a block by chaining these, and the fuel it consumes
is the block's instruction count. Each lemma discharges the universally
quantified successor obligation through the inversion lemmas above, so the
per-program proof never reasons about `Step` constructors directly.
-/

/-- An internal ISA step. -/
theorem Safe.ofInternal {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {state after : isa.State} {env0 env : platform.Environment}
    (stepEq : isa.step state = .internal after)
    (rest : Check ⟨env0, env, .running after⟩ ∨
      Safe platform Check n ⟨env0, env, .running after⟩) :
    Safe platform Check (n + 1) ⟨env0, env, .running state⟩ := by
  refine .stepOr ⟨_, _, _, Step.internal stepEq⟩ ?_
  intro choice event next step
  rw [Step.next_of_internal stepEq step]
  exact rest

/-- The machine stopping by itself. The successor is halted, so no fuel is
needed beyond this step and any `Check` will do. -/
theorem Safe.ofHalt {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {state : isa.State} {env0 env : platform.Environment}
    (stepEq : isa.step state = .halted) :
    Safe platform Check (n + 1) ⟨env0, env, .running state⟩ := by
  refine .stepOr ⟨_, _, _, Step.halt stepEq⟩ ?_
  intro choice event next step
  rw [Step.next_of_halt stepEq step]
  exact Or.inr (.halted rfl)

/-- A native call the platform realizes as a non-terminal request: the machine
moves to the awaiting state, which must itself be a checkpoint or `Safe`. -/
theorem Safe.ofCall {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {state : isa.State} {call : isa.NativeCall}
    {resume : isa.NativeReturn → isa.State} {request : D.Request}
    {env0 env : platform.Environment}
    (stepEq : isa.step state = .external call resume)
    (decoded : platform.decode call = some request)
    (continues : ¬ D.Terminal request)
    (rest : Check ⟨env0, env, .awaiting call request resume⟩ ∨
      Safe platform Check n ⟨env0, env, .awaiting call request resume⟩) :
    Safe platform Check (n + 1) ⟨env0, env, .running state⟩ := by
  refine .stepOr ⟨_, _, _, Step.call stepEq decoded continues⟩ ?_
  intro choice event next step
  rw [Step.next_of_call stepEq decoded continues step]
  exact rest

/-- A native call the platform realizes as a terminal request: the machine
halts and the response is never delivered. -/
theorem Safe.ofExit {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {state : isa.State} {call : isa.NativeCall}
    {resume : isa.NativeReturn → isa.State} {request : D.Request}
    {env0 env : platform.Environment}
    (stepEq : isa.step state = .external call resume)
    (decoded : platform.decode call = some request)
    (ends : D.Terminal request) :
    Safe platform Check (n + 1) ⟨env0, env, .running state⟩ := by
  refine .stepOr ⟨_, _, _, Step.exit stepEq decoded ends⟩ ?_
  intro choice event next step
  rw [Step.next_of_exit stepEq decoded ends step]
  exact Or.inr (.halted rfl)

/-- An awaiting state. The witness is one response the environment is allowed
to give — without it the state would be stuck — and the obligation ranges over
*every* allowed response, which is what forces a program to handle partial
writes and failures. -/
theorem Safe.ofAwaiting {platform : Platform isa D} {Check : State isa D platform → Prop}
    {n : Nat} {call : isa.NativeCall} {request : D.Request}
    {resume : isa.NativeReturn → isa.State} {env0 env : platform.Environment}
    {witnessResponse : D.Response request} {witnessEnv : platform.Environment}
    (witness : platform.Responds env request witnessResponse witnessEnv)
    (rest : ∀ (response : D.Response request) (env' : platform.Environment),
      platform.Responds env request response env' →
      Check ⟨env0, env', .running (resume (platform.encodeReturn call request response))⟩ ∨
      Safe platform Check n
        ⟨env0, env', .running (resume (platform.encodeReturn call request response))⟩) :
    Safe platform Check (n + 1) ⟨env0, env, .awaiting call request resume⟩ := by
  refine .stepOr ⟨_, _, _, Step.reply witness⟩ ?_
  intro choice event next step
  obtain ⟨response, env', allowed, _, _, nextEq⟩ := step.inv_awaiting
  rw [nextEq]
  exact rest response env' allowed

end Grass.Target.Machine
