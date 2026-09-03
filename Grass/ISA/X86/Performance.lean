import Grass.ISA.X86.Sources

/-!
# Machine performance and timing-leakage model

A `CostModel` is for two things, and they want different guarantees.

**Security.** "The time this program takes does not depend on the secret." That
is a theorem, and proving it does not require predicting a single cycle
correctly — only knowing which quantities the cost is a *function of*. A model
that says "this instruction's cost depends on its opcode and operand widths but
not on operand values" supports the proof even if its cycle counts are wildly
wrong.

**Performance.** "This loop should take about 9 cycles per iteration." That
needs the numbers to be roughly right; they are measurements of a particular
chip, carried as `TimingBasis.measured` rather than as anything guaranteed.

These are separated throughout, because merging them is how an unguaranteed
measurement ends up load-bearing in a security proof. `TimingBasis` records
which kind of claim each fact is, and `TimingFact.SoundFor` accepts only
architectural guarantees.

## Why not floats

The predecessor `gasm` model (`Gasm/Targets/X86_64/Performance.lean`) computes
port pressure and cycle bounds in `Float`. That is right for a report and wrong
here: `Float` has no useful algebraic laws in Lean, does not reduce in the
kernel, and cannot carry a proof. Every quantity below is `Nat`, and every bound
is a whole number of cycles or uops. Where a rate would naturally be fractional
— reciprocal throughput — the model counts whole uops per port instead and
takes a maximum, which is the same bound without leaving the integers.

## Why the timing classification is dual-cited

`docs/DECISIONS.md` 15 makes the ISA the reviewed intersection of the Intel and
AMD contracts. The same applies here and is the whole reason a *security* claim
is possible: both vendors publish which instructions have data-operand-
independent timing, so the set Grass may rely on is the intersection of the two
published lists. An instruction on neither list, or on only one, is
`.dataDependent` for the common profile and a `VendorRefinement` at best.

Microarchitectural *latencies* get no such treatment, because no vendor makes
them a promise: they carry `TimingBasis.measured`, which
`TimingBasis.admissibleForSecurity` rejects.

## What this module does not model

Cache state, branch prediction state, frequency scaling, SMT contention, and
speculative execution. Their absence is why `LeakageChannel` names
`dataAddress` and `controlFlow` as channels rather than pretending a cycle count
covers them: a program whose *cost function* is value-independent can still leak
through which addresses it touched. `LeakageProfile` therefore tracks the
channels separately from the cost, and the security predicate closes all of
them, not just the arithmetic one.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

/-! ## What a timing fact rests on -/

/--
The kind of claim a timing fact is.

The distinction is load-bearing rather than bookkeeping: a security proof may
consume only `architectural`, because that is the only class anyone has
promised. `measured` numbers are a description of one chip on one day.
-/
inductive TimingBasis where
  /-- Measured on named hardware by a named harness. A fact about a part, not
  about an architecture.

  Deliberately **first**, so that it is what `Inhabited` hands out. With
  `architectural` first, `default : TimingBasis` was a vendor guarantee, and
  anything reaching for a default — `Option.getD`, an empty-list lookup — minted
  one silently. The weakest claim is the safe default; the strongest must be
  written on purpose. -/
  | measured (part : String)
  /-- The vendor's optimization guide states it as guidance. Useful, revisable,
  and not a promise. -/
  | optimizationGuide
  /-- The vendor documents this as a guarantee of the architecture — for
  example a published data-operand-independent-timing instruction list. Binding
  on future parts that claim the same architecture. -/
  | architectural
deriving DecidableEq, Repr, Inhabited

namespace TimingBasis

/-- Whether a security argument may rest on a fact with this basis.

Only `architectural`. `docs/VALIDATION.md` §1: "Undocumented observations may
motivate a restriction or research item, never a portable guarantee." -/
def admissibleForSecurity : TimingBasis → Bool
  | .architectural => true
  | .optimizationGuide => false
  | .measured _ => false

@[simp] theorem measured_inadmissible (part : String) :
    (TimingBasis.measured part).admissibleForSecurity = false := rfl

@[simp] theorem optimizationGuide_inadmissible :
    TimingBasis.optimizationGuide.admissibleForSecurity = false := rfl

end TimingBasis

/-! ## Leakage channels -/

/--
A way execution time can reveal something.

Naming these separately is what stops a cost model from being mistaken for a
timing-safety argument. An instruction sequence whose *cycle count* is a
function of the opcodes alone still leaks through `dataAddress` if it indexes
memory by a secret, because the cache is not in the cost function.
-/
inductive LeakageChannel where
  /-- Execution time depends on the *values* in the operands. Integer division
  is the standard example. -/
  | operandValue
  /-- Execution time depends on the addresses touched, through the cache and
  the TLB. Any secret-dependent index is this channel. -/
  | dataAddress
  /-- Execution time depends on which way control went, through the branch
  predictor and the instruction cache. -/
  | controlFlow
deriving DecidableEq, Repr, Inhabited

namespace LeakageChannel

/-- Every channel this model knows about.

A profile lists the channels it *establishes* closed, so a channel added to this
type is closed by no existing profile until someone reviews and adds it — which
is the reopening `LeakageProfile.closed` describes. `sealed_closes_all` is
stated over this list, so it stops holding the moment the list grows. -/
def all : List LeakageChannel := [.operandValue, .dataAddress, .controlFlow]

theorem mem_all (c : LeakageChannel) : c ∈ all := by cases c <;> decide

end LeakageChannel

/--
Which channels a fact establishes are closed.

`docs/INSTRUCTIONS.md` §1: "Missing metadata is rejection, not a default empty
effect." The empty profile therefore establishes *nothing* and closes no
channel, which is the honest reading of silence. Claiming a channel closed takes
an entry, and that entry needs the citation `TimingFact` carries.
-/
structure LeakageProfile where
  /-- The channels this fact **establishes** are closed.

  This direction, not "channels it leaks through", and the difference is the
  whole point. With a leaks-through list, a channel nobody considered is absent
  from it and therefore closed — so adding a fourth `LeakageChannel` tomorrow
  would silently make every existing profile claim to close it. Listing what is
  *established* means an unconsidered channel is open until someone accounts for
  it, which is what `docs/INSTRUCTIONS.md` §1 requires: "Missing metadata is
  rejection, not a default empty effect." -/
  closed : List LeakageChannel
deriving DecidableEq, Repr, Inhabited

namespace LeakageProfile

/-- Closes every channel this model currently knows about. A strong claim, and
only usable with an `architectural` basis behind it.

Written out rather than defined as `⟨LeakageChannel.all⟩`, so that adding a
channel does *not* silently extend this claim to cover it. A new constructor
leaves `sealed` open on it until someone reviews and adds it here, which is the
reopening the header promises. -/
def sealed : LeakageProfile := ⟨[.operandValue, .dataAddress, .controlFlow]⟩

/-- Closes everything except the addresses it touches — the profile of an
ordinary load or store whose timing does not depend on the value moved. -/
def addressOnly : LeakageProfile := ⟨[.operandValue, .controlFlow]⟩

/-- Whether this profile establishes that a channel is closed. -/
def closes (p : LeakageProfile) (c : LeakageChannel) : Bool := p.closed.contains c

/-- The profile closes every channel in the given set. -/
def Closes (p : LeakageProfile) (cs : List LeakageChannel) : Prop :=
  ∀ c ∈ cs, p.closes c = true

instance (p : LeakageProfile) (cs : List LeakageChannel) : Decidable (p.Closes cs) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `sealed` closes every channel the model knows about today.

Stated over `LeakageChannel.all` rather than over an arbitrary list. The old
form was provable for *every* list, including channels that did not exist, which
is what made the default-closed representation look sound. -/
@[simp] theorem sealed_closes_all : sealed.Closes LeakageChannel.all := by decide

/-- Running two things in sequence closes only what **both** close.

An intersection, not a union: if either part leaks through a channel, the
sequence does. -/
def sequence (p q : LeakageProfile) : LeakageProfile :=
  ⟨p.closed.filter (fun c => q.closed.contains c)⟩

theorem closes_sequence {p q : LeakageProfile} {c : LeakageChannel}
    (hp : p.closes c = true) (hq : q.closes c = true) :
    (p.sequence q).closes c = true := by
  simp only [closes, sequence, List.contains_eq_mem, decide_eq_true_eq,
    List.mem_filter] at *
  exact ⟨hp, by simpa using hq⟩

end LeakageProfile

/-! ## A timing fact about one instruction -/

/--
What this profile claims about one instruction's timing, and on what authority.

`subject` names the modeled instruction so the fact can be joined to the
citation ledger the same way an encoding rule is.
-/
structure TimingFact where
  /-- The instruction this is about. -/
  subject : Name
  /-- Which channels this fact establishes are closed. -/
  leakage : LeakageProfile
  /-- What kind of claim this is. -/
  basis : TimingBasis
  /-- Grass's statement of the claim, for review against the anchors. -/
  statement : String
  /-- Both vendors' anchors for exactly this subject.

  A timing fact carries the same citation burden as an encoding rule, and for
  the same reason: `docs/DECISIONS.md` 15 makes the common profile the
  intersection of two contracts, and a data-operand-independent-timing claim is
  only as good as the two published lists behind it. Without this field the
  header's whole "why the timing classification is dual-cited" section described
  an intention rather than a structure. -/
  citation : DualCitation subject

namespace TimingFact

/--
This fact may be used in a security argument: it rests on an architectural
guarantee and closes every channel named.

Both halves are needed and they fail independently. A measured observation that
an instruction happens to be constant-time on one part is not a guarantee about
the architecture; an architectural guarantee that says nothing about the
`dataAddress` channel does not close it.
-/
def SoundFor (f : TimingFact) (cs : List LeakageChannel) : Prop :=
  f.basis.admissibleForSecurity = true ∧ f.leakage.Closes cs

instance (f : TimingFact) (cs : List LeakageChannel) : Decidable (f.SoundFor cs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A measured fact is never sound for a security argument, whatever it claims
about leakage. -/
theorem not_soundFor_measured {f : TimingFact} {part : String}
    (h : f.basis = .measured part) (cs : List LeakageChannel) :
    ¬ f.SoundFor cs := by
  intro hs
  have := hs.1
  rw [h] at this
  exact absurd this (by simp)

/-- Nor is an optimization-guide fact. -/
theorem not_soundFor_optimizationGuide {f : TimingFact}
    (h : f.basis = .optimizationGuide) (cs : List LeakageChannel) :
    ¬ f.SoundFor cs := by
  intro hs
  have := hs.1
  rw [h] at this
  exact absurd this (by simp)

end TimingFact

/-! ## The cost model -/

/--
A cost model over an abstract instruction type and an abstract notion of "the
values the operands hold".

Abstract in both because the security theorem does not need either to be
concrete, and stating it here rather than after a machine state exists keeps the
theorem from quietly depending on one. `Insn` becomes the raw instruction type
and `Vals` becomes the projection of machine state the cost could see, when this
is plugged into execution semantics.
-/
structure CostModel (Insn Vals : Type) where
  /-- Cycles this instruction takes, given what its operands hold. -/
  cost : Insn → Vals → Nat

namespace CostModel

variable {Insn Vals : Type}

/--
This instruction's cost does not depend on operand values.

The property the security theorem is built from, and the reason it can be proved
without any cycle count being correct: it says the cost function *ignores* an
argument, not what the function returns.
-/
def ValueIndependent (m : CostModel Insn Vals) (i : Insn) : Prop :=
  ∀ v₁ v₂ : Vals, m.cost i v₁ = m.cost i v₂

/-- The cost of a trace: a sequence of instructions each paired with the values
in effect when it ran. -/
def traceCost (m : CostModel Insn Vals) : List (Insn × Vals) → Nat
  | [] => 0
  | (i, v) :: rest => m.cost i v + m.traceCost rest

@[simp] theorem traceCost_nil (m : CostModel Insn Vals) : m.traceCost [] = 0 := rfl

@[simp] theorem traceCost_cons (m : CostModel Insn Vals) (i : Insn) (v : Vals)
    (rest : List (Insn × Vals)) :
    m.traceCost ((i, v) :: rest) = m.cost i v + m.traceCost rest := rfl

/-- The instruction sequence of a trace, with the values dropped. -/
def instructions : List (Insn × Vals) → List Insn := List.map Prod.fst

@[simp] theorem instructions_nil : (instructions ([] : List (Insn × Vals))) = [] := rfl

@[simp] theorem instructions_cons (i : Insn) (v : Vals) (rest : List (Insn × Vals)) :
    instructions ((i, v) :: rest) = i :: instructions rest := rfl

/--
**Two executions of the same instruction sequence take the same time, whatever
values they carried.**

This is the timing-safety theorem. Its premises are exactly what a caller must
establish, and neither is about cycle counts:

- the two traces ran the same instructions in the same order — which is the
  `controlFlow` channel, discharged elsewhere by showing the secret does not
  select a branch;
- every instruction in that sequence is `ValueIndependent` — which is the
  `operandValue` channel, discharged by the dual-cited timing facts.

The `dataAddress` channel is *not* discharged here and cannot be: this model has
no cache, so two traces with identical instructions and identical costs may
still differ in the addresses they touched. `LeakageChannel.dataAddress` exists
to keep that visible, and a full timing-safety argument owes it separately.
-/
theorem traceCost_eq_of_valueIndependent (m : CostModel Insn Vals)
    (t₁ t₂ : List (Insn × Vals))
    (hsame : instructions t₁ = instructions t₂)
    (hind : ∀ i ∈ instructions t₁, m.ValueIndependent i) :
    m.traceCost t₁ = m.traceCost t₂ := by
  induction t₁ generalizing t₂ with
  | nil =>
      cases t₂ with
      | nil => rfl
      | cons hd tl => exact absurd hsame (by simp [instructions])
  | cons hd tl ih =>
      cases t₂ with
      | nil => exact absurd hsame (by simp [instructions])
      | cons hd₂ tl₂ =>
          obtain ⟨i, v⟩ := hd
          obtain ⟨i₂, v₂⟩ := hd₂
          simp only [instructions_cons, List.cons.injEq] at hsame
          obtain ⟨hi, htl⟩ := hsame
          subst hi
          have hhead : m.cost i v = m.cost i v₂ :=
            hind i (by simp [instructions]) v v₂
          have hrest : m.traceCost tl = m.traceCost tl₂ :=
            ih tl₂ htl (fun j hj => hind j (by
              simp only [instructions_cons, List.mem_cons]
              exact Or.inr hj))
          simp only [traceCost_cons, hhead, hrest]

/-- A trace of value-independent instructions costs the same as any other trace
of the same instructions — stated as a function of the instruction sequence
alone, which is the form a caller usually wants. -/
theorem traceCost_determined (m : CostModel Insn Vals) (t : List (Insn × Vals))
    (hind : ∀ i ∈ instructions t, m.ValueIndependent i) (t' : List (Insn × Vals))
    (hsame : instructions t = instructions t') :
    m.traceCost t = m.traceCost t' :=
  m.traceCost_eq_of_valueIndependent t t' hsame hind

end CostModel

/-! ## Microarchitectural profile

The quantitative half. Everything here is `measured` or `optimizationGuide` and
is therefore inadmissible in a security argument by `TimingBasis`. It exists for
performance work and for reporting, and `TimingFact.SoundFor` is what keeps it
out of a security proof rather than convention.
-/

/-- An execution port.

A `Nat` rather than a closed `p0`-`p11` enumeration because port counts and
meanings are microarchitecture-specific: `docs/FOUNDATION.md` law 8 forbids a
closed sum where new members are expected, and every new core is a new member.
`MicroarchProfile.portCount` bounds the valid range. -/
abbrev PortId := Nat

/-- What kind of execution resource a micro-operation needs. -/
inductive UopClass where
  /-- Integer arithmetic and logic. -/ | intALU
  /-- Integer multiply. -/ | intMul
  /-- Integer divide. Data-dependent latency on most parts. -/ | intDiv
  /-- Address generation. -/ | addressGen
  /-- A load. -/ | load
  /-- The address half of a store. -/ | storeAddress
  /-- The data half of a store. -/ | storeData
  /-- A branch. -/ | branch
deriving DecidableEq, Repr, Inhabited

/-- One micro-operation. -/
structure Uop where
  /-- Which resource class it needs. -/
  uopClass : UopClass
  /-- The ports that can execute it. -/
  eligiblePorts : List PortId
  /-- Result latency in cycles. -/
  latency : Nat
deriving DecidableEq, Repr, Inhabited

/--
A named microarchitecture's pipeline capacities.

Carries a `basis` and a citation because a cycle bound derived from these
numbers inherits their trust class, and `docs/VALIDATION.md` §6 requires a
profile to publish "validation environments and last successful campaigns".
-/
structure MicroarchProfile where
  /-- The microarchitecture's name. -/
  name : Name
  /-- How many execution ports it has. Port ids are `0` to `portCount - 1`. -/
  portCount : Nat
  /-- Micro-operations issued per cycle. -/
  issueWidth : Nat
  /-- What kind of claim these numbers are. Never `architectural`: no vendor
  guarantees pipeline widths. -/
  basis : TimingBasis
  /-- Where the numbers came from. -/
  citation : Citation
deriving DecidableEq, Repr

namespace MicroarchProfile

/-- A port id this profile actually has. -/
def ValidPort (p : MicroarchProfile) (id : PortId) : Prop := id < p.portCount

instance (p : MicroarchProfile) (id : PortId) : Decidable (p.ValidPort id) :=
  inferInstanceAs (Decidable (_ < _))

/-- How many of these uops can only go to ports this profile does not have.

A uop bound to a nonexistent port would silently contribute no pressure and make
the bound below an underestimate, so this is checked rather than assumed. -/
def unroutable (p : MicroarchProfile) (uops : List Uop) : List Uop :=
  uops.filter fun u => u.eligiblePorts.all fun id => decide (¬ p.ValidPort id)

/-- Every uop can reach at least one port this profile has. -/
def Routable (p : MicroarchProfile) (uops : List Uop) : Prop :=
  ∀ u ∈ uops, ∃ id ∈ u.eligiblePorts, p.ValidPort id

end MicroarchProfile

/-- How many uops in a list can only be executed on one given port.

Counting the uops with no alternative is the sound half of port pressure: a uop
with a choice may be steered away, but one bound to a single port must wait for
it, so this is a lower bound on that port's occupancy and never an
overestimate. -/
def portPressure (uops : List Uop) (id : PortId) : Nat :=
  (uops.filter fun u => u.eligiblePorts == [id]).length

/--
A lower bound on the cycles a block of uops takes, in whole cycles.

The larger of two independent constraints: the issue width cannot retire more
than `issueWidth` uops per cycle, and a port with `n` uops bound to it needs at
least `n` cycles. Both are `Nat`, and the bound is a *lower* bound — the honest
direction for a model that omits cache misses, branch mispredictions and
contention, all of which only add time.
-/
def cycleLowerBound (p : MicroarchProfile) (uops : List Uop) : Nat :=
  let byIssue := if p.issueWidth = 0 then uops.length
                 else (uops.length + p.issueWidth - 1) / p.issueWidth
  let byPort := (List.range p.portCount).foldl
    (fun acc id => max acc (portPressure uops id)) 0
  max byIssue byPort

/-- No uops, no cycles. -/
@[simp] theorem cycleLowerBound_nil (p : MicroarchProfile) :
    cycleLowerBound p [] = 0 := by
  have hports : ∀ (l : List PortId) (acc : Nat),
      l.foldl (fun acc id => max acc (portPressure [] id)) acc = acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons hd tl ih => intro acc; simpa [portPressure] using ih acc
  simp only [cycleLowerBound, hports]
  split
  · simp
  · rename_i hne
    have hpos : 0 < p.issueWidth := Nat.pos_of_ne_zero hne
    have hzero : (List.length ([] : List Uop) + p.issueWidth - 1) / p.issueWidth = 0 :=
      Nat.div_eq_of_lt (by simp only [List.length_nil]; omega)
    simp only [hzero, Nat.max_self]

end Grass.ISA.X86
