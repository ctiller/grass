import Grass.Std.Logical.Vec

/-!
# The partial-write loop, reduced to sequence laws

`docs/SPIKE_PROOF_BURDEN.md` carries six `library-instance` rows. Three of them,
in three different spikes, are the same proof shape:

- Spike 1, `write_all_loop(payload)` — "standard partial-write induction over
  the derived payload suffix";
- Spike 2, `buffered_stdout(output_buffer, outUsed, committedPrefix)` —
  "standard partial-write consumer plus local buffer representation";
- Spike 3, `SliceConsumerInvariant(output, consumed, outLen)` — "standard
  partial-write consumer with gzip output ownership".

A fourth, Spike 3's `crc32_prefix(transferred - remaining)`, indexes the same
prefix but is a "standard CRC prefix theorem", so what it needs beyond this
section is a CRC model rather than more sequence law.

`library-instance` means "a parametric proved constructor is named with its
arguments and residual goals", and §7 of that document requires every
`library-instance` to "report the exact theorem and arguments". So the ledger is
asking for one reusable theorem, and the question this fixture answers is a
narrow one: does the pure half of that theorem hold with only
`Grass/Std/Logical/Vec.lean`, or does it need something the library does not
have?

It holds. Every proof below is a `Vec` law applied, with `omega` for the
arithmetic. Nothing here needs induction, which is the point: the induction is
already discharged inside `Vec.take_add` and `Vec.drop_drop`.

## What this fixture is not

It is not the four burdens. `docs/STDLIB.md` §6 puts machine-state templates such
as `SliceConsumerInvariant` in the CFG proof library rather than in `Std.Logical`,
because "the pure library owns ordered-sequence and slice laws, while the CFG
layer connects those laws to selected registers, pointers, provenance, and
loans." Nothing below mentions a register, a handle, a provenance token, or a
loan, and the connection to those is exactly the part this fixture does not do.

What it establishes is the division of labour: an author instantiating
`write_all_loop` inherits conservation, exact-prefix commitment, monotonicity,
and termination from here, and owes only the register-to-sequence connection.
`Spikes/1_Hello_World/Program.lean`'s loop carries `cursor` in `r13` and
`remaining` in `r14d`; the two theorems that make its `add r13, rax` /
`sub r14d, eax` step sound are `step_commits_exactly` and `step_shortens` below.
-/

namespace Grass.Tests.Std

open Grass.Std.Logical

universe u

variable {α : Type u}

/--
A partial-write loop's state: a payload and a count of how much of it has been
written. The bound is a field because every law below needs it and a loop that
could not maintain it would not be a partial-write loop.
-/
structure WriteState (α : Type u) where
  /-- The whole sequence being written. -/
  payload : Vec α
  /-- How many elements have been committed so far. -/
  written : Nat
  /-- The written count never runs past the payload. -/
  bound : written ≤ payload.length

namespace WriteState

/-- The prefix that has been committed. -/
def committed (s : WriteState α) : Vec α := s.payload.take s.written

/-- The suffix that has not. -/
def remaining (s : WriteState α) : Vec α := s.payload.drop s.written

/-- The state a loop starts in: nothing written. -/
def start (payload : Vec α) : WriteState α :=
  { payload, written := 0, bound := Nat.zero_le _ }

@[simp] theorem start_committed (payload : Vec α) :
    (start payload).committed = Vec.empty := by
  simp [start, committed]

@[simp] theorem start_remaining (payload : Vec α) :
    (start payload).remaining = payload := by
  simp [start, remaining]

/-- Conservation: the committed prefix and the unwritten suffix reconstruct the
payload, in every state, not merely at the end. -/
theorem conserved (s : WriteState α) : s.committed ++ s.remaining = s.payload :=
  Vec.append_splitAt s.payload s.written

/-- The remaining length is the payload length less what was written. This is what
`r14d` holds in `Spikes/1_Hello_World/Program.lean`. -/
theorem remaining_length (s : WriteState α) :
    s.remaining.length = s.payload.length - s.written := by
  simp [remaining]

/-- The loop's exit test. Nothing remains exactly when everything was written, so
testing the counter and testing the sequence agree. -/
theorem remaining_empty_iff (s : WriteState α) :
    s.remaining = Vec.empty ↔ s.written = s.payload.length := by
  rw [remaining, Vec.drop_eq_empty_iff]
  have := s.bound
  omega

/-- Commit `k` more elements. -/
def step (s : WriteState α) (k : Nat) (fits : s.written + k ≤ s.payload.length) :
    WriteState α :=
  { payload := s.payload, written := s.written + k, bound := fits }

@[simp] theorem step_payload (s : WriteState α) (k : Nat)
    (fits : s.written + k ≤ s.payload.length) : (s.step k fits).payload = s.payload := rfl

/--
A step commits exactly the next `k` elements and nothing else.

This is the theorem the ledger's "commits exact prefixes" reduces to, and it is
`Vec.take_add` applied. Without it, a provider that reported writing `k` bytes
could be modelled as having committed some other `k` elements.
-/
theorem step_commits_exactly (s : WriteState α) (k : Nat)
    (fits : s.written + k ≤ s.payload.length) :
    (s.step k fits).committed = s.committed ++ s.remaining.take k :=
  Vec.take_add s.payload s.written k

/-- A step never retracts what an earlier step committed. -/
theorem step_extends (s : WriteState α) (k : Nat)
    (fits : s.written + k ≤ s.payload.length) :
    s.committed.IsPrefix (s.step k fits).committed :=
  Vec.take_isPrefix_take s.payload (Nat.le_add_right _ _)

/-- The unwritten suffix after a step is the suffix of the one before it. -/
theorem step_remaining (s : WriteState α) (k : Nat)
    (fits : s.written + k ≤ s.payload.length) :
    (s.step k fits).remaining = s.remaining.drop k := by
  simp [step, remaining]

/--
A positive step strictly shortens what is left, while anything is left.

This is the loop variant. `Spikes/1_Hello_World/Program.lean` has a separate
`exit_no_progress` terminal precisely because a provider reporting zero written
bytes cannot be allowed to satisfy this, and the `0 < k` hypothesis is where that
shows up in the proof rather than in a comment.
-/
theorem step_shortens (s : WriteState α) (k : Nat)
    (fits : s.written + k ≤ s.payload.length) (positive : 0 < k)
    (unfinished : s.written < s.payload.length) :
    (s.step k fits).remaining.length < s.remaining.length := by
  simp only [remaining, step, Vec.length_drop]
  omega

end WriteState

/-! ## The loop, run

A concrete three-step trace, so the laws above are exercised on values rather
than only quantified over. The payload is the bytes of `Hi!`, written two then
one, as a provider making partial progress would.
-/

def hi : Vec Byte := Vec.fromList [0x48, 0x69, 0x21]

def s0 : WriteState Byte := WriteState.start hi

def s1 : WriteState Byte := s0.step 2 (by decide)

def s2 : WriteState Byte := s1.step 1 (by decide)

example : s0.remaining.toList = [0x48, 0x69, 0x21] := rfl
example : s1.committed.toList = [0x48, 0x69] := rfl
example : s1.remaining.toList = [0x21] := rfl
example : s2.committed.toList = [0x48, 0x69, 0x21] := rfl
example : s2.remaining = Vec.empty := rfl

/-- The trace ends done, by the exit test rather than by inspection. -/
example : s2.written = s2.payload.length := (WriteState.remaining_empty_iff s2).mp rfl

/-- And nothing was lost on the way: conservation holds at the middle step, which
is the one where both halves are non-empty. -/
example : s1.committed ++ s1.remaining = hi := WriteState.conserved s1

end Grass.Tests.Std
