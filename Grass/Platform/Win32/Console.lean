import Grass.ISA.X86.Citation
import Grass.Platform.Win32.Profile

/-!
# Win32 standard-output API contracts

`GetStdHandle`, `WriteFile` and `ExitProcess` — the three imports
`docs/HELLO_WORLD.md` names, modeled as the contracts
`docs/PLATFORM_ABI.md` §2 requires rather than as function signatures.

## What a contract has to say

`docs/PLATFORM_ABI.md` §2 lists what every API operation declares: complete
input domain, all permitted return values, partial completion, failure
outcomes, and the rest. The load-bearing part for this milestone is the shape of
`Allowed`:

> "Its `Allowed` relation covers every behavior permitted by the cited external
> contract; it may restrict behavior only when a cited stronger platform
> precondition justifies the restriction. A profile with `Allowed q r := False`
> and no pending behavior is unusable."

Two failure modes, opposite directions, and both are silent:

- **Too narrow** is unsound. A profile that forgets partial writes proves a
  program correct that mishandles them. `writeAdequate` is the check that at
  least one response is allowed for every request, and it is deliberately weak;
  the real defence against narrowness is that the permitted set is enumerated
  from the documentation, not from what the program happens to handle.
- **Too wide** makes the program unverifiable rather than wrong, which is the
  safe direction and why over-approximation is permitted.

## Where the environment-violation boundary sits

`WriteFile` reporting more bytes written than were requested is not a failure
response. It is outside the contract entirely, and `docs/DECISIONS.md` 28 ends
assurance at the first such violation:

> "Environment-contract violations receive assurance only through the maximal
> matched safe prefix before the first violation."

So `excessWriteCount` is *not* a constructor of `WriteResponse`. Putting it
there would make it a behaviour the program must handle to be correct, when the
truth is that no conforming behaviour follows it. It is a separate predicate on
a response that would otherwise be a success, and `Spikes/1_Hello_World` carries
a containment tail for exactly it — optional hardening, never part of the
conforming theorem.

## Zero-byte writes

A successful write of zero bytes is *allowed* by the contract and makes no
progress. `docs/HELLO_WORLD.md` requires it to be "handled as an explicit
no-progress failure unless a stronger provider contract supplies a reviewed
progress rule", so it stays in `Allowed` — the environment may do it — and the
program takes a failure branch. Modeling it as forbidden would be the
too-narrow error above.
-/

namespace Grass.Platform.Win32

open Grass.Core Grass.Cite

/-- A Win32 `HANDLE`.

The width follows `decision16` rather than being written here.
`Grass/Platform/Win32/Profile.lean` recorded the alternative as owed: this
module used to state `BitVec 64` independently of the profile that selects the
ABI, so the two agreed by inspection, and its header names that as "the exact
hazard `Console` itself records for `StdHandleId.value`" -- a constant that
happens to be right.

Now it is a consequence. A second `TargetAbi` with a different `handleBits`
changes this type, and every declaration below with it, rather than leaving a
64 here that nothing rechecks. `TargetAbi.handleBits` is total, so such an ABI
cannot be added without answering the question. -/
abbrev Handle : Type := BitVec decision16.abi.handleBits

/-! ## Handles -/

/--
Which standard device `GetStdHandle` is asked for.

A closed type: the documented input domain is exactly these three values, and
`docs/PLATFORM_ABI.md` §2 requires the "complete input domain" rather than an
open integer that would leave the other 2^32 - 3 cases unmodeled.
-/
inductive StdHandleId where
  /-- `STD_INPUT_HANDLE`, `(DWORD)-10`. -/ | input
  /-- `STD_OUTPUT_HANDLE`, `(DWORD)-11`. -/ | output
  /-- `STD_ERROR_HANDLE`, `(DWORD)-12`. -/ | error
deriving DecidableEq, Repr, Inhabited

namespace StdHandleId

/-- The `DWORD` value passed in `ECX`, as an unsigned 32-bit pattern. -/
def value : StdHandleId → BitVec 32
  | .input => 0xFFFFFFF6   -- -10
  | .output => 0xFFFFFFF5  -- -11
  | .error => 0xFFFFFFF4   -- -12

/-- The three values are distinct, so the argument determines the device. -/
theorem value_injective {a b : StdHandleId} (h : a.value = b.value) : a = b := by
  revert h; cases a <;> cases b <;> decide

/--
**Each identifier has the value the API documents, not merely a distinct one.**

`value_injective` says the three are mutually distinct and nothing about which
is which -- a reviewer showed that shifting all three consistently, input to
-11 and output to -12 and error to -13, satisfies it and every other theorem in
this file. That freedom is not harmless: `GetStdHandle` would then return the
console's output handle for a request meant for input, and a program writing
its results would read them back instead.

So the three constants are stated individually. `STD_INPUT_HANDLE` is
`(DWORD)-10`, `STD_OUTPUT_HANDLE` is `-11` and `STD_ERROR_HANDLE` is `-12`, and
as unsigned thirty-two bit patterns those are `0xFFFFFFF6`, `0xFFFFFFF5` and
`0xFFFFFFF4`. A shift now contradicts this rather than passing it.

This closes the second of the two obligations this module's header recorded.
The first -- narrowing `WriteResult.Allowed` to the statuses the API
documents -- remains open. -/
theorem value_pinned :
    StdHandleId.input.value = 0xFFFFFFF6
    ∧ StdHandleId.output.value = 0xFFFFFFF5
    ∧ StdHandleId.error.value = 0xFFFFFFF4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/--
**The values are consecutive descending, which is why a shift looked plausible.**

Stated because it is the pattern that makes the three easy to mis-remember as a
block: they differ by one, so any consistent renumbering preserves every
relation between them. It is `value_pinned` and not this that rules a shift
out; this records why the shift was a tempting mistake rather than an obvious
one. -/
theorem value_consecutive :
    StdHandleId.input.value = StdHandleId.output.value + 1
    ∧ StdHandleId.output.value = StdHandleId.error.value + 1 := by
  refine ⟨?_, ?_⟩ <;> decide

end StdHandleId

/--
What `GetStdHandle` returns.

Three outcomes, not two. `INVALID_HANDLE_VALUE` signals an error; a **null**
handle signals that the process has no such standard device, which is not an
error and is what a GUI process or one started with redirected-to-nothing
handles sees. A model with only "handle or error" would treat null as a usable
handle and pass it to `WriteFile`.

`Spikes/1_Hello_World/Program.lean` tests both — `test rax, rax` then
`cmp rax, INVALID_HANDLE_VALUE` — which is why both are here.
-/
inductive GetStdHandleResult where
  /-- A usable handle. The value is opaque; nothing may be inferred from it
  beyond that it is neither null nor `INVALID_HANDLE_VALUE`. -/
  | handle (value : Handle)
  /-- `INVALID_HANDLE_VALUE`, `(HANDLE)-1`: the call failed. -/
  | invalid
  /-- `NULL`: the process has no such standard device. Not an error. -/
  | null
deriving DecidableEq, Repr, Inhabited

namespace GetStdHandleResult

/-- `INVALID_HANDLE_VALUE` as a 64-bit pattern. -/
def invalidHandleValue : Handle := 0xFFFFFFFFFFFFFFFF

/-- The `RAX` value the ABI returns for this result. -/
def returnValue : GetStdHandleResult → Handle
  | .handle v => v
  | .invalid => invalidHandleValue
  | .null => 0

/--
A result is well-formed when a `handle` really is distinguishable from the two
sentinels.

Without this, `handle 0` and `null` would be the same return value while being
different results, and a program that checked for null would be proved to have
checked something it had not.
-/
def WellFormed : GetStdHandleResult → Prop
  | .handle v => v ≠ 0 ∧ v ≠ invalidHandleValue
  | .invalid => True
  | .null => True

instance (r : GetStdHandleResult) : Decidable r.WellFormed := by
  cases r <;> unfold WellFormed <;> infer_instance

/-- A well-formed usable handle is distinguishable from both sentinels by its
return value alone, which is all the assembly can test. -/
theorem handle_distinguishable {v : Handle} (h : (handle v).WellFormed) :
    (handle v).returnValue ≠ (null : GetStdHandleResult).returnValue ∧
      (handle v).returnValue ≠ (invalid : GetStdHandleResult).returnValue :=
  ⟨h.1, h.2⟩

/--
Which results `GetStdHandle` may return for a given identifier.

The permitted-result relation this module lacked for two thirds of its surface.
It is deliberately weak, and the weakness is the claim: **nothing documented
makes the permitted results depend on which standard handle was asked for.**
Any of the three identifiers may yield a usable handle, may yield `NULL` when
the process has no such device, and may yield `INVALID_HANDLE_VALUE` on error.

So this says only that the result is well formed -- which is not nothing. It
excludes `handle 0` and `handle INVALID_HANDLE_VALUE`, the two values a caller
would misclassify with the `test rax, rax` and `cmp rax, -1` that
`Spikes/1_Hello_World/Program.lean` actually performs.

Stating a weak relation is better than stating none, but only because the
weakness is asserted rather than left as an absence. An earlier version of this
module had no relation here at all, and a reviewer noted that the too-narrow
and too-wide analysis done for `WriteFile.Allowed` was simply missing for the
other two calls. This makes the missing half a claim that can be attacked: if
the permitted set *is* id-dependent in some documented way, `permitted_id_
independent` below is false and should be refuted rather than quietly widened.
-/
def Permitted (_ : StdHandleId) (r : GetStdHandleResult) : Prop := r.WellFormed

instance (i : StdHandleId) (r : GetStdHandleResult) : Decidable (Permitted i r) :=
  inferInstanceAs (Decidable r.WellFormed)

/--
**The permitted set does not depend on the identifier.**

The content of `Permitted`, stated so it can be contradicted. Any documented
behaviour that made one identifier's permitted results differ from another's
would refute this. -/
theorem permitted_id_independent (a b : StdHandleId)
    (r : GetStdHandleResult) : Permitted a r ↔ Permitted b r := Iff.rfl

/--
**A colliding handle is not permitted, for any identifier.**

The half of `Permitted` that is not vacuous: the two values whose return value
a caller cannot tell from a sentinel are excluded. Without this the relation
would accept every result and say nothing. -/
theorem colliding_handle_not_permitted (i : StdHandleId) :
    ¬ Permitted i (.handle 0)
    ∧ ¬ Permitted i (.handle GetStdHandleResult.invalidHandleValue) :=
  ⟨fun h => h.1 rfl, fun h => h.2 rfl⟩

/--
**Every sentinel is permitted, for any identifier.**

The other half, and the reason `Permitted` is weak rather than wrong: a
process legitimately has no console, and `GetStdHandle` legitimately fails. A
relation that refused either would be too narrow, which is the error the
`WriteFile` analysis was careful to avoid in the other direction. -/
theorem sentinels_permitted (i : StdHandleId) :
    Permitted i .null ∧ Permitted i .invalid := ⟨trivial, trivial⟩

/--
The three results `handle 0` collides with, kept as theorems.

`WellFormed` was a predicate nobody had to satisfy: `handle 0` is freely
constructible, `handle_distinguishable` takes well-formedness as a hypothesis,
and nothing carried it. A reviewer made the point that this is the same defect
`Grass.ABI.Win64.SearchablePdata` was introduced to fix in the sibling module,
and that the fix pattern was already in the tree. `UsableHandle` below is it.
-/
theorem handle_zero_collides_with_null :
    (handle 0).returnValue = (null : GetStdHandleResult).returnValue := rfl

/-- And the other sentinel collides the same way. -/
theorem handle_invalid_collides :
    (handle invalidHandleValue).returnValue
      = (invalid : GetStdHandleResult).returnValue := rfl

end GetStdHandleResult

/--
A `GetStdHandle` result carrying the proof that a program can act on it.

`GetStdHandleResult.WellFormed` states the condition and nothing required it, so
`handle 0` -- indistinguishable from `null` by the only thing assembly can test,
its return value -- was as constructible as any other result. This is the shape
`Grass.ABI.Win64.SearchablePdata` uses: the obligation is a field, so the value
cannot exist without it, and `mk?` discharges it for a caller with a concrete
return value.
-/
structure UsableHandle where
  /-- The result. -/
  result : GetStdHandleResult
  /-- It is distinguishable from both sentinels. -/
  wellFormed : result.WellFormed

namespace UsableHandle

/-- Build a usable handle from a returned value, or refuse. -/
def mk? (v : Handle) : Option UsableHandle :=
  if h : (GetStdHandleResult.handle v).WellFormed then some ⟨_, h⟩ else none

/-- `mk?` succeeds exactly on values distinguishable from both sentinels. -/
theorem mk?_isSome_iff (v : Handle) :
    (mk? v).isSome ↔ (GetStdHandleResult.handle v).WellFormed := by
  unfold mk?
  by_cases h : (GetStdHandleResult.handle v).WellFormed
  case pos => rw [dif_pos h]; simp [h]
  case neg => rw [dif_neg h]; simp [h]

/-- Neither sentinel value yields a usable handle, so a caller that went
through `mk?` cannot be holding one. -/
theorem sentinels_refused :
    mk? 0 = none ∧ mk? GetStdHandleResult.invalidHandleValue = none := by
  constructor <;> decide

end UsableHandle

/-!
## What this module does not model

`docs/PLATFORM_ABI.md` §2 asks each API operation to declare which responses are
permitted, and `WriteFile` was long the only call here with one: `Allowed`,
with `writeAdequate` and `excess_not_allowed` around it. A reviewer pointed out
that `GetStdHandle` and process exit had no such relation at all, so the
too-narrow and too-wide analysis performed for `WriteFile` was simply absent
for the other two thirds of the surface.

`GetStdHandle` now has one. `Permitted` is deliberately weak -- it says the
result is well formed and nothing more -- but its weakness is asserted rather
than left implicit: `permitted_id_independent` claims that nothing documented
makes the permitted set depend on which identifier was asked for, which is a
statement that can be refuted. `colliding_handle_not_permitted` is the half
with content and `sentinels_permitted` is the half that keeps it from being too
narrow, since a process legitimately has no console.

Process exit needed no relation, and that was a misreading of the gap rather
than a gap. `ExitProcess` does not return, so there is no result for a relation
to range over: `ExitResponse` is empty and `exit_never_returns` says so. A
predicate over it would have been satisfied by `fun _ => False` as readily as
by anything true, which `exit_result_claims_vacuous` makes explicit. The two
absences the reviewer grouped together were not the same kind -- one was a
missing claim and the other was a claim with no subject.

`StdHandleId.value` used to be pinned only by `value_injective`, which says the
three identifiers are mutually distinct and nothing about which is which. A
consistent shift of all three -- input to -11, output to -12, error to -13 --
satisfied every theorem here and every gate in the tree; the reviewer checked.
`value_pinned` closes that: each constant is now stated individually, so a
shift is contradicted rather than tolerated. It was not a harmless freedom --
`GetStdHandle` would have returned the output handle for an input request, and
a program writing its results would read them back.
The constants are right, and the reason they are right is that they were read
off the SDK, not that anything mechanical would notice if they were not.

## WriteFile
-/

/--
A `WriteFile` request, in the part of its input domain this profile covers.

The buffer's contents do not appear: what is written is not what the *contract*
constrains, and the memory footprint is the memory model's concern. What matters
to the response is how many bytes were asked for.

`docs/HELLO_WORLD.md` fixes the product profile as
"explicitly synchronous-standard-output-only; inherited overlapped handles are
unsupported until an adaptive provider is realized", so `lpOverlapped` is null
by construction here rather than being a modeled field.
-/
structure WriteRequest where
  /-- The handle written to. -/
  handle : Handle
  /-- `nNumberOfBytesToWrite`. -/
  requested : BitVec 32
deriving DecidableEq, Repr, Inhabited

/--
What `WriteFile` returns.

`success` carries the byte count the call reported through
`lpNumberOfBytesWritten`, which may be **less** than requested — that is the
partial write the whole Spike 1 loop exists to handle — and may be **zero**,
which is allowed and makes no progress.
-/
inductive WriteResponse where
  /-- Returned nonzero. `written` is what `lpNumberOfBytesWritten` received. -/
  | success (written : BitVec 32)
  /-- Returned zero. `code` is what `GetLastError` would report. -/
  | failure (code : BitVec 32)
deriving DecidableEq, Repr, Inhabited

/--
The responses the cited contract permits for a request.

A success may report anything from zero up to the requested count inclusive. Any
failure code is permitted, which is `Allowed`'s over-approximation on the
`failure` branch: the documentation does not enumerate the codes the API may
return for an arbitrary handle, so restricting them would be a narrowing this
profile cannot cite.
-/
def Allowed (q : WriteRequest) (r : WriteResponse) : Prop :=
  match r with
  | .success written => written.toNat ≤ q.requested.toNat
  | .failure _ => True

instance (q : WriteRequest) (r : WriteResponse) : Decidable (Allowed q r) := by
  cases r <;> unfold Allowed <;> infer_instance

/-!
### A note on the failure branch

`Allowed q (.failure _) = True` for every status, including `.failure 0` -- a
returned zero with `GetLastError` reporting success, which is arguably outside
the documented contract rather than a lawful failure. The over-approximation is
in the safe direction: it admits a response the API may never produce, and never
rejects one it does.

A reviewer pointed out that `writeAdequate` used to witness adequacy with
`.failure 0`, so the profile proved "some response is allowed" using the one
response whose lawfulness is least certain. It now witnesses with
`.success q.requested`, a complete write, which is lawful beyond argument.
Adequacy no longer rests on the branch the note is about.

Narrowing the branch itself remains open and is deliberately not done here.
Requiring a nonzero status would strengthen `Allowed`, but it would also reject
a response if the API ever does produce one -- and this module's stated rule is
that too narrow is unsound while too wide only makes a program unverifiable.
Narrowing wants a documented enumeration of the statuses `WriteFile` can
report, which is what the citation campaign is for, not a guess about which
ones look plausible.
-/

/--
**Response adequacy.** Every well-formed request has at least one allowed
response.

`docs/PLATFORM_ABI.md` §2: "For every reachable well-formed request, either at
least one response is allowed or the contract explicitly admits a
pending/infinite blocking execution... A profile with `Allowed q r := False` and
no pending behavior is unusable."

This is a weak check and is meant to be. `writeAdequate` catches the profile
that is accidentally empty, and a profile that is merely too narrow is an **open
obligation** it cannot see, because nothing inside the model knows what the
documentation says. That is what the citation and the probe campaign are for.
-/
theorem writeAdequate (q : WriteRequest) : ∃ r, Allowed q r :=
  ⟨.success q.requested, Nat.le_refl _⟩

/-- Adequacy is not satisfied only by failures: a complete write is allowed for
every request, so the profile does not accidentally permit only errors. -/
theorem writeAdequate_success (q : WriteRequest) : Allowed q (.success q.requested) :=
  Nat.le_refl _

/-- A zero-byte success is allowed for every request.

Kept explicit because it is the response `docs/HELLO_WORLD.md` requires the
program to treat as a no-progress *failure*. It is permitted by the environment
and rejected by the program, and those are different statements. -/
theorem zeroWrite_allowed (q : WriteRequest) : Allowed q (.success 0) := by
  simp [Allowed]

/-- A partial write is allowed whenever it does not exceed the request. -/
theorem partialWrite_allowed (q : WriteRequest) (n : BitVec 32)
    (h : n.toNat ≤ q.requested.toNat) : Allowed q (.success n) := h

/-! ## The environment-contract violation -/

/--
The response reported more bytes written than were requested.

Not a `WriteResponse` constructor: no conforming behaviour follows it, so it is
not something a correct program handles. `docs/DECISIONS.md` 28 ends assurance
at the first environment-contract violation, and `docs/PLATFORM_ABI.md` §2
attaches a `ViolationReturnEnvelope` to exactly this narrow class — one that
"may retain ordinary Win64 control return, an initialized in-bounds
`bytesWritten` slot, returned call loans, and reconstructed frame authority
while proving only that the reported count exceeds the request".

That narrowness is the point. It is why a containment tail for this class can
say anything at all, where an arbitrary memory or control-transfer violation
leaves nothing to say.
-/
def ExcessWriteCount (q : WriteRequest) (r : WriteResponse) : Prop :=
  match r with
  | .success written => q.requested.toNat < written.toNat
  | .failure _ => False

instance (q : WriteRequest) (r : WriteResponse) : Decidable (ExcessWriteCount q r) := by
  cases r <;> unfold ExcessWriteCount <;> infer_instance

/-- The violation and the contract are exclusive: a response is never both
allowed and an excess-count violation. -/
theorem excess_not_allowed {q : WriteRequest} {r : WriteResponse}
    (h : ExcessWriteCount q r) : ¬ Allowed q r := by
  cases r with
  | success written =>
      simp only [ExcessWriteCount] at h
      simp only [Allowed]
      omega
  | failure code => exact absurd h (by simp [ExcessWriteCount])

/-- And they are exhaustive on successes: a success either honours the request
or violates it, with nothing in between. -/
theorem success_allowed_or_excess (q : WriteRequest) (written : BitVec 32) :
    Allowed q (.success written) ∨ ExcessWriteCount q (.success written) := by
  simp only [Allowed, ExcessWriteCount]
  omega

/-- A failure is never an excess-count violation, so the containment tail for
this class is unreachable from the failure path. -/
theorem failure_never_excess (q : WriteRequest) (code : BitVec 32) :
    ¬ ExcessWriteCount q (.failure code) := by simp [ExcessWriteCount]

/-! ## ExitProcess -/

/--
`ExitProcess` does not return.

Modeled as a type with no way to produce an ongoing execution rather than as a
function returning `Unit`, because `docs/HELLO_WORLD.md` requires that
"`ExitProcess` is not assumed to return" and a `Unit` return would let a proof
continue past it.

`Spikes/1_Hello_World/Program.lean` still places `ud2` after the call. That is
containment for the case where the contract is violated by returning, which
`docs/PLATFORM_ABI.md` §3 makes an explicit implementation policy rather than a
requirement of the conforming theorem.
-/
structure ExitRequest where
  /-- `uExitCode`, the status the process terminates with. -/
  status : BitVec 32
deriving DecidableEq, Repr, Inhabited

/--
What `ExitProcess` returns to the code that called it.

Empty, and that is the whole content. `ExitProcess` does not return: it
terminates the calling process, so no instruction after the call executes and
there is no value for a caller to inspect.

This is why `ExitProcess` has no permitted-result relation while `WriteFile`
and `GetStdHandle` do. An earlier version of this module's header recorded that
absence as an open obligation, alongside the same absence for `GetStdHandle`.
The two were not the same gap. `GetStdHandle`'s was real and is now filled by
`Permitted`; this one is not a missing relation but a relation with nothing to
range over, and saying so is the correct closure rather than inventing a
predicate over an empty domain.

The exit status is not a counterexample. It is delivered to whoever *waits* on
the process -- a parent, a shell -- and not to the caller, which no longer
exists to receive it. `ExitRequest` carries it for that reason and there is no
`ExitResponse` beside it.
-/
abbrev ExitResponse := PEmpty

/--
**`ExitProcess` never returns.**

Stated as the emptiness of its response type, which is what makes it
unwritable rather than merely undocumented: a caller cannot construct a
response, so no theorem in this tree can accidentally reason about what
follows the call. -/
theorem exit_never_returns (r : ExitResponse) : False := nomatch r

/--
**Every claim about a post-exit result is vacuous.**

The consequence worth having explicitly. Any predicate whatever holds of every
`ExitResponse`, which is precisely why writing a permitted-result relation for
this call would have been an empty gesture -- it would have been satisfied by
`fun _ => False` as readily as by anything true. -/
theorem exit_result_claims_vacuous (P : ExitResponse → Prop) :
    ∀ r, P r := fun r => nomatch r

/-- The exit status for a successful run, per `docs/HELLO_WORLD.md`: zero. -/
def successStatus : BitVec 32 := 0

/-- The exit status for every noncontinuable failure: one.

`docs/HELLO_WORLD.md` gives one public `.failure` outcome, so
"standard-output unavailable, write failure, and zero progress remain distinct
only in the complete audit trace". They share this status deliberately. -/
def failureStatus : BitVec 32 := 1

/-- The two statuses are distinguishable, which is what makes the terminal
protocol's `distinguish` law satisfiable for this program's demanded set. -/
theorem statuses_distinct : successStatus ≠ failureStatus := by decide

end Grass.Platform.Win32
