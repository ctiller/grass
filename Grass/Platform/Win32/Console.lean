import Grass.ABI.Win64.Convention

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
  | handle (value : BitVec 64)
  /-- `INVALID_HANDLE_VALUE`, `(HANDLE)-1`: the call failed. -/
  | invalid
  /-- `NULL`: the process has no such standard device. Not an error. -/
  | null
deriving DecidableEq, Repr, Inhabited

namespace GetStdHandleResult

/-- `INVALID_HANDLE_VALUE` as a 64-bit pattern. -/
def invalidHandleValue : BitVec 64 := 0xFFFFFFFFFFFFFFFF

/-- The `RAX` value the ABI returns for this result. -/
def returnValue : GetStdHandleResult → BitVec 64
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
theorem handle_distinguishable {v : BitVec 64} (h : (handle v).WellFormed) :
    (handle v).returnValue ≠ (null : GetStdHandleResult).returnValue ∧
      (handle v).returnValue ≠ (invalid : GetStdHandleResult).returnValue :=
  ⟨h.1, h.2⟩

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
def mk? (v : BitVec 64) : Option UsableHandle :=
  if h : (GetStdHandleResult.handle v).WellFormed then some ⟨_, h⟩ else none

/-- `mk?` succeeds exactly on values distinguishable from both sentinels. -/
theorem mk?_isSome_iff (v : BitVec 64) :
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
permitted, and only `WriteFile` has one here: `Allowed`, with `writeAdequate`
and `excess_not_allowed` around it. A reviewer pointed out that `GetStdHandle`
and process exit have no such relation at all -- nothing in this module says
which results are permitted for which `StdHandleId`, so the too-narrow and
too-wide analysis performed for `WriteFile` is simply absent for the other two
thirds of the surface. That is an open obligation, not a claim that any result
is permitted.

`StdHandleId.value` is likewise pinned only by `value_injective`, which says the
three identifiers are mutually distinct and nothing about which is which. A
consistent shift of all three -- input to -11, output to -12, error to -13 --
satisfies every theorem here and every gate in the tree; the reviewer checked.
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
  handle : BitVec 64
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

It is worth naming because `writeAdequate` witnesses adequacy with a `.failure`
response. A reviewer pointed out that the profile therefore proves "some
response is allowed" using the one response whose lawfulness is least certain.
Narrowing the branch to statuses the API documents is an open obligation; it
would strengthen `Allowed` without changing `excess_not_allowed` or
`success_allowed_or_excess`, which partition the `success` constructor and are
where the content is.
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
  ⟨.failure 0, trivial⟩

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
