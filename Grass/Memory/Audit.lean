import Grass.Core.Context
import Grass.Core.Name
import Grass.Memory.Provenance
import Grass.Memory.Range

/-!
# The audit violation ledger

`docs/MEMORY_MODEL.md` §8: "Audit violations are a private append-only diagnostic
ledger. They cannot be erased or masked. `VerifiedProgram` proves the ledger
remains empty and that only spec-allowed fault outcomes occur."

**A naming collision worth stating.** `docs/SEMANTICS.md` §3 uses "audit trace"
for the complete observation trace, which a verified program certainly does not
keep empty — it contains the program's own output. That is a different object
from this one. The types here are named `AuditViolation` and
`AuditViolationLedger` so the two cannot be confused at a use site, and so that
the `@audit(.stdoutUnavailable)` annotations in the Spike 1 source, which
classify an ordinary modelled failure, are visibly not violations of this kind.

## What "append-only" can and cannot mean

The constructor and the record list are `private`, so outside this module the
only way to obtain a ledger is `empty` or `append`.

That is **not** the same as "no shorter ledger can be built", and an earlier
version of this comment claimed it was. Since `records?` reads the list out and
`append` folds it back in, anyone can construct
`(l.records?.filter keep).foldl append empty` — a laundered ledger, provable
equal to `empty` by `decide`. No private field prevents that, and no arrangement
of this type could: any type with a readable projection and a constructor can be
rebuilt.

So the property `docs/MEMORY_MODEL.md` §8 demands — "they cannot be erased or
masked" — is not a property of the type. It is a property of the *transition
relation*: the ledger threaded through an execution must only ever grow.
`Extends` states that, and M2's step relation owes a proof that every step
preserves it. What laundering produces is a different value that never enters the
execution; what would be a real violation is a step returning a ledger that does
not extend its input, and that is what `Extends` is there to forbid.

`recordCount` and `records?` are the read-only views diagnostics need. Reading a
ledger is safe; the prohibition is on constructing one.
-/

namespace Grass.Memory

open Grass.Core

/--
The identity of an audit violation class.

Open nominal: a profile classifies the ways its own authority checks can be
violated. This is not the fault taxonomy — a `FaultClassId` is architectural
behavior the specification may permit, while a violation of this kind is behavior
`VerifiedProgram` proves never happens.
-/
structure AuditViolationClass where
  /-- The violation class's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace AuditViolationClass

/-- An access was attempted outside the bounds its provenance authorizes. -/
def outOfBounds : AuditViolationClass := ⟨⟨"outOfBounds"⟩⟩

/-- An access was attempted through provenance that is no longer live. -/
def deadProvenance : AuditViolationClass := ⟨⟨"deadProvenance"⟩⟩

/-- An access was attempted without the permission it requires. -/
def permissionDenied : AuditViolationClass := ⟨⟨"permissionDenied"⟩⟩

/-- A read was attempted of bytes that are not initialized. -/
def uninitializedRead : AuditViolationClass := ⟨⟨"uninitializedRead"⟩⟩

/-- An access was attempted without satisfying its alignment demand. -/
def misaligned : AuditViolationClass := ⟨⟨"misaligned"⟩⟩

/-- An access was attempted without the authority its loan state requires. -/
def authorityUnavailable : AuditViolationClass := ⟨⟨"authorityUnavailable"⟩⟩

/-- An access declared a ledger effect its protocol does not authorize against
the obligations actually outstanding: consuming a duty that is not live,
producing an identity that already is, or splitting into obligations governed by
a different protocol. -/
def obligationNotAuthorized : AuditViolationClass := ⟨⟨"obligationNotAuthorized"⟩⟩

/-- Two accesses from distinct contexts touched the same bytes with at least one
writer, unordered and not both compatible atomic accesses — `docs/MEMORY_MODEL.md`
§7.3's race.

Distinct from `authorityUnavailable`, and this class exists because it was not.
`refusalOf` recorded three different rules under that one name: §3's authority-state
clause, §3's holder clause, and this. Review demonstrated a race recorded as
`authorityUnavailable` from a state where *nothing was held* — the ledger entry
byte-identical in class to a genuine loan violation. The rule against collapsing
distinguishable failures is stated three times in this layer (here for
`wrongAddressSpace`, again for `authorityEffectRefused`, and again for
`faultWithUndeclaredAuthorityEffect`) and was broken once, which is why §7.3's second
paragraph — race-freedom as a claim separate from an authority claim — could not be
stated by a profile. -/
def conflictingAccess : AuditViolationClass := ⟨⟨"conflictingAccess"⟩⟩

/-- An access declared a change to the authority map that the map refuses: lending
under an identity already in use, lending bytes the named lender does not hold,
returning a grant the acting context neither holds nor lent, splitting or joining
another context's authority, or a transfer that would leave a conflicting pair.

Distinct from `authorityUnavailable`, which is about an access *reading* bytes it
lacks authority over. This one is about an access *changing* who holds what. -/
def authorityEffectRefused : AuditViolationClass := ⟨⟨"authorityEffectRefused"⟩⟩

/-- An access to storage in an address space other than the one its provenance
names. `docs/MEMORY_MODEL.md` §7.5 makes this a distinct failure from a bounds
error: the spaces are not interchangeable, so reporting it as `outOfBounds` would
lose which rule was broken. -/
def wrongAddressSpace : AuditViolationClass := ⟨⟨"wrongAddressSpace"⟩⟩

/-- The machine could not complete an access the profile admitted.

`Oracle.answer` returns `none` when it cannot fill a completed access, and the
transition records this rather than accepting a short answer as success. It is a
statement about the *model*, not about the program: an oracle that cannot supply
the bytes a store declared is a machine description that does not match the
access, and `docs/FOUNDATION.md` law 8 says refuse rather than approximate. -/
def machineAnswerIncomplete : AuditViolationClass := ⟨⟨"machineAnswerIncomplete"⟩⟩

/-- A provenance whose recorded root extent is not the extent of the allocation it
names.

`Provenance.rootExtent` is what `AccessDescriptor.WellFormedIn.rangeInProvenance`
bounds an access against, and nothing compared it to the allocation table — so a
descriptor supplied the bound it was checked against, and a 512-byte write into a
64-byte allocation was well formed. `denialOf`'s extent check caught the write
incidentally, as `outOfBounds`, which is the wrong report: the access was not out
of the bounds it declared, it declared the wrong bounds. Review found the gap and
found `rootExtent`'s docstring claiming M2 checked it. -/
def provenanceExtentMismatch : AuditViolationClass := ⟨⟨"provenanceExtentMismatch"⟩⟩

/-- An access whose declared address is not the address its allocation's placement
gives that offset.

`AccessDescriptor.address` and `AccessDescriptor.range` were unconnected: the range
is an offset into the provenance's root and the address is a separate field, and
nothing compared them even once `AllocationRecord.base` existed to compare against.
Every address in the Spike 1 fixtures contradicted the placement the same fixture
built — a slot at offset 32 of an allocation based at `0x0000` declared `0x1020` —
and six of `Tests/Op/FakeIsa.lean`'s own descriptors named an address belonging to a
different allocation. Nothing complained, because `denialOf` read the base for
nothing and `Grass/Memory/Addressing.lean`'s bridge lemmas had no consumer on the
access path.

Only checked where there is something to check: an unplaced allocation has no
address, and a symbolic space has none either, so both skip. That is the `Option` in
`base` doing its job rather than a hole. -/
def addressDisagreesWithPlacement : AuditViolationClass :=
  ⟨⟨"addressDisagreesWithPlacement"⟩⟩

/-- An allocation placed so that its own bytes wrap the address space.

The clause bounds by `extent.stop`. It bounded by `extent.size` until review placed
an allocation with a non-zero `extent.start` past the wrap point and had its store
admitted at an address inside another live allocation — the same demonstration that
motivated this class, defeated by the one arithmetic difference nothing had stated.

`Grass/Memory/Addressing.lean`'s `addressOf` is `base + offset` in `BitVec 64`,
which reduces mod 2^64, and every bridge lemma in that module takes `FitsAllocation`
as a hypothesis. Nothing checked it. Review placed a sixty-four-byte allocation at
`2 ^ 64 - 16` and had its offset-16 store admitted at declared address **0**, which
is the first byte of a second, unrelated live allocation — the exact non-aliasing
debt `Grass/Memory/Range.lean` records and `Addressing.lean` claims to pay.

Refused rather than approximated: an allocation whose addresses are not well defined
is a placement the model has no account of. -/
def placementWraps : AuditViolationClass := ⟨⟨"placementWraps"⟩⟩

/--
The classes the generic transition relation can emit.

A profile must declare all of these, which is what makes
`AdmittedVocabulary.auditViolationClasses` a consulted registry rather than a
field nothing reads. `StepPolicy` carries the proof.
-/
def emittedByTransition : List AuditViolationClass :=
  [outOfBounds, deadProvenance, permissionDenied, uninitializedRead, misaligned,
   authorityUnavailable, obligationNotAuthorized, wrongAddressSpace,
   machineAnswerIncomplete, provenanceExtentMismatch, addressDisagreesWithPlacement,
   placementWraps, authorityEffectRefused, conflictingAccess]

end AuditViolationClass

/--
One recorded audit violation.

The record names the offending context, provenance, and range rather than the
access descriptor itself, which keeps this module below `Access` and avoids a
dependency cycle. It carries enough to identify what was attempted and where.
-/
structure AuditViolation where
  /-- Which class of violation this is. -/
  class_ : AuditViolationClass
  /-- The context that attempted the access. -/
  context : ContextId
  /-- The provenance the access presented. -/
  provenance : Provenance
  /-- The byte range the access named. -/
  range : ByteRange
deriving DecidableEq, Repr

/--
The append-only ledger of audit violations.

Exposed operations are `empty` and `append`. Nothing removes a record.
-/
structure AuditViolationLedger where
  private mk ::
  private records : List AuditViolation

namespace AuditViolationLedger

instance : DecidableEq AuditViolationLedger := fun a b =>
  if h : a.records = b.records then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by intro eq; exact h (congrArg AuditViolationLedger.records eq))

instance : Repr AuditViolationLedger :=
  ⟨fun ledger prec => reprPrec ledger.records prec⟩

/-- The ledger of a program that has violated nothing. -/
def empty : AuditViolationLedger := ⟨[]⟩

instance : EmptyCollection AuditViolationLedger := ⟨empty⟩

/-- Record one violation. This is the only way a ledger grows, and the only way
one ledger is built from another. -/
def append (ledger : AuditViolationLedger) (violation : AuditViolation) :
    AuditViolationLedger :=
  ⟨ledger.records ++ [violation]⟩

/--
`ledger.IsEmpty` holds when nothing has been recorded.

This is the property `VerifiedProgram` proves. It is stated over the record list
rather than as `ledger = empty` so that it composes with the prefix lemmas below
without unfolding the structure.
-/
def IsEmpty (ledger : AuditViolationLedger) : Prop := ledger.records = []

instance (ledger : AuditViolationLedger) : Decidable ledger.IsEmpty :=
  inferInstanceAs (Decidable (_ = _))

/-- A read-only view of the recorded violations, for diagnostics and reports. -/
def records? (ledger : AuditViolationLedger) : List AuditViolation := ledger.records

/-- How many violations have been recorded. -/
def recordCount (ledger : AuditViolationLedger) : Nat := ledger.records.length

@[simp] theorem isEmpty_empty : empty.IsEmpty := rfl

@[simp] theorem recordCount_empty : empty.recordCount = 0 := rfl

@[simp] theorem records?_append (ledger : AuditViolationLedger) (violation : AuditViolation) :
    (ledger.append violation).records? = ledger.records? ++ [violation] := rfl

@[simp] theorem recordCount_append (ledger : AuditViolationLedger)
    (violation : AuditViolation) :
    (ledger.append violation).recordCount = ledger.recordCount + 1 := by
  simp [recordCount, append]

/-- Emptiness is visible through the read-only view, so a consumer can check it
without the private field. -/
theorem isEmpty_iff_records?_nil (ledger : AuditViolationLedger) :
    ledger.IsEmpty ↔ ledger.records? = [] := Iff.rfl

/-- Appending never produces an empty ledger, by `records?_append`, so recording
something after a violation does not mask it. `Grass.Op.step_extends_violations`
is what makes this hold of a whole execution. -/
@[simp] theorem not_isEmpty_append (ledger : AuditViolationLedger)
    (violation : AuditViolation) : ¬ (ledger.append violation).IsEmpty := by
  simp [IsEmpty, append]

/--
Growth is monotone: every earlier ledger is a prefix of every later one.

This is what lets a whole-execution emptiness claim be checked at the end. If a
violation were recorded at any step, the prefix property carries it forward to
the final ledger, where `IsEmpty` fails.
-/
theorem append_isPrefix (ledger : AuditViolationLedger) (violation : AuditViolation) :
    ledger.records? <+: (ledger.append violation).records? :=
  ⟨[violation], rfl⟩

/--
An empty ledger has an empty history.

Contrapositive of the prefix law, and the form a `VerifiedProgram` proof uses:
from emptiness at the end, nothing was ever recorded.
-/
theorem isEmpty_of_isPrefix_of_isEmpty {earlier later : AuditViolationLedger}
    (prefix_ : earlier.records? <+: later.records?) (h : later.IsEmpty) : earlier.IsEmpty := by
  obtain ⟨suffix, hs⟩ := prefix_
  rw [isEmpty_iff_records?_nil] at h ⊢
  rw [h] at hs
  exact List.append_eq_nil_iff.mp hs |>.1

/--
`earlier.Extends` into `later` when `later` records everything `earlier` did, in
order, and possibly more.

This is the property M2's step relation must preserve, and the one that carries
§8's meaning. It is stated here rather than left implicit because the type alone
cannot enforce it; see the module comment.
-/
def Extends (later earlier : AuditViolationLedger) : Prop :=
  earlier.records? <+: later.records?

theorem Extends.refl (ledger : AuditViolationLedger) : ledger.Extends ledger :=
  List.prefix_refl _

theorem Extends.trans {a b c : AuditViolationLedger}
    (h₁ : b.Extends a) (h₂ : c.Extends b) : c.Extends a :=
  List.IsPrefix.trans h₁ h₂

/-- Appending extends. This is the only ledger-to-ledger operation, so every
transition built from it preserves `Extends` by construction. -/
theorem extends_append (ledger : AuditViolationLedger) (violation : AuditViolation) :
    (ledger.append violation).Extends ledger := append_isPrefix ledger violation

/-- A step that extends a non-empty ledger cannot report emptiness, by
`isEmpty_of_isPrefix_of_isEmpty`. This is the form `VerifiedProgram` uses:
emptiness at the end propagates backwards through every step that preserved
`Extends`. -/
theorem isEmpty_of_extends {later earlier : AuditViolationLedger}
    (h : later.Extends earlier) (hempty : later.IsEmpty) : earlier.IsEmpty :=
  isEmpty_of_isPrefix_of_isEmpty h hempty


end AuditViolationLedger

end Grass.Memory
