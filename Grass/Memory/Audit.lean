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

The append-only property is enforced structurally: the constructor and the record
list are `private`, so outside this module the only way to obtain a ledger is
`empty` or `append`. There is no erase, no filter, no mask, and no way to build a
shorter ledger from a longer one — not by convention, but because
`AuditViolationLedger.mk` and the `records` field do not exist to a consumer.

That is worth stating plainly, because an earlier version of this module carried
this same paragraph while leaving the constructor public, which made it false:
`⟨dirty.records.drop 1⟩` laundered a ledger in one line, and `VerifiedProgram`'s
emptiness proof would then have been a claim about a value any caller could
manufacture.

`append_isPrefix` makes growth monotone, so a violation recorded at any point in
an execution is present in every later ledger, which is what makes `IsEmpty` at
the end a statement about the whole run.

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

/-- Appending never produces an empty ledger. A violation cannot be masked by
recording something after it. -/
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

end AuditViolationLedger

end Grass.Memory
