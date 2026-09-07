import Grass.Core.Context
import Grass.Core.Uid
import Grass.Memory.Provenance
import Grass.Memory.Rights

/-!
# Authority grants

`docs/MEMORY_MODEL.md` §3: "Every loan has a unique identity. The authoritative
state is a finite map from loan identity to holder, range, rights, lifetime, and
conditions. Counts are derived caches only."

`AuthorityGrant` is that shape, one milestone early and deliberately general. It
is **not** the loan model of M3 or the frame model of M4. Those milestones own
split and join, frozen owner fragments, exclusivity-iff-empty, pinning and
rebasing, and the call-framing theorem; none of that is here.

What is here exists to answer one question that has to be answered before the
operation seam can be called anything but provisional: **can a new kind of
authority evidence be added without redesigning operation packaging?** A grant
table plus `Grass/Op/Step.lean`'s `AuthorityProvider` is the smallest thing that
can be checked against a real access, and `Tests/Op/FakeIsa.lean` adds two
distinct authority kinds over it — a loan and a stack frame — without touching
`AccessDescriptor`, `OperationFacets`, `HasOperationFacets`, `SomeOperation`, or
the shape of `step`.

An access does not name the grant it relies on. `docs/MEMORY_MODEL.md` §3 makes
returning a loan consume "that exact identity", which is a ledger operation and
already goes through `LedgerDelta` with its typed `ProtocolAuthority`; ordinary
use only requires that *some* live grant covers what the access does. Naming one
would have put a field on the descriptor, and the point of this exercise is that
the descriptor does not change.
-/

namespace Grass.Memory

open Grass.Core

/-- Phantom tag for authority-grant identities. -/
inductive GrantTag : Type

/--
The generative identity of one grant.

`docs/MEMORY_MODEL.md` §3 requires loan identities to be unique and counts to be
derived caches of the map. A `Uid` cannot be reissued, so returning one grant
consumes that grant and not another that happens to look alike.
-/
abbrev GrantId := Uid GrantTag

/-- What kind of authority a grant conveys. Open nominal, so a profile adds its
own without editing this module. -/
structure GrantKind where
  /-- The kind's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace GrantKind

/-- A borrow of authority over bytes the lender retains. -/
def loan : GrantKind := ⟨⟨"loan"⟩⟩

/-- A live call frame's authority over its own stack storage. -/
def frame : GrantKind := ⟨⟨"frame"⟩⟩

/-- A pin, which `docs/MEMORY_MODEL.md` §5.1 uses to stop reallocation while
interior pointers exist. Named here for the vocabulary only; M6 owns the
mechanism, and nothing in this module enforces it. -/
def pin : GrantKind := ⟨⟨"pin"⟩⟩

end GrantKind

/--
One grant of authority.

The field list is §3's: identity, holder, range, rights. Lifetime and conditions
are not modelled — a grant is live while it is in the table, and M3 and M4 own
the lifetime discipline that makes removal correspond to a real return.
-/
structure AuthorityGrant where
  /-- Which kind of authority this is. -/
  kind : GrantKind
  /-- The context that holds it. -/
  holder : ContextId
  /-- The storage it is over. -/
  provenance : Provenance
  /-- The bytes it covers, relative to that provenance's root allocation. -/
  range : ByteRange
  /-- What the holder may do with them. -/
  rights : Permission
deriving DecidableEq, Repr

namespace AuthorityGrant

/--
`grant.Authorizes context provenance range intent` holds when this grant lets
`context` perform that access.

Same storage, covering range, sufficient rights, and the holder is the context
performing the access. `Provenance.SameStorage` rather than provenance equality,
because a grant over an object authorizes access to a field of it — the path
descends, the storage does not change.
-/
def Authorizes (grant : AuthorityGrant) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  grant.holder = context ∧
  grant.provenance.SameStorage provenance ∧
  grant.range.Contains range ∧
  grant.rights.Permits intent

instance (grant : AuthorityGrant) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (grant.Authorizes context provenance range intent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A grant held by one context authorizes nothing for another. Authority is not
ambient: `docs/FOUNDATION.md` law 6 forbids ambient provider choice, and the same
reading applies to authority a context did not receive. -/
theorem not_authorizes_of_other_holder {grant : AuthorityGrant} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (h : grant.holder ≠ context) :
    ¬ grant.Authorizes context provenance range intent := fun ha => h ha.1

/-- A grant over one allocation authorizes nothing over another, however their
offsets compare (`docs/MEMORY_MODEL.md` §7.5). -/
theorem not_authorizes_of_other_storage {grant : AuthorityGrant} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (h : ¬ grant.provenance.SameStorage provenance) :
    ¬ grant.Authorizes context provenance range intent := fun ha => h ha.2.1

/-- A read-only grant does not authorize a write. -/
theorem not_authorizes_of_insufficient_rights {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent} (h : ¬ grant.rights.Permits intent) :
    ¬ grant.Authorizes context provenance range intent := fun ha => h ha.2.2.2

end AuthorityGrant

end Grass.Memory
