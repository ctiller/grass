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

The field list is §3's — identity, holder, range, rights — plus the lender, which
§6's return protocol needs and §3 does not name. Lifetime and conditions are not
modelled: a grant is live while it is in the table, and M3 and M4 own the lifetime
discipline that makes removal correspond to a real return.
-/
structure AuthorityGrant where
  /-- Which kind of authority this is. -/
  kind : GrantKind
  /-- The context that holds it. -/
  holder : ContextId
  /-- The context that issued it, and may reclaim it.

  `docs/MEMORY_MODEL.md` §6: an ABI call profile "lends the exact buffer/slot
  authorities to the environment, retains only disjoint residual frame authority,
  and **consumes the same loan identities to reconstruct local authority on a
  conforming return**". The subject of "consumes" is the caller, and the holder is
  the callee, so a return checked against the holder alone leaves §6's return to a
  party that is not §6's — `MemoryState.returnLoan?_isSome_of_lender` is the
  permission, and `Tests/Memory/Loans.lean`'s `the_lender_may_return_the_loan` is it
  exercised. For an external API agent, which never executes a
  Grass step, nothing in the model could perform the return at all, and
  `Spikes/1_Hello_World` lends a frame slot to `WriteFile` and reads it back after
  the call.

  Not defaulted, and not derivable. A grant does not know who issued it unless it
  is told, and there is no "nobody" context to default to. `MemoryState.returnLoan?`
  accepts a return by the holder or by this context, and by nobody else. §5's arena
  reset and §5.1's reallocation precondition have the same shape. -/
  lender : ContextId
  /-- The storage it is over. -/
  provenance : Provenance
  /-- The bytes it covers, relative to that provenance's root allocation. -/
  range : ByteRange
  /-- What the holder may do with them. -/
  rights : Permission
deriving DecidableEq, Repr

/-! Whether a grant authorizes an access is **not** decided here.

It was: the deleted `Authorizes` function lived in this namespace and matched provenances
with `Provenance.SameStorage`. Whether two allocations name the same bytes is a fact
about the machine state — `MemoryState.aliases` and its transitive closure — and a
pure function on provenances cannot see it, so a holder reaching its own lent bytes
through a declared alias was authorized by nothing while being frozen by its own
loan. `MemoryState.AuthorizedBy` is the test, and it takes the state.
-/

end Grass.Memory
