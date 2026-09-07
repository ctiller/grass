import Grass.Process.Cancellation.Identity
import Grass.Process.Cancellation.Policy

/-!
# The cancellation authoring facet

`docs/DECISIONS.md` decision 134: "`Grass.Process.Cancellation` is likewise a
bounded public facet."

A separate facet from `Grass/Process.lean` rather than part of it, because most
process authors never write a cancellation policy — `Spikes/4_Web_Server` has
one `Cancellation.lean` beside six process modules — and because the two have
genuinely different closures.

## The bound here is the interesting one

`Grass/Process.lean`'s closure excludes cancellation. This one's excludes the
*network*: a cancellation author names points, calls, regions and certificates,
and never a channel, an escrow ledger, a plan or a transition. That is
`docs/PROCESS_SHARDING.md` §4's whole argument for the scope-indexed form made
visible in the import graph — a policy is exact against one scope's discovered
blocking calls, so adding a `Sleep` rebuilds that certificate and the bounded
aggregate path above it, and nothing else.

`Tests/Process/FacadeFixtures.lean` checks both directions: a cancellation
certificate is authorable against this import line alone, and `ProcessPlan`,
`ChannelContract` and `NetworkAssertion` do not resolve through it.

## What is in

* `Identity` — `CancellationMask`, `CancellationPointId`, `BlockingCallId`,
  `AtomicRegionId` and `CancelReason`, the nominal identities a policy is
  written over.
* `Policy` — `CancellationPolicy`, `ProcessScopeSummary`,
  `ScopedCancellationCertificate`, and the composition that makes whole-plan
  cancellation a fold rather than a monolith.

The *liveness* half — that a requested cancellation actually reaches a
disposition under declared premises — is not here and is not anywhere yet. It
needs the transition family, and `docs/PROCESS_IMPLEMENTATION_PLAN.md` schedules
it in M3. An author reading this facet should not conclude that a
`ScopedCancellationCertificate` proves their process stops.

This module declares nothing of its own.
-/
