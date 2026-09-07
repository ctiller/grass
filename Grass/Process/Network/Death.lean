/-!
# Why a process stopped existing

One enumeration, in its own module because two unrelated layers need it and
neither should have to import the other to get it.
`Grass/Process/Network/Instance.lean` tags a dead incarnation with it;
`Grass/Process/Network/Child.lean` routes it to a parent. `Child.lean` is
parameterized by a `ProcessSpec` and a `ProtocolRegistry` and mentions no
topology at all, so making it import the instance layer for a three-constructor
enum would tie it to `ProcessTopologyCore`, `ProcessGraph` and the nominal
machinery it has no other use for.

This module imports nothing.

## Why the reason is carried at all

`docs/PROCESS.md` §3 is emphatic that a network records what ended a process
rather than merely that it ended: the child binding must classify "every child
terminal result, failure, interruption, cancellation acknowledgement/race,
fault, violation, and death". Death is the one ending that no protocol event
describes — a terminated process's state is terminal, a faulted one raised a
fault, but a process that stopped existing produced nothing at all. If the tag
does not say why, nothing does.
-/

namespace Grass.Process

/--
Why a process stopped existing without finishing its protocol.

Previously `ChildDeathReason` in `Grass/Process/Network/Child.lean`. The name
was wrong: none of the three reasons is about being a child, and
`docs/PROCESS.md` §3 gives `senderDeath` and `receiverDeath` to processes that
may be roots.
-/
inductive ProcessDeathReason
  /-- Its parent died, and it was not detached. -/
  | parentDied
  /-- A supervisor stopped it. -/
  | supervised
  /-- The provider realizing it disappeared. -/
  | providerLost
  deriving DecidableEq, Repr

end Grass.Process
