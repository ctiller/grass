import Grass.Core.Name

/-!
# Resource axes and their policies

`docs/RESOURCES.md` §1 makes "resource axes over which the specification exports a
bound" part of the semantic budget, and [DECISIONS.md] 52 is explicit that metrics
are not memory-specific: "file descriptors, handles, sockets, threads, GPU
resources, pending work, obligations, and products of axes use explicit sum,
maximum, shared-once, or transfer composition laws."

An axis is therefore an open nominal name. The axes defined here are those the
corpus already names, in `docs/SEMANTICS.md`'s `WebServerResources` and in
`docs/RESOURCES.md` §5; a subsystem introduces its own without editing this
module.

The two policies are separate because they answer different questions. Exhaustion
says what the product does when the axis runs out, and is observable at the
boundary — `docs/RESOURCES.md` §1 lists "exhaustion outcomes visible at the
product boundary" as semantic. Lifecycle says how holdings on the axis compose,
which is what stops a shared region being counted twice or an affine transfer
being counted at both ends.
-/

namespace Grass.Resource

open Grass.Core

/--
The name of a resource axis.

Open nominal, so a subsystem may introduce an axis this module has never heard
of. Consumers reject an axis they do not recognize rather than treating it as
unbounded; see `docs/FOUNDATION.md` law 8.
-/
structure ResourceAxisName where
  /-- The axis's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace ResourceAxisName

/-- Bytes resident in memory at one time. -/
def residentBytes : ResourceAxisName := ⟨⟨"residentBytes"⟩⟩

/-- Concurrently admitted connections. -/
def connections : ResourceAxisName := ⟨⟨"connections"⟩⟩

/-- Concurrently admitted protocol streams. -/
def streams : ResourceAxisName := ⟨⟨"streams"⟩⟩

/-- Operating-system sockets. -/
def sockets : ResourceAxisName := ⟨⟨"sockets"⟩⟩

/-- Operating-system handles or descriptors. -/
def handles : ResourceAxisName := ⟨⟨"handles"⟩⟩

/-- Execution contexts, such as worker threads. -/
def threads : ResourceAxisName := ⟨⟨"threads"⟩⟩

/-- Outstanding units of requested work. -/
def requestWork : ResourceAxisName := ⟨⟨"requestWork"⟩⟩

/-- Outstanding obligations. -/
def obligations : ResourceAxisName := ⟨⟨"obligations"⟩⟩

/-- Device or GPU memory. -/
def deviceBytes : ResourceAxisName := ⟨⟨"deviceBytes"⟩⟩

end ResourceAxisName

/--
What the product does when an axis is exhausted.

`docs/RESOURCES.md` §1 makes exhaustion outcomes semantic when they are visible
at the product boundary, so this is a specification-level choice and not a
realization detail. There is no "undefined" case: a specification that does not
say what happens when it runs out has not said what it does.
-/
inductive ResourceExhaustionPolicy (axis : ResourceAxisName) where
  /-- New demands on the axis are refused, with an outcome the specification
  reports. -/
  | reject
  /-- New demands wait until capacity is returned. Requires a real backpressure
  frontier, per `docs/FOUNDATION.md` law 20, not merely an assumption of one. -/
  | backpressure
  /-- Exhaustion is a failure of the whole operation. -/
  | fail
  /-- A policy owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

/--
How holdings on an axis compose.

This is the field that stops double counting. `docs/PROCESS.md`'s resource metric
requires disjoint holdings to add "by default", with "explicit attribution,
phase-exclusion, and transfer witnesses" justifying the other equations; this
type names which of those a given axis uses.
-/
inductive ResourceLifecyclePolicy (axis : ResourceAxisName) where
  /-- Holdings add, and a transfer moves the holding rather than copying it.
  Counting it at both ends would be the double count law 20 forbids. -/
  | affineTransfer
  /-- A shared holding is charged once, to an explicitly attributed owner. -/
  | sharedOnce
  /-- Holdings that cannot coexist are charged at their maximum rather than
  their sum. -/
  | phaseExclusive
  /-- The holding is released when its scope ends. -/
  | scopedRelease
  /-- A composition law owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

end Grass.Resource
