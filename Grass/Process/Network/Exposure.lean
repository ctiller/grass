import Grass.Process.Network.Boundary

/-!
# How a root protocol exposes a driver boundary

`docs/PROCESS.md` §3 gives `ProcessGraph` a field
`rootBoundary : ProtocolExposesBoundary (registry.protocol (protocolKey root)) boundary`,
and §5 requires the driver to expose *exactly* that boundary. This module is
that relation.

## Why it is four partial maps and not an equality

The tempting declaration is that the root protocol's interface types simply
*are* the boundary's. They are not, and the difference is the whole point of the
boundary existing:

- **Demands are exported selectively.** §3: "`ProcessPlan` carries a partial
  `boundaryProjection` from selected root-local occurrences to `DriverBoundary`
  occurrences; nested and flattened internal demands remain private." A root
  that asks a child for a parsed header is not asking the driver for anything.
- **Observations are filtered.** §4 and §6 both turn on an observation filter:
  "Physical effects hidden from the product projection remain in the audit trace
  and retain the same origin relation."
- **Events are delivered totally in the other direction.** The driver must be
  able to deliver every event it can produce, or `docs/FOUNDATION.md` law 5 is
  violated by construction — there would be entropy the process has no
  transition for.

So the shape is: events map *from* the boundary *into* the protocol and totally;
demands and observations map *from* the protocol *out to* the boundary and
partially; and a result of an exported demand maps back in.

## What this module does not do

It relates two interfaces. It says nothing about whether the protocol's
*behavior* over those interfaces refines anything, and nothing about occurrence
identity — a `Demand` here is still a value, never a pending occurrence.
Exactness of the occurrence-level projection is `ProcessPlanRealizes`, and it is
M4 work.
-/

namespace Grass.Process

universe u w

/--
The interface half of "this protocol can sit at this driver boundary".

Every field is a map between the two vocabularies, with the direction and
totality forced by the module note.
-/
structure ProtocolExposesBoundary (p : ProcessSpec.{u, w})
    (boundary : DriverBoundary.{u}) where
  /--
  Every event the driver can deliver is an event the protocol receives.

  Total, and in this direction: `docs/FOUNDATION.md` law 5 requires every
  admitted external result to be handled, and a partial map here would leave
  driver-producible entropy with no corresponding process event.
  -/
  deliver : boundary.ExternalEvent → p.ExternalEvent
  /--
  Which of the protocol's demands are exported to the driver.

  Partial. A demand answered inside the network — by a child, a flattened
  subsystem, or another process — is not a boundary demand, and
  `docs/PROCESS.md` §3 requires those to stay private.
  -/
  exportDemand : p.Demand → Option boundary.Demand
  /--
  A boundary result for an exported demand is a result for that demand.

  Indexed by the export equation, so a result can only be routed to the demand
  that actually produced it. `docs/PROCESS.md` §5: a driver "may not fabricate a
  result [or] attach one result to another occurrence."
  -/
  accept : ∀ {demand : p.Demand} {exported : boundary.Demand},
    exportDemand demand = some exported → boundary.Result exported → p.Result demand
  /--
  The observation filter: which of the protocol's observations are visible at
  the boundary.

  Partial. `docs/PROCESS.md` §6 lets a commit be hidden from the product
  projection while remaining in the audit trace, and §4 requires the hidden ones
  to keep their origin relation.
  -/
  observe : p.Observation → Option boundary.Observation

namespace ProtocolExposesBoundary

variable {p : ProcessSpec.{u, w}} {boundary : DriverBoundary.{u}}

/-- A demand this protocol answers internally rather than at the boundary. -/
def Private (exposure : ProtocolExposesBoundary p boundary)
    (demand : p.Demand) : Prop :=
  exposure.exportDemand demand = none

/-- An observation the boundary does not see. -/
def Hidden (exposure : ProtocolExposesBoundary p boundary)
    (observation : p.Observation) : Prop :=
  exposure.observe observation = none

/--
The boundary trace a protocol trace projects to: the visible observations, in
order, with the hidden ones dropped.

Order-preserving and prefix-monotone, which is what makes an acceptance relation
stated over the boundary usable on a process prefix.
-/
def project (exposure : ProtocolExposesBoundary p boundary)
    (trace : Trace p.Observation) : Trace boundary.Observation :=
  trace.filterMap exposure.observe

@[simp] theorem project_nil (exposure : ProtocolExposesBoundary p boundary) :
    exposure.project [] = [] := rfl

@[simp] theorem project_append (exposure : ProtocolExposesBoundary p boundary)
    (left right : Trace p.Observation) :
    exposure.project (left ++ right) =
      exposure.project left ++ exposure.project right :=
  List.filterMap_append

/--
Projection is monotone on prefixes: extending a trace extends its projection.

This is what lets `docs/PROCESS.md` §7's "universal prefix safety" be checked at
the boundary. Without it a boundary acceptance relation could be satisfied by a
prefix and violated by an extension for reasons invisible at the boundary.
-/
theorem project_extends (exposure : ProtocolExposesBoundary p boundary)
    (trace : Trace p.Observation) (extension : Trace p.Observation) :
    ∃ appended, exposure.project (trace ++ extension) =
      exposure.project trace ++ appended :=
  ⟨exposure.project extension, exposure.project_append trace extension⟩

/-- A hidden observation contributes nothing to the boundary trace. -/
@[simp] theorem project_cons_hidden (exposure : ProtocolExposesBoundary p boundary)
    {observation : p.Observation} (hidden : exposure.Hidden observation)
    (rest : Trace p.Observation) :
    exposure.project (observation :: rest) = exposure.project rest := by
  unfold Hidden at hidden
  simp [project, hidden]

/-- A visible observation contributes exactly itself. -/
theorem project_cons_visible (exposure : ProtocolExposesBoundary p boundary)
    {observation : p.Observation} {visible : boundary.Observation}
    (seen : exposure.observe observation = some visible)
    (rest : Trace p.Observation) :
    exposure.project (observation :: rest) = visible :: exposure.project rest := by
  simp [project, seen]


end ProtocolExposesBoundary

end Grass.Process
