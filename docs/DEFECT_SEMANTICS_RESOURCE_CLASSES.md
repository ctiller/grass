# Defect: the tripartite resource classes in SEMANTICS.md do not elaborate

Filed by: the `c-mem` implementation agent.
Against: the owner of [SEMANTICS.md](SEMANTICS.md).
Status: open. A working shape is implemented and is described below; the
normative document still displays the shape that does not work.

## The defect

[SEMANTICS.md](SEMANTICS.md), "Tripartite specification", displays:

```lean
class WebServerResources (R : Type u) [ResourceModel R]
    extends HasResourceLimit R .residentBytes,
            HasResourceLimit R .connections,
            HasResourceLimit R .sockets,
            HasResourceLimit R .requestWork where
  requestDeadline : R -> Duration
  responseDeadline : R -> Duration
  fixedAfterReady : R -> Prop
```

This cannot be written in Lean 4. Lean deduplicates parent structures by **head
constant**, not by full type, so `HasResourceLimit R .connections` is treated as a
repeat of `HasResourceLimit R .residentBytes` and is dropped. Reproduced against
Lean 4.33.1 with the implemented classes:

```text
warning: Duplicate parent structure `HasResourceLimit`; skipping   (×3)

#print WebServerResources
parents:
  WebServerResources.toHasResourceLimit :
    HasResourceLimit R ResourceAxisName.residentBytes
```

Three of the four axes vanish silently. Under this repository's
`warningAsError = true` — set so that a `sorry` cannot pass the build — the
warning is a hard error, so the declaration does not merely lose axes, it fails
to compile.

## Why it matters beyond a syntax fix

The failure is silent in a way that matters. Without `warningAsError` the class
elaborates, every `HasResourceLimit` projection resolves to the *first* axis, and
a specification that believed it bounded four axes bounds one. A proof about
`sockets` would be discharged by the `residentBytes` limit without anyone
noticing. This is exactly the shape of defect
[FOUNDATION.md](FOUNDATION.md) law 8 exists to prevent, arriving through the
elaborator rather than through a permissive default.

## The working shape

Axis witnesses are held as **fields**, not parents. Implemented in
`Grass/Resource/Algebra.lean` as `ResourceLimit R axis`:

```lean
class WebServerResources (R : Type) [ResourceModel R] where
  residentBytes : ResourceLimit R .residentBytes
  connections : ResourceLimit R .connections
  sockets : ResourceLimit R .sockets
  requestWork : ResourceLimit R .requestWork
  requestDeadline : R → Duration
  responseDeadline : R → Duration
  fixedAfterReady : R → Prop
```

Verified to elaborate with all four axis fields present and distinct.
`HasResourceLimit R axis` is kept for the single-axis case, where instance
resolution is the convenient thing and the deduplication problem does not arise.

An axis-indexed method — `limit : (axis : ResourceAxisName) → …` with a proof of
membership in a declared axis set — is the other workable shape. It trades
instance-resolution convenience for uniformity, and is worth considering if the
axis family becomes large or dynamic.

## Requested disposition

Update the displayed class in [SEMANTICS.md](SEMANTICS.md) to a shape that
elaborates. This plan does not edit that document, because
[README.md](README.md) gives it a narrower owner and a normative interface change
is not a tier-four decision.

## A second, smaller finding in the same area

[SEMANTICS.md](SEMANTICS.md) shows the law bundle as
`OrderedPartialCommutativeResourceLaws combine le`, while
[PROCESS.md](PROCESS.md) shows `OrderedCommutativeResourceAlgebra (Value axis)
(combine axis) (zero axis) (le axis)` — a different name and a different arity for
what is evidently one concept, and only the second carries the identity element
its own `ResourceMetric.empty` field requires. The implementation unifies them and
records the reconciliation in `Grass/Resource/Algebra.lean`.

The unified bundle also carries a second binary operation. `combine` is parallel
composition and is cancellative; `alternative` is peak demand across mutually
exclusive branches and is idempotent. Neither document distinguishes them, and
collapsing them gets one case wrong in either direction: `max` as a parallel
composition undercounts simultaneously held sockets, while `+` as a temporal
aggregation makes an exclusive-branch peak bound artificially additive. See
`Tests/Resource/CompositionSplit.lean`, which proves no law bundle can use either
operator for the other role.
