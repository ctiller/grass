/-!
# Observation segments and run traces

`docs/PROCESS.md` §2:

> The final argument of `Step` is the finite observation segment emitted by that
> exact transition. A process run concatenates these segments. Processes do not
> carry their complete observation history in local state, and revisiting or
> rendering a state cannot duplicate an observation.

That paragraph is the whole design. A segment is finite and belongs to one
transition; the run's trace is the concatenation, and it is *derived* rather
than stored, so no state can carry a history and no re-render can duplicate an
entry.

`Segmented` keeps the concatenation and its decomposition together. It is what
`ProcessRun.observationCausality` in §4 needs: that theorem is not an
application proof obligation but the generic fact that every occurrence in the
flattened trace came from exactly one emitting segment, retained so that later
weaving, flattening, and machine simulation can still say which transition
produced a given observed byte.

The word *occurrence* is load-bearing. A trace may contain the same observation
value many times, so a statement about values would not identify a single
emission and would not survive projection. `origin` below is therefore stated
over a position: it takes the split of the trace at an occurrence and returns
the matching split of the segments and of the emitting segment, and
`origin_unique` says that split is the only one.

## Not part of run state

An earlier draft put a `Segmented` inside `ProcessRunState`. That was wrong:
`segments.length` is the number of transitions taken, and whether a transition
emitted `[a, b]` or two transitions emitted `[a]` and `[b]` is a batching fact
that `docs/FOUNDATION.md` law 18 makes a replaceable realization choice. A run
*state* carries the flat trace; the segmentation is a property of the run.

## Ownership note

`Trace` is `docs/SEMANTICS.md`'s word. `docs/PROCESS_IMPLEMENTATION_PLAN.md`
§2.2 records the decision to spell it as a `List` alias here so that the arrival
of the semantics layer replaces one declaration rather than every use site.
`Segmented` and its origin function are process-owned: they are about the
`Step`-segment structure, which is this document's.
-/

namespace Grass.Process

universe u

/-- The finite observation segment emitted by one transition. -/
abbrev ObservationSegment (Observation : Type u) := List Observation

/--
The observation history of a run: the concatenation of its segments.

Alias rather than a new type, pending `Grass.Semantics.Trace`.
-/
abbrev Trace (Observation : Type u) := List Observation

/--
A trace together with the segmentation that produced it.

`flat` is redundant with `segments`, and `flatExact` says so. It is a field
rather than a definition because the flattened trace is what the observation
filter and the machine-level committed trace are compared against, and it should
not be recomputed at every use.
-/
structure Segmented (Observation : Type u) where
  /-- One entry per emitting transition, in transition order. -/
  segments : List (ObservationSegment Observation)
  /-- The concatenated history. -/
  flat : Trace Observation
  /-- The history is exactly the concatenation; nothing is added or dropped. -/
  flatExact : flat = segments.flatten

namespace Segmented

variable {Observation : Type u}

/-- The empty history: no transition has emitted yet. -/
def empty : Segmented Observation where
  segments := []
  flat := []
  flatExact := rfl

instance : EmptyCollection (Segmented Observation) := ⟨empty⟩

/-- Append the segment emitted by one further transition. -/
def emit (history : Segmented Observation)
    (segment : ObservationSegment Observation) : Segmented Observation where
  segments := history.segments ++ [segment]
  flat := history.flat ++ segment
  flatExact := by
    simp [history.flatExact, List.flatten_append]

@[simp] theorem empty_segments :
    (empty : Segmented Observation).segments = [] := rfl

@[simp] theorem empty_flat : (empty : Segmented Observation).flat = [] := rfl

@[simp] theorem emit_segments (history : Segmented Observation)
    (segment : ObservationSegment Observation) :
    (history.emit segment).segments = history.segments ++ [segment] := rfl

@[simp] theorem emit_flat (history : Segmented Observation)
    (segment : ObservationSegment Observation) :
    (history.emit segment).flat = history.flat ++ segment := rfl

/--
Emitting the empty segment is a silent transition: it changes the history's
segment list but not the trace.

`docs/PROCESS.md` §2 calls these "ordinary silent/stuttering transitions". A
silent transition still gets a segment entry, because `segments` is a record of
what each transition emitted and a transition that emitted nothing emitted the
empty list. That the entry is invisible in `flat` is the point: it is why the
segmentation must not reach a consumer that could branch on it.
-/
@[simp] theorem emit_nil_flat (history : Segmented Observation) :
    (history.emit []).flat = history.flat := by simp

/--
The number of observations is the sum of the segment lengths: a transition
cannot emit an observation that fails to appear in the trace, and the trace
cannot contain one no transition emitted.
-/
theorem flat_length (history : Segmented Observation) :
    history.flat.length = (history.segments.map List.length).sum := by
  rw [history.flatExact, List.length_flatten]

/--
The origin of the observation occurrence at a given position.

`split` locates one occurrence: the trace is `before`, then this occurrence,
then `after`. The conclusion decomposes the segment list at the emitting
segment, and that segment at the occurrence, and states how the surrounding
trace is built from the two.

This is the retained form of `ProcessRun.observationCausality` in
`docs/PROCESS.md` §4. It is a decomposition rather than an index function
because that is the form later projections consume: an observation filter that
keeps a suffix, or a weave that interleaves two histories, needs the
surrounding context, not an integer.
-/
private theorem origin_flatten {Observation : Type u}
    {segments : List (ObservationSegment Observation)} {observation : Observation}
    {before after : Trace Observation}
    (split : segments.flatten = before ++ observation :: after) :
    ∃ segmentsBefore segment segmentsAfter segmentBefore segmentAfter,
      segments = segmentsBefore ++ segment :: segmentsAfter ∧
      segment = segmentBefore ++ observation :: segmentAfter ∧
      before = segmentsBefore.flatten ++ segmentBefore ∧
      after = segmentAfter ++ segmentsAfter.flatten := by
  induction segments generalizing before with
  | nil => simp at split
  | cons head tail ih =>
    rw [List.flatten_cons] at split
    rcases List.append_eq_append_iff.mp split with
      ⟨middle, beforeEq, tailEq⟩ | ⟨middle, headEq, obsEq⟩
    · -- The occurrence is in a later segment; `head` is entirely in `before`.
      obtain ⟨segmentsBefore, segment, segmentsAfter, segmentBefore, segmentAfter,
        segmentsSplit, segmentSplit, beforeExact, afterExact⟩ := ih tailEq
      refine ⟨head :: segmentsBefore, segment, segmentsAfter, segmentBefore,
        segmentAfter, by rw [segmentsSplit]; rfl, segmentSplit, ?_, afterExact⟩
      rw [beforeEq, beforeExact, List.flatten_cons, List.append_assoc]
    · match middle, headEq, obsEq with
      | [], headEq, obsEq =>
        -- `head` ends exactly at the occurrence, which is in a later segment.
        obtain ⟨segmentsBefore, segment, segmentsAfter, segmentBefore, segmentAfter,
          segmentsSplit, segmentSplit, beforeExact, afterExact⟩ :=
          ih (before := []) (by simpa using obsEq.symm)
        refine ⟨head :: segmentsBefore, segment, segmentsAfter, segmentBefore,
          segmentAfter, by rw [segmentsSplit]; rfl, segmentSplit, ?_, afterExact⟩
        rw [List.flatten_cons, List.append_assoc, ← beforeExact]
        simpa using headEq.symm
      | occurrence :: rest, headEq, obsEq =>
        -- The occurrence is inside `head`.
        obtain ⟨sameObservation, afterEq⟩ := List.cons.inj obsEq
        exact ⟨[], head, tail, before, rest,
          rfl, by rw [headEq, sameObservation], rfl, afterEq⟩

/--
The origin of the observation occurrence at a given position.

`split` locates one occurrence: the trace is `before`, then this occurrence,
then `after`. The conclusion decomposes the segment list at the emitting
segment, and that segment at the occurrence, and states how the surrounding
trace is built from the two.

This is the retained form of `ProcessRun.observationCausality` in
`docs/PROCESS.md` §4. It is a decomposition rather than an index function
because that is the form later projections consume: an observation filter that
keeps a suffix, or a weave that interleaves two histories, needs the surrounding
context, not an integer. `origin_unique` below supplies the "exactly one" half.
-/
theorem origin (history : Segmented Observation) {observation : Observation}
    {before after : Trace Observation}
    (split : history.flat = before ++ observation :: after) :
    ∃ segmentsBefore segment segmentsAfter segmentBefore segmentAfter,
      history.segments = segmentsBefore ++ segment :: segmentsAfter ∧
      segment = segmentBefore ++ observation :: segmentAfter ∧
      before = segmentsBefore.flatten ++ segmentBefore ∧
      after = segmentAfter ++ segmentsAfter.flatten :=
  origin_flatten (history.flatExact ▸ split)

private theorem segments_prefix_flatten_le
    {Observation : Type u}
    {segments leftBefore leftAfter rightBefore rightAfter :
      List (ObservationSegment Observation)}
    {leftSegment rightSegment : ObservationSegment Observation}
    (leftSplit : segments = leftBefore ++ leftSegment :: leftAfter)
    (rightSplit : segments = rightBefore ++ rightSegment :: rightAfter)
    (shorter : leftBefore.length < rightBefore.length) :
    leftBefore.flatten.length + leftSegment.length ≤ rightBefore.flatten.length := by
  have joined : leftBefore ++ leftSegment :: leftAfter =
      rightBefore ++ rightSegment :: rightAfter := leftSplit ▸ rightSplit
  rcases List.append_eq_append_iff.mp joined with
    ⟨middle, rightEq, leftEq⟩ | ⟨middle, leftEq, _⟩
  · match middle, rightEq, leftEq with
    | [], rightEq, _ =>
      exact absurd (by simpa using congrArg List.length rightEq) (by omega)
    | first :: rest, rightEq, leftEq =>
      have headEq : first = leftSegment := (List.cons.inj leftEq).1.symm
      subst headEq
      rw [rightEq, List.flatten_append, List.length_append, List.flatten_cons,
        List.length_append]
      omega
  · exact absurd (by simpa using congrArg List.length leftEq) (by omega)

/--
The decomposition is the only one: an occurrence has exactly one emitting
segment and exactly one position within it.

Uniqueness is what `docs/PROCESS.md` §4 asks for, and it is what an existence
statement over observation *values* could not give, since a trace may contain
the same value many times. The argument is about lengths: a decomposition puts
the occurrence strictly inside its emitting segment, so `before` is at least as
long as everything before that segment and strictly shorter than everything
through it. Two decompositions at different segment indices would put
`before.length` on both sides of the same bound.
-/
theorem origin_unique (history : Segmented Observation)
    {observation : Observation} {before : Trace Observation}
    {leftSegmentsBefore leftSegmentsAfter rightSegmentsBefore rightSegmentsAfter :
      List (ObservationSegment Observation)}
    {leftSegment rightSegment : ObservationSegment Observation}
    {leftSegmentBefore leftSegmentAfter rightSegmentBefore rightSegmentAfter :
      Trace Observation}
    (leftSplit : history.segments =
      leftSegmentsBefore ++ leftSegment :: leftSegmentsAfter)
    (leftInner : leftSegment = leftSegmentBefore ++ observation :: leftSegmentAfter)
    (leftBefore : before = leftSegmentsBefore.flatten ++ leftSegmentBefore)
    (rightSplit : history.segments =
      rightSegmentsBefore ++ rightSegment :: rightSegmentsAfter)
    (rightInner : rightSegment = rightSegmentBefore ++ observation :: rightSegmentAfter)
    (rightBefore : before = rightSegmentsBefore.flatten ++ rightSegmentBefore) :
    leftSegmentsBefore = rightSegmentsBefore ∧ leftSegment = rightSegment ∧
      leftSegmentsAfter = rightSegmentsAfter := by
  -- Each decomposition bounds `before.length` between the flattened prefix and
  -- the end of its own emitting segment.
  have leftBound : before.length < leftSegmentsBefore.flatten.length + leftSegment.length := by
    rw [leftBefore, List.length_append, leftInner, List.length_append]
    simp
  have rightBound : before.length < rightSegmentsBefore.flatten.length + rightSegment.length := by
    rw [rightBefore, List.length_append, rightInner, List.length_append]
    simp
  have leftLower : leftSegmentsBefore.flatten.length ≤ before.length := by
    rw [leftBefore, List.length_append]; omega
  have rightLower : rightSegmentsBefore.flatten.length ≤ before.length := by
    rw [rightBefore, List.length_append]; omega
  have sameCount : leftSegmentsBefore.length = rightSegmentsBefore.length := by
    rcases Nat.lt_trichotomy leftSegmentsBefore.length rightSegmentsBefore.length with
      shorter | equal | longer
    · exact absurd (segments_prefix_flatten_le leftSplit rightSplit shorter) (by omega)
    · exact equal
    · exact absurd (segments_prefix_flatten_le rightSplit leftSplit longer) (by omega)
  obtain ⟨segmentsEq, restEq⟩ :=
    List.append_inj (leftSplit ▸ rightSplit :
      leftSegmentsBefore ++ leftSegment :: leftSegmentsAfter =
        rightSegmentsBefore ++ rightSegment :: rightSegmentsAfter) sameCount
  exact ⟨segmentsEq, (List.cons.inj restEq).1, (List.cons.inj restEq).2⟩

end Segmented

end Grass.Process
