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

`docs/PROCESS.md` §2 calls these "ordinary silent/stuttering transitions". They
keep a segment entry because the origin of a *later* observation is stated by
transition index, and dropping silent transitions would renumber it.
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
Every observation occurrence in the flattened trace has a segment of origin, and
the trace is exactly the segments before it, that segment, and the segments
after it.

This is the retained form of `ProcessRun.observationCausality` in
`docs/PROCESS.md` §4. It is stated as an existence of a decomposition rather
than as an index function because that is the form later projections consume:
an observation filter that keeps a suffix, or a weave that interleaves two
histories, needs the surrounding context, not an integer.
-/
theorem origin (history : Segmented Observation)
    {observation : Observation} (occurs : observation ∈ history.flat) :
    ∃ before segment after,
      history.segments = before ++ segment :: after ∧
      observation ∈ segment := by
  rw [history.flatExact, List.mem_flatten] at occurs
  obtain ⟨segment, segmentMember, member⟩ := occurs
  obtain ⟨before, after, split⟩ := List.append_of_mem segmentMember
  exact ⟨before, segment, after, split, member⟩

end Segmented

end Grass.Process
