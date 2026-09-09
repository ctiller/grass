import Grass.Console.CapturedProjection
import Grass.Refinement.Console.WriteFileProjection
import Grass.Platform.Win32.WriteFileNonresponse

/-! Coherent finite projection from an aligned, reached caller history.
The caller-to-handoff relation is selected once and remains an explicit machine
realization obligation. Provider histories retain every action and publication;
the upper history retains its existing choices and each positive publication.
Zero provider publications stutter locally, without authorizing silent caller
divergence, physical nonresponse, or coverage of all allowed behaviors.
-/

namespace Grass.Refinement.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32.WriteFile

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}

/-- A reached upper frontier of the exact captured projection and the actual
call's remaining bytes. Its history is supplied, never reconstructed from a cut. -/
structure Start (projection : CapturedTargetProjection spec Status)
    (record : CallProtocol.Pending Request) where
  upper : projection.system.History
  cut : OutputCut projection.target.payload
  located : upper.state = .pending cut
  suffix : record.request.bytes = cut.remaining

variable {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}

/-- The selected relation binds the reached caller to the actual provider
handoff. No default relation or realization proof is supplied by lowering. -/
def HandoffRelation (projection : CapturedTargetProjection spec Status) :=
  Realization → CallProtocol.State Request → (call : CallProtocol.CallId) →
    (record : CallProtocol.Pending Request) → projection.system.History →
    (state : CallProtocol.State Request) → Prefix state call record → Prop

/-- Follow the original root, not an independently reconstructed handoff. -/
def RootAligned (relation : HandoffRelation projection)
    (upper : projection.system.History) {state : CallProtocol.State Request}
    {frontier : Prefix state call record} : History realization initial call record frontier → Prop
  | .handoff frontier _ _ _ _ => relation realization initial call record upper _ frontier
  | .step previous _ _ _ => RootAligned relation upper previous

private abbrev Located (projection : CapturedTargetProjection spec Status)
    (cut : OutputCut projection.target.payload) :=
  { upper : projection.system.History // upper.state = .pending cut }

private def positiveUpper {before after : CallProtocol.State Request}
    {pre : Prefix before call record} {post : Prefix after call record}
    (start : Start projection record) (action : Action) (output : Vec Byte)
    (step : CommittedStep realization pre post action output)
    (upper : Located projection (WriteFileProjection.cut start.cut start.suffix pre))
    (positive : pre.accepted < post.accepted) :
    Located projection (WriteFileProjection.cut start.cut start.suffix post) := by
    refine ⟨upper.val.append (Grass.RelationalSystem.Path.snoc (system := projection.system) .nil
      (.reply (WriteFileProjection.cut start.cut start.suffix pre)
        (.advance (WriteFileProjection.cut start.cut start.suffix post) (by
          change start.cut.offset + pre.accepted < start.cut.offset + post.accepted
          omega)))
      (.emitted output) (.pending (WriteFileProjection.cut start.cut start.suffix post)) () ?_), rfl⟩
    exact ⟨upper.property, congrArg Behavior.Event.emitted
      (WriteFileProjection.publication_between start.cut start.suffix step), rfl⟩

private def advanceUpper {before after : CallProtocol.State Request}
    {pre : Prefix before call record} {post : Prefix after call record}
    (start : Start projection record) (action : Action) (output : Vec Byte)
    (step : CommittedStep realization pre post action output)
    (upper : Located projection (WriteFileProjection.cut start.cut start.suffix pre)) :
    Located projection (WriteFileProjection.cut start.cut start.suffix post) := by
  by_cases positive : pre.accepted < post.accepted
  · exact positiveUpper start action output step upper positive
  · have same : post.accepted = pre.accepted := by
      have monotone := step.publication.monotone
      omega
    refine ⟨upper.val, ?_⟩
    exact upper.property.trans (congrArg Behavior.State.pending
      (WriteFileProjection.zero_step start.cut start.suffix step same).1.symm)

private def fold (start : Start projection record) {state : CallProtocol.State Request}
    {frontier : Prefix state call record}
    (history : History realization initial call record frontier) :
    Located projection (WriteFileProjection.cut start.cut start.suffix frontier) :=
  match history with
  | .handoff frontier _ _ _ zero =>
    ⟨start.upper, start.located.trans (congrArg Behavior.State.pending (by
      apply OutputCut.ext
      simp [WriteFileProjection.cut, zero]))⟩
  | .step previous action output committed =>
    advanceUpper start action output committed (fold start previous)

/-- `Aligned` retains the complete provider history and fixed relation;
`Aligned.extend_start` preserves its original captured caller prefix. -/
structure Aligned (relation : HandoffRelation projection)
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    (history : History realization initial call record frontier) where
  start : Start projection record
  aligned : RootAligned relation start.upper history

namespace Aligned

variable {relation : HandoffRelation projection}
  {state : CallProtocol.State Request} {frontier : Prefix state call record}
  {history : History realization initial call record frontier}

def upper (aligned : Aligned relation history) : projection.system.History :=
  (fold aligned.start history).val

def endpoint (aligned : Aligned relation history) : OutputCut projection.target.payload :=
  WriteFileProjection.cut aligned.start.cut aligned.start.suffix frontier

theorem upper_located (aligned : Aligned relation history) :
    aligned.upper.state = .pending aligned.endpoint := (fold aligned.start history).property

/-- Full acceptance of this suffix reaches the complete payload without return. -/
theorem endpoint_full (aligned : Aligned relation history)
    (full : frontier.accepted = record.request.bytes.length) :
    aligned.endpoint = OutputCut.full projection.target.payload := by
  apply OutputCut.ext
  change aligned.start.cut.offset + frontier.accepted = projection.target.payload.length
  have lengths := congrArg Vec.length aligned.start.suffix
  simp only [OutputCut.remaining, Vec.length_drop] at lengths
  have bounded := aligned.start.cut.bounded
  omega

/-- `extend` retains the original alignment witness; `extend_start` exposes
preservation of the caller history. -/
def extend (aligned : Aligned relation history) {after : CallProtocol.State Request}
    {post : Prefix after call record} (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output) :
    Aligned relation (.step history action output step) := ⟨aligned.start, aligned.aligned⟩

private theorem history_transport
    (other : Σ otherState, Prefix otherState call record)
    (pointEq : other = ⟨state, frontier⟩)
    (otherHistory : History realization initial call record other.2)
    (same : HEq otherHistory history) (start : Start projection record) :
    RootAligned relation start.upper otherHistory = RootAligned relation start.upper history ∧
      (fold start otherHistory).val = (fold start history).val := by
  cases pointEq
  cases eq_of_heq same
  exact ⟨rfl, rfl⟩

/-- Carry the original caller alignment along the actual provider stream. -/
def alignedAt (aligned : Aligned relation history) (continuation : InfiniteContinuation history) :
    (n : Nat) → Aligned relation (continuation.historyAt n)
  | 0 => by
    refine ⟨aligned.start, ?_⟩
    rw [(history_transport (continuation.point 0) continuation.start
      (continuation.historyAt 0) continuation.historyAt_zero aligned.start).1]
    exact aligned.aligned
  | n + 1 => (aligned.alignedAt continuation n).extend
      (continuation.action n) (continuation.output n) (continuation.committed n)

theorem alignedAt_start (aligned : Aligned relation history)
    (continuation : InfiniteContinuation history) (n : Nat) :
    (aligned.alignedAt continuation n).start = aligned.start := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem alignedAt_zero_upper (aligned : Aligned relation history)
    (continuation : InfiniteContinuation history) :
    (aligned.alignedAt continuation 0).upper = aligned.upper :=
  (history_transport (relation := relation) (continuation.point 0) continuation.start
    (continuation.historyAt 0) continuation.historyAt_zero aligned.start).2

theorem extend_start (aligned : Aligned relation history) {after : CallProtocol.State Request}
    {post : Prefix after call record} (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output) :
    (aligned.extend action output step).start = aligned.start := rfl

/-- Zero-output provider extensions leave the entire upper history unchanged. -/
theorem extend_zero (aligned : Aligned relation history) {after : CallProtocol.State Request}
    {post : Prefix after call record} (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (same : post.accepted = frontier.accepted) :
    (aligned.extend action output step).upper = aligned.upper := by
  simp [upper, extend, fold, advanceUpper, same]

/-- Every actual finite prefix of a fixed-cut stream folds to the SAME upper
history from the original alignment, not a freshly selected same-cut prefix. -/
theorem alignedAt_fixed_upper (aligned : Aligned relation history)
    (continuation : InfiniteContinuation history) (fixed : FixedCut continuation) (n : Nat) :
    (aligned.alignedAt continuation n).upper = aligned.upper := by
  induction n with
  | zero => exact aligned.alignedAt_zero_upper continuation
  | succ n ih =>
    exact ((aligned.alignedAt continuation n).extend_zero
      (continuation.action n) (continuation.output n) (continuation.committed n)
      ((fixed.accepted (n + 1)).trans (fixed.accepted n).symm)).trans ih

/-- The literal upper suffix for one positive provider publication. -/
def publicationPath (aligned : Aligned relation history) {after : CallProtocol.State Request}
    {post : Prefix after call record} (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    projection.system.Path aligned.upper.state aligned.upper.graph
      (.pending (aligned.extend action output step).endpoint) () :=
  Grass.RelationalSystem.Path.snoc (system := projection.system) .nil (.reply aligned.endpoint
    (.advance (aligned.extend action output step).endpoint (by
      change aligned.start.cut.offset + frontier.accepted < aligned.start.cut.offset + post.accepted
      omega))) (.emitted output) (.pending (aligned.extend action output step).endpoint) ()
    ⟨aligned.upper_located, congrArg Behavior.Event.emitted
      (WriteFileProjection.publication_between aligned.start.cut aligned.start.suffix step), rfl⟩

/-- Full path coherence, including original states, graph and all prior choices. -/
theorem extend_positive (aligned : Aligned relation history) {after : CallProtocol.State Request}
    {post : Prefix after call record} (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    (aligned.extend action output step).upper =
      aligned.upper.append (aligned.publicationPath action output step positive) :=
  congrArg Subtype.val (show advanceUpper aligned.start action output step (fold aligned.start history) =
    positiveUpper aligned.start action output step (fold aligned.start history) positive from dif_pos positive)

/-- A positive extension appends its exact emitted bytes to the existing events. -/
theorem extend_positive_events (aligned : Aligned relation history)
    {after : CallProtocol.State Request} {post : Prefix after call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    (aligned.extend action output step).upper.path.events =
      aligned.upper.path.events ++ [.emitted output] := by
  have chose : advanceUpper aligned.start action output step (fold aligned.start history) =
      positiveUpper aligned.start action output step (fold aligned.start history) positive :=
    dif_pos positive
  have events := congrArg (fun result : Located projection
      (WriteFileProjection.cut aligned.start.cut aligned.start.suffix post) => result.val.path.events) chose
  exact events.trans rfl

/-- Existing choices survive, followed by the exact projected cut-indexed reply. -/
theorem extend_positive_choices (aligned : Aligned relation history)
    {after : CallProtocol.State Request} {post : Prefix after call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    (aligned.extend action output step).upper.path.choices =
      aligned.upper.path.choices ++
        [.reply aligned.endpoint (.advance (aligned.extend action output step).endpoint (by
          change aligned.start.cut.offset + frontier.accepted < aligned.start.cut.offset + post.accepted
          omega))] := by
  have chose : advanceUpper aligned.start action output step (fold aligned.start history) =
      positiveUpper aligned.start action output step (fold aligned.start history) positive :=
    dif_pos positive
  have choices := congrArg (fun result : Located projection
      (WriteFileProjection.cut aligned.start.cut aligned.start.suffix post) => result.val.path.choices) chose
  exact choices.trans rfl

/-- Exact bytes of the reached caller history followed by this provider history. -/
theorem output_exact (aligned : Aligned relation history) :
    Behavior.emittedBytes aligned.upper.path.events =
      Behavior.emittedBytes aligned.start.upper.path.events ++ history.published := by
  have current := Accounting.history_accounting (payload := projection.target.payload) aligned.upper
  have first := Accounting.history_accounting (payload := projection.target.payload) aligned.start.upper
  have currentCut := congrArg Accounting.committed aligned.upper_located
  have firstCut := congrArg Accounting.committed aligned.start.located
  exact (current.trans currentCut).trans
    ((WriteFileProjection.history_prefix_exact aligned.start.cut aligned.start.suffix history).symm.trans
      (congrArg (fun bytes => bytes ++ history.published) (first.trans firstCut).symm))

end Aligned
end Grass.Refinement.Console.WriteFileHistory
