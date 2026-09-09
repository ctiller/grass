import Grass.Semantics.BoundaryTiming

namespace Grass.Tests.Semantics.BoundaryTiming

open RelationalSystem

private def spinning : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def protocol : WaitProtocol Unit where
  Response := fun _ => Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

private def boundary : spinning.WaitBoundary protocol where
  Occurrence := Unit
  request := id
  Pending := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := fun _ _ _ _ _ _ => rfl
  nonterminal := by simp [spinning]
  step_reply := by intros; exact ⟨(), trivial, trivial⟩
  reply_step := by intros; exact ⟨(), (), (), (), trivial, trivial⟩

private def history : spinning.History :=
  History.initial (state := ()) (graph := ()) trivial

private def forever : spinning.InfiniteContinuation history.state history.graph
    history.path.events where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => ()
  stateZero := rfl
  graphZero := rfl
  step := fun _ => trivial
  consistent := trivial

/-- Responsiveness excludes only permanent nonresponse, so it coexists with a
productive infinite sequence of actual boundary replies. -/
def responsiveInfinite :
    (BoundaryTimingStrategy.responding boundary).GeneratedComplete :=
  BoundaryTimingStrategy.infiniteCompatible _ history forever

example : BoundaryResponsive (BoundaryTimingStrategy.responding boundary) := by simp

end Grass.Tests.Semantics.BoundaryTiming
