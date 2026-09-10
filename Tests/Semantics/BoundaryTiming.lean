import Grass.Semantics.BoundaryTiming

namespace Grass.Tests.Semantics.BoundaryTiming

open RelationalSystem

private def spinning : RelationalSystem Unit where
  State := Nat
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ state _ _ next _ => next = state + 1
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
  Occurrence := Nat
  request := fun _ => ()
  Pending := fun history occurrence => history.state = occurrence
  External := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := fun _ _ _ _ _ _ => rfl
  nonterminal := by simp [spinning]
  step_external := by intros; trivial
  step_pending_or_reply := by intros; right; exact ⟨(), trivial, trivial⟩
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply later
    change next = occurrence at later
    have step' : (show Nat from next) = (show Nat from history.state) + 1 := by
      simpa only [spinning] using step
    have pending' : (show Nat from history.state) = occurrence := pending
    have impossible : occurrence = occurrence + 1 :=
      later.symm.trans (step'.trans (congrArg (· + 1) pending'))
    omega
private def history : spinning.History :=
  History.initial (state := (0 : Nat)) (graph := ()) trivial

private def forever : spinning.InfiniteContinuation history.state history.graph
    history.path.events where
  stateAt := fun index => index
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => ()
  stateZero := rfl
  graphZero := rfl
  step := by intro index; simp [spinning]
  consistent := trivial

/-- Responsiveness excludes only permanent nonresponse, so it coexists with a
productive infinite sequence of actual boundary replies. -/
def responsiveInfinite :
    (BoundaryTimingStrategy.responding boundary).GeneratedComplete :=
  BoundaryTimingStrategy.infiniteCompatible _ history forever

example : BoundaryResponsive (BoundaryTimingStrategy.responding boundary) := by simp

end Grass.Tests.Semantics.BoundaryTiming
