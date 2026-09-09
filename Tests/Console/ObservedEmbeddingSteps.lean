import Grass.Console.ObservedEmbeddingSteps

namespace Grass.Tests.Console.ObservedEmbeddingSteps

open Grass.Specification Grass.Semantics Grass.Console Grass.RelationalSystem
open Grass.Console.ObservedBehavior Grass.Console.ObservedEmbedding

private def request : LineRequest Bool := ⟨"x", ⟨true, false, false, false⟩⟩
private def rendering : LineRendering := ⟨TextEncoding.utf8, "\r\n"⟩
private def start := Behavior.initial (rendering.bytes request.line)
private def full := OutputCut.full (rendering.bytes request.line)
private theorem positive : (OutputCut.zero (rendering.bytes request.line)).offset < full.offset := by decide
private def first : OutputCut (rendering.bytes request.line) := ⟨1, by decide⟩
private def progressed := Behavior.advanceHistory (rendering.bytes request.line)
  (OutputCut.zero _) first (by decide) start rfl

example := embedHistory_advance request rendering start (OutputCut.zero _) full positive rfl
example := embedHistory_finish request rendering start (OutputCut.zero _) .writeFailed trivial rfl

example := embedHistory_advance request rendering progressed first full (by decide) rfl
example := embedHistory_finish request rendering progressed first .writeFailed trivial rfl

example : (embedPermanentWait request rendering (Behavior.permanentWaitAt _ full)).occurrence =
    .output full := embedPermanentWait_occurrence request rendering _

end Grass.Tests.Console.ObservedEmbeddingSteps
