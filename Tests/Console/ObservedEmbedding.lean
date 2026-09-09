import Grass.Console.ObservedEmbedding
namespace Grass.Tests.Console.ObservedEmbedding
open Grass.Specification Grass.Semantics Grass.Console Grass.RelationalSystem
open Grass.Console.ObservedBehavior Grass.Console.ObservedEmbedding
private def request : LineRequest Bool := ⟨"x", ⟨true, false, false, false⟩⟩
private def rendering : LineRendering := ⟨TextEncoding.utf8, "\r\n"⟩
private def cut : OutputCut (rendering.bytes request.line) := OutputCut.full _
private def componentHistory : (Behavior.system (rendering.bytes request.line)).History :=
  let pending := Behavior.pendingAt _ cut
  have step : (Behavior.system (rendering.bytes request.line)).Step () (.pending cut)
      (Behavior.Choice.reply cut (.finish .writeFailed))
      (Behavior.Event.terminal .writeFailed) (Behavior.State.finished cut .writeFailed) () :=
    ⟨rfl, trivial, rfl, rfl⟩
  pending.append (.snoc .nil (Behavior.Choice.reply cut (.finish .writeFailed))
    (Behavior.Event.terminal .writeFailed) (Behavior.State.finished cut .writeFailed) ()
    (Behavior.pendingAt_state _ _ ▸ step))
private theorem componentTerminal :
    (Behavior.system (rendering.bytes request.line)).Terminal componentHistory.state () :=
  ⟨cut, .writeFailed, rfl, trivial⟩
example : ∃ selection,
    (embedHistory request rendering componentHistory).observed.state = .reporting selection :=
  terminal_embeds_reporting request rendering componentTerminal
example : Nonempty (TerminalExtension (boundary request rendering)
    (embedHistory request rendering componentHistory).observed) :=
  observeEmbeddedTerminal request rendering componentTerminal
example : ¬ (system request rendering).Terminal
    (embedHistory request rendering componentHistory).observed.state () :=
  embedded_terminal_not_terminal request rendering componentTerminal
end Grass.Tests.Console.ObservedEmbedding
