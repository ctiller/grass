import Grass.Refinement.Console.WriteHistory

/-!
# Reachable histories of the portable console writer

These fixtures build actual `ExecutionPrefix` values through the elaborated
sequential machine. They exercise unavailable output, complete success, and a
partial successful write followed by a failure which emits the whole remainder.
-/

namespace Tests.Std.ConsoleHistory

open Grass Grass.Process Grass.Std.Logical Grass.Std.Console
open Grass.Std.Console.WriteProcess
open Grass.Refinement.Console.WriteHistory

private def payload : Vec Byte := ⟨[65, 66, 67]⟩
private def start : WriteCursor payload := startCursor payload
private def firstCount : WriteCount start := ⟨1, by decide⟩
private def afterFirst : WriteCursor payload := advance start firstCount
private def remainderCount : WriteCount afterFirst := fullRemainingCount afterFirst
private def fullCount : WriteCount start := fullRemainingCount start

private def initialPoint : (machine payload).Point := ⟨0, .acquire⟩

private def initialPrefix : (system payload).ExecutionPrefix :=
  RelationalSystem.ExecutionPrefix.initial (state := initialPoint) (graph := ()) (by
    change initialPoint = ⟨0, State.acquire⟩ ∧
      (machine payload).held initialPoint = (machine payload).held initialPoint ∧ [] = []
    exact ⟨rfl, rfl, rfl⟩)

private def stdoutOccurrence : (machine payload).Occurrence :=
  ⟨initialPoint, .stdout, fun available =>
    match available with
    | true => .writing start
    | false => .unavailable⟩

private theorem stdoutIssues : stdoutOccurrence.Issues := by
  change WriteProcess.decide (State.acquire : State payload) = .effect .stdout
    (fun available => match available with
      | true => .writing (startCursor payload)
      | false => .unavailable)
  simp only [WriteProcess.decide]
  congr 1
  funext available
  cases available <;> rfl

private theorem holdsStdout :
    (machine payload).held initialPoint = {stdoutOccurrence} := by
  rw [SequentialMachine.held_of_effect (decision := rfl)]
  apply congrArg (fun occurrence => ({occurrence} : Bag (machine payload).Occurrence))
  apply SequentialMachine.issuing_occurrence_determined_by_point
    (machine := machine payload)
  · rfl
  · exact stdoutIssues
  · rfl

private def unavailablePoint : (machine payload).Point := ⟨1, .unavailable⟩

private def unavailablePrefix : (system payload).ExecutionPrefix :=
  initialPrefix.step (choice := .result stdoutOccurrence false) (event := [])
    (nextState := unavailablePoint) (nextGraph := ()) (by
      change (program payload).Step initialPoint (.result stdoutOccurrence false)
        unavailablePoint ((machine payload).held unavailablePoint) []
      exact ⟨rfl, rfl, holdsStdout, rfl, rfl⟩)

example : (program payload).terminal () unavailablePrefix.state .unavailable := by rfl

example : historyBytes unavailablePrefix.events = Vec.empty :=
  run_unavailable unavailablePrefix (by rfl)

private def writingPoint : (machine payload).Point := ⟨1, .writing start⟩

private def availablePrefix : (system payload).ExecutionPrefix :=
  initialPrefix.step (choice := .result stdoutOccurrence true) (event := [])
    (nextState := writingPoint) (nextGraph := ()) (by
      change (program payload).Step initialPoint (.result stdoutOccurrence true)
        writingPoint ((machine payload).held writingPoint) []
      exact ⟨rfl, rfl, holdsStdout, rfl, rfl⟩)

private def firstWriteOccurrence : (machine payload).Occurrence :=
  ⟨writingPoint, .write start, fun response =>
    .publish start (by decide) response⟩

private def successPublishPoint : (machine payload).Point :=
  ⟨2, .publish start (by decide) (.success fullCount)⟩

private def successResultPrefix : (system payload).ExecutionPrefix :=
  availablePrefix.step (choice := .result firstWriteOccurrence (.success fullCount))
    (event := []) (nextState := successPublishPoint) (nextGraph := ()) (by
      change (program payload).Step writingPoint
        (.result firstWriteOccurrence (.success fullCount)) successPublishPoint
        ((machine payload).held successPublishPoint) []
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

private def successPoint : (machine payload).Point :=
  ⟨3, .finished .success (advance start fullCount)⟩

private def successPrefix : (system payload).ExecutionPrefix :=
  successResultPrefix.step (choice := .internal) (event := [payload])
    (nextState := successPoint) (nextGraph := ()) (by
      change (program payload).Step successPublishPoint .internal successPoint
        ((machine payload).held successPoint) [payload]
      refine ⟨rfl, rfl, ?_⟩
      rfl)

example : (program payload).terminal () successPrefix.state
    (.written .success (advance start fullCount)) := by rfl

example : historyBytes successPrefix.events = payload :=
  run_success successPrefix (advance start fullCount) (by rfl)

private def partialPublishPoint : (machine payload).Point :=
  ⟨2, .publish start (by decide) (.success firstCount)⟩

private def partialResultPrefix : (system payload).ExecutionPrefix :=
  availablePrefix.step (choice := .result firstWriteOccurrence (.success firstCount))
    (event := []) (nextState := partialPublishPoint) (nextGraph := ()) (by
      change (program payload).Step writingPoint
        (.result firstWriteOccurrence (.success firstCount)) partialPublishPoint
        ((machine payload).held partialPublishPoint) []
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

private def retryPoint : (machine payload).Point := ⟨3, .writing afterFirst⟩

private def partialPrefix : (system payload).ExecutionPrefix :=
  partialResultPrefix.step (choice := .internal) (event := [⟨[65]⟩])
    (nextState := retryPoint) (nextGraph := ()) (by
      change (program payload).Step partialPublishPoint .internal retryPoint
        ((machine payload).held retryPoint) [⟨[65]⟩]
      refine ⟨rfl, rfl, ?_⟩
      rfl)

private def remainderWriteOccurrence : (machine payload).Occurrence :=
  ⟨retryPoint, .write afterFirst, fun response =>
    .publish afterFirst (by decide) response⟩

private def failurePublishPoint : (machine payload).Point :=
  ⟨4, .publish afterFirst (by decide) (.failure remainderCount)⟩

private def failureResultPrefix : (system payload).ExecutionPrefix :=
  partialPrefix.step
    (choice := .result remainderWriteOccurrence (.failure remainderCount))
    (event := []) (nextState := failurePublishPoint) (nextGraph := ()) (by
      change (program payload).Step retryPoint
        (.result remainderWriteOccurrence (.failure remainderCount)) failurePublishPoint
        ((machine payload).held failurePublishPoint) []
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

private def failedCursor : WriteCursor payload := advance afterFirst remainderCount
private def failurePoint : (machine payload).Point :=
  ⟨5, .finished .writeFailed failedCursor⟩

private def failurePrefix : (system payload).ExecutionPrefix :=
  failureResultPrefix.step (choice := .internal) (event := [⟨[66, 67]⟩])
    (nextState := failurePoint) (nextGraph := ()) (by
      change (program payload).Step failurePublishPoint .internal failurePoint
        ((machine payload).held failurePoint) [⟨[66, 67]⟩]
      refine ⟨rfl, rfl, ?_⟩
      rfl)

example : (program payload).terminal () failurePrefix.state
    (.written .writeFailed failedCursor) := by rfl

example : historyBytes partialPrefix.events = ⟨[65]⟩ := by rfl

example : historyBytes failurePrefix.events = payload := by rfl

/-- A failure's ghost witness may account for every payload byte. -/
example : historyBytes failurePrefix.events = payload :=
  run_writeFailed failurePrefix failedCursor (by rfl) |>.trans (by rfl)

end Tests.Std.ConsoleHistory
