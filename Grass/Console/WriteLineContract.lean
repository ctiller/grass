import Grass.Spec.Root
import Grass.Specification.TextLine
import Grass.Console.OutcomePolicy

/-!
# The portable write-line-and-exit behavior contract

`Console.writeLineContract` is the precise portable meaning of "write one text
line to stdout, then exit with the policy's outcome", stated as a
`BehaviorContract` over `Grass.Service.Console.domain`'s finite event traces:

- an optional probe (`query stdout` replying `false`) that ends the process
  with `policy.stdoutUnavailable`; or
- a write loop that repeatedly offers every still-pending byte to
  `write stdout`, until either a `failed` reply ends the process with
  `policy.writeFailed`, an `accepted 0` reply (no bytes taken, but bytes
  remain) ends it with `policy.noProgress`, or the offered bytes are fully
  accepted (possibly across several partial writes) and the process ends with
  `policy.success`.

**Why the terminal event carries `Outcome`, not a target exit status.**
`docs/VERIFIED_PROGRAM.md` and `docs/TARGET_SEAMS.md` both put the mapping
from an author's outcome to a concrete platform status number at the driver
tier (`TargetOutcomeProjection`, in the not-yet-written `Program.lean`), not
in the authored specification. `Grass.Service.Console.domain`'s own `exit`
request carries a `UInt32`, which is exactly the platform-shaped vocabulary
this contract must not mention. Rather than deferring the link through an
`OutcomeStatus : Outcome → UInt32 → Prop` parameter threaded through every
call site (which `Spikes/1_Hello_World/Spec.lean`'s exact three-argument
`Console.writeLineContract resources message policy` has no room for), this
contract's domain is `Grass.Service.Console.domain` **summed** with a second,
synthetic domain whose only request type is `Outcome` and which is `Terminal`
everywhere (`Grass.Service.Domain.sum`, already exported by
`Grass/Service/Domain.lean` for exactly this composition). The trace's last
event is then literally `call (Sum.inr policy.success)` and so on: the
authored contract names its own outcome value directly and never touches a
status code, while remaining a plain `Service.Event` trace over a portable
domain built entirely from existing, unedited `Grass.Service` vocabulary.
-/

namespace Grass.Console

open Specification

/-- The synthetic "reached this outcome" domain: one request per outcome
value, no response (matching `Grass.Service.Domain.Terminal`'s "no response is
delivered" contract), and every request terminal. -/
private def outcomeDomain (Outcome : Type) : Service.Domain where
  Request := Outcome
  Response := fun _ => Empty
  Terminal := fun _ => True

/-- The portable domain of one write-line-and-exit contract: console I/O,
plus the program's own outcome value in place of a target exit status. -/
def writeLineDomain (Outcome : Type) : Service.Domain :=
  Service.Console.domain.sum (outcomeDomain Outcome)

/-- One accepted write-loop trace for the bytes still `pending`: each `write`
either fails outright, stalls with zero bytes accepted while bytes remain, or
accepts some positive number of the offered bytes (at most what was offered)
and recurses on the remainder, until nothing is pending. -/
inductive WriteLoopAccepts {Outcome : Type} (policy : ConsoleWriteOutcomePolicy Outcome) :
    List UInt8 → List (Service.Event (writeLineDomain Outcome)) → Prop
  | complete :
      WriteLoopAccepts policy [] [.call (.inr policy.success)]
  | failed (pending : List UInt8) :
      WriteLoopAccepts policy pending
        [.call (.inl (.write .stdout pending)),
          .reply (.inl (.write .stdout pending)) .failed,
          .call (.inr policy.writeFailed)]
  | stalled (pending : List UInt8) (nonempty : pending ≠ []) :
      WriteLoopAccepts policy pending
        [.call (.inl (.write .stdout pending)),
          .reply (.inl (.write .stdout pending)) (.accepted 0),
          .call (.inr policy.noProgress)]
  | progress (pending : List UInt8) (count : Nat) (positive : 0 < count)
      (bound : count ≤ pending.length)
      (rest : List (Service.Event (writeLineDomain Outcome)))
      (continues : WriteLoopAccepts policy (pending.drop count) rest) :
      WriteLoopAccepts policy pending
        (.call (.inl (.write .stdout pending)) ::
          .reply (.inl (.write .stdout pending)) (.accepted count) :: rest)

/-- The exact accepted traces: the failed-probe branch, or a write loop over
the message's UTF-8 bytes. -/
def writeLineContractAccepts {Outcome : Type} (message : TextLine)
    (policy : ConsoleWriteOutcomePolicy Outcome) :
    List (Service.Event (writeLineDomain Outcome)) → Prop := fun trace =>
  trace = [.call (.inl (.query .stdout)), .reply (.inl (.query .stdout)) false,
      .call (.inr policy.stdoutUnavailable)] ∨
    WriteLoopAccepts policy message.text.toUTF8.data.toList trace

/-- The precise portable meaning of "write one text line to stdout, then exit
with the policy's outcome". See the module docstring for the domain choice. -/
def writeLineContract {R : Type} [Resource.ResourceModel R] (resources : R) {Outcome : Type}
    (message : TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    BehaviorContract resources where
  Input := Unit
  D := writeLineDomain Outcome
  admits := fun _ => True
  accepts := fun _ trace => writeLineContractAccepts message policy trace

/-- A trace ending exactly at a known request terminates, with the empty
prefix. -/
private theorem terminates_singleton {D : Service.Domain} (request : D.Request)
    (terminal : D.Terminal request) :
    Service.Event.Terminates [Service.Event.call request] :=
  ⟨[], request, rfl, terminal⟩

/-- Prefixing a terminating trace with one more event still terminates, at
the same request. -/
private theorem terminates_cons {D : Service.Domain} (event : Service.Event D)
    {trace : List (Service.Event D)} (terminates : Service.Event.Terminates trace) :
    Service.Event.Terminates (event :: trace) := by
  obtain ⟨lead, request, eq, terminal⟩ := terminates
  exact ⟨event :: lead, request, by simp [eq], terminal⟩

/-- Every accepted write-loop trace terminates: each branch either ends
immediately at the named outcome, or defers to a shorter terminating
continuation. -/
theorem writeLoopAccepts_terminates {Outcome : Type} (policy : ConsoleWriteOutcomePolicy Outcome)
    {pending : List UInt8} {trace : List (Service.Event (writeLineDomain Outcome))}
    (accepted : WriteLoopAccepts policy pending trace) : Service.Event.Terminates trace := by
  induction accepted with
  | complete => exact terminates_singleton _ trivial
  | failed pending => exact terminates_cons _ (terminates_cons _ (terminates_singleton _ trivial))
  | stalled pending nonempty =>
      exact terminates_cons _ (terminates_cons _ (terminates_singleton _ trivial))
  | progress pending count positive bound rest continues ih =>
      exact terminates_cons _ (terminates_cons _ ih)

/-- `writeLineContract`'s author theorem obligation: under the recorded
`.environmentResponsive` liveness demand, every trace it accepts terminates.
This is exactly `MeetsAllSpecificationTheorems` for the `SpecProcess` a spike
builds from `writeLineContract` and this one liveness demand
(`Spikes/1_Hello_World/Spec.lean`'s `helloSpecCorrect`). -/
theorem writeLineContractCorrect {R : Type} [Resource.ResourceModel R] (resources : R)
    {Outcome : Type} (message : TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    MeetsAllSpecificationTheorems
      ((SpecProcess.ofRelational (writeLineContract resources message policy)).withLiveness
        (.terminatesUnder [.environmentResponsive])) := by
  intro demand membership
  simp only [SpecProcess.withLiveness_liveness, SpecProcess.ofRelational_liveness,
    List.nil_append, List.mem_singleton] at membership
  subst membership
  intro _input _admitted trace accepted
  rcases accepted with unavailable | loop
  · subst unavailable
    exact terminates_cons _ (terminates_cons _ (terminates_singleton _ trivial))
  · exact writeLoopAccepts_terminates policy loop

end Grass.Console
