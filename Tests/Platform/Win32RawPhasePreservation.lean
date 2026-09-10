import Grass.Platform.Win32.RawPhasePreservation

/-! Compose actual GetStd return with a bounded actual CPU suffix. The same
state is shared at the join; an unrelated prefix ending elsewhere cannot serve
as the suffix. This proves bookkeeping preservation, not CPU enabledness. -/

namespace Grass.Tests.Win32RawPhasePreservation

open Grass.Core Grass.Op
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

theorem returned_caller_cpu_suffix {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation} {before : RawState} {beforeGraph : Raw.Graph}
    {call : CallProtocol.CallId} {gpr : Grass.ISA.X86.Gpr → BitVec 64} {rflags : BitVec 64}
    {returnEvent : Raw.Event}
    (raw : Nat → RawState) (graphs : Nat → Raw.Graph)
    (choices : Nat → Grass.ISA.X86.Execution.CheckedChoice) (events : Nat → Raw.Event)
    (length : Nat)
    (returned : Raw.RawStep loaded realization environment interpretation beforeGraph before
      (.stdoutResult call gpr rflags) returnEvent (raw 0) (graphs 0))
    (steps : ∀ n, n < length → Raw.RawStep loaded realization environment interpretation (graphs n) (raw n)
      (.cpu (choices n)) (events n) (raw (n + 1)) (graphs (n + 1))) :
    ∀ n, n ≤ length → (raw n).control = .caller inputs.thread ∧
      (raw n).calls.lookup call = none := by
  intro n bounded
  obtain ⟨_, control, calls⟩ := Raw.RawStep.cpu_prefix_frame raw graphs choices events length steps n bounded
  obtain ⟨_, _, caller, retired⟩ := returned.stdout_phase
  exact ⟨control.trans caller, by rw [calls]; exact retired⟩

end Grass.Tests.Win32RawPhasePreservation
