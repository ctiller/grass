import Grass.Refinement.Console.WriteAllGuards
import Tests.Console.WriteAllHead

namespace Grass.Tests.Console.WriteAllGuards

open Grass.Assembly Grass.ISA.X86.Execution Grass.Refinement.Console.WriteFileLoad

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def selected (text : List Char) : Option Bool := do
  let symbols ← Grass.Tests.Assembly.SourceResolve.checkedSymbols
  let body ← (SourceInput.extractHelloSourceChars text).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let source ← SourceResolve.resolve? splice symbols 1000
  pure (WriteAllGuardSource.selectAll? source).isSome

example : selected WriteAllHead.authored = some true := by decide +kernel

/-- These remain valid resolved programs, but have the wrong authored target. -/
example : selected (WriteAllHead.mutated "jz exit_no_progress" "jz exit_write_failed") = some false := by
  decide +kernel

example : selected (WriteAllHead.mutated "jz exit_write_failed" "jz exit_no_progress") = some false := by
  decide +kernel

example : selected (WriteAllHead.mutated "je exit_success" "je exit_unavailable") = some false := by
  decide +kernel

/-- A well-encoded comparison against a different register is also rejected. -/
example : selected (WriteAllHead.mutated "cmp eax, r14d" "cmp eax, r13d") = some false := by
  decide +kernel

/-- A raw failure reaches its exact source target with no load, initialized
count, or successful-path continuation premise. -/
example {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selected : WriteAllGuardSource.AllSelection source)
    {before : State} {raw : TestZeroRun .rax before}
    (bound : SourceGuard selected.candidate.rawTest.output selected.candidate.failed.output raw)
    (failed : (before.gpr .rax).setWidth 32 = 0) :
    raw.result.rip = BitVec.ofNat 64 (bound.tested.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.failureTarget) := by
  have taken : raw.result.rip = raw.branch.target := by
    apply raw.branch.taken_rip
    change raw.tested.result.statusFlags.zf = true
    rw [raw.zero_flag, failed]
    rfl
  exact taken.trans (source_failure_target selected bound)

end Grass.Tests.Console.WriteAllGuards
