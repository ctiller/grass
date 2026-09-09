import Grass.Assembly.WriteAllLoopSource

/-! Exact source selection for the post-load guards preceding the write-all
update. Branch destinations derive from the checked labels, not numeric inputs.
-/

namespace Grass.Assembly.WriteAllGuardSource

open Grass.ISA.X86 Grass.Std.Logical X86Source WriteAllLoopSource

variable {frame : SourceFrame.Result} {rootOffset : Nat}

def loadInstruction : Instruction := ⟨.mov, [.register ⟨.rax, .w32⟩, .symbol "transferred"]⟩
def testInstruction : Instruction := ⟨.test, [.register ⟨.rax, .w32⟩, .register ⟨.rax, .w32⟩]⟩
def zeroInstruction : Instruction := ⟨.jz, [.symbol "exit_no_progress"]⟩
def cmpInstruction : Instruction := ⟨.cmp, [.register ⟨.rax, .w32⟩, .register ⟨.r14, .w32⟩]⟩
def aboveInstruction : Instruction := ⟨.ja, [.symbol "provider_violation"]⟩

def branchTargetFor {splice : SourceSplice.Result frame rootOffset}
    {symbols : SourceResolve.Symbols} {codeBase : Nat}
    (kind : Rel32.Kind) (output : SourceResolve.Output splice symbols codeBase) : Option Nat :=
  match output.detail with
  | .branch actual target _ => if actual = kind then some target else none
  | _ => none

def labelIndex (source : SourceResolve.Result frame rootOffset) (label : String) : Option Nat :=
  (findValue frame.program.collected.labels label).map
    (SourceSplice.sourceFinalIndex frame.saved.savedItems.length source.splice.initialization.entries.length)

structure Candidate (source : SourceResolve.Result frame rootOffset) where
  loop : WriteAllLoopSource.Selection source
  loadIndex : Nat
  load : OutputAt source loadIndex
  tested : OutputAt source (loadIndex + 1)
  zero : OutputAt source (loadIndex + 2)
  compared : OutputAt source (loadIndex + 3)
  above : OutputAt source (loadIndex + 4)
  zeroTarget : Nat
  aboveTarget : Nat

def Candidate.Valid {source : SourceResolve.Result frame rootOffset} (candidate : Candidate source) : Prop :=
  candidate.loop.candidate.addIndex = candidate.loadIndex + 5 ∧
  originInstruction candidate.load.output = some loadInstruction ∧
  originInstruction candidate.tested.output = some testInstruction ∧
  originInstruction candidate.zero.output = some zeroInstruction ∧
  originInstruction candidate.compared.output = some cmpInstruction ∧
  originInstruction candidate.above.output = some aboveInstruction ∧
  labelIndex source "exit_no_progress" = some candidate.zeroTarget ∧
  labelIndex source "provider_violation" = some candidate.aboveTarget ∧
  branchTargetFor .equal candidate.zero.output = some candidate.zeroTarget ∧
  branchTargetFor .above candidate.above.output = some candidate.aboveTarget

instance {source : SourceResolve.Result frame rootOffset} (candidate : Candidate source) :
    Decidable candidate.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure Selection (source : SourceResolve.Result frame rootOffset) where
  private mk ::
  candidate : Candidate source
  valid : candidate.Valid

/-- Select guard occurrences relative to the already checked update, retaining
the original load and every intervening source instruction. -/
def select? (source : SourceResolve.Result frame rootOffset) : Option (Selection source) := do
  let loop ← WriteAllLoopSource.select? source
  if loop.candidate.addIndex < 5 then none else do
    let loadIndex := loop.candidate.addIndex - 5
    let load ← outputAt? source loadIndex
    let tested ← outputAt? source (loadIndex + 1)
    let zero ← outputAt? source (loadIndex + 2)
    let compared ← outputAt? source (loadIndex + 3)
    let above ← outputAt? source (loadIndex + 4)
    let zeroTarget ← labelIndex source "exit_no_progress"
    let aboveTarget ← labelIndex source "provider_violation"
    let candidate : Candidate source := ⟨loop, loadIndex, load, tested, zero, compared, above, zeroTarget, aboveTarget⟩
    if valid : candidate.Valid then some ⟨candidate, valid⟩ else none

def headExitInstruction : Instruction := ⟨.je, [.symbol "exit_success"]⟩
def failedInstruction : Instruction := ⟨.jz, [.symbol "exit_write_failed"]⟩

structure PrefixCandidate (source : SourceResolve.Result frame rootOffset) where
  post : Selection source
  headExit : OutputAt source (post.candidate.loop.candidate.headIndex + 1)
  rawIndex : Nat
  rawTest : OutputAt source rawIndex
  failed : OutputAt source (rawIndex + 1)
  successTarget : Nat
  failureTarget : Nat

def PrefixCandidate.Valid {source : SourceResolve.Result frame rootOffset}
    (candidate : PrefixCandidate source) : Prop :=
  candidate.rawIndex + 2 = candidate.post.candidate.loadIndex ∧
  originInstruction candidate.headExit.output = some headExitInstruction ∧
  originInstruction candidate.rawTest.output = some testInstruction ∧
  originInstruction candidate.failed.output = some failedInstruction ∧
  labelIndex source "exit_success" = some candidate.successTarget ∧
  labelIndex source "exit_write_failed" = some candidate.failureTarget ∧
  branchTargetFor .equal candidate.headExit.output = some candidate.successTarget ∧
  branchTargetFor .equal candidate.failed.output = some candidate.failureTarget

instance {source : SourceResolve.Result frame rootOffset} (candidate : PrefixCandidate source) :
    Decidable candidate.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure AllSelection (source : SourceResolve.Result frame rootOffset) where
  private mk ::
  candidate : PrefixCandidate source
  valid : candidate.Valid

/-- Include the source-selected head-success and raw-BOOL failure guards.
The latter is before the actual DWORD load, preserving failure's no-read path. -/
def selectAll? (source : SourceResolve.Result frame rootOffset) : Option (AllSelection source) := do
  let post ← select? source
  if post.candidate.loadIndex < 2 then none else do
    let rawIndex := post.candidate.loadIndex - 2
    let headExit ← outputAt? source (post.candidate.loop.candidate.headIndex + 1)
    let rawTest ← outputAt? source rawIndex
    let failed ← outputAt? source (rawIndex + 1)
    let successTarget ← labelIndex source "exit_success"
    let failureTarget ← labelIndex source "exit_write_failed"
    let candidate : PrefixCandidate source := ⟨post, headExit, rawIndex, rawTest, failed, successTarget, failureTarget⟩
    if valid : candidate.Valid then some ⟨candidate, valid⟩ else none

end Grass.Assembly.WriteAllGuardSource
