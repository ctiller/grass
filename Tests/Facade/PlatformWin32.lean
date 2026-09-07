import Grass.Platform.Win32
import Tests.Facade.Containment

/-!
# The `Grass.Platform.Win32` boundary

`win32Cone` pins the whole dependency closure; see `Tests/Facade/Containment.lean`
for why that replaced a list of names that must be absent.

## A correction, because the first version of this fixture asserted the opposite

The facade was drafted claiming that x86 vocabulary does not reach the platform
cone, with `Grass.ISA.X86.Gpr` as the example. The sampled fixture rejected
that, because `Grass/Platform/Win32/Console.lean` imported
`Grass.ABI.Win64.Convention`, which reaches `Grass.ISA.X86.Register`. I took the
fixture's word for it, moved `Gpr` into the *present* list, and wrote a
paragraph explaining that a calling convention is partly a statement about
registers so the edge belonged there.

A second reviewer checked what `Console.lean` actually used from `Convention`
and found the answer was nothing: one grep, and the only hit was the import
line itself. The file needed the `Grass.Cite` namespace, which comes from
`Grass.ISA.X86.Citation`. The import was dead, the cone was wider than anything
required it to be, and pinning `Gpr` as *present* had made a dead import load
bearing -- so removing it, which is exactly the cleanup `lake shake` exists to
prompt, would have failed this fixture.

`Console.lean` now imports `Grass.ISA.X86.Citation` directly. The original draft
claim was right and the correction was wrong, which is worth leaving written
down: the fixture proved the cone contained `Gpr`, and I read that as proving
the edge was meant to be there.

`Grass.ISA.X86.Citation` remains, and is the only x86 module in the cone: the
console entry points carry external-authority citations like every other
machine-facing declaration in this repository.
-/

namespace Grass.Tests.Facade

/-- Every `Grass` module reachable through `import Grass.Platform.Win32`. -/
def win32Cone : List Lean.Name :=
  [ `Grass.Core.Name
  , `Grass.ISA.X86.Citation
  , `Grass.Platform.Win32
  , `Grass.Platform.Win32.Console
  , `Grass.Platform.Win32.Profile
  ]

/-- Vocabulary that must resolve through `import Grass.Platform.Win32` alone. -/
def win32Present : List Lean.Name :=
  -- Handles.
  [ `Grass.Platform.Win32.StdHandleId
  , `Grass.Platform.Win32.GetStdHandleResult
  , `Grass.Platform.Win32.UsableHandle
  , `Grass.Platform.Win32.UsableHandle.mk?
  , `Grass.Platform.Win32.GetStdHandleResult.invalidHandleValue
  -- Writing, including the relation the facade advertises as the point of the
  -- module. It was unpinned in the first version, which a reviewer noted.
  , `Grass.Platform.Win32.WriteRequest
  , `Grass.Platform.Win32.WriteResponse
  , `Grass.Platform.Win32.Allowed
  , `Grass.Platform.Win32.writeAdequate
  , `Grass.Platform.Win32.partialWrite_allowed
  , `Grass.Platform.Win32.zeroWrite_allowed
  , `Grass.Platform.Win32.ExcessWriteCount
  -- Exit.
  , `Grass.Platform.Win32.ExitRequest
  , `Grass.Platform.Win32.successStatus
  -- The profile values docs/MODULES.md moved out of the module path.
  , `Grass.Platform.Win32.ApiBaseline
  , `Grass.Platform.Win32.TargetAbi
  , `Grass.Platform.Win32.TargetAbi.handleBits
  , `Grass.Platform.Win32.CallDiscipline
  , `Grass.Platform.Win32.Profile
  , `Grass.Platform.Win32.decision16
  , `Grass.Platform.Win32.Profile.FollowsDecision16
  , `Grass.Platform.Win32.decision16_follows
  ]

open Lean Elab Command in
run_cmd checkCone "Grass.Platform.Win32" win32Cone win32Present

end Grass.Tests.Facade
