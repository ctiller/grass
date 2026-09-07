import Grass.Platform.Win32
import Tests.Facade.Containment

/-!
# The `Grass.Platform.Win32` boundary

The present list is the Win32 API vocabulary plus the profile values that
`docs/MODULES.md` moved out of the module path and into this API. Both belong in
the same list: the ruling's point is that a Windows floor and an ABI are
*selected through this facade*, so a facade that exported the console calls but
not `Profile` would have moved the spelling without moving the selection.

## Where the boundary actually falls

Writing this fixture corrected a claim made when the facade was drafted. The
draft asserted that x86 vocabulary does not reach the platform facade and used
`Grass.ISA.X86.Gpr` as the example; the fixture rejected it, because
`Grass.ABI.Win64.Convention` states which general-purpose registers are
volatile and which carry arguments, and `Grass.Platform.Win32.Console` describes
its entry points in those terms. `Gpr` is in the cone, and correctly so.

The boundary is one layer finer than "no x86 here". Register *names* arrive with
the calling convention, because a calling convention is partly a statement about
registers. The instruction *encoder and decoder* do not arrive, because nothing
about calling `WriteFile` depends on how a `mov` is spelled in bytes. So
`Grass.ISA.X86.Gpr` is required present and `Grass.ISA.X86.decodeInsn` and
`Grass.ISA.X86.encodeMemInsn` are required absent, which is the distinction
worth pinning.

`Grass.ABI.Win64.UnwindInfo` is absent for the same kind of reason:
`Grass.Platform.Win32.Console` imports `Convention` and not `Unwind`, and unwind
tables are a different concern from the API family this facade fronts.
-/

namespace Grass.Tests.Facade

/-- Vocabulary that must resolve through `import Grass.Platform.Win32` alone. -/
def win32Present : List Lean.Name :=
  [ `Grass.Platform.Win32.StdHandleId
  , `Grass.Platform.Win32.GetStdHandleResult
  , `Grass.Platform.Win32.UsableHandle
  , `Grass.Platform.Win32.WriteRequest
  , `Grass.Platform.Win32.WriteResponse
  , `Grass.Platform.Win32.ExitRequest
  , `Grass.Platform.Win32.ApiBaseline
  , `Grass.Platform.Win32.TargetAbi
  , `Grass.Platform.Win32.CallDiscipline
  , `Grass.Platform.Win32.Profile
  , `Grass.Platform.Win32.decision16
  , `Grass.Platform.Win32.Profile.FollowsDecision16
  , `Grass.ABI.Win64.Volatility
  , `Grass.ABI.Win64.argumentRegister
  , `Grass.ISA.X86.Gpr
  ]

/-- Declarations that must not be reachable through the facade.

`decodeInsn` and `encodeMemInsn` are the load-bearing entries: they are what
separates "the ABI names registers" from "the platform facade is an assembler".
-/
def win32Absent : List Lean.Name :=
  [ `Grass.ISA.X86.decodeInsn
  , `Grass.ISA.X86.encodeMemInsn
  , `Grass.ISA.X86.InsnEncoding
  , `Grass.ABI.Win64.UnwindInfo
  , `Grass.DemandCertificateFamily
  , `Grass.Memory.MemoryEvent
  ]

open Lean Elab Command in
run_cmd checkCone "Grass.Platform.Win32" win32Present win32Absent

end Grass.Tests.Facade
