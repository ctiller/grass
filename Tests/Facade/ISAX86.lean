import Grass.ISA.X86
import Tests.Facade.Containment

/-!
# The `Grass.ISA.X86` boundary

This module imports the facade and nothing else from `Grass`, so its environment
is the facade's cone. See `Tests/Facade/Containment.lean` for why absence is
checked this way.

The present list is the vocabulary a machine-model author or
`Grass.Assembly.X86` reaches for: the register and operand types, the encoding
byte-level types, the encode and decode entry points, and the validation
metadata `docs/MODULES.md` names as part of this facade's region.

The absent list is chosen to be *representative rather than exhaustive*, which
is the honest description of a negative list. Each entry is a real declaration
that some other module imports normally:

* `Grass.DemandCertificateFamily` is the certificate layer, which
  `docs/MODULES.md` forbids by name.
* `Grass.Memory.MemoryEvent` is a peer machine model. An ISA table has no
  business depending on the memory-event vocabulary, and if it starts to, that
  is a design change rather than an import.
* `Grass.ABI.Win64.UnwindInfo` and `Grass.Platform.Win32.StdHandleId` are the
  two neighbouring trees the same agent owns. They are the entries most likely
  to be added by accident, precisely because there is no ownership boundary to
  stop it.
-/

namespace Grass.Tests.Facade

/-- Vocabulary that must resolve through `import Grass.ISA.X86` alone. -/
def isaPresent : List Lean.Name :=
  [ `Grass.ISA.X86.Gpr
  , `Grass.ISA.X86.ByteReg
  , `Grass.ISA.X86.Scale
  , `Grass.ISA.X86.Rex
  , `Grass.ISA.X86.ModRm
  , `Grass.ISA.X86.Sib
  , `Grass.ISA.X86.MemOperand
  , `Grass.ISA.X86.Immediate
  , `Grass.ISA.X86.InsnEncoding
  , `Grass.ISA.X86.decodeInsn
  , `Grass.ISA.X86.encodeMemInsn
  , `Grass.ISA.X86.movRegImm64
  , `Grass.ISA.X86.leaR64
  , `Grass.ISA.X86.Ledger
  , `Grass.ISA.X86.CommonRule
  , `Grass.ISA.X86.commonProfileLedger
  , `Grass.ISA.X86.openReleaseBlockers
  ]

/-- Declarations that must not be reachable through the facade. -/
def isaAbsent : List Lean.Name :=
  [ `Grass.DemandCertificateFamily
  , `Grass.Memory.MemoryEvent
  , `Grass.ABI.Win64.UnwindInfo
  , `Grass.Platform.Win32.StdHandleId
  ]

open Lean Elab Command in
run_cmd checkCone "Grass.ISA.X86" isaPresent isaAbsent

end Grass.Tests.Facade
