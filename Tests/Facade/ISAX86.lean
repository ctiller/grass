import Grass.ISA.X86
import Tests.Facade.Containment

/-!
# The `Grass.ISA.X86` boundary

This module imports the facade and nothing else from `Grass`, so its environment
is the facade's cone. See `Tests/Facade/Containment.lean` for why the cone is
pinned exhaustively rather than sampled with a list of names that must be
absent: two cold reviewers defeated the sampled version, once by renaming the
sampled names and once by widening the cone with modules the sample did not
mention.

`isaCone` is the whole of the `Grass` claim. Fourteen modules: the eleven
shards, the facade itself, and outside `Grass.ISA.X86` exactly two leaves,
`Grass.Core.Name` and `Grass.Std.Logical.Byte`. A `Grass` edge to a module
*outside* those fourteen fails this fixture, including one nobody anticipated.

Two kinds of edge do not, and this paragraph has now overclaimed twice, so both
are written down rather than left to be discovered a third time.

`import Lean` added to a shard passes: `Tests/Facade/Containment.lean` explains
why non-`Grass` widening is structurally invisible here.

And a cone is a *set of modules*, not a graph of edges, so an edge between two
modules that are already in it changes nothing this fixture can see. Adding
`import Grass.ISA.X86.Decode` to `Grass/ISA/X86/Performance.lean` -- the
performance model reaching into the decoder, a layering violation of exactly the
kind a cone fixture is expected to catch -- builds green. A reviewer
demonstrated it; nothing here would notice.

`isaPresent` is the other half: the vocabulary a machine-model author or
`Grass.Assembly.X86` reaches for, which the facade may not quietly stop
exporting. It is a floor and not a ceiling -- a name absent from it is not
thereby forbidden, it is merely unpromised -- so if a consumer needs a name that
is not here, add it, which is what turns a current fact into a commitment.
-/

namespace Grass.Tests.Facade

/-- Every `Grass` module reachable through `import Grass.ISA.X86`. -/
def isaCone : List Lean.Name :=
  [ `Grass.Core.Name
  , `Grass.ISA.X86
  , `Grass.ISA.X86.Addressing
  , `Grass.ISA.X86.Bytes
  , `Grass.ISA.X86.Citation
  , `Grass.ISA.X86.Decode
  , `Grass.ISA.X86.DualCitation
  , `Grass.ISA.X86.Encoding
  , `Grass.ISA.X86.Ledger
  , `Grass.ISA.X86.Performance
  , `Grass.ISA.X86.Profile
  , `Grass.ISA.X86.Register
  , `Grass.ISA.X86.Sources
  , `Grass.Std.Logical.Byte
  ]

/-- Vocabulary that must resolve through `import Grass.ISA.X86` alone. -/
def isaPresent : List Lean.Name :=
  -- Registers and operands.
  [ `Grass.ISA.X86.Gpr
  , `Grass.ISA.X86.ByteReg
  , `Grass.ISA.X86.Scale
  , `Grass.ISA.X86.MemOperand
  , `Grass.ISA.X86.Displacement
  , `Grass.ISA.X86.Immediate
  -- Encoding bytes.
  , `Grass.ISA.X86.Rex
  , `Grass.ISA.X86.ModRm
  , `Grass.ISA.X86.Sib
  , `Grass.ISA.X86.RmEncoding
  , `Grass.ISA.X86.InsnEncoding
  , `Grass.ISA.X86.OpcodeSpec
  -- Encoding and decoding entry points.
  , `Grass.ISA.X86.encodeMem
  , `Grass.ISA.X86.encodeMemInsn
  , `Grass.ISA.X86.decodeMem
  , `Grass.ISA.X86.decodeInsn
  , `Grass.ISA.X86.DecodeError
  , `Grass.ISA.X86.movRegImm64
  , `Grass.ISA.X86.leaR64
  -- The performance model. Pinned because nothing else pins it, and an
  -- unpinned shard can leave the facade without the fixture noticing.
  , `Grass.ISA.X86.CostModel
  , `Grass.ISA.X86.TimingBasis
  , `Grass.ISA.X86.LeakageChannel
  -- Validation metadata.
  , `Grass.ISA.X86.Ledger
  , `Grass.ISA.X86.CommonRule
  , `Grass.ISA.X86.Vendor
  , `Grass.ISA.X86.commonProfileLedger
  , `Grass.ISA.X86.openReleaseBlockers
  ]

open Lean Elab Command in
run_cmd checkCone "Grass.ISA.X86" isaCone isaPresent

end Grass.Tests.Facade
