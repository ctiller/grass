import Grass.Emit

/-!
# Verified emission facade fixtures

This file imports only `Grass.Emit`. The positive checks establish the intended
surface; the guarded failures pin representative implementation vocabulary
outside its transitive dependency cone.
-/

namespace Grass.Tests.Artifact.EmitFacade

open Grass

example (spec : SpecProcess) := VerifiedProgram spec

example {spec : SpecProcess} (verified : VerifiedProgram spec) : ByteArray :=
  emitProgram verified

example {spec : SpecProcess} (verified : VerifiedProgram spec) :
    verified.artifact.format.Parses (emitProgram verified)
      verified.artifact.artifact :=
  emitProgram_parses verified

/-! The x86 byte writer is machine implementation detail, not emission API. -/

/--
error: Unknown identifier `Grass.ISA.X86.le32`
-/
#guard_msgs in
#check Grass.ISA.X86.le32

/-! Mutable allocation state is likewise outside the emission facade. -/

/--
error: Unknown identifier `Grass.Memory.AllocationRecord`
-/
#guard_msgs in
#check Grass.Memory.AllocationRecord

end Grass.Tests.Artifact.EmitFacade
