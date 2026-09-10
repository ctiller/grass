import Grass.Platform.BareMetal.Target.AArch64
import Grass.Target.Platform

/-!
# The bare-metal PL011 platform

Assembles `Target.AArch64`'s ISA-specific `Admits`/`entry`/`decode`/
`encodeReturn` with `Grass.Platform.BareMetal`'s shared `Environment`/
`Responds` into `platformAArch64`, the first bare-metal
`Grass.Target.Platform` instance: the first whose native calls come from the
`CallTarget.mmioLoad`/`mmioStore` device-window mechanism rather than a
`syscall`/`svc`/import-thunk call site.
-/

namespace Grass.Platform.BareMetal.Target

/-- The bare-metal AArch64/PL011 platform. -/
def platformAArch64 :
    Grass.Target.Platform Grass.ISA.AArch64.isa Grass.Platform.BareMetal.uartDomain where
  Environment := Grass.Platform.BareMetal.Environment
  Admits := Grass.Platform.BareMetal.Target.AArch64.Admits
  entry := Grass.Platform.BareMetal.Target.AArch64.entry
  decode := Grass.Platform.BareMetal.Target.AArch64.decode
  Responds := Grass.Platform.BareMetal.Responds
  encodeReturn := Grass.Platform.BareMetal.Target.AArch64.encodeReturn

/-- Every `txWrite` `platformAArch64.Responds` accepts extends the
transcript by exactly the stored byte — the ISA-independent honesty theorem
`Grass.Platform.BareMetal.transcript_append`, restated at the platform-record
level a Hello World adequacy proof actually consumes. -/
theorem platformAArch64_txWrite_transcript_append
    {env env' : Grass.Platform.BareMetal.Environment} {b : UInt8}
    (responds : platformAArch64.Responds env (.txWrite b) true env') :
    env'.txTranscript = env.txTranscript ++ [b] :=
  Grass.Platform.BareMetal.transcript_append responds

end Grass.Platform.BareMetal.Target
