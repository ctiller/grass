import Grass.Assembly.SourceUnwind
import Tests.Assembly.SourceResolve

namespace Grass.Tests.Assembly.SourceUnwind
open Grass.Assembly
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The existing typed ABI constructor accepts metadata derived from the actual
authored Hello prologue. This does not execute an unwind or load an image. -/
def actual : Option Bool := do
  let body ← (SourceInput.extractHelloSourceChars SourceResolve.authored).toOption
  let frame ← SourceFrame.derive? body
  let prologue ← SourcePrologue.generate? frame
  pure (SourceUnwind.prepare? prologue).isSome

example : actual = some true := by decide +kernel
end Grass.Tests.Assembly.SourceUnwind
