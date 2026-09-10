import Grass.Op.CallProtocolSettlement
import Tests.Platform.Win32MatchedReturn

namespace Grass.Tests.CallProtocolSettlement

open Grass.Op Grass.Tests.Win32MatchedReturn Grass.Tests.Win32WriteFile

/-- The generic settlement law applies to the existing actual-return fixture. -/
example : CallProtocol.callerPending returnedState record.caller = false :=
  CallProtocol.return?_callerPending_false matched.ran

end Grass.Tests.CallProtocolSettlement
