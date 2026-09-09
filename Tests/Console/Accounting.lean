import Grass.Console.Accounting

namespace Grass.Tests.Console.Accounting

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Console.Behavior Grass.Console.Accounting

/-- The zero-step initial history has the zero committed prefix. -/
theorem initial_accounting (payload : Vec Byte) :
    emittedBytes (initial payload).path.events = Vec.empty := by
  rfl

/-- A one-step advance to any positive cut publishes its exact prefix. -/
theorem cut_accounting (payload : Vec Byte) (cut : OutputCut payload)
    (_positive : 0 < cut.offset) :
    emittedBytes (pendingAt payload cut).path.events = cut.emitted := by
  simpa [pendingAt_state payload cut, committed] using history_accounting (pendingAt payload cut)

/-- The interaction's decreasing rank rules out an infinite step continuation. -/
theorem no_infinite {payload : Vec Byte} {state : State payload} {graph : Unit}
    {events : List Event} (continuation : (system payload).InfiniteContinuation state graph events) : False :=
  no_infinite_continuation continuation

end Grass.Tests.Console.Accounting
