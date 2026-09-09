import Grass.Frontend.Source
import Tests.Frontend.Target
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Frontend

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def otherSpec := SpecProcess.ofRelational
  (Console.writeLineContract resources ("Other" : Specification.TextLine) policy)
def otherProjection : TargetProjection otherSpec .win10X64 :=
  TargetProjection.win10ConsoleText (newline := .crlf) (encoding := .utf8)
    (outcome := targetPolicy)
def otherPlan : PlatformPlan otherSpec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly otherProjection

example : spec.driverBoundary.requirements = otherSpec.driverBoundary.requirements := rfl
example (_value : MachineSource plan) : True := by
  fail_if_success have : MachineSource otherPlan := _value
  trivial

-- Fixture ingress only: the production command elaborator captures its own
-- input range and passes the actually elaborated table to the same producer.
def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

theorem source_present : (MachineSource.ofHello? plan authored statics).isSome = true := by
  decide +kernel

def source : MachineSource plan := (MachineSource.ofHello? plan authored statics).get source_present

theorem source_table_exact : source.table = statics := by
  exact (MachineSource.ofHello?_inputs (Option.some_get source_present).symm).2

theorem source_authored_exact : source.authored = authored := by
  exact (MachineSource.ofHello?_inputs (Option.some_get source_present).symm).1

-- Invalid source is rejected before any artifact can be supplied.
example : (MachineSource.ofHello? plan [] statics).isSome = false := by decide

end Grass.Tests.Frontend
