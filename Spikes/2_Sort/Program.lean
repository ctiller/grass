import Grass.Emit
import Spikes.«2_Sort».Bindings

namespace Grass.Spikes.Sort

def sortVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_component sortImplementationBinding
    using_source_closure sortSourceClosureComplete
    using_expansion sortExpansionExact
    with sortExpandedSource

def bytes : ByteArray := emitProgram sortVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  sortVerified.sound

end Grass.Spikes.Sort
