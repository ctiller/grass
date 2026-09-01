import Grass.Emit
import Spikes.«2_Sort».Assembly

namespace Grass.Spikes.Sort

def parserWitness :
    SelectedProcessRequirementWitness (lineParserRequirement resources) :=
  Format.inlineParserWitness
    (format := lineStreamFormat)
    (scope := lineParserScope)
    (representation := lineParserRepresentation)

def sortVerified : VerifiedProgram spec := by
  verify_assembly plan
    deriving_standard_process_from spec
    using_requirement parserWitness
    using_component sortImplementationBinding
    with sortSource

def bytes : ByteArray := emitProgram sortVerified

end Grass.Spikes.Sort
