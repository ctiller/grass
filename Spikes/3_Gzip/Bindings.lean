import Spikes.«3_Gzip».Assembly

namespace Grass.Spikes.Gzip

def gzipSourceClosure : ClosedAsmSource platformPlan :=
  ClosedAsmSource.close gzipSource .empty gzipStaticObjects gzipImports

theorem gzipSourceClosureComplete : SourceClosureComplete gzipSourceClosure := by
  validate_source_closure

def gzipExpandedSource : RawAsmSource platformPlan := gzipSourceClosure.expand

def gzipExpandedListing : RawInstructionListing := gzipExpandedSource.listing

theorem gzipExpandedListingExact :
    gzipExpandedListing = gzipSourceClosure.expand.listing := rfl

theorem gzipExpansionExact :
    SourceElaboratesExactlyTo gzipSourceClosure gzipExpandedSource := by
  exact ClosedAsmSource.expansionExact gzipSourceClosure

def codecAlgorithmScope : SourceScope gzipExpandedSource :=
  SourceScope.closedRegion `process_block `process_block_return

def fixed32KRepresentation : RepresentationPlan codecAlgorithmScope :=
  Std.Zlib.Fixed32K.machineRepresentation codecPlan GzipMachineState

def gzipCodecRequirement : ProgramRequirement spec :=
  ProgramRequirement.named spec `gzip_fixed32k

theorem gzipSourceRefinesModel :
    AssemblyRefinesImplementation
      codecAlgorithmScope fixed32KRepresentation fixed32KModel gzipExpandedSource := by
  verify_asm_model

theorem fixed32KContractConnects :
    ComponentContractRefinesRequirement fixed32KContract gzipCodecRequirement := by
  exact spec.fixed32KRequirement codecPlan

def gzipImplementationBinding :
    ImplementationBinding gzipExpandedSource gzipCodecRequirement := {
  sourceScope := codecAlgorithmScope
  componentContract := fixed32KContract
  implementation := fixed32KModel
  representation := fixed32KRepresentation
  model := { realizes := fixed32KModelCorrect }
  assembly := gzipSourceRefinesModel
  connects := fixed32KContractConnects
}

def gzipBindingMutationExpectations :
    BindingMutationExpectations gzipImplementationBinding :=
  #[.sourceEdit `codec_body .assemblyRefinement,
    .representationEdit `codec_arena .assemblyRefinement,
    .modelContractEdit `fixed32k .contractConnection]

theorem gzipBindingMutationLocality :
    BindingMutationExpectations.Hold gzipBindingMutationExpectations := by
  check_binding_mutations

theorem sourceImplementsDriver :
    AssemblyImplements processRealization platformPlan gzipExpandedSource := by
  verify_asm

theorem fixed32KFunctionImplementation :
    SerialFunctionImplementation fixed32KFunctionContract := by
  exact extract_serial_function gzipImplementationBinding sourceImplementsDriver

end Grass.Spikes.Gzip
