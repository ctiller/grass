import Spikes.«2_Sort».Assembly

namespace Grass.Spikes.Sort

def sortSourceClosure : ClosedAsmSource plan :=
  ClosedAsmSource.close sortSource sortConstructorClosure sortStaticObjects sortImports

theorem sortSourceClosureComplete : SourceClosureComplete sortSourceClosure := by
  validate_source_closure

def sortExpandedSource : RawAsmSource plan := sortSourceClosure.expand

def sortExpandedListing : RawInstructionListing := sortExpandedSource.listing

theorem sortExpandedListingExact :
    sortExpandedListing = sortSourceClosure.expand.listing := rfl

theorem sortExpansionExact :
    SourceElaboratesExactlyTo sortSourceClosure sortExpandedSource := by
  exact ClosedAsmSource.expansionExact sortSourceClosure

def sortAlgorithmScope : SourceScope sortExpandedSource :=
  SourceScope.closedRegion `sort_pass `sort_complete

def lineDescRepresentation : RepresentationPlan sortAlgorithmScope :=
  StableSort.physicalLineDescRepresentation PhysicalLineDesc

def sortRequirement : ProgramRequirement spec :=
  ProgramRequirement.named spec `stable_sort

theorem sortSourceRefinesModel :
    AssemblyRefinesImplementation
      sortAlgorithmScope lineDescRepresentation stableSortModel sortExpandedSource := by
  verify_asm_model

theorem stableSortContractConnects :
    ComponentContractRefinesRequirement stableSortContract sortRequirement := by
  exact spec.stableSortRequirement format order

def sortImplementationBinding :
    ImplementationBinding sortExpandedSource sortRequirement := {
  sourceScope := sortAlgorithmScope
  componentContract := stableSortContract
  implementation := stableSortModel
  representation := lineDescRepresentation
  model := { realizes := stableSortModelCorrect }
  assembly := sortSourceRefinesModel
  connects := stableSortContractConnects
}

def sortBindingMutationExpectations :
    BindingMutationExpectations sortImplementationBinding :=
  #[.sourceEdit `merge_body .assemblyRefinement,
    .representationEdit `line_descriptor .assemblyRefinement,
    .modelContractEdit `stable_sort .contractConnection]

theorem sortBindingMutationLocality :
    BindingMutationExpectations.Hold sortBindingMutationExpectations := by
  check_binding_mutations

theorem sourceImplementsDriver :
    AssemblyImplements processRealization plan sortExpandedSource := by
  verify_asm

theorem stableSortFunctionImplementation :
    SerialFunctionImplementation stableSortFunctionContract := by
  exact extract_serial_function sortImplementationBinding sourceImplementsDriver

end Grass.Spikes.Sort
