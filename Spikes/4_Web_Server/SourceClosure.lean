import Spikes.«4_Web_Server».Assembly

namespace Grass.Spikes.WebServer

def serverSourceClosure : ClosedAsmSource platformPlan :=
  ClosedAsmSource.closeWithFragmentHierarchy
    serverSource serverMacros serverFragmentHierarchy
    serverStaticObjects serverImports

theorem serverSourceClosureComplete : SourceClosureComplete serverSourceClosure := by
  validate_hierarchical_source_closure

theorem serverSourceClosureOwnsEveryHelperBody :
    EverySelectedOperationHasExactlyOneLocalConstructorBody
      serverMacros serverFragmentHierarchy :=
  serverFragmentHierarchyComplete

def serverExpandedSource : RawAsmSource platformPlan :=
  serverSourceClosure.expand

def serverExpandedListing : RawInstructionListing :=
  serverExpandedSource.listing

theorem serverExpandedListingExact :
    serverExpandedListing = serverSourceClosure.expand.listing := rfl

theorem serverExpansionExact :
    SourceElaboratesExactlyTo serverSourceClosure serverExpandedSource := by
  exact ClosedAsmSource.hierarchicalExpansionExact
    serverSourceClosure serverFragmentExpansionExact

theorem serverExpansionHasNoGhostInstructions :
    EveryInstructionIsRaw serverExpandedSource :=
  serverSourceClosure.expansionRaw

theorem serverExpansionPreservesCancellationMetadata :
    ExpansionPreservesCancellationMasksSafePointsAndCustody
      serverSourceClosure serverExpandedSource :=
  serverSourceClosure.expansionPreservesCancellation
    serverMacrosCancellationTransparent

end Grass.Spikes.WebServer
