import Spikes.«4_Web_Server».Assembly

namespace Grass.Spikes.WebServer

def serverSourceClosure : ClosedAsmSource platformPlan :=
  ClosedAsmSource.close serverSource serverMacros serverStaticObjects serverImports

theorem serverSourceClosureComplete : SourceClosureComplete serverSourceClosure := by
  validate_source_closure

def serverExpandedSource : RawAsmSource platformPlan :=
  serverSourceClosure.expand

def serverExpandedListing : RawInstructionListing :=
  serverExpandedSource.listing

theorem serverExpandedListingExact :
    serverExpandedListing = serverSourceClosure.expand.listing := rfl

theorem serverExpansionExact :
    SourceElaboratesExactlyTo serverSourceClosure serverExpandedSource := by
  exact ClosedAsmSource.expansionExact serverSourceClosure

theorem serverExpansionHasNoGhostInstructions :
    EveryInstructionIsRaw serverExpandedSource :=
  serverSourceClosure.expansionRaw

theorem serverExpansionPreservesCancellationMetadata :
    ExpansionPreservesCancellationMasksSafePointsAndCustody
      serverSourceClosure serverExpandedSource :=
  serverSourceClosure.expansionPreservesCancellation
    serverMacrosCancellationTransparent

end Grass.Spikes.WebServer
