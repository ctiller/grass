import Grass.Op.Step

/-!
# Placement facts retained by prepared accesses

These lemmas expose the two numeric-placement checks already performed by
`prepareAccess`. They make no claim about physical aliases or mappings beyond
the allocation and address selected by that successful preparation.
-/

namespace Grass.Op

open Grass.Core Grass.Memory

/-- A prepared access whose resolved allocation has a numeric base fits below
the address-space bound and names that base plus its range start. -/
theorem prepared_base_fits_and_address
    {state : MemoryState} {d : AccessDescriptor}
    {resolved : state.ResolvedAccess d.provenance d.range} {base : BitVec 64}
    (prepared : prepareAccess state d = .ok resolved)
    (hasBase : resolved.allocation.base = some base) :
    FitsAllocation base resolved.allocation.extent.stop ∧
      d.address = .numeric (addressOf base d.range.start) := by
  unfold prepareAccess at prepared
  repeat' split at prepared
  all_goals try contradiction
  rename_i access resolvedAccess dedicated fitsGuard addressGuard permission intent initialization
  cases Except.ok.inj prepared
  constructor
  · simpa [hasBase] using fitsGuard
  · simpa [hasBase] using addressGuard

end Grass.Op
