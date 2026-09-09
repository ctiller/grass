import Grass.Assembly.SourceResolve
import Grass.ISA.X86.Execution.FetchedEncoding

/-!
# Source outputs observed by an actual instruction fetch

This adapter joins one typed source-resolution output to one completed,
memory-backed x86 fetch. It records an affine image-placement relation supplied
by its caller, not a loader model: `SourceResolve.Result.codeBase` remains an
RVA, and only the stated equation relates it to an architectural address.

It does not establish that a PE loader created this relation, that a source
output is a particular binary entry point, or that the decoded instruction's
semantics executed.
-/

namespace Grass.Assembly.SourceFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

/-- One exact source output observed by one actual completed fetch. -/
structure SourceSite {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset)
    (before : State) (afterFetch : MachineState) where
  /-- The statically typed output selected from this exact resolved source. -/
  output : SourceResolve.Output source.splice source.symbols source.codeBase
  outputAt : source.outputs[output.index]? = some output
  /-- The actual execute access and canonical decode. -/
  fetch : FetchedSite before afterFetch
  /-- Source-code placement is an architectural CPU-virtual fetch, so its
  address equation below is not reused across address spaces. -/
  space : fetch.descriptor.space = .cpuVirtual
  /-- The actual completion observed precisely the selected source encoding. -/
  observed : fetch.run.complete.committed.observed = some output.encoding.toBytes
  /-- The placed allocation base used by the actual prepared fetch. -/
  base : MachineAddress
  baseExact : fetch.run.resolved.allocation.base = some base
  /-- Allocation-local offset at which the image code region begins. -/
  codeRootOffset : Nat
  /-- The caller-supplied loaded-image base in the same natural address view. -/
  loadedImageBase : Nat
  /-- An affine placement equation, not a loader-existence claim. -/
  placementExact : base.toNat + codeRootOffset = loadedImageBase + source.codeBase
  /-- The actual fetch range begins at the selected source output's translated
  image-relative offset. -/
  descriptorStart : fetch.descriptor.range.start = codeRootOffset +
    ByteLayout.offset source.splice.finalSizes output.index

namespace SourceSite

/-- The canonical fetched encoding is exactly the selected source encoding.
Both sides are identified through their decoder laws over the same observed
bytes; no encoding is selected by an opaque equality witness. -/
theorem encoding_exact {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch : MachineState} (site : SourceSite source before afterFetch) :
    site.fetch.site.encoding = site.output.encoding := by
  exact site.fetch.encoding_of_observation site.output.encoding
    (by simpa using site.output.encodingDecodes []) site.observed

/-- The actual architectural RIP is the loaded-image base plus the selected
source RVA. The proof obtains RIP only from the completed fetch placement and
the resolved descriptor's containment certificate. -/
theorem rip_exact {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch : MachineState} (site : SourceSite source before afterFetch) :
    before.rip.toNat = site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes site.output.index := by
  obtain ⟨base, basePlaced, fits, ripAtStart⟩ := FetchedSite.placement site.fetch
  have baseEq : base = site.base :=
    Option.some.inj (basePlaced.symm.trans site.baseExact)
  subst base
  have descriptorPositive : 0 < site.fetch.descriptor.range.size := by
    rw [site.fetch.extent_exact]
    exact site.fetch.site.lengthBound.1
  have descriptorContained := site.fetch.run.resolved.coordinates.withinView
  have descriptorStartBound : site.fetch.descriptor.range.start <
      site.fetch.run.resolved.allocation.extent.stop := by
    unfold ByteRange.Contains at descriptorContained
    unfold ByteRange.stop at descriptorContained ⊢
    omega
  rw [← ripAtStart, toNat_addressOf fits descriptorStartBound,
    site.descriptorStart, SourceResolve.sourceOffset]
  calc
    site.base.toNat + (site.codeRootOffset +
        ByteLayout.offset source.splice.finalSizes site.output.index) =
        (site.base.toNat + site.codeRootOffset) +
          ByteLayout.offset source.splice.finalSizes site.output.index := by omega
    _ = (site.loadedImageBase + source.codeBase) +
          ByteLayout.offset source.splice.finalSizes site.output.index := by
      rw [site.placementExact]
    _ = site.loadedImageBase + (source.codeBase +
          ByteLayout.offset source.splice.finalSizes site.output.index) := by omega

/-- The actual fetch event records precisely the selected source encoding's
bytes. This is an execution event for the supplied fetch receipt; it says
nothing about source-level instruction semantics. -/
theorem completed_event {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch : MachineState} (site : SourceSite source before afterFetch) :
    ∃ valid, afterFetch.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some site.output.encoding.toBytes ∧
      valid.event.status = .completed site.output.encoding.size 0 := by
  obtain ⟨valid, appended, read, status⟩ := FetchedSite.completed_event site.fetch
  have encoding := site.encoding_exact
  refine ⟨valid, appended, ?_, ?_⟩
  · rw [encoding] at read
    exact read
  · rw [encoding] at status
    exact status

end SourceSite
end Grass.Assembly.SourceFetch
