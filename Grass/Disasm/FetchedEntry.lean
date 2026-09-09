import Grass.Disasm.Entry
import Grass.ISA.X86.Execution.Fetch

/-! Connect exact imported bytes to an actual checked instruction-fetch event.
The caller supplies an executable backing and a real `FetchedSite` receipt;
this adapter checks its agreement with the requested original-file entry.
It does not infer OS loading, prior reachability, or execution of the fetched
instruction. A declared image base is explicit and must agree with RIP. -/
namespace Grass.Disasm.FetchedEntry

open Grass.Std.Logical Grass.Memory Grass.ISA.X86.Execution

inductive Error where
  | addressWrap
  | wrongRip
  | decode (error : DecodedSite.Error)
  | differentInstruction
deriving DecidableEq, Repr

/-- The exact imported entry and actual fetch share one canonical instruction.
The `entry` retains the checked parser success equation and original file slice. -/
structure Binding {input : Std.Logical.ByteArray} (entry : Entry.Entry input)
    (imageBase : Nat) {before : State} {after : MachineState}
    (fetch : FetchedSite before after) where
  imageFits : imageBase + entry.rva < 2^64
  atEntry : before.rip.toNat = imageBase + entry.rva
  decoded : DecodedSite before.rip entry.bytes
  sameInstruction : fetch.site.encoding = decoded.encoding

def check {input : Std.Logical.ByteArray} (entry : Entry.Entry input)
    (imageBase : Nat) {before : State} {after : MachineState}
    (fetch : FetchedSite before after) : Except Error (Binding entry imageBase fetch) :=
  if fits : imageBase + entry.rva < 2^64 then
    if atEntry : before.rip.toNat = imageBase + entry.rva then
      match DecodedSite.check before.rip entry.bytes with
      | .error error => .error (.decode error)
      | .ok decoded =>
        if same : fetch.site.encoding = decoded.encoding then
          .ok ⟨fits, atEntry, decoded, same⟩
        else .error .differentInstruction
    else .error .wrongRip
  else .error .addressWrap

/-- The observed instruction equals the prefix at the original file offset.
Both `take`s preserve the exact imported file-backed extent as an explicit bound. -/
theorem original_instruction {input entry imageBase before after}
    {fetch : FetchedSite before after} (binding : @Binding input entry imageBase before after fetch) :
    fetch.site.encoding.toBytes =
      ((input.toList.drop entry.fileOffset).take
        (Entry.fileBackedExtent entry.parsedSection - entry.localOffset)).take
          binding.decoded.encoding.size := by
  rw [binding.sameInstruction, ← binding.decoded.observed_prefix]
  exact congrArg (List.take binding.decoded.encoding.size) entry.originalBytes

/-- The actual checked fetch event records those original instruction bytes.
This is an execute-access observation, not a store-completion event. -/
theorem original_event {input entry imageBase before after}
    {fetch : FetchedSite before after} (binding : @Binding input entry imageBase before after fetch) :
    ∃ valid, after.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some (entry.bytes.take binding.decoded.encoding.size) ∧
      valid.event.status = .completed binding.decoded.encoding.size 0 := by
  obtain ⟨valid, appended, read, status⟩ := fetch.completed_event
  rw [binding.sameInstruction] at read status
  exact ⟨valid, appended, by simpa only [binding.decoded.observed_prefix] using read, status⟩

end Grass.Disasm.FetchedEntry
