import Grass.ISA.X86.Execution.Fetch

/-! Derive instruction selection from an actual fetch and a canonical encoder
round trip. Source adapters supply the encoder law, never a second decoder. -/

namespace Grass.ISA.X86.Execution.FetchedSite

open Grass.Memory

/-- The canonical round trip identifies the instruction from the bytes actually
observed by this execute access. The fetch consumes the entire instruction. -/
theorem encoding_of_observation {before : State} {after : MachineState}
    (fetch : FetchedSite before after) (encoding : InsnEncoding)
    (canonical : decodeInsn encoding.toBytes = .ok (encoding, []))
    (observed : fetch.run.complete.committed.observed = some encoding.toBytes) :
    fetch.site.encoding = encoding := by
  have bytes := Option.some.inj (fetch.observed_exact.symm.trans observed)
  have decoded := (congrArg decodeInsn fetch.site.bytesExact).symm.trans fetch.site.decoded
  rw [fetch.noTrailing, List.append_nil, bytes] at decoded
  exact congrArg Prod.fst (Except.ok.inj (decoded.symm.trans canonical))

end Grass.ISA.X86.Execution.FetchedSite
