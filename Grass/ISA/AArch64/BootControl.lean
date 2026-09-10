import Grass.ISA.AArch64.Source
import Grass.Platform.BareMetal.AArch64BootFetch

/-!
First-boot A64 body decoding from the actual shared execute-read observation.
The supplied boot admission is for a fresh physical-RAM snapshot, not an arbitrary
later machine. The selected instruction serialization is explicitly little-endian;
hardware execution-state/translation applicability still belongs to the platform.

This joins an actual fetch with a body projection. SVC still needs profile trap
checks and exception entry; no Linux occurrence or full machine step is produced.
-/
namespace Grass.ISA.AArch64.BootControl

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Grammar
open Grass.Platform.BareMetal Grass.Platform.BareMetal.BootMemory

/-- A caller explicitly selects the supported instruction-byte interpretation.
This selection is not evidence that firmware established an A64 execution regime. -/
inductive Convention where
  | a64LittleEndian
deriving DecidableEq, Repr

variable {map : PhysicalMap} {context : ContextId} {before : MachineState}
  {admission : Admission map context before} {id : AllocId} {range : ByteRange}
  {policy : BootFetch.Policy} {entry : Entry admission id range}

/-- Failure after a successful fetch. The enclosing Result retains that fetch
and its reached memory/event even for unsupported instructions. -/
inductive DecodeFailure where
  | needMore (hint : Option Nat)
  | invalid (error : ParseError)
  | trailing
  | unsupported (word : BitVec 32)

/-- Body outcome bound to the exact bytes of this completed execute read. -/
structure Decoded (fetch : AArch64BootFetch.Word policy entry) (cpu : Cpu) where
  outcome : BodyOutcome
  body : SourceBodyStep (Vec.fromList fetch.read.bytes) cpu outcome
  noTrailing : body.source.rest = Vec.empty

/-- Decode only the actual observation; neither bytes nor output CPU are supplied
by the caller. SVC is represented by its request outcome, never normal next. -/
def decode (convention : Convention) (fetch : AArch64BootFetch.Word policy entry)
    (cpu : Cpu) : Except DecodeFailure (Decoded fetch cpu) :=
  match convention with
  | .a64LittleEndian =>
    match readSource (Vec.fromList fetch.read.bytes) with
    | .needMore hint => .error (.needMore hint)
    | .invalid error => .error (.invalid error)
    | .done source _ =>
      if noTrailing : source.rest = Vec.empty then
        match decoded : CompareZero.decode source.word with
        | some instruction =>
          .ok ⟨.next (instruction.execute cpu),
            ⟨source, .cbz instruction decoded⟩, noTrailing⟩
        | none =>
          match decoded : SupervisorCall.decode source.word with
          | some immediate =>
            .ok ⟨.supervisor immediate, ⟨source, .svc immediate decoded⟩, noTrailing⟩
          | none => .error (.unsupported source.word)
      else .error .trailing

/-- The same completed read remains present on success AND decoding failure. -/
inductive Result (policy : BootFetch.Policy) (entry : Entry admission id range) (cpu : Cpu) where
  | pcMismatch (different : cpu.pc ≠ entry.pc)
  | fetchFailure (reason : AArch64BootFetch.Failure policy entry)
  | fetched (fetch : AArch64BootFetch.Word policy entry) (pcExact : cpu.pc = entry.pc)
      (body : Except DecodeFailure (Decoded fetch cpu))

/-- Run the existing fetch once, retain its failures, then decode that same read. -/
def run (convention : Convention) (policy : BootFetch.Policy)
    (entry : Entry admission id range) (cpu : Cpu) : Result policy entry cpu :=
  if pcExact : cpu.pc = entry.pc then
    match AArch64BootFetch.fetchWord policy entry with
    | .error reason => .fetchFailure reason
    | .ok fetch => .fetched fetch pcExact (decode convention fetch cpu)
  else .pcMismatch pcExact

theorem run_fetchFailure (convention : Convention) (cpu : Cpu)
    (pcExact : cpu.pc = entry.pc) (reason : AArch64BootFetch.Failure policy entry)
    (failed : AArch64BootFetch.fetchWord policy entry = .error reason) :
    run convention policy entry cpu = .fetchFailure reason := by
  simp [run, pcExact, failed]

theorem run_fetched (convention : Convention) (cpu : Cpu)
    (pcExact : cpu.pc = entry.pc) (fetch : AArch64BootFetch.Word policy entry)
    (fetched : AArch64BootFetch.fetchWord policy entry = .ok fetch) :
    run convention policy entry cpu = .fetched fetch pcExact (decode convention fetch cpu) := by
  simp [run, pcExact, fetched]

/-- A successful packet retains the shared parser's exact observation equation. -/
theorem Decoded.parsed {fetch : AArch64BootFetch.Word policy entry} {cpu : Cpu}
    (decoded : Decoded fetch cpu) :
    Grass.Artifact.Binary.takeLittleEndian 4 (Vec.fromList fetch.read.bytes) =
      .done decoded.body.source.word Vec.empty := by
  rw [← decoded.noTrailing]
  exact decoded.body.source.parsed

/-- Actual post-fetch machine state is the shared receipt's endpoint, even if the body
is unsupported. This does not assert that SVC's system effects have executed. -/
def completedFetchState {cpu : Cpu} (result : Result policy entry cpu) : Option MachineState :=
  match result with
  | .fetched fetch _ _ => some fetch.read.after
  | _ => none

/-- The actual execute-read observation cannot be replaced by independent bits. -/
theorem fetched_observation (fetch : AArch64BootFetch.Word policy entry) :
    fetch.read.run.complete.committed.observed = some fetch.read.bytes :=
  fetch.read.observed_exact

/-- Every decoded outcome keeps the source/body theorem's actual condition or
SVC request. No external postcondition is chosen at this boundary. -/
theorem Decoded.cases {fetch : AArch64BootFetch.Word policy entry} {cpu : Cpu}
    (decoded : Decoded fetch cpu) :
    (∃ instruction : CompareZero, instruction.encode = decoded.body.source.word ∧
      decoded.outcome = .next (instruction.execute cpu) ∧
      ((instruction.isZero cpu = true ∧
        (instruction.execute cpu).pc = cpu.pc + instruction.offset) ∨
       (instruction.isZero cpu = false ∧ (instruction.execute cpu).pc = cpu.pc + 4))) ∨
    (∃ immediate, SupervisorCall.encode immediate = decoded.body.source.word ∧
      decoded.outcome = .supervisor immediate) := decoded.body.cases

end Grass.ISA.AArch64.BootControl
