import Grass.Platform.WASI.Target
import Grass.Target.Safety
import Spikes.«1_Hello_World».Spec

/-!
# Hello World on Wasm32 under WASI Preview 1

The first end-to-end consumer of the machine seam: a concrete
`Grass.ISA.Wasm.Target.Module`, run under `Grass.Platform.WASI.Target.
platform`, whose machine-tier `Adequate` obligation is discharged by hand
through `Grass.Target.Machine.adequate_of_invariant`.

The machine is deterministic in the program and branches only on the
environment's answer, so the inductive invariant is a finite enumeration of
reachable *phases* (`Reach`): the eight instruction points of `_start`, the
one point where the program is awaiting `fd_write`, and `halted`. Nothing
here is an approximation — `Reach` is closed under `Machine.Step` and every
one of its states has a successor or is halted, which is exactly memory and
control safety plus platform-call well-formedness for this program.

What adequacy does *not* say: it is a safety-and-progress statement about the
machine, not a refinement of `Grass.Spikes.HelloWorld.spec`'s accepted
traces. `eventOf` relabels service events into the specification's audit
vocabulary, but `Adequate` never looks at `SpecRoot.accepts`; a program that
printed nothing would satisfy this theorem too. The trace-level obligation is
`PortableProgramCertificate`'s, not this module's.
-/

namespace Grass.Programs.HelloWorld.Wasi

open Grass.Spikes.HelloWorld

open Grass.ISA.Wasm (Value ValType FuncType)
open Grass.ISA.Wasm.Target
open Grass.Service
open Grass.Target
open Grass.Platform.Hosted (Environment)
open Grass.Artifact.Binary (writeU32LE)

/-! ## Linear memory layout

Three regions, all inside the module's single 64 KiB page: the one-entry
`ciovec` array `fd_write` is handed, the `u32` it reports its accepted byte
count into, and the message bytes themselves. -/

/-- Address of the one-entry `ciovec` array. -/
def iovAddr : Nat := 0

/-- Address of the `u32` `fd_write` writes its byte count to. -/
def nwrittenAddr : Nat := 8

/-- Address of the message bytes. -/
def messageAddr : Nat := 16

/-- UTF-8 of `Grass.Spikes.HelloWorld.message`, newline-terminated. Spelled
as bytes rather than derived from the `TextLine` so that every step of the
machine reduces by `rfl` in the kernel. -/
def messageBytes : List UInt8 :=
  [72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33, 10]

/-- The `ciovec` entry: `(buf_ptr, buf_len)`, little-endian `u32` each. -/
def iovBytes : List UInt8 :=
  writeU32LE (UInt32.ofNat messageAddr) ++ writeU32LE (UInt32.ofNat messageBytes.length)

/-! ## The module -/

/-- `fd_write(fd, iovs, iovs_len, nwritten) -> errno`. -/
def fdWriteType : FuncType := ⟨[.i32, .i32, .i32, .i32], [.i32]⟩

/-- `proc_exit(rval)`, no return. -/
def procExitType : FuncType := ⟨[.i32], []⟩

/-- `_start()`, no arguments, no results. -/
def startType : FuncType := ⟨[], []⟩

/-- Index of `_start` in the joint import/function index space. -/
def startIndex : Nat := 2

/-- `fd_write`'s first argument: the stdout file descriptor. -/
def fdStdout : BitVec 32 := 1

/-- `fd_write`'s second argument. -/
def iovOperand : BitVec 32 := BitVec.ofNat 32 iovAddr

/-- `fd_write`'s third argument: one `ciovec` entry. -/
def iovCount : BitVec 32 := 1

/-- `fd_write`'s fourth argument. -/
def nwrittenOperand : BitVec 32 := BitVec.ofNat 32 nwrittenAddr

/-- `proc_exit`'s only argument. -/
def exitOperand : BitVec 32 := 0

/-- `_start`: offer the whole line to stdout, discard the `errno`, exit. The
`errno` is dropped deliberately — the outcome distinction the specification
draws lives in the spec's own trace, not in this program's exit status. -/
def startBody : List Instr :=
  [ .i32Const fdStdout
  , .i32Const iovOperand
  , .i32Const iovCount
  , .i32Const nwrittenOperand
  , .call 0
  , .drop
  , .i32Const exitOperand
  , .call 1 ]

/-- The assembled program. `start := none`: the entry point is the `_start`
export, resolved by `Grass.ISA.Wasm.Target.initial` from the platform's
`InitialContext`, which is WASI's own convention. -/
def program : Module where
  types := [fdWriteType, procExitType, startType]
  imports :=
    [ ⟨Grass.Platform.WASI.Target.wasiModuleName, "fd_write", 0⟩
    , ⟨Grass.Platform.WASI.Target.wasiModuleName, "proc_exit", 1⟩ ]
  functions := [⟨2, [], startBody⟩]
  memoryMinPages := 1
  globals := []
  exports := [⟨Grass.Platform.WASI.Target.startExport, startIndex⟩]
  data := [⟨iovAddr, iovBytes⟩, ⟨messageAddr, messageBytes⟩]
  start := none

/-! ## The machine states this program reaches -/

/-- The WASI platform record this program runs under. -/
abbrev platform := Grass.Platform.WASI.Target.platform

/-- The machine state type for this program. -/
abbrev MachineState :=
  Machine.State Grass.ISA.Wasm.isa Grass.Platform.Hosted.domain platform

/-- The entry context, which does not depend on the environment. -/
def ctx : InitialContext :=
  { startExport := Grass.Platform.WASI.Target.startExport, initialMemory := [] }

/-- Linear memory at instantiation: zero-filled, with the module's two data
segments installed. -/
def mem0 : Nat → Option UInt8 := buildMemory program ctx

/-- A `_start` activation at instruction `pc` with operand stack `stack`.
`_start` has no locals and this program opens no block, so the frame's locals
and label stack are empty at every reachable point. -/
def mkState (mem : Nat → Option UInt8) (pc : Nat) (stack : List Value) :
    Grass.ISA.Wasm.Target.State :=
  { module := program
    memory := mem
    memoryLength := program.memoryBytes
    globals := []
    frames := [⟨startIndex, pc, [], stack, []⟩] }

/-- The native call `_start` makes at instruction 4. -/
def fdWriteCall : NativeCall :=
  { importIndex := 0
    moduleName := Grass.Platform.WASI.Target.wasiModuleName
    fieldName := "fd_write"
    args := [.i32 fdStdout, .i32 iovOperand, .i32 iovCount, .i32 nwrittenOperand]
    read := fun addr len => readBytes mem0 addr len }

/-- How the machine resumes once the environment answers `fd_write`: the
answer's memory writes applied, masked back to the declared linear memory. -/
def fdWriteResume : NativeReturn → Grass.ISA.Wasm.Target.State := fun ret =>
  { module := program
    memory := fun a =>
      if a < program.memoryBytes then
        ret.writes.foldl (fun mem (addr, bytes) => writeBytes mem addr bytes) mem0 a
      else none
    memoryLength := program.memoryBytes
    globals := []
    frames := [⟨startIndex, 5, [], ret.results.reverse ++ [], []⟩] }

/-- The native call `_start` makes at instruction 7, from a memory the
environment's `fd_write` answer may already have written into. -/
def procExitCall (mem : Nat → Option UInt8) : NativeCall :=
  { importIndex := 1
    moduleName := Grass.Platform.WASI.Target.wasiModuleName
    fieldName := "proc_exit"
    args := [.i32 exitOperand]
    read := fun addr len => readBytes mem addr len }

/-- `proc_exit` is terminal, so this resumption is never taken; it exists
only because `StepOutcome.external` carries one. -/
def procExitResume (base : Nat → Option UInt8) :
    NativeReturn → Grass.ISA.Wasm.Target.State := fun ret =>
  { module := program
    memory := fun a =>
      if a < program.memoryBytes then
        ret.writes.foldl (fun mem (addr, bytes) => writeBytes mem addr bytes) base a
      else none
    memoryLength := program.memoryBytes
    globals := []
    frames := [⟨startIndex, 8, [], ret.results.reverse ++ [], []⟩] }

/-- The portable request `fd_write` decodes to. -/
def writeRequest : Grass.Platform.Hosted.domain.Request :=
  .inl (.inl (.write .stdout messageBytes))

/-- The portable request `proc_exit` decodes to. -/
def exitRequest : Grass.Platform.Hosted.domain.Request :=
  .inl (.inl (.exit (UInt32.ofNat 0)))

-- Every equation below reduces a closed machine state in the kernel; the
-- byte-at-a-time reduction of linear memory is deeper than the default.
set_option maxRecDepth 100000

/-! ## The concrete transition table

Each equation reduces in the kernel: `Grass.ISA.Wasm.Target.step` is a total
function of the state, and every state below is closed. -/

theorem step0 :
    Grass.ISA.Wasm.isa.step (mkState mem0 0 []) =
      .internal (mkState mem0 1 [.i32 fdStdout]) := rfl

theorem step1 :
    Grass.ISA.Wasm.isa.step (mkState mem0 1 [.i32 fdStdout]) =
      .internal (mkState mem0 2 [.i32 iovOperand, .i32 fdStdout]) := rfl

theorem step2 :
    Grass.ISA.Wasm.isa.step (mkState mem0 2 [.i32 iovOperand, .i32 fdStdout]) =
      .internal (mkState mem0 3 [.i32 iovCount, .i32 iovOperand, .i32 fdStdout]) := rfl

theorem step3 :
    Grass.ISA.Wasm.isa.step (mkState mem0 3 [.i32 iovCount, .i32 iovOperand, .i32 fdStdout]) =
      .internal (mkState mem0 4
        [.i32 nwrittenOperand, .i32 iovCount, .i32 iovOperand, .i32 fdStdout]) := rfl

theorem step4 :
    Grass.ISA.Wasm.isa.step (mkState mem0 4
        [.i32 nwrittenOperand, .i32 iovCount, .i32 iovOperand, .i32 fdStdout]) =
      .external fdWriteCall fdWriteResume := rfl

theorem step5 (mem : Nat → Option UInt8) (v : Value) :
    Grass.ISA.Wasm.isa.step (mkState mem 5 [v]) = .internal (mkState mem 6 []) := rfl

theorem step6 (mem : Nat → Option UInt8) :
    Grass.ISA.Wasm.isa.step (mkState mem 6 []) =
      .internal (mkState mem 7 [.i32 exitOperand]) := rfl

theorem step7 (mem : Nat → Option UInt8) :
    Grass.ISA.Wasm.isa.step (mkState mem 7 [.i32 exitOperand]) =
      .external (procExitCall mem) (procExitResume mem) := rfl

/-- The loaded state is `_start` at its first instruction: the export name
resolved to index `2`, not guessed. -/
theorem initialState (env : Environment) :
    Grass.ISA.Wasm.isa.initial program (platform.entry env) = mkState mem0 0 [] := rfl

/-- The `fd_write` call site decodes: both the `ciovec` entry and the buffer
it names are inside the module's linear memory, so the platform realizes the
call rather than leaving the machine stuck. -/
theorem decodeWrite : platform.decode fdWriteCall = some writeRequest := rfl

/-- The `proc_exit` call site decodes, whatever the environment wrote into
linear memory when it answered `fd_write`. -/
theorem decodeExit (mem : Nat → Option UInt8) :
    platform.decode (procExitCall mem) = some exitRequest := rfl

theorem writeNotTerminal : ¬ Grass.Platform.Hosted.domain.Terminal writeRequest := by
  intro h
  exact h

theorem exitTerminal : Grass.Platform.Hosted.domain.Terminal exitRequest := trivial

/-! ## Step inversion

Three lemmas turn "the ISA step at this state is *this*" into "the machine
step out of this state lands *there*". They are the whole of the case
analysis a block verifier would generate. -/

/-- Out of a running state whose ISA step is a known internal transition,
every machine step lands in the named state. -/
theorem next_of_internal {env0 env : Environment} {s n : Grass.ISA.Wasm.Target.State}
    (known : Grass.ISA.Wasm.isa.step s = .internal n)
    {choice : Machine.Choice Grass.Platform.Hosted.domain}
    {event : Event Grass.Platform.Hosted.domain} {next : MachineState}
    (st : Machine.Step platform ⟨env0, env, .running s⟩ choice event next) :
    next = ⟨env0, env, .running n⟩ := by
  cases st with
  | internal h => rw [known] at h; injection h with h; subst h; rfl
  | halt h => simp [known] at h
  | call h _ _ => simp [known] at h
  | exit h _ _ => simp [known] at h

/-- Out of a running state whose ISA step is a known native call the platform
decodes to a non-terminal request, every machine step lands in the matching
awaiting state. -/
theorem next_of_call {env0 env : Environment} {s : Grass.ISA.Wasm.Target.State}
    {c : NativeCall} {resume : NativeReturn → Grass.ISA.Wasm.Target.State}
    {request : Grass.Platform.Hosted.domain.Request}
    (known : Grass.ISA.Wasm.isa.step s = .external c resume)
    (dec : platform.decode c = some request)
    (continues : ¬ Grass.Platform.Hosted.domain.Terminal request)
    {choice : Machine.Choice Grass.Platform.Hosted.domain}
    {event : Event Grass.Platform.Hosted.domain} {next : MachineState}
    (st : Machine.Step platform ⟨env0, env, .running s⟩ choice event next) :
    next = ⟨env0, env, .awaiting c request resume⟩ := by
  cases st with
  | internal h => simp [known] at h
  | halt h => simp [known] at h
  | call h decoded _ =>
      rw [known] at h
      injection h with hc hr
      subst hc; subst hr
      rw [dec] at decoded
      injection decoded with hq
      subst hq
      rfl
  | exit h decoded ends =>
      rw [known] at h
      injection h with hc hr
      subst hc; subst hr
      rw [dec] at decoded
      injection decoded with hq
      subst hq
      exact absurd ends continues

/-- Out of a running state whose ISA step is a known native call the platform
decodes to a terminal request, every machine step halts. -/
theorem next_of_exit {env0 env : Environment} {s : Grass.ISA.Wasm.Target.State}
    {c : NativeCall} {resume : NativeReturn → Grass.ISA.Wasm.Target.State}
    {request : Grass.Platform.Hosted.domain.Request}
    (known : Grass.ISA.Wasm.isa.step s = .external c resume)
    (dec : platform.decode c = some request)
    (ends : Grass.Platform.Hosted.domain.Terminal request)
    {choice : Machine.Choice Grass.Platform.Hosted.domain}
    {event : Event Grass.Platform.Hosted.domain} {next : MachineState}
    (st : Machine.Step platform ⟨env0, env, .running s⟩ choice event next) :
    next = ⟨env0, env, .halted⟩ := by
  cases st with
  | internal h => simp [known] at h
  | halt h => simp [known] at h
  | call h decoded continues =>
      rw [known] at h
      injection h with hc hr
      subst hc; subst hr
      rw [dec] at decoded
      injection decoded with hq
      subst hq
      exact absurd ends continues
  | exit _ _ _ => rfl

/-- Out of an awaiting state, every machine step is the environment answering
with some allowed response. -/
theorem next_of_reply {env0 env : Environment} {c : NativeCall}
    {request : Grass.Platform.Hosted.domain.Request}
    {resume : NativeReturn → Grass.ISA.Wasm.Target.State}
    {choice : Machine.Choice Grass.Platform.Hosted.domain}
    {event : Event Grass.Platform.Hosted.domain} {next : MachineState}
    (st : Machine.Step platform ⟨env0, env, .awaiting c request resume⟩ choice event next) :
    ∃ (response : Grass.Platform.Hosted.domain.Response request) (env' : Environment),
      next = ⟨env0, env', .running (resume (platform.encodeReturn c request response))⟩ := by
  cases st with
  | reply _ => exact ⟨_, _, rfl⟩

/-! ## The invariant -/

/-- The phases this program reaches. The program is deterministic, so this is
a list of shapes, one per instruction point, plus the awaiting point and
`halted`.

Linear memory is pinned to `mem0` only up to the `fd_write` call, because
that is the only place the machine reads it: after the call the environment
may have written the accepted byte count anywhere `encodeReturn` puts it, and
the remaining three instructions (`drop`, `i32.const`, `call proc_exit`) never
touch memory, so `mem` is existential there. The value left on the stack at
instruction 5 is existential for the same reason: `drop` discards it, so the
`errno` branch the environment chose does not split the state space. -/
inductive Reach : Machine.Phase Grass.ISA.Wasm.isa Grass.Platform.Hosted.domain → Prop
  | pc0 : Reach (.running (mkState mem0 0 []))
  | pc1 : Reach (.running (mkState mem0 1 [.i32 fdStdout]))
  | pc2 : Reach (.running (mkState mem0 2 [.i32 iovOperand, .i32 fdStdout]))
  | pc3 : Reach (.running (mkState mem0 3 [.i32 iovCount, .i32 iovOperand, .i32 fdStdout]))
  | pc4 : Reach (.running (mkState mem0 4
      [.i32 nwrittenOperand, .i32 iovCount, .i32 iovOperand, .i32 fdStdout]))
  | awaiting : Reach (.awaiting fdWriteCall writeRequest fdWriteResume)
  | pc5 (mem : Nat → Option UInt8) (v : Value) : Reach (.running (mkState mem 5 [v]))
  | pc6 (mem : Nat → Option UInt8) : Reach (.running (mkState mem 6 []))
  | pc7 (mem : Nat → Option UInt8) : Reach (.running (mkState mem 7 [.i32 exitOperand]))
  | halted : Reach .halted

/-- The machine-tier inductive invariant for this program: `Reach` holds
initially, is closed under `Machine.Step`, and every phase it admits is
halted or has a successor. -/
def invariant : Machine.Invariant platform program where
  Inv state := Reach state.phase
  initial := by
    intro state valid
    obtain ⟨-, -, phase⟩ := valid
    rw [phase]
    exact .pc0
  preserved := by
    intro state choice event next holds st
    obtain ⟨env0, env, phase⟩ := state
    have reach : Reach phase := holds
    clear holds
    cases reach with
    | pc0 => rw [next_of_internal step0 st]; exact .pc1
    | pc1 => rw [next_of_internal step1 st]; exact .pc2
    | pc2 => rw [next_of_internal step2 st]; exact .pc3
    | pc3 => rw [next_of_internal step3 st]; exact .pc4
    | pc4 =>
        rw [next_of_call step4 decodeWrite writeNotTerminal st]
        exact .awaiting
    | awaiting =>
        obtain ⟨response, env', eq⟩ := next_of_reply st
        rw [eq]
        cases response with
        | accepted n => exact .pc5 _ _
        | failed => exact .pc5 _ _
    | pc5 mem v => rw [next_of_internal (step5 mem v) st]; exact .pc6 _
    | pc6 mem => rw [next_of_internal (step6 mem) st]; exact .pc7 _
    | pc7 mem =>
        rw [next_of_exit (step7 mem) (decodeExit mem) exitTerminal st]
        exact .halted
    | halted => cases st
  progress := by
    intro state holds
    obtain ⟨env0, env, phase⟩ := state
    have reach : Reach phase := holds
    clear holds
    cases reach with
    | pc0 => exact .inr ⟨_, _, _, .internal step0⟩
    | pc1 => exact .inr ⟨_, _, _, .internal step1⟩
    | pc2 => exact .inr ⟨_, _, _, .internal step2⟩
    | pc3 => exact .inr ⟨_, _, _, .internal step3⟩
    | pc4 => exact .inr ⟨_, _, _, .call step4 decodeWrite writeNotTerminal⟩
    | awaiting =>
        -- An I/O error is an answer the hosted environment always allows,
        -- so this state has a successor even with stdout unavailable.
        exact .inr ⟨_, _, _, .reply (request := writeRequest) (response := .failed)
          (env' := env) rfl⟩
    | pc5 mem v => exact .inr ⟨_, _, _, .internal (step5 mem v)⟩
    | pc6 mem => exact .inr ⟨_, _, _, .internal (step6 mem)⟩
    | pc7 mem => exact .inr ⟨_, _, _, .exit (step7 mem) (decodeExit mem) exitTerminal⟩
    | halted => exact .inl rfl

/-! ## Adequacy against the spike's own specification root -/

/-- The hosted domain's events, relabeled into the specification's audit
vocabulary. `Grass.Console.writeLineDomain` carries the program's *outcome*
in place of a target exit status, so `proc_exit` maps to the outcome the
status stands for; heap and clock events (which this program never raises)
are silent. -/
def eventOf : Event Grass.Platform.Hosted.domain →
    Event (Grass.Console.writeLineDomain HelloOutcome)
  | .silent => .silent
  | .call (.inl (.inl (.exit status))) =>
      .call (.inr (if status = 0 then HelloOutcome.success else HelloOutcome.failure))
  | .call (.inl (.inl r)) => .call (.inl r)
  | .call (.inl (.inr _)) => .silent
  | .call (.inr _) => .silent
  | .reply (.inl (.inl (.write s b))) response => .reply (.inl (.write s b)) response
  | .reply (.inl (.inl (.read s n))) response => .reply (.inl (.read s n)) response
  | .reply (.inl (.inl (.query s))) response => .reply (.inl (.query s)) response
  | .reply (.inl (.inl (.exit _))) response => response.elim
  | .reply (.inl (.inr _)) _ => .silent
  | .reply (.inr _) _ => .silent

/-- The specification's input is `Unit`: `Console.writeLineContract` takes
responsibility for every environment. -/
def inputOf (_env : Environment) : spec.root.Input := ()

/-- One environment this platform admits, witnessing input coverage. -/
def sampleEnvironment : Environment where
  arguments := []
  stdinRemaining := []
  stdinAvailable := false
  stdoutAvailable := true
  stderrAvailable := true
  stdoutTranscript := []
  stderrTranscript := []
  nextHandle := 0
  allocations := []
  heapCapacity := 1
  clock := 0
  writeChunking := none

/-- The platform admits it: empty arena under a positive capacity, nothing
already written, and no buffered input behind an unavailable stdin. -/
theorem sampleAdmitted : Grass.Platform.Hosted.Admits sampleEnvironment :=
  ⟨fun _ => rfl, rfl, Nat.zero_lt_one, rfl, rfl⟩

/-- Every input the specification admits is presented by an environment the
platform admits. -/
theorem covers (input : spec.root.Input) (_admitted : spec.root.admits input) :
    ∃ env, platform.Admits env ∧ inputOf env = input :=
  ⟨sampleEnvironment, sampleAdmitted, rfl⟩

/-- **The machine-tier obligation, discharged for a real program.** Every
input `Grass.Spikes.HelloWorld.spec` admits starts an execution, and every
reachable frontier of this loaded module either halts or continues: no
reachable state faults, no native call goes unrealized, and no pending
request goes unanswerable. -/
theorem adequate :
    (Machine.behavior platform program spec.root eventOf inputOf).Adequate :=
  Machine.adequate_of_invariant invariant spec.root eventOf inputOf covers

end Grass.Programs.HelloWorld.Wasi
