import Grass.Platform.BareMetal.Environment
import Grass.Platform.BareMetal.Registers
import Grass.Service.Domain

/-!
# The bare-metal UART device: request vocabulary and response relation

The ISA-independent half of a bare-metal `Grass.Target.Platform`: the
service domain a UART realizes, and the environment's `Responds` relation
for it. Nothing here names x86, AArch64, an instruction, or a register — the
device only knows bytes, counts, and the two portable domains
(`uartDomain` itself, and `Grass.Service.Console`, which it realizes).

## Why a new domain instead of reusing `Console` directly

A bare-metal program does not call anything: `docs/TARGET_SEAMS.md` and
`Grass.Target.ISA` give `step` exactly one way to leave the ISA,
`.external call resume`, and on every ISA in this tree that constructor
fires only for call-like instructions (`syscall`, `svc`, an import thunk).
Bare metal has none of those. What it has is a memory-mapped (AArch64) or
port-mapped (x86) *store*, which every existing ISA's `step` reports as an
ordinary internal transition, not as `.external`. So a platform cannot
realize `Console` directly the way Win32 or Linux do: there is no native
call site to `decode`.

`uartDomain` is this round's answer to the part of that problem that is
ISA-independent: fix the vocabulary of device requests a UART accepts and
the environment relation that answers them, in a form any ISA's MMIO-as-
`external` extension (proposed below and in this module's report) can
`decode` into. `toConsole` then shows that vocabulary is not a new console
protocol invented for bare metal — every one of its requests already
corresponds to a `Console` request, so a program written against the
portable console domain and compiled for a hosted platform continues to
mean the same thing when it is instead compiled for bare metal and its
console calls are realized through `uartDomain`. That correspondence is
approximate in one place; see `toConsole`'s docstring.

## The proposed ISA-seam extension (not made here)

`docs/TARGET_SEAMS.md` forbids editing `Grass.Target.ISA`; this is a written
proposal for the change an ISA would need, for review before it is made.

An `ISA` would gain one field, `deviceRange : InitialContext → ByteRange`
(or a `List` of them, one per MMIO window, if a target has more than one
device), naming the address range treated as device registers rather than
ordinary memory for a given entry context. `step` would then be required to
report a store whose address falls in `deviceRange ctx` as
`.external (mmioWrite addr value) resume`, not as an internal memory write —
symmetrically, a load from that range would report
`.external (mmioRead addr) resume`. `NativeCall` would need a constructor
(or a sum case) carrying `addr : MachineAddress` and, for a write,
`value : Byte` (or a width tag, if a target exposes wider MMIO accesses);
`resume` would build the post-load state from the platform's answer instead
of always resuming with the same state the way a plain load does today.

For x86, the mechanism is different but the shape is the same: `out dx, al`
and `in al, dx` already decode as ordinary instructions with no memory
effect, so the natural encoding is for `step` to report them directly as
`.external (portOut port value) resume` / `.external (portIn port) resume`
without any `deviceRange` at all — port space is already disjoint from
address space, so there is nothing to range-check. A shared `NativeCall`
sum type (`mmio addr value | portIo port value`, or two ISA-specific
`NativeCall` shapes unified only by what `Platform.decode` produces) lets
`Platform.decode` for bare metal pattern-match either encoding down to the
same `uartDomain.Request` — a store to `pl011Base + pl011DR` and an `out` to
`com1Data` both decode to `.txWrite value`.

This keeps the rule the ISA seam states — "the ISA never knows what a call
means" — intact: the ISA reports *that* an address was a device access (or,
for x86, that a port instruction ran) and hands over the raw address/port
and value; deciding that this particular address is a UART data register
and this particular write means `txWrite` is entirely the platform's job,
exactly like decoding a `syscall` number today.
-/

namespace Grass.Platform.BareMetal

open Grass.Service

/-! ## The UART's own request vocabulary -/

/-- The bare-metal UART's requests. Named for the register operation they
realize, not for the register address, so the same four requests serve both
the AArch64 PL011 (`Registers.pl011Base` + offsets) and the x86 16550
(`Registers.com1Base` + offsets) — `Platform.decode` is what ties a
specific address or port to one of these. -/
inductive UartRequest where
  /-- Push one byte onto the transmit FIFO: a store to `UARTDR`
  (`pl011DR`) or an `out` to `com1Data`. -/
  | txWrite (byte : UInt8)
  /-- Read transmit-FIFO status: a load of `UARTFR`'s `TXFF` bit or of the
  16550 Line Status Register's `THRE` bit. -/
  | txReady
  /-- Pop one byte from the receive queue: a load of `UARTDR` or of
  `com1Data` with `DR` set. -/
  | rxRead
  /-- Stop the machine. Terminal: no response follows it. -/
  | halt
deriving DecidableEq, Repr

/-- The response type for each UART request. `txWrite`'s and `txReady`'s
`Bool` are different questions answered the same way a hardware status bit
would be: `txWrite`'s says whether the byte was accepted, `txReady`'s says
whether one would be right now. -/
def UartResponse : UartRequest → Type
  | .txWrite _ => Bool
  | .txReady => Bool
  | .rxRead => Option UInt8
  | .halt => Unit

/-- Only `halt` ends the run; the other three requests always get a
response and the program continues. -/
def UartTerminal : UartRequest → Prop
  | .halt => True
  | _ => False

instance (request : UartRequest) : Decidable (UartTerminal request) := by
  cases request <;> unfold UartTerminal <;> infer_instance

/-- The bare-metal UART's portable service vocabulary. This is the `Domain`
a bare-metal `Grass.Target.Platform` would set as (one summand of) its `D`,
once an ISA exposes MMIO/port I/O as `external` (see this module's
docstring). -/
def uartDomain : Domain where
  Request := UartRequest
  Response := UartResponse
  Terminal := UartTerminal

/-! ## Realizing the portable console domain -/

/--
Every `uartDomain` request as the `Console` request it realizes for a
program written against the portable console vocabulary: `txWrite`
realizes a one-byte `stdout` write, `txReady` realizes asking whether
`stdout` will accept output, `rxRead` realizes a one-byte `stdin` read, and
`halt` realizes `exit 0`.

This is a **request-level** correspondence, not a `Domain` morphism: the
response types disagree in two places, and both disagreements are
documented rather than hidden.

- `txReady ↦ Console.query .stdout`: `Console.query`'s `Bool` answers "does
  this stream exist at all" (a detached console, a closed descriptor); a
  UART's readiness bit answers "is there room in the transmit FIFO right
  now". A UART that exists always answers `query` `true` — `uartTxReady`
  below states this — so the correspondence is sound in the direction a
  refinement needs (a program that only ever branches on `query` before
  writing, the way `docs/HELLO_WORLD.md`-style programs do, still branches
  correctly) but is not an equivalence: a program that used `query` to mean
  "poll until there is room" would be relying on flow control this map does
  not carry. Closing that gap needs the portable domain to grow a
  flow-control response, which is out of this round's scope.
- `halt ↦ Console.Request.exit 0`: `uartDomain.halt`'s response type is
  `Unit` so the terminal transition is reachable (see `Device.Responds`'s
  docstring); `Console.exit`'s response type is `Empty`, encoding that no
  reply is ever delivered. Both encode "the run ends here" — the type
  difference is in how each domain spells "no further transition", not in
  what happens.

A driver instantiating the ISA-seam proposal above would use `toConsole` to
build its `Platform.decode`: decode the MMIO/port event to a `UartRequest`
first (address- or port-specific), then apply `toConsole` to get the
`Console.Request` a portable specification was written against.
-/
def toConsole : UartRequest → Option Console.Request
  | .txWrite b => some (Console.Request.write .stdout [b])
  | .txReady => some (Console.Request.query .stdout)
  | .rxRead => some (Console.Request.read .stdin 1)
  | .halt => some (Console.Request.exit 0)

@[simp] theorem toConsole_txWrite (b : UInt8) :
    toConsole (.txWrite b) = some (Console.Request.write .stdout [b]) := rfl

@[simp] theorem toConsole_txReady :
    toConsole .txReady = some (Console.Request.query .stdout) := rfl

@[simp] theorem toConsole_rxRead :
    toConsole .rxRead = some (Console.Request.read .stdin 1) := rfl

@[simp] theorem toConsole_halt :
    toConsole .halt = some (Console.Request.exit 0) := rfl

/-- `toConsole` never refuses a `uartDomain` request: every one of the four
has a `Console` realization. -/
theorem toConsole_isSome (request : UartRequest) : (toConsole request).isSome := by
  cases request <;> rfl

/-! ## The environment's response relation -/

/--
What the environment may answer to each UART request, and how it changes.

- `txWrite b`: if the transmit FIFO has room (`env.txPending < env.txCapacity`),
  the **only** legitimate answer is acceptance — `true`, with `b` appended
  to the permanent transcript and `txPending` incremented. If the FIFO is
  full, the **only** legitimate answer is refusal — `false`, environment
  unchanged. `Device.txWrite_accepted_of_room` and `Device.txWrite_may_refuse`
  state these two halves; together they rule out both a UART that lies about
  having room (accepting past capacity) and one that refuses out of
  capriciousness (refusing with room to spare) — see that section for why
  the latter, not "refusal is always a legitimate choice", is this round's
  design.
- `txReady`: deterministic — the answer is exactly whether there is room,
  and asking never changes anything.
- `rxRead`: deterministic — the front of `rxQueue` if it is nonempty,
  `none` if it is empty; a successful read removes that byte.
- `halt`: terminal, so `Grass.Target.Machine`'s `Step.terminal` is what
  actually ends the run; the environment's own contribution is recording
  that it happened. `Device.halt_preserves` states the environment is
  otherwise untouched — reused literally, since a `halted` field nothing
  ever sets would be exactly the kind of environment state that lies about
  itself.

What this relation does **not** model: nothing ever decreases `txPending`.
A real UART drains its transmit FIFO onto the wire asynchronously, so a
program that polls `txReady` between writes eventually sees room again even
without any read-side event. Adding that requires the environment to be
able to change on its own, between program-visible events — this
`Responds`, like every `Platform.Responds`, only fires when the program
asks something, so it cannot express spontaneous draining without either a
platform-supplied fairness assumption or a `Domain` for "time passes" that
nothing in this round's request list called for. The honest statement of
the limit is: this model proves a bounded number of accepted bytes, not
unbounded serial output, until a drain transition is added.
-/
def Responds : Environment → (request : UartRequest) →
    UartResponse request → Environment → Prop
  | env, .txWrite b, true, env' =>
      env.txPending < env.txCapacity ∧
        env' = { env with
          txTranscript := env.txTranscript ++ [b], txPending := env.txPending + 1 }
  | env, .txWrite _b, false, env' =>
      env.txCapacity ≤ env.txPending ∧ env' = env
  | env, .txReady, ready, env' =>
      ready = decide (env.txPending < env.txCapacity) ∧ env' = env
  | env, .rxRead, none, env' =>
      env.rxQueue = [] ∧ env' = env
  | env, .rxRead, some b, env' =>
      ∃ rest, env.rxQueue = b :: rest ∧ env' = { env with rxQueue := rest }
  | env, .halt, _response, env' =>
      env' = { env with halted := true }

/-! ### Honesty theorems -/

/-- Refusing a write is always a legitimate environment choice once the
transmit FIFO is full — the program must poll `txReady` and retry. -/
theorem txWrite_may_refuse {env : Environment} {b : UInt8}
    (full : env.txCapacity ≤ env.txPending) :
    Responds env (.txWrite b) false env :=
  ⟨full, rfl⟩

/-- Whenever the FIFO has room, `Responds` forces acceptance: no refusal is
a legitimate environment choice while there is room. Together with
`txWrite_may_refuse`, this pins refusal to exactly "FIFO full" — the
"only when full" reading `Device.Responds`'s docstring commits to. -/
theorem txWrite_accepted_of_room {env env' : Environment} {b : UInt8} {response : Bool}
    (room : env.txPending < env.txCapacity)
    (responds : Responds env (.txWrite b) response env') :
    response = true ∧
      env' = { env with
        txTranscript := env.txTranscript ++ [b], txPending := env.txPending + 1 } := by
  cases response with
  | true => exact ⟨rfl, responds.2⟩
  | false => exact absurd responds.1 (by omega)

/-- The converse of `txWrite_accepted_of_room`: a refusal is only ever the
environment's answer when the FIFO was actually full. Rules out a `Responds`
implementation that refuses capriciously with room to spare. -/
theorem txWrite_refused_implies_full {env env' : Environment} {b : UInt8}
    (responds : Responds env (.txWrite b) false env') :
    env.txCapacity ≤ env.txPending :=
  responds.1

/-- An accepted write extends the transcript by exactly the written byte —
never more, never fewer, never a different byte. -/
theorem transcript_append {env env' : Environment} {b : UInt8}
    (responds : Responds env (.txWrite b) true env') :
    env'.txTranscript = env.txTranscript ++ [b] :=
  congrArg Environment.txTranscript responds.2

/-- Every `Responds` transition, whatever the request, leaves the old
transcript a prefix of the new one: the audit record only ever grows at the
end, never elsewhere. -/
theorem transcript_prefix_of_responds {env env' : Environment} {request : UartRequest}
    {response : UartResponse request} (responds : Responds env request response env') :
    ∃ rest : List UInt8, env'.txTranscript = env.txTranscript ++ rest := by
  cases request with
  | txWrite b =>
      cases response with
      | true => exact ⟨[b], congrArg Environment.txTranscript responds.2⟩
      | false => exact ⟨[], by simp [responds.2]⟩
  | txReady => exact ⟨[], by simp [responds.2]⟩
  | rxRead =>
      cases response with
      | none => exact ⟨[], by simp [responds.2]⟩
      | some b =>
          obtain ⟨rest, -, hEnv⟩ := responds
          exact ⟨[], by simp [hEnv]⟩
  | halt =>
      have hEnv : env' = { env with halted := true } := responds
      exact ⟨[], by simp [hEnv]⟩

/-- `txReady`'s answer is exactly the room status, and asking never changes
the environment: querying readiness is a pure read. -/
theorem txReady_status {env env' : Environment} {ready : Bool}
    (responds : Responds env .txReady ready env') :
    ready = decide (env.txPending < env.txCapacity) ∧ env' = env :=
  responds

/-- A UART environment always answers `txReady`: there is no request for
which it has no legitimate response, matching `toConsole_txReady`'s claim
that a program polling `Console.query` before writing sees a real answer. -/
theorem uartTxReady_isSome (env : Environment) :
    Responds env .txReady (decide (env.txPending < env.txCapacity)) env :=
  ⟨rfl, rfl⟩

/-- A read against a nonempty queue delivers its front byte and removes it;
against an empty queue it delivers `none` and changes nothing. -/
theorem rxRead_pops {env env' : Environment} {byte : Option UInt8}
    (responds : Responds env .rxRead byte env') :
    (env.rxQueue = [] ∧ byte = none ∧ env' = env) ∨
      ∃ b rest, env.rxQueue = b :: rest ∧ byte = some b ∧ env' = { env with rxQueue := rest } := by
  cases byte with
  | none => exact .inl ⟨responds.1, rfl, responds.2⟩
  | some b =>
      obtain ⟨rest, hq, hEnv⟩ := responds
      exact .inr ⟨b, rest, hq, rfl, hEnv⟩

/-- `halt` is terminal, so `Grass.Target.Machine.Step.terminal` — not this
relation — is what actually stops the run; the environment's own change is
exactly recording that halt happened, and nothing else about it. -/
theorem halt_preserves {env env' : Environment} {response : Unit}
    (responds : Responds env .halt response env') :
    env' = { env with halted := true } :=
  responds

/-- `halt`'s transcript, pending count, capacity, receive queue and RAM
window are byte-for-byte what they were before halting — only `halted`
itself moves. Restates `halt_preserves` field by field for a consumer that
does not want to unfold the record update. -/
theorem halt_fields_preserved {env env' : Environment} {response : Unit}
    (responds : Responds env .halt response env') :
    env'.txTranscript = env.txTranscript ∧ env'.txPending = env.txPending ∧
      env'.txCapacity = env.txCapacity ∧ env'.rxQueue = env.rxQueue ∧
      env'.ram = env.ram ∧ env'.halted = true := by
  rw [halt_preserves responds]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Grass.Platform.BareMetal
