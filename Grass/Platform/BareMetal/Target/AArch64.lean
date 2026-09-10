import Grass.ISA.AArch64.Target
import Grass.Platform.BareMetal.Device

/-!
# The AArch64 half of the bare-metal PL011 platform

`Admits`/`entry`/`decode`/`encodeReturn` for `Grass.Target.Platform
Grass.ISA.AArch64.isa Grass.Platform.BareMetal.uartDomain`, built against the
`CallTarget.mmioLoad`/`mmioStore` native call
`Grass.ISA.AArch64.Target.Step.execLoadStoreUImm` produces for a load or
store inside an `InitialContext.devices` window. `halt` is never decoded
here: `hlt` already steps the ISA straight to `StepOutcome.halted`
(`Grass.ISA.AArch64.Target.Step.stepInstr`), so no native call for it ever
reaches a platform's `decode`.

## Decode table

Address is relative to `Registers.pl011Base`; `size` is the load/store's
byte width (`Step.lsBytes`: `1` for `ldrb`/`strb`, `4` for 32-bit
`ldr`/`str`, `8` for the 64-bit form).

| Access | Address | Size | Decodes to |
|---|---|---|---|
| store | `pl011DR` | `1` or `4` | `.txWrite` (the stored word's low byte) |
| store | anything else | any | `none` (stuck) |
| load | `pl011FR` | `4` | `.txReady` |
| load | `pl011DR` | any | `.rxRead` |
| load | anything else | any | `none` (stuck) |

An 8-byte `str`/`ldr` to `pl011DR`/`pl011FR` decodes to `none`: the PL011's
registers are 32 bits wide, so a 64-bit access to one is already a
programming error, and refusing it (stuck) is more honest than guessing
which half was meant.

## `encodeReturn`

- `txWrite`: `x0 := 0`. `execLoadStoreUImm`'s store `resume` ignores
  `NativeReturn.x0` entirely, so this value is unobservable; fixed at `0`
  rather than left to vary for no reason.
- `txReady`: `x0` is a UARTFR word with `TXFF` (bit 5) set iff the FIFO is
  *not* ready, every other bit `0`. Enough for a program that only tests
  `TXFF` (the `and`+`cbz`/`tst` families this ISA subset covers) to behave
  correctly; a program testing another flag bit would see a fabricated `0`
  no real PL011 promises.
- `rxRead`: `x0 :=` the delivered byte, or `0` if none was waiting. A real
  PL011 leaves stale FIFO contents in `UARTDR` on an empty read; `decode`
  cannot refuse an empty read instead, because `decode` sees only the
  `NativeCall`, never `Environment.rxQueue` — only `Grass.Platform.
  BareMetal.Responds` knows whether the queue is empty, and it runs after
  `decode` has already committed the machine to this `.external` step. `0`
  is therefore a modeling choice, not a hardware fact: a program must poll
  `UARTFR.RXFE` before trusting the byte, exactly as real firmware must.

## What this still allows that real PL011 hardware would not

- `Admits` places no constraint on `rxQueue`: a real UART's receive FIFO
  cannot hold bytes before its first genuine RX interrupt, but an admitted
  environment here may start with any queue at all.
- `encodeReturn`'s `txReady` fabricates every UARTFR bit other than `TXFF`,
  as noted above.
-/

namespace Grass.Platform.BareMetal.Target.AArch64

open Grass.ISA.AArch64 (NativeCall NativeReturn InitialContext)
open Grass.Platform.BareMetal (Environment UartRequest UartResponse pl011Base pl011DR pl011FR
  pl011FR_TXFF pl011Size)

/-! ## Admission -/

/-- The environments this platform is willing to start a program in: the
UART is fresh (nothing transmitted, no bytes occupying the FIFO, not
halted, a positive FIFO depth), the boot RAM window is a well-formed
physical extent, and that RAM window is disjoint from the PL011's declared
register window (so `entry`'s device range can never steal what should have
been an ordinary memory access — see `admits_ram_not_deviceAt`). See the
module docstring for what this does not check. -/
def Admits (env : Environment) : Prop :=
  env.txTranscript = [] ∧
    env.txPending = 0 ∧
    env.halted = false ∧
    0 < env.txCapacity ∧
    env.ram.WellFormed ∧
    env.ram.numericRange.Disjoint ⟨pl011Base.toNat, pl011Size⟩

/-! ## Entry -/

/-- The admitted RAM window's top address, aligned down to 16 bytes — the
AArch64 SP alignment requirement (ARM DDI 0602 ID032025, "Stack pointer
alignment checking"). -/
def stackTop (env : Environment) : Nat :=
  let top := env.ram.base.toNat + env.ram.size
  top - top % 16

/-- Registers zeroed, `sp` at the aligned top of the admitted RAM window, no
staged bytes (bare metal stages no argv/envp), and exactly the PL011's
register window declared as a device range. -/
def entry (env : Environment) : InitialContext where
  registers := fun _ => 0
  sp := BitVec.ofNat 64 (stackTop env)
  staged := []
  devices := [(pl011Base.toNat, pl011Size)]

/-- The admitted RAM window never overlaps the PL011's device window in the
loaded machine: `Grass.ISA.AArch64.Target.initial` carries `entry env`'s
`devices` list verbatim, that list is exactly the PL011's window, and
`Admits`'s new disjointness conjunct rules out any address in the RAM window
also falling in it. So `State.deviceAt` — the predicate `execLoadStoreUImm`
consults before ever reaching ordinary memory — never fires over RAM. -/
theorem admits_ram_not_deviceAt {env : Environment} (h : Admits env)
    {program : Grass.Target.Sectioned} {address : Nat}
    (hram : env.ram.numericRange.Covers address) :
    Grass.ISA.AArch64.Target.State.deviceAt
        (Grass.ISA.AArch64.Target.initial program (entry env)) address = false := by
  obtain ⟨-, -, -, -, -, hdisjoint⟩ := h
  simp only [Grass.ISA.AArch64.Target.initial, entry, Grass.ISA.AArch64.Target.State.deviceAt,
    List.any_cons, List.any_nil, Bool.or_false, decide_eq_false_iff_not]
  rw [Grass.Memory.ByteRange.covers_def] at hram
  rw [Grass.Memory.ByteRange.disjoint_def] at hdisjoint
  simp only [BootMemory.PhysicalWindow.numericRange] at hram hdisjoint
  omega

/-! ## Decode -/

/-- Decode an AArch64 device access into a `uartDomain` request. See the
module docstring's table. -/
def decode (call : NativeCall) : Option UartRequest :=
  match call.target with
  | .mmioStore address bytes =>
      if address = pl011Base.toNat + pl011DR.toNat then
        match bytes with
        | [b] => some (.txWrite b)
        | [b, _, _, _] => some (.txWrite b)
        | _ => none
      else none
  | .mmioLoad address size =>
      if address = pl011Base.toNat + pl011FR.toNat then
        if size = 4 then some .txReady else none
      else if address = pl011Base.toNat + pl011DR.toNat then
        some .rxRead
      else none
  | .supervisor _ => none
  | .importSlot _ => none

/-! ## encodeReturn -/

/-- Encode the environment's answer as the AArch64 return effect. See the
module docstring's honesty notes on `txReady` and `rxRead`. -/
def encodeReturn (_call : NativeCall) :
    (request : UartRequest) → UartResponse request → NativeReturn
  | .txWrite _b, _accepted => { x0 := 0 }
  | .txReady, true => { x0 := 0 }
  | .txReady, false => { x0 := BitVec.ofNat 64 pl011FR_TXFF.toNat }
  | .rxRead, some b => { x0 := BitVec.ofNat 64 b.toNat }
  | .rxRead, none => { x0 := 0 }
  | .halt, _response =>
      -- `decode` never produces this request: `hlt` steps the ISA straight
      -- to `.halted` and never reaches a platform's `decode`. Kept only so
      -- `encodeReturn` is total over `uartDomain.Request`.
      { x0 := 0 }

end Grass.Platform.BareMetal.Target.AArch64
