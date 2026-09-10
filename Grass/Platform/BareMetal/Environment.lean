import Grass.Platform.BareMetal.BootMemory

/-!
# The bare-metal device environment

Everything outside a bare-metal program: the physical RAM window it was
admitted into (`Grass.Platform.BareMetal.BootMemory`), and the one device
every bare-metal target in this round needs — a UART console — modeled as
its own piece of environment state rather than as a slice of ordinary
memory. `Grass.Platform.BareMetal.Device` gives this state a request
vocabulary and a `Responds` relation; this module only owns the state
itself, so it has no dependency on either ISA or on `Grass.Service`.

No program, register, or instruction encoding is named here: `Environment`
is built only from portable notions (bytes, counts, a physical window) and
`BootMemory.PhysicalWindow`, which is already ISA-independent.
-/

namespace Grass.Platform.BareMetal

open Grass.Platform.BareMetal.BootMemory

/--
The whole bare-metal device environment: the physical RAM window a program
was admitted into, plus the state of the one UART console every bare-metal
target in this round exposes.

The UART fields separate three things a real 16550/PL011 keeps separate:

- `txTranscript` is the permanent audit record of every byte the program has
  ever gotten accepted onto the wire, in order. It is never truncated or
  rewritten — draining the transmit FIFO removes a byte from hardware, not
  from history.
- `txPending`/`txCapacity` model transmit flow control: `txPending` is how
  many of the bytes in `txTranscript` are still occupying the FIFO's
  hardware capacity `txCapacity`. `Device.Responds` only ever grows
  `txPending` (see that module's docstring for why draining is future
  work); a fresh environment starts it at `0`.
- `rxQueue` is the receive side: bytes already delivered by the outside
  world and not yet consumed by the program, oldest first.

`halted` records whether the device has processed a `halt` request. It is
part of `Environment` rather than inferred from `Grass.Target.Machine`'s own
`Phase.halted` because `Environment` must stay meaningful on its own: a
consumer inspecting only the environment (an audit trail, a test oracle)
should not have to reconstruct machine phase to know whether the run ended
because the program was still running or because it asked to stop.
-/
structure Environment where
  /-- The physical RAM window the program was admitted into. Reused
  unchanged from the shared boot-memory admission model rather than
  redeclared here, so a RAM claim stays anchored to the one place it is
  checked. -/
  ram : BootMemory.PhysicalWindow
  /-- Every byte the environment has ever accepted from a `txWrite`, in
  transmission order. Append-only. -/
  txTranscript : List UInt8
  /-- How many of the bytes in `txTranscript` are still occupying the
  transmit FIFO's hardware capacity. `txPending ≤ txCapacity` is maintained
  by every `Device.Responds` transition; see
  `Device.txWrite_accepted_of_room` and `Device.txWrite_may_refuse`. -/
  txPending : Nat
  /-- The transmit FIFO's hardware depth in bytes. A field rather than a
  fixed constant so a target that disables FIFOs (depth `1`, matching the
  16550's non-FIFO mode) and one that runs the full 16-byte 16550/PL011
  FIFO are the same `Environment` type with a different boot-time value. -/
  txCapacity : Nat
  /-- Bytes already delivered by the outside world and not yet consumed by
  the program, oldest first. -/
  rxQueue : List UInt8
  /-- Whether the device has processed a `halt` request. -/
  halted : Bool
deriving DecidableEq, Repr

end Grass.Platform.BareMetal
