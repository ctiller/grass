/-!
# UART register maps

The named MMIO offsets and I/O ports the bare-metal UART model in
`Grass.Platform.BareMetal.Environment` and `Grass.Platform.BareMetal.Device`
is built against. Two devices, because the two ISAs this round targets reach
their consoles differently:

- **AArch64 on QEMU's `virt` machine**: an ARM PrimeCell PL011, memory-mapped
  at a fixed physical base. Register layout, offsets and flag bits are from
  ARM DDI 0183 (PrimeCell UART (PL011) Technical Reference Manual) §3.3.
- **x86-64 bare metal**: a 16550-compatible UART at the PC platform's
  conventional COM1 *I/O port* range (not memory-mapped — see the port-I/O
  note in `Grass.Platform.BareMetal.Device`). Offsets and bits are the
  National Semiconductor PC16550D register description.

Only the constants this model's `Responds` relation and its docstrings cite
are named here: the data register, the one flag/status bit each device uses
to report transmit-FIFO fullness, and (for completeness of the citation) the
matching receive-empty bit. Divisor latches, interrupt enables, and the other
setup-only registers belong to a boot/initialization model, not to the
steady-state read/write/status vocabulary `uartDomain` exposes.
-/

namespace Grass.Platform.BareMetal

/-! ## ARM PrimeCell PL011 (ARM DDI 0183), QEMU `virt` -/

/-- The PL011 instance QEMU's `virt` machine places at this fixed physical
address. ARM DDI 0183 gives the register layout relative to this base;
QEMU's `virt` board documentation fixes the base itself. -/
def pl011Base : UInt64 := 0x09000000

/-- `UARTDR`, the PL011 Data Register: byte offset `0x00` from `pl011Base`.
A store here pushes a byte onto the transmit FIFO (or transmits it directly
with FIFOs disabled); a load pops the next received byte. ARM DDI 0183
§3.3.1. -/
def pl011DR : UInt64 := 0x000

/-- `UARTFR`, the PL011 Flag Register: byte offset `0x18` from `pl011Base`,
read-only. ARM DDI 0183 §3.3.6. -/
def pl011FR : UInt64 := 0x018

/-- `TXFF`, bit 5 of `UARTFR`: the transmit FIFO is full: a further write to
`UARTDR` must be refused or deferred. ARM DDI 0183 §3.3.6, Table 3-8. -/
def pl011FR_TXFF : UInt8 := 0x20

/-- `RXFE`, bit 4 of `UARTFR`: the receive FIFO is empty: a read of `UARTDR`
has no delivered byte. ARM DDI 0183 §3.3.6, Table 3-8. -/
def pl011FR_RXFE : UInt8 := 0x10

/-- The physical address span a platform declares as the PL011's device
window at `pl011Base`: 4 KiB, matching QEMU's `virt` machine memory map
(`hw/arm/virt.c`, the `VIRT_UART` entry) and large enough to cover every
register offset ARM DDI 0183 §3.3 defines. -/
def pl011Size : Nat := 0x1000

/-! ## 16550 UART, COM1, x86 port I/O -/

/-- The 16550's COM1 I/O-port base on the PC platform. Unlike the PL011 this
is an I/O-space port, not a memory address: it is reached by `in`/`out`
instructions, never by a load or store. National Semiconductor PC16550D,
register description table. -/
def com1Base : UInt16 := 0x3F8

/-- Receiver Buffer Register (read) / Transmitter Holding Register (write):
port offset `0` from `com1Base`, valid when the Divisor Latch Access Bit
(`LCR` bit 7) is clear. PC16550D register description. -/
def com1Data : UInt16 := com1Base

/-- Line Status Register: port offset `5` from `com1Base`, read-only.
PC16550D register description. -/
def com1LineStatus : UInt16 := com1Base + 5

/-- `THRE`, bit 5 of the Line Status Register: the Transmitter Holding
Register is empty, i.e. there is room for another byte. PC16550D register
description. -/
def com1LSR_THRE : UInt8 := 0x20

/-- `DR`, bit 0 of the Line Status Register: a received byte is waiting in
the Receiver Buffer Register. PC16550D register description. -/
def com1LSR_DR : UInt8 := 0x01

end Grass.Platform.BareMetal
