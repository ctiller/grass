# Bare-metal boot memory boundary

[`BootMemory`](../Grass/Platform/BareMetal/BootMemory.lean) admits an explicit
post-firmware memory snapshot. It does not
model processor reset, discover a board, or establish that firmware supplied
the snapshot. The same RAM ownership check serves x86-64 and AArch64 consumers.
Each consumer must separately establish its instruction-set and address-
translation regime.

## Admitted RAM

The input is an explicit fresh `MachineState`, a core context, and a physical
map declaring usable RAM and excluded device windows. Admission checks every
represented live allocation: physical address space, present nonwrapping
placement, RAM coverage, exclusion from device windows, sole ownership by the
core, and an admitted boot source (image mapping, stack, or boot RAM). Source
names do not prove hardware classification. Live placements must be pairwise
disjoint, backing stores must satisfy `DedicatedBackings`, and no grants may
remain. Allocation-local offsets include the allocation extent's start when
translated to physical coordinates.

These checks do not infer that the listed RAM is the entire physical inventory.
The map is supplied applicability data, not evidence that a board implements it
or that firmware transferred ownership. The checker requires fresh event, fault,
obligation, context and synchronization state and the initial event supply. It
retains that exact input machine and registers the core context; it does not
clear supplied history or duties. Constructing an unrelated fresh candidate
from old bytes still does not prove that it is a valid continuation of the old
execution.

## Executable bytes

[`BootFetch`](../Grass/Platform/BareMetal/BootFetch.lean) uses the shared
[`AccessFactory`](../Grass/Op/AccessFactory.lean) for the operation step, resolved backing
observation, permission and initialization checks. A RAM classification alone
does not initialize bytes or authorize execution. Successful boot admission
alone does not prove that a source artifact was loaded at the entry address.
That connection requires the exact loaded bytes and their provenance.

The [x86 adapter](../Grass/Platform/BareMetal/X86BootFetch.lean) supplies the
existing observed-fetch receipt and canonical decoder with the committed bytes.
The [AArch64 adapter](../Grass/Platform/BareMetal/AArch64BootFetch.lean) checks
four-byte width and PC alignment, then returns the actual bytes in address
order. It does not decode the instruction or select a byte-order interpretation.

The x86 consumer starts at a supplied 64-bit entry, after firmware and any mode
switch. It makes no real-mode or reset-vector claim. The AArch64 consumer needs
an explicit applicable exception level, translation regime and byte order.
Neither a numeric physical address nor equal physical and virtual numbers
proves a translation mapping. Existing x86 virtual-memory execution contracts
remain separate from this physical-RAM boundary.

## Devices and remaining applicability

MMIO is excluded from ordinary RAM. A write-back `ByteStore` cannot represent
volatile register reads, device side effects, DMA, or cache-maintenance duties.
Device execution needs its own operation receipts and an explicit relationship
between device addresses, ownership, and observable effects. An address-space
name or permission flag cannot supply that relationship.

There is no implicit operating-system service: AArch64 SVC does not acquire
Linux syscall meaning on bare metal. Console, file, network, display, and
terminal-status capabilities need concrete platform providers. Missing
capabilities remain applicability gaps against the unchanged spike
specifications. Boot admission and model checks are not native validation or
an end-to-end program certificate.
