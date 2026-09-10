/-!
# Raw kernel error returns

The Linux kernel's raw syscall boundary reports failure as a value in
`[-4095, -1]`, interpreted as `-errno` on a signed reading of the 64-bit
result register (`include/linux/err.h`, `IS_ERR_VALUE`); this is the
convention a bare `syscall` instruction observes, before any libc wrapper
translates it into `-1` plus a separately stored `errno`. `Grass.Platform.
Linux.Syscall.decodeRaw`/`errorThreshold` state the general boundary; this
module supplies the small, named subset of `errno.h` values this seam's
`encodeReturn` needs to cite by name instead of by bare literal, and the
two's-complement encoding of `-code` as a `UInt64` that a real `rax` holds.
-/

namespace Grass.Platform.Linux.Target.Errno

/-- I/O error (`include/uapi/asm-generic/errno-base.h`: `#define EIO 5`). -/
def EIO : Nat := 5

/-- Out of memory (`include/uapi/asm-generic/errno-base.h`:
`#define ENOMEM 12`). -/
def ENOMEM : Nat := 12

/-- Invalid argument (`include/uapi/asm-generic/errno-base.h`:
`#define EINVAL 22`). -/
def EINVAL : Nat := 22

/-- Function not implemented (`include/uapi/asm-generic/errno.h`:
`#define ENOSYS 38`). -/
def ENOSYS : Nat := 38

/-- The 64-bit two's-complement bit pattern of `-code`, the exact value the
kernel's raw syscall return convention places in the result register for a
failure (`code` in `[1, 4095]`; every constant above is in range). Wraparound
`UInt64` subtraction from `0` gives this directly, with no case split on
`code`. -/
def negative (code : Nat) : UInt64 := (0 : UInt64) - UInt64.ofNat code

end Grass.Platform.Linux.Target.Errno
