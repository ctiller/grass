import Grass.Platform.Linux.Syscall

namespace Tests.Platform.LinuxSyscall

open Grass.Platform.Linux.Syscall

example : id? .x86_64 1 = some .write := by decide
example : id? .aarch64 64 = some .write := by decide
example : id? .x86_64 0x40000001 = none := by decide

def x86Write : X86RegisterView where
  rax := (7 : BitVec 64) <<< 32 ||| 1
  rdi := 0x100000001
  rsi := 0x7fff0000
  rdx := 13

/-- Kernel number decoding uses EAX while the typed fd uses EDI. -/
example : decode? .x86_64 (captureX86 x86Write) =
    some (.write 1 0x7fff0000 13) := by decide

def armExit : AArch64RegisterView where
  x0 := 0x100000007
  x1 := 0xaaaaaaaaaaaaaaaa
  x2 := 0xbbbbbbbbbbbbbbbb
  x8 := (9 : BitVec 64) <<< 32 ||| 94

/-- AArch64 entry consumes W8, and exit status consumes the low `int`. -/
example : decode? .aarch64 (captureAArch64 armExit) =
    some (.exitGroup 7) := by decide

/-- `-4095`, `-1`, and the adjacent successful value distinguish the boundary. -/
example : decodeRaw (BitVec.ofNat 64 (2 ^ 64 - 4095)) = .error 4095 := by decide
example : decodeRaw (BitVec.ofNat 64 (2 ^ 64 - 1)) = .error 1 := by decide
example : decodeRaw (BitVec.ofNat 64 (2 ^ 64 - 4096)) =
    .success (BitVec.ofNat 64 (2 ^ 64 - 4096)) := by decide
example : decodeRaw 27 = .success 27 := by decide

end Tests.Platform.LinuxSyscall
