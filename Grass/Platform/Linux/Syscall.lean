/-!
# Native Linux direct-syscall boundary

This module describes the register-to-request boundary for the native x86-64
and AArch64 Linux ABIs.  It does not claim that a `SYSCALL` or `SVC`
instruction was executed, that the kernel serviced the request, or that libc's
wrapper conventions apply.

The syscall numbers and register assignments follow the Linux kernel UAPI and
entry sources:

* `arch/x86/entry/syscalls/syscall_64.tbl` and `arch/x86/entry/entry_64.S`
  (the kernel consumes the low 32-bit number):
  https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/entry
* `include/uapi/asm-generic/unistd.h`:
  https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/uapi/asm-generic/unistd.h
* `arch/arm64/kernel/entry-common.c` (`do_el0_svc` passes `regs->regs[8]`
  through the kernel's integer syscall-number boundary):
  https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/arm64/kernel/entry-common.c

Linux reserves raw return values -1 through -4095 for errors; see
`include/linux/err.h`:
https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/err.h
A libc wrapper normally translates these to `-1` and
`errno`, which is a different boundary.
-/

namespace Grass.Platform.Linux.Syscall

/-- Native kernel syscall table selected at the physical entry boundary. -/
inductive Abi where
  | x86_64
  | aarch64
deriving DecidableEq, Repr

/-- Initial syscall population needed by the console and process-exit spikes. -/
inductive Id where
  | read
  | write
  | exit
  | exitGroup
deriving DecidableEq, Repr

/-- Native syscall number.  The x86 x32 namespace is intentionally absent. -/
def number : Abi → Id → Nat
  | .x86_64, .read => 0
  | .x86_64, .write => 1
  | .x86_64, .exit => 60
  | .x86_64, .exitGroup => 231
  | .aarch64, .read => 63
  | .aarch64, .write => 64
  | .aarch64, .exit => 93
  | .aarch64, .exitGroup => 94

/-- Checked identity recovery from the 32 bits consumed by the kernel entry. -/
def id? (abi : Abi) (physicalNumber : BitVec 32) : Option Id :=
  if physicalNumber.toNat = number abi .read then some .read
  else if physicalNumber.toNat = number abi .write then some .write
  else if physicalNumber.toNat = number abi .exit then some .exit
  else if physicalNumber.toNat = number abi .exitGroup then some .exitGroup
  else none

/-- Every declared native number is accepted by the checked decoder. -/
theorem id?_number (abi : Abi) (id : Id) :
    id? abi (BitVec.ofNat 32 (number abi id)) = some id := by
  cases abi <;> cases id <;> decide

/-- Successful identity recovery fixes the consumed physical number exactly. -/
theorem id?_exact {abi : Abi} {physicalNumber : BitVec 32} {id : Id}
    (selected : id? abi physicalNumber = some id) :
    physicalNumber.toNat = number abi id := by
  unfold id? at selected
  split at selected
  next equal => cases selected; exact equal
  split at selected
  next equal => cases selected; exact equal
  split at selected
  next equal => cases selected; exact equal
  split at selected
  next equal => cases selected; exact equal
  next => contradiction

/-- Exact words captured at the Linux kernel ABI boundary. -/
structure Captured where
  number : BitVec 32
  arg0 : BitVec 64
  arg1 : BitVec 64
  arg2 : BitVec 64
deriving DecidableEq, Repr

/-- An x86-64 register reader at syscall entry. -/
structure X86RegisterView where
  rax : BitVec 64
  rdi : BitVec 64
  rsi : BitVec 64
  rdx : BitVec 64

/-- An AArch64 register reader at syscall entry. -/
structure AArch64RegisterView where
  x0 : BitVec 64
  x1 : BitVec 64
  x2 : BitVec 64
  x8 : BitVec 64

/-- Project the exact x86-64 physical syscall registers. -/
def captureX86 (registers : X86RegisterView) : Captured where
  number := BitVec.setWidth 32 registers.rax
  arg0 := registers.rdi
  arg1 := registers.rsi
  arg2 := registers.rdx

/-- Project the exact AArch64 physical syscall registers. -/
def captureAArch64 (registers : AArch64RegisterView) : Captured where
  number := BitVec.setWidth 32 registers.x8
  arg0 := registers.x0
  arg1 := registers.x1
  arg2 := registers.x2

@[simp] theorem captureX86_number (registers : X86RegisterView) :
    (captureX86 registers).number = BitVec.setWidth 32 registers.rax := rfl

@[simp] theorem captureAArch64_number (registers : AArch64RegisterView) :
    (captureAArch64 registers).number = BitVec.setWidth 32 registers.x8 := rfl

@[simp] theorem captureX86_arguments (registers : X86RegisterView) :
    (captureX86 registers).arg0 = registers.rdi ∧
    (captureX86 registers).arg1 = registers.rsi ∧
    (captureX86 registers).arg2 = registers.rdx := by
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem captureAArch64_arguments (registers : AArch64RegisterView) :
    (captureAArch64 registers).arg0 = registers.x0 ∧
    (captureAArch64 registers).arg1 = registers.x1 ∧
    (captureAArch64 registers).arg2 = registers.x2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Typed requests retain pointer and count words exactly.  Linux `int`
arguments expose their ABI-significant low 32 bits. -/
inductive Request where
  | read (fd : BitVec 32) (buffer count : BitVec 64)
  | write (fd : BitVec 32) (buffer count : BitVec 64)
  | exit (status : BitVec 32)
  | exitGroup (status : BitVec 32)
deriving DecidableEq, Repr

def Request.id : Request → Id
  | .read .. => .read
  | .write .. => .write
  | .exit .. => .exit
  | .exitGroup .. => .exitGroup

/-- Decode only recognized native syscalls from the actual captured words. -/
def decode? (abi : Abi) (captured : Captured) : Option Request :=
  match id? abi captured.number with
  | some .read => some (.read (BitVec.setWidth 32 captured.arg0) captured.arg1 captured.arg2)
  | some .write => some (.write (BitVec.setWidth 32 captured.arg0) captured.arg1 captured.arg2)
  | some .exit => some (.exit (BitVec.setWidth 32 captured.arg0))
  | some .exitGroup => some (.exitGroup (BitVec.setWidth 32 captured.arg0))
  | none => none

theorem decode_write {abi : Abi} {captured : Captured}
    (selected : id? abi captured.number = some .write) :
    decode? abi captured = some (.write (BitVec.setWidth 32 captured.arg0)
      captured.arg1 captured.arg2) := by
  simp [decode?, selected]

theorem decode_exitGroup {abi : Abi} {captured : Captured}
    (selected : id? abi captured.number = some .exitGroup) :
    decode? abi captured = some (.exitGroup (BitVec.setWidth 32 captured.arg0)) := by
  simp [decode?, selected]

/-- `decode?_id` shows a successful typed extraction retains the identity selected from the same
captured number; it cannot relabel a syscall after argument decoding. -/
theorem decode?_id {abi : Abi} {captured : Captured} {request : Request}
    (decoded : decode? abi captured = some request) :
    id? abi captured.number = some request.id := by
  unfold decode? at decoded
  cases selected : id? abi captured.number <;> simp only [selected] at decoded
  next => contradiction
  next id =>
    cases id <;> cases decoded <;> rfl

/-- Successful typed extraction therefore fixes the ABI's native syscall
number, while the request constructors retain the exact decoded arguments. -/
theorem decode?_number {abi : Abi} {captured : Captured} {request : Request}
    (decoded : decode? abi captured = some request) :
    captured.number.toNat = number abi request.id :=
  id?_exact (decode?_id decoded)

/-- Raw kernel return classification, before libc `errno` translation. -/
inductive RawResult where
  | success (value : BitVec 64)
  | error (errno : Nat)
deriving DecidableEq, Repr

def errorThreshold : Nat := 2 ^ 64 - 4095

/-- Interpret the kernel's unsigned 64-bit representation of `[-4095, -1]`. -/
def decodeRaw (raw : BitVec 64) : RawResult :=
  if raw.toNat < errorThreshold then .success raw
  else .error (2 ^ 64 - raw.toNat)

theorem decodeRaw_success {raw : BitVec 64} (below : raw.toNat < errorThreshold) :
    decodeRaw raw = .success raw := by
  simp [decodeRaw, below]

theorem decodeRaw_error {raw : BitVec 64} (reserved : errorThreshold ≤ raw.toNat) :
    decodeRaw raw = .error (2 ^ 64 - raw.toNat) := by
  simp [decodeRaw, Nat.not_lt.mpr reserved]

theorem decodeRaw_error_range {raw : BitVec 64} {errno : Nat}
    (decoded : decodeRaw raw = .error errno) : 1 ≤ errno ∧ errno ≤ 4095 := by
  simp only [decodeRaw] at decoded
  split at decoded <;> rename_i boundary
  · contradiction
  · injection decoded with same
    subst errno
    have rawLt : raw.toNat < 2 ^ 64 := raw.isLt
    simp only [errorThreshold] at boundary
    omega

end Grass.Platform.Linux.Syscall
