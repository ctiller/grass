import Grass.Core.Name

/-!
# The platform profile, as values rather than as a module path

`docs/DECISIONS.md` 16 fixes the initial platform profile: "Win32 x64 with
Windows 10 as API baseline and documented APIs rather than direct syscalls".

`docs/MODULES.md` requires those to be *selections made through this API* rather
than components of a module path, and replaces the spike spelling
`Grass.Platform.Win10.X64` with `Grass.Platform.Win32` for exactly that reason:
a path segment cannot be varied, compared, or discharged, so encoding a
deployment floor and an architecture into one conflates four separate choices
and makes none of them checkable.

## What is enforced here, and what is not

The three axes below are total functions of an inductive, and that totality is
the whole of the mechanism: `TargetAbi.handleBits` cannot be extended with a
second ABI without stating that ABI's handle width, because a missing case is a
compile error under this repository's settings. The equations proved below are
`rfl` and establish nothing on their own -- with one inhabitant per axis there
is nothing yet for them to distinguish. They are here to fail later, when a
second inhabitant arrives.

`CallDiscipline` is the axis that is not yet degenerate. `docs/DECISIONS.md` 16
chooses documented APIs *rather than* direct syscalls, so both are named and
`decision16` selects one; `Profile.FollowsDecision16` is decidable and
`decision16_follows` discharges it.
-/

namespace Grass.Platform.Win32

/-! ## API baseline -/

/-- The Windows API version floor a program is authored against.

One inhabitant today, named because `docs/DECISIONS.md` 16 names it. -/
inductive ApiBaseline where
  /-- Windows 10, the baseline of `docs/DECISIONS.md` 16. -/
  | windows10
  deriving DecidableEq, Repr

/-! ## Architecture and ABI -/

/-- The architecture and calling-convention selection.

`docs/DECISIONS.md` 16 selects x64. `Grass.ABI.Win64` is the convention that
selection implies, which is why the ABI is not also spelled into the module
path. -/
inductive TargetAbi where
  /-- x86-64 under the Windows x64 calling convention. -/
  | x64
  deriving DecidableEq, Repr

/-- The width of a Win32 `HANDLE` under this ABI, in bits.

Total by construction. A second ABI cannot be added without answering this,
which is the point: `Grass.Platform.Win32.Console` states handles as
`BitVec 64`, and that width is a consequence of the selection rather than a
constant that happens to be right. -/
def TargetAbi.handleBits : TargetAbi → Nat
  | .x64 => 64

/-- The width of a Win32 pointer under this ABI, in bits. -/
def TargetAbi.pointerBits : TargetAbi → Nat
  | .x64 => 64

/-! ## Call discipline

The axis with two real inhabitants, because `docs/DECISIONS.md` 16 rejects one
of them. `documentedApi` is declared first so `Inhabited` and any
first-constructor default land on the selected discipline rather than on the
rejected one.
-/

/-- How a program reaches the operating system. -/
inductive CallDiscipline where
  /-- Through documented Win32 entry points. Selected by
  `docs/DECISIONS.md` 16. -/
  | documentedApi
  /-- Through the undocumented syscall boundary directly. Named so that it can
  be excluded rather than merely absent. -/
  | directSyscall
  deriving DecidableEq, Repr

instance : Inhabited CallDiscipline := ⟨.documentedApi⟩

/-! ## The profile -/

/-- A complete platform selection. -/
structure Profile where
  /-- The API version floor. -/
  baseline : ApiBaseline
  /-- The architecture and ABI. -/
  abi : TargetAbi
  /-- How the operating system is reached. -/
  discipline : CallDiscipline
  deriving DecidableEq, Repr

/-- The profile `docs/DECISIONS.md` 16 fixes. -/
def decision16 : Profile :=
  { baseline := .windows10, abi := .x64, discipline := .documentedApi }

instance : Inhabited Profile := ⟨decision16⟩

/-- Holds when a profile is the one `docs/DECISIONS.md` 16 fixes. -/
def Profile.FollowsDecision16 (p : Profile) : Prop :=
  p.baseline = .windows10 ∧ p.abi = .x64 ∧ p.discipline = .documentedApi

instance (p : Profile) : Decidable p.FollowsDecision16 := by
  unfold Profile.FollowsDecision16
  infer_instance

/-- `decision16` satisfies the decision it is named for. -/
theorem decision16_follows : decision16.FollowsDecision16 := by decide

/-- A profile reaching the kernel directly is not the decision's profile.

The one statement here that is not degenerate: `CallDiscipline` has two
inhabitants, so this rules something out. -/
theorem directSyscall_not_decision16 (p : Profile)
    (h : p.discipline = .directSyscall) : ¬ p.FollowsDecision16 := by
  intro ⟨_, _, hd⟩
  rw [h] at hd
  exact CallDiscipline.noConfusion hd

/-- Handle width under the selected profile.

`rfl` today, and stated so that a second `TargetAbi` inhabitant with a different
handle width has to change this line rather than pass silently. -/
theorem decision16_handleBits : decision16.abi.handleBits = 64 := rfl

/-- Pointer width under the selected profile. Degenerate for the same reason as
`decision16_handleBits`, and here for the same purpose. -/
theorem decision16_pointerBits : decision16.abi.pointerBits = 64 := rfl

end Grass.Platform.Win32
