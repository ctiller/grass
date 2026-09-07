import Grass.Core.Name

/-!
# The platform profile, as values rather than as a module path

`docs/DECISIONS.md` 16 fixes the initial platform profile: "Win32 x64 with
Windows 10 as API baseline and documented APIs rather than direct syscalls".

`docs/MODULES.md` requires those to be *selections made through this API* rather
than components of a module path, and replaces the spike spelling
`Grass.Platform.Win10.X64` with `Grass.Platform.Win32`. A path segment is
not a value, so it supports no comparison and nothing can be discharged
against it, and one segment holding a deployment floor and an architecture
conflates four separate choices. `Profile.FollowsDecision16` is decidable,
which is what the change buys.

## Mechanism, and its absence

One mechanism, on one axis: `TargetAbi.handleBits` and
`TargetAbi.pointerBits` are total functions of `TargetAbi`, so a second ABI
cannot be added without stating its widths: omitting a case is
`error: Missing cases: x86` under this repository's settings. That was checked
by adding an `x86` inhabitant, not assumed.

Everything else here is vocabulary with no enforcement behind it, and an earlier
version of this header claimed otherwise in three ways a reviewer falsified by
running the mutations:

* "the three axes are total functions" -- they are inductives, and only
  `TargetAbi` has any total function over it. Adding `| windows11` to
  `ApiBaseline`, or a fourth `CallDiscipline`, compiles with zero friction,
  because nothing in the repository matches on either.
* two `rfl` equations were said to be "here to fail later, when a second
  inhabitant arrives". They cannot fail: they were about the ABI that
  `decision16` selects, which stays `.x64` whatever else is added. They have been deleted rather than
  reworded: an equation that holds by `rfl` under every extension is not a
  safeguard.
* the widths were said to be "a consequence of the selection" for
  `Grass.Platform.Win32.Console`. Nothing consumes this module.
  `Console.lean` writes `BitVec 64` literally and does not import it, so the
  width is a constant that happens to be right -- the exact hazard `Console`
  itself records for `StdHandleId.value`.

`docs/DECISIONS.md` 16 fixes x64 but says nothing about how wide a `HANDLE` is,
so `handleBits` and `pointerBits` are uncited external ABI facts and are carried
as debt in `Tests/ISA/X86/LedgerAudit.lean`'s `owed` list. Wiring `Console` to
this module, so the width follows the selection rather than agreeing with it by
coincidence, is an open obligation and not something this file has done.

`CallDiscipline` is the one axis that is not degenerate as *vocabulary*:
`docs/DECISIONS.md` 16 chooses documented APIs *rather than* direct syscalls, so
both are named, `Profile.FollowsDecision16` is decidable, `decision16_follows`
discharges it, and `directSyscall_not_decision16` rules the alternative out.
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

`TargetAbi.handleBits` is total, so a second ABI cannot be added without
answering this.

That exhaustiveness is the only guarantee here. `Grass.Platform.Win32.Console`
states handles as `BitVec 64` independently and does not import this module, so
the two agree by inspection rather than by construction. An external ABI fact
with no citation: carried in `owed` by `Tests/ISA/X86/LedgerAudit.lean`. -/
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

end Grass.Platform.Win32
