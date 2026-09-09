import Grass.ABI.Win64.Convention
import Grass.Assembly.X86ControlFlow

/-!
# Initial saved-register extraction

This is a structural check over `CheckedProgram.collected.code`.
`extract?_program` establishes equality with the original checked program,
including its source and control-flow data. It rejects explicit local
transfers into the saved prefix, but makes no claim about entry from outside the
checked program. That validation remains an open obligation for a generated
prologue layer.
-/
namespace Grass.Assembly.SavedPrefix

open Grass.ABI.Win64 Grass.ISA.X86 X86Source X86ControlFlow

def pushedRegister? (item : CodeItem) : Option Gpr :=
  match item.instruction.mnemonic, item.instruction.operands with
  | .push, [.register ⟨reg, .w64⟩] => some reg
  | _, _ => none

private def splitPushes : List CodeItem → List CodeItem × List Gpr × List CodeItem
  | [] => ([], [], [])
  | item :: items =>
    match pushedRegister? item with
    | none => ([], [], item :: items)
    | some reg =>
      let (savedItems, registers, rest) := splitPushes items
      (item :: savedItems, reg :: registers, rest)

def IsPushOf (item : CodeItem) (reg : Gpr) : Prop := pushedRegister? item = some reg

instance (item : CodeItem) (reg : Gpr) : Decidable (IsPushOf item reg) :=
  inferInstanceAs (Decidable (pushedRegister? item = some reg))

/-- Explicit local transfers that enter at their target. Ordinary fallthrough
and conditional continuations are deliberately absent. -/
def localTakenTargets : Flow → List Nat
  | .jump target => [target]
  | .conditional _ target _ => [target]
  | .next _ | .externalCall _ _ | .trap => []

structure Result where
  private mk ::
  program : CheckedProgram
  registers : List Gpr
  savedItems : List CodeItem
  rest : List CodeItem
  partitionExact : program.collected.code = savedItems ++ rest
  lengthsExact : savedItems.length = registers.length
  pushesExact : ∀ pair ∈ savedItems.zip registers, IsPushOf pair.1 pair.2
  noLaterPush : ∀ item ∈ rest, pushedRegister? item = none
  registersNodup : registers.Nodup
  registersNonvolatile : ∀ reg ∈ registers, volatility reg = .nonvolatile
  excludesStackPointer : .rsp ∉ registers
  noReentryInsidePrefix : ∀ flow ∈ program.flows, ∀ target ∈ localTakenTargets flow,
    savedItems.length ≤ target

def extract? (program : CheckedProgram) : Option Result :=
  let (savedItems, registers, rest) := splitPushes program.collected.code
  if hp : program.collected.code = savedItems ++ rest then
    if hl : savedItems.length = registers.length then
      if he : ∀ pair ∈ savedItems.zip registers, IsPushOf pair.1 pair.2 then
        if hr : ∀ item ∈ rest, pushedRegister? item = none then
          if hn : registers.Nodup then
            if hv : ∀ reg ∈ registers, volatility reg = .nonvolatile then
              if hs : .rsp ∉ registers then
                if hf : ∀ flow ∈ program.flows, ∀ target ∈ localTakenTargets flow,
                    savedItems.length ≤ target then
                  some ⟨program, registers, savedItems, rest, hp, hl, he, hr, hn, hv, hs, hf⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem extract?_program {program : CheckedProgram} {result : Result}
    (success : extract? program = some result) : result.program = program := by
  unfold extract? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

theorem Result.prefix_length (result : Result) :
    result.savedItems.length = result.registers.length := result.lengthsExact

theorem Result.code_partition (result : Result) :
    result.program.collected.code = result.savedItems ++ result.rest := result.partitionExact

theorem Result.prefix_member_is_push (result : Result) (item : CodeItem) (reg : Gpr)
    (member : (item, reg) ∈ result.savedItems.zip result.registers) : IsPushOf item reg :=
  result.pushesExact (item, reg) member

theorem Result.register_nonvolatile (result : Result) (reg : Gpr)
    (member : reg ∈ result.registers) : volatility reg = .nonvolatile :=
  result.registersNonvolatile reg member

end Grass.Assembly.SavedPrefix

