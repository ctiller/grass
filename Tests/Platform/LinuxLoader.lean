import Grass.Platform.Linux.Loader
import Tests.Artifact.ELF.LoadPlan

set_option maxRecDepth 100000

namespace Tests.Platform.LinuxLoader

open Grass.Core Grass.Memory Grass.Memory.ImageInstall Grass.ISA.AArch64
open Grass.Artifact.ELF Grass.Platform.Linux.Loader Grass.Std.Logical

def contexts : FreshSupply ContextTag := .initial
def context : ContextId := contexts.fresh.1
def allocations : FreshSupply AllocTag := .initial
def storages : FreshSupply StorageTag := .initial
def epochs : FreshSupply EpochTag := .initial

def environment : MachineState :=
  { MachineState.initial .empty with
    contexts := Grass.Std.Logical.FiniteMap.insert .empty context .thread }

def cpu : Cpu := { gpr := fun _ => 0x1234, pc := 0, nzcv := 0b1010 }

def identity : RegionIdentity :=
  { allocation := allocations.fresh.1, storage := storages.fresh.1, epoch := epochs.fresh.1 }

def inputs : Inputs :=
  { environment, context, identities := [identity], cpu }

def loaded := load? Tests.Artifact.ELF.LoadPlan.profile Tests.Artifact.ELF.LoadPlan.image inputs

example : loaded.isSome := by decide

example (image : LoadedImage Tests.Artifact.ELF.LoadPlan.profile
    Tests.Artifact.ELF.LoadPlan.image inputs) :
    image.cpu.gpr = inputs.cpu.gpr ∧ image.cpu.nzcv = inputs.cpu.nzcv :=
  image.registers_exact

example (image : LoadedImage Tests.Artifact.ELF.LoadPlan.profile
    Tests.Artifact.ELF.LoadPlan.image inputs) :
    { image.machine with memory := inputs.environment.memory } = inputs.environment :=
  image.environment_frame

example (image : LoadedImage Tests.Artifact.ELF.LoadPlan.profile
    Tests.Artifact.ELF.LoadPlan.image inputs) :
    image.cpu.pc = image.plan.image.header.entry := image.entry_exact

example (image : LoadedImage Tests.Artifact.ELF.LoadPlan.profile
    Tests.Artifact.ELF.LoadPlan.image inputs)
    (paired : (Tests.Artifact.ELF.LoadPlan.load, identity) ∈
      (loadSegments image.plan.image).zip inputs.identities) :
    image.machine.memory.cellAt? identity.allocation 0 = some (0xa5, true) :=
  image.file_byte paired (by decide) (by decide)

example (image : LoadedImage Tests.Artifact.ELF.LoadPlan.profile
    Tests.Artifact.ELF.LoadPlan.image inputs)
    (paired : (Tests.Artifact.ELF.LoadPlan.load, identity) ∈
      (loadSegments image.plan.image).zip inputs.identities) :
    image.machine.memory.cellAt? identity.allocation 2 = some (0, true) :=
  image.zero_byte paired (by decide) (by decide)

/-- Installation needs exactly one fresh identity per checked PT_LOAD segment. -/
example :
    (load? Tests.Artifact.ELF.LoadPlan.profile Tests.Artifact.ELF.LoadPlan.image
      { inputs with identities := [] }).isNone := by decide

/-- The selected initial instruction range is four-byte aligned. -/
def unalignedImage : Grass.Std.Logical.ByteArray :=
  Tests.Artifact.ELF.LoadPlan.imageWith
    (Tests.Artifact.ELF.LoadPlan.elfHeader (entry := 0x400001))
    [Tests.Artifact.ELF.LoadPlan.load]

example :
    (load? Tests.Artifact.ELF.LoadPlan.profile unalignedImage inputs).isNone := by decide

/-- Reusing an allocation/storage identity already present in the environment is refused. -/
def collisionMemory : MemoryState :=
  (installRegions? .empty
    [regionFor Tests.Artifact.ELF.LoadPlan.image context Tests.Artifact.ELF.LoadPlan.load identity]).getD .empty

def collisionInputs : Inputs :=
  { inputs with environment := { MachineState.initial collisionMemory with
      contexts := Grass.Std.Logical.FiniteMap.insert .empty context .thread } }

example :
    (load? Tests.Artifact.ELF.LoadPlan.profile Tests.Artifact.ELF.LoadPlan.image collisionInputs).isNone := by
  decide

end Tests.Platform.LinuxLoader
