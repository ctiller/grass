import Grass.Target.Device
import Grass.Shader.WGSL.Module

/-!
# WGSL as a `Grass.Target.ShaderLanguage`

Wires `Grass.Shader.WGSL.Module` into the device seam's `ShaderLanguage`
record. This file adds no new facts of its own: every law the seam asks for
is proved in `Grass.Shader.WGSL.Module`, so this is only the assembly.
-/

namespace Grass.Shader.WGSL

open Grass.Target

/-- WGSL, as the seam sees it: modules, their canonical UTF-8 byte encoding,
and the entry points a WebGPU pipeline binds a stage to. -/
def language : ShaderLanguage where
  Module := Module.Module
  encode := Module.Module.encode
  decode := Module.Module.decode
  decode_encode := Module.Module.decode_encode
  Entry := Module.Entry
  entries := Module.Module.entries
  Stage := Module.Stage
  stageOf := Module.Entry.stage

end Grass.Shader.WGSL
