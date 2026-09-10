import Grass.Service.Domain

/-!
# The device seam

A graphics API is, to the host program, a service domain: requests that
create devices, buffers, pipelines and shader modules, submit work, and
present. A shader language is a second artifact language: modules with a
canonical encoding the host embeds as data and hands to the API through a
request that carries shader bytes.

The host machine tier does not execute shaders. A `GraphicsAPI` names which
requests carry shader code so the certificate can relate the bytes the host
passes to the shader module the author verified, and a `ShaderLanguage`
supplies the encoding round trip that makes that relation exact. Shader
execution semantics live in the language's own model and are connected by a
device-side refinement, not by the host ISA.
-/

namespace Grass.Target

open Grass.Service

/-- A shader language: SPIR-V, WGSL. -/
structure ShaderLanguage where
  /-- A whole shader module. -/
  Module : Type
  /-- Canonical encoding (SPIR-V words as little-endian bytes; WGSL as UTF-8). -/
  encode : Module → List UInt8
  /-- Recover a module from its bytes. -/
  decode : List UInt8 → Option Module
  decode_encode : ∀ module, decode (encode module) = some module
  /-- Entry point identification within a module. -/
  Entry : Type
  entries : Module → List Entry
  /-- Pipeline stage of an entry point. -/
  Stage : Type
  stageOf : Entry → Stage

/-- A graphics API: Vulkan, WebGPU. -/
structure GraphicsAPI where
  /-- The API's request vocabulary as a service domain. -/
  domain : Domain
  /-- The shader language the API consumes. -/
  language : ShaderLanguage
  /-- The shader bytes a request carries, when it creates a shader module. -/
  shaderBytes : domain.Request → Option (List UInt8)

namespace GraphicsAPI

/-- A request that creates a shader module from bytes the language decodes. -/
def CarriesModule (api : GraphicsAPI) (request : api.domain.Request)
    (module : api.language.Module) : Prop :=
  api.shaderBytes request = some (api.language.encode module)

/-- The module carried by a request is recovered exactly by the language's
decoder, so the host never has to reason about shader bytes. -/
theorem decode_of_carriesModule (api : GraphicsAPI) {request : api.domain.Request}
    {module : api.language.Module} (carries : api.CarriesModule request module) :
    ∃ bytes, api.shaderBytes request = some bytes ∧ api.language.decode bytes = some module :=
  ⟨_, carries, api.language.decode_encode module⟩

end GraphicsAPI

end Grass.Target
