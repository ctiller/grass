import Grass.Target.Device
import Grass.Shader.WGSL.Target

/-!
# WebGPU as a `Grass.Target.GraphicsAPI`

The WebGPU calls a host program makes to drive the same kind of frame Spike
5's Vulkan host drives, as a `Grass.Service.Domain`: adapter and device
request, surface configuration and the per-frame current texture, shader
module creation from WGSL text, bind group layout / pipeline layout / render
pipeline creation, a command encoder and one render pass, one draw call,
buffer creation and queue writes, queue submission, and present. Unlike
Vulkan's `VkResult`-and-handle pattern, WebGPU's creation calls either
succeed with a handle or fail silently (`GPUObjectBase` creation is
synchronous and non-throwing; only `requestAdapter`/`requestDevice` are
genuinely asynchronous and Promise-shaped), so responses here are plain
`Option handle` — there is no separate result code to carry.

Every handle is its own type (`Device`, `Texture`, `RenderPipeline`, ...)
for the same reason as `Grass.Device.Vulkan`: so a caller cannot pass a
`Buffer` where a `Texture` is expected. `Terminal := fun _ => False`: no
WebGPU call ends the process.

W3C WebGPU specification: https://www.w3.org/TR/webgpu/
-/

namespace Grass.Device.WebGPU

open Grass.Service

/-! ## Handles -/

structure Adapter where val : Nat deriving DecidableEq, Repr
structure Device where val : Nat deriving DecidableEq, Repr
structure Queue where val : Nat deriving DecidableEq, Repr
structure Texture where val : Nat deriving DecidableEq, Repr
structure TextureView where val : Nat deriving DecidableEq, Repr
structure ShaderModule where val : Nat deriving DecidableEq, Repr
structure BindGroupLayout where val : Nat deriving DecidableEq, Repr
structure PipelineLayout where val : Nat deriving DecidableEq, Repr
structure BindGroup where val : Nat deriving DecidableEq, Repr
structure RenderPipeline where val : Nat deriving DecidableEq, Repr
structure Buffer where val : Nat deriving DecidableEq, Repr
structure CommandEncoder where val : Nat deriving DecidableEq, Repr
structure RenderPassEncoder where val : Nat deriving DecidableEq, Repr
structure CommandBuffer where val : Nat deriving DecidableEq, Repr

/-! ## Argument structures -/

structure RequestAdapterOptions where
  powerPreferenceHighPerformance : Bool
deriving DecidableEq, Repr

structure DeviceDescriptor where
  requiredFeatures : List String
deriving Repr

structure Extent3D where
  width : Nat
  height : Nat
  depthOrArrayLayers : Nat
deriving DecidableEq, Repr

/-- `format` and `presentMode`/`alphaMode` are named rather than enumerated
in full: this seam carries the fields Spike 5's frame loop needs (extent and
a texture usage bit), not the whole `GPUCanvasConfiguration` dictionary. -/
structure SurfaceConfiguration where
  device : Device
  format : String
  usageRenderAttachment : Bool
  size : Extent3D
deriving DecidableEq, Repr

structure ShaderModuleDescriptor where
  code : List UInt8
deriving DecidableEq, Repr

structure BindGroupLayoutEntry where
  binding : Nat
  visibilityVertex : Bool
  visibilityFragment : Bool
  bufferUniform : Bool
deriving DecidableEq, Repr

structure BindGroupLayoutDescriptor where
  entries : List BindGroupLayoutEntry
deriving DecidableEq, Repr

structure PipelineLayoutDescriptor where
  bindGroupLayouts : List BindGroupLayout
deriving DecidableEq, Repr

structure BindGroupEntryBuffer where
  binding : Nat
  buffer : Buffer
  offset : Nat
  size : Nat
deriving DecidableEq, Repr

structure BindGroupDescriptor where
  layout : BindGroupLayout
  entries : List BindGroupEntryBuffer
deriving DecidableEq, Repr

structure VertexState where
  «module» : ShaderModule
  entryPoint : String
deriving Repr

structure FragmentTarget where
  format : String
deriving DecidableEq, Repr

structure FragmentState where
  «module» : ShaderModule
  entryPoint : String
  targets : List FragmentTarget
deriving Repr

/-- The fixed-function state a line-list render pipeline needs, at the
granularity Spike 5's single pipeline uses: `Grass.Device.Vulkan`'s
`GraphicsPipelineCreateInfo` is its Vulkan counterpart. -/
structure RenderPipelineDescriptor where
  layout : PipelineLayout
  vertex : VertexState
  fragment : Option FragmentState
  topologyLineList : Bool
deriving Repr

structure BufferDescriptor where
  size : Nat
  usageVertex : Bool
  usageUniform : Bool
  usageCopyDst : Bool
deriving DecidableEq, Repr

structure Color where
  r : Float
  g : Float
  b : Float
  a : Float
deriving Repr

structure RenderPassColorAttachment where
  view : TextureView
  clearValue : Color
deriving Repr

structure RenderPassDescriptor where
  colorAttachments : List RenderPassColorAttachment
deriving Repr

structure Viewport where
  x : Float
  y : Float
  width : Float
  height : Float
  minDepth : Float
  maxDepth : Float
deriving Repr

structure Rect2D where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
deriving DecidableEq, Repr

/-! ## Requests -/

inductive Request where
  | requestAdapter (options : RequestAdapterOptions)
  | requestDevice (adapter : Adapter) (descriptor : DeviceDescriptor)
  | destroyDevice (device : Device)
  | configureSurface (config : SurfaceConfiguration)
  | getCurrentTexture (device : Device)
  | createTextureView (texture : Texture)
  | createShaderModule (device : Device) (descriptor : ShaderModuleDescriptor)
  | destroyShaderModule (shaderModule : ShaderModule)
  | createBindGroupLayout (device : Device) (descriptor : BindGroupLayoutDescriptor)
  | createPipelineLayout (device : Device) (descriptor : PipelineLayoutDescriptor)
  | createBindGroup (device : Device) (descriptor : BindGroupDescriptor)
  | createRenderPipeline (device : Device) (descriptor : RenderPipelineDescriptor)
  | destroyRenderPipeline (pipeline : RenderPipeline)
  | createBuffer (device : Device) (descriptor : BufferDescriptor)
  | destroyBuffer (buffer : Buffer)
  | writeBuffer (queue : Queue) (buffer : Buffer) (offset : Nat) (data : List UInt8)
  | createCommandEncoder (device : Device)
  | beginRenderPass (encoder : CommandEncoder) (descriptor : RenderPassDescriptor)
  | setPipeline (pass : RenderPassEncoder) (pipeline : RenderPipeline)
  | setBindGroup (pass : RenderPassEncoder) (index : Nat) (bindGroup : BindGroup)
  | setViewport (pass : RenderPassEncoder) (viewport : Viewport)
  | setScissorRect (pass : RenderPassEncoder) (rect : Rect2D)
  | draw (pass : RenderPassEncoder) (vertexCount instanceCount firstVertex firstInstance : Nat)
  | endRenderPass (pass : RenderPassEncoder)
  | finishCommandEncoder (encoder : CommandEncoder)
  | submit (queue : Queue) (commandBuffers : List CommandBuffer)
  | present (device : Device)

/-! ## Responses -/

def Response : Request → Type
  | .requestAdapter _ => Option Adapter
  | .requestDevice .. => Option Device
  | .destroyDevice _ => Unit
  | .configureSurface _ => Unit
  | .getCurrentTexture _ => Option Texture
  | .createTextureView _ => Option TextureView
  | .createShaderModule .. => Option ShaderModule
  | .destroyShaderModule _ => Unit
  | .createBindGroupLayout .. => Option BindGroupLayout
  | .createPipelineLayout .. => Option PipelineLayout
  | .createBindGroup .. => Option BindGroup
  | .createRenderPipeline .. => Option RenderPipeline
  | .destroyRenderPipeline _ => Unit
  | .createBuffer .. => Option Buffer
  | .destroyBuffer _ => Unit
  | .writeBuffer .. => Unit
  | .createCommandEncoder _ => CommandEncoder
  | .beginRenderPass .. => RenderPassEncoder
  | .setPipeline .. => Unit
  | .setBindGroup .. => Unit
  | .setViewport .. => Unit
  | .setScissorRect .. => Unit
  | .draw .. => Unit
  | .endRenderPass _ => Unit
  | .finishCommandEncoder _ => CommandBuffer
  | .submit .. => Unit
  | .present _ => Unit

def domain : Domain where
  Request := Request
  Response := Response
  Terminal := fun _ => False

/-- The bytes a `createShaderModule` request carries, for every other
request `none`. -/
def shaderBytes : Request → Option (List UInt8)
  | .createShaderModule _ descriptor => some descriptor.code
  | _ => none

/-- WebGPU, as the device seam sees it: the request vocabulary above,
consuming WGSL modules. -/
def api : Grass.Target.GraphicsAPI where
  domain := domain
  language := Grass.Shader.WGSL.language
  shaderBytes := shaderBytes

theorem shaderBytes_createShaderModule (device : Device) (descriptor : ShaderModuleDescriptor) :
    api.shaderBytes (.createShaderModule device descriptor) = some descriptor.code := rfl

end Grass.Device.WebGPU
