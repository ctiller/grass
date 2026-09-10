import Grass.Target.Device
import Grass.Shader.SPIRV.Target

/-!
# Vulkan 1.3 as a `Grass.Target.GraphicsAPI`

The Vulkan calls a Win32/Vulkan/SPIR-V host program makes, as a
`Grass.Service.Domain`: instance and device creation and queue selection,
Win32 surface and swapchain lifetime (create/destroy/acquire/present),
shader module creation from SPIR-V words, pipeline layout and a dynamic-
rendering graphics pipeline, command pool/buffer, dynamic rendering
begin/end, one draw call, semaphores and fences, queue submission, and
buffer/device-memory allocation. It is the request vocabulary Spike 5's host
assembly calls (`Spikes/5_Spinning_Cube/Assembly.lean`'s `vk_call` sites),
generalized to typed request/response records instead of one program's
register and stack layout — nothing here names a spike, a window class, or a
push-constant layout.

Every handle a call returns is its own type (`Instance`, `Device`, `Queue`,
`SurfaceKHR`, ...) rather than a shared opaque `Nat`, so a caller cannot pass
a `Fence` where a `Semaphore` is expected; the platform tier is what marshals
these to and from real 64-bit Vulkan handles, a concern this seam does not
model. Arguments are typed Lean structures, not pointers or byte offsets:
`docs/TARGET_SEAMS.md` assigns pointer/struct marshalling to the platform
tier, not to the device seam.

Every create call keeps the real API's `VkResult` in its response, alongside
`Option handle` — `none` exactly when `result ≠ .success`, so a caller cannot
observe a handle from a failed call. `Terminal := fun _ => False`: no Vulkan
call ends the process.

Khronos Vulkan 1.3 specification:
https://registry.khronos.org/vulkan/specs/latest-ratified/html/vkspec.html
-/

namespace Grass.Device.Vulkan

open Grass.Service

/-! ## Handles

One structure per handle kind, so the type system tells `Instance` and
`Device` apart the way two different pointer types would in C, without this
seam committing to what a real handle's bits are. -/

structure Instance where val : Nat deriving DecidableEq, Repr
structure PhysicalDevice where val : Nat deriving DecidableEq, Repr
structure Device where val : Nat deriving DecidableEq, Repr
structure Queue where val : Nat deriving DecidableEq, Repr
structure SurfaceKHR where val : Nat deriving DecidableEq, Repr
structure SwapchainKHR where val : Nat deriving DecidableEq, Repr
structure Image where val : Nat deriving DecidableEq, Repr
structure ImageView where val : Nat deriving DecidableEq, Repr
structure ShaderModule where val : Nat deriving DecidableEq, Repr
structure PipelineLayout where val : Nat deriving DecidableEq, Repr
structure Pipeline where val : Nat deriving DecidableEq, Repr
structure CommandPool where val : Nat deriving DecidableEq, Repr
structure CommandBuffer where val : Nat deriving DecidableEq, Repr
structure Semaphore where val : Nat deriving DecidableEq, Repr
structure Fence where val : Nat deriving DecidableEq, Repr
structure DeviceMemory where val : Nat deriving DecidableEq, Repr
structure Buffer where val : Nat deriving DecidableEq, Repr

/-- `VkResult`, the subset the spike's error handling distinguishes plus the
common WSI outcomes. -/
inductive VkResult where
  | success
  | notReady
  | timeout
  | incomplete
  | suboptimalKHR
  | errorOutOfHostMemory
  | errorOutOfDeviceMemory
  | errorInitializationFailed
  | errorDeviceLost
  | errorLayerNotPresent
  | errorExtensionNotPresent
  | errorFeatureNotPresent
  | errorIncompatibleDriver
  | errorSurfaceLostKHR
  | errorNativeWindowInUseKHR
  | errorOutOfDateKHR
  | errorOutOfPoolMemory
deriving DecidableEq, Repr

/-! ## Argument structures -/

structure ApplicationInfo where
  applicationName : String
  applicationVersion : Nat
  engineName : String
  engineVersion : Nat
  apiVersion : Nat
deriving Repr

structure InstanceCreateInfo where
  applicationInfo : ApplicationInfo
  enabledExtensionNames : List String
deriving Repr

/-- Vulkan 1.3 features Spike 5 enables: dynamic rendering and
synchronization2, the two `VkPhysicalDeviceVulkan13Features` bits this device
tier needs. A driver-realized seam growing more features is a reviewed
addition, not this record's problem to anticipate. -/
structure PhysicalDeviceFeatures13 where
  dynamicRendering : Bool
  synchronization2 : Bool
deriving DecidableEq, Repr

structure DeviceQueueCreateInfo where
  queueFamilyIndex : Nat
  queuePriorities : List Float
deriving Repr

structure DeviceCreateInfo where
  queueCreateInfos : List DeviceQueueCreateInfo
  enabledExtensionNames : List String
  features13 : PhysicalDeviceFeatures13
deriving Repr

/-- The Win32-specific surface constructor; a non-Win32 platform adds its own
`createXlibSurface`/`createWaylandSurface`/... request rather than widening
this one, mirroring how `Grass.Target.Platform` is one record per platform. -/
structure Win32SurfaceCreateInfo where
  hinstance : Nat
  hwnd : Nat
deriving DecidableEq, Repr

structure Extent2D where
  width : Nat
  height : Nat
deriving DecidableEq, Repr

structure SurfaceCapabilitiesKHR where
  minImageCount : Nat
  maxImageCount : Nat
  currentExtent : Extent2D
  supportedUsageColorAttachment : Bool
  supportedCompositeAlphaOpaque : Bool
deriving DecidableEq, Repr

structure SurfaceFormatKHR where
  format : Nat
  colorSpace : Nat
deriving DecidableEq, Repr

structure SwapchainCreateInfoKHR where
  surface : SurfaceKHR
  minImageCount : Nat
  imageFormat : Nat
  imageColorSpace : Nat
  imageExtent : Extent2D
  imageUsageColorAttachment : Bool
  presentModeFIFO : Bool
  oldSwapchain : Option SwapchainKHR
deriving Repr

structure ImageSubresourceRange where
  baseMipLevel : Nat
  levelCount : Nat
  baseArrayLayer : Nat
  layerCount : Nat
deriving DecidableEq, Repr

structure ImageViewCreateInfo where
  image : Image
  format : Nat
  subresourceRange : ImageSubresourceRange
deriving DecidableEq, Repr

/-- `code` is exactly the SPIR-V module's canonical bytes
(`Grass.Shader.SPIRV.language.encode`); `GraphicsAPI.shaderBytes` projects it
back out below. -/
structure ShaderModuleCreateInfo where
  code : List UInt8
deriving DecidableEq, Repr

structure PushConstantRange where
  stageVertex : Bool
  stageFragment : Bool
  offset : Nat
  size : Nat
deriving DecidableEq, Repr

structure PipelineLayoutCreateInfo where
  pushConstantRanges : List PushConstantRange
deriving DecidableEq, Repr

structure PipelineShaderStageCreateInfo where
  stageVertex : Bool
  «module» : ShaderModule
  entryPoint : String
deriving Repr

/-- The fixed-function pipeline state a dynamic-rendering graphics pipeline
needs, at the granularity Spike 5's single line-list pipeline uses. -/
structure GraphicsPipelineCreateInfo where
  stages : List PipelineShaderStageCreateInfo
  topologyLineList : Bool
  colorAttachmentFormats : List Nat
  layout : PipelineLayout
deriving Repr

structure CommandPoolCreateInfo where
  queueFamilyIndex : Nat
  resetCommandBuffer : Bool
deriving DecidableEq, Repr

structure CommandBufferAllocateInfo where
  commandPool : CommandPool
  count : Nat
deriving DecidableEq, Repr

structure CommandBufferBeginInfo where
  oneTimeSubmit : Bool
deriving DecidableEq, Repr

structure ClearColorValue where
  r : Float
  g : Float
  b : Float
  a : Float
deriving Repr

structure RenderingAttachmentInfo where
  imageView : ImageView
  clear : ClearColorValue
deriving Repr

structure Rect2D where
  offsetX : Nat
  offsetY : Nat
  extent : Extent2D
deriving DecidableEq, Repr

structure RenderingInfo where
  renderArea : Rect2D
  colorAttachments : List RenderingAttachmentInfo
deriving Repr

structure Viewport where
  x : Float
  y : Float
  width : Float
  height : Float
  minDepth : Float
  maxDepth : Float
deriving Repr

/-- An `VkImageMemoryBarrier2`/`VkDependencyInfo` pair collapsed to the
fields Spike 5's layout transitions use: old/new layout by name, and the
image being transitioned. Synchronization masks are simplified to "before
and after color attachment output", the one stage transition the spike's
render loop needs. -/
structure ImageLayoutTransition where
  image : Image
  fromUndefined : Bool
  toColorAttachment : Bool
  toPresentSrc : Bool
deriving DecidableEq, Repr

structure DependencyInfo where
  imageBarriers : List ImageLayoutTransition
deriving DecidableEq, Repr

structure SemaphoreSubmitInfo where
  semaphore : Semaphore
deriving DecidableEq, Repr

structure CommandBufferSubmitInfo where
  commandBuffer : CommandBuffer
deriving DecidableEq, Repr

structure SubmitInfo2 where
  waitSemaphores : List SemaphoreSubmitInfo
  commandBuffers : List CommandBufferSubmitInfo
  signalSemaphores : List SemaphoreSubmitInfo
deriving DecidableEq, Repr

structure PresentInfoKHR where
  waitSemaphores : List Semaphore
  swapchain : SwapchainKHR
  imageIndex : Nat
deriving DecidableEq, Repr

structure MemoryAllocateInfo where
  allocationSize : Nat
  memoryTypeIndex : Nat
deriving DecidableEq, Repr

structure BufferCreateInfo where
  size : Nat
  usageTransferDst : Bool
  usageVertex : Bool
deriving DecidableEq, Repr

/-! ## Requests -/

inductive Request where
  | createInstance (info : InstanceCreateInfo)
  | destroyInstance (instanceHandle : Instance)
  | enumeratePhysicalDevices (instanceHandle : Instance)
  | createDevice (physicalDevice : PhysicalDevice) (info : DeviceCreateInfo)
  | destroyDevice (device : Device)
  | getDeviceQueue (device : Device) (queueFamilyIndex queueIndex : Nat)
  | deviceWaitIdle (device : Device)
  | createWin32SurfaceKHR (instanceHandle : Instance) (info : Win32SurfaceCreateInfo)
  | destroySurfaceKHR (instanceHandle : Instance) (surface : SurfaceKHR)
  | getPhysicalDeviceSurfaceCapabilitiesKHR (physicalDevice : PhysicalDevice) (surface : SurfaceKHR)
  | getPhysicalDeviceSurfaceFormatsKHR (physicalDevice : PhysicalDevice) (surface : SurfaceKHR)
  | createSwapchainKHR (device : Device) (info : SwapchainCreateInfoKHR)
  | destroySwapchainKHR (device : Device) (swapchain : SwapchainKHR)
  | getSwapchainImagesKHR (device : Device) (swapchain : SwapchainKHR)
  | acquireNextImageKHR (device : Device) (swapchain : SwapchainKHR) (timeoutNanos : Nat)
      (semaphore : Option Semaphore) (fence : Option Fence)
  | queuePresentKHR (queue : Queue) (info : PresentInfoKHR)
  | createImageView (device : Device) (info : ImageViewCreateInfo)
  | destroyImageView (device : Device) (view : ImageView)
  | createShaderModule (device : Device) (info : ShaderModuleCreateInfo)
  | destroyShaderModule (device : Device) (shaderModule : ShaderModule)
  | createPipelineLayout (device : Device) (info : PipelineLayoutCreateInfo)
  | destroyPipelineLayout (device : Device) (layout : PipelineLayout)
  | createGraphicsPipeline (device : Device) (info : GraphicsPipelineCreateInfo)
  | destroyPipeline (device : Device) (pipeline : Pipeline)
  | createCommandPool (device : Device) (info : CommandPoolCreateInfo)
  | destroyCommandPool (device : Device) (pool : CommandPool)
  | allocateCommandBuffers (device : Device) (info : CommandBufferAllocateInfo)
  | resetCommandBuffer (commandBuffer : CommandBuffer)
  | beginCommandBuffer (commandBuffer : CommandBuffer) (info : CommandBufferBeginInfo)
  | endCommandBuffer (commandBuffer : CommandBuffer)
  | cmdPipelineBarrier2 (commandBuffer : CommandBuffer) (info : DependencyInfo)
  | cmdBeginRendering (commandBuffer : CommandBuffer) (info : RenderingInfo)
  | cmdEndRendering (commandBuffer : CommandBuffer)
  | cmdBindPipeline (commandBuffer : CommandBuffer) (pipeline : Pipeline)
  | cmdSetViewport (commandBuffer : CommandBuffer) (viewport : Viewport)
  | cmdSetScissor (commandBuffer : CommandBuffer) (scissor : Rect2D)
  | cmdPushConstants (commandBuffer : CommandBuffer) (layout : PipelineLayout) (offset : Nat) (values : List UInt8)
  | cmdDraw (commandBuffer : CommandBuffer) (vertexCount instanceCount firstVertex firstInstance : Nat)
  | queueSubmit2 (queue : Queue) (info : SubmitInfo2) (fence : Option Fence)
  | createSemaphore (device : Device)
  | destroySemaphore (device : Device) (semaphore : Semaphore)
  | createFence (device : Device) (signaled : Bool)
  | destroyFence (device : Device) (fence : Fence)
  | waitForFences (device : Device) (fences : List Fence) (waitAll : Bool) (timeoutNanos : Nat)
  | resetFences (device : Device) (fences : List Fence)
  | allocateMemory (device : Device) (info : MemoryAllocateInfo)
  | freeMemory (device : Device) (memory : DeviceMemory)
  | createBuffer (device : Device) (info : BufferCreateInfo)
  | destroyBuffer (device : Device) (buffer : Buffer)
  | bindBufferMemory (device : Device) (buffer : Buffer) (memory : DeviceMemory) (offset : Nat)

/-! ## Responses -/

structure Created (α : Type) where
  result : VkResult
  handle : Option α
deriving Repr

structure Listed (α : Type) where
  result : VkResult
  values : List α
deriving Repr

def Response : Request → Type
  | .createInstance _ => Created Instance
  | .destroyInstance _ => Unit
  | .enumeratePhysicalDevices _ => Listed PhysicalDevice
  | .createDevice .. => Created Device
  | .destroyDevice _ => Unit
  | .getDeviceQueue .. => Queue
  | .deviceWaitIdle _ => VkResult
  | .createWin32SurfaceKHR .. => Created SurfaceKHR
  | .destroySurfaceKHR .. => Unit
  | .getPhysicalDeviceSurfaceCapabilitiesKHR .. => Created SurfaceCapabilitiesKHR
  | .getPhysicalDeviceSurfaceFormatsKHR .. => Listed SurfaceFormatKHR
  | .createSwapchainKHR .. => Created SwapchainKHR
  | .destroySwapchainKHR .. => Unit
  | .getSwapchainImagesKHR .. => Listed Image
  | .acquireNextImageKHR .. => VkResult × Option Nat
  | .queuePresentKHR .. => VkResult
  | .createImageView .. => Created ImageView
  | .destroyImageView .. => Unit
  | .createShaderModule .. => Created ShaderModule
  | .destroyShaderModule .. => Unit
  | .createPipelineLayout .. => Created PipelineLayout
  | .destroyPipelineLayout .. => Unit
  | .createGraphicsPipeline .. => Created Pipeline
  | .destroyPipeline .. => Unit
  | .createCommandPool .. => Created CommandPool
  | .destroyCommandPool .. => Unit
  | .allocateCommandBuffers .. => Listed CommandBuffer
  | .resetCommandBuffer _ => VkResult
  | .beginCommandBuffer .. => VkResult
  | .endCommandBuffer _ => VkResult
  | .cmdPipelineBarrier2 .. => Unit
  | .cmdBeginRendering .. => Unit
  | .cmdEndRendering _ => Unit
  | .cmdBindPipeline .. => Unit
  | .cmdSetViewport .. => Unit
  | .cmdSetScissor .. => Unit
  | .cmdPushConstants .. => Unit
  | .cmdDraw .. => Unit
  | .queueSubmit2 .. => VkResult
  | .createSemaphore _ => Created Semaphore
  | .destroySemaphore .. => Unit
  | .createFence .. => Created Fence
  | .destroyFence .. => Unit
  | .waitForFences .. => VkResult
  | .resetFences .. => VkResult
  | .allocateMemory .. => Created DeviceMemory
  | .freeMemory .. => Unit
  | .createBuffer .. => Created Buffer
  | .destroyBuffer .. => Unit
  | .bindBufferMemory .. => VkResult

def domain : Domain where
  Request := Request
  Response := Response
  Terminal := fun _ => False

/-- The bytes a `createShaderModule` request carries, for every other
request `none`: this is what lets the certificate relate the module the
shader author verified to the exact bytes the host hands the driver. -/
def shaderBytes : Request → Option (List UInt8)
  | .createShaderModule _ info => some info.code
  | _ => none

/-- Vulkan 1.3, as the device seam sees it: the request vocabulary above,
consuming SPIR-V modules. -/
def api : Grass.Target.GraphicsAPI where
  domain := domain
  language := Grass.Shader.SPIRV.language
  shaderBytes := shaderBytes

theorem shaderBytes_createShaderModule (device : Device) (info : ShaderModuleCreateInfo) :
    api.shaderBytes (.createShaderModule device info) = some info.code := rfl

end Grass.Device.Vulkan
