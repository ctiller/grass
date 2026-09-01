import Spikes.«5_Spinning_Cube».Assembly
import Spikes.«5_Spinning_Cube».Staged

namespace Grass.Spikes.SpinningCube

def instanceExtensionNames : Vec CString := #[
  "VK_KHR_surface",
  "VK_KHR_win32_surface"
]

def deviceExtensionNames : Vec CString := #["VK_KHR_swapchain"]

def instanceFunctionNames : Vec CString := #[
  "vkDestroyInstance",
  "vkCreateWin32SurfaceKHR",
  "vkDestroySurfaceKHR",
  "vkEnumeratePhysicalDevices",
  "vkGetPhysicalDeviceProperties2",
  "vkGetPhysicalDeviceFeatures2",
  "vkEnumerateDeviceExtensionProperties",
  "vkGetPhysicalDeviceQueueFamilyProperties2",
  "vkGetPhysicalDeviceSurfaceSupportKHR",
  "vkGetPhysicalDeviceSurfaceCapabilitiesKHR",
  "vkGetPhysicalDeviceSurfaceFormatsKHR",
  "vkCreateDevice"
]

def deviceFunctionNames : Vec CString := #[
  "vkDestroyDevice",
  "vkGetDeviceQueue",
  "vkCreateCommandPool",
  "vkDestroyCommandPool",
  "vkAllocateCommandBuffers",
  "vkCreateSemaphore",
  "vkDestroySemaphore",
  "vkCreateFence",
  "vkDestroyFence",
  "vkCreateShaderModule",
  "vkDestroyShaderModule",
  "vkCreatePipelineLayout",
  "vkDestroyPipelineLayout",
  "vkCreateSwapchainKHR",
  "vkDestroySwapchainKHR",
  "vkGetSwapchainImagesKHR",
  "vkCreateImageView",
  "vkDestroyImageView",
  "vkCreateGraphicsPipelines",
  "vkDestroyPipeline",
  "vkDeviceWaitIdle",
  "vkWaitForFences",
  "vkAcquireNextImageKHR",
  "vkResetFences",
  "vkResetCommandBuffer",
  "vkBeginCommandBuffer",
  "vkCmdPipelineBarrier2",
  "vkCmdBeginRendering",
  "vkCmdBindPipeline",
  "vkCmdSetViewport",
  "vkCmdSetScissor",
  "vkCmdPushConstants",
  "vkCmdDraw",
  "vkCmdEndRendering",
  "vkEndCommandBuffer",
  "vkQueueSubmit2",
  "vkQueuePresentKHR"
]

def win32Imports : Vec ImportSymbol := #[
  `GetModuleHandleW,
  `LoadCursorW,
  `RegisterClassExW,
  `CreateWindowExW,
  `ShowWindow,
  `DestroyWindow,
  `DefWindowProcW,
  `WaitMessage,
  `PeekMessageW,
  `TranslateMessage,
  `DispatchMessageW,
  `UnregisterClassW,
  `QueryPerformanceFrequency,
  `QueryPerformanceCounter,
  `GetProcessHeap,
  `HeapAlloc,
  `HeapFree,
  `ExitProcess
]

def vulkanImports : Vec ImportSymbol := #[
  `vkGetInstanceProcAddr,
  `vkGetDeviceProcAddr
]

def cubeFrameObjects : Vec StackObjectSpec := #[
  .object `wc .wndClassExW,
  .object `msg .msg,
  .object `state .cubeWindowState,
  .object `qpcFrequency .int64,
  .object `qpcEpoch .int64,
  .object `qpcPrevious .int64,
  .object `qpcNow .int64,
  .object `appInfo .vkApplicationInfo,
  .object `instanceCI .vkInstanceCreateInfo,
  .object `queueCI .vkDeviceQueueCreateInfo,
  .object `features2 .vkPhysicalDeviceFeatures2,
  .object `features13 .vkPhysicalDeviceVulkan13Features,
  .object `deviceCI .vkDeviceCreateInfo,
  .object `caps .vkSurfaceCapabilitiesKHR,
  .object `extent .vkExtent2D,
  .object `swapCI .vkSwapchainCreateInfoKHR,
  .object `pipelineRendering .vkPipelineRenderingCreateInfo,
  .object `graphicsCI .vkGraphicsPipelineCreateInfo,
  .object `shaderStages (.array 2 .vkPipelineShaderStageCreateInfo),
  .object `push .cubePushConstants,
  .object `barrier .vkImageMemoryBarrier2,
  .object `rendering .vkRenderingInfo,
  .object `submit .vkSubmitInfo2,
  .object `present .vkPresentInfoKHR,
  .object `instanceDispatch (.array instanceFunctionNames.size .pointer),
  .object `deviceDispatch (.array deviceFunctionNames.size .pointer),
  .object `ownership .cubeOwnershipLedger,
  .outgoingCallArea,
  .parallelMoveSpill
]

def cubeFrameLayout : StackFrameLayout :=
  StackFrameLayout.packWin64 cubeFrameObjects

def cubeStaticObjects : StaticObjectTable := #[
  .utf16 `className "GrassCube\0",
  .utf16 `title "Grass Vulkan Cube\0",
  .ascii `grass "grass\0",
  .ascii `mainName "main\0",
  .cstringArray `instanceExts instanceExtensionNames,
  .cstringArray `deviceExts deviceExtensionNames,
  .cstringArray `instanceNames instanceFunctionNames,
  .cstringArray `deviceNames deviceFunctionNames,
  .float32 `one 1.0,
  .float64 `angularVelocity 0.6,
  .float64 `tau 6.283185307179586,
  .spirvWords `cubeVertexBytes (Spirv.writeWords cubeVertex),
  .spirvWords `cubeFragmentBytes (Spirv.writeWords cubeFragment)
]

def cubeMacroDefinitions : AsmMacroRegistry plan := #[
  AsmMacro.win64Call,
  AsmMacro.vulkanDispatchCall,
  AsmMacro.zeroInitializedStructure,
  AsmMacro.widthCheckedStore,
  AsmMacro.checkedHeapAllocation,
  AsmMacro.checkedHeapRelease,
  AsmMacro.instanceDispatchResolution,
  AsmMacro.deviceDispatchResolution,
  AsmMacro.vulkanDeviceEnumeration,
  AsmMacro.vulkanDeviceSelection,
  AsmMacro.requiredSurfaceFormatSelection,
  AsmMacro.swapchainExtentAndCount,
  AsmMacro.swapchainGenerationRetirement,
  AsmMacro.reverseDependencyCleanup,
  AsmMacro.containedViolationTail,
  AsmMacro.exitProcess
]

def cubeSourceClosure : AsmSourceClosure plan where
  authored := cubeHost
  macros := cubeMacroDefinitions
  statics := cubeStaticObjects
  frames := #[cubeFrameLayout]
  imports := win32Imports ++ vulkanImports

def rawCubeHost : RawAsmSource plan := cubeSourceClosure.expand

theorem cubeSourceElaboratesExactly :
    SourceElaboratesExactlyTo cubeSourceClosure rawCubeHost := rfl

theorem cubeSourceHasNoUnresolvedForms :
    rawCubeHost.unresolvedForms = #[] := by
  decide

theorem cubeSourceManifestExact :
    rawCubeHost.manifest = cubeSourceClosure.expectedManifest := by
  decide

theorem rawHostImplementsDriver :
    HostAssemblyImplements
      stagedProcessRealization
      plan rawCubeHost :=
  hostImplementsDriver.transportSourceElaboration cubeSourceElaboratesExactly

def cubeMachineBlendInput :
    MachineBlendInput plan stagedProcessRealization :=
  MachineBlendInput.heterogeneous
    (host := rawCubeHost)
    (devices := #[cubeVertex, cubeFragment])
    (scopeSources := cube_exact_closed_scope_sources)
    (crossIsa := cube_host_shader_edges_exact)

theorem cubeMachineBlendInputComplete :
    EveryReachableClosedScopeAppearsExactlyOnce cubeMachineBlendInput :=
  cube_exact_closed_scope_coverage

end Grass.Spikes.SpinningCube
