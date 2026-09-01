import Spikes.«5_Spinning_Cube».Assembly
import Spikes.«5_Spinning_Cube».Macros
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
  `GetWindowLongPtrW,
  `SetWindowLongPtrW,
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
  .object `processHeap .pointer,
  .object `vkCreateInstancePtr .pointer,
  .object `instance .vkInstance,
  .object `surface .vkSurfaceKHR,
  .object `physical .vkPhysicalDevice,
  .object `qfamily .uint32,
  .object `device .vkDevice,
  .object `queue .vkQueue,
  .object `commandPool .vkCommandPool,
  .object `cmd .vkCommandBuffer,
  .object `imageAvail .vkSemaphore,
  .object `renderDone .vkSemaphore,
  .object `fence .vkFence,
  .object `vertModule .vkShaderModule,
  .object `fragModule .vkShaderModule,
  .object `pipelineLayout .vkPipelineLayout,
  .object `pipeline .vkPipeline,
  .object `swapchain .vkSwapchainKHR,
  .object `oldSwapchain .vkSwapchainKHR,
  .object `newSwapchain .vkSwapchainKHR,
  .object `count .uint32,
  .object `deviceCount .uint32,
  .object `devices .pointer,
  .object `extCount .uint32,
  .object `extProps .pointer,
  .object `queueCount .uint32,
  .object `queueProps .pointer,
  .object `supported .vkBool32,
  .object `fmtCount .uint32,
  .object `formats .pointer,
  .object `surfaceFormat .vkSurfaceFormatKHR,
  .object `imageCount .uint32,
  .object `requestedImageCount .uint32,
  .object `imagesAndViews .pointer,
  .object `images .pointer,
  .object `views .pointer,
  .object `imageInitialized .pointer,
  .object `initializedViewCount .uint32,
  .object `viewIndex .uint32,
  .object `imageIndex .uint32,
  .object `appInfo .vkApplicationInfo,
  .object `instanceCI .vkInstanceCreateInfo,
  .object `properties2 .vkPhysicalDeviceProperties2,
  .object `queueCI .vkDeviceQueueCreateInfo,
  .object `features2 .vkPhysicalDeviceFeatures2,
  .object `features13 .vkPhysicalDeviceVulkan13Features,
  .object `deviceCI .vkDeviceCreateInfo,
  .object `win32SurfaceCI .vkWin32SurfaceCreateInfoKHR,
  .object `commandPoolCI .vkCommandPoolCreateInfo,
  .object `commandBufferAI .vkCommandBufferAllocateInfo,
  .object `semaphoreCI .vkSemaphoreCreateInfo,
  .object `fenceCI .vkFenceCreateInfo,
  .object `vertexShaderCI .vkShaderModuleCreateInfo,
  .object `fragmentShaderCI .vkShaderModuleCreateInfo,
  .object `pipelineLayoutCI .vkPipelineLayoutCreateInfo,
  .object `pushConstantRange .vkPushConstantRange,
  .object `caps .vkSurfaceCapabilitiesKHR,
  .object `extent .vkExtent2D,
  .object `swapCI .vkSwapchainCreateInfoKHR,
  .object `pipelineRendering .vkPipelineRenderingCreateInfo,
  .object `graphicsCI .vkGraphicsPipelineCreateInfo,
  .object `imageViewCI .vkImageViewCreateInfo,
  .object `commandBufferBI .vkCommandBufferBeginInfo,
  .object `shaderStages (.array 2 .vkPipelineShaderStageCreateInfo),
  .object `emptyVertexInput .vkPipelineVertexInputStateCreateInfo,
  .object `lineList .vkPipelineInputAssemblyStateCreateInfo,
  .object `oneDynamicViewport .vkPipelineViewportStateCreateInfo,
  .object `lineRaster .vkPipelineRasterizationStateCreateInfo,
  .object `sample1 .vkPipelineMultisampleStateCreateInfo,
  .object `colorAttachment .vkPipelineColorBlendAttachmentState,
  .object `opaqueBlend .vkPipelineColorBlendStateCreateInfo,
  .object `dynamicStates (.array 2 .vkDynamicState),
  .object `viewportScissor .vkPipelineDynamicStateCreateInfo,
  .object `push .cubePushConstants,
  .object `barrier .vkImageMemoryBarrier2,
  .object `dependencyInfo .vkDependencyInfo,
  .object `rendering .vkRenderingInfo,
  .object `renderingAttachment .vkRenderingAttachmentInfo,
  .object `viewport .vkViewport,
  .object `scissor .vkRect2D,
  .object `submit .vkSubmitInfo2,
  .object `waitSemaphoreInfo .vkSemaphoreSubmitInfo,
  .object `signalSemaphoreInfo .vkSemaphoreSubmitInfo,
  .object `commandBufferInfo .vkCommandBufferSubmitInfo,
  .object `present .vkPresentInfoKHR,
  .object `instanceDispatch (.array instanceFunctionNames.size .pointer),
  .object `deviceDispatch (.array deviceFunctionNames.size .pointer),
  .object `ownership .cubeOwnershipLedger,
  .outgoingCallArea,
  .parallelMoveSpill
]

def cubeCallbackFrameObjects : Vec StackObjectSpec := #[
  .object `callbackHwnd .pointer,
  .object `callbackMessage .uint32,
  .object `callbackWparam .uint64,
  .object `callbackLparam .int64,
  .object `callbackState .pointer,
  .outgoingCallArea,
  .parallelMoveSpill
]

def cubeFrameLayout : StackFrameLayout :=
  StackFrameLayout.packWin64 cubeFrameObjects

def cubeCallbackFrameLayout : StackFrameLayout :=
  StackFrameLayout.packWin64 cubeCallbackFrameObjects

def cubeStaticObjects : StaticObjectTable := #[
  .utf16 `className "GrassCube\0",
  .utf16 `title "Grass Vulkan Cube\0",
  .ascii `grass "grass\0",
  .ascii `mainName "main\0",
  .ascii `vkCreateInstanceName "vkCreateInstance\0",
  .ascii `swapchainExtName "VK_KHR_swapchain\0",
  .cstringArray `instanceExts instanceExtensionNames,
  .cstringArray `deviceExts deviceExtensionNames,
  .cstringArray `instanceNames instanceFunctionNames,
  .cstringArray `deviceNames deviceFunctionNames,
  .uint32 `instanceSlotCount instanceFunctionNames.size,
  .uint32 `deviceSlotCount deviceFunctionNames.size,
  .float32 `one 1.0,
  .uint32 `colorFormat VK_FORMAT_B8G8R8A8_UNORM,
  .float64 `angularVelocity 0.6,
  .float64 `tau 6.283185307179586,
  .spirvWords `cubeVertexBytes (Spirv.writeWords cubeVertex),
  .spirvWords `cubeFragmentBytes (Spirv.writeWords cubeFragment)
]

def cubeSourceClosure : AsmSourceClosure plan where
  authored := cubeHost
  macros := cubeMacroDefinitions
  statics := cubeStaticObjects
  frames := #[cubeFrameLayout, cubeCallbackFrameLayout]
  imports := win32Imports ++ vulkanImports

def rawCubeHost : RawAsmSource plan := cubeSourceClosure.expand

def cubeReviewedBlocks : Vec Lean.Name := #[
  `entry, `wndproc, `wp_size, `wp_nccreate, `wp_reject_create, `wp_close,
  `wp_destroyed, `wp_ncdestroy, `wp_default, `vk_instance, `select_device,
  `create_device, `create_fixed, `recreate, `create_view_loop,
  `create_pipeline, `minimized_wait, `event_loop, `pump_messages,
  `request_exit, `messages_done, `acquired_suboptimal, `acquired,
  `acquired_first_layout, `acquired_layout_ready,
  `surface_result, `device_result, `clean_exit, `fail_init, `fail_runtime,
  `fail_surface, `fail_device, `clock_violation, `cleanup
]

def cubeReviewedMacroFragments : Vec Lean.Name := #[
  `expandArguments, `expandCall, `expandZeroInitializedStructure,
  `expandLoad, `expandUnsignedClamp, `expandConditionalDestroy,
  `checkedHeapAllocationBody, `checkedHeapReleaseBody,
  `instanceDispatchResolutionBody, `deviceDispatchResolutionBody,
  `deviceSelectionBody, `exactCStringScanBody,
  `queuePropertyInitializationBody, `surfaceSelectionBody,
  `extentAndCountBody,
  `swapchainRetirementBody, `installNewSwapchainBody,
  `reverseCleanupBody
]

def cubeReviewedStaticSymbols : Vec Lean.Name := #[
  `className, `title, `grass, `mainName, `vkCreateInstanceName,
  `swapchainExtName, `instanceExts, `deviceExts, `instanceNames,
  `deviceNames, `instanceSlotCount, `deviceSlotCount, `one, `colorFormat,
  `angularVelocity, `tau,
  `cubeVertexBytes, `cubeFragmentBytes
]

def cubeReviewedManifest : RawSourceManifest :=
  RawSourceManifest.fromReviewed
    (blocks := cubeReviewedBlocks)
    (fragmentBodies := cubeReviewedMacroFragments)
    (statics := cubeReviewedStaticSymbols)
    (frames := #[cubeFrameLayout, cubeCallbackFrameLayout])
    (imports := win32Imports ++ vulkanImports)

theorem cubeSourceElaboratesExactly :
    SourceElaboratesExactlyTo cubeSourceClosure rawCubeHost := rfl

theorem cubeSourceHasNoUnresolvedForms :
    rawCubeHost.unresolvedForms = #[] := by
  decide

theorem cubeSourceManifestExact :
    rawCubeHost.manifest = cubeReviewedManifest := by
  decide

theorem cubeSymbolResolutionExact :
    EverySymbolicAddressResolvesExactlyOnce rawCubeHost cubeReviewedManifest := by
  verify_symbol_resolution

theorem cubeFrameLifetimesNonoverlapping :
    PackedFrameDemandsHaveValidNonoverlappingLifetimes
      rawCubeHost #[cubeFrameLayout, cubeCallbackFrameLayout] := by
  verify_frame_layouts

structure CubeCallbackStateConnection where
  createParameter :
    CreateWindowParameterIsAddressOf rawCubeHost `state
  install :
    WmNcCreateInstallsUserData rawCubeHost `state GWLP_USERDATA
  recover :
    EveryCallbackStateAccessUsesRecoveredUserData rawCubeHost `state
  live :
    StackObjectLiveThroughWindowNcDestroy rawCubeHost cubeFrameLayout `state
  clear :
    WmNcDestroyClearsUserDataBeforeFrameRelease rawCubeHost GWLP_USERDATA
  imports :
    ExactCallbackImports rawCubeHost #[`GetWindowLongPtrW, `SetWindowLongPtrW]

theorem cubeCallbackStateConnection : CubeCallbackStateConnection := by
  verify_callback_state_connection

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
