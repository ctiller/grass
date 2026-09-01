import Grass.Assembly.X86
import Grass.Assembly.Spirv
import Spikes.«5_Spinning_Cube».Plan

namespace Grass.Spikes.SpinningCube

def cubeVertex : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  %glsl = OpExtInstImport "GLSL.std.450"
  OpMemoryModel Logical GLSL450
  OpEntryPoint Vertex %main "main" %vertexIndex %positionOut %colorOut
    %push %positionsVar %indicesVar
  OpName %main "main"
  OpDecorate %vertexIndex BuiltIn VertexIndex
  OpDecorate %positionOut BuiltIn Position
  OpDecorate %colorOut Location 0
  OpMemberDecorate %Push 0 Offset 0
  OpMemberDecorate %Push 1 Offset 4
  OpDecorate %Push Block

  %void = OpTypeVoid
  %fn = OpTypeFunction %void
  %bool = OpTypeBool
  %int = OpTypeInt 32 1
  %uint = OpTypeInt 32 0
  %float = OpTypeFloat 32
  %i0=OpConstant %int 0  %i1=OpConstant %int 1
  %i2=OpConstant %int 2  %i3=OpConstant %int 3
  %i4=OpConstant %int 4  %i5=OpConstant %int 5
  %i6=OpConstant %int 6  %i7=OpConstant %int 7
  %u8=OpConstant %uint 8  %u24=OpConstant %uint 24
  %f0=OpConstant %float 0.0  %f1=OpConstant %float 1.0
  %fn1=OpConstant %float -1.0  %f2=OpConstant %float 2.0
  %f3=OpConstant %float 3.0  %f025=OpConstant %float 0.25
  %v3 = OpTypeVector %float 3
  %v4 = OpTypeVector %float 4
  %Push = OpTypeStruct %float %float
  %ptrPush = OpTypePointer PushConstant %Push
  %ptrPushF = OpTypePointer PushConstant %float
  %ptrInI = OpTypePointer Input %int
  %ptrOutV4 = OpTypePointer Output %v4
  %ptrOutV3 = OpTypePointer Output %v3
  %arrPos = OpTypeArray %v3 %u8
  %arrIdx = OpTypeArray %int %u24
  %ptrPrivatePos = OpTypePointer Private %arrPos
  %ptrPrivateIdx = OpTypePointer Private %arrIdx
  %ptrPrivateV3 = OpTypePointer Private %v3
  %ptrPrivateI = OpTypePointer Private %int

  %p0=OpConstantComposite %v3 %fn1 %fn1 %fn1
  %p1=OpConstantComposite %v3 %f1 %fn1 %fn1
  %p2=OpConstantComposite %v3 %f1 %f1 %fn1
  %p3=OpConstantComposite %v3 %fn1 %f1 %fn1
  %p4=OpConstantComposite %v3 %fn1 %fn1 %f1
  %p5=OpConstantComposite %v3 %f1 %fn1 %f1
  %p6=OpConstantComposite %v3 %f1 %f1 %f1
  %p7=OpConstantComposite %v3 %fn1 %f1 %f1
  %bias=OpConstantComposite %v3 %f025 %f025 %f025
  %positions=OpConstantComposite %arrPos %p0 %p1 %p2 %p3 %p4 %p5 %p6 %p7
  %indices=OpConstantComposite %arrIdx
    %i0 %i1 %i1 %i2 %i2 %i3 %i3 %i0
    %i4 %i5 %i5 %i6 %i6 %i7 %i7 %i4
    %i0 %i4 %i1 %i5 %i2 %i6 %i3 %i7
  %vertexIndex = OpVariable %ptrInI Input
  %positionOut = OpVariable %ptrOutV4 Output
  %colorOut = OpVariable %ptrOutV3 Output
  %push = OpVariable %ptrPush PushConstant
  %positionsVar = OpVariable %ptrPrivatePos Private %positions
  %indicesVar = OpVariable %ptrPrivateIdx Private %indices

  %main = OpFunction %void None %fn
  %entry = OpLabel
  %vi = OpLoad %int %vertexIndex
  %ip = OpAccessChain %ptrPrivateI %indicesVar %vi
  %ix = OpLoad %int %ip
  %pp = OpAccessChain %ptrPrivateV3 %positionsVar %ix
  %p = OpLoad %v3 %pp
  %anglePtr = OpAccessChain %ptrPushF %push %i0
  %aspectPtr = OpAccessChain %ptrPushF %push %i1
  %angle = OpLoad %float %anglePtr
  %aspect = OpLoad %float %aspectPtr
  %s = OpExtInst %float %glsl Sin %angle
  %c = OpExtInst %float %glsl Cos %angle
  %x = OpCompositeExtract %float %p 0
  %y = OpCompositeExtract %float %p 1
  %z = OpCompositeExtract %float %p 2
  %cx = OpFMul %float %c %x
  %sz = OpFMul %float %s %z
  %rx = OpFAdd %float %cx %sz
  %sx = OpFMul %float %s %x
  %cz = OpFMul %float %c %z
  %rz0 = OpFSub %float %cz %sx
  %rz = OpFAdd %float %rz0 %f3
  %rxAspect = OpFDiv %float %rx %aspect
  %clipX = OpFDiv %float %rxAspect %rz
  %clipY = OpFDiv %float %y %rz
  %depth0 = OpFSub %float %rz %f1
  %depth = OpFDiv %float %depth0 %rz
  %clip = OpCompositeConstruct %v4 %clipX %clipY %depth %f1
  OpStore %positionOut %clip
  %half = OpVectorTimesScalar %v3 %p %f025
  %color = OpFAdd %v3 %half %bias
  OpStore %colorOut %color
  OpReturn
  OpFunctionEnd
}

def cubeFragment : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  OpMemoryModel Logical GLSL450
  OpEntryPoint Fragment %main "main" %colorIn %colorOut
  OpExecutionMode %main OriginUpperLeft
  OpDecorate %colorIn Location 0
  OpDecorate %colorOut Location 0
  %void=OpTypeVoid
  %fn=OpTypeFunction %void
  %float=OpTypeFloat 32
  %v3=OpTypeVector %float 3
  %v4=OpTypeVector %float 4
  %ptrInV3=OpTypePointer Input %v3
  %ptrOutV4=OpTypePointer Output %v4
  %f1=OpConstant %float 1.0
  %colorIn=OpVariable %ptrInV3 Input
  %colorOut=OpVariable %ptrOutV4 Output
  %main=OpFunction %void None %fn
  %entry=OpLabel
  %rgb=OpLoad %v3 %colorIn
  %r=OpCompositeExtract %float %rgb 0
  %g=OpCompositeExtract %float %rgb 1
  %b=OpCompositeExtract %float %rgb 2
  %rgba=OpCompositeConstruct %v4 %r %g %b %f1
  OpStore %colorOut %rgba
  OpReturn
  OpFunctionEnd
}

def cubeHost : AsmSource plan := asm_source {
entry: @entry win64_gui_entry
  push rbx
  push rbp
  push rsi
  push rdi
  push r12
  push r13
  push r14
  push r15
  sub rsp, FRAME_SIZE
  xor eax,eax
  lea rdi,[rsp+locals]
  mov ecx,LOCALS_QWORDS
  rep stosq
  win_call GetProcessHeap() -> rax
  test rax,rax
  jz fail_init
  mov qword ptr [processHeap],rax
  win_call GetModuleHandleW(0) -> r12
  test r12,r12
  jz fail_init
  store32 wc.cbSize,SIZEOF_WNDCLASSEXW
  store32 wc.style,CS_HREDRAW|CS_VREDRAW|CS_OWNDC
  store64 wc.lpfnWndProc,&wndproc
  store64 wc.hInstance,r12
  win_call LoadCursorW(0,IDC_ARROW) -> rax
  store64 wc.hCursor,rax
  store64 wc.lpszClassName,&className
  win_call RegisterClassExW(&wc) -> eax
  test ax,ax
  jz fail_init
  mov registered,1
  win_call CreateWindowExW(0,&className,&title,WS_OVERLAPPEDWINDOW,
      CW_USEDEFAULT,CW_USEDEFAULT,960,720,0,0,r12,&state) -> r13
  test r13,r13
  jz fail_init
  win_call ShowWindow(r13,SW_SHOW) -> _
  win_call QueryPerformanceFrequency(&qpcFrequency) -> eax
  test eax,eax
  jz fail_init
  cmp qword ptr [qpcFrequency],0
  jle fail_init
  win_call QueryPerformanceCounter(&qpcEpoch) -> eax
  test eax,eax
  jz fail_init
  mov rax,qword ptr [qpcEpoch]
  mov qword ptr [qpcPrevious],rax
  jmp vk_instance

wndproc: @entry win64_callback(hwnd,msg,wparam,lparam)
  sub rsp,40
  cmp edx,WM_CLOSE
  je wp_close
  cmp edx,WM_DESTROY
  je wp_destroyed
  cmp edx,WM_KEYDOWN
  jne wp_size
  cmp r8d,VK_ESCAPE
  je wp_close
wp_size:
  cmp edx,WM_SIZE
  jne wp_default
  mov eax,r9d
  and eax,0xffff
  shr r9d,16
  store32 [state.width],eax
  store32 [state.height],r9d
  mov byte ptr [state.resize],1
  xor eax,eax
  add rsp,40
  ret
wp_close:
  mov byte ptr [state.exit],1
  xor eax,eax
  add rsp,40
  ret
wp_destroyed:
  mov byte ptr [state.exit],1
  mov byte ptr [state.hwndOwned],0
  xor eax,eax
  add rsp,40
  ret
wp_default:
  win_call DefWindowProcW(rcx,rdx,r8,r9) -> rax
  add rsp,40
  ret

vk_instance:
  init appInfo {sType=APPLICATION_INFO,pApplicationName=&title,
      applicationVersion=1,pEngineName=&grass,engineVersion=1,
      apiVersion=VK_API_VERSION_1_3}
  init instanceCI {sType=INSTANCE_CREATE_INFO,pApplicationInfo=&appInfo,
      enabledExtensionCount=2,ppEnabledExtensionNames=&instanceExts}
  xor ecx,ecx
  lea rdx,[vkCreateInstanceName]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax
  jz fail_init
  mov [vkCreateInstancePtr],rax
  mov rcx,&instanceCI
  xor edx,edx
  lea r8,[instance]
  call qword ptr [vkCreateInstancePtr]
  test eax,eax
  jnz fail_init
  resolve_instance_functions_or_fail instance, instanceDispatch
  vk_call vkCreateWin32SurfaceKHR(instance,
      {sType=WIN32_SURFACE_CREATE_INFO_KHR,hinstance=r12,hwnd=r13},0,&surface)
  test eax,eax
  jnz fail_init

select_device:
  vk_call vkEnumeratePhysicalDevices(instance,&count,0)
  test eax,eax
  jnz fail_init
  test count,count
  jz fail_init
  checked_alloc count*8 -> devices
  jz fail_init
  vk_call vkEnumeratePhysicalDevices(instance,&count,devices)
  test eax,eax
  jnz fail_init
  enumerate_and_select_literal_loop devices,count -> physical,qfamily
  test physical,physical
  jz fail_init

create_device:
  init queueCI {sType=DEVICE_QUEUE_CREATE_INFO,queueFamilyIndex=qfamily,
      queueCount=1,pQueuePriorities=&one}
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES,
      dynamicRendering=1,synchronization2=1}
  init deviceCI {sType=DEVICE_CREATE_INFO,pNext=&features13,
      queueCreateInfoCount=1,pQueueCreateInfos=&queueCI,
      enabledExtensionCount=1,ppEnabledExtensionNames=&swapchainExt}
  vk_call vkCreateDevice(physical,&deviceCI,0,&device)
  test eax,eax
  jnz fail_init
  resolve_device_functions_or_fail device,deviceDispatch
  vk_call vkGetDeviceQueue(device,qfamily,0,&queue)
  jmp create_fixed

create_fixed:
  vk_call vkCreateCommandPool(device,
    {sType=COMMAND_POOL_CREATE_INFO,flags=RESET_COMMAND_BUFFER_BIT,
     queueFamilyIndex=qfamily},0,&commandPool)
     test eax,eax
     jnz fail_init
  vk_call vkAllocateCommandBuffers(device,
    {sType=COMMAND_BUFFER_ALLOCATE_INFO,commandPool=commandPool,
     level=PRIMARY,commandBufferCount=1},&cmd)
     test eax,eax
     jnz fail_init
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&imageAvail)
  test eax,eax
  jnz fail_init
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&renderDone)
  test eax,eax
  jnz fail_init
  vk_call vkCreateFence(device,{sType=FENCE_CREATE_INFO,flags=SIGNALED_BIT},0,&fence)
  test eax,eax
  jnz fail_init
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeVertexBytes.size,pCode=&cubeVertexBytes},0,&vertModule)
  test eax,eax
  jnz fail_init
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeFragmentBytes.size,pCode=&cubeFragmentBytes},0,&fragModule)
  test eax,eax
  jnz fail_init
  vk_call vkCreatePipelineLayout(device,{sType=PIPELINE_LAYOUT_CREATE_INFO,
    pushConstantRangeCount=1,pPushConstantRanges=&{stageFlags=VERTEX_BIT,
    offset=0,size=8}},0,&pipelineLayout)
    test eax,eax
    jnz fail_init
  jmp recreate

recreate: @invariant fixed_objects_owned_and_no_swapchain_work
  load width,height
  test width,width
  jz minimized_wait
  test height,height
  jz minimized_wait
  vk_call vkDeviceWaitIdle(device)
  cmp eax,VK_SUCCESS
  jne fail_runtime
  destroy_swapchain_views_pipeline_if_owned
  vk_call vkGetPhysicalDeviceSurfaceCapabilitiesKHR(physical,surface,&caps)
  test eax,eax
  jnz surface_result
  test caps.supportedUsageFlags,VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT
  jz fail_runtime
  test caps.supportedCompositeAlpha,VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR
  jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,0)
  test eax,eax
  jnz surface_result
  checked_alloc fmtCount*SIZEOF_FORMAT -> formats
  jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,formats)
  test eax,eax
  jnz surface_result
  select_required_format_or_fail formats,fmtCount -> surfaceFormat
  compute_extent_and_count caps,width,height -> extent,imageCount
  init swapCI {sType=SWAPCHAIN_CREATE_INFO_KHR,surface=surface,
    minImageCount=imageCount,imageFormat=B8G8R8A8_UNORM,
    imageColorSpace=SRGB_NONLINEAR_KHR,imageExtent=extent,imageArrayLayers=1,
    imageUsage=COLOR_ATTACHMENT_BIT,imageSharingMode=EXCLUSIVE,
    preTransform=caps.currentTransform,compositeAlpha=OPAQUE_BIT_KHR,
    presentMode=FIFO_KHR,clipped=1,oldSwapchain=oldSwapchain}
  vk_call vkCreateSwapchainKHR(device,&swapCI,0,&newSwapchain)
  test eax,eax
  jnz surface_result
  destroy_old_swapchain_after_new_created
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,0)
  test eax,eax
  jnz surface_result
  checked_alloc imageCount*(8+8) -> imagesAndViews
  jz fail_runtime
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,images)
  test eax,eax
  jnz surface_result
create_view_loop: @measure imageCount-viewIndex
  cmp viewIndex,imageCount
  je create_pipeline
  vk_call vkCreateImageView(device,{sType=IMAGE_VIEW_CREATE_INFO,
    image=images[viewIndex],viewType=TYPE_2D,format=B8G8R8A8_UNORM,
    components={IDENTITY,IDENTITY,IDENTITY,IDENTITY},subresourceRange=
    {aspectMask=COLOR_BIT,baseMipLevel=0,levelCount=1,
     baseArrayLayer=0,layerCount=1}},0,&views[viewIndex])
  test eax,eax
  jnz fail_runtime
  inc viewIndex
  jmp create_view_loop
create_pipeline:
  init pipelineRendering {sType=PIPELINE_RENDERING_CREATE_INFO,
      colorAttachmentCount=1,pColorAttachmentFormats=&B8G8R8A8_UNORM}
  init graphicsCI {sType=GRAPHICS_PIPELINE_CREATE_INFO,pNext=&pipelineRendering,
      stageCount=2,pStages=&shaderStages,pVertexInputState=&emptyVertexInput,
      pInputAssemblyState=&lineList,pViewportState=&oneDynamicViewport,
      pRasterizationState=&lineRaster,pMultisampleState=&sample1,
      pColorBlendState=&opaqueBlend,pDynamicState=&viewportScissor,
      layout=pipelineLayout,renderPass=0,subpass=0}
  vk_call vkCreateGraphicsPipelines(device,0,1,&graphicsCI,0,&pipeline)
  test eax,eax
  jnz fail_runtime
  mov byte ptr [state.resize],0
  jmp event_loop

minimized_wait:
  cmp byte ptr [state.exit],0
  jne clean_exit
  win_call WaitMessage() -> eax
  test eax,eax
  jz fail_runtime
  jmp pump_messages

event_loop: @frontier_or_measure(message_or_frame)
pump_messages:
  win_call PeekMessageW(&msg,0,0,0,PM_REMOVE) -> eax
  test eax,eax
  jz messages_done
  cmp msg.message,WM_QUIT
  je request_exit
  win_call TranslateMessage(&msg) -> _
  win_call DispatchMessageW(&msg) -> _
  jmp pump_messages
request_exit:
  mov byte ptr [state.exit],1
messages_done:
  cmp byte ptr [state.exit],0
  jne clean_exit
  cmp byte ptr [state.resize],0
  jne recreate
  vk_call vkWaitForFences(device,1,&fence,1,UINT64_MAX)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkAcquireNextImageKHR(device,swapchain,UINT64_MAX,imageAvail,0,&imageIndex)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  cmp eax,VK_SUBOPTIMAL_KHR
  je acquired_suboptimal
  cmp eax,VK_SUCCESS
  jne device_result
  mov byte ptr [state.recreateAfterPresent],0
  jmp acquired
acquired_suboptimal:
  mov byte ptr [state.recreateAfterPresent],1
acquired:
  vk_call vkResetFences(device,1,&fence)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkResetCommandBuffer(cmd,0)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkBeginCommandBuffer(cmd,{sType=COMMAND_BUFFER_BEGIN_INFO,
      flags=ONE_TIME_SUBMIT_BIT})
      cmp eax,VK_SUCCESS
      jne device_result
  vk_call vkCmdPipelineBarrier2(cmd,&barrier selectedOldLayout->ColorAttachmentOptimal
      for images[imageIndex],srcStage=NONE,srcAccess=NONE,
      dstStage=COLOR_ATTACHMENT_OUTPUT,dstAccess=COLOR_ATTACHMENT_WRITE)
  vk_call vkCmdBeginRendering(cmd,{sType=RENDERING_INFO,renderArea={0,extent},
      layerCount=1,colorAttachmentCount=1,pColorAttachments=&{imageView=
      views[imageIndex],imageLayout=COLOR_ATTACHMENT_OPTIMAL,
      loadOp=CLEAR,storeOp=STORE,clearValue={0.02,0.02,0.04,1}}})
  vk_call vkCmdBindPipeline(cmd,GRAPHICS,pipeline)
  vk_call vkCmdSetViewport(cmd,0,1,&{0,0,float(extent.width),float(extent.height),0,1})
  vk_call vkCmdSetScissor(cmd,0,1,&{0,0,extent})
  win_call QueryPerformanceCounter(&qpcNow) -> eax
  test eax,eax
  jz fail_runtime
  mov rax,qword ptr [qpcNow]
  cmp rax,qword ptr [qpcPrevious]
  jl clock_violation @violation_edge(.monotonicClockRegressed)
  mov qword ptr [qpcPrevious],rax
  sub rax,qword ptr [qpcEpoch]
  jo clock_violation @violation_edge(.monotonicClockRangeExceeded)
  cvtsi2sd xmm1,rax
  cvtsi2sd xmm2,qword ptr [qpcFrequency]
  divsd xmm1,xmm2
  mulsd xmm1,qword ptr [angularVelocity]
  movapd xmm0,xmm1
  movapd xmm3,xmm0
  divsd xmm3,qword ptr [tau]
  roundsd xmm3,xmm3,1
  mulsd xmm3,qword ptr [tau]
  subsd xmm0,xmm3
  cvtsd2ss xmm0,xmm0
  cvtsi2ss xmm1,extent.width
  cvtsi2ss xmm2,extent.height
  divss xmm1,xmm2
  store32 push.angle,xmm0
  store32 push.aspect,xmm1
  vk_call vkCmdPushConstants(cmd,pipelineLayout,VERTEX_BIT,0,8,&push)
  vk_call vkCmdDraw(cmd,24,1,0,0)
  vk_call vkCmdEndRendering(cmd)
  vk_call vkCmdPipelineBarrier2(cmd,&barrier ColorAttachmentOptimal->PresentSrcKHR
      for images[imageIndex],srcStage=COLOR_ATTACHMENT_OUTPUT,
      srcAccess=COLOR_ATTACHMENT_WRITE,dstStage=NONE,dstAccess=NONE)
  vk_call vkEndCommandBuffer(cmd)
  cmp eax,VK_SUCCESS
  jne device_result
  init submit {sType=SUBMIT_INFO_2,waitSemaphoreInfoCount=1,
      pWaitSemaphoreInfos=&{sType=SEMAPHORE_SUBMIT_INFO,semaphore=imageAvail,
      stageMask=COLOR_ATTACHMENT_OUTPUT},commandBufferInfoCount=1,
      pCommandBufferInfos=&{sType=COMMAND_BUFFER_SUBMIT_INFO,commandBuffer=cmd},
      signalSemaphoreInfoCount=1,pSignalSemaphoreInfos=&{sType=
      SEMAPHORE_SUBMIT_INFO,semaphore=renderDone,stageMask=ALL_GRAPHICS}}
  vk_call vkQueueSubmit2(queue,1,&submit,fence)
  cmp eax,VK_SUCCESS
  jne device_result
  init present {sType=PRESENT_INFO_KHR,waitSemaphoreCount=1,
      pWaitSemaphores=&renderDone,swapchainCount=1,pSwapchains=&swapchain,
      pImageIndices=&imageIndex}
  vk_call vkQueuePresentKHR(queue,&present)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  cmp eax,VK_SUBOPTIMAL_KHR
  je recreate
  cmp eax,VK_SUCCESS
  jne device_result
  cmp byte ptr [state.recreateAfterPresent],0
  jne recreate
  jmp event_loop

surface_result:
  cmp eax,VK_ERROR_SURFACE_LOST_KHR
  je fail_surface
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  jmp fail_runtime
device_result:
  cmp eax,VK_ERROR_DEVICE_LOST
  je fail_device
  cmp eax,VK_ERROR_SURFACE_LOST_KHR
  je fail_surface
  jmp fail_runtime

clean_exit: mov ebx,0
jmp cleanup
fail_init: mov ebx,1
jmp cleanup
fail_runtime: mov ebx,2
jmp cleanup
fail_surface: mov ebx,3
mark_surface_lost
jmp cleanup
fail_device: mov ebx,4
mark_device_lost
jmp cleanup
clock_violation:
  ud2 @containment_tail(.monotonicClockRegressed)

cleanup: @invariant reverse_dependency_ledger(status=ebx)
  if device_owned and not device_lost: vkDeviceWaitIdle(device)
  for each owned imageView in reverse: vkDestroyImageView(device,view,0)
  if pipeline_owned: vkDestroyPipeline(device,pipeline,0)
  if swapchain_owned: vkDestroySwapchainKHR(device,swapchain,0)
  if pipelineLayout_owned: vkDestroyPipelineLayout(device,pipelineLayout,0)
  if fragModule_owned: vkDestroyShaderModule(device,fragModule,0)
  if vertModule_owned: vkDestroyShaderModule(device,vertModule,0)
  if fence_owned: vkDestroyFence(device,fence,0)
  if renderDone_owned: vkDestroySemaphore(device,renderDone,0)
  if imageAvail_owned: vkDestroySemaphore(device,imageAvail,0)
  if commandPool_owned: vkDestroyCommandPool(device,commandPool,0)
  if device_owned: vkDestroyDevice(device,0)
  if surface_owned: vkDestroySurfaceKHR(instance,surface,0)
  if instance_owned: vkDestroyInstance(instance,0)
  if hwnd_owned: win_call DestroyWindow(hwnd)
  if class_registered: win_call UnregisterClassW(&className,hInstance)
  add rsp,FRAME_SIZE
  pop r15
  pop r14
  pop r13
  pop r12
  pop rdi
  pop rsi
  pop rbp
  pop rbx
  exit_with ebx
}

theorem vertexCorrect :
    AssemblyRefinesImplementation
      vertexShaderScope VertexSpirvRepresentation vertexModel cubeVertex := by
  verify_spirv

theorem fragmentCorrect :
    AssemblyRefinesImplementation
      fragmentShaderScope FragmentSpirvRepresentation fragmentModel cubeFragment := by
  verify_spirv

theorem hostImplementsDriver :
    HostAssemblyImplements
      (ProcessRealization.explicit processPlanRealizes)
      plan cubeHost := by
  verify_asm

end Grass.Spikes.SpinningCube
