import Spikes.«5_Spinning_Cube».Layout

namespace Grass.Spikes.SpinningCube

def win64ArgLocation : Nat → CallLocation
  | 0 => .register .rcx
  | 1 => .register .rdx
  | 2 => .register .r8
  | 3 => .register .r9
  | n + 4 => .stack (32 + 8 * n)

def expandArguments (arguments : Vec Operand) : Vec RawInstruction :=
  ParallelMove.expand
    (arguments.mapIdx fun index argument =>
      (argument, win64ArgLocation index))

def expandCall (target : CallTarget) (arguments : Vec Operand)
    (result : Option Register) : Vec RawInstruction :=
  expandArguments arguments ++
  #[match target with
    | .iat symbol => .callMem (.ripRelative (iatSymbol symbol))
    | .dispatch base slot => .callMem (.baseDisplacement base slot)] ++
  match result with
  | none => #[]
  | some .rax => #[]
  | some destination => #[.mov destination .rax]

def expandZeroInitializedStructure
    (layout : ProvedStructLayout) (address : Address)
    (fields : Vec FieldInitializer) : Vec RawInstruction :=
  #[.xor .eax .eax,
    .lea .rdi address,
    .mov .ecx (.immediate (layout.size / 8)),
    .repStosq] ++
  fields.map fun field =>
    .movWidth field.layout.width (address + field.layout.offset) field.value

def expandLoad (destinations : Vec Register) (sources : Vec Address) :
    Vec RawInstruction :=
  Vec.zipWith (fun destination source => .mov destination (.memory source))
    destinations sources

def expandUnsignedClamp
    (value low high : Operand) (destination : Address) : Vec RawInstruction := #[
  .mov .eax value,
  .cmp .eax low,
  .cmovb .eax low,
  .cmp .eax high,
  .cmova .eax high,
  .mov32 destination .eax
]

def expandConditionalDestroy
    (tag : Address) (arguments : Vec Operand) (target : CallTarget) :
    Vec RawInstruction :=
  RawInstructionBuilder.withFreshLabel `destroy_done fun done =>
    #[.cmp8 tag 0, .je (.label done)] ++
    expandCall target arguments none ++
    #[.mov8 tag 0, .label done]

def exactCStringScanBody : TransparentAsmFragment plan := asm_fragment {
  xor ebx,ebx
cstr_record_head: @measure recordCount-rbx
  cmp ebx,recordCount
  je cstr_not_found
  lea rsi,[records+rbx*recordStride+recordNameOffset]
  mov rdi,needle
  xor ecx,ecx
cstr_char_head: @measure VK_MAX_EXTENSION_NAME_SIZE-rcx
  cmp ecx,VK_MAX_EXTENSION_NAME_SIZE
  je cstr_next_record
  mov al,[rsi+rcx]
  cmp al,[rdi+rcx]
  jne cstr_next_record
  test al,al
  jz cstr_found
  inc ecx
  jmp cstr_char_head
cstr_next_record:
  inc ebx
  jmp cstr_record_head
cstr_not_found:
  mov ebx,-1
cstr_found:
}

def queuePropertyInitializationBody : TransparentAsmFragment plan := asm_fragment {
  xor ebx,ebx
queue_record_head: @measure queueCount-rbx
  cmp ebx,[queueCount]
  je queue_record_done
  lea rdi,[queueProps+rbx*QSIZE]
  xor eax,eax
  mov ecx,QSIZE/8
  rep stosq
  mov dword ptr [queueProps+rbx*QSIZE+sType],PHYSICAL_DEVICE_QUEUE_FAMILY_PROPERTIES_2
  inc ebx
  jmp queue_record_head
queue_record_done:
}

def checkedHeapAllocationBody : TransparentAsmFragment plan := asm_fragment {
  mov pointer,0
  mov byte ptr [tag],0
  mov rax,count
  mov rcx,stride
  mul rcx
  test rdx,rdx
  jnz allocation_failed
  test count,count
  jz allocation_failed
  test rax,rax
  jz allocation_failed
  mov r8,rax
  mov rcx,[processHeap]
  xor edx,edx
  call qword ptr [rip+__imp_HeapAlloc]
  test rax,rax
  jz allocation_failed
  mov pointer,rax
  mov byte ptr [tag],1
  mov eax,1
  jmp allocation_done
allocation_failed:
  xor eax,eax
allocation_done:
  test eax,eax
}

def checkedHeapReleaseBody : TransparentAsmFragment plan := asm_fragment {
free_head:
  cmp byte ptr [tag],0
  je free_done
  mov rcx,[processHeap]
  xor edx,edx
  mov r8,pointer
  call qword ptr [rip+__imp_HeapFree]
  test eax,eax
  jz provider_violation @violation_edge(.ownedHeapFreeRejected)
  mov pointer,0
  mov byte ptr [tag],0
free_done:
}

def instanceDispatchResolutionBody : TransparentAsmFragment plan := asm_fragment {
resolve_i_init:
  xor r14d,r14d
resolve_i_head: @measure instanceSlotCount-r14
  cmp r14d,instanceSlotCount
  je resolve_i_seal
  mov rcx,[instance]
  mov rdx,[instanceNames+r14*8]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax
  jz fail_init
  mov [instanceDispatch+r14*8],rax
  inc r14d
  jmp resolve_i_head
resolve_i_seal:
  @ghost seal_read_only(instanceDispatch)
}

def deviceDispatchResolutionBody : TransparentAsmFragment plan := asm_fragment {
resolve_d_init:
  xor r14d,r14d
resolve_d_head: @measure deviceSlotCount-r14
  cmp r14d,deviceSlotCount
  je resolve_d_seal
  mov rcx,[device]
  mov rdx,[deviceNames+r14*8]
  call qword ptr [rip+__imp_vkGetDeviceProcAddr]
  test rax,rax
  jz fail_init
  mov [deviceDispatchCandidate+r14*8],rax
  inc r14d
  jmp resolve_d_head
resolve_d_seal:
  lea rsi,[deviceDispatchCandidate]
  lea rdi,[deviceDispatch]
  mov ecx,deviceSlotCount
  rep movsq
  @ghost seal_read_only(deviceDispatch)
  mov byte ptr [ownership.deviceDispatchReady],1
}

def deviceSelectionBody : TransparentAsmFragment plan := asm_fragment {
dev_init:
  xor r14d,r14d
dev_head: @measure deviceCount-r14
  cmp r14d,[deviceCount]
  je fail_init
  mov r15,[devices+r14*8]
  init properties2 {sType=PHYSICAL_DEVICE_PROPERTIES_2}
  vk_call vkGetPhysicalDeviceProperties2(r15,&properties2)
  cmp [properties2.properties.apiVersion],VK_API_VERSION_1_3
  jb dev_next
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES}
  init features2 {sType=PHYSICAL_DEVICE_FEATURES_2,pNext=&features13}
  vk_call vkGetPhysicalDeviceFeatures2(r15,&features2)
  cmp [features13.dynamicRendering],0
  je dev_next
  cmp [features13.synchronization2],0
  je dev_next
ext_count:
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,0)
  cmp eax,VK_SUCCESS
  jne dev_next
  checked_alloc extCount*SIZEOF_EXTENSION_PROPERTIES -> extProps
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,extProps)
  cmp eax,VK_INCOMPLETE
  je ext_retry
  cmp eax,VK_SUCCESS
  jne dev_next_free_ext
  exact_find_c_string extProps,extCount,&swapchainExtName -> ebx
  js dev_next_free_ext
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,0)
  checked_alloc queueCount*SIZEOF_QUEUE_PROPERTIES_2 -> queueProps
  initialize_queue_property_records queueProps,queueCount
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,queueProps)
  xor ebx,ebx
queue_head: @measure queueCount-rbx
  cmp ebx,[queueCount]
  je dev_next_free_all
  test [queueProps+rbx*QSIZE+queueFlags],VK_QUEUE_GRAPHICS_BIT
  jz queue_next
  vk_call vkGetPhysicalDeviceSurfaceSupportKHR(r15,ebx,[surface],&supported)
  cmp eax,VK_SUCCESS
  jne dev_next_free_all
  cmp [supported],0
  jne dev_selected
queue_next:
  inc ebx
  jmp queue_head
dev_selected:
  mov [physical],r15
  mov [qfamily],ebx
  free queueProps
  free extProps
  free devices
  jmp create_device
dev_next_free_all:
  free queueProps
dev_next_free_ext:
  free extProps
dev_next:
  inc r14d
  jmp dev_head
ext_retry:
  free extProps
  jmp ext_count
}

def surfaceSelectionBody : TransparentAsmFragment plan := asm_fragment {
fmt_init:
  xor ebx,ebx
fmt_head: @measure fmtCount-rbx
  cmp ebx,[fmtCount]
  je fail_runtime_free_formats
  cmp [formats+rbx*FSIZE+format],VK_FORMAT_B8G8R8A8_UNORM
  jne fmt_next
  cmp [formats+rbx*FSIZE+colorSpace],VK_COLOR_SPACE_SRGB_NONLINEAR_KHR
  je fmt_found
fmt_next:
  inc ebx
  jmp fmt_head
fmt_found:
  mov rax,[formats+rbx*FSIZE]
  mov [surfaceFormat],rax
  free formats
}

def expandExtentAndCount
    (caps width height extent imageCount : AddressOperand) :
    TransparentAsmFragment plan := asm_fragment {
  cmp [caps.currentExtent.width],UINT32_MAX
  jne extent_fixed
  clamp_u32 width,[caps.min.width],[caps.max.width] -> [extent.width]
  clamp_u32 height,[caps.min.height],[caps.max.height] -> [extent.height]
  jmp extent_done
extent_fixed:
  mov rax,[caps.currentExtent]
  mov [extent],rax
extent_done:
  cmp [extent.width],0
  je minimized_wait
  cmp [extent.height],0
  je minimized_wait
  mov eax,[caps.minImageCount]
  cmp eax,UINT32_MAX
  je fail_runtime
  inc eax
  mov ecx,[caps.maxImageCount]
  test ecx,ecx
  jz count_done
  cmp eax,ecx
  cmova eax,ecx
count_done:
  mov [imageCount],eax
}

def swapchainRetirementBody : TransparentAsmFragment plan := asm_fragment {
destroy_old_init:
  mov ecx,[initializedViewCount]
destroy_old_head: @measure ecx
  test ecx,ecx
  jz destroy_old_pipeline
  dec ecx
  vk_call vkDestroyImageView(device,views[rcx],0)
  mov qword ptr [views+rcx*8],0
  jmp destroy_old_head
destroy_old_pipeline:
  cmp byte ptr [ownership.pipelineOwned],0
  je destroy_old_swap
  vk_call vkDestroyPipeline(device,pipeline,0)
  mov byte ptr [ownership.pipelineOwned],0
destroy_old_swap:
  cmp byte ptr [ownership.swapchainOwned],0
  je destroy_old_arrays
  vk_call vkDestroySwapchainKHR(device,swapchain,0)
  mov byte ptr [ownership.swapchainOwned],0
destroy_old_arrays:
  mov dword ptr [initializedViewCount],0
  mov dword ptr [viewIndex],0
  free imageInitialized
  free views
  free images
}

def installNewSwapchainBody : TransparentAsmFragment plan := asm_fragment {
  mov rax,[newSwapchain]
  mov [swapchain],rax
  mov byte ptr [ownership.newSwapchainOwned],0
  mov byte ptr [ownership.swapchainOwned],1
}

def reverseCleanupBody : TransparentAsmFragment plan := asm_fragment {
cleanup_device_wait:
  cmp byte ptr [ownership.deviceDispatchReady],0
  je cleanup_views
  cmp byte ptr [ownership.deviceLost],0
  jne cleanup_views
  vk_call vkDeviceWaitIdle(device)
cleanup_views:
  mov ecx,[initializedViewCount]
cleanup_view_head: @measure ecx
  test ecx,ecx
  jz cleanup_pipeline
  dec ecx
  vk_call vkDestroyImageView(device,views[rcx],0)
  jmp cleanup_view_head
cleanup_pipeline:
  destroy_if_owned ownership.pipelineOwned,vkDestroyPipeline,device,pipeline
  destroy_if_owned ownership.swapchainOwned,vkDestroySwapchainKHR,device,swapchain
  destroy_if_owned ownership.pipelineLayoutOwned,vkDestroyPipelineLayout,device,pipelineLayout
  destroy_if_owned ownership.fragModuleOwned,vkDestroyShaderModule,device,fragModule
  destroy_if_owned ownership.vertModuleOwned,vkDestroyShaderModule,device,vertModule
  destroy_if_owned ownership.fenceOwned,vkDestroyFence,device,fence
  destroy_if_owned ownership.renderDoneOwned,vkDestroySemaphore,device,renderDone
  destroy_if_owned ownership.imageAvailOwned,vkDestroySemaphore,device,imageAvail
  destroy_if_owned ownership.commandPoolOwned,vkDestroyCommandPool,device,commandPool
  cmp byte ptr [ownership.deviceOwned],0
  je cleanup_surface
  cmp byte ptr [ownership.deviceDestroyReady],0
  je provider_violation @violation_edge(.ownedDeviceWithoutDestroyCapability)
  mov rcx,[device]
  xor edx,edx
  call qword ptr [vkDestroyDevicePtr]
  mov byte ptr [ownership.deviceOwned],0
cleanup_surface:
  destroy_if_owned ownership.surfaceOwned,vkDestroySurfaceKHR,instance,surface
  destroy_if_owned ownership.instanceOwned,vkDestroyInstance,instance
  free imageInitialized
  free views
  free images
  free queueProps
  free extProps
  free devices
  cmp byte ptr [state.hwndOwned],0
  je cleanup_class
  win_call DestroyWindow(r13)
cleanup_class:
  cmp byte ptr [ownership.classRegistered],0
  je cleanup_return
  win_call UnregisterClassW(&className,r12)
cleanup_return:
}

def cubeMacroDefinitions : AsmMacroRegistry plan := #[
  .functional `win_call expandCall,
  .functional `vk_call expandCall,
  .functional `init expandZeroInitializedStructure,
  .literal `checked_alloc checkedHeapAllocationBody,
  .literal `free checkedHeapReleaseBody,
  .literal `resolve_instance_functions_or_fail instanceDispatchResolutionBody,
  .literal `resolve_device_functions_or_fail deviceDispatchResolutionBody,
  .literal `enumerate_and_select_literal_loop deviceSelectionBody,
  .literal `select_required_format_or_fail surfaceSelectionBody,
  .functional `compute_extent_and_count expandExtentAndCount,
  .literal `destroy_swapchain_views_pipeline_if_owned swapchainRetirementBody,
  .literal `destroy_old_swapchain_after_new_created installNewSwapchainBody,
  .literal `reverse_cleanup reverseCleanupBody,
  .singleInstruction `store32 .mov32,
  .singleInstruction `store64 .mov64,
  .functional `load expandLoad,
  .functional `clamp_u32 expandUnsignedClamp,
  .literal `exact_find_c_string exactCStringScanBody,
  .literal `initialize_queue_property_records queuePropertyInitializationBody,
  .functional `destroy_if_owned expandConditionalDestroy
]

end Grass.Spikes.SpinningCube
