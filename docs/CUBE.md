# Milestone 5: Win32 Vulkan spinning cube

The complete annotated proof proposal is [SPIKE_5.md](SPIKE_5.md). This file is
the concise acceptance checklist.

## Specification

- The precious `cubeApplication : ProcessSpec` describes a responsive logical
  application that presents an indefinitely rotating, perspective-projected
  colored wireframe cube until the user requests termination by closing the
  window or pressing Escape.
- Its state is only phase, desired extent/angle, last monotonic opportunity, and
  an ordered correlated-command ledger with no fixed population bound. Process
  execution owns observation history separately. Its
  pure `render` produces a
  `DesiredCubeView`; commands request frame commit or terminal completion.
- It does not mention a process topology, Win32, Vulkan, SPIR-V, swapchains,
  frame counts, refresh rates, floating-point bit patterns, or a numeric process
  status.
- Every accepted committed frame records the monotonic clock sample used to
  construct it and represents the same cube geometry at an angle within the
  proved representation-independent angular-accuracy contract for
  specified angular velocity and portable monotonic elapsed time. Sample times
  are nondecreasing; equal samples imply zero elapsed time and the same
  represented angle;
  resize changes only the viewport/aspect projection. Refresh rate, occlusion,
  coalescing, device scheduling, and the number of frames between inputs are
  environmental entropy and may change which frames appear, not rotation speed.
- Safety holds for every finite prefix. Between input, acquire, GPU-completion,
  and present frontiers, host work is finite. Termination is conditional on a
  close/Escape request and responsive Win32/Vulkan/scheduler strategies.
- Initialization failure, device loss, surface loss, out-of-date swapchains,
  minimization, and shutdown are explicit outcomes. A recoverable resize or
  out-of-date result recreates the swapchain; device/surface loss terminates.

## Realization

- `processPlan : ProcessPlan cubeProtocols spec.driverBoundary` is a reviewed replaceable weave with one root
  application, window/input source, frame-opportunity source, graphics
  coordinator, terminal child, and identity-indexed
  acquire/submission/presentation/API child processes. The topology is not
  precious.
- `processPlanRealizes` proves every child protocol, channel, population law,
  state-ownership boundary, cancellation/device-loss disposition, commit
  filter, and progress obligation, and proves the plan refines the root process.
- Mutable logical state is process-local. The only read-shared region is the
  immutable selected profile. Window and Vulkan resources have a unique local
  ledger; per-frame children receive affine resource loans through channels.
- One coherent plan selects Win32 x64, common Intel/AMD x86-64, Vulkan 1.3,
  `VK_KHR_surface`, `VK_KHR_win32_surface`, `VK_KHR_swapchain`, SPIR-V 1.5 under
  the Vulkan environment, PE32+, and ASLR. Ambient provider search cannot mix
  Vulkan, Metal, WebGPU, or a second window system.
- Device selection requires both Vulkan 1.3 `dynamicRendering` and
  `synchronization2`; device creation explicitly enables both before any
  `vkCmdPipelineBarrier2` or `vkQueueSubmit2` use.
- The authored host artifact is an `asm_source` whose stable per-block
  declarations verify to a typed x86-64 CFG. The authored vertex and fragment
  machine sources are typed SPIR-V modules. Source values alone assert no
  application refinement, and none is generated from a hidden high-level shader
  or graphics framework.
- The host creates and owns the window, instance, surface, physical-device
  selection witness, logical device/queue, swapchain images and views, dynamic
  rendering pipeline, command pool/buffer, semaphores, and fence. The ledger
  enforces reverse-order destruction and GPU-idle prerequisites.
- Close/Escape records an exit request but does not destroy the `HWND` from the
  callback. Cleanup first retires device work and destroys the Vulkan surface,
  then destroys the dependent window and unregisters its class.
- Acquire, submit, and present transfer image and synchronization obligations
  explicitly. No image is rendered before acquisition, reused before its fence,
  destroyed while in flight, or presented outside the required layout.
- Win32 callback reentrancy, resize/minimize behavior, close input, Vulkan
  return entropy, monotonic clock results, floating-point behavior, and GPU
  execution are modeled. `QueryPerformanceCounter` is one replaceable Win32
  realization of the portable monotonic frame-opportunity protocol.

## Acceptance chain

1. The portable reactive specification is minimal, observation-filtered, and
   universal over input/timing/environment choices.
2. `cubeApplicationCorrect` proves the root invariant, pure view, observation,
   abstract-demand/result, and reactive-progress laws without platform vocabulary.
3. The exact nonprecious process plan defines all child populations, local and
   shared state, typed channels, spawning, cancellation, and supervision;
   `processPlanRealizes` proves the replaceable root process model satisfies the
   selected instance of the precious resource-parameterized specification.
4. Provider selection is globally coherent and all Win32, Vulkan, SPIR-V,
   x86-64, ABI, loader, and device-feature requirements are explicit.
5. The complete authored host source has locally checked entry/exit contracts for
   every call, callback, loop, failure, recreation, and cleanup edge.
6. Both complete authored SPIR-V instruction modules validate in the declared
   Vulkan environment and refine the portable cube-frame contract.
7. Cross-ISA composition proves that the exact shader words embedded in the PE
   are the words passed to `vkCreateShaderModule`, and that the selected Vulkan
   provider executes those modules under the proved pipeline contract.
8. Every allocation, handle, image acquisition, command-buffer state,
   semaphore/fence transition, queue ownership, callback loan, and destruction
   obligation typechecks on success, failure, resize, and termination paths.
9. `source : MachineSource plan` contains the exact host and two device sources;
   `verify_assembly plan using explicit_process processPlanRealizes with source` connects
   that heterogeneous source to the exact process plan. Process boundaries
   introduce no hidden machine code or unexplained macro.
10. Erasure, x86 encoding, SPIR-V writing/reading, PE writing/reading, imports,
   relocations, unwind metadata, loading, and the exact emitted bytes compose
   into `cubeVerified.sound`.
11. Differential validators and physical probes challenge the x86, Win32,
   Vulkan, SPIR-V, synchronization, presentation, and artifact models without
   replacing proof.
12. The dependency report demonstrates that root behavior, process topology,
   shader tuning, host instruction tuning, window policy, and portable semantic
   changes invalidate only their justified cones.

This milestone is a deliberately small Vulkan desktop program, not an engine.
It has one window, one graphics queue, one frame in flight, no recovery from
device/surface loss, no accessibility UI, and no promise of deterministic
physical pixels across conforming GPUs. Those are explicit product limits, not
facts hidden to make the proof pass.

Changing worker counts, frame-pipeline decomposition, event routing, or the
location of a resource ledger is an implementation-plan change when external
behavior is preserved. Changing which inputs terminate, what a committed frame
means, whether rotation is frame- or time-relative, or which failures count as
success changes the precious specification function. Review must reject a proof
convenience that silently moves a product choice across that boundary.
