import Grass.Platform.Win10.Vulkan13
import Spikes.«5_Spinning_Cube».Spec

namespace Grass.Spikes.SpinningCube

def projection : TargetProjection spec .win10X64Vulkan13Spirv15 :=
  TargetProjection.win10VulkanInteractive
    (clock := .queryPerformanceCounter)
    (userExitStatus := 0)
    (failureStatus := 1)

end Grass.Spikes.SpinningCube
