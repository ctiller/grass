import Grass.Spec.Resource

namespace Grass.Spikes.SpinningCube

def resources : GraphicsResourceModel :=
  GraphicsResourceModel.longLivedApplication
    |>.withNoUnboundedGrassOwnedGrowth
    |>.withTerminalDisposition .closeAllOwnedGraphicsObjects

end Grass.Spikes.SpinningCube
