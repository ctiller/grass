/-!
# Specification-authoring facade: graphics

A thin re-export module, empty this round. No `Grass/Graphics/*.lean`
interactive-scene vocabulary exists yet to re-export: `Grass/Target/Device.lean`
is the machine-tier shader/API seam (`docs/TARGET_SEAMS.md`) and must not be
named above the machine tier, so it is not a candidate source for this facade.
`Spikes/5_Spinning_Cube/Spec.lean` needs a portable authoring surface
(`WireGeometry`, `VertexColoring`, `AngularVelocity`, `InteractiveScene`,
`Scene.spinningWireGeometry`, `ElapsedRotationAccuracy`, `ProgressFragment`,
`SceneSpec`, `TraceSpec`, `Graphics.sceneSpec`, `Graphics.interactiveTraceSpec`,
`Graphics.interactiveSceneSuite`, `Graphics.interactiveSceneSuiteCaptureCorrect`)
that a future `Grass/Graphics/*.lean` module must define before this file has
anything to re-export.
-/
