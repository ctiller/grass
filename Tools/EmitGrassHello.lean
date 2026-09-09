import Tests.Platform.Win32LoaderEntry

/-! Thin validation exporter. The executable body is the unchanged Grass Hello
World authored source, linked by SourceLinkedImage and serialized by writeImage.
This host IO command supplies no proof of Windows behavior. -/

def main (args : List String) : IO UInt32 := do
  let [imagePath, expectedPath] := args
    | throw (IO.userError "usage: EmitGrassHello <exe-path> <expected-stdout-path>")
  let some plan := Grass.Tests.Win32LoaderEntry.helloPlan?
    | throw (IO.userError "Grass source linking refused Hello World")
  IO.FS.writeBinFile imagePath (Grass.Artifact.PE.writeImage plan).toHostBytes
  IO.FS.writeBinFile expectedPath Grass.Tests.Assembly.SourceLinkedImage.payload.toHostBytes
  IO.println s!"Emitted {plan.layout.placed.length} sections; entry RVA {plan.layout.entryPointRva}."
  pure 0
