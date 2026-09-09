import Tests.Platform.Win32LoaderEntry

/-! Thin validation exporter. The executable body is the unchanged Grass Hello
World authored source, linked by SourceLinkedImage and serialized by writeImage.
This host IO command supplies no proof of Windows behavior. -/

def main (args : List String) : IO UInt32 := do
  let [imagePath, expectedPath, sourceSnapshotPath] := args
    | throw (IO.userError "usage: EmitGrassHello <exe-path> <expected-stdout-path> <source-snapshot-path>")
  let sourceBytes ← IO.FS.readBinFile "Spikes/1_Hello_World/Program.lean"
  let some source := String.fromUTF8? sourceBytes
    | throw (IO.userError "authored Grass source is not UTF-8")
  let some plan := Grass.Tests.Win32LoaderEntry.helloPlanFrom? source.toList
    | throw (IO.userError "Grass source linking refused Hello World")
  IO.FS.writeBinFile imagePath (Grass.Artifact.PE.writeImage plan).toHostBytes
  IO.FS.writeBinFile expectedPath Grass.Tests.Assembly.SourceLinkedImage.payload.toHostBytes
  IO.FS.writeBinFile sourceSnapshotPath sourceBytes
  IO.println s!"Emitted {plan.layout.placed.length} sections; entry RVA {plan.layout.entryPointRva}."
  pure 0
