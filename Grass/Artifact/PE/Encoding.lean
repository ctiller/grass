import Grass.Artifact.Encoding
import Grass.Artifact.PE.ImageRoundTrip

namespace Grass.Artifact.PE

/-- `encoding` packages the existing PE writer and reader with
`readImage_writeImage`; it adds no alternate serialization or loader. -/
def encoding : Grass.ArtifactEncoding where
  Artifact := ImagePlan
  Parsed := ParsedImage
  write := writeImage
  read := readImage
  decoded := ImagePlan.expectedImage
  read_write := readImage_writeImage

end Grass.Artifact.PE
