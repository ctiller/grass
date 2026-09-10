/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Grass.Std.Zlib.Gzip.Member
import Grass.Std.Zlib.Deflate.FixedSizeBound

/-!
# Output-size bound for a written gzip member

Wraps `Grass.Std.Zlib.Deflate.compressFixed_size_bound` with the fixed ten-byte
header and eight-byte trailer `Member.write` always adds.
-/

namespace Grass.Std.Zlib.Gzip

open Grass.Std.Logical

/-- **Output-size bound for a gzip member.** A written member is never more
than five times its payload plus a small constant, combining the fixed
18-byte container overhead with `Deflate.compressFixed_size_bound`. -/
theorem write_size_bound (m : Member) : (write m).length ≤ 5 * m.payload.length + 21 := by
  have hc := Deflate.compressFixed_size_bound (Vec.toHostBytes m.payload)
  simp only [write, Vec.length_append, length_header, Trailer.length_write,
    Vec.length_ofHostBytes, Vec.size_toHostBytes] at hc ⊢
  omega

end Grass.Std.Zlib.Gzip
