import Grass.Assembly.X86ClosedEncoding
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86ClosedEncoding
open Grass.Assembly SourceInput X86Source X86ClosedEncoding
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

example : encode ⟨.mov, [.register ⟨.rax,.w64⟩, .immediate (2^64)]⟩ = none := by decide
example : encode ⟨.mov, [.register ⟨.rax,.w32⟩, .immediate (2^32)]⟩ = none := by decide
example : encode ⟨.push, [.register ⟨.rax,.w32⟩]⟩ = none := by decide
example : encode ⟨.add, [.register ⟨.rax,.w64⟩, .register ⟨.rcx,.w32⟩]⟩ = none := by decide

end Grass.Tests.Assembly.X86ClosedEncoding
