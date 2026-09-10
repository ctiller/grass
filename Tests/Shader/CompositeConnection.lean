import Grass.Shader.CompositeConnection
import Grass.Trust.Audit

/-!
Audit the runtime/module dependency closures of both primitive implementations
and the common theorem. The full repository gate additionally discovers
VerifiedProgram roots; no shader certificate is constructed here.
-/
#audit_runtime_dependencies Grass.ISA.SPIRV.Composite.decode
#audit_runtime_dependencies Grass.ISA.SPIRV.Composite.transfer
#audit_runtime_dependencies Grass.Shader.WGSL.Composite.check?
#audit_runtime_dependencies Grass.Shader.CompositeConnection.checked_construct4_agrees

#print axioms Grass.Shader.CompositeConnection.checked_construct4_agrees
#print axioms Grass.ISA.SPIRV.Composite.decode_encode_append
#print axioms Grass.ISA.SPIRV.Composite.transfer_frame
#print axioms Grass.ISA.SPIRV.Composite.checked_extract_total
#print axioms Grass.ISA.SPIRV.Composite.checked_construct4_total
#print axioms Grass.Shader.WGSL.Composite.check_sound
