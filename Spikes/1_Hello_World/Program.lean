import Grass.Emit
import Grass.Artifact.PE32Plus
import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Process.Sequential
import Spikes.«1_Hello_World».Spec

namespace Grass.Spikes.HelloWorld

def stdoutProtocol : AbstractSpecificationProcessNetwork resources :=
  Console.linearStdoutProtocol resources message HelloOutcome

def stdoutPresentation : ProcessPresentation spec where
  network := stdoutProtocol
  denotationExact := Console.linearStdoutProtocolDenotesWriteLineContract
  requirementsExact := Console.linearStdoutProtocolRequirementsExact

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard
    (Grass.Std.Realizers.lookupExact stdoutPresentation)

def policy : TargetOutcomeProjection HelloOutcome UInt32 :=
  .successOrFailure
    (success := HelloOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ConsoleText
    (newline := .crlf)
    (encoding := .utf8)
    (outcome := policy)

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly projection

def helloSource : MachineSource plan :=
  withStack (transferred : UInt32 := 0)
  withCallFrame WriteFile asm_source {
entry:
  push r12
  push r13
  push r14
  mov ecx, STD_OUTPUT_HANDLE
  call qword ptr [rip + __imp_GetStdHandle]
  test rax, rax
  jz exit_unavailable
  cmp rax, INVALID_HANDLE_VALUE
  je exit_unavailable
  mov r12, rax
  lea r13, [rip + message]
  mov r14d, sizeof(message)

write_head: @placement [handle := r12, cursor := r13, remaining := r14d]
            @invariant write_all_loop(message)
  test r14d, r14d
  je exit_success
  arg WriteFile.overlapped, 0
  mov transferred, 0
  mov rcx, r12
  mov rdx, r13
  mov r8d, r14d
  lea r9, transferred.addr
  call qword ptr [rip + __imp_WriteFile]
  test eax, eax
  jz exit_write_failed
  mov eax, transferred
  test eax, eax
  jz exit_no_progress
  cmp eax, r14d
  ja provider_violation @violation_edge(.excessWriteCount)
  add r13, rax
  sub r14d, eax
  jmp write_head

exit_success: @terminal(.success)
  xor ecx, ecx
  jmp exit

exit_unavailable: @terminal(.stdoutUnavailable)
  mov ecx, 1
  jmp exit

exit_write_failed: @terminal(.writeFailed)
  mov ecx, 1
  jmp exit

exit_no_progress: @terminal(.noProgress)
  mov ecx, 1
  jmp exit

exit:
  call qword ptr [rip + __imp_ExitProcess]
  ud2 @containment_tail(.terminalUnexpectedReturn)

provider_violation:
  ud2 @containment_tail(.excessWriteCount)
}

theorem sourceImplementsDriver :
    AssemblyImplements processRealization plan helloSource := by
  verify_asm

def helloVerified : VerifiedProgram spec := by
  verify_assembly plan with helloSource

def bytes : ByteArray := emitProgram helloVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  helloVerified.sound

def artifact : PE32Plus := helloVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact helloVerified.rawProgram :=
  helloVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.HelloWorld
