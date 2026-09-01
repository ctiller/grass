import Grass.Assembly.X86
import Spikes.«1_Hello_World».Plan

namespace Grass.Spikes.HelloWorld

def helloSource : MachineSource plan := asm_source {
entry:
  push r12
  push r13
  push r14
  sub rsp, 48
  mov ecx, STD_OUTPUT_HANDLE
  call qword ptr [rip + __imp_GetStdHandle]
  test rax, rax
  jz exit_unavailable
  cmp rax, INVALID_HANDLE_VALUE
  je exit_unavailable
  mov r12, rax
  lea r13, [rip + message]
  mov r14d, sizeof(message)

write_head: @invariant write_all_loop(message, handle=r12, ptr=r13, rem=r14d)
  test r14d, r14d
  je exit_success
  mov qword ptr [rsp+32], 0
  mov dword ptr [rsp+40], 0
  mov rcx, r12
  mov rdx, r13
  mov r8d, r14d
  lea r9, [rsp+40]
  call qword ptr [rip + __imp_WriteFile]
  test eax, eax
  jz exit_write_failed
  mov eax, dword ptr [rsp+40]
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

end Grass.Spikes.HelloWorld
