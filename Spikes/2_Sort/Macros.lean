import Grass.Assembly.X86
import Spikes.«2_Sort».Data

namespace Grass.Spikes.Sort

structure PhysicalLineDesc where
  offset : UInt64
  length : UInt64

structure SortFrameLayout where
  shadow : Bytes 32
  arg5 : UInt64
  ioCount : UInt32
  ioRequest : UInt32
  stdin : UInt64
  stdout : UInt64
  lines : UInt64
  scratch : UInt64
  lineCount : UInt64
  width : UInt64
  left : UInt64
  mid : UInt64
  right : UInt64
  i : UInt64
  j : UInt64
  k : UInt64
  appendPtr : UInt64
  appendRemaining : UInt64
  outputIndex : UInt64
  finalDescriptors : UInt64
  outUsed : UInt64
  savedRsi : UInt64
  savedRdi : UInt64
  flushPtr : UInt64
  flushRemaining : UInt64

def SortFrame : FrameLayout Win64 := FrameLayout.derive SortFrameLayout

def compareRecordsMacro : TransparentAsmMacro plan := asm_macro compare_records(left, right) {
    mov  rax, qword ptr [left+0]
    add  rax, r13
    mov  r10, qword ptr [left+8]
    mov  rcx, qword ptr [right+0]
    add  rcx, r13
    mov  r11, qword ptr [right+8]
    xor  r9d, r9d
.compare_loop:
    cmp  r9, r10
    jae  .left_end
    cmp  r9, r11
    jae  .less
    movzx edx, byte ptr [rax+r9]
    movzx r8d, byte ptr [rcx+r9]
    cmp  edx, r8d
    jb   .less
    ja   .greater
    add  r9, 1
    jmp  .compare_loop
.left_end:
    cmp  r9, r11
    jb   .less
    xor  eax, eax
    jmp  .done
.less:
    mov  eax, -1
    jmp  .done
.greater:
    mov  eax, 1
.done:
}

def flushOutputMacro : TransparentAsmMacro plan := asm_macro flush_output() {
    lea  rax, [rip + output_buffer]
    mov  qword ptr [rsp+SortFrame.flushPtr], rax
    mov  rax, qword ptr [rsp+SortFrame.outUsed]
    mov  qword ptr [rsp+SortFrame.flushRemaining], rax
.flush_head:
    cmp  qword ptr [rsp+SortFrame.flushRemaining], 0
    je   .flush_complete
    mov  eax, dword ptr [rsp+SortFrame.flushRemaining]
    mov  dword ptr [rsp+SortFrame.ioRequest], eax
    mov  rcx, qword ptr [rsp+SortFrame.stdout]
    mov  rdx, qword ptr [rsp+SortFrame.flushPtr]
    mov  r8d, dword ptr [rsp+SortFrame.ioRequest]
    lea  r9, [rsp+SortFrame.ioCount]
    mov  dword ptr [rsp+SortFrame.ioCount], 0
    mov  qword ptr [rsp+SortFrame.arg5], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   .flush_failed
    mov  eax, dword ptr [rsp+SortFrame.ioCount]
    cmp  eax, dword ptr [rsp+SortFrame.ioRequest]
    ja   provider_violation
    test eax, eax
    jz   .flush_stalled
    add  qword ptr [rsp+SortFrame.flushPtr], rax
    sub  qword ptr [rsp+SortFrame.flushRemaining], rax
    jmp  .flush_head
.flush_complete:
    mov  qword ptr [rsp+SortFrame.outUsed], 0
    xor  eax, eax
    jmp  .flush_done
.flush_failed:
    mov  eax, 1
    jmp  .flush_done
.flush_stalled:
    mov  eax, 2
.flush_done:
}

def bufferAppendMacro : TransparentAsmMacro plan := asm_macro buffer_append(pointer, length) {
    mov  qword ptr [rsp+SortFrame.savedRsi], rsi
    mov  qword ptr [rsp+SortFrame.savedRdi], rdi
    mov  qword ptr [rsp+SortFrame.appendPtr], pointer
    mov  qword ptr [rsp+SortFrame.appendRemaining], length
.append_head:
    cmp  qword ptr [rsp+SortFrame.appendRemaining], 0
    je   .append_complete
    cmp  qword ptr [rsp+SortFrame.outUsed], 65536
    jb   .append_have_room
    flush_output -> eax
    test eax, eax
    jnz  .append_restore
    jmp  .append_head
.append_have_room:
    mov  rcx, 65536
    sub  rcx, qword ptr [rsp+SortFrame.outUsed]
    mov  rax, qword ptr [rsp+SortFrame.appendRemaining]
    cmp  rax, rcx
    cmovb rcx, rax
    mov  r10, rcx
    mov  rsi, qword ptr [rsp+SortFrame.appendPtr]
    lea  rdi, [rip + output_buffer]
    add  rdi, qword ptr [rsp+SortFrame.outUsed]
    cld
    rep movsb
    mov  qword ptr [rsp+SortFrame.appendPtr], rsi
    sub  qword ptr [rsp+SortFrame.appendRemaining], r10
    add  qword ptr [rsp+SortFrame.outUsed], r10
    jmp  .append_head
.append_complete:
    xor  eax, eax
.append_restore:
    mov  rsi, qword ptr [rsp+SortFrame.savedRsi]
    mov  rdi, qword ptr [rsp+SortFrame.savedRdi]
}

def failureExitMacro : TransparentAsmMacro plan := asm_macro failure_exit(outcome) {
    mov  ecx, policy.status outcome
    jmp  exit
}

def sortMacroRegistry : TransparentMacroRegistry plan :=
  #[compareRecordsMacro, flushOutputMacro, bufferAppendMacro, failureExitMacro]

end Grass.Spikes.Sort
