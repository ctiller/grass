import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Std.Sort.Stable
import Spikes.«2_Sort».Spec

namespace Grass.Spikes.Sort

def policy : TargetOutcomeProjection SortOutcome UInt32 :=
  .successOrFailure
    (success := .success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

def stableSortContract : ComponentContract :=
  StableSort.contract format order

def stableSortModel : ImplementationModel :=
  StableSort.bottomUpMergeModel format order

theorem stableSortModelCorrect :
    ImplementationRealizesContract stableSortModel stableSortContract :=
  StableSort.bottomUpMergeCorrect format order

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StandardByteSort projection

def sortStaticObjects : StaticObjectTable := static_objects {
  rodata align 1 {
    lf_byte: bytes #[10]
  }
  bss align 64 {
    output_buffer: zero 65536
  }
}

structure PhysicalLineDesc where
  offset : UInt64
  length : UInt64

def LineDesc : StructLayout Win64 := StructLayout.derive PhysicalLineDesc

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

def compareRecords (left right : AddressOperand) :
    VerifiedFragment (CompareEntry left right) CompareExit := asm_fragment {
    mov  rax, qword ptr [left + LineDesc.offset]
    add  rax, r13
    mov  r10, qword ptr [left + LineDesc.length]
    mov  rcx, qword ptr [right + LineDesc.offset]
    add  rcx, r13
    mov  r11, qword ptr [right + LineDesc.length]
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

def flushOutput :
    VerifiedFragment FlushOutputEntry FlushOutputExit := asm_fragment {
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

def bufferAppend (pointer length : MachineOperand) :
    VerifiedFragment (BufferAppendEntry pointer length) BufferAppendExit := asm_fragment {
    mov  qword ptr [rsp+SortFrame.savedRsi], rsi
    mov  qword ptr [rsp+SortFrame.savedRdi], rdi
    mov  qword ptr [rsp+SortFrame.appendPtr], pointer
    mov  qword ptr [rsp+SortFrame.appendRemaining], length
.append_head:
    cmp  qword ptr [rsp+SortFrame.appendRemaining], 0
    je   .append_complete
    cmp  qword ptr [rsp+SortFrame.outUsed], 65536
    jb   .append_have_room
    $(flushOutput)
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

def failureExit (outcome : SortOutcome) :
    VerifiedFragment (FailureExitEntry outcome) NoReturn := asm_fragment {
    mov  ecx, policy.status outcome
    jmp  exit
}

def sortConstructorClosure : FragmentConstructorClosure plan := constructors {
  compareRecords
  flushOutput
  bufferAppend
  failureExit
}

def sortSource : AsmSource plan :=
  asm_source
    (statics := sortStaticObjects)
    (constructors := sortConstructorClosure) {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, SortFrame.size
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted
    mov  r12, rax
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdin_unavailable
    mov  qword ptr [rsp+SortFrame.stdin], rax
    xor  r13d, r13d
    xor  r14d, r14d
    xor  r15d, r15d
    jmp  read_head

read_head: @placement [input := r13, length := r14, capacity := r15]
           @invariant growable_input_vec
           @frontier_or_measure(read_or_growth)
    cmp  r14, r15
    je   grow_input
read_issue:

    mov  rax, r15
    sub  rax, r14
    mov  r8d, 0xffffffff
    cmp  rax, r8
    cmovb r8, rax
    test r8d, r8d
    jz   grow_input
    mov  dword ptr [rsp+SortFrame.ioRequest], r8d
    mov  rcx, qword ptr [rsp+SortFrame.stdin]
    lea  rdx, [r13+r14]
    lea  r9, [rsp+SortFrame.ioCount]
    mov  dword ptr [rsp+SortFrame.ioCount], 0
    mov  qword ptr [rsp+SortFrame.arg5], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, dword ptr [rsp+SortFrame.ioCount]
    cmp  eax, dword ptr [rsp+SortFrame.ioRequest]
    ja   provider_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    add  r14, rax
    jmp  read_head

grow_input: @placement [input := r13, length := r14, capacity := r15]
            @invariant growable_input_vec
            @measure representable_capacity_remaining
    test r15, r15
    jnz  grow_existing
    mov  ebx, 4096
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  r13, rax
    mov  r15, rbx
    jmp  read_issue

grow_existing:
    mov  rbx, -1
    shr  rbx, 1
    cmp  r15, rbx
    ja   grow_saturate
    mov  rbx, r15
    shl  rbx, 1
    jmp  grow_realloc
grow_saturate:
    mov  rbx, -1
    cmp  r15, rbx
    je   resource_exhausted
grow_realloc:
    mov  rcx, r12
    xor  edx, edx
    mov  r8, r13
    mov  r9, rbx
    call qword ptr [rip + __imp_HeapReAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  r13, rax
    mov  r15, rbx
    jmp  read_issue

input_eof:
    xor  ebp, ebp
    xor  ebx, ebx
    test r14, r14
    jz   no_descriptors
count_loop: @placement [input := r13, inputLength := r14,
                        cursor := rbx, lineCount := rbp]
            @invariant count_lf_prefix
            @measure r14-rbx
    cmp  rbx, r14
    jae  count_suffix
    cmp  byte ptr [r13+rbx], 10
    jne  count_next
    add  rbp, 1
    jc   resource_exhausted
count_next:
    add  rbx, 1
    jc   resource_exhausted
    jmp  count_loop
count_suffix:
    lea  rax, [r14-1]
    cmp  byte ptr [r13+rax], 10
    je   allocate_descriptors
    add  rbp, 1
    jc   resource_exhausted

allocate_descriptors:
    mov  rbx, rbp
    shl  rbx, 4
    mov  rax, rbx
    shr  rax, 4
    cmp  rax, rbp
    jne  resource_exhausted
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  rdi, rax
    mov  qword ptr [rsp+SortFrame.lines], rax
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  rsi, rax
    mov  qword ptr [rsp+SortFrame.scratch], rax
    jmp  descriptor_scan_init

no_descriptors:
    xor  edi, edi
    xor  esi, esi
    mov  qword ptr [rsp+SortFrame.lines], 0
    mov  qword ptr [rsp+SortFrame.scratch], 0
    mov  qword ptr [rsp+SortFrame.lineCount], 0
    mov  qword ptr [rsp+SortFrame.finalDescriptors], 0
    jmp  sort_done

descriptor_scan_init:
    mov  qword ptr [rsp+SortFrame.lineCount], rbp
    xor  r8d, r8d
    xor  r9d, r9d
    xor  r10d, r10d
descriptor_scan: @placement [cursor := r8, lineStart := r9, index := r10]
                 @invariant represents_scanned_prefix
                 @measure r14-r8
    cmp  r8, r14
    jae  descriptor_suffix
    cmp  byte ptr [r13+r8], 10
    jne  descriptor_next_byte
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r8
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
    add  r8, 1
    mov  r9, r8
    jmp  descriptor_scan
descriptor_next_byte:
    add  r8, 1
    jmp  descriptor_scan
descriptor_suffix:
    cmp  r9, r14
    jae  descriptor_scan_done
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r14
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
descriptor_scan_done:
    cmp  r10, rbp
    jne  internal_fault
    mov  qword ptr [rsp+SortFrame.width], 1
    jmp  sort_pass

sort_pass: @contract StableSortContract
           @invariant stable_merge_pass(input, lines, scratch)
           @measure merge_pass_measure
    mov  rax, qword ptr [rsp+SortFrame.width]
    cmp  rax, rbp
    jae  sort_complete
    mov  qword ptr [rsp+SortFrame.left], 0
merge_run_head:
    mov  rax, qword ptr [rsp+SortFrame.left]
    cmp  rax, rbp
    jae  merge_pass_done
    mov  rcx, rax
    add  rcx, qword ptr [rsp+SortFrame.width]
    cmp  rcx, rbp
    cmova rcx, rbp
    mov  qword ptr [rsp+SortFrame.mid], rcx
    mov  rdx, rcx
    add  rdx, qword ptr [rsp+SortFrame.width]
    cmp  rdx, rbp
    cmova rdx, rbp
    mov  qword ptr [rsp+SortFrame.right], rdx
    mov  qword ptr [rsp+SortFrame.i], rax
    mov  qword ptr [rsp+SortFrame.j], rcx
    mov  qword ptr [rsp+SortFrame.k], rax
merge_choose: @invariant stable_merge_cursors(i,j,k)
              @measure (mid-i)+(right-j)
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_drain_right
    mov  rcx, qword ptr [rsp+SortFrame.j]
    cmp  rcx, qword ptr [rsp+SortFrame.right]
    jae  merge_drain_left
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  rax, rcx
    shl  rax, 4
    lea  r8, [rdi+rax]
    $(compareRecords rdx r8)
    cmp  eax, 0
    jle  merge_take_left
merge_take_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_take_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    add  qword ptr [rsp+SortFrame.i], 1
merge_copy:
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  rax, qword ptr [rsp+SortFrame.k]
    shl  rax, 4
    lea  r8, [rsi+rax]
    mov  rcx, qword ptr [rdx + LineDesc.offset]
    mov  qword ptr [r8 + LineDesc.offset], rcx
    mov  rcx, qword ptr [rdx + LineDesc.length]
    mov  qword ptr [r8 + LineDesc.length], rcx
    add  qword ptr [rsp+SortFrame.k], 1
    jmp  merge_choose
merge_drain_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.i], 1
    jmp  merge_copy
merge_drain_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    cmp  rax, qword ptr [rsp+SortFrame.right]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_run_done:
    mov  rax, qword ptr [rsp+SortFrame.right]
    mov  qword ptr [rsp+SortFrame.left], rax
    jmp  merge_run_head
merge_pass_done:
    xchg rdi, rsi
    mov  rax, qword ptr [rsp+SortFrame.width]
    add  rax, rax
    cmp  rax, rbp
    cmova rax, rbp
    mov  qword ptr [rsp+SortFrame.width], rax
    jmp  sort_pass
sort_complete:
    mov  qword ptr [rsp+SortFrame.finalDescriptors], rdi

sort_done:
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdout_unavailable
    mov  qword ptr [rsp+SortFrame.stdout], rax

    mov  qword ptr [rsp+SortFrame.outputIndex], 0
    mov  qword ptr [rsp+SortFrame.outUsed], 0
    jmp  emit_head

emit_head: @invariant sorted_occurrence_consumer(finalDescriptors)
           @invariant buffered_stdout(output_buffer, outUsed, committedPrefix)
           @measure remaining_source_bytes_plus_records
    mov  rax, qword ptr [rsp+SortFrame.outputIndex]
    cmp  rax, rbp
    jae  emit_final_flush
    shl  rax, 4
    add  rax, qword ptr [rsp+SortFrame.finalDescriptors]
    mov  rdx, qword ptr [rax + LineDesc.offset]
    add  rdx, r13
    mov  r8, qword ptr [rax + LineDesc.length]
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    lea  rdx, [rip + lf_byte]
    mov  r8d, 1
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    add  qword ptr [rsp+SortFrame.outputIndex], 1
    jmp  emit_head

emit_final_flush:
    $(flushOutput)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    jmp  exit_success

stdin_unavailable:   @terminal(.inputFailure) @audit(.stdinUnavailable)
    $(failureExit .inputFailure)
read_failed:         @terminal(.inputFailure) @audit(.readFailed)
    $(failureExit .inputFailure)
resource_exhausted:  @terminal(.allocationFailure) @audit(.resourceExhausted)
    $(failureExit .allocationFailure)
stdout_unavailable:  @terminal(.outputFailure) @audit(.stdoutUnavailable)
    $(failureExit .outputFailure)
write_failed:        @terminal(.outputFailure) @audit(.writeFailed)
    $(failureExit .outputFailure)
no_progress:         @terminal(.outputFailure) @audit(.noProgress)
    $(failureExit .outputFailure)
exit_success:       @terminal(.success)
    xor ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
provider_violation:
    ud2 @containment_tail(.returnedCountExceedsRequest)
internal_fault:
    ud2 @containment_tail(.provedUnreachable)

}

end Grass.Spikes.Sort
