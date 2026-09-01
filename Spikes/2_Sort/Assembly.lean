import Spikes.«2_Sort».Macros

namespace Grass.Spikes.Sort

def sortSource : AsmSource plan := asm_source {

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

read_head: @invariant growable_input_vec(r13, len=r14, cap=r15)
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

grow_input: @invariant growable_input_vec(r13, len=r14, cap=r15)
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
count_loop: @invariant count_lf_prefix(r13, r14, rbx, rbp)
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
descriptor_scan: @invariant represents_scanned_prefix(r8,r9,r10)
                 @measure r14-r8
    cmp  r8, r14
    jae  descriptor_suffix
    cmp  byte ptr [r13+r8], 10
    jne  descriptor_next_byte
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx+0], r9
    mov  rcx, r8
    sub  rcx, r9
    mov  qword ptr [rdx+8], rcx
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
    mov  qword ptr [rdx+0], r9
    mov  rcx, r14
    sub  rcx, r9
    mov  qword ptr [rdx+8], rcx
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
    compare_records rdx, r8 -> eax
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
    mov  rcx, qword ptr [rdx+0]
    mov  qword ptr [r8+0], rcx
    mov  rcx, qword ptr [rdx+8]
    mov  qword ptr [r8+8], rcx
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
    mov  rdx, qword ptr [rax+0]
    add  rdx, r13
    mov  r8, qword ptr [rax+8]
    buffer_append rdx, r8 -> eax
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    lea  rdx, [rip + lf_byte]
    mov  r8d, 1
    buffer_append rdx, r8 -> eax
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    add  qword ptr [rsp+SortFrame.outputIndex], 1
    jmp  emit_head

emit_final_flush:
    flush_output -> eax
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    jmp  exit_success

stdin_unavailable:   @terminal(.stdinUnavailable)
    failure_exit $policy
read_failed:         @terminal(.readFailed)
    failure_exit $policy
resource_exhausted:  @terminal(.resourceExhausted)
    failure_exit $policy
stdout_unavailable:  @terminal(.stdoutUnavailable)
    failure_exit $policy
write_failed:        @terminal(.writeFailed)
    failure_exit $policy
no_progress:         @terminal(.noProgress)
    failure_exit $policy
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
