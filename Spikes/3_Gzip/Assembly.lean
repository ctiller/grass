import Grass.Assembly.X86
import Spikes.«3_Gzip».Data

namespace Grass.Spikes.Gzip

structure GzipMachineState where
  input : OwnedBuffer
  window : OwnedBuffer
  head : OwnedBuffer
  prev : OwnedBuffer
  tokens : OwnedBuffer
  output : OwnedBuffer
  crc : UInt32
  inputSize : UInt32
  bitAccumulator : UInt64
  bitCount : UInt8
  blockLength : UInt32
  generation : UInt16
  phase : GzipPhase

def gzipSource : AsmSource platformPlan := asm_source using codecPlan {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, 72
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, -1
    je   stdin_unavailable
    mov  r13, rax
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, -1
    je   stdout_unavailable
    mov  r14, rax
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  rbx, rax
    mov  rcx, rbx
    xor  edx, edx
    mov  r8d, 295168
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  r12, rax
    mov  [r12+0], rbx
    mov  [r12+8], r13
    mov  [r12+16], r14
    mov  [r12+56], r12
    lea  rax, [r12+256]
    mov  [r12+64], rax
    lea  rax, [r12+33024]
    mov  [r12+72], rax
    lea  rax, [r12+164096]
    mov  [r12+80], rax
    lea  rax, [r12+229632]
    mov  [r12+88], rax
    mov  dword ptr [r12+24], 0
    mov  dword ptr [r12+28], 0
    mov  dword ptr [r12+32], 10
    mov  dword ptr [r12+36], 0
    mov  qword ptr [r12+40], 0
    mov  dword ptr [r12+48], 0xffffffff
    mov  dword ptr [r12+52], 0
    mov  rdi, [r12+88]
    mov  rax, 0x0000000000088b1f
    mov  [rdi], rax
    mov  word ptr [rdi+8], 0xff00
    jmp  read_head

read_head: @invariant collecting_block(state, capacity=32768)
           @frontier_or_measure(read_or_remaining_spare)
    mov  eax, [r12+24]
    cmp  eax, 32768
    je   process_nonfinal_block
    mov  ecx, 32768
    sub  ecx, eax
    mov  [r12+96], ecx
    mov  rcx, [r12+8]
    mov  rdx, [r12+64]
    add  rdx, rax
    mov  r8d, [r12+96]
    lea  r9, [rsp+40]
    mov  dword ptr [rsp+40], 0
    mov  qword ptr [rsp+32], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, [rsp+40]
    cmp  eax, [r12+96]
    ja   read_count_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    mov  [r12+100], eax
    mov  esi, [r12+24]
    add  [r12+24], eax
    add  [r12+52], eax
    mov  edi, [r12+100]
    mov  rbx, [r12+64]
    add  rbx, rsi
crc_byte_head: @invariant crc32_prefix(transferred-edi)
               @measure edi
    test edi, edi
    jz   read_head
    movzx edx, byte ptr [rbx]
    mov  eax, [r12+48]
    xor  al, dl
    mov  ecx, 8
crc_bit_head: @measure ecx
    mov  edx, eax
    and  edx, 1
    neg  edx
    shr  eax, 1
    and  edx, 0xedb88320
    xor  eax, edx
    dec  ecx
    jnz  crc_bit_head
    mov  [r12+48], eax
    inc  rbx
    dec  edi
    jmp  crc_byte_head

process_nonfinal_block:
    xor  ecx, ecx
    call_local process_block
    test eax, eax
    jnz  route_io_error
    mov  dword ptr [r12+24], 0
    jmp  read_head

input_eof:
    mov  ecx, 1
    call_local process_block
    test eax, eax
    jnz  route_io_error
    call_local align_writer
    test eax, eax
    jnz  route_io_error
    mov  eax, [r12+48]
    not  eax
    mov  ebx, eax
    mov  esi, 4
trailer_crc_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_crc_head
    mov  ebx, [r12+52]
    mov  esi, 4
trailer_size_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_size_head
    call_local flush_output
    test eax, eax
    jnz  route_io_error
    jmp  exit_success


process_block: @contract fixed_block_refines_input
    push rbx
    push rbp
    push rsi
    push rdi
    push r13
    push r14
    push r15
    sub  rsp, 48
    mov  ebp, ecx
    mov  rdi, [r12+72]
    mov  ecx, 65536
    mov  ax, 0xffff
    cld
    rep  stosw
    mov  dword ptr [r12+28], 0
    mov  eax, ebp
    or   eax, 2
    mov  ecx, 3
    call_local emit_bits
    test eax, eax
    jnz  process_block_return
token_head: @invariant token_prefix_expands_to_input_prefix(position)
            @measure inputLen-position
    mov  esi, [r12+28]
    cmp  esi, [r12+24]
    jae  token_eob
    mov  eax, [r12+24]
    sub  eax, esi
    cmp  eax, 3
    jb   token_literal
    mov  rdi, [r12+64]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rbx, [r12+72]
    movzx r13d, word ptr [rbx+rax*2]
    mov  rdx, [r12+80]
    mov  word ptr [rdx+rsi*2], r13w
    mov  word ptr [rbx+rax*2], si
    mov  r14d, 2
    xor  r15d, r15d
    mov  ebx, 64
candidate_head: @invariant candidates_strictly_precede_position
                @measure (ebx, chain_rank)
    test ebx, ebx
    jz   candidate_done
    cmp  r13d, 0xffff
    je   candidate_done
    cmp  r13d, esi
    jae  dictionary_violation
    mov  eax, esi
    sub  eax, r13d
    cmp  eax, 32768
    ja   candidate_next
    mov  ebp, [r12+24]
    sub  ebp, esi
    cmp  ebp, 258
    jbe  compare_setup
    mov  ebp, 258
compare_setup:
    xor  ecx, ecx
    mov  rdi, [r12+64]
compare_head: @measure ebp-ecx
    cmp  ecx, ebp
    jae  compare_done
    mov  r8d, r13d
    add  r8d, ecx
    movzx r9d, byte ptr [rdi+r8]
    mov  r10d, esi
    add  r10d, ecx
    cmp  r9b, byte ptr [rdi+r10]
    jne  compare_done
    inc  ecx
    jmp  compare_head
compare_done:
    cmp  ecx, r14d
    jbe  candidate_next
    mov  r14d, ecx
    mov  r15d, esi
    sub  r15d, r13d
    cmp  ecx, ebp
    je   candidate_done
candidate_next:
    mov  rdx, [r12+80]
    movzx r13d, word ptr [rdx+r13*2]
    dec  ebx
    jmp  candidate_head
candidate_done:
    cmp  r14d, 3
    jb   token_literal_after_insert
    mov  ecx, r14d
    mov  edx, r15d
    call_local emit_reference
    test eax, eax
    jnz  process_block_return
    mov  ebx, esi
    add  ebx, r14d
    inc  esi
insert_consumed_head: @invariant inserted_range(oldPosition,esi)
                      @measure ebx-esi
    cmp  esi, ebx
    jae  reference_advance
    mov  eax, [r12+24]
    sub  eax, esi
    cmp  eax, 3
    jb   insert_consumed_skip
    mov  rdi, [r12+64]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rdi, [r12+72]
    movzx ecx, word ptr [rdi+rax*2]
    mov  rdx, [r12+80]
    mov  word ptr [rdx+rsi*2], cx
    mov  word ptr [rdi+rax*2], si
insert_consumed_skip:
    inc  esi
    jmp  insert_consumed_head
reference_advance:
    mov  [r12+28], ebx
    jmp  token_head
token_literal_after_insert:
token_literal:
    mov  rdi, [r12+64]
    movzx ecx, byte ptr [rdi+rsi]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  process_block_return
    inc  esi
    mov  [r12+28], esi
    jmp  token_head
token_eob:
    mov  ecx, 256
    call_local emit_fixed_symbol
process_block_return:
    add  rsp, 48
    pop  r15
    pop  r14
    pop  r13
    pop  rdi
    pop  rsi
    pop  rbp
    pop  rbx
    ret
dictionary_violation:
    mov  eax, 4
    jmp  process_block_return


emit_reference:
    push rbx
    push rsi
    push rdi
    sub  rsp, 32
    mov  ebx, ecx
    mov  esi, edx
    xor  edi, edi
length_code_head: @measure 29-edi
    cmp  edi, 28
    je   length_code_found
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  ebx, eax
    jb   reference_impossible
    cmp  ebx, edx
    jb   length_code_found
    inc  edi
    jmp  length_code_head
length_code_found:
    lea  ecx, [rdi+257]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + lengthExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   distance_lookup
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, ebx
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    test eax, eax
    jnz  reference_return
distance_lookup:
    xor  edi, edi
distance_code_head: @measure 30-edi
    cmp  edi, 29
    je   distance_code_found
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  esi, eax
    jb   reference_impossible
    cmp  esi, edx
    jb   distance_code_found
    inc  edi
    jmp  distance_code_head
distance_code_found:
    mov  eax, edi
    mov  ecx, 5
    call_local reverse_low_bits
    mov  ecx, 5
    call_local emit_bits
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + distanceExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   reference_ok
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, esi
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    jmp  reference_return
reference_ok:
    xor  eax, eax
reference_return:
    add  rsp, 32
    pop  rdi
    pop  rsi
    pop  rbx
    ret
reference_impossible:
    mov  eax, 4
    jmp  reference_return



emit_fixed_symbol:
    sub  rsp, 40
    cmp  ecx, 143
    ja   fixed_144
    lea  eax, [rcx+0x30]
    mov  ecx, 8
    jmp  fixed_reverse
fixed_144:
    cmp  ecx, 255
    ja   fixed_256
    lea  eax, [rcx+0x100]
    mov  ecx, 9
    jmp  fixed_reverse
fixed_256:
    cmp  ecx, 279
    ja   fixed_280
    lea  eax, [rcx-256]
    mov  ecx, 7
    jmp  fixed_reverse
fixed_280:
    cmp  ecx, 287
    ja   fixed_symbol_impossible
    lea  eax, [rcx-88]
    mov  ecx, 8
fixed_reverse:
    mov  r10d, ecx
    call_local reverse_low_bits
    mov  ecx, r10d
    call_local emit_bits
    add  rsp, 40
    ret
fixed_symbol_impossible:
    mov  eax, 4
    add  rsp, 40
    ret


reverse_low_bits:
    xor  edx, edx
reverse_head: @measure ecx
    test ecx, ecx
    jz   reverse_done
    shl  edx, 1
    mov  r8d, eax
    and  r8d, 1
    or   edx, r8d
    shr  eax, 1
    dec  ecx
    jmp  reverse_head
reverse_done:
    mov  eax, edx
    ret


emit_bits:
    push rbx
    sub  rsp, 32
    mov  r10d, ecx
    mov  edx, 1
    mov  ecx, r10d
    shl  edx, cl
    dec  edx
    and  eax, edx
    mov  edx, [r12+36]
    mov  r8, [r12+40]
    mov  r9, rax
    mov  cl, dl
    shl  r9, cl
    or   r8, r9
    add  edx, r10d
emit_full_byte_head: @invariant bitAccRep(bitAcc,bitCount)
                     @measure edx
    cmp  edx, 8
    jb   emit_bits_store
    cmp  dword ptr [r12+32], 65536
    jne  emit_bits_space
    mov  [r12+40], r8
    mov  [r12+36], edx
    call_local flush_output
    test eax, eax
    jnz  emit_bits_return
    mov  r8, [r12+40]
    mov  edx, [r12+36]
emit_bits_space:
    mov  rbx, [r12+88]
    mov  ecx, [r12+32]
    mov  byte ptr [rbx+rcx], r8b
    inc  ecx
    mov  [r12+32], ecx
    shr  r8, 8
    sub  edx, 8
    jmp  emit_full_byte_head
emit_bits_store:
    mov  [r12+40], r8
    mov  [r12+36], edx
    xor  eax, eax
emit_bits_return:
    add  rsp, 32
    pop  rbx
    ret


align_writer:
    mov  ecx, [r12+36]
    test ecx, ecx
    jz   align_done
    mov  edx, 8
    sub  edx, ecx
    xor  eax, eax
    mov  ecx, edx
    jmp  emit_bits
align_done:
    xor  eax, eax
    ret


emit_raw_byte:
    push rbx
    sub  rsp, 32
    mov  ebx, eax
    cmp  dword ptr [r12+36], 0
    jne  raw_byte_impossible
    cmp  dword ptr [r12+32], 65536
    jne  raw_byte_space
    call_local flush_output
    test eax, eax
    jnz  raw_byte_return
raw_byte_space:
    mov  rdx, [r12+88]
    mov  ecx, [r12+32]
    mov  byte ptr [rdx+rcx], bl
    inc  ecx
    mov  [r12+32], ecx
    xor  eax, eax
raw_byte_return:
    add  rsp, 32
    pop  rbx
    ret
raw_byte_impossible:
    mov  eax, 4
    jmp  raw_byte_return


flush_output:
    push rbx
    push rsi
    push rdi
    sub  rsp, 48
    xor  ebx, ebx
flush_head: @invariant SliceConsumerInvariant(output,consumed,outLen)
            @frontier_or_measure(write_or_remaining)
    mov  esi, [r12+32]
    cmp  ebx, esi
    jae  flush_done
    mov  edi, esi
    sub  edi, ebx
    mov  [r12+96], edi
    mov  rcx, [r12+16]
    mov  rdx, [r12+88]
    add  rdx, rbx
    mov  r8d, [r12+96]
    lea  r9, [rsp+40]
    mov  dword ptr [rsp+40], 0
    mov  qword ptr [rsp+32], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   flush_failed
    mov  eax, [rsp+40]
    cmp  eax, [r12+96]
    ja   flush_violation
    test eax, eax
    jz   flush_no_progress
    add  ebx, eax
    jmp  flush_head
flush_done:
    mov  dword ptr [r12+32], 0
    xor  eax, eax
    jmp  flush_return
flush_failed:
    mov  eax, 1
    jmp  flush_return
flush_no_progress:
    mov  eax, 2
    jmp  flush_return
flush_violation:
    mov  eax, 3
flush_return:
    add  rsp, 48
    pop  rdi
    pop  rsi
    pop  rbx
    ret

route_io_error:
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    cmp  eax, 3
    je   write_count_violation @violation_edge(.excessWriteCount)
    jmp  dictionary_violation_terminal @violation_edge(.internalCodecInvariant)

stdin_unavailable:      @terminal(.stdinUnavailable)
    mov  ecx, 1
    jmp  exit
stdout_unavailable:     @terminal(.stdoutUnavailable)
    mov  ecx, 1
    jmp  exit
resource_exhausted_no_root: @terminal(.resourceExhausted)
    mov  ecx, 1
    jmp  exit
read_failed:            @terminal(.readFailed)
    mov  ecx, 1
    jmp  exit
write_failed:           @terminal(.writeFailed)
    mov  ecx, 1
    jmp  exit
no_progress:            @terminal(.noProgress)
    mov  ecx, 1
    jmp  exit
exit_success:           @terminal(.success)
    xor  ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
read_count_violation:
    ud2 @containment_tail(.excessReadCount)
write_count_violation:
    ud2 @containment_tail(.excessWriteCount)
dictionary_violation_terminal:
    ud2 @containment_tail(.internalCodecInvariant)
}

end Grass.Spikes.Gzip
