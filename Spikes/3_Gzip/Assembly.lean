import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Std.Zlib.Fixed32K
import Spikes.«3_Gzip».Spec

namespace Grass.Spikes.Gzip

def policy : TargetOutcomeProjection GzipOutcome UInt32 :=
  .successOrFailure
    (success := GzipOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

def codecPlan : GzipImplementationPlan :=
  .fixed32KHashChain (maxProbes := 64)

def fixed32KContract : ComponentContract :=
  Std.Zlib.Fixed32K.contract codecPlan

def fixed32KModel : ImplementationModel :=
  Std.Zlib.Fixed32K.model codecPlan

theorem fixed32KModelCorrect :
    ImplementationRealizesContract fixed32KModel fixed32KContract :=
  Std.Zlib.Fixed32K.correct codecPlan

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StreamingIO projection

structure GzipFrameFields where
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32
  locals : Bytes 28

def GzipFrame : FrameLayout Win64 := FrameLayout.derive GzipFrameFields

structure GzipArenaFields where
  heap : UInt64
  stdin : UInt64
  stdout : UInt64
  inputLength : UInt32
  position : UInt32
  outputLength : UInt32
  bitCount : UInt32
  bitAccumulator : UInt64
  crc : UInt32
  totalInput : UInt32
  root : UInt64
  input : UInt64
  head : UInt64
  prev : UInt64
  output : UInt64
  ioRequest : UInt32
  ioCount : UInt32
  reserved : Bytes 152
  inputBytes : Bytes 32768
  headEntries : Bytes 131072
  prevEntries : Bytes 65536
  outputBytes : Bytes 65536

def GzipArena : StructLayout Win64 := StructLayout.derive GzipArenaFields

structure GzipHeaderFields where
  magic : UInt16
  compressionMethod : UInt8
  flags : UInt8
  modificationTime : UInt32
  extraFlags : UInt8
  operatingSystem : UInt8

def GzipHeader : PackedStructLayout :=
  PackedStructLayout.derive GzipHeaderFields

def ProcessBlockFrame :=
  Win64.callFrameAfterSaves #[rbx, rbp, rsi, rdi, r13, r14, r15]

def EmitReferenceFrame := Win64.callFrameAfterSaves #[rbx, rsi, rdi]

def EmitFixedSymbolFrame := Win64.callFrameAfterSaves #[]

def EmitBitsFrame := Win64.callFrameAfterSaves #[rbx]

def EmitRawByteFrame := Win64.callFrameAfterSaves #[rbx]

structure FlushFrameFields where
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32

def FlushFrame : FrameLayout Win64 := FrameLayout.derive FlushFrameFields

def gzipSource : AsmSource platformPlan :=
  asm_source
    (model := codecPlan)
    (statics := Std.Zlib.Fixed32K.staticObjects codecPlan) {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, GzipFrame.size
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
    mov  r8d, GzipArena.size
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  r12, rax
    mov  [r12 + GzipArena.heap], rbx
    mov  [r12 + GzipArena.stdin], r13
    mov  [r12 + GzipArena.stdout], r14
    mov  [r12 + GzipArena.root], r12
    lea  rax, [r12 + GzipArena.inputBytes]
    mov  [r12 + GzipArena.input], rax
    lea  rax, [r12 + GzipArena.headEntries]
    mov  [r12 + GzipArena.head], rax
    lea  rax, [r12 + GzipArena.prevEntries]
    mov  [r12 + GzipArena.prev], rax
    lea  rax, [r12 + GzipArena.outputBytes]
    mov  [r12 + GzipArena.output], rax
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  dword ptr [r12 + GzipArena.outputLength], 10
    mov  dword ptr [r12 + GzipArena.bitCount], 0
    mov  qword ptr [r12 + GzipArena.bitAccumulator], 0
    mov  dword ptr [r12 + GzipArena.crc], 0xffffffff
    mov  dword ptr [r12 + GzipArena.totalInput], 0
    mov  rdi, [r12 + GzipArena.output]
    mov  rax, 0x0000000000088b1f
    mov  [rdi + GzipHeader.magic], rax
    mov  word ptr [rdi + GzipHeader.extraFlags], 0xff00
    jmp  read_head

read_head: @invariant collecting_block(state, capacity=32768)
           @frontier_or_measure(read_or_remaining_spare)
    mov  eax, [r12 + GzipArena.inputLength]
    cmp  eax, 32768
    je   process_nonfinal_block
    mov  ecx, 32768
    sub  ecx, eax
    mov  [r12 + GzipArena.ioRequest], ecx
    mov  rcx, [r12 + GzipArena.stdin]
    mov  rdx, [r12 + GzipArena.input]
    add  rdx, rax
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + GzipFrame.transferred]
    mov  dword ptr [rsp + GzipFrame.transferred], 0
    mov  qword ptr [rsp + GzipFrame.overlapped], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, [rsp + GzipFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   read_count_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    mov  [r12 + GzipArena.ioCount], eax
    mov  esi, [r12 + GzipArena.inputLength]
    add  [r12 + GzipArena.inputLength], eax
    add  [r12 + GzipArena.totalInput], eax
    mov  edi, [r12 + GzipArena.ioCount]
    mov  rbx, [r12 + GzipArena.input]
    add  rbx, rsi
crc_byte_head: @placement [remaining := edi]
               @invariant crc32_prefix(transferred - remaining)
               @measure edi
    test edi, edi
    jz   read_head
    movzx edx, byte ptr [rbx]
    mov  eax, [r12 + GzipArena.crc]
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
    mov  [r12 + GzipArena.crc], eax
    inc  rbx
    dec  edi
    jmp  crc_byte_head

process_nonfinal_block:
    xor  ecx, ecx
    call_local process_block
    test eax, eax
    jnz  route_io_error
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    jmp  read_head

input_eof:
    mov  ecx, 1
    call_local process_block
    test eax, eax
    jnz  route_io_error
    call_local align_writer
    test eax, eax
    jnz  route_io_error
    mov  eax, [r12 + GzipArena.crc]
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
    mov  ebx, [r12 + GzipArena.totalInput]
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


process_block: @implements fixed32KContract using fixed32KModelCorrect
    push rbx
    push rbp
    push rsi
    push rdi
    push r13
    push r14
    push r15
    sub  rsp, ProcessBlockFrame.size
    mov  ebp, ecx
    mov  rdi, [r12 + GzipArena.head]
    mov  ecx, 65536
    mov  ax, 0xffff
    cld
    rep  stosw
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  eax, ebp
    or   eax, 2
    mov  ecx, 3
    call_local emit_bits
    test eax, eax
    jnz  process_block_return
token_head: @invariant token_prefix_expands_to_input_prefix(position)
            @measure inputLen-position
    mov  esi, [r12 + GzipArena.position]
    cmp  esi, [r12 + GzipArena.inputLength]
    jae  token_eob
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   token_literal
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rbx, [r12 + GzipArena.head]
    movzx r13d, word ptr [rbx+rax*2]
    mov  rdx, [r12 + GzipArena.prev]
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
    mov  ebp, [r12 + GzipArena.inputLength]
    sub  ebp, esi
    cmp  ebp, 258
    jbe  compare_setup
    mov  ebp, 258
compare_setup:
    xor  ecx, ecx
    mov  rdi, [r12 + GzipArena.input]
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
    mov  rdx, [r12 + GzipArena.prev]
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
insert_consumed_head: @placement [cursor := esi]
                      @invariant inserted_range(oldPosition, cursor)
                      @measure ebx-esi
    cmp  esi, ebx
    jae  reference_advance
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   insert_consumed_skip
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rdi, [r12 + GzipArena.head]
    movzx ecx, word ptr [rdi+rax*2]
    mov  rdx, [r12 + GzipArena.prev]
    mov  word ptr [rdx+rsi*2], cx
    mov  word ptr [rdi+rax*2], si
insert_consumed_skip:
    inc  esi
    jmp  insert_consumed_head
reference_advance:
    mov  [r12 + GzipArena.position], ebx
    jmp  token_head
token_literal_after_insert:
token_literal:
    mov  rdi, [r12 + GzipArena.input]
    movzx ecx, byte ptr [rdi+rsi]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  process_block_return
    inc  esi
    mov  [r12 + GzipArena.position], esi
    jmp  token_head
token_eob:
    mov  ecx, 256
    call_local emit_fixed_symbol
process_block_return:
    add  rsp, ProcessBlockFrame.size
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
    sub  rsp, EmitReferenceFrame.size
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
    add  rsp, EmitReferenceFrame.size
    pop  rdi
    pop  rsi
    pop  rbx
    ret
reference_impossible:
    mov  eax, 4
    jmp  reference_return



emit_fixed_symbol:
    sub  rsp, EmitFixedSymbolFrame.size
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
    add  rsp, EmitFixedSymbolFrame.size
    ret
fixed_symbol_impossible:
    mov  eax, 4
    add  rsp, EmitFixedSymbolFrame.size
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
    sub  rsp, EmitBitsFrame.size
    mov  r10d, ecx
    mov  edx, 1
    mov  ecx, r10d
    shl  edx, cl
    dec  edx
    and  eax, edx
    mov  edx, [r12 + GzipArena.bitCount]
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  r9, rax
    mov  cl, dl
    shl  r9, cl
    or   r8, r9
    add  edx, r10d
emit_full_byte_head: @invariant bitAccRep(bitAcc,bitCount)
                     @measure edx
    cmp  edx, 8
    jb   emit_bits_store
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  emit_bits_space
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    call_local flush_output
    test eax, eax
    jnz  emit_bits_return
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  edx, [r12 + GzipArena.bitCount]
emit_bits_space:
    mov  rbx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rbx+rcx], r8b
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    shr  r8, 8
    sub  edx, 8
    jmp  emit_full_byte_head
emit_bits_store:
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    xor  eax, eax
emit_bits_return:
    add  rsp, EmitBitsFrame.size
    pop  rbx
    ret


align_writer:
    mov  ecx, [r12 + GzipArena.bitCount]
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
    sub  rsp, EmitRawByteFrame.size
    mov  ebx, eax
    cmp  dword ptr [r12 + GzipArena.bitCount], 0
    jne  raw_byte_impossible
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  raw_byte_space
    call_local flush_output
    test eax, eax
    jnz  raw_byte_return
raw_byte_space:
    mov  rdx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rdx+rcx], bl
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    xor  eax, eax
raw_byte_return:
    add  rsp, EmitRawByteFrame.size
    pop  rbx
    ret
raw_byte_impossible:
    mov  eax, 4
    jmp  raw_byte_return


flush_output:
    push rbx
    push rsi
    push rdi
    sub  rsp, FlushFrame.size
    xor  ebx, ebx
flush_head: @invariant SliceConsumerInvariant(output,consumed,outLen)
            @frontier_or_measure(write_or_remaining)
    mov  esi, [r12 + GzipArena.outputLength]
    cmp  ebx, esi
    jae  flush_done
    mov  edi, esi
    sub  edi, ebx
    mov  [r12 + GzipArena.ioRequest], edi
    mov  rcx, [r12 + GzipArena.stdout]
    mov  rdx, [r12 + GzipArena.output]
    add  rdx, rbx
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + FlushFrame.transferred]
    mov  dword ptr [rsp + FlushFrame.transferred], 0
    mov  qword ptr [rsp + FlushFrame.overlapped], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   flush_failed
    mov  eax, [rsp + FlushFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   flush_violation
    test eax, eax
    jz   flush_no_progress
    add  ebx, eax
    jmp  flush_head
flush_done:
    mov  dword ptr [r12 + GzipArena.outputLength], 0
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
    add  rsp, FlushFrame.size
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
