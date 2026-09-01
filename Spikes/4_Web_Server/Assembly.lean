import Grass.Assembly.X86
import Spikes.«4_Web_Server».Macros

namespace Grass.Spikes.WebServer

structure ServerEntryFrameFields where
  shadow : Bytes 32
  callArg5 : UInt64
  callArg6 : UInt64
  locals : Bytes 8

def ServerEntryFrame : FrameLayout Win64 :=
  FrameLayout.derive ServerEntryFrameFields

structure WorkerFrameFields where
  shadow : Bytes 32
  locals : Bytes 24

def WorkerFrame : FrameLayout Win64 := FrameLayout.derive WorkerFrameFields

def serverJoinContracts : JoinContractSelection platformPlan := cfg_join_contracts {
  entry => FixedPool.X86.serverEntry processPolicy executionEnvelope
  create_workers => FixedPool.X86.workerCreationLoop processPolicy
  resume_loop => FixedPool.X86.workerResumeLoop processPolicy
  join_workers => FixedPool.X86.workerJoinLoop processPolicy
  console_handler => FixedPool.X86.shutdownCallback processPolicy
  worker_entry => FixedPool.X86.workerEntry processPolicy
  worker_gate => FixedPool.X86.initializationGate processPolicy
  accept_wait => FixedPool.X86.acceptFrontier processPolicy
  preface_loop => Http2.X86.prefaceLoop processPolicy.connection
  connection_schedule => Http2.X86.connectionScheduler processPolicy.connection
  receive_result_observation => Http2.X86.receiveCancellationPoint processPolicy.connection
  frame_parse_loop => Http2.X86.frameParseLoop processPolicy.connection
  decode_fields => Http2.X86.normalizedFieldBlock processPolicy.connection
  send_suffix_loop => Http2.X86.partialSendLoop processPolicy.connection
  send_readiness_observation => Http2.X86.writerCancellationPoint processPolicy.connection
  enqueue_stream_error => Http2.X86.streamErrorJoin processPolicy.connection
  enqueue_connection_error => Http2.X86.connectionErrorJoin processPolicy.connection
  connection_draining => Http2.X86.goawayDrainLoop processPolicy.connection
  connection_close => Http2.X86.connectionTeardown processPolicy.connection
  connection_closed_boundary => Http2.X86.connectionCustodyDischarged processPolicy.connection
  worker_return => FixedPool.X86.workerLoansReturned processPolicy
}

def serverSource : AsmSource platformPlan :=
  asm_source
    (statics := serverStaticObjects)
    (constructors := serverMacros)
    (layouts := #[ServerEntryFrame, WorkerFrame])
    (joinContracts := serverJoinContracts) {

entry: @entrypoint @unwind(server_entry_unwind)
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, ServerEntryFrame.size
    xor  ebp, ebp
    xor  r13d, r13d
    mov  qword ptr [rip+listen_socket], INVALID_SOCKET
    mov  dword ptr [rip+shutdown], 0
    mov  dword ptr [rip+fatal], 0
    mov  dword ptr [rip+start_gate], 0
    mov  ecx, 0x0202
    lea  rdx, [rip+wsa_data]
    call qword ptr [rip+__imp_WSAStartup]
    test eax, eax
    jnz  exit_failure_no_wsa
    mov  ecx, AF_INET
    mov  edx, SOCK_STREAM
    mov  r8d, IPPROTO_TCP
    xor  r9d, r9d
    mov  qword ptr [rsp + ServerEntryFrame.callArg5], 0
    mov  dword ptr [rsp + ServerEntryFrame.callArg6], 0
    call qword ptr [rip+__imp_WSASocketW]
    cmp  rax, INVALID_SOCKET
    je   startup_failure_wsa
    mov  r12, rax
    mov  qword ptr [rip+listen_socket], rax
    mov  rcx, r12
    lea  rdx, [rip+bind_address]
    mov  r8d, 16
    call qword ptr [rip+__imp_bind]
    test eax, eax
    jnz  startup_failure_socket
    mov  rcx, r12
    mov  edx, SOMAXCONN
    call qword ptr [rip+__imp_listen]
    test eax, eax
    jnz  startup_failure_socket
    mov  dword ptr [rip+nonblocking_one], 1
    mov  rcx, r12
    mov  edx, FIONBIO
    lea  r8, [rip+nonblocking_one]
    call qword ptr [rip+__imp_ioctlsocket]
    test eax, eax
    jnz  startup_failure_socket
    lea  rcx, [rip+console_handler]
    mov  edx, 1
    call qword ptr [rip+__imp_SetConsoleCtrlHandler]
    test eax, eax
    jz   startup_failure_socket

create_workers: @placement [created := r13]
                @invariant created_prefix(worker_handles, worker_slots)
                @measure executionEnvelope.workerCount-r13
    cmp  r13d, executionEnvelope.workerCount
    je   resume_workers
    mov  rax, r13
    imul rax, rax, WORKER_SLOT_BYTES
    lea  r9, [rip+worker_slots]
    add  r9, rax
    xor  ecx, ecx
    xor  edx, edx
    lea  r8, [rip+worker_entry]
    mov  dword ptr [rsp + ServerEntryFrame.callArg5], CREATE_SUSPENDED
    mov  qword ptr [rsp + ServerEntryFrame.callArg6], 0
    call qword ptr [rip+__imp_CreateThread]
    test rax, rax
    jz   startup_partial_workers
    lea  rdx, [rip+worker_handles]
    mov  qword ptr [rdx+r13*8], rax
    inc  r13d
    jmp  create_workers

resume_workers:
    xor  r14d, r14d
resume_loop: @placement [resumed := r14, created := r13]
             @invariant resumed_prefix @measure created-resumed
    cmp  r14d, r13d
    je   publish_ready
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r14*8]
    call qword ptr [rip+__imp_ResumeThread]
    cmp  eax, -1
    je   fatal_exit
    inc  r14d
    jmp  resume_loop

publish_ready:
    mov  eax, 1
    xchg dword ptr [rip+start_gate], eax
service_loop: @reactive_frontier bounded_sleep
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  join_workers
    mov  ecx, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_Sleep]
    jmp  service_loop

startup_partial_workers:
    mov  ebp, 1
    mov  eax, 1
    xchg dword ptr [rip+shutdown], eax
    xor  r14d, r14d
resume_failure_workers: @placement [resumed := r14, created := r13]
                        @invariant failure_resumed_prefix
                        @measure created-resumed
    cmp  r14d, r13d
    je   join_workers
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r14*8]
    call qword ptr [rip+__imp_ResumeThread]
    cmp  eax, -1
    je   fatal_exit
    inc  r14d
    jmp  resume_failure_workers

join_workers: @placement [remainingWorkers := r13]
              @invariant joined_suffix(worker_handles) @measure remainingWorkers
    test r13d, r13d
    jz   unregister_handler
    dec  r13d
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r13*8]
    mov  edx, INFINITE
    call qword ptr [rip+__imp_WaitForSingleObject]
    cmp  eax, WAIT_FAILED
    je   fatal_exit
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r13*8]
    call qword ptr [rip+__imp_CloseHandle]
    test eax, eax
    jnz  join_workers
    mov  ebp, 1
    jmp  join_workers

unregister_handler:
    lea  rcx, [rip+console_handler]
    xor  edx, edx
    call qword ptr [rip+__imp_SetConsoleCtrlHandler]
    test eax, eax
    jnz  close_listener
    mov  ebp, 1

close_listener:
    mov  rcx, r12
    call qword ptr [rip+__imp_closesocket]
    test eax, eax
    jz   cleanup_wsa
    mov  ebp, 1
cleanup_wsa:
    call qword ptr [rip+__imp_WSACleanup]
    test eax, eax
    jz   finish_status
    mov  ebp, 1
finish_status:
    mov  eax, dword ptr [rip+fatal] @atomic(.acquire)
    or   ebp, eax
    mov  ecx, ebp
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn

startup_failure_socket:
    mov  rcx, r12
    call qword ptr [rip+__imp_closesocket]
startup_failure_wsa:
    call qword ptr [rip+__imp_WSACleanup]
exit_failure_no_wsa:
    mov  ecx, 1
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn
fatal_exit:
    mov  ecx, 1
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn

console_handler: @callback_leaf @atomic_only
    mov  eax, 1
    xchg dword ptr [rip+shutdown], eax
    mov  eax, 1
    ret

worker_entry: @thread_entry @unwind(worker_entry_unwind)
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, WorkerFrame.size
    mov  rbx, rcx
    mov  rsi, INVALID_SOCKET

worker_gate: @reactive_frontier initialization_gate
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  worker_return
    mov  eax, dword ptr [rip+start_gate] @atomic(.acquire)
    test eax, eax
    jnz  accept_wait
    mov  ecx, 1
    call qword ptr [rip+__imp_Sleep]
    jmp  worker_gate

accept_wait: @placement [workerSlot := rbx]
             @reactive_frontier poll_listener @invariant owns_worker_slot
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  worker_return
    mov  rax, qword ptr [rip+listen_socket]
    mov  qword ptr [rbx+POLL_SOCKET], rax
    mov  word ptr [rbx+POLL_EVENTS], POLLRDNORM
    mov  rcx, rbx
    mov  edx, 1
    mov  r8d, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_WSAPoll]
    test eax, eax
    jle  accept_wait
    mov  rcx, qword ptr [rip+listen_socket]
    xor  edx, edx
    xor  r8d, r8d
    call qword ptr [rip+__imp_accept]
    cmp  rax, INVALID_SOCKET
    jne  accepted_connection
    call qword ptr [rip+__imp_WSAGetLastError]
    cmp  eax, WSAEWOULDBLOCK
    je   accept_wait
    mov  ecx, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_Sleep]
    jmp  accept_wait
accepted_connection:
    mov  rsi, rax
    mov  rcx, rsi
    mov  edx, FIONBIO
    lea  r8, [rip+nonblocking_one]
    call qword ptr [rip+__imp_ioctlsocket]
    test eax, eax
    jnz  accepted_mode_failure
    mov  rcx, rbx
    mov  rdx, rsi
    call h2_initialize_connection_state
    call qword ptr [rip+__imp_GetTickCount64]
    mov  qword ptr [rbx+LAST_PROGRESS], rax
    jmp  preface_loop

accepted_mode_failure:
    mov  rcx, rsi
    call qword ptr [rip+__imp_closesocket]
    mov  rsi, INVALID_SOCKET
    jmp  accept_wait

preface_loop: @frontier_or_measure(preface_input_or_24-preface_count)
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  connection_shutdown
    call receive_into_ring
    cmp  eax, IO_PENDING
    je   connection_schedule
    cmp  eax, IO_CLOSED
    je   connection_peer_close
    cmp  eax, IO_FAILED
    je   connection_io_error
    mov  rcx, rbx
    call h2_consume_preface
    cmp  eax, PARSE_NEED_MORE
    je   preface_loop
    cmp  eax, PARSE_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    lea  rdx, [rip+settings_frame]
    mov  r8d, $settingsFrame.length
    call h2_enqueue_control
    test eax, eax
    jnz  connection_internal_error
    jmp  connection_schedule

connection_schedule: @reactive_frontier socket_readiness_or_deadline
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jz   connection_deadlines
    mov  rcx, rbx
    mov  edx, NO_ERROR
    call h2_enqueue_goaway
    cmp  eax, GOAWAY_QUEUE_FAILURE
    je   connection_goaway_failure
connection_deadlines:
    call qword ptr [rip+__imp_GetTickCount64]
    mov  rdx, rax
    mov  rcx, rbx
    call h2_check_connection_deadline
    test eax, eax
    jnz  connection_shutdown
    mov  rcx, rbx
    call h2_cancel_expired_streams
    mov  rcx, rbx
    call h2_release_closed_streams
    mov  rcx, rbx
    call h2_should_close_drained
    test eax, eax
    jnz  connection_close
    mov  rcx, rbx
    call h2_has_sendable_outbound
    test eax, eax
    jnz  send_selected_frame
    mov  rcx, rbx
    call connection_poll
    test eax, POLL_READABLE
    jnz  receive_frames
    test eax, POLL_WRITABLE
    jnz  send_selected_frame
    test eax, POLL_FAILED
    jnz  connection_io_error
    jmp  connection_schedule

receive_frames:
    call receive_into_ring
    cmp  eax, IO_PENDING
    je   connection_schedule
    cmp  eax, IO_CLOSED
    je   connection_peer_close
    cmp  eax, IO_FAILED
    je   connection_io_error

receive_result_observation: @cancellation_observation connection_receive_result
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  connection_shutdown

frame_parse_loop: @measure buffered_complete_frames_or_need_input
    mov  rcx, rbx
    call h2_parse_frame_header
    cmp  eax, PARSE_NEED_MORE
    je   connection_schedule
    cmp  eax, PARSE_CONNECTION_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    call h2_require_initial_settings
    test eax, eax
    jnz  connection_protocol_error
    mov  rcx, rbx
    call h2_dispatch_frame
    cmp  eax, FRAME_DATA
    je   frame_data
    cmp  eax, FRAME_HEADERS
    je   frame_headers
    cmp  eax, FRAME_CONTINUATION
    je   frame_continuation
    cmp  eax, FRAME_SETTINGS
    je   frame_settings
    cmp  eax, FRAME_PING
    je   frame_ping
    cmp  eax, FRAME_GOAWAY
    je   frame_goaway
    cmp  eax, FRAME_RST_STREAM
    je   frame_rst_stream
    cmp  eax, FRAME_WINDOW_UPDATE
    je   frame_window_update
    cmp  eax, FRAME_PRIORITY
    je   frame_ignore_priority
    cmp  eax, FRAME_PUSH_PROMISE
    je   connection_protocol_error
    cmp  eax, FRAME_UNKNOWN
    je   frame_ignore_unknown
    jmp  connection_protocol_error

frame_headers:
    mov  rcx, rbx
    call h2_normalize_headers_payload
    test eax, eax
    jnz  connection_protocol_error
    mov  rcx, rbx
    call h2_transition_stream
    cmp  eax, TRANSITION_STREAM_ERROR
    je   stream_protocol_error
    cmp  eax, TRANSITION_CONNECTION_ERROR
    je   connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_END_HEADERS
    jz   begin_continuation
    jmp  decode_fields

begin_continuation:
    mov  rcx, rbx
    call h2_begin_header_block
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_continuation:
    mov  rcx, rbx
    call h2_append_continuation
    test eax, eax
    jnz  connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_END_HEADERS
    jz   frame_parse_loop

decode_fields:
    mov  rcx, rbx
    call hpack_decode_field_section
    cmp  eax, HPACK_CONNECTION_ERROR
    je   connection_compression_error
    mov  rcx, rbx
    call h2_validate_request_fields
    cmp  eax, REQUEST_OK
    je   enqueue_success
    cmp  eax, REQUEST_NOT_FOUND
    je   enqueue_not_found
    cmp  eax, REQUEST_STREAM_ERROR
    je   stream_protocol_error
    jmp  connection_protocol_error

enqueue_success:
    mov  rcx, rbx
    call h2_enqueue_response
    test eax, eax
    jnz  stream_refused
    jmp  frame_parse_loop

enqueue_not_found:
    mov  rcx, rbx
    call h2_enqueue_not_found
    test eax, eax
    jnz  stream_refused
    jmp  frame_parse_loop

frame_data:
    mov  rcx, rbx
    call h2_normalize_data_payload
    test eax, eax
    jnz  connection_protocol_error
    mov  rcx, rbx
    call h2_transition_stream
    cmp  eax, TRANSITION_STREAM_ERROR
    je   stream_protocol_error
    cmp  eax, TRANSITION_CONNECTION_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    call h2_debit_inbound_credit
    cmp  eax, FLOW_STREAM_ERROR
    je   stream_flow_error
    cmp  eax, FLOW_CONNECTION_ERROR
    je   connection_flow_error
    mov  rcx, rbx
    call h2_release_inbound_data
    test eax, eax
    jnz  connection_internal_error
    jmp  frame_parse_loop

frame_settings:
    mov  rcx, rbx
    call h2_apply_settings
    test eax, eax
    jnz  connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_ACK
    jnz  frame_parse_loop
    mov  rcx, rbx
    mov  edx, CONTROL_SETTINGS_ACK
    call h2_enqueue_control
    test eax, eax
    jnz  connection_internal_error
    jmp  frame_parse_loop

frame_ping:
    mov  rcx, rbx
    call h2_ack_ping
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_goaway:
    mov  rcx, rbx
    call h2_apply_goaway
    jmp  connection_draining

frame_rst_stream:
    mov  rcx, rbx
    call h2_apply_rst_stream
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_window_update:
    mov  rcx, rbx
    call h2_apply_window_update
    cmp  eax, FLOW_STREAM_ERROR
    je   stream_flow_error
    cmp  eax, FLOW_CONNECTION_ERROR
    je   connection_flow_error
    jmp  frame_parse_loop

frame_ignore_priority:
    mov  rcx, rbx
    call h2_validate_ignored_priority
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_ignore_unknown:
    mov  rcx, rbx
    call h2_consume_unknown_payload
    jmp  frame_parse_loop

send_selected_frame:
    mov  eax, dword ptr [rbx+TX_COMMITTED]
    cmp  eax, dword ptr [rbx+TX_LENGTH]
    jb   send_suffix_loop
    mov  rcx, rbx
    call h2_select_outbound
    test eax, eax
    jz   connection_schedule
    mov  rcx, rbx
    call h2_debit_outbound_credit
    cmp  eax, FLOW_BLOCKED
    je   connection_schedule
    cmp  eax, FLOW_ERROR
    je   connection_flow_error
    mov  rcx, rbx
    call h2_serialize_selected_frame
    test eax, eax
    jnz  connection_internal_error

send_suffix_loop: @frontier_or_measure(socket_writable_or_tx_length-tx_committed)
    mov  rcx, rbx
    call poll_connection_writable
    test eax, POLL_FAILED
    jnz  connection_io_error
    test eax, POLL_WRITABLE
    jz   connection_schedule
send_readiness_observation: @cancellation_observation writer_readiness_result
    mov  rcx, rbx
    call h2_observe_writer_cancellation
    cmp  eax, WRITER_CANCEL_CONNECTION_CLOSE
    je   connection_goaway_failure
    mov  rcx, rsi
    lea  rdx, [rbx+TX_BUFFER]
    add  rdx, qword ptr [rbx+TX_COMMITTED]
    mov  r8d, dword ptr [rbx+TX_LENGTH]
    sub  r8d, dword ptr [rbx+TX_COMMITTED]
    xor  r9d, r9d
    call qword ptr [rip+__imp_send]
    cmp  eax, SOCKET_ERROR
    jne  send_positive
    call qword ptr [rip+__imp_WSAGetLastError]
    cmp  eax, WSAEWOULDBLOCK
    je   connection_schedule
    jmp  connection_io_error
send_positive:
    test eax, eax
    jz   connection_io_error
    mov  rcx, rbx
    mov  edx, eax
    call h2_commit_sent_prefix
    cmp  dword ptr [rbx+TX_COMMITTED], dword ptr [rbx+TX_LENGTH]
    jne  send_suffix_loop
    jmp  connection_schedule

stream_refused:
    mov  edx, REFUSED_STREAM
    jmp  enqueue_stream_error
stream_protocol_error:
    mov  edx, PROTOCOL_ERROR
    jmp  enqueue_stream_error
stream_flow_error:
    mov  edx, FLOW_CONTROL_ERROR
enqueue_stream_error:
    mov  rcx, rbx
    call h2_enqueue_error
    jmp  frame_parse_loop

connection_compression_error:
    mov  edx, COMPRESSION_ERROR
    jmp  enqueue_connection_error
connection_flow_error:
    mov  edx, FLOW_CONTROL_ERROR
    jmp  enqueue_connection_error
connection_protocol_error:
    mov  edx, PROTOCOL_ERROR
    jmp  enqueue_connection_error
connection_internal_error:
    mov  edx, INTERNAL_ERROR
enqueue_connection_error:
    mov  rcx, rbx
    call h2_enqueue_error
    jmp  connection_draining

connection_shutdown:
    mov  rcx, rbx
    mov  edx, NO_ERROR
    call h2_enqueue_goaway
    cmp  eax, GOAWAY_QUEUE_FAILURE
    je   connection_goaway_failure
connection_draining: @frontier_or_measure(control_queue_or_drain_deadline)
    jmp  connection_schedule

connection_goaway_failure:
    mov  rcx, rbx
    call h2_mark_exact_teardown_suffix_disposition
    jmp  connection_close

connection_peer_close:
connection_io_error:
connection_close: @discharge exact_socket_and_connection_custody(rsi,rbx)
    mov  rcx, rsi
    call qword ptr [rip+__imp_closesocket]
    mov  rsi, INVALID_SOCKET
    mov  rcx, rbx
    call h2_release_connection_state
connection_closed_boundary: @cancellation_point exact_connection_custody_discharged
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jz   accept_wait

worker_return: @return_worker_loans
    xor  eax, eax
    add  rsp, 56
    pop  r15
    pop  r14
    pop  r13
    pop  r12
    pop  rdi
    pop  rsi
    pop  rbp
    pop  rbx
    ret
}

end Grass.Spikes.WebServer
