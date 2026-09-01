# Multithreaded in-memory cleartext HTTP/2 server acceptance checklist

This checklist owns the acceptance surface for Spike 4. The detailed proposed
proof is [SPIKE_4.md](SPIKE_4.md). The spike is a design fixture, not an
implemented Grass library. The keyed, implementation-facing trace of every
captured demand is [HTTP2_CONSTRAINTS.md](HTTP2_CONSTRAINTS.md); that inventory
is an audit projection of the precious spec, not parallel semantic authority.

## Portable behavior and protocol profile

- [ ] The precious specification names a cleartext HTTP/2 prior-knowledge
  server, immutable route table, connection and stream observations, scoped
  errors, graceful shutdown, and conditional progress without naming Windows,
  x86, PE, sockets, OS threads, polling, or buffer layouts.
- [ ] `GET /` produces a `200` field section and exactly `Grass web server\n`;
  an unknown route produces `404` and an empty body. Other methods are rejected
  at stream scope unless RFC 9113 requires connection scope.
- [ ] The peer must send the client connection preface. The server emits its
  initial SETTINGS and applies peer SETTINGS only after complete validation,
  then emits an ACK.
- [ ] The claimed profile has an explicit transition for DATA, HEADERS,
  CONTINUATION, SETTINGS, PING, GOAWAY, RST_STREAM, WINDOW_UPDATE, PRIORITY,
  PUSH_PROMISE, and unknown extension frames.
- [ ] Deprecated priority signals are length/stream-state validated and then
  ignored. Unknown extension frames are consumed and ignored. PUSH_PROMISE is a
  connection error because server push is disabled.
- [ ] Stream-state legality covers idle, open, half-closed-local,
  half-closed-remote, and closed, including frames received on idle or closed
  streams and monotonically increasing client stream identifiers.
- [ ] Every malformed condition is assigned the RFC 9113 error code and exact
  connection or stream scope. A stream error cannot corrupt sibling streams or
  HPACK connection state; a connection error stops new streams and leads to
  GOAWAY/close.
- [ ] There is no HTTP/1.1 upgrade path, TLS, push, trailers, dynamic content,
  logging, or deployment-hardening claim.

## HPACK and framing

- [ ] The frame parser handles all 24-bit lengths, flags, reserved stream bit,
  partial headers, partial payloads, multiple frames per receive, and configured
  maximum frame size.
- [ ] `Frame.parse (Frame.write f) = .ok f` holds for every admissible frame.
  The parser-conformance theorem says every success consumes exactly one valid
  encoded prefix and returns its exact suffix; it never merely reports that
  tests passed.
- [ ] RFC 7541 integer and string encodings have writer round trips. HPACK
  decoding covers indexed fields, literals with incremental indexing, literals
  without indexing, never-indexed literals, table-size updates, and dynamic
  eviction by the RFC size formula.
- [ ] HPACK Huffman decoding accepts exactly valid code sequences, enforces EOS
  and padding rules, and rejects overlong/invalid suffixes. The generated table
  is exact static source data tied to the model.
- [ ] Header-list size is charged over decoded fields. Dynamic-table and header-
  list bounds are independent. CONTINUATION fragments are bounded and no other
  frame can interleave within a field-section block.
- [ ] HPACK state belongs to the connection and follows connection frame order,
  even when decoded field sections are delivered to independently progressing
  stream processes.

## Multiplexing, byte flow, and backpressure

- [ ] A logical stream process exists for each admitted client stream. The
  selected four-worker topology is replaceable and does not identify one OS
  thread per stream.
- [ ] Positive `recv` results append exact bytes to a bounded byte channel;
  partial frame boundaries are invisible to protocol semantics. Pending,
  readiness, orderly close, failure, cancellation, and positive results remain
  distinct universally quantified cases.
- [ ] Positive `send` results commit exactly the returned prefix. The unsent
  suffix remains owned and byte-identical; frames cannot interleave on the wire.
- [ ] DATA admission debits both the connection and stream receive windows.
  DATA emission debits both peer-advertised send windows. WINDOW_UPDATE checks
  zero increments and 31-bit overflow at the correct scope.
- [ ] Connection and stream credits are conserved. Exhausted credit prevents
  DATA admission/emission and creates a genuine environment frontier; control
  frames remain schedulable without consuming DATA credit.
- [ ] Bounded control and DATA queues define scheduler capacity. The fair
  connection writer preserves frame atomicity and per-stream byte order while
  allowing progress by unrelated streams.
- [ ] A stuck stream finishes the current frame and resets without disturbing
  siblings when the connection remains writable and scheduled. Otherwise the
  bounded result is exact connection teardown with suffix disposition; HPACK or
  connection failure still cancels all descendants.

## Resource and ownership proof

- [ ] The selected resource value bounds active connections, streams per
  connection, frame and continuation bytes, decoded header-list bytes, HPACK
  dynamic table, receive/transmit storage, control-frame slots, DATA queue
  bytes, sockets, thread handles, and deadlines.
- [ ] Generic behavior derives HPACK/header/window/admission limits from the
  passed resource value. Concrete layouts/macros/bounds use the retained
  `spec.resourceSemantics`; an equality ties that capture to the selected
  construction, and no global policy is consulted by the generic family.
- [ ] Startup owns all fixed storage before publishing `.ready`. Any pre-ready
  startup/worker creation failure serves and emits no HTTP bytes, discharges
  acquired resources, and exits nonzero.
- [ ] Partial worker creation resumes the suspended created prefix only through
  a failure gate, then joins/closes it without publishing readiness. Fixtures
  cover every creation index and every `ResumeThread` failure index; the latter
  uses its declared failed-adoption/no-return boundary rather than hanging.
- [ ] After `.ready`, no allocation API is imported or invoked. Admission and
  flow-control credits make exhaustion a refused/deferred protocol action, not
  an allocation failure.
- [ ] Per-stream, per-connection, and whole-server bounds include descendants,
  queues, HPACK state, byte-channel storage, escrow, stack/layout charges,
  sockets, and Windows handles. Bounds are stated on independent resource axes.
- [ ] The fixture exports a whole-server resident-byte bound and one exact root
  resource equation over the mandatory concrete-axis family, whose selected
  axis keys are injective.
- [ ] Immutable route bytes have one owner and disjoint shared read loans. Each
  mutable connection/stream slot has one generation-indexed owner. Numeric
  socket or stream-id reuse cannot alias an old cancellation action.
- [ ] Shutdown publication is atomic. Every accepted socket, worker handle,
  Winsock session, callback registration, queued suffix, and flow credit has one
  explicit terminal disposition.

## Process realization and progress

- [ ] The precious `SpecProcess` graph names listener, connection, and stream
  roles and their logical protocols. It does not name physical worker count,
  polling strategy, slot assignment, or Win32 calls.
- [ ] The replaceable realization adds listener, fixed workers, connection
  parser, connection-local HPACK decoder, stream children, serialized writer,
  API-call children, cancellation, and supervision.
- [ ] Hoare-style channel contracts transfer bytes, decoded fields, frames,
  credits, response requests, cancellation, custody, and obligations with local
  pre/postconditions.
- [ ] No-shutdown service is intentionally infinite. Every internal loop either
  decreases a finite measure or crosses socket readiness, scheduler, clock, or
  shutdown frontiers.
- [ ] Under scheduler fairness, advancing monotonic time, and responsive APIs,
  each admitted stream completes, is reset, or reaches its cancellation
  deadline. Shutdown eventually sends GOAWAY, settles/cancels streams, closes
  connections, joins workers, and terminates.

## Optional compositional cancellation

- [ ] `ProcessCorrect` has no cancellation field. Plain serial/leaf processes
  receive only the weakest uncancellable summary and incur no new proof burden.
- [ ] The server's stronger `CancellationSummary` is calculated from bounded
  uncancellable segments and calls, explicit observation points, and
  sequence/choice/loop/parallel/supervisor combinators.
- [ ] A summary exports a `ProcessTerminationContract` only after its progress
  and disposition premises suffice. The root summary does so and converts via
  `toSupervisedTerminationFacet` using an explicit supervisor-compatibility
  proof; a plain or forever-blocking uncancellable summary exports `none`.
- [ ] Every continuing HPACK decode loop crosses a point between bounded slices.
  The proof names distinct committed and private working decoder states. No
  cancellation is legal during mutation; cancellation returns the old committed
  state or a separately proved committed successor after finishing the slice.
- [ ] Per-stream cancellation never addresses the connection HPACK decoder. An
  already accepted field block advances shared decoder state in connection
  order even if its decoded fields are later discarded for a reset stream.
- [ ] This nonblocking Win32 plan has no provider interrupt operation.
  `WSAPoll`, `Sleep`, `accept`, `recv`, and `send` are bounded uncancellable
  calls followed by displayed cancellation-observation blocks. A
  forever-blocking masked provider call cannot be promoted to a bounded claim.
- [ ] A positive partial send enters a bounded uncancellable prefix-commit
  segment. Cancellation becomes legal only after committed bytes and exact
  suffix custody are restored. Stream cancellation finishes that frame before
  RST_STREAM; only connection close may dispose a mid-frame suffix.
- [ ] A stream blocked on either flow-control window has an immediate stream
  cancellation observation point. Its result is frame-finish-then-RST under
  writability/survival/fairness, or exact connection teardown otherwise.
- [ ] Connection cancellation publishes GOAWAY with the exact admitted prefix,
  drains/resets children, settles writer/HPACK custody, and closes only at the
  connection safe boundary. Root shutdown composes root service policy with the
  worker family and does not count connection policy twice.
- [ ] `goawayPublished` makes shutdown idempotent: one successful publication
  consumes one control slot and freezes the prefix; repeated observations
  consume no slot, and queue failure takes exact teardown. Drain either makes
  progress under named premises or reaches its deadline/escalation frontier.
- [ ] Normal and failed terminal boundaries have distinct exhaustive custody,
  resource, observation, and obligation dispositions. A supervisor cannot
  invent a forced safe point while a worker owns a live socket or child state.
- [ ] Sequence reassociation, inlining, macro expansion, and process flattening
  preserve the calculated cancellation summary.

## First-class assembly and exact artifact

- [ ] The comment-free fixture shows the real entry/setup, worker gate,
  accept/preface loop, partial receive channel, frame dispatch, HPACK/CONTINUATION
  path, flow-credit debits, fair output selection, partial-send suffix, scoped
  errors, per-stream cancellation, GOAWAY drain, and cleanup.
- [ ] Large algorithms are local typed fragment constructors first and may move
  into the verified standard library later. Every selected helper retains its
  assembly algorithm, exact raw expansion, references, citations, and machine
  certificate in the hierarchical closure. Macro-shaped call names are only
  transparent adapters; an absent standard-library module is never the body.
- [ ] A total cancellation CFG map distinguishes bounded calls, safe states,
  real observation/control-transfer blocks, request publishers, faults and
  terminal boundaries. Expanded macro
  interiors map to the same summary; callbacks and faults cannot counterfeit a
  safe point.
- [ ] An author may replace any macro with arbitrary custom assembly and prove
  the same local before/after contract. No opaque compiler output is privileged.
- [ ] Static data, imports, relocations, unwind records, section permissions,
  ASLR, entry point, PE writer/parser laws, loaded instruction decoding, and all
  admissible loads connect the authored source to `emitProgram serverVerified`.

## Adversarial fixtures

- [ ] Test every split of the client preface, 9-byte frame header, payload,
  HPACK integer, Huffman code, and CONTINUATION sequence across receives.
- [ ] Test SETTINGS ACK misuse, invalid setting values, window overflow/zero,
  DATA without credit, interleaved CONTINUATION, stream-id reuse, frames on each
  stream state, invalid padding, invalid Huffman EOS/padding, dynamic-table
  eviction, unknown frames, ignored PRIORITY, forbidden PUSH_PROMISE, and scoped
  stream/connection errors.
- [ ] Test partial sends at every byte, blocked connection versus stream window,
  one stuck stream among progressing siblings, shutdown at every setup/service
  point, callback at every instruction boundary, peer close, poll/recv/send
  failure, worker starvation, and infinite service.
- [ ] Positive fixtures prove conditional addressed RST_STREAM or exact
  teardown, idempotent GOAWAY/drain, cancellation
  while flow blocked, interrupted readiness, HPACK slice cancellation, exact
  partial-send suffix custody, and normal/failed terminal settlement.
- [ ] Negative fixtures reject cancellation mid-HPACK mutation, after `send`
  returns but before prefix commit, at arbitrary CFG instructions, forced worker
  stop with live socket custody, and a bounded claim over a forever-blocking
  uncancellable call.
- [ ] Mutation reports separately cover route/body changes, protocol-profile or
  resource-bound changes, macro implementation changes, worker-topology changes,
  platform/provider changes, and PE serialization changes.
