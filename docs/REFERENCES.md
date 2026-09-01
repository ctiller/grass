# Initial references and design lineage

This is the seed register for design review. Implementation will replace bare
entries with machine-validated citation records as specified by
[VALIDATION.md](VALIDATION.md). Retrieval date for external links below is
2026-09-01.

## Authoritative external sources

### x86-64

- Intel, *Intel 64 and IA-32 Architectures Software Developer's Manuals*,
  current collection and revision history:
  https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
- AMD, *AMD64 Architecture Programmer's Manual, Volumes 1-5*, publication
  40332, revision 4.09 at corpus creation:
  https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB

The common x86 profile requires anchored citations to both relevant instruction
and system/memory sections. These collection links are discovery roots, not
sufficient declaration-level anchors.

### Win32 x64 and PE/COFF

- Microsoft, *x64 calling convention*:
  https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention
- Microsoft, *PE Format* (PE/COFF structure, imports, relocations, exception
  data, and libraries):
  https://learn.microsoft.com/en-us/windows/win32/debug/pe-format
- Microsoft, `GetStdHandle`:
  https://learn.microsoft.com/en-us/windows/console/getstdhandle
- Microsoft, `WriteFile`:
  https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile
- Microsoft, `ReadFile`:
  https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-readfile
- Microsoft, `GetProcessHeap`:
  https://learn.microsoft.com/en-us/windows/win32/api/heapapi/nf-heapapi-getprocessheap
- Microsoft, `HeapAlloc`:
  https://learn.microsoft.com/en-us/windows/win32/api/heapapi/nf-heapapi-heapalloc
- Microsoft, `HeapReAlloc`:
  https://learn.microsoft.com/en-us/windows/win32/api/heapapi/nf-heapapi-heaprealloc
- Microsoft, `ExitProcess`:
  https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess
- Microsoft, `/HIGHENTROPYVA` support for 64-bit ASLR:
  https://learn.microsoft.com/en-us/cpp/build/reference/highentropyva-support-64-bit-aslr?view=msvc-170
- Microsoft, Windows 10 Home/Pro lifecycle (context for the chosen API baseline,
  not a deployment requirement):
  https://learn.microsoft.com/en-us/lifecycle/products/windows-10-home-and-pro

### Arena example

- Protocol Buffers, *C++ Arena Allocation Guide*:
  https://protobuf.dev/reference/cpp/arenas/

The Protobuf document motivates validation cases; Grass's arena semantics is its
own allocator abstraction and must not attribute guarantees beyond a selected
allocator profile.

### Hosted and bare-metal terminal status

- Linux kernel man-pages, `exit(3)`/`wait(2)` status behavior:
  https://www.kernel.org/pub/linux/docs/man-pages/book/man-pages-6.13.pdf
- Arm, *Debugger usage*, semihosting overview:
  https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/Learn%20the%20Architecture/Debugger%20usage.pdf
- QEMU, `isa-debug-exit` device implementation (guest value to host shutdown
  code transformation):
  https://github.com/qemu/qemu/blob/master/hw/misc/debugexit.c

These establish that a numeric terminal status can have non-process physical
realizations. Each platform profile still needs a precise representation and
normalization theorem; a target with no observable status channel cannot realize
a specification that demands one.

### Standard-library design inputs

- Rust, `std::vec::Vec` guarantees (contiguous initialized prefix, spare
  capacity, length/capacity, allocation and invalidation behavior):
  https://doc.rust-lang.org/std/vec/struct.Vec.html
- C++ working draft, container and allocator-aware container requirements:
  https://eel.is/c++draft/container.requirements and
  https://eel.is/c++draft/container.alloc.reqmts
- Haskell `vector` package documentation, algebraic and traversal operations:
  https://hackage.haskell.org/package/vector/docs/

These are design inputs. Grass states and proves its own exact contracts rather
than inheriting undocumented implementation behavior.

### Proof-construction precedents

- Bond et al., *Vale: Verifying High-Performance Cryptographic Assembly Code*:
  https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/Vale.pdf
- Almeida et al., *Jasmin: High-Assurance and High-Speed Cryptography*:
  https://acmccs.github.io/papers/p1807-almeidaA.pdf
- Stewart et al., *Compositional CompCert*:
  https://www.cs.princeton.edu/~appel/papers/compcomp.pdf
- CompCert, separate-compilation correctness theorem:
  https://compcert.org/doc/html/compcert.driver.Compiler.html
- Iris project and mechanized concurrent-separation-logic resources:
  https://iris-project.org/
- Iris lecture notes, including authoritative resource algebras:
  https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf
- Lee and Parks, *Dataflow Process Networks*:
  https://ptolemy.berkeley.edu/publications/papers/95/processNets/

These sources establish relevant proof shapes, not Grass correctness. The exact
Grass claims, required inputs, acceptance fixtures, and fallbacks are in
[PROOF_FEASIBILITY.md](PROOF_FEASIBILITY.md).

### Portable monotonic time and Win32 realization

- Microsoft, `QueryPerformanceCounter`:
  https://learn.microsoft.com/en-us/windows/win32/api/profileapi/nf-profileapi-queryperformancecounter
- Microsoft, `QueryPerformanceFrequency`:
  https://learn.microsoft.com/en-us/windows/win32/api/profileapi/nf-profileapi-queryperformancefrequency

The selected Cube provider must model their complete return/value behavior and
prove the conversion to portable `MonotonicInstant`; the documentation is an
external contract anchor, not a theorem that physical clocks conform.

### HTTP/2 and HPACK

- IETF RFC 9113, *HTTP/2*: https://www.rfc-editor.org/rfc/rfc9113.html
- IETF RFC 7541, *HPACK: Header Compression for HTTP/2*:
  https://www.rfc-editor.org/rfc/rfc7541.html

Spike 4's cleartext prior-knowledge profile derives frame parsing, stream-state
legality, connection and stream flow-control accounting, settings, error scope,
and field-section requirements from RFC 9113. Its HPACK state, integer/string
decoding, static/dynamic tables, eviction accounting, and Huffman validation are
anchored to RFC 7541. The RFCs define the external protocol contract; Grass
still owes parsers, writers, round trips, model refinements, exact assembly, and
boundary probes for those contracts.

The declaration anchors are RFC 9113 sections 3.3–3.4 (connection preface and
cleartext prior knowledge), 4 (frames/field sections), 5 (streams and flow
control), 6 (individual frame types), 7 (errors), and 8 (HTTP semantics), plus
RFC 7541 sections 2–4 (context and dynamic table), 5 (representations, integers,
strings, and Huffman coding), 6 (examples), and appendices A–C (static and
Huffman tables). Review must refine these section anchors to individual model
declarations; a whole-RFC citation is not sufficient implementation metadata.

### Spike 4 Win32 network and concurrency providers

- Microsoft, `WSAStartup`, `WSASocketW`, `bind`, `listen`, `ioctlsocket`,
  `WSAPoll`, `accept`, `recv`, `send`, `WSAGetLastError`, `closesocket`, and
  `WSACleanup`:
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsastartup,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsasocketw,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-bind,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-listen,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-ioctlsocket,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsapoll,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-accept,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-recv,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-send,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsagetlasterror,
  https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-closesocket,
  and https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsacleanup.
- Microsoft, `CreateThread`, `ResumeThread`, `WaitForSingleObject`, `CloseHandle`,
  `Sleep`, `SetConsoleCtrlHandler`, and `GetTickCount64`:
  https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createthread,
  https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-resumethread,
  https://learn.microsoft.com/en-us/windows/win32/api/synchapi/nf-synchapi-waitforsingleobject,
  https://learn.microsoft.com/en-us/windows/win32/api/handleapi/nf-handleapi-closehandle,
  https://learn.microsoft.com/en-us/windows/win32/api/synchapi/nf-synchapi-sleep,
  https://learn.microsoft.com/en-us/windows/console/setconsolectrlhandler,
  and https://learn.microsoft.com/en-us/windows/win32/api/sysinfoapi/nf-sysinfoapi-gettickcount64.

Each imported function receives its own declaration-level citation record,
modeled success/failure/result cases, differential probes, and reviewed version
applicability. Grouping links here does not permit one generic “Winsock” model
to stand in for those separate contracts.

### Erlang/OTP process semantics

- Erlang/OTP reference manual, processes and signals:
  https://www.erlang.org/doc/system/ref_man_processes.html
- Erlang/OTP design principles, supervisor behaviour:
  https://www.erlang.org/doc/system/sup_princ.html
- Erlang/OTP `gen_server` behaviour:
  https://www.erlang.org/doc/system/gen_server_concepts.html
- Erlang/OTP `gen_statem` behaviour:
  https://www.erlang.org/doc/system/statem.html

Grass mines these as operational precedents for per-sender signal order,
mailbox selection, correlated request/reply, links versus monitors, restart
strategies and intensity, shutdown ordering, postponed events, state-entry
actions, and timeout races. It does not inherit BEAM scheduling, unbounded
mailboxes, distributed-delivery guarantees, garbage collection, or “let it
crash” as proof principles. The exact adopted and rejected semantics are stated
in [PROCESS.md](PROCESS.md).

## Internal predecessor material

These documents are design lineage, not external semantic authority. Citations
use immutable repository revisions and repository-relative paths:

- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/MEMORY_MODEL.md`
  — unique loan identities, event vocabulary, ownership and concurrency design.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/MEMORY_HOOK.md`
  — sealed instruction memory-access chokepoint and fault reporting.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/MEMORY_PROVENANCE.md`
  — hierarchical provenance and allocator sketches.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/OBLIGATIONS_AND_CAUSALITY.md`
  — obligation/event orientation.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/READ_BINDER_CONTRACT.md`
  — universal dependent read-result handling.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/SYSTEM_EFFECTS.md`
  — high-level effect modelling and observation projections.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/ABI_CONTEXT.md`
  — nominal ABI contexts and dependent boundary outcomes.
- `gasm@a86d7e092833e6151ac1f2903af02251553026bd:docs/REVIEW.md`
  — citation, universal-proof, connection-theorem, and ratchet discipline.
- `wsc@7149a65b90bfe452fcecf605e88e852788d72f66:docs/ARCHITECTURE.md` and
  sibling review/testing documents
  — existential instruction modelling, citation coverage, and differential tests.

Grass deliberately does not inherit their module interfaces or compatibility
requirements. Where this corpus differs, the Grass normative owner governs.
