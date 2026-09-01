# Initial references and design lineage

This is the seed register for design review. Implementation will replace bare
entries with machine-validated citation records as specified by
[VALIDATION.md](VALIDATION.md). Retrieval date for external links below is
2026-08-31.

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
- Microsoft, `ExitProcess`:
  https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess
- Microsoft, Windows 10 Home/Pro lifecycle (context for the chosen API baseline,
  not a deployment requirement):
  https://learn.microsoft.com/en-us/lifecycle/products/windows-10-home-and-pro

### Arena example

- Protocol Buffers, *C++ Arena Allocation Guide*:
  https://protobuf.dev/reference/cpp/arenas/

The Protobuf document motivates validation cases; Grass's arena semantics is its
own allocator abstraction and must not attribute guarantees beyond a selected
allocator profile.

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
