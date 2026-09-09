# AMD APM source migration, 2026-09-09

The active x86 profile now pins combined APM publication 40332 revision 4.10.
This repairs the dead source locator for the existing nine subjects. Eight AMD
anchors are confirmed; the stronger misplaced-REX claim remains unconfirmed.
No instruction population or citation-covered declaration population is added.
The eight pending common bases and one weaker-common basis remain unchanged.

## Retrieval and identity

AMD's [official publication page](https://docs.amd.com/v/u/en-US/40332_4.10_APM_Vol1-5_PUB)
identifies revision 4.10 and a posting date of July 29, 2026. Its linked
[combined PDF](https://docs.amd.com/api/khub/documents/SLs_hsYJwsu9rrIjE0rGxA/content)
was downloaded and inspected. The cover says July 2026; component covers and
headers identify Volume 1 as 24592 revision 3.25 (May 2026), and Volume 3 as
24594 revision 3.38 (July 2026). These are separate revision identities, not an
assumption that old and new editions are interchangeable.

The retrieved file has 4,342 PDF pages and 24,737,536 bytes. Its SHA-256 is
`b95c6db015807bf38daed8cc0c294c42e479c42c62cf25655661754d21f591db`.
This fingerprint identifies inspected bytes; it proves neither semantics nor
publisher authority. Text extraction was cross-checked against rendered covers,
register diagrams, encoding tables and instruction pages. The source remains
`referenceOnly`. No manual or extracted manual text is distributed in this repo.

The [historical 4.09 route](https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB)
and its indexed PDF endpoint returned 404. Search metadata still advertising
4.09 does not constitute retrieval. `amd64Apm409` retains its old identity and
dead status; this does not assert an exhaustive search of every possible archive.
`Vendor.document .amd` selects the distinct `amd64Apm410` record.

The source-liveness tool checks a title fragment in PDF metadata at the direct
download endpoint. That checks availability, not revision or anchor accuracy.
Cover, component revision, prose and table inspection supply separate evidence.

## Existing subject mapping

Section numbers in the old column are the former 4.09 locators, not newly
verified statements about that unavailable edition. Printed pages below refer
to the component volume. PDF pages are one-based in the combined 4.10 file.

| Subject suffix | Old locator | Inspected replacement | Printed pages | PDF pages |
| --- | --- | --- | --- | --- |
| `writeBack` | Vol. 1 §3.1 | Vol. 1 §3.1.2, Figures 3-3/3-4 | 26–28 | 66–68 |
| `Rex.toByte` | Vol. 3 §1.2.7 | §1.2.7, Figure 1-3; §1.4.4, Table 1-15 | 14–16, 23–24 | 1329–1331, 1338–1339 |
| `ByteReg.Encodable` | Vol. 3 §1.2.7 | §1.8.1; Table 1-14; Vol. 1 register figures | 26, 22 | 1341, 1337 |
| `ModRm.toByte` | Vol. 3 §1.4 | §1.4.1, Figure 1-4, Table 1-10 | 17–18 | 1332–1333 |
| `Sib.toByte` | Vol. 3 §1.4 | §1.4.2, Figure 1-5, Table 1-11; Table 1-10 note 3 | 19, 18 | 1334, 1333 |
| `decodeMem.ripRelative` | Vol. 3 §1.7 | §1.7.1–1.7.3, Table 1-16 | 24–26 | 1339–1341 |
| `decodeMem.sibEscape` | Vol. 3 §1.4 | §1.8.2, Table 1-17 first row | 26–27 | 1341–1342 |
| `decodeMem.noIndex` | Vol. 3 §1.4 | §1.8.2, Table 1-17; Table 1-12 note 1 | 27, 20 | 1342, 1335 |
| `decodeMem.noBase` | Vol. 3 §1.4 | §1.8.2, Table 1-17; Table 1-13; §1.5; Table 1-16 | 27, 20, 24–25 | 1342, 1335, 1339–1340 |

All subject names retain the `Grass.ISA.X86.` prefix. Each citation stores its
primary printed page and a locator with the supporting cross-references.

Register-write exceptions were checked separately in Volume 3: BSF/BSR at
printed 123/124 (PDF 1438/1439), NOP at 272 (PDF 1587), and XCHG at 370
(PDF 1685). AMD documents unchanged destination for zero-source BSF/BSR. That
does not strengthen Intel's weaker undefined guarantee in the common model.
NOP's special handling of opcode 90 does not apply to two-byte ModRM XCHG.
This migration adds no BSF/BSR semantics or hardware-derived source authority.

## Remaining scope and obligations

The REX source specifies immediate adjacency to opcode/escape and the bit
layout. It does not establish the rule's stronger assertion that a REX followed
by a legacy prefix is ignored with all its effects removed. That whole AMD
anchor remains unconfirmed. Canonical `InsnEncoding.toBytes` has no legacy
prefix field, and `decodeInsn` rejects those prefixes even after REX. Existing
Hello emission therefore does not need this unresolved behavior. Extending the
decoder to legacy prefixes requires resolving it first.

RIP-relative and no-base statements now explicitly use default 64-bit address
size. Section 1.7.3 describes truncation with an address-size override, outside
the existing decoder's scope. The no-base displacement-only statement also
requires an absent index; a scaled index is not an absolute constant address.
The decoder's rejection of 67 prevents accidental admission of that extension.

The active release-blocker list becomes empty, while the historical dead record
remains available. `CitationsChecked` is still false because the REX anchor is
unconfirmed. Retrieval does not supply timing facts: the existing impossibility
theorem for an unavailable AMD source now takes unavailability as an explicit
premise instead of baking the old dead pin into its proof.

`Tests/ISA/X86/AmdSourceMigration.lean` checks unchanged subject names, exact
section/page mapping, distinct revisions, reference-only policy, the remaining
unconfirmed anchor, and failed citation checking. Negative controls demonstrate
that inventing a verified old record cannot match the registered document,
clearing confirmation prevents full checking, and legacy-prefix inputs are
rejected. These are checks of recorded policy and supported scope; they cannot
prove a manual says what a locator claims.
