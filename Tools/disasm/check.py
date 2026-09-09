"""Exercise the real CLI/exporter, including byte retention on refused input.

This is runtime validation. Grass.Disasm.Linear owns the universal byte laws.
Run after lake build grass-disasm grass-disasm-hello Tests.Disasm.Linear.
"""
import json
import argparse
import os
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
BIN = ROOT / ".lake" / "build" / "bin"
SUFFIX = ".exe" if os.name == "nt" else ""
CLI = BIN / ("grass-disasm" + SUFFIX)
EXPORT = BIN / ("grass-disasm-hello" + SUFFIX)


def invoke(*args, expected=0):
    result = subprocess.run([str(CLI), *map(str, args)], capture_output=True, text=True)
    assert result.returncode == expected, (args, result.returncode, result.stderr, result.stdout)
    return json.loads(result.stdout)


def reconstruct(listing):
    return bytes.fromhex("".join(row["bytes"] for row in listing["rows"]) + listing["remainingBytes"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiled-c", type=pathlib.Path,
                        help="validate real artifacts emitted by build-c.ps1")
    options = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="disasm-", dir=ROOT / ".lake") as directory:
        work = pathlib.Path(directory)
        raw = work / "input.bin"
        cases = [
            ("534883ec20", 4096, 0, 2),
            ("530fff53", 4096, 3, 1),
            ("4883", 4096, 3, 0),
            ("53", 2**64 - 1, 3, 0),
            ("", 4096, 0, 0),
        ]
        for encoded, base, code, rows in cases:
            data = bytes.fromhex(encoded)
            raw.write_bytes(data)
            report = invoke("raw", raw, base, expected=code)
            listing = report["report"]
            assert reconstruct(listing) == data
            assert len(listing["rows"]) == rows
            assert report["assurance"] == "decode evidence only; memory safety unresolved"
            cursor = base
            for row in listing["rows"]:
                assert row["address"] == cursor
                assert row["fileOffset"] == cursor - base
                cursor += len(bytes.fromhex(row["bytes"]))

        image = work / "hello.exe"
        payload = work / "payload.bin"
        payload.write_bytes(b"Hello, World!\r\n")
        exported = subprocess.run(
            [str(EXPORT), str(ROOT / "Spikes/1_Hello_World/Program.lean"), str(payload), str(image)],
            capture_output=True, text=True,
        )
        assert exported.returncode == 0, exported.stderr
        assert "no end-to-end safety certificate" in exported.stdout
        assert "Surrounding source declarations are not elaborated" in exported.stdout
        report = invoke("pe", image)
        data = image.read_bytes()
        decoded = 0
        for section in report["report"]["sections"]:
            if not section["executable"]:
                continue
            listing = section["listing"]
            start = section["fileOffset"]
            size = listing["byteLength"]
            assert reconstruct(listing) == data[start:start + size]
            assert listing["stop"] is None
            decoded += len(listing["rows"])
        assert decoded > 0

        # Truncation and unrelated bytes cannot appear as accepted containers.
        for contents in (data[:30], b"not a PE image"):
            raw.write_bytes(contents)
            refused = invoke("pe", raw, expected=2)
            assert refused["report"]["parse"] != "accepted-bounded-imported-container"

        # Explicit data inputs must affect the artifact; the exporter must not
        # silently replace them with a hardcoded Hello string.
        payload.write_bytes(b"X")
        changed = work / "changed.exe"
        subprocess.run([str(EXPORT), str(ROOT / "Spikes/1_Hello_World/Program.lean"),
                        str(payload), str(changed)], check=True, capture_output=True)
        assert changed.read_bytes() != data

        # The declared contract extracts assembly, not surrounding Lean values.
        # This explicit control prevents a future whole-source assurance claim.
        source = (ROOT / "Spikes/1_Hello_World/Program.lean").read_text(encoding="utf-8")
        declaration = "def payload : ByteArray := projection.encodeLine message"
        assert declaration in source
        mutated_source = work / "ChangedPayload.lean"
        mutated_source.write_text(source.replace(declaration,
                                  'def payload : ByteArray := Text.utf8 "X"'), encoding="utf-8")
        same_explicit_data = work / "same-explicit-data.exe"
        projected = subprocess.run([str(EXPORT), str(mutated_source), str(payload),
                                    str(same_explicit_data)], check=True, capture_output=True, text=True)
        assert same_explicit_data.read_bytes() == changed.read_bytes()
        assert "Surrounding source declarations are not elaborated" in projected.stdout

        # Mutate actual artifact offsets; no writer-normalization is involved.
        nt = report["report"]["ntHeaderOffset"]
        mutations = [(60, (63).to_bytes(4, "little")),
                     (60, (len(data) + 4096).to_bytes(4, "little")),
                     (nt, b"PX\0\0"),
                     (nt + 20, (0).to_bytes(2, "little")),
                     (nt + 24 + 60, (0).to_bytes(4, "little"))]
        for offset, replacement in mutations:
            mutant = bytearray(data)
            mutant[offset:offset + len(replacement)] = replacement
            raw.write_bytes(mutant)
            invoke("pe", raw, expected=2)

        if options.compiled_c:
            for name, displacement in (("store_safe", "04"), ("store_oob", "08")):
                for extension in (".exe", ".dll"):
                    binary = options.compiled_c / (name + extension)
                    evidence = invoke("pe", binary, expected=3)["report"]
                    original = binary.read_bytes()
                    assert len(bytes.fromhex(evidence["dosStub"])) == evidence["ntHeaderOffset"] - 64
                    code = next(item for item in evidence["sections"] if item["executable"])
                    if extension == ".exe":
                        assert code["rva"] == evidence["entryRva"]
                    listing = code["listing"]
                    assert listing["rows"][0]["bytes"] == "c741" + displacement + "2a000000"
                    # RET is currently outside the shared decoder; preserve it.
                    assert listing["remainingBytes"] == "c3"
                    assert reconstruct(listing) == original[code["fileOffset"]:
                                                           code["fileOffset"] + listing["byteLength"]]
                    conditional = invoke("store", binary, str(code["rva"]), "5368709120",
                                         "8192", "8", "16")["report"]
                    assert conditional["status"] == "conditional-spatial-assessment"
                    assert conditional["assessment"] == (
                        "within-declared-object" if name == "store_safe" else "outside-declared-object")
                    assert conditional["instructionBytes"] == listing["rows"][0]["bytes"]
                    assert conditional["fileOffset"] == code["fileOffset"]
                    assert conditional["candidateAddress"] == 8192 + int(displacement, 16)
                    assert conditional["remainingObligations"]
                    # Enlarging the declared object changes this conditional claim.
                    enlarged = invoke("store", binary, str(code["rva"]), "5368709120",
                                      "8192", "16", "16")["report"]
                    assert enlarged["assessment"] == "within-declared-object"
                    invoke("store", binary, str(code["rva"]), "5368709120",
                           "8192", "17", "16", expected=2)
                    invoke("store", binary, "0", "5368709120", "8192", "8", "16", expected=2)
                    # Exercise production entry refusal on accepted, mutated
                    # containers, not a parallel test-only mapping function.
                    table = evidence["ntHeaderOffset"] + 24 + 240
                    zero_fill = bytearray(original)
                    zero_fill[table + 8:table + 12] = (code["rawSize"] + 8).to_bytes(4, "little")
                    raw.write_bytes(zero_fill)
                    refused = invoke("store", raw, str(code["rva"] + code["rawSize"]),
                                     "5368709120", "8192", "8", "16", expected=2)["report"]
                    assert refused["stage"] == "entry-bytes" and "zeroFillOnly" in refused["reason"]
                    overlap = bytearray(original)
                    overlap[table + 40 + 12:table + 40 + 16] = code["rva"].to_bytes(4, "little")
                    raw.write_bytes(overlap)
                    refused = invoke("store", raw, str(code["rva"]), "5368709120",
                                     "8192", "8", "16", expected=2)["report"]
                    assert refused["stage"] == "entry-bytes" and "ambiguous" in refused["reason"]
            print("Actual MSVC safe/OOB artifacts ingested; exact store bytes recovered; RET remains unsupported.")

        print(f"Disasm CLI checks passed; actual structural Hello decoded {decoded} instructions.")


if __name__ == "__main__":
    main()
