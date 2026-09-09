"""Success-only PUSH/frame-allocation observations on an initialized scratch stack."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import run as native

SIZE = 65536
ENTRY_OFFSET = SIZE - 120  # ABI entry RSP is 8 modulo 16.
INPUT = [0xFEDCBA9876543210 + i * 0x102030405 for i in range(16)]
FLAGS = 0xAD7
COVERAGE = 'a2b0d896b93776986ee5abd0dd3da228a22462a8456e0129c7470c3cc2ee012d'


def coverage_identity(raw):
    # Pin the declared semantic footprint, not encoder output: byte mutations
    # must reach the real-machine comparison rather than a digest approval gate.
    identity = '\n'.join('\t'.join(row[i] for i in (0,2,3,4,5))
                         for row in (line.split('\t') for line in raw.splitlines()))
    return hashlib.sha256(identity.encode()).hexdigest()


def stack_differences(actual, case):
    errors = native.differences(actual, case['code'], INPUT,
        FLAGS if case['flags_preserved'] else None, case['decrease'], 14)
    if actual['status'] != 'completed':
        return errors  # exception delivery may have written scratch; do not judge it
    try:
        stack = actual['stack']
        base, size, offset = (stack[k] for k in ('base', 'size', 'entry_offset'))
        native.require(all(type(x) is int for x in (base, size, offset)), 'stack geometry')
        native.require(size == SIZE and offset == ENTRY_OFFSET and
                       0 < base < base+size < 2**64, 'stack bounds')
        native.require(actual['entry_rsp'] == base+offset, 'entry relocation')
        native.require(actual['entry_rsp'] % 16 == 8, 'entry alignment')
        host_low, host_high, host_rsp, code_base, page = (stack[k] for k in
            ('host_low', 'host_high', 'host_rsp', 'code_base', 'page_size'))
        native.require(all(type(x) is int for x in (host_low, host_high, host_rsp, code_base, page)),
                       'mapping types')
        native.require(1024 <= page <= SIZE and SIZE % page == 0, 'page size')
        native.require(0 < host_low <= host_rsp < host_high < 2**64, 'host stack')
        regions = [(base-page, base+SIZE+page), (code_base, code_base+page),
                   (code_base+page, code_base+2*page),
                   (code_base+2*page, code_base+3*page), (host_low, host_high)]
        for start, end in regions:
            native.require(0 < start < end < 2**64, 'mapping overflow')
        for i, (a, b) in enumerate(regions):
            for c, d in regions[i+1:]:
                native.require(b <= c or d <= a, 'mapping overlap')
        # Independently decode the two harness RIP-relative relocations.
        suffix = bytes.fromhex(stack['suffix'])
        native.require(len(suffix) == 14 and suffix[:3] == bytes.fromhex('488925') and
                       suffix[7:10] == bytes.fromhex('488b25'), 'suffix opcodes')
        suffix_pc = code_base+1+len(bytes.fromhex(case['code']))
        native.require(suffix_pc+7+int.from_bytes(suffix[3:7], 'little', signed=True) == code_base+page,
                       'save slot')
        native.require(suffix_pc+14+int.from_bytes(suffix[10:14], 'little', signed=True) == code_base+2*page,
                       'restore slot')
        before, after = bytes.fromhex(stack['before']), bytes.fromhex(stack['after'])
        native.require(len(before) == len(after) == SIZE, 'snapshot size')
        native.require(before == bytes((i*37+0xA5)&255 for i in range(SIZE)), 'initialization')
        expected = bytearray(before)
        for index, reg in enumerate(case['pushes']):
            where = offset-8*(index+1)
            native.require(0 <= where and where+8 <= SIZE, 'push range')
            # PUSH RSP reads the pre-decrement value, including previous pushes.
            value = actual['entry_rsp']-8*index if reg == 4 else INPUT[reg]
            expected[where:where+8] = value.to_bytes(8, 'little')
        if after != expected:
            errors.append('stack-bytes')
    except (ValueError, KeyError, TypeError, OverflowError):
        errors.append('stack-protocol')
    return errors


def control(worker):
    empty = dict(code='90', decrease=0, pushes=[], flags_preserved=True)
    nop = native.observe(worker, '90', INPUT, FLAGS, stack=True)
    native.require(stack_differences(nop, empty) == [], nop.get('status'))
    # Wrong expected stack movement and missing/misdirected memory writes fail.
    native.require('rsp' in stack_differences(nop, dict(empty, decrease=8)), 'RSP negative control')
    push = dict(code='54', decrease=8, pushes=[4], flags_preserved=True)
    actual = native.observe(worker, push['code'], INPUT, FLAGS, stack=True)
    native.require(stack_differences(actual, push) == [], 'PUSH RSP control')
    native.require('stack-bytes' in stack_differences(actual, dict(push, pushes=[])), 'missing store control')
    native.require('stack-bytes' in stack_differences(actual, dict(push, pushes=[0])), 'wrong source control')
    changed = dict(actual, stack=dict(actual['stack'], suffix='00'*14))
    native.require('stack-protocol' in stack_differences(changed, push), 'suffix negative control')
    remote_byte = bytearray.fromhex(actual['stack']['after'])
    remote_byte[0] ^= 1
    changed = dict(actual, stack=dict(actual['stack'], after=remote_byte.hex()))
    native.require('stack-bytes' in stack_differences(changed, push), 'whole-region negative control')
    return 7


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    native.require(platform.system() == 'Windows' and platform.machine().lower() in ('amd64','x86_64'),
                   'requires x86-64 Windows')
    worker = args.worker.resolve(strict=True)
    args.output.mkdir(parents=True, exist_ok=False)
    subprocess.run(['lake','build','Tests.ISA.X86.NativeStackCorpus'], cwd=native.ROOT, check=True)
    raw = subprocess.check_output(['lake','env','lean','--run','Tests/ISA/X86/NativeStackCorpus.lean'],
                                  cwd=native.ROOT, text=True)
    (args.output/'corpus.tsv').write_text(raw, encoding='utf-8')
    cases = []
    for line in raw.splitlines():
        label, code, delta, pushed, flags, basis = line.split('\t')
        pushes = [] if pushed == '-' else [int(x) for x in pushed.split(',')]
        decrease = int(delta)
        native.require(0 < len(bytes.fromhex(code)) <= 255, 'body length')
        native.require(0 <= decrease <= 8192 and 8*len(pushes) <= decrease, 'bounded scratch footprint')
        native.require(all(0 <= r < 16 for r in pushes), 'register indices')
        native.require(flags in ('yes','-'), 'flag mask')
        cases.append(dict(label=label,code=code,decrease=decrease,pushes=pushes,
                          flags_preserved=flags=='yes',basis=basis))
    native.require(cases and len({c['label'] for c in cases}) == len(cases), 'empty/duplicate population')
    native.require(coverage_identity(raw) == COVERAGE, 'unreviewed stack population')
    mutated = raw.splitlines()
    fields = mutated[0].split('\t')
    fields[2] = str(int(fields[2])+8)
    mutated[0] = '\t'.join(fields)
    native.require(coverage_identity('\n'.join(mutated)) != COVERAGE, 'coverage negative control')
    metadata = dict(schema=2, adapter='windows-scratch-stack-success-only',
        started_utc=datetime.now(timezone.utc).isoformat(), os=platform.platform(),
        cpu=json.loads(subprocess.check_output([str(worker),'--host'],text=True)), microcode='unknown',
        revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=native.ROOT,text=True).strip(),
        dirty=subprocess.check_output(['git','status','--porcelain'],cwd=native.ROOT,text=True),
        corpus_sha256=hashlib.sha256(raw.encode()).hexdigest(),
        worker_sha256=hashlib.sha256(worker.read_bytes()).hexdigest(), inputs=INPUT,
        source_sha256={str(p.relative_to(native.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [Path(__file__).resolve(),native.ROOT/'Tools/x86-native/run.py',
                      native.ROOT/'Tools/x86-native/windows.c',
                      native.ROOT/'Tests/ISA/X86/NativeStackCorpus.lean',
                      *sorted((native.ROOT/'Grass/Assembly').glob('*.lean')),
                      *sorted((native.ROOT/'Grass/ISA/X86').glob('*.lean')),
                      *sorted((native.ROOT/'Grass/ABI/Win64').glob('*.lean'))]},
        controls=control(worker))
    (args.output/'host.json').write_text(json.dumps(metadata,indent=2),encoding='utf-8')
    failures = 0
    with (args.output/'observations.jsonl').open('w',encoding='utf-8') as out:
        for case in cases:
            actual = native.observe(worker,case['code'],INPUT,FLAGS,stack=True)
            errors = stack_differences(actual,case)
            failures += bool(errors)
            out.write(json.dumps(dict(case=case,actual=actual,differences=errors))+'\n')
            out.flush()
    summary = dict(cases=len(cases),mismatches=failures,stack_controls=7,
                   memory_basis='test-local PUSH little-endian reference; successful final state only')
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
    print(json.dumps(summary))
    return int(failures != 0)


if __name__ == '__main__':
    sys.exit(main())
