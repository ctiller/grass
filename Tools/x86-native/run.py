"""Generate Lean cases and retain native observations. No execution is proof authority."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import platform
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
REGS = 'rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15'.split()
FLAGS_MASK = 0x8D5  # CF/PF/AF/ZF/SF/OF; OS-owned/reserved flags are not predictions.
# Coverage identity excludes emitted bytes and expected outputs: changes to the
# model must reach the hardware comparator, not ask users to bless a new digest.
COVERAGE_SHA256 = '9bdf88e1e44543f42dd87e923e8d9ca0affd0a091f67c6248ff282273f50b643'


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def observe(worker, code, before, flags, timeout=5, stack=False):
    try:
        result = subprocess.run([str(worker), code, *[f'{0 if x is None else x:x}' for x in before],
                                 f'{flags:x}', *(['--stack'] if stack else [])],
                                capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'status': 'timeout'}
    if result.returncode:
        return {'status': 'harness-error', 'exit': result.returncode,
                'stdout': result.stdout, 'stderr': result.stderr}
    try:
        data = json.loads(result.stdout)
        require(data['status'] in ('completed', 'fault'), 'status')
        require(len(data['registers']) == 16, 'register count')
        require(all(type(x) is int and 0 <= x < 2**64 for x in data['registers']), 'register values')
        require(all(type(data[k]) is int for k in
                    ('exception', 'pc_offset', 'rip_offset', 'entry_rsp', 'flags')), 'context fields')
        return data
    except (ValueError, KeyError, TypeError):
        return {'status': 'protocol-error', 'stdout': result.stdout, 'stderr': result.stderr}


def differences(actual, code, expected, flags, rsp_decrease=0, terminal_extra=0,
                flags_mask=FLAGS_MASK):
    if actual['status'] != 'completed':
        return [actual['status']]
    errors = []
    if actual['exception'] != 0x80000003:
        errors.append('completion-exception')
    if actual['pc_offset'] != len(bytes.fromhex(code)) + terminal_extra:
        errors.append('completion-address')
    # Windows CONTEXT reports the breakpoint instruction, not its successor.
    if actual['rip_offset'] != len(bytes.fromhex(code)) + terminal_extra:
        errors.append('completion-rip')
    for i, name in enumerate(REGS):
        want = actual['entry_rsp'] - rsp_decrease if i == 4 else expected[i]
        if actual['registers'][i] != want:
            errors.append(name)
    if flags is not None and (actual['flags'] ^ flags) & flags_mask:
        errors.append('flags')
    return errors


def self_test(worker):
    """Challenge capture and comparator using independent, fixed ISA controls."""
    before = [0xFEDCBA9876543210 + i for i in range(16)]
    nop = observe(worker, '90', before, 0xAD7)
    require(differences(nop, '90', before, 0xAD7) == [], nop)
    bad = before.copy()
    bad[0] ^= 1
    require(differences(nop, '90', bad, 0xAD7) == ['rax'], 'register negative control')
    require(differences(nop, '90', before, 0xAD6) == ['flags'], 'flag negative control')
    require(differences(dict(nop, exception=0), '90', before, 0xAD7) ==
            ['completion-exception'], 'exception negative control')
    require(differences(dict(nop, rip_offset=999), '90', before, 0xAD7) ==
            ['completion-rip'], 'RIP negative control')
    logical_mask = FLAGS_MASK & ~0x10
    require(differences(nop, '90', before, 0xAD7 ^ 0x10,
                        flags_mask=logical_mask) == [], 'logical AF mask control')
    require(differences(nop, '90', before, 0xAD7 ^ 0x10) == ['flags'],
            'defined AF negative control')
    require(differences(nop, '90', before, 0xAD7 ^ 1,
                        flags_mask=logical_mask) == ['flags'],
            'defined CF negative control')
    # These are harness controls, never model-coverage rows.
    for code, status in [('0f0b', 0xC000001D), ('f4', 0xC0000096),
                         ('cc', 0x80000003)]:
        actual = observe(worker, code, before, 0xAD7)
        require(actual['status'] == 'fault' and actual['exception'] == status, actual)
        require(actual['pc_offset'] == 0, actual)
        require(actual['registers'][0] == before[0], actual)
    require(observe(worker, 'ebfe', before, 0xAD7, timeout=0.25)['status'] == 'timeout', 'timeout control')
    return 12


def parse_flags(field):
    """Accept legacy full-status hex/- fields and value/mask semantic fields."""
    if field == '-':
        return None, FLAGS_MASK
    if '/' not in field:
        value = int(field, 16)
        require(0 <= value < 2**64, 'legacy flag value')
        return value, FLAGS_MASK
    value, mask = field.split('/', 1)
    value, mask = int(value, 16), int(mask, 16)
    require(0 <= value < 2**64 and 0 <= mask < 2**64 and not mask & ~FLAGS_MASK,
            'flag value/mask')
    return value, mask


def parse_corpus_flags(label, field):
    """The modeled campaign requires a prediction for every defined flag."""
    value, mask = parse_flags(field)
    require(value is not None, f'modeled flags required for {label}')
    expected_mask = (FLAGS_MASK & ~0x10
                     if label.startswith(('boundary-test-', 'boundary-xor-'))
                     or label == 'hello-test-eax-eax' else FLAGS_MASK)
    require(mask == expected_mask, f'flag mask for {label}')
    return value, mask


def corpus_controls(raw):
    """Mutate a full-status row to the legacy unchecked marker before execution."""
    row = raw.splitlines()[0].split('\t')
    require(row[0].startswith('mov-'), 'full-status control row')
    row[5] = '-'
    try:
        parse_corpus_flags(row[0], row[5])
    except ValueError as error:
        require(str(error) == f'modeled flags required for {row[0]}',
                'unchecked flags rejected for unexpected reason')
    else:
        raise ValueError('unchecked flags negative control failed')
    return 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if platform.system() != 'Windows' or platform.machine().lower() not in ('amd64', 'x86_64'):
        parser.error('this adapter requires x86-64 Windows; no fallback counts as a pass')
    worker = args.worker.resolve(strict=True)
    args.output.mkdir(parents=True, exist_ok=False)  # never overwrite evidence
    subprocess.run(['lake', 'build', 'Tests.ISA.X86.NativeCorpus'], cwd=ROOT, check=True)
    raw = subprocess.run(['lake', 'env', 'lean', '--run', 'Tests/ISA/X86/NativeCorpus.lean'],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    (args.output / 'corpus.tsv').write_text(raw, encoding='utf-8')
    coverage = '\n'.join('\t'.join(row[i] for i in (0, 2, 4, 6))
                         for row in (line.split('\t') for line in raw.splitlines()))
    require(hashlib.sha256(coverage.encode()).hexdigest() == COVERAGE_SHA256,
            'coverage identity changed; review the population, inputs and prediction basis')
    intake_controls = corpus_controls(raw)
    cases, seen = [], set()
    for line in raw.splitlines():
        label, code, before, after, flags_in, flags_out, basis = line.split('\t')
        require(label not in seen, label)
        seen.add(label)
        before = [None if x == '-' else int(x, 16) for x in before.split(',')]
        after = [None if x == '-' else int(x, 16) for x in after.split(',')]
        require(len(before) == len(after) == 16, 'corpus register count')
        require(before[4] is None and after[4] is None, 'RSP must use the host-stack marker')
        require(all(type(x) is int and 0 <= x < 2**64
                    for row in (before, after) for i, x in enumerate(row) if i != 4), 'corpus register value')
        require(0 < len(bytes.fromhex(code)) <= 15, 'instruction length')
        flags_out, flags_mask = parse_corpus_flags(label, flags_out)
        cases.append(dict(label=label, code=code, before=before, expected=after,
                          flags_in=int(flags_in, 16), flags_out=flags_out,
                          flags_mask=flags_mask, basis=basis))
    # 450 MOV + 420 immediate arithmetic + 120 register boundaries + 4 Hello operations.
    require(len(cases) == 994, f'unreviewed population change: {len(cases)}')
    require(sum(case['flags_mask'] == FLAGS_MASK for case in cases) == 953 and
            sum(case['flags_mask'] == FLAGS_MASK & ~0x10 for case in cases) == 41,
            'modeled flag-mask population')
    metadata = dict(schema=1, adapter='windows-veh', os=platform.platform(),
                    started_utc=datetime.now(timezone.utc).isoformat(),
                    cpu=json.loads(subprocess.check_output([str(worker), '--host'], text=True)),
                    microcode='unknown', virtualization='CPUID hypervisor bit only; absence is not proof',
                    revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    working_tree=subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True),
                    corpus_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                    worker_sha256=hashlib.sha256(worker.read_bytes()).hexdigest(),
                    source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in [Path(__file__).resolve(), ROOT/'Tools/x86-native/windows.c',
                                             ROOT/'Tests/ISA/X86/NativeCorpus.lean',
                                             *sorted((ROOT/'Grass/ISA/X86').glob('*.lean'))]})
    metadata['harness_controls'] = self_test(worker)
    metadata['corpus_controls'] = intake_controls
    (args.output / 'host.json').write_text(json.dumps(metadata, indent=2), encoding='utf-8')
    failures = 0
    with (args.output / 'observations.jsonl').open('w', encoding='utf-8') as out:
        for case in cases:
            actual = observe(worker, case['code'], case['before'], case['flags_in'])
            errors = differences(actual, case['code'], case['expected'], case['flags_out'],
                                 flags_mask=case['flags_mask'])
            failures += bool(errors)
            out.write(json.dumps(dict(case=case, actual=actual, differences=errors)) + '\n')
            out.flush()
    summary = dict(cases=len(cases), mismatches=failures, mov_cases=470,
                   immediate_arithmetic_cases=420, boundary_register_cases=120,
                   hello_operation_cases=4, modeled_register_cases=994,
                   fully_defined_status_flag_cases=953,
                   logical_defined_status_flag_cases=41,
                   logical_af_undefined_cases=41, harness_controls=12,
                   corpus_controls=intake_controls)
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2), encoding='utf-8')
    print(json.dumps(summary))
    return int(failures != 0)


if __name__ == '__main__':
    sys.exit(main())
