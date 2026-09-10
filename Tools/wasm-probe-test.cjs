// AUD-009 regression: distinguish module instantiation from exported invocation.
// Uses retained production-emitted inputs; never proof authority.
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const {spawnSync} = require('node:child_process');
const repo = path.resolve(__dirname, '..');
const input = path.join(repo, '.lake', 'wasm-probe');
const tempParent = path.join(repo, '.lake');
const scratch = fs.mkdtempSync(path.join(tempParent, 'wasm-probe-phase-'));
const startTrap = Buffer.from(
  '0061736d0100000001040160000003030200000707010372756e00010801000a08020300000b02000b', 'hex');
const noStart = Buffer.from(
  '0061736d0100000001040160000003030200000707010372756e00010a08020300000b02000b', 'hex');
assert(WebAssembly.validate(startTrap));
assert(WebAssembly.validate(noStart));
try {
  for (const [name, replacement, diagnostic] of [
    ['invocation-trap', null, null],
    ['instantiation-trap', startTrap, 'module instantiation must succeed'],
    ['nontrapping-run', noStart, 'run must trap during invocation'],
  ]) {
    const cwd = path.join(scratch, name);
    const output = path.join(cwd, '.lake', 'wasm-probe');
    fs.mkdirSync(output, {recursive: true});
    for (const file of ['host', 'locals', 'constant', 'trap']) {
      fs.copyFileSync(path.join(input, `${file}.wasm`), path.join(output, `${file}.wasm`));
    }
    if (replacement) fs.writeFileSync(path.join(output, 'trap.wasm'), replacement);
    const result = spawnSync(process.execPath, [path.join(__dirname, 'wasm-probe.cjs')],
      {cwd, encoding: 'utf8', timeout: 10000});
    assert.ifError(result.error);
    assert.equal(result.signal, null, `${name}: child terminated by signal`);
    if (diagnostic === null) {
      assert.equal(result.status, 0, `${name}: ${result.stderr}`);
      assert.match(result.stdout, /Wasm probe passed:/);
    } else {
      assert.notEqual(result.status, 0, `${name}: harness falsely accepted mutant`);
      assert(result.stderr.includes(diagnostic), `${name}: ${result.stderr}`);
      assert(!result.stdout.includes('Wasm probe passed:'), `${name}: false success banner`);
    }
    console.log(`${name}: expected harness exit ${result.status}`);
  }
} finally {
  // Verify the generated deletion target is one direct child of our workspace cache.
  assert.equal(path.dirname(path.resolve(scratch)), path.resolve(tempParent));
  fs.rmSync(scratch, {recursive: true});
}
