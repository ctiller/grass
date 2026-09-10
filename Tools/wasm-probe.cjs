// Native validation of actual Lean-emitted bytes; never proof authority.
const fs = require('node:fs');
const assert = require('node:assert/strict');
function load(name, imports = {}) {
  const bytes = fs.readFileSync(`.lake/wasm-probe/${name}.wasm`);
  assert(WebAssembly.validate(bytes), `${name}: invalid emitted module`);
  return new WebAssembly.Instance(new WebAssembly.Module(bytes), imports).exports;
}
const calls = [];
const host = load('host', {env: {observe(a, b) { calls.push([a, b]); return a + b; }}});
assert.equal(host.run(), 9);
assert.deepEqual(calls, [[4, 5]]);
const locals = load('locals');
for (const a of [0, 1, -1, 7, 2147483647, -2147483648]) {
  for (const b of [0, 1, -1, 3, 2147483647, -2147483648]) {
    assert.equal(locals.run(a, b), (a - b) | 0);
  }
}
assert.equal(load('constant').run(), -1n);
let trap;
assert.doesNotThrow(() => { trap = load('trap'); },
  'trap: module instantiation must succeed before testing invocation');
const trapRun = trap.run;
assert.equal(typeof trapRun, 'function', 'trap: run must be a function export');
assert.throws(() => trapRun(), WebAssembly.RuntimeError,
  'trap: run must trap during invocation');
console.log('Wasm probe passed: 4 emitted modules, host arguments/results, 36 local subtraction cases, signed i64 constant, architectural trap.');
