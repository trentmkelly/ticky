// Compiles every example and runs its tests through the WebAssembly build (src/pkg), failing on
// any compiler panic or failed test: what can break in the browser but not natively (e.g. a
// call to the system clock, which wasm32 doesn't have; use ticky_compiler::clock instead).
// usage: node scripts/check-wasm.mjs [NAME-PREFIX]   (after `npm run wasm`)
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { initSync, compile, test, last_panic } from "../src/pkg/ticky_web.js";

const here = (p) => fileURLToPath(new URL(p, import.meta.url));
const wasm = readFileSync(here("../src/pkg/ticky_web_bg.wasm"));
const dir = here("../../examples/");
const only = process.argv[2] ?? "";
let bad = 0, checked = 0;
for (const f of readdirSync(dir).filter((f) => f.endsWith(".ticky") && f.startsWith(only)).sort()) {
  initSync({ module: wasm }); // a fresh instance: a panic leaves the old one unusable
  const src = readFileSync(dir + f, "utf8");
  // `# ticky: --checks` on the first line asks for runtime checks (as tests/examples.rs does).
  const opts = JSON.stringify({ checks: src.startsWith("# ticky: --checks") });
  try {
    const r = JSON.parse(compile(src, opts));
    if (!r.ok) {
      // Programs that don't compile natively either (work in progress) aren't the wasm's fault.
      console.log(`${f}: doesn't compile: ${r.diagnostics[0]?.message}`);
      continue;
    }
    const failed = JSON.parse(test(src, opts)).tests.filter((t) => !t.passed);
    checked++;
    if (failed.length) {
      bad++;
      console.log(`${f}: FAILED ${failed.map((t) => t.name).join(", ")}`);
    }
  } catch (e) {
    bad++;
    console.log(`${f}: PANIC ${last_panic() ?? e}`);
  }
}
console.log(`${checked} examples compiled and tested in wasm, ${bad} problems`);
process.exit(bad ? 1 : 0);
