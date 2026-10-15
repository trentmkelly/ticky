import { EditorView, basicSetup } from "codemirror";
import { EditorState } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { setDiagnostics, lintGutter } from "@codemirror/lint";
import { oneDark } from "@codemirror/theme-one-dark";
import { ticky } from "./ticky-lang";
import { Compiler, type CompileResult, type Diagnostic, type Options } from "./compiler";
import { CircuitView, legend } from "./circuit";
import "./style.css";

// Examples that make sense without knowing Factorio, in menu order.
const FRIENDLY = [
  "blinker", "counters", "fib", "collatz", "primes", "sorting", "calculator", "guess", "dice",
  "functions", "math", "arrays", "stats", "hysteresis", "thermostat", "handshake", "bestof",
  "ranking", "histogram", "signed-duration", "aes128", "thruster",
];
const sources = import.meta.glob("../../examples/*.ticky", { query: "?raw", import: "default", eager: true }) as Record<string, string>;
const examples = new Map<string, string>();
for (const name of FRIENDLY) {
  const src = sources[`../../examples/${name}.ticky`];
  if (src) examples.set(name, src);
}

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
const status = $("status");
const copyBtn = $<HTMLButtonElement>("copy");
const compiler = new Compiler();
const circuit = new CircuitView($<HTMLCanvasElement>("circuit"), $("tip"));
$("legend").innerHTML = legend;

const STORE = "ticky-playground-source";
let last: CompileResult | null = null;

const escape = (s: string) => s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!);

function options(): Options {
  return {
    opt: $<HTMLSelectElement>("opt").value as Options["opt"],
    place: $<HTMLSelectElement>("place").value as Options["place"],
    poles: $<HTMLInputElement>("poles").checked,
    // `# ticky: --checks` on the first line asks for runtime checks (failed asserts and the
    // like halt the program), as with the command line.
    checks: view.state.doc.line(1).text.startsWith("# ticky: --checks"),
  };
}

function showDiagnostics(ds: Diagnostic[]) {
  const len = view.state.doc.length;
  view.dispatch(
    setDiagnostics(
      view.state,
      ds.map((d) => ({
        from: Math.min(d.from, len),
        to: Math.min(Math.max(d.to, d.from), len),
        severity: d.severity,
        message: d.help ? `${d.message}\nhelp: ${d.help}` : d.message,
      })),
    ),
  );
  $("pane-problems").innerHTML = ds.length
    ? ds.map((d) => `<pre class="diag ${d.severity}">${escape(d.rendered)}</pre>`).join("")
    : `<p class="muted">No problems.</p>`;
}

let generation = 0;
async function build() {
  const g = ++generation;
  const src = view.state.doc.toString();
  localStorage.setItem(STORE, src);
  status.textContent = "Compiling…";
  status.className = "";
  try {
    const r = await compiler.compile(src, options());
    if (g !== generation) return;
    last = r;
    showDiagnostics(r.diagnostics);
    copyBtn.disabled = !r.ok;
    if (r.ok && r.stats) {
      const s = r.stats;
      status.textContent = `Compiled: ${s.combinators} combinators, ${s.width}×${s.height} tiles${s.relays ? `, ${s.relays} wire relays` : ""}.`;
      $("pane-summary").innerHTML = `<pre>${escape(r.report ?? "")}</pre>`;
      circuit.show(r.circuit);
    } else {
      const errors = r.diagnostics.filter((d) => d.severity === "error").length;
      status.textContent = `${errors} error${errors === 1 ? "" : "s"}.`;
      status.className = "bad";
    }
  } catch (e) {
    if (g !== generation) return;
    status.textContent = `The compiler failed: ${(e as Error).message}`;
    status.className = "bad";
  }
}

let timer = 0;
const schedule = () => {
  clearTimeout(timer);
  timer = window.setTimeout(build, 400);
};

const view = new EditorView({
  parent: $("editor"),
  state: EditorState.create({
    doc: localStorage.getItem(STORE) ?? examples.get("blinker") ?? "",
    extensions: [
      basicSetup,
      keymap.of([indentWithTab]),
      indentUnit.of("    "),
      ticky,
      oneDark,
      lintGutter(),
      EditorView.updateListener.of((u) => u.docChanged && schedule()),
    ],
  }),
});

// Controls.
const select = $<HTMLSelectElement>("examples");
select.innerHTML = `<option value="">(choose)</option>` + [...examples.keys()].map((n) => `<option>${n}</option>`).join("");
select.onchange = () => {
  const src = examples.get(select.value);
  if (src === undefined) return;
  view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: src } });
  select.value = "";
};
for (const id of ["opt", "place", "poles"]) $(id).addEventListener("change", build);

copyBtn.onclick = async () => {
  if (!last?.blueprint) return;
  await navigator.clipboard.writeText(last.blueprint);
  const text = copyBtn.textContent;
  copyBtn.textContent = "Copied!";
  setTimeout(() => (copyBtn.textContent = text), 1200);
};

$("run-tests").onclick = async () => {
  activate("tests");
  const pane = $("pane-tests");
  pane.innerHTML = `<p class="muted">Running…</p>`;
  try {
    const r = await compiler.test(view.state.doc.toString(), options());
    if (!r.ok) {
      pane.innerHTML = `<p class="bad">The program doesn't compile; see Problems.</p>`;
      return;
    }
    if (!r.tests.length) {
      pane.innerHTML = `<p class="muted">This program has no <code>test</code> blocks.</p>`;
      return;
    }
    const passed = r.tests.filter((t) => t.passed).length;
    pane.innerHTML =
      `<p class="${passed === r.tests.length ? "good" : "bad"}">${passed} of ${r.tests.length} passed.</p>` +
      r.tests
        .map(
          (t) =>
            `<div class="test ${t.passed ? "pass" : "fail"}"><span>${t.passed ? "✔" : "✘"}</span> ${escape(t.name)} <small>${t.ticks} ticks</small>` +
            (t.failure ? `<pre class="diag error">${escape(t.failure.rendered)}</pre>` : "") +
            `</div>`,
        )
        .join("");
  } catch (e) {
    pane.innerHTML = `<p class="bad">The test run failed: ${escape((e as Error).message)}</p>`;
  }
};

// Tabs.
function activate(tab: string) {
  document.querySelectorAll("#tabs button").forEach((b) => b.classList.toggle("active", (b as HTMLElement).dataset.tab === tab));
  document.querySelectorAll(".pane").forEach((p) => p.classList.toggle("active", p.id === `pane-${tab}`));
  if (tab === "circuit") circuit.draw();
}
document.querySelectorAll<HTMLButtonElement>("#tabs button").forEach((b) => (b.onclick = () => activate(b.dataset.tab!)));

build();
