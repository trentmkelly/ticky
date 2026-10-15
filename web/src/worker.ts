// Runs the compiler (wasm) off the main thread, so long builds don't freeze the page.
import init, { compile, test, version, last_panic } from "./pkg/ticky_web.js";

const ready = init();

self.onmessage = async (e: MessageEvent) => {
  const { id, cmd, src, opts } = e.data;
  try {
    await ready;
    const json = JSON.stringify(opts ?? {});
    const out = cmd === "test" ? test(src, json) : cmd === "version" ? JSON.stringify(version()) : compile(src, json);
    postMessage({ id, result: JSON.parse(out) });
  } catch (err) {
    // A panic in the compiler (its message, if it got one): the page restarts the worker.
    let panic: string | undefined;
    try {
      panic = last_panic() ?? undefined;
    } catch {}
    postMessage({ id, error: panic ? `internal compiler error: ${panic}` : String(err) });
  }
};
