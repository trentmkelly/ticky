// Talks to the compiler worker: one request at a time, and a fresh worker after a crash or
// a build that takes too long.

export interface Diagnostic {
  severity: "error" | "warning" | "info";
  message: string;
  help: string | null;
  from: number;
  to: number;
  rendered: string;
}

export interface Entity {
  name: string;
  x: number;
  y: number;
  w: number;
  h: number;
  /** 0 north, 1 east, 2 south, 3 west. */
  dir: number;
  /** What a combinator's display shows (the game's symbol sprite name), if anything. */
  symbol: string | null;
  description: string | null;
}

export interface Wire {
  a: number;
  b: number;
  colour: "red" | "green";
  /** Which terminal each end uses: "in", "out", or "" for one-terminal entities. */
  as: string;
  bs: string;
}

export interface CompileResult {
  ok: boolean;
  diagnostics: Diagnostic[];
  report?: string;
  blueprint?: string;
  stats?: { combinators: number; entities: number; width: number; height: number; poles: number; relays: number };
  circuit?: { entities: Entity[]; wires: Wire[] };
}

export interface TestResult {
  ok: boolean;
  diagnostics: Diagnostic[];
  tests: { name: string; ticks: number; passed: boolean; failure: Diagnostic | null }[];
}

export interface Options {
  opt: "speed" | "size";
  place: "grid" | "anneal";
  poles: boolean;
  checks: boolean;
}

const TIMEOUT_MS = 60_000;

export class Compiler {
  private worker!: Worker;
  private next = 1;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void; timer: number }>();

  constructor() {
    this.start();
  }

  private start() {
    this.worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
    this.worker.onmessage = (e: MessageEvent) => {
      const p = this.pending.get(e.data.id);
      if (!p) return;
      this.pending.delete(e.data.id);
      clearTimeout(p.timer);
      if (e.data.error) {
        p.reject(new Error(e.data.error));
        this.restart();
      } else {
        p.resolve(e.data.result);
      }
    };
  }

  private restart() {
    this.worker.terminate();
    for (const p of this.pending.values()) {
      clearTimeout(p.timer);
      p.reject(new Error("the compiler was restarted"));
    }
    this.pending.clear();
    this.start();
  }

  private call<T>(cmd: string, src: string, opts: Options): Promise<T> {
    const id = this.next++;
    return new Promise<T>((resolve, reject) => {
      const timer = window.setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`gave up after ${TIMEOUT_MS / 1000} s`));
        this.restart();
      }, TIMEOUT_MS);
      this.pending.set(id, { resolve, reject, timer });
      this.worker.postMessage({ id, cmd, src, opts });
    });
  }

  compile(src: string, opts: Options): Promise<CompileResult> {
    return this.call("compile", src, opts);
  }

  test(src: string, opts: Options): Promise<TestResult> {
    return this.call("test", src, opts);
  }
}
