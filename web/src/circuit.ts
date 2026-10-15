// Draws the placed circuit: one box per entity (as it sits in the blueprint) and its red and
// green wires. Hovering a box shows what it is and what made it.
import type { CompileResult, Entity } from "./compiler";

const COLOURS: Record<string, string> = {
  "arithmetic-combinator": "#3b82c4",
  "decider-combinator": "#d4892a",
  "selector-combinator": "#9a5cc6",
  "constant-combinator": "#7a8288",
  "medium-electric-pole": "#6b4f35",
  "small-lamp": "#d8c64a",
  "programmable-speaker": "#4aa58a",
  "display-panel": "#5a7fa0",
};

const LABELS: Record<string, string> = {
  "arithmetic-combinator": "arithmetic",
  "decider-combinator": "decider",
  "selector-combinator": "selector",
  "constant-combinator": "constant",
  "medium-electric-pole": "pole",
  "small-lamp": "lamp",
};

export class CircuitView {
  private ctx: CanvasRenderingContext2D;
  private data: CompileResult["circuit"] | null = null;
  private view = { scale: 1, ox: 0, oy: 0 };

  constructor(private canvas: HTMLCanvasElement, private tip: HTMLElement) {
    this.ctx = canvas.getContext("2d")!;
    new ResizeObserver(() => this.draw()).observe(canvas);
    canvas.addEventListener("mousemove", (e) => this.hover(e));
    canvas.addEventListener("mouseleave", () => (this.tip.hidden = true));
  }

  show(circuit: CompileResult["circuit"] | undefined) {
    this.data = circuit ?? null;
    this.draw();
  }

  private bounds(es: Entity[]) {
    let [x0, y0, x1, y1] = [Infinity, Infinity, -Infinity, -Infinity];
    for (const e of es) {
      x0 = Math.min(x0, e.x - e.w / 2);
      y0 = Math.min(y0, e.y - e.h / 2);
      x1 = Math.max(x1, e.x + e.w / 2);
      y1 = Math.max(y1, e.y + e.h / 2);
    }
    return { x0, y0, x1, y1 };
  }

  draw() {
    const { canvas, ctx } = this;
    const dpr = window.devicePixelRatio || 1;
    const w = canvas.clientWidth, h = canvas.clientHeight;
    if (!w || !h) return;
    canvas.width = w * dpr;
    canvas.height = h * dpr;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, w, h);
    const es = this.data?.entities ?? [];
    if (!es.length) return;
    const b = this.bounds(es);
    const pad = 16;
    const scale = Math.min((w - 2 * pad) / (b.x1 - b.x0), (h - 2 * pad) / (b.y1 - b.y0), 48);
    const ox = (w - (b.x1 - b.x0) * scale) / 2 - b.x0 * scale;
    const oy = (h - (b.y1 - b.y0) * scale) / 2 - b.y0 * scale;
    this.view = { scale, ox, oy };
    const X = (x: number) => ox + x * scale, Y = (y: number) => oy + y * scale;
    // Tile grid.
    ctx.strokeStyle = "rgba(255,255,255,0.04)";
    ctx.lineWidth = 1;
    for (let x = Math.floor(b.x0); x <= b.x1; x++) {
      ctx.beginPath(); ctx.moveTo(X(x), Y(b.y0)); ctx.lineTo(X(x), Y(b.y1)); ctx.stroke();
    }
    for (let y = Math.floor(b.y0); y <= b.y1; y++) {
      ctx.beginPath(); ctx.moveTo(X(b.x0), Y(y)); ctx.lineTo(X(b.x1), Y(y)); ctx.stroke();
    }
    // Entities.
    for (const e of es) {
      ctx.fillStyle = COLOURS[e.name] ?? "#888";
      const inset = Math.min(2, scale * 0.08);
      ctx.fillRect(X(e.x - e.w / 2) + inset, Y(e.y - e.h / 2) + inset, e.w * scale - 2 * inset, e.h * scale - 2 * inset);
    }
    // Wires on top, slightly apart so red and green between the same pair both show.
    ctx.lineWidth = Math.max(1, scale * 0.06);
    for (const wire of this.data!.wires) {
      const a = es[wire.a], c = es[wire.b];
      if (!a || !c) continue;
      const d = (wire.colour === "red" ? -1 : 1) * scale * 0.12;
      ctx.strokeStyle = wire.colour === "red" ? "rgba(235,70,60,0.85)" : "rgba(70,200,90,0.85)";
      ctx.beginPath();
      ctx.moveTo(X(a.x) + d, Y(a.y) + d);
      ctx.lineTo(X(c.x) + d, Y(c.y) + d);
      ctx.stroke();
    }
  }

  private hover(ev: MouseEvent) {
    const es = this.data?.entities ?? [];
    const r = this.canvas.getBoundingClientRect();
    const { scale, ox, oy } = this.view;
    const x = (ev.clientX - r.left - ox) / scale, y = (ev.clientY - r.top - oy) / scale;
    const e = es.find((e) => Math.abs(x - e.x) <= e.w / 2 && Math.abs(y - e.y) <= e.h / 2);
    if (!e) {
      this.tip.hidden = true;
      return;
    }
    this.tip.hidden = false;
    this.tip.textContent = `${LABELS[e.name] ?? e.name}${e.description ? `: ${e.description}` : ""}`;
    this.tip.style.left = `${ev.clientX - r.left + 14}px`;
    this.tip.style.top = `${ev.clientY - r.top + 14}px`;
  }
}

export const legend = Object.entries(LABELS)
  .map(([k, v]) => `<span><i style="background:${COLOURS[k]}"></i>${v}</span>`)
  .join("");
