// Draws the placed circuit with the game's own graphics (sliced by scripts/build-sprites.py):
// shadows, then entities back to front with their display symbols, then red and green wires
// between the real terminals. Hovering an entity shows what it is and what made it.
import type { CompileResult, Entity } from "./compiler";

const LABELS: Record<string, string> = {
  "arithmetic-combinator": "arithmetic",
  "decider-combinator": "decider",
  "selector-combinator": "selector",
  "constant-combinator": "constant",
  "medium-electric-pole": "pole",
  "small-lamp": "lamp",
  "programmable-speaker": "speaker",
  "display-panel": "display panel",
};

/** Where a frame of a sheet lands, in tiles from the entity's centre. */
interface Frame { file: string; x: number; y: number; w: number; h: number; dx: number; dy: number; dw: number; dh: number }
type Point = [number, number];
/** Per entity: terminal ("in", "out", or "") → per direction → wire colour → point. */
type Connections = Record<string, Record<string, Record<string, Point | null>[]>>;

interface Sprites { frames: Record<string, Frame>; connections: Connections; images: Map<string, HTMLImageElement> }

const BASE = `${import.meta.env.BASE_URL}sprites/`;

async function loadSprites(): Promise<Sprites> {
  const r = await fetch(`${BASE}sprites.json`);
  const { frames, connections } = (await r.json()) as { frames: Record<string, Frame>; connections: Connections };
  const files = [...new Set(Object.values(frames).map((f) => f.file))];
  const images = new Map<string, HTMLImageElement>();
  await Promise.all(
    files.map(
      (file) =>
        new Promise<void>((resolve, reject) => {
          const img = new Image();
          img.onload = () => resolve();
          img.onerror = () => reject(new Error(`couldn't load ${file}`));
          img.src = BASE + file;
          images.set(file, img);
        }),
    ),
  );
  return { frames, connections, images };
}

/** Entities drawn in one direction only (the frame for direction 0). */
const ONE_WAY = new Set(["medium-electric-pole", "small-lamp", "programmable-speaker"]);

/** Wire terminals for entities whose game definition isn't sliced (generic connectors). */
const FALLBACK: Record<string, Point> = { "small-lamp": [0, -0.25], "programmable-speaker": [0, -1.1] };

export class CircuitView {
  private ctx: CanvasRenderingContext2D;
  private data: CompileResult["circuit"] | null = null;
  private view = { scale: 1, ox: 0, oy: 0 };
  private sprites: Sprites | null = null;

  constructor(private canvas: HTMLCanvasElement, private tip: HTMLElement) {
    this.ctx = canvas.getContext("2d")!;
    new ResizeObserver(() => this.draw()).observe(canvas);
    canvas.addEventListener("mousemove", (e) => this.hover(e));
    canvas.addEventListener("mouseleave", () => (this.tip.hidden = true));
    loadSprites()
      .then((s) => {
        this.sprites = s;
        this.draw();
      })
      .catch((e) => console.warn("circuit graphics:", e));
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
    // Room for what sticks out of the footprints: poles' tops, shadows to the right.
    return { x0: x0 - 0.5, y0: y0 - 2.5, x1: x1 + 1, y1: y1 + 0.5 };
  }

  private frame(e: Entity, part = ""): Frame | undefined {
    const dir = ONE_WAY.has(e.name) ? 0 : e.dir;
    return this.sprites?.frames[`${e.name}/${dir}${part ? `/${part}` : ""}`];
  }

  /** A wire end: the entity's terminal for that colour, in tiles. */
  private terminal(e: Entity, side: string, colour: string): Point {
    const c = this.sprites?.connections[e.name];
    const p = c?.[side]?.[ONE_WAY.has(e.name) ? 0 : e.dir]?.[colour] ?? c?.[""]?.[ONE_WAY.has(e.name) ? 0 : e.dir]?.[colour];
    const [dx, dy] = p ?? FALLBACK[e.name] ?? [0, 0];
    return [e.x + dx, e.y + dy];
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
    const pad = 12;
    const scale = Math.min((w - 2 * pad) / (b.x1 - b.x0), (h - 2 * pad) / (b.y1 - b.y0), 64);
    const ox = (w - (b.x1 - b.x0) * scale) / 2 - b.x0 * scale;
    const oy = (h - (b.y1 - b.y0) * scale) / 2 - b.y0 * scale;
    this.view = { scale, ox, oy };
    const X = (x: number) => ox + x * scale, Y = (y: number) => oy + y * scale;
    // Ground and tile grid.
    ctx.fillStyle = "#3a3631";
    ctx.fillRect(X(b.x0), Y(b.y0), (b.x1 - b.x0) * scale, (b.y1 - b.y0) * scale);
    ctx.strokeStyle = "rgba(0,0,0,0.18)";
    ctx.lineWidth = 1;
    for (let x = Math.ceil(b.x0); x <= b.x1; x++) {
      ctx.beginPath(); ctx.moveTo(X(x), Y(b.y0)); ctx.lineTo(X(x), Y(b.y1)); ctx.stroke();
    }
    for (let y = Math.ceil(b.y0); y <= b.y1; y++) {
      ctx.beginPath(); ctx.moveTo(X(b.x0), Y(y)); ctx.lineTo(X(b.x1), Y(y)); ctx.stroke();
    }
    const blit = (e: Entity, f: Frame) => {
      const img = this.sprites!.images.get(f.file)!;
      ctx.drawImage(img, f.x, f.y, f.w, f.h, X(e.x + f.dx), Y(e.y + f.dy), f.dw * scale, f.dh * scale);
    };
    // Back to front, as the game draws them.
    const order = [...es].sort((a, c) => a.y + a.h / 2 - (c.y + c.h / 2) || a.x - c.x);
    if (this.sprites) {
      ctx.imageSmoothingQuality = "high";
      ctx.globalAlpha = 0.5;
      for (const e of order) {
        const f = this.frame(e, "shadow");
        if (f) blit(e, f);
      }
      ctx.globalAlpha = 1;
    }
    for (const e of order) {
      const f = this.frame(e);
      if (!f) {
        ctx.fillStyle = "#777";
        const inset = Math.min(2, scale * 0.08);
        ctx.fillRect(X(e.x - e.w / 2) + inset, Y(e.y - e.h / 2) + inset, e.w * scale - 2 * inset, e.h * scale - 2 * inset);
        continue;
      }
      blit(e, f);
      const sym = e.symbol && this.frame(e, e.symbol);
      if (sym) blit(e, sym);
    }
    // Wires on top, sagging a little like the game's.
    ctx.lineWidth = Math.max(1, scale * 0.045);
    ctx.lineCap = "round";
    for (const wire of this.data!.wires) {
      const a = es[wire.a], c = es[wire.b];
      if (!a || !c) continue;
      const [x1, y1] = this.terminal(a, wire.as, wire.colour);
      const [x2, y2] = this.terminal(c, wire.bs, wire.colour);
      const sag = Math.min(0.6, Math.hypot(x2 - x1, y2 - y1) * 0.06);
      ctx.strokeStyle = wire.colour === "red" ? "rgba(220,50,40,0.95)" : "rgba(60,190,70,0.95)";
      ctx.beginPath();
      ctx.moveTo(X(x1), Y(y1));
      ctx.quadraticCurveTo(X((x1 + x2) / 2), Y((y1 + y2) / 2 + 2 * sag), X(x2), Y(y2));
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

export const legend = "Hover an entity to see what it is and what made it. Graphics © Wube Software.";
