/**
 * Pattern helpers for PatternMaker: symbols for repeating patterns, the
 * remainder rule for "what is item k?", and quadratic growing patterns
 * a·n² + b·n + c drawn as tiles (n × n squares, columns of n, single tiles).
 */
import { COLOUR_NAMES, type ColourName } from "./shape-util";

export const SHAPES = ["circle", "triangle", "square", "star", "heart", "diamond"] as const;
export type ShapeName = (typeof SHAPES)[number];

export const DEFAULT_COLOUR: Record<ShapeName, ColourName> = {
  circle: "orange",
  triangle: "blue",
  square: "yellow",
  star: "purple",
  heart: "red",
  diamond: "green",
};

export interface PatternSymbol {
  id: string;
  shape: ShapeName;
  colour: ColourName;
}

/** "triangle" (default colour) or "triangle-red". Unknown ids give null. */
export function parseSymbol(raw: unknown): PatternSymbol | null {
  if (typeof raw !== "string") return null;
  const [shape, colour, extra] = raw.trim().toLowerCase().split("-");
  if (extra !== undefined || !(SHAPES as readonly string[]).includes(shape)) return null;
  const s = shape as ShapeName;
  if (colour === undefined) return { id: s, shape: s, colour: DEFAULT_COLOUR[s] };
  if (!(COLOUR_NAMES as string[]).includes(colour)) return null;
  const c = colour as ColourName;
  return { id: c === DEFAULT_COLOUR[s] ? s : `${s}-${c}`, shape: s, colour: c };
}

export const MAX_CORE = 6;
export const DEFAULT_CORE = ["circle", "triangle", "square"];

/** The core unit from the `core` prop: valid symbols only (at most 6); the default ●▲■ if none are valid. */
export function parseCore(core: unknown): PatternSymbol[] {
  const out = Array.isArray(core) ? core.map(parseSymbol).filter((s): s is PatternSymbol => s !== null).slice(0, MAX_CORE) : [];
  return out.length ? out : DEFAULT_CORE.map((id) => parseSymbol(id)!);
}

/** Symbols offered for building a core. */
export const PALETTE = ["circle", "triangle", "square", "star", "heart", "diamond", "circle-blue", "circle-green", "square-red", "triangle-yellow"].map((id) => parseSymbol(id)!);

/**
 * Where item k (1-based) falls in a repeating pattern with a core of length
 * `len`: k ÷ len = q remainder r, and the item is position `pos` of the core
 * (pos = r, except that remainder 0 means the last item of the core).
 */
export function repeatPosition(k: number, len: number): { q: number; r: number; pos: number } {
  const q = Math.floor(k / len);
  const r = k % len;
  return { q, r, pos: r === 0 ? len : r };
}

/** Number of tiles at step n of the growing pattern a·n² + b·n + c. */
export const growTerm = (a: number, b: number, c: number, n: number) => a * n * n + b * n + c;

/** Successive differences of a sequence. */
export const differences = (seq: number[]) => seq.slice(1).map((v, i) => v - seq[i]);

/** The rule a·n² + b·n + c written nicely: "n² + 2n + 1", "2n − 1", "−n + 10", "3", "0". */
export function formatRule(a: number, b: number, c: number): string {
  const terms: { coef: number; sym: string }[] = [
    { coef: a, sym: "n²" },
    { coef: b, sym: "n" },
    { coef: c, sym: "" },
  ].filter((x) => x.coef !== 0);
  if (!terms.length) return "0";
  return terms
    .map(({ coef, sym }, i) => {
      const mag = Math.abs(coef);
      const body = sym && mag === 1 ? sym : `${mag}${sym}`;
      if (i === 0) return coef < 0 ? `−${body}` : body;
      return coef < 0 ? ` − ${body}` : ` + ${body}`;
    })
    .join("");
}

/** One term of the rule on its own ("2n²", "−n", "+3" style without the plus): used in the legend. */
export function formatTerm(coef: number, sym: "n²" | "n" | ""): string {
  const mag = Math.abs(coef);
  const body = sym && mag === 1 ? sym : `${mag}${sym}`;
  return coef < 0 ? `−${body}` : body;
}

export type TilePart = "square" | "column" | "single";
export interface Tile {
  x: number;
  y: number;
  part: TilePart;
  removed: boolean;
}

/**
 * Tiles for step n. Positive parts are drawn (a squares of n × n, then b
 * columns of n, then c single tiles); negative parts are shown as tiles taken
 * away (marked `removed`) from the end of the drawing, so the tiles that are
 * not removed always number exactly a·n² + b·n + c. Coordinates are in tile
 * units with y = 0 the bottom row. Returns null when the count would be negative.
 */
export function growLayout(a: number, b: number, c: number, n: number): { tiles: Tile[]; width: number; height: number } | null {
  if (growTerm(a, b, c, n) < 0) return null;
  const pos = (v: number) => Math.max(0, v);
  const neg = (v: number) => Math.max(0, -v);
  const squares: Tile[] = [];
  const columns: Tile[] = [];
  const singles: Tile[] = [];
  let x = 0;
  for (let s = 0; s < pos(a); s++) {
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) squares.push({ x: x + i, y: j, part: "square", removed: false });
    x += n + 0.5;
  }
  for (let s = 0; s < pos(b); s++) {
    for (let j = 0; j < n; j++) columns.push({ x, y: j, part: "column", removed: false });
    x += s === pos(b) - 1 ? 1.5 : 1.2;
  }
  const colH = Math.max(1, Math.min(pos(c), Math.max(n, 2)));
  for (let k = 0; k < pos(c); k++) singles.push({ x: x + Math.floor(k / colH), y: k % colH, part: "single", removed: false });
  // Removal order: squares are taken from their last column first, then columns, then single tiles.
  const ordered = [...singles, ...columns, ...squares];
  let take = neg(a) * n * n + neg(b) * n + neg(c);
  for (let i = ordered.length - 1; i >= 0 && take > 0; i--, take--) ordered[i].removed = true;
  const tiles = [...squares, ...columns, ...singles];
  const width = tiles.length ? Math.max(...tiles.map((t) => t.x)) + 1 : 1;
  const height = tiles.length ? Math.max(...tiles.map((t) => t.y)) + 1 : 1;
  return { tiles, width, height };
}

/** Clamp the growing-pattern coefficients to what can be drawn. */
export const clampCoefficients = (a: number, b: number, c: number) => ({
  a: Math.max(-3, Math.min(3, a)),
  b: Math.max(-10, Math.min(10, b)),
  c: Math.max(-20, Math.min(20, c)),
});
