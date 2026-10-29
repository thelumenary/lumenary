/**
 * Small, dependency-free helpers shared by the shape-data widgets
 * (ShapeExplorer, AreaGrid, AnalogClock, RulerMeasure, PatternMaker, DataChart, Spinner).
 * Everything here is pure so it can be unit-tested and rendered identically on server and client.
 */

export const clamp = (v: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, v));

/** Read a number from an MDX prop (number or numeric string); anything else gives NaN. */
export function asNumber(v: unknown): number {
  if (typeof v === "number") return v;
  if (typeof v === "string" && v.trim() !== "") return Number(v);
  return NaN;
}

/** An MDX prop coerced to an integer in [lo, hi]; malformed input gives the fallback. */
export function toInt(v: unknown, fallback: number, lo: number, hi: number): number {
  const x = asNumber(v);
  if (!Number.isFinite(x)) return clamp(Math.round(fallback), lo, hi);
  return clamp(Math.round(x), lo, hi);
}

/** One of a fixed set of string options, else the fallback. */
export function oneOf<T extends string>(v: unknown, options: readonly T[], fallback: T): T {
  return typeof v === "string" && (options as readonly string[]).includes(v) ? (v as T) : fallback;
}

/** A list of allowed strings from an MDX array prop (unknown entries are dropped, order kept, no duplicates). */
export function listOf<T extends string>(v: unknown, options: readonly T[]): T[] {
  if (!Array.isArray(v)) return [];
  const out: T[] = [];
  for (const x of v) if (typeof x === "string" && (options as readonly string[]).includes(x) && !out.includes(x as T)) out.push(x as T);
  return out;
}

export const gcd = (a: number, b: number): number => {
  a = Math.abs(Math.round(a));
  b = Math.abs(Math.round(b));
  while (b) [a, b] = [b, a % b];
  return a;
};

/** Lowest terms of p/q (q > 0). */
export function simplify(p: number, q: number): [number, number] {
  if (q === 0) return [p, q];
  const g = gcd(p, q) || 1;
  const s = q < 0 ? -1 : 1;
  return [(s * p) / g, (s * q) / g];
}

/** True when x has at most `dp` decimal places (up to floating-point noise). */
export function isExactTo(x: number, dp = 2): boolean {
  const k = 10 ** dp;
  return Math.abs(Math.round(x * k) - x * k) < 1e-6;
}

/** Round to `dp` decimal places and report whether that is exact. */
export function roundTo(x: number, dp = 2): { value: number; exact: boolean } {
  const k = 10 ** dp;
  const value = Math.round(x * k) / k;
  return { value: Object.is(value, -0) ? 0 : value, exact: isExactTo(x, dp) };
}

/** A signed number for diagrams and formulas, written with the true minus sign (−), not a hyphen. */
export const signed = (v: number) => (v < 0 ? `−${-v}` : `${v}`);

/**
 * Mulberry32: a tiny seeded PRNG. Pure step function: give it the state, get
 * a number in [0, 1) and the next state. Used instead of Math.random() so that
 * simulations are reproducible and identical on server and client.
 */
export function nextRandom(state: number): [number, number] {
  const s = (state + 0x6d2b79f5) >>> 0;
  let t = s;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  const u = ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  return [u, s];
}

/** A well-mixed 32-bit seed from a small integer (so seeds 1, 2, 3… give unrelated streams). */
export function seedFrom(n: number): number {
  let h = (Math.round(n) ^ 0x9e3779b9) >>> 0;
  h = Math.imul(h ^ (h >>> 16), 0x85ebca6b) >>> 0;
  h = Math.imul(h ^ (h >>> 13), 0xc2b2ae35) >>> 0;
  return (h ^ (h >>> 16)) >>> 0;
}

/** Named colours available to lesson authors, mapped to theme tokens (they adapt to dark mode). */
export const NAMED_COLOURS = {
  red: "var(--bad)",
  orange: "var(--human)",
  yellow: "var(--gold)",
  green: "var(--good)",
  teal: "var(--compute)",
  blue: "var(--sky)",
  purple: "var(--formal)",
} as const;
export type ColourName = keyof typeof NAMED_COLOURS;
export const COLOUR_NAMES = Object.keys(NAMED_COLOURS) as ColourName[];
/** Order used when an author does not name colours: neighbours stay easy to tell apart. */
export const DEFAULT_COLOUR_ORDER: ColourName[] = ["blue", "orange", "green", "purple", "yellow", "teal", "red"];
