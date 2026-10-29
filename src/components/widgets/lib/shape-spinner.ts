/**
 * Spinner helpers: sector parsing, the sector under an angle, seeded spins
 * (the landing angle decides the outcome, exactly as on a real spinner) and
 * exact sector fractions.
 */
import { COLOUR_NAMES, DEFAULT_COLOUR_ORDER, asNumber, nextRandom, simplify, type ColourName } from "./shape-util";

export interface SectorSpec {
  /** Author's label, or null to use a translated default. */
  label: string | null;
  weight: number;
  colour: ColourName;
}

export const MAX_SECTORS = 10;

/** Sectors from the `sectors` prop ({label, weight, color?}); malformed entries are ignored. Null when none are valid. */
export function parseSectors(sectors: unknown): SectorSpec[] | null {
  if (!Array.isArray(sectors)) return null;
  const raw: { label: string; weight: number; colour: ColourName | null }[] = [];
  for (const s of sectors) {
    if (!s || typeof s !== "object") continue;
    const rec = s as Record<string, unknown>;
    const label = typeof rec.label === "string" || typeof rec.label === "number" ? String(rec.label).trim().slice(0, 20) : "";
    const w = rec.weight === undefined ? 1 : asNumber(rec.weight);
    if (!label || !Number.isFinite(w) || w <= 0) continue;
    const c = rec.color ?? rec.colour;
    const colour = typeof c === "string" && (COLOUR_NAMES as string[]).includes(c.toLowerCase()) ? (c.toLowerCase() as ColourName) : null;
    raw.push({ label, weight: Math.min(w, 1000), colour });
    if (raw.length >= MAX_SECTORS) break;
  }
  if (!raw.length) return null;
  const used = new Set(raw.map((r) => r.colour).filter(Boolean));
  const free = DEFAULT_COLOUR_ORDER.filter((c) => !used.has(c));
  let k = 0;
  return raw.map((r) => ({ label: r.label, weight: r.weight, colour: r.colour ?? free[k++ % Math.max(1, free.length)] ?? DEFAULT_COLOUR_ORDER[k % DEFAULT_COLOUR_ORDER.length] }));
}

/** The default spinner: red and blue quarters and a green half. */
export const DEFAULT_SECTORS: SectorSpec[] = [
  { label: null, weight: 1, colour: "red" },
  { label: null, weight: 1, colour: "blue" },
  { label: null, weight: 2, colour: "green" },
];

/** Start of each sector as a fraction of a full turn (clockwise from 12), plus 1 at the end. */
export function cumulative(weights: number[]): number[] {
  const total = weights.reduce((s, w) => s + w, 0);
  const out = [0];
  let acc = 0;
  for (const w of weights) {
    acc += w;
    out.push(acc / total);
  }
  out[out.length - 1] = 1;
  return out;
}

/** The sector under the pointer at a fraction u ∈ [0, 1) of a full turn. */
export function sectorAt(u: number, weights: number[]): number {
  const cum = cumulative(weights);
  for (let i = 0; i < weights.length; i++) if (u < cum[i + 1]) return i;
  return weights.length - 1;
}

/** k seeded spins: returns the outcomes in order, the last landing fraction and the next PRNG state. */
export function spinMany(state: number, k: number, weights: number[]): { outcomes: number[]; lastU: number; state: number } {
  const outcomes: number[] = [];
  let s = state;
  let lastU = 0;
  for (let i = 0; i < k; i++) {
    const [u, next] = nextRandom(s);
    s = next;
    lastU = u;
    outcomes.push(sectorAt(u, weights));
  }
  return { outcomes, lastU, state: s };
}

/** Exact fraction of the spinner for sector i, e.g. "1/4" (null when the weights are not whole numbers). */
export function sectorFraction(weights: number[], i: number): string | null {
  if (!weights.every((w) => Number.isInteger(w))) return null;
  const total = weights.reduce((s, w) => s + w, 0);
  const [p, q] = simplify(weights[i], total);
  return q === 1 ? `${p}` : `${p}/${q}`;
}

/** SVG path of a sector of a circle from fraction f0 to f1 of a turn (clockwise from 12). */
export function sectorPath(cx: number, cy: number, r: number, f0: number, f1: number): string {
  if (f1 - f0 >= 1 - 1e-9) return `M${cx} ${cy - r} A${r} ${r} 0 1 1 ${cx - 0.01} ${cy - r} Z`;
  const p = (f: number) => `${cx + r * Math.sin(2 * Math.PI * f)} ${cy - r * Math.cos(2 * Math.PI * f)}`;
  return `M${cx} ${cy} L${p(f0)} A${r} ${r} 0 ${f1 - f0 > 0.5 ? 1 : 0} 1 ${p(f1)} Z`;
}
