import { gcd, lcm } from "./number-common";

/** An exact non-negative rational number n/d (d ≥ 1). Not necessarily in lowest terms. */
export interface Frac {
  n: number;
  d: number;
}

export interface ParsedValue {
  frac: Frac;
  /** How the author wrote it (trimmed), used as the label on number lines. */
  label: string;
  kind: "whole" | "fraction" | "mixed" | "decimal";
}

const LIMIT = 100000;

export const frac = (n: number, d: number): Frac => ({ n, d });

export function reduce(f: Frac): Frac {
  const g = gcd(f.n, f.d) || 1;
  return { n: f.n / g, d: f.d / g };
}

export const valueOf = (f: Frac) => f.n / f.d;

export function compare(a: Frac, b: Frac): -1 | 0 | 1 {
  const l = a.n * b.d;
  const r = b.n * a.d;
  return l < r ? -1 : l > r ? 1 : 0;
}

export const sameValue = (a: Frac, b: Frac) => compare(a, b) === 0;

export function add(a: Frac, b: Frac): Frac {
  return reduce({ n: a.n * b.d + b.n * a.d, d: a.d * b.d });
}

/** a − b (may be negative). */
export function sub(a: Frac, b: Frac): Frac {
  const n = a.n * b.d - b.n * a.d;
  const d = a.d * b.d;
  const g = gcd(n, d) || 1;
  return { n: n / g, d: d / g };
}

/** Rewrite f with denominator `d` (which must be a multiple of f.d). */
export function withDenominator(f: Frac, d: number): Frac {
  return { n: (f.n * d) / f.d, d };
}

export const commonDenominator = (a: Frac, b: Frac) => lcm(a.d, b.d);

/** "3/4", or "2" for a whole number. */
export function fracText(f: Frac): string {
  return f.d === 1 ? `${f.n}` : `${f.n}/${f.d}`;
}

/** "1 1/2" for improper fractions (keeps proper fractions and wholes as they are). */
export function mixedText(f: Frac): string {
  const r = reduce(f);
  if (r.d === 1 || r.n < r.d) return fracText(r);
  const w = Math.floor(r.n / r.d);
  const rest = r.n - w * r.d;
  return rest === 0 ? `${w}` : `${w} ${rest}/${r.d}`;
}

/** Exact decimal expansion if it terminates within `maxDigits` places, else null. */
export function decimalText(f: Frac, maxDigits = 4): string | null {
  const r = reduce(f);
  let d = r.d;
  while (d % 2 === 0) d /= 2;
  while (d % 5 === 0) d /= 5;
  if (d !== 1) return null;
  for (let places = 0; places <= maxDigits; places++) {
    const scaled = (r.n * 10 ** places) / r.d;
    if (Number.isInteger(scaled)) {
      if (places === 0) return `${scaled}`;
      const s = `${scaled}`.padStart(places + 1, "0");
      return `${s.slice(0, -places)}.${s.slice(-places)}`;
    }
  }
  return null;
}

/**
 * Read a non-negative number written as a fraction ("3/4"), a mixed number ("1 1/2"),
 * a whole number ("2") or a decimal ("0.75", ".5", "0,75"). Returns null for anything else,
 * including negatives, zero denominators and absurdly large values.
 */
export function parseValue(raw: unknown): ParsedValue | null {
  if (typeof raw === "number") raw = Number.isFinite(raw) ? String(raw) : "";
  if (typeof raw !== "string") return null;
  const label = raw.trim().replace(/\s+/g, " ");
  const s = label.replace(/[⁄∕÷]/g, "/");
  let m: RegExpMatchArray | null;
  const ok = (f: Frac, kind: ParsedValue["kind"]): ParsedValue | null =>
    f.d >= 1 && f.n >= 0 && f.n <= LIMIT * f.d && f.d <= LIMIT ? { frac: f, label, kind } : null;
  if ((m = s.match(/^(\d+)$/))) return ok({ n: Number(m[1]), d: 1 }, "whole");
  if ((m = s.match(/^(\d+)\s*\/\s*(\d+)$/))) return ok({ n: Number(m[1]), d: Number(m[2]) }, "fraction");
  if ((m = s.match(/^(\d+)\s+(\d+)\s*\/\s*(\d+)$/))) {
    const d = Number(m[3]);
    return ok({ n: Number(m[1]) * d + Number(m[2]), d }, "mixed");
  }
  if ((m = s.match(/^(\d*)[.,](\d{1,6})$/))) {
    const whole = m[1] === "" ? 0 : Number(m[1]);
    const d = 10 ** m[2].length;
    return ok(reduce({ n: whole * d + Number(m[2]), d }), "decimal");
  }
  return null;
}

/** Parse a list of author-supplied values, keeping the good ones and reporting the bad ones. */
export function parseList(raw: unknown): { values: ParsedValue[]; bad: string[] } {
  const items = Array.isArray(raw) ? raw : raw === undefined || raw === null ? [] : [raw];
  const values: ParsedValue[] = [];
  const bad: string[] = [];
  for (const item of items) {
    const p = parseValue(item);
    if (p) values.push(p);
    else bad.push(String(item));
  }
  return { values, bad };
}
