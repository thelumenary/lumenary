/**
 * Small helpers shared by the number-and-arithmetic widgets (TenFrame, PlaceValue,
 * FractionBars, NumberGrid, BalanceScale, DoubleNumberLine).
 * Everything here is pure, so it is unit-tested in tests/widgets-number.test.ts.
 */

/** Coerce an MDX prop to an integer in [lo, hi]. Non-numbers fall back to `fallback` (also clamped). */
export function clampInt(value: unknown, lo: number, hi: number, fallback: number): number {
  const x = typeof value === "number" ? value : typeof value === "string" && value.trim() !== "" ? Number(value) : NaN;
  const v = Number.isFinite(x) ? Math.round(x) : fallback;
  return Math.min(hi, Math.max(lo, v));
}

/** One of a fixed set of strings, or the fallback. */
export function oneOf<T extends string>(value: unknown, options: readonly T[], fallback: T): T {
  return typeof value === "string" && (options as readonly string[]).includes(value) ? (value as T) : fallback;
}

export function gcd(a: number, b: number): number {
  let x = Math.abs(Math.trunc(a));
  let y = Math.abs(Math.trunc(b));
  while (y) [x, y] = [y, x % y];
  return x;
}

export function lcm(a: number, b: number): number {
  if (a === 0 || b === 0) return 0;
  return Math.abs((a / gcd(a, b)) * b);
}

/** Integer with a typographic minus sign (−3), as the other widgets print negatives. */
export const signed = (v: number) => (v < 0 ? `−${-v}` : `${v}`);

/** True when the reader asked the system for reduced motion (always false on the server). */
export function prefersReducedMotion(): boolean {
  return typeof window !== "undefined" && typeof window.matchMedia === "function" && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
}

/** Integers lo..hi inclusive. */
export const range = (lo: number, hi: number) => Array.from({ length: Math.max(0, hi - lo + 1) }, (_, i) => lo + i);
