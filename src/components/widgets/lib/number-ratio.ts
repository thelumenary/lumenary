/** Ratios and rates for the DoubleNumberLine widget. */
import { gcd } from "./number-common";
import { decimalText, mixedText, reduce, type Frac } from "./number-fraction";

/** The ratio a : b in simplest form, and the factor removed. */
export function simplestRatio(a: number, b: number): { p: number; q: number; g: number } {
  const g = gcd(a, b) || 1;
  return { p: a / g, q: b / g, g };
}

/** The bottom amount that matches `top` on the top line, for the ratio a : b (exact). */
export function matchBottom(top: number, a: number, b: number): Frac {
  return reduce({ n: top * b, d: a });
}

/** Print a rational the friendliest exact way: "8", "7.5", "2 2/3", "1/3". */
export function rationalText(f: Frac): string {
  const r = reduce(f);
  if (r.d === 1) return `${r.n}`;
  return decimalText(r, 3) ?? mixedText(r);
}

/**
 * Step for a slider over the top amount 0..max·a. Every multiple of a is reachable,
 * values stay whole numbers, and there are at most `positions` stops.
 */
export function sliderStep(a: number, max: number, positions = 240): number {
  if (max * a <= positions) return 1;
  let best = 1;
  for (let d = 1; d <= a; d++) if (a % d === 0 && max * d <= positions) best = d;
  return a / best;
}
