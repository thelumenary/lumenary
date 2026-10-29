/**
 * Pure calculus logic for CalculusLab: difference quotients and a careful
 * numerical derivative (that recognises corners, jumps and vertical
 * tangents), Riemann sums, exact Taylor coefficients of the classic series,
 * and the sampled ε–δ check. Everything here is numerical evidence; the
 * widget labels it as such.
 */

export type Fn = (x: number) => number;

/* ---------------------------------------------------------------------------
 * Derivatives
 * ------------------------------------------------------------------------- */

/** (f(x0 + h) − f(x0)) / h. */
export function differenceQuotient(f: Fn, x0: number, h: number): number {
  if (h === 0) return NaN;
  return (f(x0 + h) - f(x0)) / h;
}

export type DerivativeInfo =
  | { kind: "smooth"; slope: number }
  | { kind: "corner"; left: number; right: number }
  | { kind: "jump" }
  | { kind: "vertical" }
  | { kind: "undefined" };

/**
 * Numerical derivative at x0 with an honest diagnosis. One-sided quotients
 * at two scales tell a smooth point (left and right quotients agree, their
 * gap shrinks with h) from a corner (the gap stays), a jump (f itself does
 * not settle) and a vertical tangent (both quotients blow up).
 */
export function derivativeAt(f: Fn, x0: number): DerivativeInfo {
  const y0 = f(x0);
  if (!Number.isFinite(y0)) return { kind: "undefined" };
  const s = Math.max(1, Math.abs(x0));
  const h1 = 1e-4 * s;
  const h2 = 1e-6 * s;
  const fp1 = f(x0 + h1);
  const fm1 = f(x0 - h1);
  const fp2 = f(x0 + h2);
  const fm2 = f(x0 - h2);
  if (![fp1, fm1, fp2, fm2].every(Number.isFinite)) return { kind: "undefined" };
  // Continuity: the change in f must shrink as h does.
  const tiny = 1e-9 * (1 + Math.abs(y0));
  const jumpR = Math.abs(fp2 - y0) > tiny && Math.abs(fp2 - y0) > 0.5 * Math.abs(fp1 - y0);
  const jumpL = Math.abs(y0 - fm2) > tiny && Math.abs(y0 - fm2) > 0.5 * Math.abs(y0 - fm1);
  if (jumpR || jumpL) return { kind: "jump" };
  const R1 = (fp1 - y0) / h1;
  const L1 = (y0 - fm1) / h1;
  const R2 = (fp2 - y0) / h2;
  const L2 = (y0 - fm2) / h2;
  // A one-sided quotient that keeps growing as h shrinks: vertical tangent (or cusp).
  const grows = (q2: number, q1: number) => Math.abs(q2) > 100 && Math.abs(q2) > 5 * Math.abs(q1);
  if (grows(R2, R1) || grows(L2, L1)) return { kind: "vertical" };
  const scale = Math.max(1, Math.abs(R2), Math.abs(L2));
  const d1 = Math.abs(R1 - L1);
  const d2 = Math.abs(R2 - L2);
  if (d2 > 1e-3 * scale && d2 > 0.3 * d1) return { kind: "corner", left: L2, right: R2 };
  // Central difference with one Richardson step: error O(h⁴) instead of O(h²).
  const h = 1e-5 * s;
  const D = (k: number) => (f(x0 + k) - f(x0 - k)) / (2 * k);
  const slope = (4 * D(h / 2) - D(h)) / 3;
  return Number.isFinite(slope) ? { kind: "smooth", slope } : { kind: "undefined" };
}

/* ---------------------------------------------------------------------------
 * Riemann sums
 * ------------------------------------------------------------------------- */

export type RiemannMethod = "left" | "right" | "midpoint" | "trapezoid";
export const RIEMANN_METHODS: readonly RiemannMethod[] = ["left", "right", "midpoint", "trapezoid"];

export interface RiemannPiece {
  x0: number;
  x1: number;
  /** Height at the left and right edges (equal for rectangles). */
  h0: number;
  h1: number;
  /** Where f was evaluated (for dots on the curve). */
  samples: number[];
}

export interface RiemannResult {
  sum: number;
  pieces: RiemannPiece[];
  ok: boolean;
}

/** Riemann (or trapezoid) sum of f over [a, b] with n equal strips. */
export function riemannSum(f: Fn, a: number, b: number, n: number, method: RiemannMethod): RiemannResult {
  const N = Math.max(1, Math.min(2000, Math.round(Number.isFinite(n) ? n : 1)));
  const dx = (b - a) / N;
  const pieces: RiemannPiece[] = [];
  let sum = 0;
  let ok = Number.isFinite(dx);
  for (let i = 0; i < N && ok; i++) {
    const x0 = a + i * dx;
    const x1 = i === N - 1 ? b : a + (i + 1) * dx;
    let h0: number;
    let h1: number;
    let samples: number[];
    if (method === "trapezoid") {
      h0 = f(x0);
      h1 = f(x1);
      samples = [x0, x1];
      sum += ((h0 + h1) / 2) * (x1 - x0);
    } else {
      const xs = method === "left" ? x0 : method === "right" ? x1 : (x0 + x1) / 2;
      h0 = h1 = f(xs);
      samples = [xs];
      sum += h0 * (x1 - x0);
    }
    if (!Number.isFinite(h0) || !Number.isFinite(h1)) ok = false;
    pieces.push({ x0, x1, h0, h1, samples });
  }
  return { sum: ok ? sum : NaN, pieces, ok };
}

/* ---------------------------------------------------------------------------
 * Taylor polynomials about 0
 * ------------------------------------------------------------------------- */

export type TaylorId = "sin" | "cos" | "exp" | "ln1p" | "geometric" | "atan";
export const TAYLOR_IDS: readonly TaylorId[] = ["sin", "cos", "exp", "ln1p", "geometric", "atan"];

export interface TaylorPreset {
  id: TaylorId;
  f: Fn;
  /** Display name of f (mathematical notation, not translated). */
  label: string;
  /** |c_k| = 1/den(k) (or 0), with sign(k) ∈ {−1, 0, 1}. */
  sign: (k: number) => number;
  den: (k: number) => number;
  /** Whether den(k) is k! (shown as "k!"). */
  factorial: boolean;
  /** Interval of convergence of the series; null = every real number. */
  conv: { lo: number; hi: number; loClosed: boolean; hiClosed: boolean } | null;
}

const fact = (k: number) => {
  let r = 1;
  for (let i = 2; i <= k; i++) r *= i;
  return r;
};

export const TAYLOR: Record<TaylorId, TaylorPreset> = {
  sin: { id: "sin", f: Math.sin, label: "sin x", sign: (k) => (k % 2 === 0 ? 0 : (k - 1) % 4 === 0 ? 1 : -1), den: fact, factorial: true, conv: null },
  cos: { id: "cos", f: Math.cos, label: "cos x", sign: (k) => (k % 2 === 1 ? 0 : k % 4 === 0 ? 1 : -1), den: fact, factorial: true, conv: null },
  exp: { id: "exp", f: Math.exp, label: "eˣ", sign: () => 1, den: fact, factorial: true, conv: null },
  ln1p: { id: "ln1p", f: Math.log1p, label: "ln(1 + x)", sign: (k) => (k === 0 ? 0 : k % 2 === 1 ? 1 : -1), den: (k) => Math.max(1, k), factorial: false, conv: { lo: -1, hi: 1, loClosed: false, hiClosed: true } },
  geometric: { id: "geometric", f: (x) => 1 / (1 - x), label: "1/(1 − x)", sign: () => 1, den: () => 1, factorial: false, conv: { lo: -1, hi: 1, loClosed: false, hiClosed: false } },
  atan: { id: "atan", f: Math.atan, label: "arctan x", sign: (k) => (k % 2 === 0 ? 0 : (k - 1) % 4 === 0 ? 1 : -1), den: (k) => Math.max(1, k), factorial: false, conv: { lo: -1, hi: 1, loClosed: true, hiClosed: true } },
};

/** Coefficient c_k of x^k in the Maclaurin series. */
export function taylorCoefficient(p: TaylorPreset, k: number): number {
  const s = p.sign(k);
  return s === 0 ? 0 : s / p.den(k);
}

/** The Taylor polynomial T_n as a function (Horner's rule). */
export function taylorPolynomial(p: TaylorPreset, n: number): Fn {
  const N = Math.max(0, Math.min(40, Math.round(n)));
  const c = Array.from({ length: N + 1 }, (_, k) => taylorCoefficient(p, k));
  return (x: number) => {
    let y = 0;
    for (let k = N; k >= 0; k--) y = y * x + c[k];
    return y;
  };
}

const SUP: Record<string, string> = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" };
const sup = (k: number) => String(k).replace(/\d/g, (d) => SUP[d]);

/** Display one term without its sign: "1", "x", "x³/3!", "x⁴/4". */
function termText(p: TaylorPreset, k: number): string {
  const d = p.den(k);
  const power = k === 0 ? "" : k === 1 ? "x" : `x${sup(k)}`;
  if (d === 1) return power || "1";
  const den = p.factorial ? `${k}!` : String(d);
  return power ? `${power}/${den}` : `1/${den}`;
}

/**
 * T_n as a readable formula, e.g. "x − x³/3! + x⁵/5!". Long sums keep the
 * first four terms and the last one: "1 + x + x²/2! + x³/3! + ⋯ + x²⁰/20!".
 */
export function taylorFormula(p: TaylorPreset, n: number): string {
  const N = Math.max(0, Math.min(40, Math.round(n)));
  const terms: { k: number; s: number }[] = [];
  for (let k = 0; k <= N; k++) {
    const s = p.sign(k);
    if (s !== 0) terms.push({ k, s });
  }
  if (terms.length === 0) return "0";
  const shown = terms.length > 6 ? [...terms.slice(0, 4), null, terms[terms.length - 1]] : terms;
  let out = "";
  shown.forEach((t, i) => {
    if (t === null) {
      out += " + ⋯";
      return;
    }
    const body = termText(p, t.k);
    if (i === 0) out += t.s < 0 ? `−${body}` : body;
    else out += t.s < 0 ? ` − ${body}` : ` + ${body}`;
  });
  return out;
}

/** Whether x lies in the interval of convergence. */
export function inConvergence(p: TaylorPreset, x: number): boolean {
  const c = p.conv;
  if (!c) return true;
  const loOk = c.loClosed ? x >= c.lo : x > c.lo;
  const hiOk = c.hiClosed ? x <= c.hi : x < c.hi;
  return loOk && hiOk;
}

/* ---------------------------------------------------------------------------
 * The ε–δ game
 * ------------------------------------------------------------------------- */

/** Sample points of the punctured neighbourhood 0 < |x − a| < δ: uniform plus geometric towards a. */
export function puncturedSamples(a: number, delta: number, uniform = 1000, geometric = 60): number[] {
  const xs: number[] = [];
  for (let i = 1; i < uniform; i++) {
    const u = (i / uniform) * delta;
    xs.push(a - u, a + u);
  }
  for (let j = 0; j < geometric; j++) {
    const u = delta * Math.pow(10, -6 * ((j + 1) / geometric)); // from δ·10^-0.1 down to δ·10^-6
    xs.push(a - u, a + u);
  }
  return xs;
}

export interface DeltaCheck {
  ok: boolean;
  /** The failing sample closest to a, if any. */
  badX: number | null;
  /** |f(badX) − L| there. */
  gap: number;
  /** Points actually checked (points where f is undefined are skipped). */
  checked: number;
}

/** Does every sampled x with 0 < |x − a| < δ satisfy |f(x) − L| < ε? */
export function checkDelta(f: Fn, a: number, L: number, eps: number, delta: number): DeltaCheck {
  if (!(delta > 0) || !(eps > 0)) return { ok: false, badX: null, gap: NaN, checked: 0 };
  let checked = 0;
  let badX: number | null = null;
  let gap = NaN;
  for (const x of puncturedSamples(a, delta)) {
    if (x === a) continue;
    const y = f(x);
    if (!Number.isFinite(y)) continue;
    checked++;
    const g = Math.abs(y - L);
    if (!(g < eps) && (badX === null || Math.abs(x - a) < Math.abs(badX - a))) {
      badX = x;
      gap = g;
    }
  }
  return { ok: badX === null && checked > 0, badX, gap, checked };
}

/**
 * Numerical search for the largest δ ≤ maxDelta that works: walk outwards
 * from a on each side to the first failing sample and bisect the boundary.
 * Returns null when even the closest samples fail (no δ works), and
 * maxDelta when nothing in the window fails.
 */
export function largestDelta(f: Fn, a: number, L: number, eps: number, maxDelta: number): number | null {
  if (!(eps > 0) || !(maxDelta > 0)) return null;
  const bad = (x: number) => {
    const y = f(x);
    return Number.isFinite(y) && !(Math.abs(y - L) < eps);
  };
  // Distances from a, increasing: geometric close to a, then uniform.
  const ds: number[] = [];
  for (let j = 60; j >= 1; j--) ds.push(maxDelta * Math.pow(10, -6 * (j / 60)) * 0.999);
  for (let i = 1; i <= 4000; i++) ds.push((i / 4000) * maxDelta);
  ds.sort((p, q) => p - q);
  let best = maxDelta;
  for (const side of [-1, 1]) {
    let prev = 0;
    for (const d of ds) {
      if (d >= best) break;
      if (bad(a + side * d)) {
        if (prev === 0) return null;
        // Bisect between the last good distance and this bad one.
        let lo = prev;
        let hi = d;
        for (let k = 0; k < 50; k++) {
          const m = (lo + hi) / 2;
          if (bad(a + side * m)) hi = m;
          else lo = m;
        }
        best = Math.min(best, lo);
        break;
      }
      prev = d;
    }
  }
  return best;
}

/* ---------------------------------------------------------------------------
 * Logarithmic slider mapping (for h and δ)
 * ------------------------------------------------------------------------- */

/** Slider position v ∈ [0, 100] ↦ value from `max` (v = 0) down to `min` (v = 100), geometrically. */
export function logSliderValue(v: number, max: number, min: number): number {
  const t = Math.min(100, Math.max(0, v)) / 100;
  return max * Math.pow(min / max, t);
}

/** Inverse of logSliderValue. */
export function logSliderPosition(value: number, max: number, min: number): number {
  const c = Math.min(max, Math.max(min, Math.abs(value)));
  return Math.max(0, (100 * Math.log(c / max)) / Math.log(min / max));
}
