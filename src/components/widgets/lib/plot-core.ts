/**
 * Plotting core shared by the analysis widgets: linear scales, "nice" tick
 * values (including multiples of π), robust sampling of curves that breaks at
 * poles and jumps instead of drawing false vertical lines, polyline clipping,
 * numerical integration and number formatting. Pure functions, unit-tested.
 */

export type Range = [number, number];
export type Pt = [number, number];

/* ---------------------------------------------------------------------------
 * Numbers
 * ------------------------------------------------------------------------- */

export const clamp = (v: number, lo: number, hi: number) => (v < lo ? lo : v > hi ? hi : v);
export const isFiniteNum = (v: unknown): v is number => typeof v === "number" && Number.isFinite(v);

const SUPERSCRIPT: Record<string, string> = { "-": "⁻", "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" };

/**
 * Compact display of a number in formulas and read-outs: at most `digits`
 * decimals, trailing zeros trimmed, a true minus sign, scientific notation for
 * very large or very small magnitudes.
 */
export function fmt(v: number, digits = 3): string {
  if (Number.isNaN(v)) return "undefined";
  if (v === Infinity) return "∞";
  if (v === -Infinity) return "−∞";
  const a = Math.abs(v);
  // Floating-point dust such as sin(π) ≈ 1.2e-16 is shown as 0.
  if (a < 1e-12) return "0";
  if (a >= 1e6 || a < Math.pow(10, -digits) / 2) {
    const exp = Math.floor(Math.log10(a));
    const mant = v / Math.pow(10, exp);
    const m = trim(mant.toFixed(Math.min(2, digits)));
    return `${m}×10${String(exp).replace(/[-0-9]/g, (c) => SUPERSCRIPT[c])}`.replace(/^-/, "−");
  }
  let s = trim(v.toFixed(digits));
  if (s === "-0") s = "0";
  return s.replace(/^-/, "−");
}
const trim = (s: string) => (s.includes(".") ? s.replace(/0+$/, "").replace(/\.$/, "") : s);

/** Signed display for "+ 3" / "− 3" inside formulas. */
export function fmtSigned(v: number, digits = 3): string {
  const s = fmt(Math.abs(v), digits);
  return v < 0 ? `− ${s}` : `+ ${s}`;
}

/* ---------------------------------------------------------------------------
 * Scales and ticks
 * ------------------------------------------------------------------------- */

export interface Scale {
  (v: number): number;
  invert: (p: number) => number;
  domain: Range;
  range: Range;
}

export function linearScale(domain: Range, range: Range): Scale {
  const [d0, d1] = domain;
  const [r0, r1] = range;
  const k = d1 === d0 ? 0 : (r1 - r0) / (d1 - d0);
  const s = ((v: number) => r0 + (v - d0) * k) as Scale;
  s.invert = (p: number) => (k === 0 ? d0 : d0 + (p - r0) / k);
  s.domain = [d0, d1];
  s.range = [r0, r1];
  return s;
}

/** A "nice" step (1, 2 or 5 times a power of ten) giving roughly `target` intervals over `span`. */
export function niceStep(span: number, target: number): number {
  if (!(span > 0) || !(target > 0)) return 1;
  const raw = span / target;
  const p = Math.pow(10, Math.floor(Math.log10(raw)));
  const f = raw / p;
  const m = f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10;
  return m * p;
}

export interface Ticks {
  step: number;
  values: number[];
  labels: string[];
}

/** Decimal places needed to print multiples of `step` exactly. */
export function stepDecimals(step: number): number {
  if (!(step > 0)) return 0;
  return Math.max(0, Math.min(10, -Math.floor(Math.log10(step) + 1e-9)));
}

export function niceTicks(min: number, max: number, target = 8): Ticks {
  const step = niceStep(max - min, target);
  const dec = stepDecimals(step);
  const values: number[] = [];
  const first = Math.ceil(min / step - 1e-9);
  const last = Math.floor(max / step + 1e-9);
  for (let k = first; k <= last && values.length < 200; k++) values.push(Number((k * step).toFixed(dec)));
  const labels = values.map((v) => {
    if (Math.abs(v) >= 1e6 || (Math.abs(v) < 1e-4 && v !== 0)) return fmt(v, 2);
    const s = trim(v.toFixed(dec));
    return (s === "-0" ? "0" : s).replace(/^-/, "−");
  });
  return { step, values, labels };
}

const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b));

/** "π/2", "−3π/4", "2π" for k·π/d. */
export function piLabel(k: number, d: number): string {
  if (k === 0) return "0";
  const g = gcd(Math.abs(k), d);
  const num = k / g;
  const den = d / g;
  const sign = num < 0 ? "−" : "";
  const a = Math.abs(num);
  const top = `${a === 1 ? "" : a}π`;
  return den === 1 ? `${sign}${top}` : `${sign}${top}/${den}`;
}

/** Ticks at multiples of π/d, choosing d so there are about `target` of them. */
export function piTicks(min: number, max: number, target = 8): Ticks {
  const candidates: { step: number; k: number; d: number }[] = [
    { step: Math.PI / 6, k: 1, d: 6 },
    { step: Math.PI / 4, k: 1, d: 4 },
    { step: Math.PI / 2, k: 1, d: 2 },
    { step: Math.PI, k: 1, d: 1 },
    { step: 2 * Math.PI, k: 2, d: 1 },
    { step: 4 * Math.PI, k: 4, d: 1 },
    { step: 10 * Math.PI, k: 10, d: 1 },
  ];
  const span = max - min;
  let best = candidates[0];
  for (const c of candidates) if (span / c.step <= target + 1) {
    best = c;
    break;
  }
  if (span / best.step > target + 1) best = candidates[candidates.length - 1];
  const values: number[] = [];
  const labels: string[] = [];
  const first = Math.ceil(min / best.step - 1e-9);
  const last = Math.floor(max / best.step + 1e-9);
  for (let i = first; i <= last && values.length < 200; i++) {
    values.push(i * best.step);
    labels.push(piLabel(i * best.k, best.d));
  }
  return { step: best.step, values, labels };
}

/** True when a window looks like it was given in multiples of π (e.g. [-2π, 2π] or [0, π]). */
export function looksLikePiRange(min: number, max: number): boolean {
  const q = Math.PI / 4;
  const isPi = (v: number) => v !== 0 && Math.abs(v / q - Math.round(v / q)) < 1e-6 && Math.abs(v - Math.round(v)) > 1e-6;
  return (isPi(min) || min === 0) && (isPi(max) || max === 0) && (isPi(min) || isPi(max));
}

/**
 * Expand one of the two windows so that one unit has the same length on both
 * axes in a `w`×`h` pixel box (the "equal aspect" used for geometry pictures).
 */
export function fitEqualAspect(x: Range, y: Range, w: number, h: number): { x: Range; y: Range } {
  const ux = (x[1] - x[0]) / w;
  const uy = (y[1] - y[0]) / h;
  if (!(ux > 0) || !(uy > 0)) return { x, y };
  if (ux > uy) {
    const c = (y[0] + y[1]) / 2;
    const half = (ux * h) / 2;
    return { x, y: [c - half, c + half] };
  }
  const c = (x[0] + x[1]) / 2;
  const half = (uy * w) / 2;
  return { x: [c - half, c + half], y };
}

/**
 * A window that shows "most" of the values: ignores the extreme 2 % at each
 * end (so a pole does not flatten the picture), pads by 10 % and snaps to
 * nice numbers. `include` values (e.g. 0) are kept in view when close.
 */
export function autoRange(values: readonly number[], fallback: Range = [-5, 5], include: readonly number[] = []): Range {
  const v = values.filter(Number.isFinite).sort((a, b) => a - b);
  if (v.length === 0) return [fallback[0], fallback[1]];
  const q = (p: number) => v[Math.min(v.length - 1, Math.max(0, Math.round(p * (v.length - 1))))];
  let lo = q(0.02);
  let hi = q(0.98);
  // When there is no pole the true extremes are better than percentiles.
  if (v[v.length - 1] - v[0] <= 3 * (hi - lo) || hi === lo) {
    lo = v[0];
    hi = v[v.length - 1];
  }
  for (const inc of include) {
    const span = Math.max(hi - lo, 1e-9);
    if (inc < lo && lo - inc < span) lo = inc;
    if (inc > hi && inc - hi < span) hi = inc;
  }
  if (hi - lo < 1e-9) {
    const pad = Math.max(1, Math.abs(lo) * 0.5);
    return [lo - pad, hi + pad];
  }
  const pad = (hi - lo) * 0.1;
  lo -= pad;
  hi += pad;
  const step = niceStep(hi - lo, 8);
  return [Math.floor(lo / step) * step, Math.ceil(hi / step) * step];
}

/* ---------------------------------------------------------------------------
 * Sampling and clipping
 * ------------------------------------------------------------------------- */

/**
 * Bisect between two finite samples whose values differ a lot. Returns the
 * one-sided limits around a jump/pole, or null when the function turns out to
 * be continuous there (the gap shrinks as the interval shrinks).
 */
function findJump(f: (x: number) => number, x0: number, y0: number, x1: number, y1: number, tol: number): { xl: number; yl: number; xr: number; yr: number } | null {
  for (let k = 0; k < 48; k++) {
    const xm = (x0 + x1) / 2;
    if (xm === x0 || xm === x1) break;
    const ym = f(xm);
    if (!Number.isFinite(ym)) return { xl: x0, yl: y0, xr: x1, yr: y1 };
    if (Math.abs(ym - y0) >= Math.abs(y1 - ym)) {
      x1 = xm;
      y1 = ym;
    } else {
      x0 = xm;
      y0 = ym;
    }
    if (Math.abs(y1 - y0) < tol) return null;
  }
  return Math.abs(y1 - y0) < tol ? null : { xl: x0, yl: y0, xr: x1, yr: y1 };
}

/** Bisect from a finite sample towards an undefined one to find where the domain ends. */
function domainEdge(f: (x: number) => number, xIn: number, xOut: number): Pt | null {
  let a = xIn;
  let b = xOut;
  let best: Pt | null = null;
  for (let k = 0; k < 40; k++) {
    const m = (a + b) / 2;
    if (m === a || m === b) break;
    const y = f(m);
    if (Number.isFinite(y)) {
      best = [m, y];
      a = m;
    } else b = m;
  }
  return best;
}

export interface SampleOptions {
  /** Number of uniform samples (default 600). */
  n?: number;
  /** The visible y-window; used to decide what counts as a jump and to clip. */
  y: Range;
}

/**
 * Sample y = f(x) on [a, b] as a list of polylines. The curve is split where
 * f is undefined and at jump discontinuities and poles (so tan x shows no
 * vertical lines), and clipped to a padded copy of the visible window.
 */
export function sampleFunction(f: (x: number) => number, [a, b]: Range, opts: SampleOptions): Pt[][] {
  const n = Math.max(16, Math.min(4000, Math.round(opts.n ?? 600)));
  const [ylo, yhi] = opts.y;
  const H = Math.max(yhi - ylo, 1e-12);
  const tol = H * 0.004;
  const lines: Pt[][] = [];
  let cur: Pt[] = [];
  const flush = () => {
    if (cur.length > 0) lines.push(cur);
    cur = [];
  };
  let px = NaN;
  let py = NaN;
  for (let i = 0; i <= n; i++) {
    const x = a + ((b - a) * i) / n;
    const y = f(x);
    const ok = Number.isFinite(y);
    const prevOk = Number.isFinite(py);
    if (ok && !prevOk && i > 0) {
      const edge = domainEdge(f, x, px);
      if (edge) cur.push(edge);
    }
    if (!ok && prevOk) {
      const edge = domainEdge(f, px, x);
      if (edge) cur.push(edge);
      flush();
    }
    if (ok) {
      if (prevOk && Math.abs(y - py) > H * 0.02) {
        const jump = findJump(f, px, py, x, y, tol);
        if (jump) {
          cur.push([jump.xl, jump.yl]);
          flush();
          cur.push([jump.xr, jump.yr]);
        }
      }
      cur.push([x, y]);
    }
    px = x;
    py = y;
  }
  flush();
  return clipPolylines(lines, { x: [a - (b - a), b + (b - a)], y: [ylo - H, yhi + H] });
}

/**
 * Sample a parametric curve (x(t), y(t)) for t in [t0, t1], splitting where it
 * is undefined or jumps (relative to the visible window) and clipping.
 */
export function sampleParametric(fx: (t: number) => number, fy: (t: number) => number, [t0, t1]: Range, view: { x: Range; y: Range }, n = 1200): Pt[][] {
  n = Math.max(16, Math.min(6000, Math.round(n)));
  const W = Math.max(view.x[1] - view.x[0], 1e-12);
  const H = Math.max(view.y[1] - view.y[0], 1e-12);
  const dist = (p: Pt, q: Pt) => Math.hypot((p[0] - q[0]) / W, (p[1] - q[1]) / H);
  const at = (t: number): Pt => [fx(t), fy(t)];
  const okPt = (p: Pt) => Number.isFinite(p[0]) && Number.isFinite(p[1]);
  const lines: Pt[][] = [];
  let cur: Pt[] = [];
  const flush = () => {
    if (cur.length > 0) lines.push(cur);
    cur = [];
  };
  let pt = NaN;
  let pp: Pt = [NaN, NaN];
  for (let i = 0; i <= n; i++) {
    const t = t0 + ((t1 - t0) * i) / n;
    const p = at(t);
    if (!okPt(p)) {
      flush();
    } else {
      if (okPt(pp) && dist(p, pp) > 0.08) {
        // Bisect in t: a real jump keeps its size, a fast but continuous stretch shrinks.
        let ta = pt;
        let tb = t;
        let a = pp;
        let b = p;
        let broken = false;
        for (let k = 0; k < 40; k++) {
          const tm = (ta + tb) / 2;
          const m = at(tm);
          if (!okPt(m)) {
            broken = true;
            break;
          }
          if (dist(a, m) >= dist(m, b)) {
            tb = tm;
            b = m;
          } else {
            ta = tm;
            a = m;
          }
          if (dist(a, b) < 0.004) break;
        }
        if (broken || dist(a, b) >= 0.004) {
          cur.push(a);
          flush();
          cur.push(b);
        }
      }
      cur.push(p);
    }
    pt = t;
    pp = p;
  }
  flush();
  return clipPolylines(lines, { x: [view.x[0] - W, view.x[1] + W], y: [view.y[0] - H, view.y[1] + H] });
}

/** Liang–Barsky clipping of polylines to a box; pieces leaving the box become separate polylines. */
export function clipPolylines(lines: Pt[][], box: { x: Range; y: Range }): Pt[][] {
  const out: Pt[][] = [];
  const [xmin, xmax] = box.x;
  const [ymin, ymax] = box.y;
  const inside = (p: Pt) => p[0] >= xmin && p[0] <= xmax && p[1] >= ymin && p[1] <= ymax;
  for (const line of lines) {
    if (line.length === 1) {
      if (inside(line[0])) out.push([line[0]]);
      continue;
    }
    let cur: Pt[] = [];
    for (let i = 1; i < line.length; i++) {
      const [x0, y0] = line[i - 1];
      const [x1, y1] = line[i];
      const dx = x1 - x0;
      const dy = y1 - y0;
      let u0 = 0;
      let u1 = 1;
      let visible = true;
      for (const [p, q] of [
        [-dx, x0 - xmin],
        [dx, xmax - x0],
        [-dy, y0 - ymin],
        [dy, ymax - y0],
      ] as const) {
        if (p === 0) {
          if (q < 0) {
            visible = false;
            break;
          }
        } else {
          const r = q / p;
          if (p < 0) {
            if (r > u1) {
              visible = false;
              break;
            }
            if (r > u0) u0 = r;
          } else {
            if (r < u0) {
              visible = false;
              break;
            }
            if (r < u1) u1 = r;
          }
        }
      }
      if (!visible) {
        if (cur.length) out.push(cur);
        cur = [];
        continue;
      }
      const a: Pt = u0 === 0 ? [x0, y0] : [x0 + u0 * dx, y0 + u0 * dy];
      const b: Pt = u1 === 1 ? [x1, y1] : [x0 + u1 * dx, y0 + u1 * dy];
      if (cur.length === 0 || u0 > 0) {
        if (cur.length) out.push(cur);
        cur = [a];
      }
      cur.push(b);
      if (u1 < 1) {
        out.push(cur);
        cur = [];
      }
    }
    if (cur.length) out.push(cur);
  }
  return out;
}

/** SVG path data for polylines in data coordinates. */
export function pathD(lines: readonly (readonly Pt[])[], sx: (v: number) => number, sy: (v: number) => number): string {
  let d = "";
  for (const line of lines) {
    if (line.length === 0) continue;
    for (let i = 0; i < line.length; i++) {
      const X = sx(line[i][0]);
      const Y = sy(line[i][1]);
      d += `${i === 0 ? "M" : "L"}${X.toFixed(2)} ${Y.toFixed(2)}`;
    }
    if (line.length === 1) d += `h0.01`;
  }
  return d;
}

/* ---------------------------------------------------------------------------
 * Numerical integration
 * ------------------------------------------------------------------------- */

/**
 * Adaptive Simpson integration of f over [a, b]. Returns NaN when f is
 * undefined somewhere it is sampled. Good to ~1e-9 for smooth integrands.
 */
export function integrate(f: (x: number) => number, a: number, b: number, tol = 1e-10): number {
  if (a === b) return 0;
  if (a > b) return -integrate(f, b, a, tol);
  let evals = 0;
  const MAX_EVALS = 200000;
  const fa = f(a);
  const fb = f(b);
  const m = (a + b) / 2;
  const fm = f(m);
  if (![fa, fb, fm].every(Number.isFinite)) return NaN;
  const simpson = (a0: number, b0: number, f0: number, fm0: number, f1: number) => ((b0 - a0) / 6) * (f0 + 4 * fm0 + f1);
  const rec = (a0: number, b0: number, f0: number, fm0: number, f1: number, whole: number, eps: number, depth: number): number => {
    const m0 = (a0 + b0) / 2;
    const lm = (a0 + m0) / 2;
    const rm = (m0 + b0) / 2;
    const flm = f(lm);
    const frm = f(rm);
    evals += 2;
    if (!Number.isFinite(flm) || !Number.isFinite(frm)) return NaN;
    const left = simpson(a0, m0, f0, flm, fm0);
    const right = simpson(m0, b0, fm0, frm, f1);
    const diff = left + right - whole;
    if (depth <= 0 || evals > MAX_EVALS || Math.abs(diff) <= 15 * eps) return left + right + diff / 15;
    return rec(a0, m0, f0, flm, fm0, left, eps / 2, depth - 1) + rec(m0, b0, fm0, frm, f1, right, eps / 2, depth - 1);
  };
  return rec(a, b, fa, fm, fb, simpson(a, b, fa, fm, fb), tol, 40);
}

/* ---------------------------------------------------------------------------
 * Seeded randomness (for any simulation; never Math.random during render)
 * ------------------------------------------------------------------------- */

export function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
