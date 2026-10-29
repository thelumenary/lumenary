/**
 * Plane curves and their signed curvature κ = (x′y″ − y′x″) / |r′|³.
 * Arc length and the total curvature ∫ κ ds are computed numerically from the
 * exact derivatives; for a closed regular curve ∫ κ ds = 2π × (turning number),
 * which is Hopf's Umlaufsatz.
 */
import { len2, TAU, type V2 } from "./topo-vec";

export const CURVE_IDS = ["circle", "ellipse", "parabola", "cardioid", "lemniscate", "limacon", "bezier"] as const;
export type CurveId = (typeof CURVE_IDS)[number];
export const isCurveId = (v: unknown): v is CurveId => typeof v === "string" && (CURVE_IDS as readonly string[]).includes(v);

export interface CurveParams {
  /** circle radius */
  R: number;
  /** ellipse: semi-minor axis (semi-major axis is 2) */
  b: number;
  /** parabola y = k x² − 1.2 */
  k: number;
  /** limaçon r = 1 + c cos θ */
  c: number;
  /** cubic Bézier control points */
  ctrl: [V2, V2, V2, V2];
}

/** Slider ranges [min, max, step] for the numeric shape parameters. */
export const PARAM_RANGES = { R: [0.4, 2.2, 0.05], b: [0.3, 2, 0.05], k: [0.1, 0.75, 0.05], c: [0.2, 2.5, 0.05] } as const;
export type NumericParam = keyof typeof PARAM_RANGES;

export const DEFAULT_PARAMS: CurveParams = {
  R: 1.5,
  b: 1.1,
  k: 0.5,
  c: 2,
  ctrl: [[-2.4, -1.2], [-1.2, 1.9], [1.0, -1.9], [2.4, 1.1]],
};

export interface CurveDef {
  id: CurveId;
  closed: boolean;
  range: [number, number];
  /** Position, first and second derivatives with respect to the parameter. */
  eval: (t: number, p: CurveParams) => { r: V2; d1: V2; d2: V2 };
}

/** Polar curve r(θ) with derivatives → Cartesian position (shifted by dx, which leaves curvature unchanged) and derivatives. */
function polar(rr: number, r1: number, r2: number, th: number, dx = 0) {
  const c = Math.cos(th);
  const s = Math.sin(th);
  return {
    r: [rr * c + dx, rr * s] as V2,
    d1: [r1 * c - rr * s, r1 * s + rr * c] as V2,
    d2: [r2 * c - 2 * r1 * s - rr * c, r2 * s + 2 * r1 * c - rr * s] as V2,
  };
}

function numeric(f: (t: number) => V2) {
  return (t: number) => {
    const h = 1e-4;
    const a = f(t - h);
    const b = f(t);
    const c = f(t + h);
    return { r: b, d1: [(c[0] - a[0]) / (2 * h), (c[1] - a[1]) / (2 * h)] as V2, d2: [(c[0] - 2 * b[0] + a[0]) / (h * h), (c[1] - 2 * b[1] + a[1]) / (h * h)] as V2 };
  };
}

const lemniscate = numeric((t) => {
  const s = Math.sin(t);
  const d = 1 + s * s;
  return [(2.4 * Math.cos(t)) / d, (2.4 * s * Math.cos(t)) / d];
});

export const CURVES: Record<CurveId, CurveDef> = {
  circle: { id: "circle", closed: true, range: [0, TAU], eval: (t, p) => polar(p.R, 0, 0, t) },
  ellipse: {
    id: "ellipse",
    closed: true,
    range: [0, TAU],
    eval: (t, p) => ({ r: [2 * Math.cos(t), p.b * Math.sin(t)], d1: [-2 * Math.sin(t), p.b * Math.cos(t)], d2: [-2 * Math.cos(t), -p.b * Math.sin(t)] }),
  },
  parabola: { id: "parabola", closed: false, range: [-2.2, 2.2], eval: (t, p) => ({ r: [t, p.k * t * t - 1.2], d1: [1, 2 * p.k * t], d2: [0, 2 * p.k] }) },
  // r = 1.2 (1 + cos θ): cusp at the origin when θ = π
  cardioid: { id: "cardioid", closed: true, range: [0, TAU], eval: (t) => polar(1.2 * (1 + Math.cos(t)), -1.2 * Math.sin(t), -1.2 * Math.cos(t), t, -1.05) },
  lemniscate: { id: "lemniscate", closed: true, range: [0, TAU], eval: (t) => lemniscate(t) },
  limacon: { id: "limacon", closed: true, range: [0, TAU], eval: (t, p) => polar(1 + p.c * Math.cos(t), -p.c * Math.sin(t), -p.c * Math.cos(t), t, -p.c / 2) },
  bezier: {
    id: "bezier",
    closed: false,
    range: [0, 1],
    eval: (t, p) => {
      const [P0, P1, P2, P3] = p.ctrl;
      const u = 1 - t;
      const r: V2 = [0, 1].map((i) => u * u * u * P0[i] + 3 * u * u * t * P1[i] + 3 * u * t * t * P2[i] + t * t * t * P3[i]) as V2;
      const d1: V2 = [0, 1].map((i) => 3 * (u * u * (P1[i] - P0[i]) + 2 * u * t * (P2[i] - P1[i]) + t * t * (P3[i] - P2[i]))) as V2;
      const d2: V2 = [0, 1].map((i) => 6 * (u * (P2[i] - 2 * P1[i] + P0[i]) + t * (P3[i] - 2 * P2[i] + P1[i]))) as V2;
      return { r, d1, d2 };
    },
  },
};

/** Signed curvature from first and second derivatives (NaN at a singular point where r′ = 0). */
export function curvatureOf(d1: V2, d2: V2): number {
  const sp = len2(d1);
  return (d1[0] * d2[1] - d1[1] * d2[0]) / (sp * sp * sp);
}

export interface Sampled {
  t: number[];
  r: V2[];
  /** Unit tangent at each sample. */
  T: V2[];
  kappa: number[];
  /** Arc length from the start. */
  s: number[];
  length: number;
  /** ∫ κ ds over the curve (midpoint rule in the parameter). */
  totalCurvature: number;
  /** Net change of the tangent angle, measured by unwrapping the tangent direction (radians). */
  tangentTurn: number;
  /** The curve has a point where it stops (r′ ≈ 0), such as the cardioid's cusp. */
  singular: boolean;
}

/**
 * Sample a curve at n + 1 points (midpoints of n equal parameter steps for the
 * integrals, so a cusp at a sample point never produces 0/0).
 */
export function sampleCurve(def: CurveDef, p: CurveParams, n = 2400): Sampled {
  const [a, b] = def.range;
  const h = (b - a) / n;
  const t: number[] = [];
  const r: V2[] = [];
  const T: V2[] = [];
  const kappa: number[] = [];
  const s: number[] = [0];
  let total = 0;
  let maxSpeed = 0;
  let minSpeed = Infinity;
  const speeds: number[] = [];
  for (let i = 0; i <= n; i++) {
    // closed curves are periodic: offset by half a step so no sample sits on a cusp (θ = π for the cardioid)
    const ti = def.closed ? a + (i + 0.5) * h : a + i * h;
    const e = def.eval(ti, p);
    const sp = len2(e.d1);
    const k = curvatureOf(e.d1, e.d2);
    t.push(ti);
    r.push(e.r);
    T.push(sp > 1e-12 ? [e.d1[0] / sp, e.d1[1] / sp] : [1, 0]);
    kappa.push(Number.isFinite(k) ? k : 0);
    speeds.push(sp);
    maxSpeed = Math.max(maxSpeed, sp);
    minSpeed = Math.min(minSpeed, sp);
  }
  for (let i = 1; i <= n; i++) s.push(s[i - 1] + ((speeds[i - 1] + speeds[i]) / 2) * h);
  // ∫ κ |r′| dt by the midpoint rule (exact derivatives at midpoints)
  for (let i = 0; i < n; i++) {
    const e = def.eval(a + (i + 0.5) * h, p);
    const sp = len2(e.d1);
    if (sp < 1e-12) continue;
    total += ((e.d1[0] * e.d2[1] - e.d1[1] * e.d2[0]) / (sp * sp)) * h;
  }
  // tangent turning by unwrapping angles between consecutive unit tangents
  let turnSum = 0;
  for (let i = 1; i <= n; i++) {
    const u = T[i - 1];
    const v = T[i];
    let d = Math.atan2(u[0] * v[1] - u[1] * v[0], u[0] * v[0] + u[1] * v[1]);
    // across a cusp the tangent flips by ±π: that jump is not part of ∫ κ ds
    if (Math.abs(Math.abs(d) - Math.PI) < 0.2) d = 0;
    turnSum += d;
  }
  return { t, r, T, kappa, s, length: s[n], totalCurvature: total, tangentTurn: turnSum, singular: minSpeed < 1e-3 * maxSpeed };
}

/** Position, unit tangent, unit normal (tangent turned +90°) and curvature at arc-length fraction u ∈ [0, 1]. */
export function frameAt(def: CurveDef, p: CurveParams, smp: Sampled, u: number) {
  const target = Math.max(0, Math.min(1, u)) * smp.length;
  let lo = 0;
  let hi = smp.s.length - 1;
  while (hi - lo > 1) {
    const mid = (lo + hi) >> 1;
    if (smp.s[mid] < target) lo = mid;
    else hi = mid;
  }
  const seg = smp.s[hi] - smp.s[lo];
  const f = seg > 0 ? (target - smp.s[lo]) / seg : 0;
  const tt = smp.t[lo] + (smp.t[hi] - smp.t[lo]) * f;
  const e = def.eval(tt, p);
  const sp = len2(e.d1);
  const T: V2 = sp > 1e-12 ? [e.d1[0] / sp, e.d1[1] / sp] : smp.T[lo];
  const N: V2 = [-T[1], T[0]];
  const k = sp > 1e-9 ? curvatureOf(e.d1, e.d2) : NaN;
  return { r: e.r, T, N, kappa: k, s: target };
}

/** Clamp and sanitise curve parameters coming from props or sliders. */
export function sanitizeParams(p: Partial<CurveParams>): CurveParams {
  const num = (v: unknown, d: number, lo: number, hi: number) => (typeof v === "number" && Number.isFinite(v) ? Math.min(hi, Math.max(lo, v)) : d);
  const ctrl = Array.isArray(p.ctrl) && p.ctrl.length === 4 && p.ctrl.every((q) => Array.isArray(q) && q.length >= 2 && q.every((x) => typeof x === "number" && Number.isFinite(x)))
    ? (p.ctrl.map((q) => [Math.min(3.2, Math.max(-3.2, q[0])), Math.min(2.4, Math.max(-2.4, q[1]))]) as [V2, V2, V2, V2])
    : DEFAULT_PARAMS.ctrl;
  return {
    R: num(p.R, DEFAULT_PARAMS.R, PARAM_RANGES.R[0], PARAM_RANGES.R[1]),
    b: num(p.b, DEFAULT_PARAMS.b, PARAM_RANGES.b[0], PARAM_RANGES.b[1]),
    k: num(p.k, DEFAULT_PARAMS.k, PARAM_RANGES.k[0], PARAM_RANGES.k[1]),
    c: num(p.c, DEFAULT_PARAMS.c, PARAM_RANGES.c[0], PARAM_RANGES.c[1]),
    ctrl,
  };
}
