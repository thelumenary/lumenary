/**
 * Complex-plane logic for the ComplexPlane widget: arithmetic and polar form,
 * n-th roots, the conformal-map presets with their derivatives and source
 * grids, image sampling, and winding numbers (by argument tracking and by
 * signed crossings of a ray). Pure functions, unit-tested.
 */

import { toNumber } from "./expr";
import { fmt, piLabel, sampleParametric, type Pt, type Range } from "./plot-core";

/** A complex number as [re, im]. */
export type C = [number, number];

export const add = (a: C, b: C): C => [a[0] + b[0], a[1] + b[1]];
export const sub = (a: C, b: C): C => [a[0] - b[0], a[1] - b[1]];
export const mul = (a: C, b: C): C => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
export const scale = (a: C, k: number): C => [a[0] * k, a[1] * k];
export const conj = (a: C): C => [a[0], -a[1]];
export const abs = (a: C): number => Math.hypot(a[0], a[1]);
/** Principal argument in (−π, π]; NaN for 0. */
export const arg = (a: C): number => (a[0] === 0 && a[1] === 0 ? NaN : Math.atan2(a[1], a[0]));
export const fromPolar = (r: number, theta: number): C => [r * Math.cos(theta), r * Math.sin(theta)];
export function div(a: C, b: C): C {
  const d = b[0] * b[0] + b[1] * b[1];
  if (d === 0) return [NaN, NaN];
  return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d];
}
export const cexp = (a: C): C => fromPolar(Math.exp(a[0]), a[1]);
export const isFiniteC = (a: C) => Number.isFinite(a[0]) && Number.isFinite(a[1]);

/** All n-th roots of c, starting with the principal one and going counter-clockwise. */
export function nthRoots(c: C, n: number): C[] {
  const k = Math.max(1, Math.round(n));
  const r = Math.pow(abs(c), 1 / k);
  const base = abs(c) === 0 ? 0 : arg(c);
  return Array.from({ length: k }, (_, j) => fromPolar(r, (base + 2 * Math.PI * j) / k));
}

/** Reduce an angle to (−π, π]. */
export function principal(theta: number): number {
  let t = theta % (2 * Math.PI);
  if (t <= -Math.PI) t += 2 * Math.PI;
  if (t > Math.PI) t -= 2 * Math.PI;
  return t;
}

/* ---------------------------------------------------------------------------
 * Display
 * ------------------------------------------------------------------------- */

const tiny = (v: number) => Math.abs(v) < 1e-10;

/** "a + bi", "a − bi", "bi", "a", "i", "−i"; "undefined" when not finite. */
export function fmtC(z: C, digits = 2): string {
  const [a, b] = z;
  if (!isFiniteC(z)) return "undefined";
  const im = (v: number) => {
    const s = fmt(Math.abs(v), digits);
    return s === "1" ? "i" : `${s}i`;
  };
  if (tiny(b) || fmt(Math.abs(b), digits) === "0") return fmt(a, digits);
  if (tiny(a) || fmt(a, digits) === "0") return `${b < 0 ? "−" : ""}${im(b)}`;
  return `${fmt(a, digits)} ${b < 0 ? "−" : "+"} ${im(b)}`;
}

/** An angle in degrees, plus an exact multiple of π when it is one of k·π/12. */
export function fmtAngle(theta: number): { deg: string; rad: string } {
  if (!Number.isFinite(theta)) return { deg: "—", rad: "—" };
  const deg = (theta * 180) / Math.PI;
  const k = (theta / Math.PI) * 12;
  const rad = Math.abs(k - Math.round(k)) < 1e-9 ? piLabel(Math.round(k), 12) : `${fmt(theta, 3)} rad`;
  return { deg: `${fmt(deg, 1)}°`, rad };
}

/** Read a complex prop: [re, im] (numbers or constant expressions) or a real number. */
export function toComplex(value: unknown, fallback: C): C {
  if (typeof value === "number" || typeof value === "string") {
    const v = toNumber(value, NaN);
    return Number.isFinite(v) ? [v, 0] : [fallback[0], fallback[1]];
  }
  if (Array.isArray(value) && value.length >= 2) {
    const a = toNumber(value[0], NaN);
    const b = toNumber(value[1], NaN);
    if (Number.isFinite(a) && Number.isFinite(b)) return [a, b];
  }
  return [fallback[0], fallback[1]];
}

/* ---------------------------------------------------------------------------
 * Conformal-map presets
 * ------------------------------------------------------------------------- */

export type MapId = "z^2" | "z^3" | "1/z" | "exp" | "mobius" | "joukowski";
export const MAP_IDS: readonly MapId[] = ["z^2", "z^3", "1/z", "exp", "mobius", "joukowski"];
export type GridKind = "cartesian" | "polar";

const MAP_ALIASES: Record<string, MapId> = {
  "z^2": "z^2",
  z2: "z^2",
  "z²": "z^2",
  square: "z^2",
  "z^3": "z^3",
  z3: "z^3",
  "z³": "z^3",
  cube: "z^3",
  "1/z": "1/z",
  inv: "1/z",
  inverse: "1/z",
  inversion: "1/z",
  exp: "exp",
  "e^z": "exp",
  ez: "exp",
  mobius: "mobius",
  möbius: "mobius",
  "(z-1)/(z+1)": "mobius",
  joukowski: "joukowski",
  "z+1/z": "joukowski",
};

export function toMapId(value: unknown, fallback: MapId = "z^2"): MapId {
  if (typeof value !== "string") return fallback;
  return MAP_ALIASES[value.trim().toLowerCase().replace(/\s+/g, "")] ?? fallback;
}

export interface MapSpec {
  id: MapId;
  /** Display formula for w = f(z). */
  formula: string;
  f: (z: C) => C;
  df: (z: C) => C;
  /** Windows for the z- and w-planes. */
  zView: { x: Range; y: Range };
  wView: { x: Range; y: Range };
  cartesian: { xs: number[]; ys: number[]; x: Range; y: Range };
  polar: { rs: number[]; thetas: number[]; r: Range; theta: Range };
  defaultGrid: GridKind;
  probe: C;
  /** Points where f′ = 0, with the factor by which angles are multiplied there. */
  critical: { z: C; order: number }[];
  poles: C[];
}

const steps = (a: number, b: number, h: number) => {
  const out: number[] = [];
  for (let k = 0; a + k * h <= b + 1e-9; k++) out.push(Number((a + k * h).toFixed(10)));
  return out;
};
const deg = (d: number) => (d * Math.PI) / 180;
const ONE: C = [1, 0];

export const MAPS: Record<MapId, MapSpec> = {
  "z^2": {
    id: "z^2",
    formula: "z²",
    f: (z) => mul(z, z),
    df: (z) => scale(z, 2),
    zView: { x: [-0.5, 2], y: [-1.9, 1.9] },
    wView: { x: [-3, 3], y: [-3.5, 3.5] },
    cartesian: { xs: steps(0.25, 1.5, 0.25), ys: steps(-1.5, 1.5, 0.25), x: [0, 1.5], y: [-1.5, 1.5] },
    polar: { rs: [0.5, 1, 1.5], thetas: steps(-90, 90, 22.5).map(deg), r: [0, 1.6], theta: [-Math.PI / 2, Math.PI / 2] },
    defaultGrid: "cartesian",
    probe: [1, 0.5],
    critical: [{ z: [0, 0], order: 2 }],
    poles: [],
  },
  "z^3": {
    id: "z^3",
    formula: "z³",
    f: (z) => mul(z, mul(z, z)),
    df: (z) => scale(mul(z, z), 3),
    zView: { x: [-0.4, 1.6], y: [-0.4, 1.6] },
    wView: { x: [-4, 4], y: [-4, 4] },
    cartesian: { xs: steps(0, 1.2, 0.2), ys: steps(0, 1.2, 0.2), x: [0, 1.2], y: [0, 1.2] },
    polar: { rs: [0.5, 0.8, 1, 1.25, 1.5], thetas: steps(0, 120, 15).map(deg), r: [0, 1.5], theta: [0, (2 * Math.PI) / 3] },
    defaultGrid: "polar",
    probe: [0.9, 0.45],
    critical: [{ z: [0, 0], order: 3 }],
    poles: [],
  },
  "1/z": {
    id: "1/z",
    formula: "1/z",
    f: (z) => div(ONE, z),
    df: (z) => scale(div(ONE, mul(z, z)), -1),
    zView: { x: [-2.5, 2.5], y: [-2.5, 2.5] },
    wView: { x: [-2.5, 2.5], y: [-2.5, 2.5] },
    cartesian: { xs: steps(-2, 2, 0.5), ys: steps(-2, 2, 0.5), x: [-2, 2], y: [-2, 2] },
    polar: { rs: [0.5, 1, 1.5, 2], thetas: steps(0, 330, 30).map(deg), r: [0, 2.2], theta: [0, 2 * Math.PI] },
    defaultGrid: "cartesian",
    probe: [1, 0.5],
    critical: [],
    poles: [[0, 0]],
  },
  exp: {
    id: "exp",
    formula: "eᶻ",
    f: cexp,
    df: cexp,
    zView: { x: [-2, 1.5], y: [-3.6, 3.6] },
    wView: { x: [-3, 3], y: [-3, 3] },
    cartesian: { xs: steps(-1.5, 1, 0.5), ys: steps(-4, 4, 1).map((k) => (k * Math.PI) / 4), x: [-1.5, 1], y: [-Math.PI, Math.PI] },
    polar: { rs: [0.5, 1, 1.5, 2], thetas: steps(0, 330, 30).map(deg), r: [0, 2], theta: [0, 2 * Math.PI] },
    defaultGrid: "cartesian",
    probe: [0.25, 0.75],
    critical: [],
    poles: [],
  },
  mobius: {
    id: "mobius",
    formula: "(z − 1)/(z + 1)",
    f: (z) => div(sub(z, ONE), add(z, ONE)),
    df: (z) => div([2, 0], mul(add(z, ONE), add(z, ONE))),
    zView: { x: [-2.5, 2.5], y: [-2.5, 2.5] },
    wView: { x: [-3, 3], y: [-3, 3] },
    cartesian: { xs: steps(-2, 2, 0.5), ys: steps(-2, 2, 0.5), x: [-2, 2], y: [-2, 2] },
    polar: { rs: [0.5, 1, 1.5, 2], thetas: steps(0, 330, 30).map(deg), r: [0, 2.2], theta: [0, 2 * Math.PI] },
    defaultGrid: "cartesian",
    probe: [0.5, 0.5],
    critical: [],
    poles: [[-1, 0]],
  },
  joukowski: {
    id: "joukowski",
    formula: "z + 1/z",
    f: (z) => add(z, div(ONE, z)),
    df: (z) => sub(ONE, div(ONE, mul(z, z))),
    zView: { x: [-2.75, 2.75], y: [-2.75, 2.75] },
    wView: { x: [-3.25, 3.25], y: [-2.75, 2.75] },
    cartesian: { xs: steps(-2, 2, 0.5), ys: steps(-2, 2, 0.5), x: [-2, 2], y: [-2, 2] },
    polar: { rs: [1, 1.25, 1.5, 2, 2.5], thetas: steps(0, 330, 30).map(deg), r: [1, 2.6], theta: [0, 2 * Math.PI] },
    defaultGrid: "polar",
    probe: [1.5, 0.75],
    critical: [
      { z: [1, 0], order: 2 },
      { z: [-1, 0], order: 2 },
    ],
    poles: [[0, 0]],
  },
};

/** A source line of the grid: family 0 = horizontal lines / circles, 1 = vertical lines / rays. */
export interface GridLine {
  family: 0 | 1;
  path: (t: number) => C;
  t: Range;
}

export function gridLines(spec: MapSpec, kind: GridKind): GridLine[] {
  if (kind === "cartesian") {
    const g = spec.cartesian;
    return [
      ...g.ys.map((y): GridLine => ({ family: 0, path: (t) => [t, y], t: g.x })),
      ...g.xs.map((x): GridLine => ({ family: 1, path: (t) => [x, t], t: g.y })),
    ];
  }
  const g = spec.polar;
  return [
    ...g.rs.map((r): GridLine => ({ family: 0, path: (t) => fromPolar(r, t), t: g.theta })),
    ...g.thetas.map((th): GridLine => ({ family: 1, path: (t) => fromPolar(t, th), t: g.r })),
  ];
}

/** Sample the image f(path(t)) as polylines in the w-window (breaks at poles and jumps, clipped). */
export function imageCurve(f: (z: C) => C, path: (t: number) => C, t: Range, view: { x: Range; y: Range }, n = 900): Pt[][] {
  let lastT = NaN;
  let last: C = [NaN, NaN];
  const at = (tt: number): C => {
    if (tt !== lastT) {
      lastT = tt;
      last = f(path(tt));
    }
    return last;
  };
  return sampleParametric((tt) => at(tt)[0], (tt) => at(tt)[1], t, view, n);
}

/**
 * The oriented angle (degrees, in [0, 360)) from the image of a small
 * horizontal step at z0 to the image of a small vertical step. 90 wherever f
 * is conformal; k·90 (mod 360) at a critical point of order k.
 */
export function imageAngle(f: (z: C) => C, z0: C, h = 1e-6): number {
  const w0 = f(z0);
  const a = sub(f(add(z0, [h, 0])), w0);
  const b = sub(f(add(z0, [0, h])), w0);
  if (!isFiniteC(a) || !isFiniteC(b) || abs(a) === 0 || abs(b) === 0) return NaN;
  let d = (Math.atan2(a[0] * b[1] - a[1] * b[0], a[0] * b[0] + a[1] * b[1]) * 180) / Math.PI;
  if (d < 0) d += 360;
  return d;
}

/** Classify the behaviour of a map at z0. */
export function probeStatus(spec: MapSpec, z0: C, tol = 1e-6): { kind: "pole" } | { kind: "critical"; order: number } | { kind: "conformal" } {
  if (spec.poles.some((p) => abs(sub(p, z0)) < tol) || !isFiniteC(spec.f(z0))) return { kind: "pole" };
  const c = spec.critical.find((q) => abs(sub(q.z, z0)) < tol);
  if (c) return { kind: "critical", order: c.order };
  return { kind: "conformal" };
}

/* ---------------------------------------------------------------------------
 * Closed curves and winding numbers
 * ------------------------------------------------------------------------- */

export type CurveId = "circle" | "ellipse" | "figure8" | "doubleLoop" | "square" | "cardioid";
export const CURVE_IDS: readonly CurveId[] = ["circle", "ellipse", "figure8", "doubleLoop", "square", "cardioid"];

const square = (t: number): C => {
  const s = 1.5;
  const u = ((t / (2 * Math.PI)) * 4 + 4) % 4;
  const e = Math.floor(u);
  const f = u - e;
  const corners: C[] = [
    [-s, -s],
    [s, -s],
    [s, s],
    [-s, s],
  ];
  const a = corners[e % 4];
  const b = corners[(e + 1) % 4];
  return [a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f];
};

/** Closed curves γ(t), t ∈ [0, 2π]. */
export const CURVES: Record<CurveId, (t: number) => C> = {
  circle: (t) => fromPolar(1.8, t),
  ellipse: (t) => [2.4 * Math.cos(t), 1.4 * Math.sin(t)],
  // Right lobe clockwise (winding −1), left lobe counter-clockwise (+1).
  figure8: (t) => [2.4 * Math.sin(t), 1.2 * Math.sin(2 * t)],
  // Limaçon r = 1 + 2 cos θ: winding 2 inside the inner loop, 1 between the loops.
  doubleLoop: (t) => {
    const r = 1 + 2 * Math.cos(t);
    return [r * Math.cos(t) - 0.5, r * Math.sin(t)];
  },
  square,
  cardioid: (t) => {
    const r = 1.3 * (1 + Math.cos(t));
    return [r * Math.cos(t) - 0.6, r * Math.sin(t)];
  },
};

export function toCurveId(value: unknown, fallback: CurveId = "doubleLoop"): CurveId {
  return typeof value === "string" && (CURVE_IDS as readonly string[]).includes(value) ? (value as CurveId) : fallback;
}

/** The curve as a closed polygon (last vertex = first), optionally traversed backwards. */
export function curvePolygon(gamma: (t: number) => C, n = 720, reversed = false): C[] {
  const pts: C[] = [];
  for (let k = 0; k <= n; k++) {
    const t = (2 * Math.PI * (reversed ? n - k : k)) / n;
    pts.push(gamma(t));
  }
  pts[n] = pts[0];
  return pts;
}

/** Distance from p to a closed polygon. */
export function distanceToPolygon(poly: readonly C[], p: C): number {
  let best = Infinity;
  for (let i = 1; i < poly.length; i++) {
    const a = poly[i - 1];
    const b = poly[i];
    const d = sub(b, a);
    const L = d[0] * d[0] + d[1] * d[1];
    const u = L === 0 ? 0 : Math.max(0, Math.min(1, ((p[0] - a[0]) * d[0] + (p[1] - a[1]) * d[1]) / L));
    best = Math.min(best, Math.hypot(a[0] + u * d[0] - p[0], a[1] + u * d[1] - p[1]));
  }
  return best;
}

/** Total turning of γ − p divided by 2π (an integer when p is off the curve). */
export function windingByAngle(poly: readonly C[], p: C): number {
  let total = 0;
  for (let i = 1; i < poly.length; i++) {
    const a = sub(poly[i - 1], p);
    const b = sub(poly[i], p);
    total += Math.atan2(a[0] * b[1] - a[1] * b[0], a[0] * b[0] + a[1] * b[1]);
  }
  return total / (2 * Math.PI);
}

export interface Crossing {
  /** Where the curve meets the ray {p + s : s > 0}. */
  x: number;
  sign: 1 | -1;
}

/**
 * Signed crossings of the horizontal ray from p to the right: +1 where the
 * curve passes upwards (counter-clockwise around p), −1 where it passes
 * downwards. Half-open rule, so a vertex on the ray is counted once.
 */
export function rayCrossings(poly: readonly C[], p: C): Crossing[] {
  const out: Crossing[] = [];
  for (let i = 1; i < poly.length; i++) {
    const a = poly[i - 1];
    const b = poly[i];
    const up = a[1] <= p[1] && b[1] > p[1];
    const down = b[1] <= p[1] && a[1] > p[1];
    if (!up && !down) continue;
    const x = a[0] + ((p[1] - a[1]) / (b[1] - a[1])) * (b[0] - a[0]);
    if (x > p[0]) out.push({ x, sign: up ? 1 : -1 });
  }
  return out.sort((u, v) => u.x - v.x);
}

export interface WindingInfo {
  onCurve: boolean;
  byAngle: number;
  crossings: Crossing[];
  /** Sum of the crossing signs. */
  byRay: number;
}

export function winding(poly: readonly C[], p: C, tol: number): WindingInfo {
  const onCurve = distanceToPolygon(poly, p) < tol;
  const crossings = rayCrossings(poly, p);
  return { onCurve, byAngle: windingByAngle(poly, p), crossings, byRay: crossings.reduce((s, c) => s + c.sign, 0) };
}

/** The winding number as an integer (never −0). */
export const windingInteger = (info: WindingInfo) => Math.round(info.byAngle) || 0;

/**
 * Regions of constant winding number, as horizontal runs on `rows` scan lines
 * across the curve's bounding box. Exact in x, quantised in y.
 */
export function windingRuns(poly: readonly C[], rows = 140): { y0: number; y1: number; x0: number; x1: number; k: number }[] {
  let ymin = Infinity;
  let ymax = -Infinity;
  for (const q of poly) {
    ymin = Math.min(ymin, q[1]);
    ymax = Math.max(ymax, q[1]);
  }
  if (!(ymax > ymin)) return [];
  const h = (ymax - ymin) / rows;
  const out: { y0: number; y1: number; x0: number; x1: number; k: number }[] = [];
  for (let r = 0; r < rows; r++) {
    const y = ymin + (r + 0.5) * h;
    const xs = rayCrossings(poly, [-Infinity, y]);
    // Winding to the right of each crossing: sweep from the right, where it is 0.
    let k = 0;
    for (let i = xs.length - 1; i > 0; i--) {
      k += xs[i].sign;
      if (k !== 0) out.push({ y0: y - h / 2, y1: y + h / 2, x0: xs[i - 1].x, x1: xs[i].x, k });
    }
  }
  return out;
}
