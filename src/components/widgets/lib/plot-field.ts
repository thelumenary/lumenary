/**
 * Planar vector fields and ODEs for the VectorField widget: RK4 solution
 * curves with honest stopping rules, presets, line and double integrals
 * (Green's theorem), the index of a field around a loop, equilibria and the
 * trace–determinant classification of linear systems. Pure functions.
 */

import type { Pt, Range } from "./plot-core";

export type Field2 = (x: number, y: number) => Pt;
export type Mat2 = [[number, number], [number, number]];
export interface Box {
  x: Range;
  y: Range;
}

export const finitePt = (p: Pt) => Number.isFinite(p[0]) && Number.isFinite(p[1]);
const diagOf = (b: Box) => Math.hypot(b.x[1] - b.x[0], b.y[1] - b.y[0]);
const inBox = (p: Pt, b: Box) => p[0] >= b.x[0] && p[0] <= b.x[1] && p[1] >= b.y[0] && p[1] <= b.y[1];
const padBox = (b: Box, k: number): Box => {
  const w = b.x[1] - b.x[0];
  const h = b.y[1] - b.y[0];
  return { x: [b.x[0] - k * w, b.x[1] + k * w], y: [b.y[0] - k * h, b.y[1] + k * h] };
};

/* ---------------------------------------------------------------------------
 * Presets
 * ------------------------------------------------------------------------- */

export interface SlopePreset {
  f: string;
  x: Range;
  y: Range;
  points: Pt[];
}
export interface SystemPreset {
  f: string;
  g: string;
  x: Range;
  y: Range;
  points: Pt[];
}
export interface FieldPreset {
  f: string;
  g: string;
  x: Range;
  y: Range;
  /** Initial loop centre and radius. */
  loop: [number, number, number];
}

const TAU = 2 * Math.PI;

export const SLOPE_PRESETS: Record<string, SlopePreset> = {
  linear: { f: "x - y", x: [-4, 4], y: [-4, 4], points: [[-3, 3], [-3, -2], [0, 2.5]] },
  logistic: { f: "y*(1 - y)", x: [-2, 6], y: [-1, 2.5], points: [[0, 0.1], [0, 0.5], [0, 1.8], [0, -0.05]] },
  circles: { f: "-x/y", x: [-4, 4], y: [-4, 4], points: [[0, 2], [0, -3]] },
  blowup: { f: "x^2 + y^2", x: [-3, 3], y: [-3, 3], points: [[-2, -1], [0, 0]] },
};

export const PHASE_PRESETS: Record<string, SystemPreset> = {
  center: { f: "-y", g: "x", x: [-4, 4], y: [-4, 4], points: [[1, 0], [2, 0], [3, 0]] },
  saddle: { f: "x", g: "-y", x: [-4, 4], y: [-4, 4], points: [[0.15, 3.8], [-0.15, 3.8], [0.15, -3.8], [-0.15, -3.8], [-3.8, 1.5], [3.8, -1.5]] },
  spiralSource: { f: "0.2*x - y", g: "x + 0.2*y", x: [-4, 4], y: [-4, 4], points: [[0.4, 0]] },
  spiralSink: { f: "-0.25*x - y", g: "x - 0.25*y", x: [-4, 4], y: [-4, 4], points: [[3.8, 0], [-3.8, 1]] },
  node: { f: "-2*x + y", g: "x - 2*y", x: [-4, 4], y: [-4, 4], points: [[3.8, 1], [-3.8, -1], [1, 3.8], [-1, -3.8], [3.8, -3], [-3.8, 3]] },
  lotkaVolterra: { f: "x*(1 - 0.5*y)", g: "y*(0.5*x - 1)", x: [0, 6], y: [0, 6], points: [[2, 1], [2, 0.5], [3, 2]] },
  pendulum: { f: "y", g: "-sin(x)", x: [-TAU, TAU], y: [-3.2, 3.2], points: [[0, 1], [0, 1.9], [-TAU, 2.4], [TAU, -2.4]] },
  vanDerPol: { f: "y", g: "(1 - x^2)*y - x", x: [-4, 4], y: [-4, 4], points: [[0.1, 0], [3.5, 3.5]] },
};

export const FIELD_PRESETS: Record<string, FieldPreset> = {
  rotation: { f: "-y", g: "x", x: [-4, 4], y: [-4, 4], loop: [0.5, 0.3, 1.5] },
  source: { f: "x", g: "y", x: [-4, 4], y: [-4, 4], loop: [0.5, 0.3, 1.5] },
  sink: { f: "-x", g: "-y", x: [-4, 4], y: [-4, 4], loop: [0.5, 0.3, 1.5] },
  saddleField: { f: "x", g: "-y", x: [-4, 4], y: [-4, 4], loop: [0.5, 0.3, 1.5] },
  dipole: { f: "x^2 - y^2", g: "2*x*y", x: [-3, 3], y: [-3, 3], loop: [0.3, 0.2, 1.2] },
  uniform: { f: "1", g: "0", x: [-4, 4], y: [-4, 4], loop: [0.5, 0.3, 1.5] },
  // F = (y, 0) vanishes along the whole x-axis: the default loop stays above it (curl −1 everywhere, index 0).
  shear: { f: "y", g: "0", x: [-4, 4], y: [-4, 4], loop: [0.5, 2, 1.2] },
};

const PRESET_ALIASES: Record<string, string> = { centre: "center", spiral: "spiralSink", predatorPrey: "lotkaVolterra", vanderpol: "vanDerPol", saddlefield: "saddleField" };
export const resolvePreset = (p: unknown): string | null => (typeof p === "string" && p ? (PRESET_ALIASES[p] ?? p) : null);

/** Which mode a preset belongs to (presets have unique names across modes). */
export function presetMode(p: unknown): "slope" | "phase" | "field" | null {
  const id = resolvePreset(p);
  if (!id) return null;
  if (id in SLOPE_PRESETS) return "slope";
  if (id in PHASE_PRESETS) return "phase";
  if (id in FIELD_PRESETS) return "field";
  return null;
}

/* ---------------------------------------------------------------------------
 * Integration
 * ------------------------------------------------------------------------- */

export function rk4(F: Field2, p: Pt, h: number): Pt {
  const k1 = F(p[0], p[1]);
  const k2 = F(p[0] + (h / 2) * k1[0], p[1] + (h / 2) * k1[1]);
  const k3 = F(p[0] + (h / 2) * k2[0], p[1] + (h / 2) * k2[1]);
  const k4 = F(p[0] + h * k3[0], p[1] + h * k3[1]);
  return [p[0] + (h / 6) * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]), p[1] + (h / 6) * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])];
}

export type StopReason = "left" | "blowup" | "equilibrium" | "closed" | "cycle" | "steps" | "undefined" | "vertical";
export interface CurveResult {
  points: Pt[];
  reason: StopReason;
}

/**
 * A trajectory of x' = F(x) from `start`, forward (dir = 1) or backward
 * (dir = -1) in time, by RK4 with a step chosen so that each step moves about
 * `ds` (so slow and fast regions are drawn equally finely). Stops when it
 * leaves a padded copy of `box`, blows up, reaches an equilibrium, closes up
 * ("closed": back at its start), runs onto a closed loop it has already
 * drawn ("cycle": a limit cycle, to drawing accuracy) or hits the step cap.
 */
export function orbit(F: Field2, start: Pt, box: Box, opts: { dir?: 1 | -1; ds?: number; maxSteps?: number; hMax?: number } = {}): CurveResult {
  const dir = opts.dir ?? 1;
  const diag = diagOf(box);
  const ds = opts.ds ?? diag / 600;
  const maxSteps = opts.maxSteps ?? 6000;
  const hMax = opts.hMax ?? 0.2;
  const pad = padBox(box, 0.2);
  const G: Field2 = dir === 1 ? F : (x, y) => {
    const v = F(x, y);
    return [-v[0], -v[1]];
  };
  const pts: Pt[] = [start];
  if (!finitePt(start)) return { points: [], reason: "undefined" };
  const v0 = G(start[0], start[1]);
  if (!finitePt(v0)) return { points: pts, reason: "undefined" };
  const s0 = Math.hypot(v0[0], v0[1]);
  if (s0 === 0) return { points: pts, reason: "equilibrium" };
  // Spatial hash of visited points, to notice when the curve runs back onto itself.
  const cell = (q: Pt) => `${Math.floor(q[0] / ds)},${Math.floor(q[1] / ds)}`;
  const seen = new Map<string, number[]>();
  const remember = (q: Pt, i: number) => {
    const k = cell(q);
    const list = seen.get(k);
    if (list) list.push(i);
    else seen.set(k, [i]);
  };
  remember(start, 0);
  let p = start;
  let travelled = 0;
  let slow = 0;
  for (let i = 0; i < maxSteps; i++) {
    const v = G(p[0], p[1]);
    if (!finitePt(v)) return { points: pts, reason: "undefined" };
    const speed = Math.hypot(v[0], v[1]);
    if (speed === 0) return { points: pts, reason: "equilibrium" };
    let h = Math.min(ds / speed, hMax);
    let q = rk4(G, p, h);
    let len = Math.hypot(q[0] - p[0], q[1] - p[1]);
    // RK4 overshooting in a fast-changing region: retry with smaller steps.
    for (let k = 0; k < 6 && (!finitePt(q) || len > 8 * ds); k++) {
      h /= 4;
      q = rk4(G, p, h);
      len = Math.hypot(q[0] - p[0], q[1] - p[1]);
    }
    if (!finitePt(q) || len > 8 * ds) return { points: pts, reason: "blowup" };
    pts.push(q);
    travelled += len;
    p = q;
    if (!inBox(p, pad)) return { points: pts, reason: "left" };
    slow = len < ds * 1e-3 ? slow + 1 : 0;
    if (slow > 40) return { points: pts, reason: "equilibrium" };
    const idx = pts.length - 1;
    if (travelled > 25 * ds && len > 0) {
      const ux = (q[0] - pts[idx - 1][0]) / len;
      const uy = (q[1] - pts[idx - 1][1]) / len;
      const gx = Math.floor(p[0] / ds);
      const gy = Math.floor(p[1] / ds);
      for (let a = -1; a <= 1; a++)
        for (let b = -1; b <= 1; b++) {
          for (const j of seen.get(`${gx + a},${gy + b}`) ?? []) {
            if (j > idx - 40) continue;
            const r = pts[j];
            if (Math.hypot(p[0] - r[0], p[1] - r[1]) > 0.6 * ds) continue;
            const nx = pts[j + 1] ?? r;
            const l2 = Math.hypot(nx[0] - r[0], nx[1] - r[1]);
            if (l2 > 0 && ((nx[0] - r[0]) * ux + (nx[1] - r[1]) * uy) / l2 > 0.9) {
              // A loop too small to see is a spiral closing in on an equilibrium, not a cycle.
              let x0 = Infinity;
              let x1 = -Infinity;
              let y0 = Infinity;
              let y1 = -Infinity;
              for (let m = j; m <= idx; m++) {
                const w = pts[m];
                if (w[0] < x0) x0 = w[0];
                if (w[0] > x1) x1 = w[0];
                if (w[1] < y0) y0 = w[1];
                if (w[1] > y1) y1 = w[1];
              }
              if (Math.hypot(x1 - x0, y1 - y0) < 10 * ds) return { points: pts, reason: "equilibrium" };
              pts.push(r);
              return { points: pts, reason: j < 5 ? "closed" : "cycle" };
            }
          }
        }
    }
    remember(p, idx);
  }
  return { points: pts, reason: "steps" };
}

/**
 * The solution y(x) of dy/dx = f(x, y) through `start`, to the right (dir = 1)
 * or left (dir = -1), by RK4 in x with steps of roughly constant arc length.
 * A solution y(x) ends where its tangent becomes vertical ("vertical"), where
 * f is undefined, or where it leaves a padded copy of the window.
 */
export function slopeSolution(f: (x: number, y: number) => number, start: Pt, box: Box, opts: { dir?: 1 | -1; ds?: number; maxSteps?: number } = {}): CurveResult {
  const dir = opts.dir ?? 1;
  const ds = opts.ds ?? diagOf(box) / 600;
  const maxSteps = opts.maxSteps ?? 6000;
  const minDx = ds * 1e-3;
  const tol = ds * 1e-5;
  const pad = padBox(box, 0.25);
  if (!finitePt(start)) return { points: [], reason: "undefined" };
  const pts: Pt[] = [start];
  let [x, y] = start;
  for (let i = 0; i < maxSteps; i++) {
    const s = f(x, y);
    if (!Number.isFinite(s)) return { points: pts, reason: Number.isNaN(s) ? "undefined" : "vertical" };
    const base = ds / Math.sqrt(1 + s * s);
    if (base < minDx) return { points: pts, reason: "vertical" };
    let dx = dir * base;
    let yn = NaN;
    // RK4 with step doubling: accept the two-half-step value when it agrees with the full step.
    const step = (x0: number, y0: number, s0: number, h: number) => {
      const k2 = f(x0 + h / 2, y0 + (h / 2) * s0);
      const k3 = f(x0 + h / 2, y0 + (h / 2) * k2);
      const k4 = f(x0 + h, y0 + h * k3);
      return y0 + (h / 6) * (s0 + 2 * k2 + 2 * k3 + k4);
    };
    for (let k = 0; k < 24; k++) {
      const full = step(x, y, s, dx);
      const half = step(x, y, s, dx / 2);
      const two = Number.isFinite(half) ? step(x + dx / 2, half, f(x + dx / 2, half), dx / 2) : NaN;
      const ok = Number.isFinite(full) && Number.isFinite(two) && Math.abs(two - full) <= tol && Math.hypot(dx, two - y) <= 8 * ds;
      if (ok) {
        yn = two;
        break;
      }
      if (Math.abs(dx) / 2 < minDx * 1e-3) break;
      dx /= 2;
    }
    if (!Number.isFinite(yn)) return { points: pts, reason: Math.abs(s) > 1 / (minDx / ds) ? "vertical" : "blowup" };
    x += dx;
    y = yn;
    pts.push([x, y]);
    if (!inBox([x, y], pad)) return { points: pts, reason: "left" };
  }
  return { points: pts, reason: "steps" };
}

/* ---------------------------------------------------------------------------
 * Linear algebra, equilibria, classification
 * ------------------------------------------------------------------------- */

/** Jacobian of F at p by central differences. */
export function jacobian(F: Field2, p: Pt, h = 1e-5): Mat2 {
  const a = F(p[0] + h, p[1]);
  const b = F(p[0] - h, p[1]);
  const c = F(p[0], p[1] + h);
  const d = F(p[0], p[1] - h);
  return [
    [(a[0] - b[0]) / (2 * h), (c[0] - d[0]) / (2 * h)],
    [(a[1] - b[1]) / (2 * h), (c[1] - d[1]) / (2 * h)],
  ];
}

const clean = (v: number) => {
  const r = Math.round(v * 1e9) / 1e9;
  return Object.is(r, -0) ? 0 : r;
};

/**
 * If F(p) = A p + b exactly (checked at several points), return A and b with
 * entries cleaned of rounding noise; otherwise null.
 */
export function linearFit(F: Field2, scale = 1): { A: Mat2; b: Pt } | null {
  const b = F(0, 0);
  if (!finitePt(b)) return null;
  const h = Math.max(scale, 1e-6) * 0.5;
  const J = jacobian(F, [0, 0], h);
  const A: Mat2 = [
    [clean(J[0][0]), clean(J[0][1])],
    [clean(J[1][0]), clean(J[1][1])],
  ];
  const s = Math.max(scale, 1e-6) / 4;
  const tests: Pt[] = [
    [1, 2],
    [-2, 1],
    [3, -1],
    [-1, -3],
    [2.5, 2.5],
    [-3.5, 0.7],
  ];
  for (const [u, v] of tests) {
    const p: Pt = [u * s, v * s];
    const Fp = F(p[0], p[1]);
    if (!finitePt(Fp)) return null;
    const lx = A[0][0] * p[0] + A[0][1] * p[1] + b[0];
    const ly = A[1][0] * p[0] + A[1][1] * p[1] + b[1];
    const tol = 1e-7 * (1 + Math.abs(Fp[0]) + Math.abs(Fp[1]));
    if (Math.abs(Fp[0] - lx) > tol || Math.abs(Fp[1] - ly) > tol) return null;
  }
  return { A, b: [clean(b[0]), clean(b[1])] };
}

/** Equilibria of F inside `box`, found by Newton's method from a grid of starting points. */
export function findEquilibria(F: Field2, box: Box, grid = 7, max = 8): Pt[] {
  const diag = diagOf(box);
  const out: Pt[] = [];
  const margin = padBox(box, 0.001);
  for (let i = 0; i < grid; i++)
    for (let j = 0; j < grid; j++) {
      let p: Pt = [box.x[0] + ((i + 0.5) / grid) * (box.x[1] - box.x[0]), box.y[0] + ((j + 0.5) / grid) * (box.y[1] - box.y[0])];
      let ok = false;
      for (let k = 0; k < 50; k++) {
        const v = F(p[0], p[1]);
        if (!finitePt(v)) break;
        if (Math.hypot(v[0], v[1]) < 1e-11) {
          ok = true;
          break;
        }
        const J = jacobian(F, p, 1e-6 * Math.max(1, diag));
        const det = J[0][0] * J[1][1] - J[0][1] * J[1][0];
        if (!Number.isFinite(det) || Math.abs(det) < 1e-14) break;
        let dx = (J[1][1] * v[0] - J[0][1] * v[1]) / det;
        let dy = (-J[1][0] * v[0] + J[0][0] * v[1]) / det;
        const step = Math.hypot(dx, dy);
        if (step > diag / 4) {
          dx *= diag / 4 / step;
          dy *= diag / 4 / step;
        }
        p = [p[0] - dx, p[1] - dy];
        if (!inBox(p, padBox(box, 0.5))) break;
      }
      if (!ok) {
        const v = F(p[0], p[1]);
        ok = finitePt(v) && Math.hypot(v[0], v[1]) < 1e-9;
      }
      if (ok && inBox(p, margin) && !out.some((q) => Math.hypot(q[0] - p[0], q[1] - p[1]) < 1e-5 * diag)) {
        out.push([clean(p[0]), clean(p[1])]);
        if (out.length >= max) return out;
      }
    }
  return out.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
}

export type LinearKind = "saddle" | "center" | "spiralSource" | "spiralSink" | "nodeSource" | "nodeSink" | "improperSource" | "improperSink" | "degenerate";

export interface Classification {
  trace: number;
  det: number;
  disc: number;
  kind: LinearKind;
  /** Eigenvalues: real parts and the (non-negative) imaginary part. */
  eig: { re: [number, number]; im: number };
}

/** Classify the equilibrium of x' = A x by trace T, determinant D and discriminant T² − 4D. */
export function classify(A: Mat2, eps = 1e-9): Classification {
  const [[a, b], [c, d]] = A;
  const T = a + d;
  const D = a * d - b * c;
  const disc = T * T - 4 * D;
  const s = Math.max(Math.abs(a), Math.abs(b), Math.abs(c), Math.abs(d), 1e-12);
  const zT = Math.abs(T) <= eps * s;
  const zD = Math.abs(D) <= eps * s * s;
  const zDisc = Math.abs(disc) <= eps * s * s;
  let kind: LinearKind;
  if (zD) kind = "degenerate";
  else if (D < 0) kind = "saddle";
  else if (zT) kind = "center";
  else if (zDisc) kind = T > 0 ? "improperSource" : "improperSink";
  else if (disc < 0) kind = T > 0 ? "spiralSource" : "spiralSink";
  else kind = T > 0 ? "nodeSource" : "nodeSink";
  const eig: Classification["eig"] =
    disc >= 0 || zDisc
      ? { re: [(T - Math.sqrt(Math.max(0, disc))) / 2, (T + Math.sqrt(Math.max(0, disc))) / 2], im: 0 }
      : { re: [T / 2, T / 2], im: Math.sqrt(-disc) / 2 };
  return { trace: zT ? 0 : T, det: zD ? 0 : D, disc: zDisc ? 0 : disc, kind, eig };
}

/* ---------------------------------------------------------------------------
 * Line integrals, Green's theorem, index
 * ------------------------------------------------------------------------- */

/** Circulation ∮F·dr and outward flux ∮F·n ds around the circle of centre c, radius r (trapezoid rule, spectrally accurate for smooth F). */
export function loopIntegrals(F: Field2, c: Pt, r: number, n = 720): { circulation: number; flux: number } {
  let circ = 0;
  let flux = 0;
  for (let k = 0; k < n; k++) {
    const s = (TAU * k) / n;
    const cs = Math.cos(s);
    const sn = Math.sin(s);
    const v = F(c[0] + r * cs, c[1] + r * sn);
    if (!finitePt(v)) return { circulation: NaN, flux: NaN };
    circ += (-v[0] * sn + v[1] * cs) * r;
    flux += (v[0] * cs + v[1] * sn) * r;
  }
  return { circulation: (circ * TAU) / n, flux: (flux * TAU) / n };
}

const glCache = new Map<number, { x: number[]; w: number[] }>();
/** Gauss–Legendre nodes and weights on [−1, 1]. */
export function gaussLegendre(n: number): { x: number[]; w: number[] } {
  const hit = glCache.get(n);
  if (hit) return hit;
  const x = new Array<number>(n).fill(0);
  const w = new Array<number>(n).fill(0);
  const m = Math.ceil(n / 2);
  for (let i = 1; i <= m; i++) {
    let z = Math.cos((Math.PI * (i - 0.25)) / (n + 0.5));
    let pp = 1;
    for (let it = 0; it < 100; it++) {
      let p1 = 1;
      let p2 = 0;
      for (let j = 1; j <= n; j++) {
        const p3 = p2;
        p2 = p1;
        p1 = ((2 * j - 1) * z * p2 - (j - 1) * p3) / j;
      }
      pp = (n * (z * p1 - p2)) / (z * z - 1);
      const z1 = z;
      z = z1 - p1 / pp;
      if (Math.abs(z - z1) < 1e-15) break;
    }
    x[i - 1] = -z;
    x[n - i] = z;
    w[i - 1] = w[n - i] = 2 / ((1 - z * z) * pp * pp);
  }
  const res = { x, w };
  glCache.set(n, res);
  return res;
}

/** Scalar curl ∂g/∂x − ∂f/∂y and divergence ∂f/∂x + ∂g/∂y by central differences. */
export function curlDiv(F: Field2, p: Pt, h = 1e-5): { curl: number; div: number } {
  const J = jacobian(F, p, h);
  return { curl: J[1][0] - J[0][1], div: J[0][0] + J[1][1] };
}

/** ∬ curl F dA and ∬ div F dA over the disk (Gauss–Legendre in the radius, trapezoid in the angle). */
export function diskIntegrals(F: Field2, c: Pt, r: number, nr = 16, nt = 96): { curl: number; div: number } {
  const { x, w } = gaussLegendre(nr);
  const h = 1e-5 * Math.max(1, r);
  let curl = 0;
  let div = 0;
  for (let i = 0; i < nr; i++) {
    const rho = ((x[i] + 1) / 2) * r;
    const wr = (w[i] * r) / 2;
    for (let k = 0; k < nt; k++) {
      const th = (TAU * k) / nt;
      const q = curlDiv(F, [c[0] + rho * Math.cos(th), c[1] + rho * Math.sin(th)], h);
      if (!Number.isFinite(q.curl) || !Number.isFinite(q.div)) return { curl: NaN, div: NaN };
      curl += q.curl * rho * wr;
      div += q.div * rho * wr;
    }
  }
  return { curl: (curl * TAU) / nt, div: (div * TAU) / nt };
}

const wrapAngle = (a: number) => a - TAU * Math.round(a / TAU);

export interface IndexResult {
  /** The winding number of F along the loop (meaningful when status is "ok" or "near"). */
  index: number;
  /** "ok"; "near" (F almost vanishes somewhere on the loop, so a small move could change the index); "zero" (F vanishes on the loop); "undefined" (F undefined on the loop). */
  status: "ok" | "near" | "zero" | "undefined";
  /** Cumulative turning angle of F (radians) at s = k/n of the way round, k = 0..n. */
  turning: number[];
  minMag: number;
  maxMag: number;
}

/** Index of F around the circle: how many times F turns as the loop is traversed once anticlockwise. */
export function fieldIndex(F: Field2, c: Pt, r: number, n = 720): IndexResult {
  for (let attempt = 0; attempt < 3; attempt++) {
    const angles: number[] = [];
    let minMag = Infinity;
    let maxMag = 0;
    for (let k = 0; k <= n; k++) {
      const s = (TAU * k) / n;
      const v = F(c[0] + r * Math.cos(s), c[1] + r * Math.sin(s));
      if (!finitePt(v)) return { index: 0, status: "undefined", turning: [], minMag: NaN, maxMag: NaN };
      const m = Math.hypot(v[0], v[1]);
      minMag = Math.min(minMag, m);
      maxMag = Math.max(maxMag, m);
      angles.push(Math.atan2(v[1], v[0]));
    }
    if (minMag <= 1e-12 * (1 + maxMag)) return { index: 0, status: "zero", turning: [], minMag, maxMag };
    const turning = [0];
    let maxJump = 0;
    for (let k = 1; k <= n; k++) {
      const d = wrapAngle(angles[k] - angles[k - 1]);
      maxJump = Math.max(maxJump, Math.abs(d));
      turning.push(turning[k - 1] + d);
    }
    if (maxJump > Math.PI / 3 && attempt < 2) {
      n *= 4;
      continue;
    }
    const total = turning[n] / TAU;
    const index = Math.round(total);
    const near = minMag < 0.005 * maxMag || Math.abs(total - index) > 0.05 || maxJump > Math.PI / 3;
    return { index: Object.is(index, -0) ? 0 : index, status: near ? "near" : "ok", turning, minMag, maxMag };
  }
  return { index: 0, status: "near", turning: [], minMag: NaN, maxMag: NaN };
}

/* ---------------------------------------------------------------------------
 * Drawing helpers
 * ------------------------------------------------------------------------- */

/** Positions and directions (radians, pixel space) for arrowheads every `every` pixels along a polyline. */
export function arrowMarks(px: readonly Pt[], every: number, offset = every / 2): { x: number; y: number; angle: number }[] {
  const out: { x: number; y: number; angle: number }[] = [];
  if (px.length < 2 || !(every > 0)) return out;
  let next = offset;
  let acc = 0;
  for (let i = 1; i < px.length && out.length < 200; i++) {
    const [x0, y0] = px[i - 1];
    const [x1, y1] = px[i];
    const len = Math.hypot(x1 - x0, y1 - y0);
    if (!(len > 0)) continue;
    while (acc + len >= next) {
      const t = (next - acc) / len;
      out.push({ x: x0 + t * (x1 - x0), y: y0 + t * (y1 - y0), angle: Math.atan2(y1 - y0, x1 - x0) });
      next += every;
    }
    acc += len;
  }
  return out;
}
