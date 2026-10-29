/**
 * Plane-geometry helpers for ShapeExplorer: a gallery of named shapes built so
 * that every angle is exact, plus generic analysis (side groups, angles, lines
 * of symmetry, rotational symmetry, diagonals) that works for any polygon.
 */
import { nextRandom, seedFrom } from "./shape-util";

export interface Pt {
  x: number;
  y: number;
}

export type ShapeFamily = "triangle" | "quadrilateral" | "polygon" | "circle";

export interface ShapeDef {
  /** The id lesson authors write, e.g. "rhombus" or "regular-7". */
  id: string;
  /** Message key under w.shapes.name / w.shapes.note. */
  key: string;
  family: ShapeFamily;
  /** Vertices in mathematical coordinates (y up), in order around the shape. Empty for the circle. */
  vertices: Pt[];
  /** For regular polygons: the number of sides (names "Regular {n}-gon"). */
  regularN?: number;
}

const rad = (deg: number) => (deg * Math.PI) / 180;
const deg = (r: number) => (r * 180) / Math.PI;

/** Triangle with base AB = 1 on the x-axis and base angles alpha (at A) and beta (at B), in degrees. */
export function triangleFromAngles(alpha: number, beta: number): Pt[] {
  const gamma = 180 - alpha - beta;
  const ac = Math.sin(rad(beta)) / Math.sin(rad(gamma));
  return [
    { x: 0, y: 0 },
    { x: 1, y: 0 },
    { x: ac * Math.cos(rad(alpha)), y: ac * Math.sin(rad(alpha)) },
  ];
}

/** Regular n-gon of circumradius 1 standing on a horizontal edge. */
export function regularPolygon(n: number): Pt[] {
  return Array.from({ length: n }, (_, k) => {
    const th = rad(-90 + 180 / n + (k * 360) / n);
    return { x: Math.cos(th), y: Math.sin(th) };
  });
}

/**
 * A convex but irregular n-gon (points in angular order on an ellipse, so it is
 * always convex). Deterministic: the same n and seed always give the same shape.
 */
export function irregularPolygon(n: number, seed: number): Pt[] {
  let s = seedFrom(seed * 131 + n);
  return Array.from({ length: n }, (_, k) => {
    const [u, s2] = nextRandom(s);
    s = s2;
    const jitter = (u - 0.5) * 0.7 * (180 / n);
    const th = rad(-90 + 180 / n + (k * 360) / n + jitter);
    return { x: Math.cos(th), y: 0.8 * Math.sin(th) };
  });
}

const tanD = (d: number) => Math.tan(rad(d));

/** Quadrilaterals with exact integer angles. */
const QUADS: Record<string, Pt[]> = {
  square: [
    { x: 0, y: 0 },
    { x: 1, y: 0 },
    { x: 1, y: 1 },
    { x: 0, y: 1 },
  ],
  rectangle: [
    { x: 0, y: 0 },
    { x: 1.7, y: 0 },
    { x: 1.7, y: 1 },
    { x: 0, y: 1 },
  ],
  // 60° and 120° angles, all sides 1.
  rhombus: [
    { x: 0, y: 0 },
    { x: 1, y: 0 },
    { x: 1 + Math.cos(rad(60)), y: Math.sin(rad(60)) },
    { x: Math.cos(rad(60)), y: Math.sin(rad(60)) },
  ],
  // 70° and 110° angles, sides 1.5 and 1.
  parallelogram: [
    { x: 0, y: 0 },
    { x: 1.5, y: 0 },
    { x: 1.5 + Math.cos(rad(70)), y: Math.sin(rad(70)) },
    { x: Math.cos(rad(70)), y: Math.sin(rad(70)) },
  ],
  // Base angles 60° and 75°, so the top angles are 120° and 105°; no two sides are equal.
  trapezoid: [
    { x: 0, y: 0 },
    { x: 2, y: 0 },
    { x: 2 - 0.9 / tanD(75), y: 0.9 },
    { x: 0.9 / tanD(60), y: 0.9 },
  ],
  // Base angles 65° and 65°, top angles 115° and 115°.
  isoTrapezoid: [
    { x: 0, y: 0 },
    { x: 2, y: 0 },
    { x: 2 - 0.9 / tanD(65), y: 0.9 },
    { x: 0.9 / tanD(65), y: 0.9 },
  ],
  // Top angle 50°, bottom angle 110°, side angles 100° each.
  kite: [
    { x: 0, y: 1 / tanD(25) },
    { x: 1, y: 0 },
    { x: 0, y: -1 / tanD(55) },
    { x: -1, y: 0 },
  ],
};

const TRIANGLES: Record<string, [number, number]> = {
  equilateral: [60, 60],
  isosceles: [70, 70],
  scalene: [50, 70],
  right: [90, 30],
  rightIsosceles: [90, 45],
  obtuse: [25, 35],
};

const NAMED_REGULAR: Record<number, string> = { 5: "pentagon", 6: "hexagon", 7: "heptagon", 8: "octagon", 9: "nonagon", 10: "decagon" };

/** Ids accepted in the `shapes` prop, with aliases. */
const ALIASES: Record<string, string> = {
  "right-isosceles": "rightIsosceles",
  trapezium: "trapezoid",
  "isosceles-trapezoid": "isoTrapezoid",
  "isosceles-trapezium": "isoTrapezoid",
  "regular-3": "equilateral",
  "regular-4": "square",
};

export const DEFAULT_GALLERY = [
  "equilateral",
  "isosceles",
  "scalene",
  "right",
  "obtuse",
  "square",
  "rectangle",
  "rhombus",
  "parallelogram",
  "trapezoid",
  "kite",
  "pentagon",
  "hexagon",
  "octagon",
  "circle",
];

/** Look up a shape by the id a lesson author wrote. Unknown ids give null. */
export function getShape(rawId: string): ShapeDef | null {
  if (typeof rawId !== "string") return null;
  const id = rawId.trim();
  const key = ALIASES[id] ?? id;
  if (key === "circle") return { id, key, family: "circle", vertices: [] };
  if (key in TRIANGLES) return { id, key, family: "triangle", vertices: triangleFromAngles(...TRIANGLES[key]) };
  if (key in QUADS) return { id, key, family: "quadrilateral", vertices: QUADS[key] };
  const named = Object.entries(NAMED_REGULAR).find(([, name]) => name === key);
  const m = /^regular-(\d+)$/.exec(key);
  const n = named ? Number(named[0]) : m ? Number(m[1]) : NaN;
  if (Number.isInteger(n) && n >= 5 && n <= 12) {
    return { id, key: NAMED_REGULAR[n] ?? "regularN", family: "polygon", vertices: regularPolygon(n), regularN: n };
  }
  return null;
}

/** The gallery from the `shapes` prop: valid ids in order, without duplicates; the default gallery if none are valid. */
export function resolveGallery(ids: unknown): ShapeDef[] {
  const out: ShapeDef[] = [];
  if (Array.isArray(ids)) {
    for (const raw of ids) {
      const s = typeof raw === "string" ? getShape(raw) : null;
      if (s && !out.some((o) => o.key === s.key && o.regularN === s.regularN)) out.push(s);
    }
  }
  return out.length ? out : DEFAULT_GALLERY.map((id) => getShape(id)!);
}

/* ---------- analysis (works in any coordinates) ---------- */

const dist = (a: Pt, b: Pt) => Math.hypot(a.x - b.x, a.y - b.y);

export function centroid(v: Pt[]): Pt {
  const n = v.length || 1;
  return { x: v.reduce((s, p) => s + p.x, 0) / n, y: v.reduce((s, p) => s + p.y, 0) / n };
}

/** Signed area (positive when the vertices run anticlockwise in y-up coordinates). */
export function signedArea(v: Pt[]): number {
  let a = 0;
  for (let i = 0; i < v.length; i++) {
    const p = v[i];
    const q = v[(i + 1) % v.length];
    a += p.x * q.y - q.x * p.y;
  }
  return a / 2;
}

/** Side i joins vertex i to vertex i + 1. */
export function sideLengths(v: Pt[]): number[] {
  return v.map((p, i) => dist(p, v[(i + 1) % v.length]));
}

/** Interior angles in degrees (correct for any simple polygon, convex or not). */
export function interiorAngles(v: Pt[]): number[] {
  const orient = Math.sign(signedArea(v)) || 1;
  return v.map((p, i) => {
    const a = v[(i - 1 + v.length) % v.length];
    const b = v[(i + 1) % v.length];
    const d1 = { x: p.x - a.x, y: p.y - a.y };
    const d2 = { x: b.x - p.x, y: b.y - p.y };
    const turn = Math.atan2(d1.x * d2.y - d1.y * d2.x, d1.x * d2.x + d1.y * d2.y);
    return 180 - deg(turn) * orient;
  });
}

/** (n − 2) × 180°. */
export const angleSum = (n: number) => (n - 2) * 180;

/** Number of diagonals of an n-gon: n(n − 3)/2. */
export const diagonalCount = (n: number) => (n * (n - 3)) / 2;

/** All diagonals as vertex-index pairs. */
export function diagonals(n: number): [number, number][] {
  const out: [number, number][] = [];
  for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) if (!(i === 0 && j === n - 1)) out.push([i, j]);
  return out;
}

/**
 * Group equal values (relative tolerance). Returns, for each index, a mark
 * number 1, 2, 3… shared by equal values, or 0 when the value is unique.
 */
export function equalMarks(values: number[], tol = 1e-6): number[] {
  const marks = values.map(() => 0);
  let next = 1;
  values.forEach((x, i) => {
    if (marks[i]) return;
    const same = values.map((y, j) => (Math.abs(x - y) <= tol * Math.max(1, Math.abs(x)) ? j : -1)).filter((j) => j >= 0);
    if (same.length > 1) {
      for (const j of same) marks[j] = next;
      next++;
    }
  });
  return marks;
}

/** Direction of each side in degrees, modulo 180. */
function sideDirections(v: Pt[]): number[] {
  return v.map((p, i) => {
    const q = v[(i + 1) % v.length];
    return ((deg(Math.atan2(q.y - p.y, q.x - p.x)) % 180) + 180) % 180;
  });
}

/** Parallel classes of sides: mark number per side (0 = parallel to no other side). */
export function parallelMarks(v: Pt[], tol = 1e-6): number[] {
  const dirs = sideDirections(v);
  const marks = dirs.map(() => 0);
  let next = 1;
  const close = (a: number, b: number) => {
    const d = Math.abs(a - b);
    return Math.min(d, 180 - d) < tol * 180;
  };
  dirs.forEach((a, i) => {
    if (marks[i]) return;
    const same = dirs.map((b, j) => (close(a, b) ? j : -1)).filter((j) => j >= 0);
    if (same.length > 1) {
      for (const j of same) marks[j] = next;
      next++;
    }
  });
  return marks;
}

/** Number of pairs of parallel sides. */
export function parallelPairCount(v: Pt[]): number {
  const marks = parallelMarks(v);
  const sizes = new Map<number, number>();
  for (const m of marks) if (m) sizes.set(m, (sizes.get(m) ?? 0) + 1);
  let pairs = 0;
  for (const k of sizes.values()) pairs += (k * (k - 1)) / 2;
  return pairs;
}

function sameVertexSet(a: Pt[], b: Pt[], tol: number): boolean {
  return a.every((p) => b.some((q) => dist(p, q) < tol));
}

function scaleOf(v: Pt[]): number {
  const c = centroid(v);
  return Math.max(1e-9, ...v.map((p) => dist(p, c)));
}

/**
 * Lines of symmetry, as directions in degrees (0 ≤ θ < 180) through the
 * vertex centroid. Every symmetry of a polygon fixes that centroid and passes
 * through a vertex or an edge midpoint, so these candidates are exhaustive.
 */
export function symmetryAxes(v: Pt[]): number[] {
  if (v.length < 3) return [];
  const c = centroid(v);
  const tol = 1e-6 * scaleOf(v);
  const candidates: Pt[] = [...v, ...v.map((p, i) => ({ x: (p.x + v[(i + 1) % v.length].x) / 2, y: (p.y + v[(i + 1) % v.length].y) / 2 }))];
  const found: number[] = [];
  for (const p of candidates) {
    const dx = p.x - c.x;
    const dy = p.y - c.y;
    if (Math.hypot(dx, dy) < tol) continue;
    const th = Math.atan2(dy, dx);
    const cos2 = Math.cos(2 * th);
    const sin2 = Math.sin(2 * th);
    const reflected = v.map((q) => {
      const x = q.x - c.x;
      const y = q.y - c.y;
      return { x: c.x + x * cos2 + y * sin2, y: c.y + x * sin2 - y * cos2 };
    });
    if (!sameVertexSet(reflected, v, tol * 10)) continue;
    const d = ((deg(th) % 180) + 180) % 180;
    if (!found.some((f) => Math.min(Math.abs(f - d), 180 - Math.abs(f - d)) < 1e-4)) found.push(d);
  }
  return found.sort((a, b) => a - b);
}

/** Order of rotational symmetry (1 means only the full turn works). */
export function rotationOrder(v: Pt[]): number {
  if (v.length < 3) return 1;
  const c = centroid(v);
  const tol = 1e-5 * scaleOf(v);
  for (let k = v.length; k >= 2; k--) {
    const a = (2 * Math.PI) / k;
    const rot = v.map((p) => {
      const x = p.x - c.x;
      const y = p.y - c.y;
      return { x: c.x + x * Math.cos(a) - y * Math.sin(a), y: c.y + x * Math.sin(a) + y * Math.cos(a) };
    });
    if (sameVertexSet(rot, v, tol)) return k;
  }
  return 1;
}

/** Fan triangulation from vertex 0: the n − 2 triangles (0, i, i + 1). */
export function fanTriangles(n: number): [number, number, number][] {
  return Array.from({ length: Math.max(0, n - 2) }, (_, i) => [0, i + 1, i + 2] as [number, number, number]);
}

/**
 * Fit math-coordinate points (y up) into an SVG box (y down), centred, with padding.
 * Returns the mapped points and the scale used.
 */
export function fitToBox(v: Pt[], w: number, h: number, pad: number): { points: Pt[]; scale: number } {
  if (v.length === 0) return { points: [], scale: 1 };
  const xs = v.map((p) => p.x);
  const ys = v.map((p) => p.y);
  const minX = Math.min(...xs);
  const maxX = Math.max(...xs);
  const minY = Math.min(...ys);
  const maxY = Math.max(...ys);
  const bw = Math.max(1e-9, maxX - minX);
  const bh = Math.max(1e-9, maxY - minY);
  const scale = Math.min((w - 2 * pad) / bw, (h - 2 * pad) / bh);
  const ox = (w - bw * scale) / 2;
  const oy = (h - bh * scale) / 2;
  return { points: v.map((p) => ({ x: ox + (p.x - minX) * scale, y: oy + (maxY - p.y) * scale })), scale };
}

/** "60°" when the angle is a whole number of degrees, otherwise "≈128.6°" (honest rounding). */
export function formatAngle(d: number): string {
  const r = Math.round(d);
  if (Math.abs(d - r) < 1e-6) return `${r}°`;
  return `≈${(Math.round(d * 10) / 10).toFixed(1)}°`;
}

/** Whether an angle is a right angle (to floating-point accuracy). */
export const isRight = (d: number) => Math.abs(d - 90) < 1e-6;

/**
 * Round each value to `dp` decimal places so that the rounded values still add
 * up to `total` exactly (largest-remainder method). Every rounded value is
 * within one unit of the last place of the true value.
 */
export function roundPreservingSum(values: number[], dp: number, total: number): number[] {
  const k = 10 ** dp;
  const scaled = values.map((v) => v * k);
  const floors = scaled.map(Math.floor);
  let missing = Math.round(total * k) - floors.reduce((s, f) => s + f, 0);
  const order = scaled.map((v, i) => ({ i, r: v - Math.floor(v) })).sort((a, b) => b.r - a.r);
  const out = [...floors];
  for (const { i } of order) {
    if (missing <= 0) break;
    out[i] += 1;
    missing--;
  }
  return out.map((v) => v / k);
}
