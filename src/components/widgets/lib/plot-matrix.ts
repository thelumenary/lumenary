/**
 * 2×2 real matrices for MatrixTransform: parsing, products, determinant,
 * eigen-structure (distinct real, repeated, defective or complex) and the
 * preset transformations of the plane. Pure functions, unit-tested.
 */
import { toNumber } from "./expr";

export type Vec2 = [number, number];
/** Row-major: [[a, b], [c, d]] acts on column vectors. */
export type Mat2 = [[number, number], [number, number]];

export const IDENTITY: Mat2 = [
  [1, 0],
  [0, 1],
];

const LIMIT = 100;
const tidy = (v: number) => (Math.abs(v) < 1e-12 ? 0 : v);

/** Read a matrix prop: [[a, b], [c, d]] or [a, b, c, d]; entries may be numbers or constant expressions ("sqrt(2)/2"). */
export function toMatrix(value: unknown, fallback: Mat2): Mat2 {
  let flat: unknown[] | null = null;
  if (Array.isArray(value) && value.length === 2 && Array.isArray(value[0]) && Array.isArray(value[1])) flat = [value[0][0], value[0][1], value[1][0], value[1][1]];
  else if (Array.isArray(value) && value.length === 4) flat = value;
  if (!flat) return cloneM(fallback);
  const nums = flat.map((v) => toNumber(v, NaN));
  if (!nums.every(Number.isFinite)) return cloneM(fallback);
  const c = nums.map((v) => Math.max(-LIMIT, Math.min(LIMIT, v)));
  return [
    [c[0], c[1]],
    [c[2], c[3]],
  ];
}

export const cloneM = (m: Mat2): Mat2 => [
  [m[0][0], m[0][1]],
  [m[1][0], m[1][1]],
];

// "+ 0" turns a negative zero into 0, so results print and compare cleanly.
export function apply(m: Mat2, v: Vec2): Vec2 {
  return [m[0][0] * v[0] + m[0][1] * v[1] + 0, m[1][0] * v[0] + m[1][1] * v[1] + 0];
}

/** The product A·B: first apply B, then A. */
export function mul(A: Mat2, B: Mat2): Mat2 {
  return [
    [A[0][0] * B[0][0] + A[0][1] * B[1][0] + 0, A[0][0] * B[0][1] + A[0][1] * B[1][1] + 0],
    [A[1][0] * B[0][0] + A[1][1] * B[1][0] + 0, A[1][0] * B[0][1] + A[1][1] * B[1][1] + 0],
  ];
}

export const det = (m: Mat2) => m[0][0] * m[1][1] - m[0][1] * m[1][0];
export const trace = (m: Mat2) => m[0][0] + m[1][1];

/** Straight-line path from A (s = 0) to B (s = 1). */
export function lerpM(A: Mat2, B: Mat2, s: number): Mat2 {
  const l = (p: number, q: number) => p + (q - p) * s;
  return [
    [l(A[0][0], B[0][0]), l(A[0][1], B[0][1])],
    [l(A[1][0], B[1][0]), l(A[1][1], B[1][1])],
  ];
}

export function equalM(A: Mat2, B: Mat2, eps = 1e-9): boolean {
  return A.every((row, i) => row.every((v, j) => Math.abs(v - B[i][j]) <= eps * Math.max(1, Math.abs(v), Math.abs(B[i][j]))));
}

export type Eigen =
  | { kind: "distinct"; values: [number, number]; vectors: [Vec2, Vec2] }
  | { kind: "scalar"; value: number }
  | { kind: "defective"; value: number; vector: Vec2 }
  | { kind: "complex"; re: number; im: number };

/** Scale a direction so its largest component is ±1 and it points right (or up). */
export function niceDirection(v: Vec2): Vec2 {
  const m = Math.max(Math.abs(v[0]), Math.abs(v[1]));
  if (!(m > 0)) return [1, 0];
  let x = v[0] / m;
  let y = v[1] / m;
  if (x < -1e-12 || (Math.abs(x) <= 1e-12 && y < 0)) {
    x = -x;
    y = -y;
  }
  return [tidy(x), tidy(y)];
}

function eigenvector(m: Mat2, lambda: number): Vec2 {
  const [[a, b], [c, d]] = m;
  // Use the row of A − λI with the larger entries for numerical stability.
  const r1 = Math.abs(a - lambda) + Math.abs(b);
  const r2 = Math.abs(c) + Math.abs(d - lambda);
  if (r1 < 1e-12 && r2 < 1e-12) return [1, 0];
  return niceDirection(r1 >= r2 ? [b, lambda - a] : [lambda - d, c]);
}

/** Real eigenvalues and eigenvectors when they exist; otherwise the complex pair. */
export function eigen(m: Mat2): Eigen {
  const tr = trace(m);
  const dt = det(m);
  const scale = Math.max(1, ...m.flat().map(Math.abs));
  const eps = 1e-10 * scale * scale;
  const disc = (tr * tr) / 4 - dt;
  if (disc > eps) {
    const s = Math.sqrt(disc);
    const l1 = tidy(tr / 2 + s);
    const l2 = tidy(tr / 2 - s);
    return { kind: "distinct", values: [l1, l2], vectors: [eigenvector(m, l1), eigenvector(m, l2)] };
  }
  if (disc >= -eps) {
    const l = tidy(tr / 2);
    const isScalar = Math.abs(m[0][1]) <= 1e-9 * scale && Math.abs(m[1][0]) <= 1e-9 * scale && Math.abs(m[0][0] - m[1][1]) <= 1e-9 * scale;
    return isScalar ? { kind: "scalar", value: l } : { kind: "defective", value: l, vector: eigenvector(m, l) };
  }
  return { kind: "complex", re: tidy(tr / 2), im: Math.sqrt(-disc) };
}

/** If m is a rotation (orthogonal, det 1), its angle in radians in (−π, π]; otherwise null. */
export function rotationAngle(m: Mat2, eps = 1e-9): number | null {
  const [[a, b], [c, d]] = m;
  if (Math.abs(a - d) > eps || Math.abs(b + c) > eps || Math.abs(a * a + c * c - 1) > 1e-6) return null;
  return Math.atan2(c, a);
}

/* ---------------------------------------------------------------------------
 * Presets
 * ------------------------------------------------------------------------- */

export const PRESET_IDS = ["identity", "rotation", "reflection", "shear", "scale", "projection", "singular"] as const;
export type PresetId = (typeof PRESET_IDS)[number];

export interface PresetParam {
  key: string;
  min: number;
  max: number;
  step: number;
  value: number;
  /** "deg" values are shown with a degree sign and converted to radians. */
  unit?: "deg";
}

export const PRESET_PARAMS: Record<PresetId, PresetParam[]> = {
  identity: [],
  rotation: [{ key: "theta", min: -180, max: 180, step: 1, value: 45, unit: "deg" }],
  reflection: [{ key: "phi", min: -90, max: 90, step: 1, value: 45, unit: "deg" }],
  shear: [{ key: "k", min: -3, max: 3, step: 0.1, value: 1 }],
  scale: [
    { key: "sx", min: -3, max: 3, step: 0.1, value: 2 },
    { key: "sy", min: -3, max: 3, step: 0.1, value: 0.5 },
  ],
  projection: [{ key: "phi", min: -90, max: 90, step: 1, value: 30, unit: "deg" }],
  singular: [],
};

export const defaultParams = (id: PresetId): Record<string, number> => Object.fromEntries(PRESET_PARAMS[id].map((p) => [p.key, p.value]));

export function isPresetId(v: unknown): v is PresetId {
  return typeof v === "string" && (PRESET_IDS as readonly string[]).includes(v);
}

const DEG = Math.PI / 180;

/** The matrix of a preset. Angles in degrees; reflection/projection use the line through 0 at angle φ. */
export function presetMatrix(id: PresetId, p: Record<string, number> = {}): Mat2 {
  const v = (k: string) => (Number.isFinite(p[k]) ? p[k] : (PRESET_PARAMS[id].find((q) => q.key === k)?.value ?? 0));
  let m: Mat2;
  switch (id) {
    case "rotation": {
      const t = v("theta") * DEG;
      m = [
        [Math.cos(t), -Math.sin(t)],
        [Math.sin(t), Math.cos(t)],
      ];
      break;
    }
    case "reflection": {
      const f = 2 * v("phi") * DEG;
      m = [
        [Math.cos(f), Math.sin(f)],
        [Math.sin(f), -Math.cos(f)],
      ];
      break;
    }
    case "shear":
      m = [
        [1, v("k")],
        [0, 1],
      ];
      break;
    case "scale":
      m = [
        [v("sx"), 0],
        [0, v("sy")],
      ];
      break;
    case "projection": {
      const f = v("phi") * DEG;
      const c = Math.cos(f);
      const s = Math.sin(f);
      m = [
        [c * c, c * s],
        [c * s, s * s],
      ];
      break;
    }
    case "singular":
      m = [
        [1, 2],
        [0.5, 1],
      ];
      break;
    default:
      m = cloneM(IDENTITY);
  }
  return m.map((row) => row.map(tidy)) as Mat2;
}

/** Read the `presets` prop: a list of preset ids to offer (unknown ids ignored; default all). */
export function toPresetList(value: unknown): PresetId[] {
  if (!Array.isArray(value)) return [...PRESET_IDS];
  const out = value.filter(isPresetId);
  return [...new Set(out)];
}

/* ---------------------------------------------------------------------------
 * Pictures
 * ------------------------------------------------------------------------- */

/** An asymmetric flag inside the unit square: a pole and a pennant, so reflections are visible. */
export const FLAG: { pole: Vec2[]; pennant: Vec2[] } = {
  pole: [
    [0.22, 0.12],
    [0.32, 0.12],
    [0.32, 0.88],
    [0.22, 0.88],
  ],
  pennant: [
    [0.32, 0.88],
    [0.82, 0.7],
    [0.32, 0.52],
  ],
};

export const UNIT_SQUARE: Vec2[] = [
  [0, 0],
  [1, 0],
  [1, 1],
  [0, 1],
];

/** Images of the grid lines x = i and y = j (|i|, |j| ≤ n) as segments, long enough to cross the view. */
export function gridImage(m: Mat2, n: number, reach: number): { vertical: [Vec2, Vec2][]; horizontal: [Vec2, Vec2][] } {
  const vertical: [Vec2, Vec2][] = [];
  const horizontal: [Vec2, Vec2][] = [];
  for (let i = -n; i <= n; i++) {
    vertical.push([apply(m, [i, -reach]), apply(m, [i, reach])]);
    horizontal.push([apply(m, [-reach, i]), apply(m, [reach, i])]);
  }
  return { vertical, horizontal };
}

/** Image of the small counter-clockwise quarter arc from e₁ to e₂ (radius r): shows orientation. */
export function orientationArc(m: Mat2, r = 0.42, steps = 24): Vec2[] {
  return Array.from({ length: steps + 1 }, (_, k) => {
    const t = (k / steps) * (Math.PI / 2);
    return apply(m, [r * Math.cos(t), r * Math.sin(t)]);
  });
}
