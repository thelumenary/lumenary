/**
 * Small vector and matrix helpers shared by the topology/geometry widgets.
 * Pure functions on plain tuples, so they are easy to test and serialise.
 */

export type V2 = [number, number];
export type V3 = [number, number, number];
/** A 3×3 matrix in row-major order. */
export type M3 = [number, number, number, number, number, number, number, number, number];

export const TAU = 2 * Math.PI;
export const DEG = 180 / Math.PI;

export const clamp = (v: number, lo: number, hi: number) => (Number.isFinite(v) ? Math.min(hi, Math.max(lo, v)) : lo);
export const isNum = (v: unknown): v is number => typeof v === "number" && Number.isFinite(v);

// ---------- 2D ----------
export const sub2 = (a: V2, b: V2): V2 => [a[0] - b[0], a[1] - b[1]];
export const dot2 = (a: V2, b: V2) => a[0] * b[0] + a[1] * b[1];
export const cross2 = (a: V2, b: V2) => a[0] * b[1] - a[1] * b[0];
export const len2 = (a: V2) => Math.hypot(a[0], a[1]);
export const norm2 = (a: V2): V2 => {
  const l = len2(a);
  return l > 1e-15 ? [a[0] / l, a[1] / l] : [0, 0];
};
/** Rotate by +90° (counter-clockwise when y points up). */
export const perp2 = (a: V2): V2 => [-a[1], a[0]];
/** Unsigned angle between two vectors, in radians, robust for nearly parallel vectors. */
export const angle2 = (a: V2, b: V2) => Math.atan2(Math.abs(cross2(a, b)), dot2(a, b));

// ---------- 3D ----------
export const add3 = (a: V3, b: V3): V3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
export const sub3 = (a: V3, b: V3): V3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
export const scale3 = (a: V3, k: number): V3 => [a[0] * k, a[1] * k, a[2] * k];
export const dot3 = (a: V3, b: V3) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
export const cross3 = (a: V3, b: V3): V3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
export const len3 = (a: V3) => Math.hypot(a[0], a[1], a[2]);
export const norm3 = (a: V3): V3 => {
  const l = len3(a);
  return l > 1e-15 ? [a[0] / l, a[1] / l, a[2] / l] : [0, 0, 0];
};
/** Unsigned angle between two 3D vectors (radians). */
export const angle3 = (a: V3, b: V3) => Math.atan2(len3(cross3(a, b)), dot3(a, b));

// ---------- 3×3 matrices ----------
export const IDENTITY3: M3 = [1, 0, 0, 0, 1, 0, 0, 0, 1];

export function mul3(a: M3, b: M3): M3 {
  const out = new Array(9).fill(0) as M3;
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) out[3 * i + j] = a[3 * i] * b[j] + a[3 * i + 1] * b[3 + j] + a[3 * i + 2] * b[6 + j];
  return out;
}
export const apply3 = (m: M3, v: V3): V3 => [m[0] * v[0] + m[1] * v[1] + m[2] * v[2], m[3] * v[0] + m[4] * v[1] + m[5] * v[2], m[6] * v[0] + m[7] * v[1] + m[8] * v[2]];
export const transpose3 = (m: M3): M3 => [m[0], m[3], m[6], m[1], m[4], m[7], m[2], m[5], m[8]];

/** Rotation about the x axis (y toward z). */
export function rotX(a: number): M3 {
  const c = Math.cos(a);
  const s = Math.sin(a);
  return [1, 0, 0, 0, c, -s, 0, s, c];
}
/** Rotation about the y axis (z toward x). */
export function rotY(a: number): M3 {
  const c = Math.cos(a);
  const s = Math.sin(a);
  return [c, 0, s, 0, 1, 0, -s, 0, c];
}

/** Re-orthonormalise a rotation matrix (rows) to stop drift after many small drags. */
export function orthonormalize(m: M3): M3 {
  const r0 = norm3([m[0], m[1], m[2]]);
  let r1: V3 = [m[3], m[4], m[5]];
  r1 = norm3(sub3(r1, scale3(r0, dot3(r0, r1))));
  const r2 = cross3(r0, r1);
  if (len3(r0) < 0.5 || len3(r1) < 0.5) return IDENTITY3;
  return [r0[0], r0[1], r0[2], r1[0], r1[1], r1[2], r2[0], r2[1], r2[2]];
}

/**
 * Turn a screen drag (dx, dy in "radians") into a view-space rotation that is
 * applied on the left, so dragging right turns the front of the object right
 * and dragging down tips the front down.
 */
export function dragRotate(m: M3, dx: number, dy: number): M3 {
  return orthonormalize(mul3(mul3(rotY(dx), rotX(dy)), m));
}

/** Round for SVG output: keeps markup small and identical between server and client. */
export const r2 = (v: number) => Math.round(v * 100) / 100;

/** Polyline → SVG path data. */
export function pathD(points: readonly V2[], closed = false): string {
  if (points.length === 0) return "";
  let d = `M${r2(points[0][0])} ${r2(points[0][1])}`;
  for (let i = 1; i < points.length; i++) d += `L${r2(points[i][0])} ${r2(points[i][1])}`;
  return closed ? `${d}Z` : d;
}
