/**
 * Closed surfaces from the unit square [0,1]² with its edges identified in pairs.
 * The boundary word is read counter-clockwise from the bottom-left corner:
 * bottom, right, top, left. A letter with exponent +1 has its arrow pointing
 * along that counter-clockwise direction, exponent −1 against it.
 *
 * A walker that leaves through one edge re-enters through its partner. The
 * re-entry is an affine map p ↦ M p + t with M orthogonal; det M = −1 means the
 * walker comes back mirror-reversed.
 */
import type { V2 } from "./topo-vec";

export const SURFACE_IDS = ["torus", "klein", "sphere", "rp2"] as const;
export type SurfaceId = (typeof SURFACE_IDS)[number];
export const isSurfaceId = (v: unknown): v is SurfaceId => typeof v === "string" && (SURFACE_IDS as readonly string[]).includes(v);

export type Side = "bottom" | "right" | "top" | "left";
export const SIDES: Side[] = ["bottom", "right", "top", "left"];

/** 2×2 matrix [[a, b], [c, d]] stored row-major. */
export type M2 = [number, number, number, number];
export interface Affine {
  m: M2;
  t: V2;
}

export interface SurfaceDef {
  id: SurfaceId;
  /** Letter and exponent on each side, in the order bottom, right, top, left. */
  word: [Letter, Letter, Letter, Letter];
  /** Where a walker leaving through each side re-enters. */
  exit: Record<Side, Affine>;
  orientable: boolean;
  chi: number;
  /** The universal cover is the plane, so copies of the square tile it. */
  tiles: boolean;
}
export interface Letter {
  name: "a" | "b";
  exp: 1 | -1;
}

const T = (a: number, b: number, c: number, d: number, tx: number, ty: number): Affine => ({ m: [a, b, c, d], t: [tx, ty] });
const L = (name: "a" | "b", exp: 1 | -1): Letter => ({ name, exp });

export const SURFACES: Record<SurfaceId, SurfaceDef> = {
  // a b a⁻¹ b⁻¹ : (x,0)~(x,1), (0,y)~(1,y)
  torus: {
    id: "torus",
    word: [L("a", 1), L("b", 1), L("a", -1), L("b", -1)],
    exit: { right: T(1, 0, 0, 1, -1, 0), left: T(1, 0, 0, 1, 1, 0), top: T(1, 0, 0, 1, 0, -1), bottom: T(1, 0, 0, 1, 0, 1) },
    orientable: true,
    chi: 0,
    tiles: true,
  },
  // a b a⁻¹ b : (x,0)~(x,1), (0,y)~(1,1−y)
  klein: {
    id: "klein",
    word: [L("a", 1), L("b", 1), L("a", -1), L("b", 1)],
    exit: { right: T(1, 0, 0, -1, -1, 1), left: T(1, 0, 0, -1, 1, 1), top: T(1, 0, 0, 1, 0, -1), bottom: T(1, 0, 0, 1, 0, 1) },
    orientable: false,
    chi: 0,
    tiles: true,
  },
  // a a⁻¹ b b⁻¹ : bottom glued to right (folding at corner (1,0)), top glued to left (folding at (0,1))
  sphere: {
    id: "sphere",
    word: [L("a", 1), L("a", -1), L("b", 1), L("b", -1)],
    exit: { bottom: T(0, 1, -1, 0, 1, 1), right: T(0, -1, 1, 0, 1, -1), top: T(0, 1, -1, 0, -1, 1), left: T(0, -1, 1, 0, 1, 1) },
    orientable: true,
    chi: 2,
    tiles: false,
  },
  // a b a b : (x,0)~(1−x,1), (0,y)~(1,1−y)
  rp2: {
    id: "rp2",
    word: [L("a", 1), L("b", 1), L("a", 1), L("b", 1)],
    exit: { right: T(1, 0, 0, -1, -1, 1), left: T(1, 0, 0, -1, 1, 1), top: T(-1, 0, 0, 1, 1, -1), bottom: T(-1, 0, 0, 1, 1, 1) },
    orientable: false,
    chi: 1,
    tiles: false,
  },
};

export const applyAffine = (f: Affine, p: V2): V2 => [f.m[0] * p[0] + f.m[1] * p[1] + f.t[0], f.m[2] * p[0] + f.m[3] * p[1] + f.t[1]];
export const applyLinear = (m: M2, v: V2): V2 => [m[0] * v[0] + m[1] * v[1], m[2] * v[0] + m[3] * v[1]];
export const mulM2 = (a: M2, b: M2): M2 => [a[0] * b[0] + a[1] * b[2], a[0] * b[1] + a[1] * b[3], a[2] * b[0] + a[3] * b[2], a[2] * b[1] + a[3] * b[3]];
export const detM2 = (m: M2) => m[0] * m[3] - m[1] * m[2];

/** The corners at the tail and head of each side's arrow (in the counter-clockwise reading, flipped for exponent −1). */
export function sideArrow(s: Side, exp: 1 | -1): [V2, V2] {
  const ccw: Record<Side, [V2, V2]> = { bottom: [[0, 0], [1, 0]], right: [[1, 0], [1, 1]], top: [[1, 1], [0, 1]], left: [[0, 1], [0, 0]] };
  const [p, q] = ccw[s];
  return exp === 1 ? [p, q] : [q, p];
}

export const partnerSide = (def: SurfaceDef, s: Side): Side => {
  const i = SIDES.indexOf(s);
  const j = SIDES.findIndex((_, k) => k !== i && def.word[k].name === def.word[i].name);
  return SIDES[j];
};

/** V − E + F of the square with identifications: corners glued by the arrows, E = 2, F = 1. */
export function squareEuler(def: SurfaceDef): { V: number; E: number; F: number; chi: number } {
  const key = (p: V2) => `${p[0]},${p[1]}`;
  const parent = new Map<string, string>();
  const find = (k: string): string => {
    const p = parent.get(k) ?? k;
    if (p === k) return k;
    const r = find(p);
    parent.set(k, r);
    return r;
  };
  const union = (a: string, b: string) => parent.set(find(a), find(b));
  for (const c of [[0, 0], [1, 0], [1, 1], [0, 1]] as V2[]) parent.set(key(c), key(c));
  SIDES.forEach((s, i) => {
    const other = partnerSide(def, s);
    const [p, q] = sideArrow(s, def.word[i].exp);
    const [p2, q2] = sideArrow(other, def.word[SIDES.indexOf(other)].exp);
    union(key(p), key(p2));
    union(key(q), key(q2));
  });
  const V = new Set([...parent.keys()].map(find)).size;
  return { V, E: 2, F: 1, chi: V - 2 + 1 };
}

export interface Walker {
  p: V2;
  /** Columns: forward direction and the walker's own left, in square coordinates. */
  frame: M2;
}
export interface Crossing {
  from: Side;
  to: Side;
  /** Exit point on the old side and entry point on the new side. */
  out: V2;
  in: V2;
}

/** Forward direction (first column of the frame). */
export const heading = (w: Walker): V2 => [w.frame[0], w.frame[2]];
/** The walker's own left (second column). */
export const leftOf = (w: Walker): V2 => [w.frame[1], w.frame[3]];
export const isMirrored = (w: Walker) => detM2(w.frame) < 0;

export function makeWalker(p: V2 = [0.3, 0.35], angle = 0.35): Walker {
  const c = Math.cos(angle);
  const s = Math.sin(angle);
  return { p, frame: [c, -s, s, c] };
}

/** Turn toward the walker's own left by `a` radians (looks clockwise to us when it is mirrored). */
export function turn(w: Walker, a: number): Walker {
  const h = heading(w);
  const l = leftOf(w);
  const c = Math.cos(a);
  const s = Math.sin(a);
  const nh: V2 = [c * h[0] + s * l[0], c * h[1] + s * l[1]];
  const nl: V2 = [-s * h[0] + c * l[0], -s * h[1] + c * l[1]];
  return { ...w, frame: [nh[0], nl[0], nh[1], nl[1]] };
}

/**
 * Move by displacement `d` (square coordinates), re-entering through partner
 * edges as needed. Also returns the edges crossed, and `chart`: the linear part
 * of all re-entry maps applied (so a drag can keep moving "straight on").
 */
export function move(def: SurfaceDef, w: Walker, d: V2): { walker: Walker; crossings: Crossing[]; chart: M2 } {
  let p: V2 = [...w.p];
  let frame = w.frame;
  let rest: V2 = [...d];
  let chart: M2 = [1, 0, 0, 1];
  const crossings: Crossing[] = [];
  for (let guard = 0; guard < 12; guard++) {
    const tx = rest[0] > 1e-15 ? (1 - p[0]) / rest[0] : rest[0] < -1e-15 ? -p[0] / rest[0] : Infinity;
    const ty = rest[1] > 1e-15 ? (1 - p[1]) / rest[1] : rest[1] < -1e-15 ? -p[1] / rest[1] : Infinity;
    const t = Math.min(tx, ty);
    if (t >= 1) {
      p = [p[0] + rest[0], p[1] + rest[1]];
      break;
    }
    const tt = Math.max(0, t);
    const hit: V2 = [p[0] + rest[0] * tt, p[1] + rest[1] * tt];
    const side: Side = tx <= ty ? (rest[0] > 0 ? "right" : "left") : rest[1] > 0 ? "top" : "bottom";
    // snap the hit point onto the side exactly
    if (side === "right") hit[0] = 1;
    if (side === "left") hit[0] = 0;
    if (side === "top") hit[1] = 1;
    if (side === "bottom") hit[1] = 0;
    const f = def.exit[side];
    const entry = applyAffine(f, hit);
    entry[0] = Math.min(1, Math.max(0, entry[0]));
    entry[1] = Math.min(1, Math.max(0, entry[1]));
    crossings.push({ from: side, to: partnerSide(def, side), out: hit, in: entry });
    const remaining: V2 = [rest[0] * (1 - tt), rest[1] * (1 - tt)];
    rest = applyLinear(f.m, remaining);
    frame = mulM2(f.m, frame);
    chart = mulM2(f.m, chart);
    p = entry;
  }
  p = [Math.min(1, Math.max(0, p[0])), Math.min(1, Math.max(0, p[1]))];
  return { walker: { p, frame }, crossings, chart };
}

/**
 * The copy of the square at tile (i, j) of the plane tiling (torus and Klein bottle):
 * returns whether that copy is mirrored (y ↦ 1 − y). For the torus all copies are translates;
 * for the Klein bottle (left/right sides glued with a flip) every other column is mirrored.
 */
export function tileMirrored(id: SurfaceId, i: number): boolean {
  return id === "klein" && Math.abs(i) % 2 === 1;
}

/** Map a point of the square into tile (i, j) of the tiling. */
export function toTile(id: SurfaceId, i: number, j: number, p: V2): V2 {
  return [i + p[0], j + (tileMirrored(id, i) ? 1 - p[1] : p[1])];
}
