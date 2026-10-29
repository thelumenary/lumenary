/**
 * Polyhedra and polyhedral surfaces for the Euler characteristic widget.
 * Convex solids are built from vertex lists (faces found as the convex hull);
 * the "picture-frame" tori are built by extruding a flat frame. Every face is
 * oriented outward and every edge borders exactly two faces (closed surfaces).
 */
import { add3, apply3, cross3, dot3, len3, norm3, scale3, sub3, type M3, type V3 } from "./topo-vec";

export const SOLID_IDS = ["tetrahedron", "cube", "octahedron", "dodecahedron", "icosahedron", "prism", "pyramid", "torus", "doubleTorus"] as const;
export type SolidId = (typeof SOLID_IDS)[number];

export interface Solid {
  id: SolidId;
  vertices: V3[];
  faces: number[][];
  edges: [number, number][];
  /** For each edge, the two faces that meet along it. */
  edgeFaces: [number, number][];
  /** Outward unit normal of each face. */
  normals: V3[];
  /** Genus of the surface (0 for a sphere-like solid). */
  genus: number;
}

const PHI = (1 + Math.sqrt(5)) / 2;

/** Faces of the convex hull of a small point set (brute force over triples; fine for ≤ 30 points). */
export function convexHullFaces(pts: V3[]): number[][] {
  const scale = Math.max(...pts.map(len3), 1e-9);
  const eps = 1e-7 * scale;
  const seen = new Set<string>();
  const faces: number[][] = [];
  const n = pts.length;
  for (let i = 0; i < n; i++)
    for (let j = i + 1; j < n; j++)
      for (let k = j + 1; k < n; k++) {
        let nrm = cross3(sub3(pts[j], pts[i]), sub3(pts[k], pts[i]));
        if (len3(nrm) < eps) continue;
        nrm = norm3(nrm);
        const d = dot3(nrm, pts[i]);
        let pos = 0;
        let neg = 0;
        const on: number[] = [];
        for (let m = 0; m < n; m++) {
          const s = dot3(nrm, pts[m]) - d;
          if (s > eps) pos++;
          else if (s < -eps) neg++;
          else on.push(m);
        }
        if (pos > 0 && neg > 0) continue;
        if (pos > 0) nrm = scale3(nrm, -1);
        const key = on.join(",");
        if (seen.has(key)) continue;
        seen.add(key);
        // order the coplanar points counter-clockwise as seen from outside
        const c = scale3(on.reduce<V3>((acc, m) => add3(acc, pts[m]), [0, 0, 0]), 1 / on.length);
        const u = norm3(sub3(pts[on[0]], c));
        const w = cross3(nrm, u);
        const ordered = [...on].sort((a, b) => {
          const pa = sub3(pts[a], c);
          const pb = sub3(pts[b], c);
          return Math.atan2(dot3(pa, w), dot3(pa, u)) - Math.atan2(dot3(pb, w), dot3(pb, u));
        });
        faces.push(ordered);
      }
  return faces;
}

/** Newell's method: a robust normal for a planar polygon (length = twice its area). */
export function newellNormal(pts: V3[], face: number[]): V3 {
  let nx = 0;
  let ny = 0;
  let nz = 0;
  for (let i = 0; i < face.length; i++) {
    const a = pts[face[i]];
    const b = pts[face[(i + 1) % face.length]];
    nx += (a[1] - b[1]) * (a[2] + b[2]);
    ny += (a[2] - b[2]) * (a[0] + b[0]);
    nz += (a[0] - b[0]) * (a[1] + b[1]);
  }
  return [nx, ny, nz];
}

/** Signed volume enclosed by oriented faces (positive when faces point outward). */
export function signedVolume(pts: V3[], faces: number[][]): number {
  let v = 0;
  for (const f of faces) for (let i = 1; i + 1 < f.length; i++) v += dot3(pts[f[0]], cross3(pts[f[i]], pts[f[i + 1]]));
  return v / 6;
}

const ekey = (a: number, b: number) => (a < b ? `${a}-${b}` : `${b}-${a}`);

/**
 * Make all faces consistently oriented (each edge traversed once in each
 * direction) and pointing outward. Returns new face arrays.
 */
export function orientFaces(pts: V3[], faces: number[][]): number[][] {
  const out = faces.map((f) => [...f]);
  const byEdge = new Map<string, number[]>();
  out.forEach((f, fi) => f.forEach((a, i) => {
    const k = ekey(a, f[(i + 1) % f.length]);
    byEdge.set(k, [...(byEdge.get(k) ?? []), fi]);
  }));
  const directed = (f: number[], a: number, b: number) => f.some((x, i) => x === a && f[(i + 1) % f.length] === b);
  const done = new Array(out.length).fill(false);
  for (let start = 0; start < out.length; start++) {
    if (done[start]) continue;
    done[start] = true;
    const queue = [start];
    while (queue.length) {
      const fi = queue.shift()!;
      const f = out[fi];
      for (let i = 0; i < f.length; i++) {
        const a = f[i];
        const b = f[(i + 1) % f.length];
        for (const gi of byEdge.get(ekey(a, b)) ?? []) {
          if (gi === fi || done[gi]) continue;
          if (directed(out[gi], a, b)) out[gi].reverse();
          done[gi] = true;
          queue.push(gi);
        }
      }
    }
  }
  if (signedVolume(pts, out) < 0) out.forEach((f) => f.reverse());
  return out;
}

/** Edges of a face list, plus the faces on each side of each edge. */
export function edgesOf(faces: number[][]): { edges: [number, number][]; edgeFaces: [number, number][] } {
  const map = new Map<string, { e: [number, number]; f: number[] }>();
  faces.forEach((f, fi) => f.forEach((a, i) => {
    const b = f[(i + 1) % f.length];
    const k = ekey(a, b);
    const entry = map.get(k) ?? { e: [Math.min(a, b), Math.max(a, b)] as [number, number], f: [] };
    entry.f.push(fi);
    map.set(k, entry);
  }));
  const edges: [number, number][] = [];
  const edgeFaces: [number, number][] = [];
  for (const { e, f } of map.values()) {
    edges.push(e);
    edgeFaces.push([f[0], f[1] ?? f[0]]);
  }
  return { edges, edgeFaces };
}

/** Extrude a flat frame (polygon with holes, already cut into disc faces) into a closed solid. */
function extrudeFrame(pts2: [number, number][], top: number[][], loops: number[][], h: number) {
  const n = pts2.length;
  const vertices: V3[] = [...pts2.map(([x, z]) => [x, h, z] as V3), ...pts2.map(([x, z]) => [x, -h, z] as V3)];
  const faces: number[][] = [...top.map((f) => [...f]), ...top.map((f) => f.map((i) => i + n).reverse())];
  for (const loop of loops)
    for (let i = 0; i < loop.length; i++) {
      const a = loop[i];
      const b = loop[(i + 1) % loop.length];
      faces.push([a, b, b + n, a + n]);
    }
  return { vertices, faces };
}

function rawSolid(id: SolidId): { vertices: V3[]; faces?: number[][]; genus: number } {
  switch (id) {
    case "tetrahedron":
      return { vertices: [[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], genus: 0 };
    case "cube": {
      const v: V3[] = [];
      for (const x of [-1, 1]) for (const y of [-1, 1]) for (const z of [-1, 1]) v.push([x, y, z]);
      return { vertices: v, genus: 0 };
    }
    case "octahedron":
      return { vertices: [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]], genus: 0 };
    case "icosahedron": {
      const v: V3[] = [];
      for (const a of [-1, 1]) for (const b of [-1, 1]) v.push([0, a, b * PHI], [a, b * PHI, 0], [b * PHI, 0, a]);
      return { vertices: v, genus: 0 };
    }
    case "dodecahedron": {
      const v: V3[] = [];
      for (const x of [-1, 1]) for (const y of [-1, 1]) for (const z of [-1, 1]) v.push([x, y, z]);
      for (const a of [-1, 1]) for (const b of [-1, 1]) v.push([0, a / PHI, b * PHI], [a / PHI, b * PHI, 0], [b * PHI, 0, a / PHI]);
      return { vertices: v, genus: 0 };
    }
    case "prism": {
      const v: V3[] = [];
      for (const y of [-0.85, 0.85]) for (let k = 0; k < 3; k++) {
        const a = Math.PI / 2 + (k * 2 * Math.PI) / 3;
        v.push([Math.cos(a), y, Math.sin(a)]);
      }
      return { vertices: v, genus: 0 };
    }
    case "pyramid":
      return { vertices: [[-1, -0.6, -1], [1, -0.6, -1], [1, -0.6, 1], [-1, -0.6, 1], [0, 1.0, 0]], genus: 0 };
    case "torus": {
      const pts2: [number, number][] = [[-2, -2], [2, -2], [2, 2], [-2, 2], [-1, -1], [1, -1], [1, 1], [-1, 1]];
      const top = [0, 1, 2, 3].map((k) => [k, (k + 1) % 4, 4 + ((k + 1) % 4), 4 + k]);
      return { ...extrudeFrame(pts2, top, [[0, 1, 2, 3], [4, 5, 6, 7]], 0.5), genus: 1 };
    }
    case "doubleTorus": {
      // outer boundary 0–7, hole 1: 8–11, hole 2: 12–15 (x, z coordinates)
      const pts2: [number, number][] = [
        [-3.5, -2], [-0.5, -2], [0.5, -2], [3.5, -2], [3.5, 2], [0.5, 2], [-0.5, 2], [-3.5, 2],
        [-2.5, -1], [-0.5, -1], [-0.5, 1], [-2.5, 1],
        [0.5, -1], [2.5, -1], [2.5, 1], [0.5, 1],
      ];
      const top = [
        [0, 1, 9, 8], [0, 8, 11, 7], [11, 10, 6, 7],
        [1, 2, 12, 15, 5, 6, 10, 9],
        [2, 3, 13, 12], [3, 4, 14, 13], [15, 14, 4, 5],
      ];
      return { ...extrudeFrame(pts2, top, [[0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]], 0.5), genus: 2 };
    }
  }
}

const cache = new Map<SolidId, Solid>();

/** A solid, scaled so its farthest vertex is at distance 1 from the centre. */
export function getSolid(id: SolidId): Solid {
  const hit = cache.get(id);
  if (hit) return hit;
  const raw = rawSolid(id);
  const centre = scale3(raw.vertices.reduce<V3>((a, v) => add3(a, v), [0, 0, 0]), 1 / raw.vertices.length);
  const shifted = raw.vertices.map((v) => sub3(v, centre));
  const r = Math.max(...shifted.map(len3));
  const vertices = shifted.map((v) => scale3(v, 1 / r));
  const faces = orientFaces(vertices, raw.faces ?? convexHullFaces(vertices));
  const { edges, edgeFaces } = edgesOf(faces);
  const normals = faces.map((f) => norm3(newellNormal(vertices, f)));
  const solid: Solid = { id, vertices, faces, edges, edgeFaces, normals, genus: raw.genus };
  cache.set(id, solid);
  return solid;
}

export const isSolidId = (v: unknown): v is SolidId => typeof v === "string" && (SOLID_IDS as readonly string[]).includes(v);

export function counts(s: Solid) {
  const V = s.vertices.length;
  const E = s.edges.length;
  const F = s.faces.length;
  return { V, E, F, chi: V - E + F };
}

/** View of a solid under rotation `m`: projected points, which faces face the viewer, hidden edges. */
export function viewSolid(s: Solid, m: M3) {
  const pts = s.vertices.map((v) => apply3(m, v));
  const front = s.normals.map((n) => apply3(m, n)[2] > 1e-9);
  const depth = s.faces.map((f) => f.reduce((acc, i) => acc + pts[i][2], 0) / f.length);
  const order = s.faces.map((_, i) => i).filter((i) => front[i]).sort((a, b) => depth[a] - depth[b]);
  const hiddenEdge = s.edgeFaces.map(([a, b]) => !front[a] && !front[b]);
  const vertexFront = new Array(s.vertices.length).fill(false);
  s.faces.forEach((f, fi) => {
    if (front[fi]) f.forEach((i) => (vertexFront[i] = true));
  });
  const light = norm3([-0.35, 0.55, 0.75]);
  const shade = s.normals.map((n) => Math.max(0, dot3(apply3(m, n), light)));
  return { pts, front, order, hiddenEdge, vertexFront, shade };
}
