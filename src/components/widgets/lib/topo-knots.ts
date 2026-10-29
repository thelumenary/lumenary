/**
 * Knot and link diagrams from 3D parametric curves.
 * The curve is projected to the plane; crossings are found numerically and the
 * height (z) decides which strand passes over. Arcs are the pieces of the
 * diagram between consecutive under-passes — the things a tricolouring colours.
 */
import { cross2, len2, sub2, type V2 } from "./topo-vec";

export const KNOT_IDS = ["unknot", "trefoil", "figureEight", "hopf", "cinquefoil"] as const;
export type KnotId = (typeof KNOT_IDS)[number];
export const isKnotId = (v: unknown): v is KnotId => typeof v === "string" && (KNOT_IDS as readonly string[]).includes(v);

type P3 = [number, number, number];

export interface KnotInfo {
  id: KnotId;
  /** Standard name (Rolfsen table) or link name. */
  notation: string;
  /** Minimal number of crossings over all diagrams of this knot or link. */
  crossingNumber: number;
  components: number;
}

export const KNOT_INFO: Record<KnotId, KnotInfo> = {
  unknot: { id: "unknot", notation: "0₁", crossingNumber: 0, components: 1 },
  trefoil: { id: "trefoil", notation: "3₁", crossingNumber: 3, components: 1 },
  figureEight: { id: "figureEight", notation: "4₁", crossingNumber: 4, components: 1 },
  hopf: { id: "hopf", notation: "L2a1", crossingNumber: 2, components: 2 },
  cinquefoil: { id: "cinquefoil", notation: "5₁", crossingNumber: 5, components: 1 },
};

const SAMPLES = 720;

/** Parametric space curves (one per component), t ∈ [0, 2π). */
function curves(id: KnotId): ((t: number) => P3)[] {
  switch (id) {
    case "unknot": {
      // a limaçon: one loop with a kink (one crossing, removable by a Reidemeister I move)
      const b = 0.42;
      return [(t) => [(b + Math.cos(t)) * Math.cos(t), (b + Math.cos(t)) * Math.sin(t), Math.sin(t)]];
    }
    case "trefoil":
      // the (2,3) torus knot
      return [(t) => {
        const r = 2 + Math.cos(3 * t);
        return [r * Math.cos(2 * t), r * Math.sin(2 * t), Math.sin(3 * t)];
      }];
    case "cinquefoil":
      // the (2,5) torus knot
      return [(t) => {
        const r = 2 + 0.85 * Math.cos(5 * t);
        return [r * Math.cos(2 * t), r * Math.sin(2 * t), Math.sin(5 * t)];
      }];
    case "figureEight":
      return [(t) => {
        const r = 2 + Math.cos(2 * t);
        return [r * Math.cos(3 * t), r * Math.sin(3 * t), Math.sin(4 * t)];
      }];
    case "hopf":
      return [
        (t) => [-0.6 + Math.cos(t), Math.sin(t), Math.sin(t)],
        (t) => [0.6 + Math.cos(t), Math.sin(t), -Math.sin(t)],
      ];
  }
}

/** Rotation applied to the projection so each diagram sits upright. */
const TURN: Record<KnotId, number> = { unknot: Math.PI / 2, trefoil: Math.PI / 2, cinquefoil: Math.PI / 2, figureEight: Math.PI / 2, hopf: 0 };

export interface Crossing {
  /** Position in diagram coordinates. */
  p: V2;
  over: number;
  /** Arc arriving at the under-pass and arc leaving it (they may be the same arc). */
  underIn: number;
  underOut: number;
  /** +1 or −1 by the right-hand rule, using each component's direction of travel. */
  sign: 1 | -1;
  components: [number, number];
}
export interface Arc {
  component: number;
  /** Polyline in diagram coordinates, trimmed back from the under-passes to leave a gap. */
  points: V2[];
  /** Where to put the arc's label. */
  label: V2;
}
export interface Diagram {
  id: KnotId;
  arcs: Arc[];
  crossings: Crossing[];
  /** Full (untrimmed) projected components, closed polylines. */
  components: V2[][];
  /** Over and under passes alternate along every component. */
  alternating: boolean;
  size: number;
}

interface RawCrossing {
  p: V2;
  a: { comp: number; s: number; z: number; dir: V2 };
  b: { comp: number; s: number; z: number; dir: V2 };
}

function segIntersect(p1: V2, p2: V2, q1: V2, q2: V2): [number, number] | null {
  const r = sub2(p2, p1);
  const s = sub2(q2, q1);
  const den = cross2(r, s);
  if (Math.abs(den) < 1e-14) return null;
  const qp = sub2(q1, p1);
  const t = cross2(qp, s) / den;
  const u = cross2(qp, r) / den;
  if (t < 0 || t >= 1 || u < 0 || u >= 1) return null;
  return [t, u];
}

/** Build a diagram fitting a square of side `size` (with margins). */
export function buildDiagram(id: KnotId, size = 400): Diagram {
  const fns = curves(id);
  const turn = TURN[id];
  const c = Math.cos(turn);
  const s = Math.sin(turn);
  const raw3: P3[][] = fns.map((f) => Array.from({ length: SAMPLES }, (_, i) => {
    // a fractional offset keeps crossings away from sample points (no double counting)
    const [x, y, z] = f(((i + 0.3183) / SAMPLES) * 2 * Math.PI);
    return [c * x - s * y, s * x + c * y, z] as P3;
  }));
  // fit into [m, size − m]² with y pointing down for SVG
  const all = raw3.flat();
  const minX = Math.min(...all.map((p) => p[0]));
  const maxX = Math.max(...all.map((p) => p[0]));
  const minY = Math.min(...all.map((p) => p[1]));
  const maxY = Math.max(...all.map((p) => p[1]));
  const m = size * 0.09;
  const k = (size - 2 * m) / Math.max(maxX - minX, maxY - minY);
  const ox = (size - k * (maxX - minX)) / 2;
  const oy = (size - k * (maxY - minY)) / 2;
  const comps: V2[][] = raw3.map((cmp) => cmp.map((p) => [ox + (p[0] - minX) * k, oy + (maxY - p[1]) * k] as V2));
  const heights: number[][] = raw3.map((cmp) => cmp.map((p) => p[2]));

  // crossings
  const raws: RawCrossing[] = [];
  for (let ca = 0; ca < comps.length; ca++)
    for (let cb = ca; cb < comps.length; cb++) {
      const A = comps[ca];
      const B = comps[cb];
      const n = A.length;
      const nb = B.length;
      for (let i = 0; i < n; i++)
        for (let j = ca === cb ? i + 2 : 0; j < nb; j++) {
          if (ca === cb && i === 0 && j === n - 1) continue;
          const hit = segIntersect(A[i], A[(i + 1) % n], B[j], B[(j + 1) % nb]);
          if (!hit) continue;
          const [t, u] = hit;
          const px = A[i][0] + (A[(i + 1) % n][0] - A[i][0]) * t;
          const py = A[i][1] + (A[(i + 1) % n][1] - A[i][1]) * t;
          if (raws.some((r) => Math.hypot(r.p[0] - px, r.p[1] - py) < 1e-6 * size)) continue;
          const za = heights[ca][i] * (1 - t) + heights[ca][(i + 1) % n] * t;
          const zb = heights[cb][j] * (1 - u) + heights[cb][(j + 1) % nb] * u;
          raws.push({
            p: [px, py],
            a: { comp: ca, s: i + t, z: za, dir: sub2(A[(i + 1) % n], A[i]) },
            b: { comp: cb, s: j + u, z: zb, dir: sub2(B[(j + 1) % nb], B[j]) },
          });
        }
    }

  // arcs: cut every component at its under-passes
  type Under = { comp: number; s: number; crossing: number };
  const unders: Under[] = raws.map((r, ci) => (r.a.z < r.b.z ? { comp: r.a.comp, s: r.a.s, crossing: ci } : { comp: r.b.comp, s: r.b.s, crossing: ci }));
  const arcs: Arc[] = [];
  /** arcStarts[comp] = sorted list of {s, arc} where each arc starts */
  const arcStarts: { s: number; arc: number }[][] = comps.map(() => []);
  const gap = size * 0.028;
  comps.forEach((cmp, ci) => {
    const cuts = unders.filter((u) => u.comp === ci).sort((x, y) => x.s - y.s);
    const n = cmp.length;
    const at = (sv: number): V2 => {
      const i = Math.floor(sv) % n;
      const f = sv - Math.floor(sv);
      const p = cmp[i];
      const q = cmp[(i + 1) % n];
      return [p[0] + (q[0] - p[0]) * f, p[1] + (q[1] - p[1]) * f];
    };
    const piece = (s0: number, s1: number): V2[] => {
      // s1 > s0 (may exceed n to wrap around)
      const pts: V2[] = [at(s0)];
      for (let i = Math.floor(s0) + 1; i < s1; i++) pts.push(cmp[i % n]);
      pts.push(at(s1));
      return pts.map((p) => [p[0], p[1]] as V2);
    };
    if (cuts.length === 0) {
      const pts = [...cmp, cmp[0]];
      arcStarts[ci].push({ s: 0, arc: arcs.length });
      arcs.push({ component: ci, points: pts, label: cmp[Math.floor(n / 4)] });
      return;
    }
    cuts.forEach((cut, k) => {
      const next = cuts[(k + 1) % cuts.length];
      const s1 = next.s > cut.s ? next.s : next.s + n;
      const pts = trim(piece(cut.s, s1), gap);
      arcStarts[ci].push({ s: cut.s, arc: arcs.length });
      arcs.push({ component: ci, points: pts, label: pointAtFraction(pts, 0.5) });
    });
  });

  const arcAt = (comp: number, sv: number): number => {
    const starts = arcStarts[comp];
    if (starts.length === 1) return starts[0].arc;
    let best = starts[starts.length - 1].arc; // wraps around from the last cut
    for (const st of starts) if (st.s <= sv) best = st.arc;
    return best;
  };
  const arcBefore = (comp: number, sv: number): number => {
    const starts = arcStarts[comp];
    const idx = starts.findIndex((st) => Math.abs(st.s - sv) < 1e-9);
    return starts[(idx - 1 + starts.length) % starts.length].arc;
  };

  const crossings: Crossing[] = raws.map((r) => {
    const overSide = r.a.z > r.b.z ? r.a : r.b;
    const underSide = r.a.z > r.b.z ? r.b : r.a;
    // sign with y pointing up (undo the SVG flip): sign of over × under
    const o: V2 = [overSide.dir[0], -overSide.dir[1]];
    const u: V2 = [underSide.dir[0], -underSide.dir[1]];
    return {
      p: r.p,
      over: arcAt(overSide.comp, overSide.s),
      underIn: arcBefore(underSide.comp, underSide.s),
      underOut: arcAt(underSide.comp, underSide.s),
      sign: cross2(o, u) > 0 ? 1 : -1,
      components: [r.a.comp, r.b.comp],
    };
  });

  // alternating: walking along each component, passes go over, under, over, …
  const alternating = comps.every((_, ci) => {
    const seq = raws
      .flatMap((r) => [
        { comp: r.a.comp, s: r.a.s, over: r.a.z > r.b.z },
        { comp: r.b.comp, s: r.b.s, over: r.b.z > r.a.z },
      ])
      .filter((x) => x.comp === ci)
      .sort((x, y) => x.s - y.s);
    return seq.every((x, i) => seq.length < 2 || x.over !== seq[(i + 1) % seq.length].over);
  });

  return { id, arcs, crossings, components: comps, alternating, size };
}

function trim(pts: V2[], d: number): V2[] {
  const cut = (arr: V2[]): V2[] => {
    let rem = d;
    let i = 0;
    while (i < arr.length - 1) {
      const seg = len2(sub2(arr[i + 1], arr[i]));
      if (seg > rem) {
        const f = rem / seg;
        const start: V2 = [arr[i][0] + (arr[i + 1][0] - arr[i][0]) * f, arr[i][1] + (arr[i + 1][1] - arr[i][1]) * f];
        return [start, ...arr.slice(i + 1)];
      }
      rem -= seg;
      i++;
    }
    return arr.slice(-1);
  };
  const front = cut(pts);
  return cut(front.reverse()).reverse();
}

function pointAtFraction(pts: V2[], f: number): V2 {
  const lens = pts.slice(1).map((p, i) => len2(sub2(p, pts[i])));
  const total = lens.reduce((a, b) => a + b, 0);
  let target = total * f;
  for (let i = 0; i < lens.length; i++) {
    if (target <= lens[i]) {
      const t = lens[i] > 0 ? target / lens[i] : 0;
      return [pts[i][0] + (pts[i + 1][0] - pts[i][0]) * t, pts[i][1] + (pts[i + 1][1] - pts[i][1]) * t];
    }
    target -= lens[i];
  }
  return pts[pts.length - 1];
}

const cache = new Map<KnotId, Diagram>();
export function getDiagram(id: KnotId): Diagram {
  const hit = cache.get(id);
  if (hit) return hit;
  const d = buildDiagram(id);
  cache.set(id, d);
  return d;
}

/** 0 = not coloured yet, 1–3 = the three colours. */
export type Colour = 0 | 1 | 2 | 3;
export type CrossingState = "pending" | "ok" | "bad";

/** The tricolouring rule at one crossing: the three arcs are all the same colour or all different. */
export function crossingState(c: Crossing, colours: readonly Colour[]): CrossingState {
  const x = colours[c.over] ?? 0;
  const y = colours[c.underIn] ?? 0;
  const z = colours[c.underOut] ?? 0;
  if (!x || !y || !z) return "pending";
  const allSame = x === y && y === z;
  const allDiff = x !== y && y !== z && x !== z;
  return allSame || allDiff ? "ok" : "bad";
}

export function checkColouring(d: Diagram, colours: readonly Colour[]) {
  const states = d.crossings.map((c) => crossingState(c, colours));
  const complete = d.arcs.every((_, i) => (colours[i] ?? 0) > 0);
  const used = new Set(colours.filter((c) => c > 0)).size;
  const valid = complete && states.every((s) => s === "ok");
  return { states, complete, used, valid, nontrivial: valid && used >= 2, bad: states.filter((s) => s === "bad").length };
}

/** All valid colourings of the diagram (brute force over 3^arcs; arcs ≤ 8 here). */
export function allColourings(d: Diagram): Colour[][] {
  const n = d.arcs.length;
  const out: Colour[][] = [];
  const total = 3 ** n;
  for (let code = 0; code < total; code++) {
    const cols: Colour[] = [];
    let x = code;
    for (let i = 0; i < n; i++) {
      cols.push(((x % 3) + 1) as Colour);
      x = Math.floor(x / 3);
    }
    if (d.crossings.every((c) => crossingState(c, cols) === "ok")) out.push(cols);
  }
  return out;
}

/** Linking number: half the sum of the signs of crossings between different components. */
export function linkingNumber(d: Diagram): number {
  const s = d.crossings.filter((c) => c.components[0] !== c.components[1]).reduce((acc, c) => acc + c.sign, 0);
  return s / 2;
}
