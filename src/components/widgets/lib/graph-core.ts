/**
 * Pure graph logic for the GraphExplorer widget: presets, parsing author input,
 * layout, degrees, walks/Euler trails, colourings, spanning trees and adjacency
 * matrices. Graphs are undirected multigraphs without loops.
 */

export type Pt = { x: number; y: number };
export type Edge = [number, number];

export interface Graph {
  labels: string[];
  edges: Edge[];
  /** Positions in drawing coordinates (see DRAW_W / DRAW_H). */
  pos: Pt[];
  /** Known planarity (presets only); undefined when not known. */
  planar?: boolean;
}

export const PRESET_IDS = ["konigsberg", "k4", "k5", "k33", "petersen", "cube", "cycle6", "tree", "wheel"] as const;
export type PresetId = (typeof PRESET_IDS)[number];
export const isPresetId = (v: unknown): v is PresetId => typeof v === "string" && (PRESET_IDS as readonly string[]).includes(v);

export const MAX_NODES = 30;
export const MAX_EDGES = 90;
export const DRAW_W = 360;
export const DRAW_H = 300;
const PAD = 38;

const letters = (n: number) => Array.from({ length: n }, (_, i) => String.fromCharCode(65 + i));

/** n points on a circle, starting at the top and going clockwise (raw coordinates). */
export function circlePoints(n: number, phase = 0): Pt[] {
  return Array.from({ length: n }, (_, i) => {
    const a = -Math.PI / 2 + phase + (2 * Math.PI * i) / Math.max(1, n);
    return { x: Math.cos(a), y: Math.sin(a) };
  });
}

/** Scale raw positions (any units, y downwards) to fit the drawing box, preserving shape. */
export function fitPositions(raw: Pt[], w = DRAW_W, h = DRAW_H, pad = PAD): Pt[] {
  if (raw.length === 0) return [];
  const xs = raw.map((p) => p.x);
  const ys = raw.map((p) => p.y);
  const minX = Math.min(...xs);
  const maxX = Math.max(...xs);
  const minY = Math.min(...ys);
  const maxY = Math.max(...ys);
  const bw = maxX - minX;
  const bh = maxY - minY;
  const sx = bw > 1e-9 ? (w - 2 * pad) / bw : Infinity;
  const sy = bh > 1e-9 ? (h - 2 * pad) / bh : Infinity;
  let s = Math.min(sx, sy);
  if (!Number.isFinite(s)) s = 1;
  const cx = (minX + maxX) / 2;
  const cy = (minY + maxY) / 2;
  return raw.map((p) => ({ x: w / 2 + (p.x - cx) * s, y: h / 2 + (p.y - cy) * s }));
}

function preset(id: PresetId): { labels: string[]; edges: Edge[]; raw: Pt[]; planar: boolean } {
  switch (id) {
    case "konigsberg":
      // A north bank, B south bank, C the island Kneiphof, D the eastern land; seven bridges.
      return {
        labels: ["A", "B", "C", "D"],
        edges: [[0, 2], [0, 2], [1, 2], [1, 2], [0, 3], [1, 3], [2, 3]],
        raw: [{ x: 0.5, y: 0 }, { x: 0.5, y: 1 }, { x: 0, y: 0.5 }, { x: 1.05, y: 0.5 }],
        planar: true,
      };
    case "k4":
      return { labels: letters(4), edges: complete(4), raw: [{ x: 0.5, y: 0 }, { x: 0, y: 0.866 }, { x: 1, y: 0.866 }, { x: 0.5, y: 0.577 }], planar: true };
    case "k5":
      return { labels: letters(5), edges: complete(5), raw: circlePoints(5), planar: false };
    case "k33": {
      const edges: Edge[] = [];
      for (let i = 0; i < 3; i++) for (let j = 3; j < 6; j++) edges.push([i, j]);
      return { labels: ["A", "B", "C", "X", "Y", "Z"], edges, raw: [0, 1, 2, 0, 1, 2].map((x, i) => ({ x, y: i < 3 ? 0 : 1.1 })), planar: false };
    }
    case "petersen": {
      const edges: Edge[] = [];
      for (let i = 0; i < 5; i++) edges.push([i, (i + 1) % 5], [i, i + 5], [5 + i, 5 + ((i + 2) % 5)]);
      const outer = circlePoints(5);
      const inner = circlePoints(5).map((p) => ({ x: p.x * 0.48, y: p.y * 0.48 }));
      return { labels: letters(10), edges, raw: [...outer, ...inner], planar: false };
    }
    case "cube": {
      const labels = Array.from({ length: 8 }, (_, i) => i.toString(2).padStart(3, "0"));
      const edges: Edge[] = [];
      for (let i = 0; i < 8; i++) for (let b = 0; b < 3; b++) if (i < (i ^ (1 << b))) edges.push([i, i ^ (1 << b)]);
      // Nested squares: the first two bits pick the corner, the last bit picks outer (0) or inner (1).
      const corner = (i: number) => {
        const hi = i >> 1; // first two bits
        const [x, y] = [[-1, -1], [-1, 1], [1, -1], [1, 1]][hi];
        const s = i & 1 ? 0.45 : 1;
        return { x: x * s, y: y * s };
      };
      return { labels, edges, raw: labels.map((_, i) => corner(i)), planar: true };
    }
    case "cycle6":
      return { labels: letters(6), edges: Array.from({ length: 6 }, (_, i) => [i, (i + 1) % 6] as Edge), raw: circlePoints(6), planar: true };
    case "tree":
      return {
        labels: letters(7),
        edges: [[0, 1], [0, 2], [1, 3], [1, 4], [2, 5], [2, 6]],
        raw: [{ x: 0.5, y: 0 }, { x: 0.25, y: 0.5 }, { x: 0.75, y: 0.5 }, { x: 0.125, y: 1 }, { x: 0.375, y: 1 }, { x: 0.625, y: 1 }, { x: 0.875, y: 1 }],
        planar: true,
      };
    case "wheel": {
      const edges: Edge[] = [];
      for (let i = 0; i < 5; i++) edges.push([i, (i + 1) % 5], [i, 5]);
      return { labels: [...letters(5), "H"], edges, raw: [...circlePoints(5), { x: 0, y: 0 }], planar: true };
    }
  }
}

function complete(n: number): Edge[] {
  const out: Edge[] = [];
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) out.push([i, j]);
  return out;
}

export function presetGraph(id: PresetId): Graph {
  const p = preset(id);
  return { labels: p.labels, edges: p.edges, pos: fitPositions(p.raw), planar: p.planar };
}

function toPoint(v: unknown): Pt | null {
  if (Array.isArray(v) && v.length >= 2 && Number.isFinite(Number(v[0])) && Number.isFinite(Number(v[1])) && v[0] !== null && v[1] !== null) return { x: Number(v[0]), y: Number(v[1]) };
  if (v && typeof v === "object" && "x" in v && "y" in v) {
    const o = v as { x: unknown; y: unknown };
    if (typeof o.x === "number" && typeof o.y === "number" && Number.isFinite(o.x) && Number.isFinite(o.y)) return { x: o.x, y: o.y };
  }
  return null;
}

/**
 * Build a graph from MDX props. Custom `nodes`/`edges` win over `preset`.
 * Endpoints may be labels (strings) or 0-based indices (numbers). Loops,
 * unknown endpoints and malformed entries are skipped and counted in `ignored`.
 */
export function buildGraph(opts: { preset?: unknown; nodes?: unknown; edges?: unknown; positions?: unknown }): { graph: Graph; ignored: number; custom: boolean } {
  const hasNodes = Array.isArray(opts.nodes) && opts.nodes.length > 0;
  const hasEdges = Array.isArray(opts.edges);
  if (!hasNodes && !hasEdges) return { graph: presetGraph(isPresetId(opts.preset) ? opts.preset : "konigsberg"), ignored: 0, custom: false };

  let ignored = 0;
  const labels: string[] = [];
  const rawEdges = hasEdges ? (opts.edges as unknown[]) : [];
  if (hasNodes) {
    for (const v of (opts.nodes as unknown[]).slice(0, MAX_NODES)) {
      const s = typeof v === "string" || typeof v === "number" ? String(v).trim() : "";
      labels.push(s || String(labels.length));
    }
    if ((opts.nodes as unknown[]).length > MAX_NODES) ignored += (opts.nodes as unknown[]).length - MAX_NODES;
  } else {
    // No labels given: collect endpoints in order of appearance (numbers sorted numerically).
    const seen = new Set<string>();
    const nums: number[] = [];
    let allNumbers = true;
    for (const e of rawEdges) {
      if (!Array.isArray(e) || e.length < 2) continue;
      for (const v of e.slice(0, 2)) {
        if (typeof v === "number" && Number.isInteger(v) && v >= 0) nums.push(v);
        else allNumbers = false;
        if ((typeof v === "string" && v.trim()) || typeof v === "number") seen.add(String(v).trim());
      }
    }
    if (allNumbers && nums.length) {
      const n = Math.min(MAX_NODES, Math.max(...nums) + 1);
      for (let i = 0; i < n; i++) labels.push(String(i));
    } else for (const s of seen) if (labels.length < MAX_NODES) labels.push(s);
  }

  const resolve = (v: unknown): number | null => {
    if (typeof v === "string") {
      const s = v.trim();
      const i = labels.indexOf(s);
      if (i >= 0) return i;
      if (/^\d+$/.test(s) && Number(s) < labels.length && hasNodes) return Number(s);
      return null;
    }
    if (typeof v === "number" && Number.isInteger(v)) {
      if (!hasNodes) {
        const i = labels.indexOf(String(v));
        return i >= 0 ? i : null;
      }
      if (v >= 0 && v < labels.length) return v;
      const i = labels.indexOf(String(v));
      return i >= 0 ? i : null;
    }
    return null;
  };

  const edges: Edge[] = [];
  for (const e of rawEdges) {
    if (!Array.isArray(e) || e.length < 2) {
      ignored++;
      continue;
    }
    const a = resolve(e[0]);
    const b = resolve(e[1]);
    if (a === null || b === null || a === b || edges.length >= MAX_EDGES) {
      ignored++;
      continue;
    }
    edges.push([a, b]);
  }

  let raw: Pt[] | null = null;
  if (Array.isArray(opts.positions) && opts.positions.length >= labels.length && labels.length > 0) {
    const pts = (opts.positions as unknown[]).slice(0, labels.length).map(toPoint);
    if (pts.every((p): p is Pt => p !== null)) raw = pts;
  }
  if (!raw) raw = circlePoints(labels.length);
  return { graph: { labels, edges, pos: fitPositions(raw) }, ignored, custom: true };
}

/* ------------------------------------------------------------------------ */
/* Drawing geometry                                                          */
/* ------------------------------------------------------------------------ */

export interface EdgeShape {
  d: string;
  /** Point on the curve halfway along. */
  mid: Pt;
}

/** Straight lines for single edges; parallel edges fan out as gentle quadratic curves. */
export function edgeShapes(g: Graph, spread = 26): EdgeShape[] {
  const groups = new Map<string, number[]>();
  g.edges.forEach(([a, b], i) => {
    const key = a < b ? `${a}-${b}` : `${b}-${a}`;
    groups.set(key, [...(groups.get(key) ?? []), i]);
  });
  const out: EdgeShape[] = new Array(g.edges.length);
  for (const idxs of groups.values()) {
    idxs.forEach((ei, k) => {
      const [a, b] = g.edges[ei];
      const lo = Math.min(a, b);
      const hi = Math.max(a, b);
      const P = g.pos[lo];
      const Q = g.pos[hi];
      const dx = Q.x - P.x;
      const dy = Q.y - P.y;
      const len = Math.hypot(dx, dy) || 1;
      const nx = -dy / len;
      const ny = dx / len;
      const off = (k - (idxs.length - 1) / 2) * spread;
      const mx = (P.x + Q.x) / 2;
      const my = (P.y + Q.y) / 2;
      if (Math.abs(off) < 1e-9) out[ei] = { d: `M${r(P.x)} ${r(P.y)}L${r(Q.x)} ${r(Q.y)}`, mid: { x: mx, y: my } };
      else {
        // Control point at twice the offset so the curve's apex sits at `off`.
        const cx = mx + nx * off * 2;
        const cy = my + ny * off * 2;
        out[ei] = { d: `M${r(P.x)} ${r(P.y)}Q${r(cx)} ${r(cy)} ${r(Q.x)} ${r(Q.y)}`, mid: { x: mx + nx * off, y: my + ny * off } };
      }
    });
  }
  return out;
}

const r = (v: number) => Math.round(v * 10) / 10;

/* ------------------------------------------------------------------------ */
/* Degrees, connectivity, Euler                                              */
/* ------------------------------------------------------------------------ */

export function degrees(g: Graph): number[] {
  const d = new Array(g.labels.length).fill(0);
  for (const [a, b] of g.edges) {
    d[a]++;
    d[b]++;
  }
  return d;
}

class DSU {
  p: number[];
  constructor(n: number) {
    this.p = Array.from({ length: n }, (_, i) => i);
  }
  find(x: number): number {
    while (this.p[x] !== x) {
      this.p[x] = this.p[this.p[x]];
      x = this.p[x];
    }
    return x;
  }
  union(a: number, b: number): boolean {
    const ra = this.find(a);
    const rb = this.find(b);
    if (ra === rb) return false;
    this.p[ra] = rb;
    return true;
  }
}

/** Number of connected pieces among `vertices` using the given edges. */
function pieces(n: number, edges: Edge[], vertices: number[]): number {
  const dsu = new DSU(n);
  for (const [a, b] of edges) dsu.union(a, b);
  return new Set(vertices.map((v) => dsu.find(v))).size;
}

export function isConnected(g: Graph): boolean {
  return g.labels.length <= 1 || pieces(g.labels.length, g.edges, g.labels.map((_, i) => i)) === 1;
}

export interface EulerInfo {
  odd: number[];
  /** All edges lie in one connected piece. */
  edgesConnected: boolean;
  circuit: boolean;
  trail: boolean;
}

export function eulerInfo(g: Graph): EulerInfo {
  const deg = degrees(g);
  const odd = deg.map((d, i) => (d % 2 ? i : -1)).filter((i) => i >= 0);
  const touched = deg.map((d, i) => (d > 0 ? i : -1)).filter((i) => i >= 0);
  const edgesConnected = touched.length === 0 || pieces(g.labels.length, g.edges, touched) === 1;
  return { odd, edgesConnected, circuit: edgesConnected && g.edges.length > 0 && odd.length === 0, trail: edgesConnected && g.edges.length > 0 && (odd.length === 0 || odd.length === 2) };
}

/* ------------------------------------------------------------------------ */
/* Walks                                                                     */
/* ------------------------------------------------------------------------ */

export interface Walk {
  start: number | null;
  edges: number[];
  /** True while the first edge's direction may still be flipped (start not chosen explicitly). */
  flexible: boolean;
}

export const emptyWalk: Walk = { start: null, edges: [], flexible: false };

/** The vertex sequence of a walk (length edges + 1), or [start] / [] when empty. */
export function walkVertices(g: Graph, w: Walk): number[] {
  if (w.start === null) return [];
  const vs = [w.start];
  for (const ei of w.edges) {
    const cur = vs[vs.length - 1];
    const [a, b] = g.edges[ei];
    vs.push(cur === a ? b : a);
  }
  return vs;
}

export type ExtendResult = { ok: true; walk: Walk } | { ok: false; at: number };

/** Append an edge to the walk; it must touch the current end (or either end of a lone first edge). */
export function extendWalk(g: Graph, w: Walk, ei: number): ExtendResult {
  const e = g.edges[ei];
  if (!e) return { ok: false, at: w.start ?? 0 };
  const [a, b] = e;
  if (w.start === null) return { ok: true, walk: { start: a, edges: [ei], flexible: true } };
  const vs = walkVertices(g, w);
  const end = vs[vs.length - 1];
  if (a === end || b === end) return { ok: true, walk: { start: w.start, edges: [...w.edges, ei], flexible: false } };
  if (w.flexible && w.edges.length === 1) {
    // Flip the first edge so the walk ends at its other endpoint.
    const other = vs[0];
    if (a === other || b === other) return { ok: true, walk: { start: vs[1], edges: [...w.edges, ei], flexible: false } };
  }
  return { ok: false, at: end };
}

export interface WalkInfo {
  vertices: number[];
  length: number;
  closed: boolean;
  /** No edge used twice. */
  trail: boolean;
  /** No vertex visited twice (a closed walk may repeat only its start). */
  path: boolean;
  circuit: boolean;
  usedEdges: number;
  eulerTrail: boolean;
  eulerCircuit: boolean;
}

export function analyseWalk(g: Graph, w: Walk): WalkInfo {
  const vs = walkVertices(g, w);
  const length = w.edges.length;
  const closed = length > 0 && vs[0] === vs[vs.length - 1];
  const trail = new Set(w.edges).size === length;
  const inner = closed ? vs.slice(0, -1) : vs;
  const path = new Set(inner).size === inner.length;
  const usedEdges = new Set(w.edges).size;
  const all = length > 0 && trail && usedEdges === g.edges.length;
  return { vertices: vs, length, closed, trail, path, circuit: closed && trail, usedEdges, eulerTrail: all, eulerCircuit: all && closed };
}

/* ------------------------------------------------------------------------ */
/* Colouring                                                                 */
/* ------------------------------------------------------------------------ */

export function neighbours(g: Graph): number[][] {
  const adj: number[][] = g.labels.map(() => []);
  for (const [a, b] of g.edges) {
    if (!adj[a].includes(b)) adj[a].push(b);
    if (!adj[b].includes(a)) adj[b].push(a);
  }
  return adj;
}

export interface ColourInfo {
  conflicts: number[];
  used: number;
  uncoloured: number;
  proper: boolean;
}

export function colourInfo(g: Graph, colours: (number | null)[]): ColourInfo {
  const conflicts = g.edges.map(([a, b], i) => (colours[a] != null && colours[a] === colours[b] ? i : -1)).filter((i) => i >= 0);
  const used = new Set(colours.filter((c): c is number => c != null)).size;
  const uncoloured = g.labels.filter((_, i) => colours[i] == null).length;
  return { conflicts, used, uncoloured, proper: conflicts.length === 0 && uncoloured === 0 };
}

/** Greedy colouring, largest degree first (Welsh–Powell order). Colours are 0, 1, 2, … */
export function greedyColouring(g: Graph): number[] {
  const adj = neighbours(g);
  const order = g.labels.map((_, i) => i).sort((x, y) => adj[y].length - adj[x].length || x - y);
  const col: number[] = new Array(g.labels.length).fill(-1);
  for (const v of order) {
    const taken = new Set(adj[v].map((u) => col[u]));
    let c = 0;
    while (taken.has(c)) c++;
    col[v] = c;
  }
  return col;
}

/** Exact chromatic number by backtracking (null when the graph is too big to search quickly). */
export function chromaticNumber(g: Graph, limit = 16): number | null {
  const n = g.labels.length;
  if (n === 0) return 0;
  if (n > limit) return null;
  const adj = neighbours(g);
  const order = g.labels.map((_, i) => i).sort((x, y) => adj[y].length - adj[x].length || x - y);
  const col = new Array(n).fill(-1);
  const tryK = (k: number, idx: number): boolean => {
    if (idx === n) return true;
    const v = order[idx];
    const maxUsed = Math.max(-1, ...order.slice(0, idx).map((u) => col[u]));
    for (let c = 0; c < Math.min(k, maxUsed + 2); c++) {
      if (adj[v].every((u) => col[u] !== c)) {
        col[v] = c;
        if (tryK(k, idx + 1)) return true;
        col[v] = -1;
      }
    }
    return false;
  };
  for (let k = 1; k <= n; k++) {
    col.fill(-1);
    if (tryK(k, 0)) return k;
  }
  return n;
}

/* ------------------------------------------------------------------------ */
/* Spanning trees                                                            */
/* ------------------------------------------------------------------------ */

export interface SpanningInfo {
  count: number;
  needed: number;
  /** Edge indices of a cycle among the chosen edges, or null. */
  cycle: number[] | null;
  /** Connected pieces of the whole vertex set using only the chosen edges. */
  pieces: number;
  isTree: boolean;
}

export function spanningInfo(g: Graph, chosen: number[]): SpanningInfo {
  const n = g.labels.length;
  const dsu = new DSU(n);
  const forest: number[] = [];
  let cycle: number[] | null = null;
  for (const ei of chosen) {
    const [a, b] = g.edges[ei];
    if (!dsu.union(a, b)) {
      if (!cycle) cycle = [...pathInForest(g, forest, a, b), ei];
    } else forest.push(ei);
  }
  const p = new Set(g.labels.map((_, i) => dsu.find(i))).size;
  return { count: chosen.length, needed: Math.max(0, n - 1), cycle, pieces: p, isTree: cycle === null && p === 1 };
}

/** Edge indices of the unique path from a to b in a forest (BFS). */
function pathInForest(g: Graph, forest: number[], a: number, b: number): number[] {
  const prev = new Map<number, { v: number; e: number }>();
  const queue = [a];
  const seen = new Set([a]);
  while (queue.length) {
    const v = queue.shift()!;
    if (v === b) break;
    for (const ei of forest) {
      const [x, y] = g.edges[ei];
      const u = x === v ? y : y === v ? x : -1;
      if (u >= 0 && !seen.has(u)) {
        seen.add(u);
        prev.set(u, { v, e: ei });
        queue.push(u);
      }
    }
  }
  const out: number[] = [];
  let cur = b;
  while (cur !== a && prev.has(cur)) {
    const step = prev.get(cur)!;
    out.push(step.e);
    cur = step.v;
  }
  return out.reverse();
}

/** A spanning forest found by breadth-first search (a spanning tree when the graph is connected). */
export function bfsTree(g: Graph): number[] {
  const n = g.labels.length;
  const seen = new Array(n).fill(false);
  const out: number[] = [];
  for (let s = 0; s < n; s++) {
    if (seen[s]) continue;
    seen[s] = true;
    const queue = [s];
    while (queue.length) {
      const v = queue.shift()!;
      g.edges.forEach(([x, y], ei) => {
        const u = x === v ? y : y === v ? x : -1;
        if (u >= 0 && !seen[u]) {
          seen[u] = true;
          out.push(ei);
          queue.push(u);
        }
      });
    }
  }
  return out;
}

/** Exact determinant of an integer matrix (Bareiss fraction-free elimination). */
export function bigDet(m: bigint[][]): bigint {
  const n = m.length;
  if (n === 0) return 1n;
  const a = m.map((row) => [...row]);
  let sign = 1n;
  let prev = 1n;
  for (let k = 0; k < n - 1; k++) {
    if (a[k][k] === 0n) {
      const swap = a.findIndex((row, i) => i > k && row[k] !== 0n);
      if (swap < 0) return 0n;
      [a[k], a[swap]] = [a[swap], a[k]];
      sign = -sign;
    }
    for (let i = k + 1; i < n; i++)
      for (let j = k + 1; j < n; j++) a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev;
    prev = a[k][k];
  }
  return sign * a[n - 1][n - 1];
}

/** Number of spanning trees (Kirchhoff's matrix-tree theorem), exact. */
export function spanningTreeCount(g: Graph): bigint {
  const n = g.labels.length;
  if (n <= 1) return 1n;
  const L: bigint[][] = Array.from({ length: n }, () => new Array(n).fill(0n));
  for (const [a, b] of g.edges) {
    L[a][a] += 1n;
    L[b][b] += 1n;
    L[a][b] -= 1n;
    L[b][a] -= 1n;
  }
  return bigDet(L.slice(1).map((row) => row.slice(1)));
}

/* ------------------------------------------------------------------------ */
/* Adjacency matrix                                                          */
/* ------------------------------------------------------------------------ */

export function adjacencyMatrix(g: Graph): number[][] {
  const n = g.labels.length;
  const A = Array.from({ length: n }, () => new Array(n).fill(0));
  for (const [a, b] of g.edges) {
    A[a][b]++;
    A[b][a]++;
  }
  return A;
}

export function matMul(A: number[][], B: number[][]): number[][] {
  const n = A.length;
  return Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => A[i].reduce((s, aik, k) => s + aik * B[k][j], 0)));
}

export function matPow(A: number[][], k: number): number[][] {
  let out: number[][] = A.map((row, i) => row.map((_, j) => (i === j ? 1 : 0)));
  for (let i = 0; i < k; i++) out = matMul(out, A);
  return out;
}

export function isSimple(g: Graph): boolean {
  const seen = new Set<string>();
  for (const [a, b] of g.edges) {
    const key = a < b ? `${a}-${b}` : `${b}-${a}`;
    if (seen.has(key)) return false;
    seen.add(key);
  }
  return true;
}

/** All walks of length k from i to j as vertex lists (simple graphs; stops after `max`). */
export function listWalks(g: Graph, i: number, j: number, k: number, max = 12): number[][] {
  const adj = neighbours(g);
  const out: number[][] = [];
  const path = [i];
  const go = (v: number, left: number) => {
    if (out.length >= max) return;
    if (left === 0) {
      if (v === j) out.push([...path]);
      return;
    }
    for (const u of adj[v]) {
      path.push(u);
      go(u, left - 1);
      path.pop();
    }
  };
  go(i, k);
  return out;
}
