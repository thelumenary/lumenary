/**
 * Deterministic layout for the knowledge-graph map: subjects are horizontal
 * lanes, levels are columns, and nodes inside a cell are ordered by the
 * average position of their prerequisites (one barycentric sweep) to reduce
 * edge crossings. Pure and framework-free so it can be unit-tested.
 */
import { LEVEL_IDS, SUBJECT_IDS, type LevelId, type SubjectId } from "./schema";

export interface LayoutInput {
  id: string;
  level: LevelId;
  subject: SubjectId;
  prerequisites: string[];
}

export interface LayoutNode {
  id: string;
  x: number;
  y: number;
}

export interface LayoutResult {
  nodes: Record<string, LayoutNode>;
  lanes: { subject: SubjectId; y: number; height: number }[];
  columns: { level: LevelId; x: number; width: number }[];
  width: number;
  height: number;
  nodeWidth: number;
  nodeHeight: number;
}

export const LAYOUT = {
  labelWidth: 150,
  colWidth: 212,
  nodeWidth: 184,
  nodeHeight: 34,
  rowGap: 10,
  lanePad: 16,
  headerHeight: 44,
};

export function layoutGraph(topics: LayoutInput[]): LayoutResult {
  const { labelWidth, colWidth, nodeWidth, nodeHeight, rowGap, lanePad, headerHeight } = LAYOUT;
  const cells = new Map<string, LayoutInput[]>();
  for (const t of topics) {
    const key = `${t.subject}|${t.level}`;
    if (!cells.has(key)) cells.set(key, []);
    cells.get(key)!.push(t);
  }

  const lanes: LayoutResult["lanes"] = [];
  let y = headerHeight;
  for (const subject of SUBJECT_IDS) {
    const maxInCell = Math.max(1, ...LEVEL_IDS.map((l) => cells.get(`${subject}|${l}`)?.length ?? 0));
    const height = lanePad * 2 + maxInCell * nodeHeight + (maxInCell - 1) * rowGap;
    lanes.push({ subject, y, height });
    y += height;
  }

  const columns = LEVEL_IDS.map((level, i) => ({ level, x: labelWidth + i * colWidth, width: colWidth }));
  const nodes: Record<string, LayoutNode> = {};

  // Sweep columns left to right so prerequisites (never at a higher level) are placed first.
  for (const [ci, level] of LEVEL_IDS.entries()) {
    for (const lane of lanes) {
      const list = [...(cells.get(`${lane.subject}|${level}`) ?? [])];
      const bary = (t: LayoutInput) => {
        const ys = t.prerequisites.map((p) => nodes[p]?.y).filter((v): v is number => v !== undefined);
        return ys.length ? ys.reduce((a, b) => a + b, 0) / ys.length : lane.y + lane.height / 2;
      };
      list.sort((a, b) => bary(a) - bary(b) || a.id.localeCompare(b.id));
      list.forEach((t, k) => {
        nodes[t.id] = {
          id: t.id,
          x: columns[ci].x + (colWidth - nodeWidth) / 2,
          y: lane.y + lanePad + k * (nodeHeight + rowGap),
        };
      });
    }
  }

  return { nodes, lanes, columns, width: labelWidth + LEVEL_IDS.length * colWidth + 16, height: y + 16, nodeWidth, nodeHeight };
}

/** Transitive closure of required prerequisites. */
export function ancestors(id: string, prereqs: Map<string, string[]>): Set<string> {
  const out = new Set<string>();
  const stack = [...(prereqs.get(id) ?? [])];
  while (stack.length) {
    const n = stack.pop()!;
    if (out.has(n)) continue;
    out.add(n);
    stack.push(...(prereqs.get(n) ?? []));
  }
  return out;
}

/** Returns a cycle (as a list of ids) if the required edges are not acyclic, else null. */
export function findCycle(topics: { id: string; prerequisites: string[] }[]): string[] | null {
  const prereqs = new Map(topics.map((t) => [t.id, t.prerequisites]));
  const state = new Map<string, 0 | 1 | 2>();
  const stack: string[] = [];
  const visit = (id: string): string[] | null => {
    const s = state.get(id) ?? 0;
    if (s === 2) return null;
    if (s === 1) return [...stack.slice(stack.indexOf(id)), id];
    state.set(id, 1);
    stack.push(id);
    for (const p of prereqs.get(id) ?? []) {
      const c = visit(p);
      if (c) return c;
    }
    stack.pop();
    state.set(id, 2);
    return null;
  };
  for (const t of topics) {
    const c = visit(t.id);
    if (c) return c;
  }
  return null;
}
