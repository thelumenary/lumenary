/** Ten-frame logic: counting facts and the "make ten" strategy for a + b. */

export interface MakeTenPlan {
  a: number;
  b: number;
  /** How many of b move up to complete the first ten (0 if a is already 10). */
  toTen: number;
  /** How many of b are left in the second frame. */
  rest: number;
  total: number;
}

export function makeTenPlan(a: number, b: number): MakeTenPlan {
  const toTen = Math.max(0, Math.min(10 - a, b));
  return { a, b, toTen, rest: b - toTen, total: a + b };
}

export interface Counter {
  id: string;
  tone: "a" | "b";
  frame: 0 | 1;
  /** Cell 0..9: row = floor(cell / 5), column = cell % 5. */
  cell: number;
}

/**
 * Where every counter sits. Before (`moved` false): a in the first frame, b in the second.
 * After: the last `toTen` counters of b have moved up into the first frame's empty cells.
 */
export function makeTenCounters(a: number, b: number, moved: boolean): Counter[] {
  const { toTen, rest } = makeTenPlan(a, b);
  const out: Counter[] = [];
  for (let i = 0; i < a; i++) out.push({ id: `a${i}`, tone: "a", frame: 0, cell: i });
  for (let i = 0; i < b; i++) {
    if (moved && i >= rest) out.push({ id: `b${i}`, tone: "b", frame: 0, cell: a + (i - rest) });
    else out.push({ id: `b${i}`, tone: "b", frame: 1, cell: i });
  }
  return out;
}

/** Counting facts for a frame display: how many more make the next ten, and the teen decomposition. */
export function countFacts(count: number, capacity: number): { toNextTen: number; tens: number; ones: number; full: boolean } {
  const tens = Math.floor(count / 10);
  const ones = count % 10;
  const full = count === capacity;
  const toNextTen = count === 0 ? 10 : ones === 0 ? 0 : 10 - ones;
  return { toNextTen, tens, ones, full };
}
