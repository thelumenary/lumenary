/**
 * Base-ten blocks: column counts, regrouping, and the column-by-column
 * addition / subtraction walkthroughs used by the PlaceValue widget.
 * Columns are little-endian: index 0 = ones, 1 = tens, 2 = hundreds, 3 = thousands.
 */

export const MAX_COLUMNS = 4;
/** Largest number of blocks a single column may hold (9 + a regrouped 10). */
export const MAX_PER_COLUMN = 19;

/** Number of digits needed to write n (at least 1). */
export function columnsFor(n: number): number {
  return Math.max(1, String(Math.max(0, Math.floor(n))).length);
}

/** The digits of n, ones first, padded to `cols`. */
export function digitsOf(n: number, cols: number): number[] {
  const out: number[] = [];
  let v = Math.max(0, Math.floor(n));
  for (let i = 0; i < cols; i++) {
    out.push(v % 10);
    v = Math.floor(v / 10);
  }
  return out;
}

export const placeValue = (i: number) => 10 ** i;

/** The number shown by a set of column counts (counts may exceed 9). */
export function totalOf(counts: number[]): number {
  return counts.reduce((s, c, i) => s + c * placeValue(i), 0);
}

/** True when every column holds at most 9 blocks (so the counts are the digits). */
export const isCanonical = (counts: number[]) => counts.every((c) => c <= 9);

/** Trade 10 blocks in column i for 1 block in column i + 1. Null if not possible. */
export function bundle(counts: number[], i: number): number[] | null {
  if (i < 0 || i + 1 >= counts.length || counts[i] < 10 || counts[i + 1] >= MAX_PER_COLUMN) return null;
  const next = [...counts];
  next[i] -= 10;
  next[i + 1] += 1;
  return next;
}

/** Break 1 block in column i into 10 blocks in column i − 1. Null if not possible. */
export function unbundle(counts: number[], i: number): number[] | null {
  if (i < 1 || i >= counts.length || counts[i] < 1 || counts[i - 1] + 10 > MAX_PER_COLUMN) return null;
  const next = [...counts];
  next[i] -= 1;
  next[i - 1] += 10;
  return next;
}

/** Add (delta = +1) or remove (delta = −1) one block in column i, respecting the column cap and the total cap. */
export function nudge(counts: number[], i: number, delta: 1 | -1, max: number): number[] | null {
  const next = [...counts];
  next[i] += delta;
  if (next[i] < 0 || next[i] > MAX_PER_COLUMN || totalOf(next) > max) return null;
  return next;
}

/** Visual style of a single block in a walkthrough snapshot. */
export type Tone =
  | "a" // came from the first number
  | "b" // came from the second number (addition)
  | "carry" // arrived by regrouping 10 smaller blocks (addition)
  | "fresh" // arrived by breaking a bigger block (subtraction)
  | "plain" // an ordinary block
  | "traded" // ghost: was just regrouped away
  | "taken"; // ghost: taken away (subtraction)

export const isGhost = (t: Tone) => t === "traded" || t === "taken";

export interface ColumnView {
  items: Tone[];
  /** Indices in `items` where a new visual group starts (a separate pile, e.g. a | b | carry). */
  breaks: number[];
}

export interface WrittenColumn {
  /** Current digit on the top line (subtraction may raise it above 9 after borrowing). */
  value: number;
  /** Earlier values of the top digit, in order, each crossed out in the written method. */
  crossed: number[];
}

export interface WrittenView {
  top: WrittenColumn[];
  bottom: number[];
  /** Carry digit written above column i (addition). */
  carries: (number | null)[];
  answer: (number | null)[];
}

export type StepKind = "start" | "combine" | "regroup" | "borrow" | "takeaway" | "done";

export interface ArithStep {
  kind: StepKind;
  /** The column being worked on (−1 for start / done). */
  col: number;
  /** For "borrow": the column whose block is broken into 10. */
  from?: number;
  /** For "borrow": true on the first break made for this column. */
  firstBreak?: boolean;
  columns: ColumnView[];
  written: WrittenView;
  /** Numbers for the step's explanation: a, b, carry, total, rest, need, have. */
  vars: Record<string, number>;
}

export interface Walkthrough {
  op: "add" | "subtract";
  a: number;
  b: number;
  result: number;
  cols: number;
  /** True if a < b was given for subtraction and the numbers were swapped. */
  swapped: boolean;
  steps: ArithStep[];
}

const fill = (n: number, t: Tone): Tone[] => Array.from({ length: n }, () => t);
const clone = <T>(x: T): T => JSON.parse(JSON.stringify(x)) as T;
const stripTraded = (cols: ColumnView[]) => {
  for (const c of cols) {
    const keep = c.items.filter((t) => t !== "traded");
    c.items = keep;
    c.breaks = c.breaks.filter((b) => b > 0 && b < keep.length);
  }
};

/** Column-by-column addition with regrouping (carrying). a + b must be ≤ 9999. */
export function additionSteps(a: number, b: number): Walkthrough {
  const sum = a + b;
  const C = Math.min(MAX_COLUMNS, columnsFor(sum));
  const aD = digitsOf(a, C);
  const bD = digitsOf(b, C);
  const columns: ColumnView[] = aD.map((x, i) => ({ items: [...fill(x, "a"), ...fill(bD[i], "b")], breaks: x > 0 && bD[i] > 0 ? [x] : [] }));
  const written: WrittenView = { top: aD.map((v) => ({ value: v, crossed: [] })), bottom: bD, carries: aD.map(() => null), answer: aD.map(() => null) };
  const steps: ArithStep[] = [];
  const snap = (kind: StepKind, col: number, vars: Record<string, number> = {}) => steps.push({ kind, col, columns: clone(columns), written: clone(written), vars });
  snap("start", -1, { a, b });
  let carry = 0;
  for (let i = 0; i < C; i++) {
    stripTraded(columns);
    const total = aD[i] + bD[i] + carry;
    columns[i].breaks = [];
    if (total <= 9) written.answer[i] = total;
    snap("combine", i, { a: aD[i], b: bD[i], carry, total });
    if (total >= 10 && i + 1 < C) {
      columns[i] = { items: [...fill(total - 10, "plain"), ...fill(10, "traded")], breaks: [] };
      const nxt = columns[i + 1];
      if (nxt.items.length > 0) nxt.breaks = [...nxt.breaks, nxt.items.length];
      nxt.items.push("carry");
      written.carries[i + 1] = 1;
      written.answer[i] = total - 10;
      snap("regroup", i, { total, rest: total - 10 });
      carry = 1;
    } else carry = 0;
  }
  stripTraded(columns);
  snap("done", -1, { a, b, result: sum });
  return { op: "add", a, b, result: sum, cols: C, swapped: false, steps };
}

/** Column-by-column subtraction with regrouping (borrowing). Swaps the numbers if a < b. */
export function subtractionSteps(a0: number, b0: number): Walkthrough {
  const swapped = b0 > a0;
  const a = swapped ? b0 : a0;
  const b = swapped ? a0 : b0;
  const C = Math.min(MAX_COLUMNS, columnsFor(a));
  const aD = digitsOf(a, C);
  const bD = digitsOf(b, C);
  const columns: ColumnView[] = aD.map((x) => ({ items: fill(x, "plain"), breaks: [] }));
  const written: WrittenView = { top: aD.map((v) => ({ value: v, crossed: [] })), bottom: bD, carries: aD.map(() => null), answer: aD.map(() => null) };
  const steps: ArithStep[] = [];
  const snap = (kind: StepKind, col: number, vars: Record<string, number> = {}, extra: Partial<ArithStep> = {}) =>
    steps.push({ kind, col, columns: clone(columns), written: clone(written), vars, ...extra });
  const live = (c: ColumnView) => c.items.filter((t) => !isGhost(t)).length;
  snap("start", -1, { a, b });
  for (let i = 0; i < C; i++) {
    stripTraded(columns);
    const need = bD[i];
    if (written.top[i].value < need) {
      let j = i + 1;
      while (j < C && written.top[j].value === 0) j++;
      for (let k = j; k > i; k--) {
        stripTraded(columns);
        // Break the last live block of column k into 10 fresh blocks in column k − 1.
        const ck = columns[k];
        const idx = ck.items.map((t, n) => (isGhost(t) ? -1 : n)).filter((n) => n >= 0).pop();
        if (idx === undefined) break;
        ck.items.splice(idx, 1);
        ck.items.push("traded");
        written.top[k].crossed.push(written.top[k].value);
        written.top[k].value -= 1;
        const below = columns[k - 1];
        if (below.items.length > 0) below.breaks = [...below.breaks, below.items.length];
        below.items.push(...fill(10, "fresh"));
        written.top[k - 1].crossed.push(written.top[k - 1].value);
        written.top[k - 1].value += 10;
        snap("borrow", i, { need, have: written.top[i].value }, { from: k, firstBreak: k === j });
      }
    }
    stripTraded(columns);
    const have = live(columns[i]);
    // Mark the last `need` live blocks as taken away.
    let toTake = need;
    for (let n = columns[i].items.length - 1; n >= 0 && toTake > 0; n--) {
      if (!isGhost(columns[i].items[n])) {
        columns[i].items[n] = "taken";
        toTake--;
      }
    }
    written.answer[i] = have - need;
    snap("takeaway", i, { have, need, rest: have - need });
  }
  stripTraded(columns);
  snap("done", -1, { a, b, result: a - b });
  return { op: "subtract", a, b, result: a - b, cols: C, swapped, steps };
}

/** Number of non-ghost blocks in a column view. */
export const liveCount = (c: ColumnView) => c.items.filter((t) => !isGhost(t)).length;

/* ---------- Drawing layout (SVG units; each column is drawn in a viewBox COLUMN_W wide) ---------- */

export const COLUMN_W = 120;
export const UNIT = 8;
const GAP = 3;

export interface BlockPos {
  x: number;
  y: number;
}

/**
 * Positions for `count` blocks of one kind laid out in a single run.
 * Ones: rows of 5 (a gap after each ten). Tens: rods side by side, 10 per row.
 * Hundreds: a fanned stack (each flat shows its top strip). Thousands: a fanned stack of cubes.
 */
export function layoutRun(kind: number, count: number): { pos: BlockPos[]; height: number } {
  const pos: BlockPos[] = [];
  if (count <= 0) return { pos, height: 0 };
  if (kind === 0) {
    const pitch = UNIT + GAP;
    const width = 5 * pitch - GAP;
    const x0 = (COLUMN_W - width) / 2;
    for (let i = 0; i < count; i++) {
      const row = Math.floor(i / 5);
      pos.push({ x: x0 + (i % 5) * pitch, y: row * pitch + Math.floor(row / 2) * 4 });
    }
    const rows = Math.ceil(count / 5);
    return { pos, height: rows * pitch - GAP + Math.floor((rows - 1) / 2) * 4 };
  }
  if (kind === 1) {
    const pitch = UNIT + GAP;
    const perRow = Math.min(10, count);
    const width = perRow * pitch - GAP + (perRow > 5 ? 5 : 0);
    const x0 = (COLUMN_W - width) / 2;
    const rowH = UNIT * 10 + 6;
    for (let i = 0; i < count; i++) {
      const k = i % 10;
      pos.push({ x: x0 + k * pitch + (k >= 5 ? 5 : 0), y: Math.floor(i / 10) * rowH });
    }
    return { pos, height: Math.ceil(count / 10) * rowH - 6 };
  }
  const size = UNIT * 10;
  const dy = kind === 2 ? 8 : 12;
  const x0 = (COLUMN_W - size) / 2;
  for (let i = 0; i < count; i++) pos.push({ x: x0, y: i * dy + (i >= 10 ? 6 : 0) });
  return { pos, height: size + (count - 1) * dy + (count > 10 ? 6 : 0) };
}

/**
 * Lay out a column view whose items may form several groups (split at `breaks`).
 * Ones: each group is its own run, stacked with a gap (the `separators` give the gap centres).
 * Tens: rods flow left to right, with a wider gap between groups, wrapping at the column width.
 * Hundreds / thousands: one fanned stack, with an extra drop between groups.
 */
export function layoutColumn(kind: number, view: ColumnView, groupGap = 18): { pos: BlockPos[]; height: number; separators: number[] } {
  const n = view.items.length;
  const breaks = view.breaks.filter((b) => b > 0 && b < n);
  const pos: BlockPos[] = [];
  const separators: number[] = [];
  if (n === 0) return { pos, height: 0, separators };
  if (kind === 0) {
    const cuts = [0, ...breaks, n];
    let y = 0;
    for (let g = 0; g + 1 < cuts.length; g++) {
      const run = layoutRun(kind, cuts[g + 1] - cuts[g]);
      if (g > 0) {
        separators.push(y + groupGap / 2);
        y += groupGap;
      }
      for (const p of run.pos) pos.push({ x: p.x, y: p.y + y });
      y += run.height;
    }
    return { pos, height: y, separators };
  }
  if (kind === 1) {
    const pitch = UNIT + GAP;
    const rowH = UNIT * 10 + 6;
    const rows: number[][] = [[]];
    let x = 0;
    let inGroup = 0;
    for (let i = 0; i < n; i++) {
      const isBreak = breaks.includes(i);
      if (isBreak) inGroup = 0;
      let gap = i === 0 || rows[rows.length - 1].length === 0 ? 0 : isBreak ? 9 : inGroup > 0 && inGroup % 5 === 0 ? 4 : 0;
      if (x + gap + UNIT > COLUMN_W && rows[rows.length - 1].length > 0) {
        rows.push([]);
        x = 0;
        gap = 0;
      }
      x += gap;
      rows[rows.length - 1].push(x);
      x += pitch;
      inGroup++;
    }
    rows.forEach((xs, r) => {
      const width = xs[xs.length - 1] + UNIT;
      const off = (COLUMN_W - width) / 2;
      for (const xx of xs) pos.push({ x: off + xx, y: r * rowH });
    });
    return { pos, height: rows.length * rowH - 6, separators };
  }
  const size = UNIT * 10;
  const dy = kind === 2 ? 8 : 12;
  const x0 = (COLUMN_W - size) / 2;
  let y = 0;
  for (let i = 0; i < n; i++) {
    if (i > 0) y += dy + (breaks.includes(i) ? 10 : 0);
    pos.push({ x: x0, y });
  }
  return { pos, height: y + size, separators };
}
