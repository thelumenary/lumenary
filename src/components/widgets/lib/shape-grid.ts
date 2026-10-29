/**
 * Square-grid helpers for AreaGrid: area, perimeter (total boundary length,
 * holes included), connected pieces, boundary edges for drawing, and presets.
 */

/** cells[row][col] is true when the unit square is filled. */
export type Cells = boolean[][];

export const emptyCells = (w: number, h: number): Cells => Array.from({ length: h }, () => Array.from({ length: w }, () => false));

/** Cells from rows like "##..": '#' (or 'x') is filled, anything else is empty. Rows are padded/trimmed to w × h. */
export function cellsFromRows(rows: string[], w: number, h: number): Cells {
  return Array.from({ length: h }, (_, r) => Array.from({ length: w }, (_, c) => /[#x]/i.test(rows[r]?.[c] ?? ".")));
}

const filled = (cells: Cells, r: number, c: number) => r >= 0 && r < cells.length && c >= 0 && c < (cells[r]?.length ?? 0) && cells[r][c];

/** Number of filled unit squares. */
export const area = (cells: Cells) => cells.reduce((s, row) => s + row.filter(Boolean).length, 0);

/** Total length of the boundary: every edge between a filled square and an empty square (or the outside). */
export function perimeter(cells: Cells): number {
  let p = 0;
  cells.forEach((row, r) =>
    row.forEach((on, c) => {
      if (!on) return;
      for (const [dr, dc] of [
        [-1, 0],
        [1, 0],
        [0, -1],
        [0, 1],
      ])
        if (!filled(cells, r + dr, c + dc)) p++;
    }),
  );
  return p;
}

/** Number of edge-connected pieces. */
export function pieces(cells: Cells): number {
  const seen = cells.map((row) => row.map(() => false));
  let count = 0;
  cells.forEach((row, r) =>
    row.forEach((on, c) => {
      if (!on || seen[r][c]) return;
      count++;
      const stack = [[r, c]];
      seen[r][c] = true;
      while (stack.length) {
        const [y, x] = stack.pop()!;
        for (const [dy, dx] of [
          [-1, 0],
          [1, 0],
          [0, -1],
          [0, 1],
        ]) {
          const ny = y + dy;
          const nx = x + dx;
          if (filled(cells, ny, nx) && !seen[ny][nx]) {
            seen[ny][nx] = true;
            stack.push([ny, nx]);
          }
        }
      }
    }),
  );
  return count;
}

/** Boundary unit edges in grid coordinates (x = column, y = row), for drawing the perimeter. */
export function boundaryEdges(cells: Cells): { x1: number; y1: number; x2: number; y2: number }[] {
  const out: { x1: number; y1: number; x2: number; y2: number }[] = [];
  cells.forEach((row, r) =>
    row.forEach((on, c) => {
      if (!on) return;
      if (!filled(cells, r - 1, c)) out.push({ x1: c, y1: r, x2: c + 1, y2: r });
      if (!filled(cells, r + 1, c)) out.push({ x1: c, y1: r + 1, x2: c + 1, y2: r + 1 });
      if (!filled(cells, r, c - 1)) out.push({ x1: c, y1: r, x2: c, y2: r + 1 });
      if (!filled(cells, r, c + 1)) out.push({ x1: c + 1, y1: r, x2: c + 1, y2: r + 1 });
    }),
  );
  return out;
}

export const rectArea = (w: number, h: number) => w * h;
export const rectPerimeter = (w: number, h: number) => 2 * (w + h);
export const triangleArea = (base: number, height: number) => (base * height) / 2;

/** The drawing board for "draw" mode. */
export const DRAW_W = 10;
export const DRAW_H = 7;

/** Three shapes with the same area (12) and different perimeters (14, 16, 26). */
export const AREA_12_PRESETS: string[][] = [
  ["..........", "...####...", "...####...", "...####...", "..........", "..........", ".........."],
  ["..........", "..........", "..######..", "..######..", "..........", "..........", ".........."],
  ["##........", ".##.......", "..##......", "...##.....", "....##....", ".....##...", ".........."],
];
