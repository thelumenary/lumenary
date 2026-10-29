/**
 * Data-handling helpers for DataChart: input parsing, mean / median / mode,
 * frequency tables, tallies, histograms with left-closed bins, nice axis
 * steps and the "fair share" view of the mean.
 */
import { asNumber } from "./shape-util";

export interface Datum {
  label: string;
  value: number;
}

export const MAX_CATEGORIES = 12;
export const MAX_VALUES = 120;

/** Categorical data from the `data` prop: entries with a label and a finite value ≥ 0 (others are ignored). */
export function parseData(data: unknown): Datum[] {
  if (!Array.isArray(data)) return [];
  const out: Datum[] = [];
  for (const d of data) {
    if (!d || typeof d !== "object") continue;
    const rec = d as Record<string, unknown>;
    const label = typeof rec.label === "string" || typeof rec.label === "number" ? String(rec.label).trim().slice(0, 24) : "";
    const value = asNumber(rec.value);
    if (!label || !Number.isFinite(value) || value < 0) continue;
    out.push({ label, value: Math.min(value, 1000) });
    if (out.length >= MAX_CATEGORIES) break;
  }
  return out;
}

/** Numerical data from the `values` prop: finite numbers only (at most 120). */
export function parseValues(values: unknown): number[] {
  if (!Array.isArray(values)) return [];
  return values
    .map(asNumber)
    .filter((v) => Number.isFinite(v) && Math.abs(v) <= 1e6)
    .slice(0, MAX_VALUES);
}

export const sum = (xs: number[]) => xs.reduce((s, x) => s + x, 0);

export const mean = (xs: number[]) => (xs.length ? sum(xs) / xs.length : NaN);

/** Median and where it comes from in the sorted list (1-based positions: one, or the two middle ones). */
export function medianInfo(xs: number[]): { median: number; sorted: number[]; positions: number[] } {
  const sorted = [...xs].sort((a, b) => a - b);
  const k = sorted.length;
  if (!k) return { median: NaN, sorted, positions: [] };
  if (k % 2) return { median: sorted[(k - 1) / 2], sorted, positions: [(k + 1) / 2] };
  return { median: (sorted[k / 2 - 1] + sorted[k / 2]) / 2, sorted, positions: [k / 2, k / 2 + 1] };
}

export const median = (xs: number[]) => medianInfo(xs).median;

/** Frequency table of distinct values, in increasing order. */
export function frequency(xs: number[]): { value: number; count: number }[] {
  const m = new Map<number, number>();
  for (const x of xs) m.set(x, (m.get(x) ?? 0) + 1);
  return [...m.entries()].sort((a, b) => a[0] - b[0]).map(([value, count]) => ({ value, count }));
}

/**
 * The mode(s): the value(s) that appear most often. When every value appears
 * exactly once there is no mode (an empty list).
 */
export function modes(xs: number[]): { values: number[]; count: number } {
  const f = frequency(xs);
  const top = Math.max(0, ...f.map((x) => x.count));
  if (top <= 1 && xs.length > 1) return { values: [], count: top };
  return { values: f.filter((x) => x.count === top).map((x) => x.value), count: top };
}

/** Labels of the largest categories (the modal category for counts); ties give several. */
export function modalCategories(data: Datum[]): string[] {
  const top = Math.max(0, ...data.map((d) => d.value));
  if (top === 0) return [];
  return data.filter((d) => d.value === top).map((d) => d.label);
}

/** Tally marks: complete gates of five and the leftover strokes. */
export const tally = (count: number) => ({ fives: Math.floor(Math.max(0, count) / 5), ones: Math.max(0, Math.round(count)) % 5 });

/** A "nice" step (1, 2 or 5 × 10^k) so that `max` spans about `target` steps. */
export function niceStep(max: number, target = 5): number {
  if (!(max > 0)) return 1;
  const raw = max / target;
  const p = 10 ** Math.floor(Math.log10(raw));
  const m = raw / p;
  const step = (m <= 1 ? 1 : m <= 2 ? 2 : m <= 5 ? 5 : 10) * p;
  return step;
}

/** Axis ticks 0, step, 2·step, … up to at least `max`, with integer steps for counts. */
export function countTicks(max: number): number[] {
  const step = Math.max(1, Math.round(niceStep(Math.max(1, max), 5)));
  const top = Math.max(step, Math.ceil(max / step) * step);
  return Array.from({ length: Math.round(top / step) + 1 }, (_, i) => i * step);
}

export interface Bin {
  lo: number;
  hi: number;
  count: number;
}

/**
 * Histogram with bins [lo, hi) of the given width, starting at a multiple of
 * the width at or below the minimum. A value on a boundary goes in the bin to
 * its right (so the maximum can open a final bin of its own).
 */
export function histogram(xs: number[], width: number): Bin[] {
  if (!xs.length || !(width > 0)) return [];
  const min = Math.min(...xs);
  const max = Math.max(...xs);
  const start = Math.floor(min / width + 1e-9) * width;
  const count = Math.floor((max - start) / width + 1e-9) + 1;
  const bins: Bin[] = Array.from({ length: count }, (_, i) => ({ lo: roundClean(start + i * width), hi: roundClean(start + (i + 1) * width), count: 0 }));
  for (const x of xs) {
    const i = Math.min(count - 1, Math.floor((x - start) / width + 1e-9));
    bins[i].count++;
  }
  return bins;
}

/** Remove floating-point noise such as 0.30000000000000004. */
export const roundClean = (x: number) => Math.round(x * 1e9) / 1e9;

const WIDTHS = [0.1, 0.2, 0.25, 0.5, 1, 2, 2.5, 5, 10, 20, 25, 50, 100, 200, 250, 500, 1000];

/** Bin widths that give between 2 and 20 bins, and a default giving about 5–8 bins. */
export function binWidthOptions(xs: number[]): { options: number[]; preferred: number } {
  if (!xs.length) return { options: [1], preferred: 1 };
  const integers = xs.every((x) => Number.isInteger(x));
  const ok = WIDTHS.filter((w) => (!integers || Number.isInteger(w)) && histogram(xs, w).length >= 2 && histogram(xs, w).length <= 20);
  const options = ok.length ? ok : [Math.max(1, niceStep(Math.max(...xs) - Math.min(...xs) || 1, 5))];
  const preferred = options.find((w) => histogram(xs, w).length <= 8) ?? options[options.length - 1];
  return { options, preferred };
}

/** Pictograph keys (one picture = k) that keep the longest row reasonable, and the default. */
export function pictographKeys(max: number): { options: number[]; preferred: number } {
  const options = [1, 2, 5, 10].filter((k) => max / k <= 30);
  const list = options.length ? options : [10];
  return { options: list, preferred: list.find((k) => max / k <= 10) ?? list[list.length - 1] };
}

/** How much each tower gives or receives when the towers are levelled to the mean. */
export function fairShare(xs: number[]): { mean: number; received: number[]; given: number[] } {
  const m = mean(xs);
  return { mean: m, received: xs.map((x) => Math.max(0, m - x)), given: xs.map((x) => Math.max(0, x - m)) };
}

/** A statistic for display: rounded to 2 decimal places, with a flag when that rounding is not exact. */
export function statText(x: number): { value: number; approx: boolean } {
  const value = Math.round(x * 100) / 100;
  return { value: Object.is(value, -0) ? 0 : value, approx: Math.abs(value - x) > 1e-9 };
}
