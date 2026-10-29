/**
 * Seeded simulations and exact probabilities for the ChanceLab widget.
 * Every simulation is a pure function of its seed, so server and client
 * renders agree and a "new run" simply changes the seed.
 */

/** mulberry32: a tiny, fast 32-bit PRNG returning numbers in [0, 1). */
export function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** A stable 32-bit seed from an experiment name and a run number. */
export function seedFor(name: string, run: number): number {
  let h = 2166136261;
  for (let i = 0; i < name.length; i++) h = Math.imul(h ^ name.charCodeAt(i), 16777619);
  return (h ^ Math.imul(run + 1, 0x9e3779b1)) >>> 0;
}

const randInt = (rng: () => number, n: number) => Math.min(n - 1, Math.floor(rng() * n));

/* ------------------------------------------------------------------------ */
/* Simulations                                                               */
/* ------------------------------------------------------------------------ */

/** 1 = heads, 0 = tails. */
export function flipCoins(seed: number, n: number): Uint8Array {
  const rng = mulberry32(seed);
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i++) out[i] = rng() < 0.5 ? 1 : 0;
  return out;
}

/** Results of rolling `dice` fair dice n times (the sum of the dice each time). */
export function rollDice(seed: number, n: number, dice = 1): Uint8Array {
  const rng = mulberry32(seed);
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    let s = 0;
    for (let d = 0; d < dice; d++) s += 1 + randInt(rng, 6);
    out[i] = s;
  }
  return out;
}

/** Tally values in [min, max] among the first `upto` entries. */
export function tally(values: ArrayLike<number>, upto: number, min: number, max: number): number[] {
  const counts = new Array(max - min + 1).fill(0);
  const m = Math.min(upto, values.length);
  for (let i = 0; i < m; i++) {
    const v = values[i];
    if (v >= min && v <= max) counts[v - min]++;
  }
  return counts;
}

/** Running proportion of 1s, sampled at about `points` evenly spaced trial counts up to `upto`. */
export function runningProportion(bits: ArrayLike<number>, upto: number, points = 160): { n: number; p: number }[] {
  const m = Math.min(upto, bits.length);
  if (m === 0) return [];
  const step = Math.max(1, Math.floor(m / points));
  const out: { n: number; p: number }[] = [];
  let ones = 0;
  for (let i = 0; i < m; i++) {
    ones += bits[i];
    const n = i + 1;
    if (n % step === 0 || n === m || n <= 10) out.push({ n, p: ones / n });
  }
  return out;
}

/** Galton board: each ball makes `rows` left/right choices; returns the bin (number of rights) of each ball and its choices. */
export function galton(seed: number, balls: number, rows: number): { bins: Uint8Array; choices: Uint8Array } {
  const rng = mulberry32(seed);
  const bins = new Uint8Array(balls);
  const choices = new Uint8Array(balls * rows);
  for (let b = 0; b < balls; b++) {
    let rights = 0;
    for (let r = 0; r < rows; r++) {
      const c = rng() < 0.5 ? 1 : 0;
      choices[b * rows + r] = c;
      rights += c;
    }
    bins[b] = rights;
  }
  return { bins, choices };
}

/**
 * Simple ±1 random walks. Returns the paths of the first `keep` walkers and,
 * for every step, the sum over all walkers of position² (for the RMS distance).
 */
export function randomWalks(seed: number, walkers: number, steps: number, keep = 8): { paths: Int16Array[]; sumSq: Float64Array } {
  const rng = mulberry32(seed);
  const paths: Int16Array[] = [];
  const sumSq = new Float64Array(steps + 1);
  for (let w = 0; w < walkers; w++) {
    const path = w < keep ? new Int16Array(steps + 1) : null;
    let x = 0;
    for (let s = 1; s <= steps; s++) {
      x += rng() < 0.5 ? -1 : 1;
      if (path) path[s] = x;
      sumSq[s] += x * x;
    }
    if (path) paths.push(path);
  }
  return { paths, sumSq };
}

/** For each simulated group of k people: 1 if two share a birthday (365 equally likely days). */
export function birthdayGroups(seed: number, groups: number, k: number, days = 365): Uint8Array {
  const rng = mulberry32(seed);
  const out = new Uint8Array(groups);
  const seen = new Uint32Array(days);
  for (let g = 0; g < groups; g++) {
    const stamp = g + 1;
    let shared = 0;
    for (let i = 0; i < k; i++) {
      const d = randInt(rng, days);
      if (seen[d] === stamp) shared = 1;
      seen[d] = stamp;
    }
    out[g] = shared;
  }
  return out;
}

export interface MontyGame {
  car: number;
  pick: number;
  opened: number;
}

/** One Monty Hall game: the host opens a goat door that is not the player's pick (at random when he has a choice). */
export function montyGame(rng: () => number, pick?: number): MontyGame {
  const car = randInt(rng, 3);
  const p = pick ?? randInt(rng, 3);
  const options = [0, 1, 2].filter((d) => d !== p && d !== car);
  const opened = options[randInt(rng, options.length)];
  return { car, pick: p, opened };
}

/** 1 when sticking with the first pick wins the car; switching wins exactly in the other games. */
export function montyHall(seed: number, games: number): Uint8Array {
  const rng = mulberry32(seed);
  const out = new Uint8Array(games);
  for (let i = 0; i < games; i++) {
    const g = montyGame(rng);
    out[i] = g.pick === g.car ? 1 : 0;
  }
  return out;
}

export interface Needles {
  x: Float32Array;
  y: Float32Array;
  dx: Float32Array;
  dy: Float32Array;
  crosses: Uint8Array;
}

/**
 * Buffon's needle with needle length = line spacing = 1. Lines are y = 0, 1, …, `strips`.
 * Directions come from rejection sampling in the unit disc, so π is never used.
 */
export function dropNeedles(seed: number, n: number, width = 6, strips = 4): Needles {
  const rng = mulberry32(seed);
  const out: Needles = { x: new Float32Array(n), y: new Float32Array(n), dx: new Float32Array(n), dy: new Float32Array(n), crosses: new Uint8Array(n) };
  for (let i = 0; i < n; i++) {
    let u = 0;
    let v = 0;
    let r2 = 0;
    do {
      u = 2 * rng() - 1;
      v = 2 * rng() - 1;
      r2 = u * u + v * v;
    } while (r2 > 1 || r2 < 1e-12);
    const r = Math.sqrt(r2);
    const x = rng() * width;
    const y = rng() * strips;
    const half = 0.5 * Math.abs(v / r);
    out.x[i] = x;
    out.y[i] = y;
    out.dx[i] = u / r;
    out.dy[i] = v / r;
    out.crosses[i] = Math.floor(y - half) !== Math.floor(y + half) ? 1 : 0;
  }
  return out;
}

/* ------------------------------------------------------------------------ */
/* Exact values                                                              */
/* ------------------------------------------------------------------------ */

export function binomialCoefficient(n: number, k: number): number {
  if (k < 0 || k > n) return 0;
  let c = 1;
  for (let i = 1; i <= Math.min(k, n - k); i++) c = (c * (n - i + 1)) / i;
  return Math.round(c);
}

/** P(k heads in n fair flips) = C(n, k) / 2ⁿ. */
export function binomialPmf(n: number, k: number): number {
  return binomialCoefficient(n, k) / 2 ** n;
}

export function normalPdf(x: number, mean: number, sd: number): number {
  const z = (x - mean) / sd;
  return Math.exp(-0.5 * z * z) / (sd * Math.sqrt(2 * Math.PI));
}

/** P(sum of two fair dice = s). */
export function twoDiceExact(s: number): number {
  return s < 2 || s > 12 ? 0 : (6 - Math.abs(s - 7)) / 36;
}

/** P(some two of k people share a birthday) with `days` equally likely birthdays. */
export function birthdayExact(k: number, days = 365): number {
  if (k > days) return 1;
  let none = 1;
  for (let i = 0; i < k; i++) none *= (days - i) / days;
  return 1 - none;
}

/** Half-width of an approximate 95% interval for a proportion (normal approximation). */
export function ci95(p: number, n: number): number {
  return n > 0 ? 1.96 * Math.sqrt(Math.max(0, p * (1 - p)) / n) : 1;
}

/** Buffon estimate of π (needle length = spacing) and an approximate 95% half-width (delta method). */
export function buffonEstimate(crossings: number, n: number): { estimate: number | null; halfWidth: number | null } {
  if (crossings === 0 || n === 0) return { estimate: null, halfWidth: null };
  const p = crossings / n;
  const se = (2 / (p * p)) * Math.sqrt((p * (1 - p)) / n);
  return { estimate: (2 * n) / crossings, halfWidth: 1.96 * se };
}

/** Nicely rounded trial counts for sliders. */
export const TRIAL_STEPS = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000];

export function trialSteps(extra?: number): number[] {
  const s = new Set(TRIAL_STEPS);
  if (extra && Number.isFinite(extra)) s.add(Math.round(Math.min(10000, Math.max(10, extra))));
  return [...s].sort((a, b) => a - b);
}
