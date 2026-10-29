/** Multiples, the Sieve of Eratosthenes, factor pairs and Euclid's algorithm, for the NumberGrid widget. */
import { gcd } from "./number-common";

/** Multiples of k in 1..size. */
export function multiplesOf(k: number, size: number): number[] {
  const out: number[] = [];
  if (k < 1) return out;
  for (let m = k; m <= size; m += k) out.push(m);
  return out;
}

export interface SieveStep {
  kind: "start" | "one" | "prime" | "done";
  /** The prime whose multiples are crossed out in this step. */
  p?: number;
  /** Numbers crossed out for the first time in this step. */
  crossed: number[];
}

/**
 * The Sieve of Eratosthenes up to `size`, one prime per step:
 * start → cross out 1 → for each prime p with p² ≤ size, cross out its multiples → done.
 */
export function sieveSteps(size: number): { steps: SieveStep[]; primes: number[] } {
  const crossed = new Uint8Array(size + 1);
  const steps: SieveStep[] = [{ kind: "start", crossed: [] }];
  if (size >= 1) {
    crossed[1] = 1;
    steps.push({ kind: "one", crossed: [1] });
  }
  for (let p = 2; p * p <= size; p++) {
    if (crossed[p]) continue;
    const newly: number[] = [];
    for (let m = 2 * p; m <= size; m += p) {
      if (!crossed[m]) {
        crossed[m] = 1;
        newly.push(m);
      }
    }
    steps.push({ kind: "prime", p, crossed: newly });
  }
  const primes: number[] = [];
  for (let m = 2; m <= size; m++) if (!crossed[m]) primes.push(m);
  steps.push({ kind: "done", crossed: [] });
  return { steps, primes };
}

/** Plain trial-division primality test (used to cross-check the sieve). */
export function isPrime(n: number): boolean {
  if (n < 2) return false;
  for (let d = 2; d * d <= n; d++) if (n % d === 0) return false;
  return true;
}

/** Factor pairs [a, b] with a ≤ b and a × b = n. */
export function factorPairs(n: number): [number, number][] {
  const out: [number, number][] = [];
  for (let a = 1; a * a <= n; a++) if (n % a === 0) out.push([a, n / a]);
  return out;
}

/** All factors of n in increasing order. */
export function factorsOf(n: number): number[] {
  const pairs = factorPairs(n);
  const small = pairs.map(([a]) => a);
  const big = pairs.map(([, b]) => b).filter((b, i) => b !== pairs[i][0]).reverse();
  return [...small, ...big];
}

export interface EuclidStep {
  big: number;
  small: number;
  q: number;
  r: number;
}

/** Euclid's algorithm: big = q × small + r, repeated until r = 0. Larger number first. */
export function euclidSteps(a: number, b: number): EuclidStep[] {
  let p = Math.max(a, b);
  let q = Math.min(a, b);
  const steps: EuclidStep[] = [];
  while (q > 0) {
    steps.push({ big: p, small: q, q: Math.floor(p / q), r: p % q });
    [p, q] = [q, p % q];
  }
  return steps;
}

export interface Square {
  x: number;
  y: number;
  size: number;
  /** Which Euclid step cut this square (0-based). */
  step: number;
}

/**
 * Cut the largest possible squares from a w × h rectangle, again and again,
 * until nothing is left. The squares of step i have side = euclidSteps(w, h)[i].small.
 */
export function euclidSquares(w: number, h: number): Square[] {
  const out: Square[] = [];
  let x = 0;
  let y = 0;
  let step = 0;
  while (w > 0 && h > 0) {
    if (w >= h) {
      const k = Math.floor(w / h);
      for (let i = 0; i < k; i++) out.push({ x: x + i * h, y, size: h, step });
      x += k * h;
      w -= k * h;
    } else {
      const k = Math.floor(h / w);
      for (let i = 0; i < k; i++) out.push({ x, y: y + i * w, size: w, step });
      y += k * w;
      h -= k * w;
    }
    step++;
  }
  return out;
}

export { gcd };
