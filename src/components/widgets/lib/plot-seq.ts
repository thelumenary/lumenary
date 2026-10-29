/**
 * Pure logic for SequenceLab: terms and ε-band indices of sequences, partial
 * sums of series (compensated summation), the harmonic series, iteration of
 * maps (orbits, cycles, fixed points) and Fourier partial sums with the Gibbs
 * overshoot. Everything here is a finite numerical computation — the widget
 * labels results as evidence, never as proof.
 */

export const EULER_GAMMA = 0.5772156649015329;
/** Limit of the Gibbs overshoot as a fraction of the jump: Si(π)/π − 1/2. */
export const GIBBS_FRACTION = 1.851937051982466 / Math.PI - 0.5;

/* ---------------------------------------------------------------------------
 * Sequences
 * ------------------------------------------------------------------------- */

/** a_1 … a_count (index i holds a_{i+1}). */
export function sequenceTerms(a: (n: number) => number, count: number): number[] {
  const m = Math.max(0, Math.min(100000, Math.floor(count)));
  const out = new Array<number>(m);
  for (let i = 0; i < m; i++) out[i] = a(i + 1);
  return out;
}

export interface EpsilonResult {
  /** First n such that every checked term from n on lies in (L − ε, L + ε); null if none convincingly. */
  index: number | null;
  /** Largest checked n whose term lies outside the band (or is undefined); null if none. */
  lastOutside: number | null;
  /** Number of terms checked. */
  checked: number;
  /** First n with an undefined term, if any. */
  firstUndefined: number | null;
}

/**
 * The ε–N test for a candidate limit L, on finitely many terms. An index is
 * only reported when at least the second half of the checked terms all lie
 * inside the band, so a sequence that keeps wandering out is not "found".
 */
export function epsilonIndex(terms: readonly number[], L: number, eps: number): EpsilonResult {
  let lastOutside: number | null = null;
  let firstUndefined: number | null = null;
  for (let i = 0; i < terms.length; i++) {
    const v = terms[i];
    if (!Number.isFinite(v)) {
      if (firstUndefined === null) firstUndefined = i + 1;
      lastOutside = i + 1;
    } else if (!(Math.abs(v - L) < eps)) lastOutside = i + 1;
  }
  const checked = terms.length;
  if (checked === 0 || !Number.isFinite(L) || !(eps > 0)) return { index: null, lastOutside, checked, firstUndefined };
  const index = lastOutside === null ? 1 : lastOutside + 1;
  return { index: index <= Math.ceil(checked / 2) ? index : null, lastOutside, checked, firstUndefined };
}

/* ---------------------------------------------------------------------------
 * Series
 * ------------------------------------------------------------------------- */

/** S_1 … S_m by compensated (Kahan–Neumaier) summation; NaN from the first undefined term on. */
export function partialSums(terms: readonly number[]): number[] {
  const out = new Array<number>(terms.length);
  let sum = 0;
  let c = 0;
  let broken = false;
  for (let i = 0; i < terms.length; i++) {
    const v = terms[i];
    if (broken || !Number.isFinite(v)) {
      broken = true;
      out[i] = NaN;
      continue;
    }
    const t = sum + v;
    c += Math.abs(sum) >= Math.abs(v) ? sum - t + v : v - t + sum;
    sum = t;
    out[i] = sum + c;
  }
  return out;
}

/** True when a_n equals 1/n (to rounding) for n = 1 … 30. */
export function looksHarmonic(a: (n: number) => number): boolean {
  for (let n = 1; n <= 30; n++) {
    const v = a(n);
    if (!Number.isFinite(v) || Math.abs(v - 1 / n) > 1e-12 / n) return false;
  }
  return true;
}

/** H_n = 1 + 1/2 + … + 1/n (exact summation for n ≤ 10⁶, asymptotic expansion beyond). */
export function harmonicNumber(n: number): number {
  if (n <= 0) return 0;
  if (n <= 1e6) return partialSums(sequenceTerms((k) => 1 / k, n))[n - 1];
  return Math.log(n) + EULER_GAMMA + 1 / (2 * n) - 1 / (12 * n * n);
}

/**
 * Heuristic for the term test: true when |a_n| does not seem to decrease
 * towards 0 (the largest |a_n| on the last half of the terms is not clearly
 * smaller than on the quarter before). Inconclusive cases return false.
 */
export function termsDoNotVanish(terms: readonly number[]): boolean {
  const m = terms.length;
  if (m < 40 || terms.some((v) => !Number.isFinite(v))) return false;
  let a = 0;
  let b = 0;
  for (let i = Math.floor(m / 4); i < Math.floor(m / 2); i++) a = Math.max(a, Math.abs(terms[i]));
  for (let i = Math.floor(m / 2); i < m; i++) b = Math.max(b, Math.abs(terms[i]));
  return b > 1e-9 && b >= 0.95 * a;
}

/* ---------------------------------------------------------------------------
 * Iteration of maps (cobweb diagrams)
 * ------------------------------------------------------------------------- */

export interface IterationRun {
  /** x_0, x_1, … up to the requested number of steps (shorter if the orbit stopped). */
  xs: number[];
  stop: "ok" | "undefined" | "escape";
}

/** x_{k+1} = f(x_k) for k steps; stops when f is undefined or |x| exceeds `bound`. */
export function iterate(f: (x: number) => number, x0: number, steps: number, bound = 1e9): IterationRun {
  const k = Math.max(0, Math.min(100000, Math.floor(steps)));
  const xs = [x0];
  if (!Number.isFinite(x0)) return { xs: [], stop: "undefined" };
  let x = x0;
  for (let i = 0; i < k; i++) {
    const y = f(x);
    if (Number.isNaN(y)) return { xs, stop: "undefined" };
    if (!Number.isFinite(y) || Math.abs(y) > bound) return { xs, stop: "escape" };
    xs.push(y);
    x = y;
  }
  return { xs, stop: "ok" };
}

export type Orbit =
  | { kind: "fixed"; value: number }
  | { kind: "cycle"; period: number; values: number[] }
  | { kind: "slow"; value: number }
  | { kind: "chaos"; iterations: number }
  | { kind: "escape" }
  | { kind: "undefined" };

/** True when every subsequence x_i, x_{i+p}, … of `xs` is monotone with shrinking steps. */
function creeping(xs: readonly number[], p: number): boolean {
  for (let r = 0; r < p; r++) {
    const sub = xs.filter((_, i) => i % p === r);
    if (sub.length < 4) return false;
    const d = sub.slice(1).map((v, i) => v - sub[i]);
    if (!d.every((v) => v !== 0 && Math.sign(v) === Math.sign(d[0]))) return false;
    if (Math.abs(d[d.length - 1]) >= Math.abs(d[0])) return false;
  }
  return true;
}

/**
 * Describe the long-run behaviour of an orbit from a finite run: settles at a
 * fixed point, settles into a cycle of period ≤ 32, still creeping slowly
 * towards a limit, escapes, or shows no repeating pattern. Numerical evidence only.
 */
export function classifyOrbit(f: (x: number) => number, x0: number, total = 3000, tail = 128, tol = 1e-7): Orbit {
  const run = iterate(f, x0, total, 1e6);
  if (run.stop === "undefined") return { kind: "undefined" };
  if (run.stop === "escape") return { kind: "escape" };
  const xs = run.xs.slice(-tail);
  const close = (a: number, b: number) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a));
  for (let p = 1; p <= 32; p++) {
    let ok = true;
    for (let i = 0; i + p < xs.length && ok; i++) if (!close(xs[i], xs[i + p])) ok = false;
    if (ok) {
      if (p === 1) return { kind: "fixed", value: xs[xs.length - 1] };
      return { kind: "cycle", period: p, values: xs.slice(-p).sort((a, b) => a - b) };
    }
  }
  if (creeping(xs, 1) || creeping(xs, 2)) return { kind: "slow", value: xs[xs.length - 1] };
  return { kind: "chaos", iterations: total };
}

export interface FixedPoint {
  x: number;
  slope: number;
  kind: "attracting" | "repelling" | "neutral";
}

/** Fixed points of f in [a, b] (sign changes of f(x) − x, refined by bisection) and their stability. */
export function fixedPoints(f: (x: number) => number, [a, b]: [number, number], samples = 2000): FixedPoint[] {
  const g = (x: number) => f(x) - x;
  const out: number[] = [];
  const span = b - a;
  if (!(span > 0)) return [];
  const push = (x: number) => {
    if (!out.some((y) => Math.abs(y - x) < span * 1e-6)) out.push(x);
  };
  let px = a;
  let pg = g(a);
  if (pg === 0) push(a);
  for (let i = 1; i <= samples && out.length < 12; i++) {
    const x = a + (span * i) / samples;
    const gx = g(x);
    if (gx === 0) push(x);
    else if (Number.isFinite(pg) && Number.isFinite(gx) && pg !== 0 && Math.sign(pg) !== Math.sign(gx)) {
      let lo = px;
      let hi = x;
      let glo = pg;
      for (let k = 0; k < 80; k++) {
        const m = (lo + hi) / 2;
        const gm = g(m);
        if (!Number.isFinite(gm)) break;
        if (gm === 0) {
          lo = hi = m;
          break;
        }
        if (Math.sign(gm) === Math.sign(glo)) {
          lo = m;
          glo = gm;
        } else hi = m;
      }
      const root = (lo + hi) / 2;
      // A pole of f also changes the sign of g; keep only genuine roots.
      if (Math.abs(g(root)) < 1e-6 * Math.max(1, Math.abs(root))) push(root);
    }
    px = x;
    pg = gx;
  }
  return out
    .sort((u, v) => u - v)
    .map((x) => {
      const h = 1e-5 * Math.max(1, Math.abs(x));
      const slope = (f(x + h) - f(x - h)) / (2 * h);
      const s = Math.abs(slope);
      const kind: FixedPoint["kind"] = !Number.isFinite(s) ? "repelling" : s < 1 - 1e-3 ? "attracting" : s > 1 + 1e-3 ? "repelling" : "neutral";
      return { x, slope, kind };
    });
}

/* ---------------------------------------------------------------------------
 * Fourier series of three classic waves (period 2π)
 * ------------------------------------------------------------------------- */

export type Wave = "square" | "sawtooth" | "triangle";
export const WAVES: readonly Wave[] = ["square", "sawtooth", "triangle"];
/** Size of the jump of each wave (0 for the continuous triangle wave). */
export const WAVE_JUMP: Record<Wave, number> = { square: 2, sawtooth: 2 * Math.PI, triangle: 0 };

const TAU = 2 * Math.PI;

/**
 * The target waves: square = sign(sin x); sawtooth = x on (−π, π);
 * triangle = (2/π)·arcsin(sin x). At a jump the value is the midpoint (0).
 */
export function waveValue(w: Wave, x: number): number {
  if (w === "triangle") return (2 / Math.PI) * Math.asin(Math.max(-1, Math.min(1, Math.sin(x))));
  const r = x - TAU * Math.floor(x / TAU); // [0, 2π)
  if (w === "square") return r === 0 || r === Math.PI ? 0 : r < Math.PI ? 1 : -1;
  const s = r > Math.PI ? r - TAU : r; // (−π, π]
  return s === Math.PI ? 0 : s;
}

/**
 * Partial sum with N non-zero terms:
 *   square    (4/π) Σ sin((2k−1)x)/(2k−1)
 *   sawtooth  2 Σ (−1)^(k+1) sin(kx)/k
 *   triangle  (8/π²) Σ (−1)^(k−1) sin((2k−1)x)/(2k−1)²
 */
export function fourierPartial(w: Wave, N: number, x: number): number {
  const n = Math.max(0, Math.min(2000, Math.floor(N)));
  let s = 0;
  if (w === "square") {
    for (let k = 1; k <= n; k++) s += Math.sin((2 * k - 1) * x) / (2 * k - 1);
    return (4 / Math.PI) * s;
  }
  if (w === "sawtooth") {
    for (let k = 1; k <= n; k++) s += ((k % 2 === 1 ? 1 : -1) * Math.sin(k * x)) / k;
    return 2 * s;
  }
  for (let k = 1; k <= n; k++) s += ((k % 2 === 1 ? 1 : -1) * Math.sin((2 * k - 1) * x)) / ((2 * k - 1) * (2 * k - 1));
  return (8 / (Math.PI * Math.PI)) * s;
}

/** Maximise f on [a, b] by dense sampling followed by golden-section refinement. */
function maximise(f: (x: number) => number, a: number, b: number, samples: number): { x: number; y: number } {
  let bi = 0;
  let by = -Infinity;
  const xs: number[] = [];
  for (let i = 0; i <= samples; i++) {
    const x = a + ((b - a) * i) / samples;
    xs.push(x);
    const y = f(x);
    if (y > by) {
      by = y;
      bi = i;
    }
  }
  let lo = xs[Math.max(0, bi - 1)];
  let hi = xs[Math.min(samples, bi + 1)];
  const g = (Math.sqrt(5) - 1) / 2;
  let c = hi - g * (hi - lo);
  let d = lo + g * (hi - lo);
  let fc = f(c);
  let fd = f(d);
  for (let k = 0; k < 80; k++) {
    if (fc > fd) {
      hi = d;
      d = c;
      fd = fc;
      c = hi - g * (hi - lo);
      fc = f(c);
    } else {
      lo = c;
      c = d;
      fc = fd;
      d = lo + g * (hi - lo);
      fd = f(d);
    }
  }
  const x = (lo + hi) / 2;
  const y = f(x);
  return y >= by ? { x, y } : { x: xs[bi], y: by };
}

export interface GibbsResult {
  /** Where the partial sum peaks just before/after the jump. */
  x: number;
  peak: number;
  /** Height above the wave's value next to the jump. */
  overshoot: number;
  /** Overshoot as a fraction of the jump. */
  fraction: number;
}

/** Peak of S_N next to the jump (square: just right of 0; sawtooth: just left of π). Null for the triangle wave. */
export function gibbsOvershoot(w: Wave, N: number): GibbsResult | null {
  if (w === "triangle" || N < 1) return null;
  const f = (x: number) => fourierPartial(w, N, x);
  const samples = Math.max(2000, 80 * N);
  const best = maximise(f, 1e-9, Math.PI - 1e-9, samples);
  const level = w === "square" ? 1 : Math.PI;
  const overshoot = best.y - level;
  return { x: best.x, peak: best.y, overshoot, fraction: overshoot / WAVE_JUMP[w] };
}

/** Largest |S_N(x) − f(x)| over one period (sampled), for a continuous wave. */
export function maxFourierError(w: Wave, N: number, samples = 4000): number {
  let m = 0;
  for (let i = 0; i <= samples; i++) {
    const x = -Math.PI + (TAU * i) / samples;
    m = Math.max(m, Math.abs(fourierPartial(w, N, x) - waveValue(w, x)));
  }
  return m;
}
