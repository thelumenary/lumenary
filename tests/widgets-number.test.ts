import { createElement, type ComponentType } from "react";
import { renderToString } from "react-dom/server";
import { describe, expect, it } from "vitest";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import ar from "@/i18n/messages/ar.json";
import { NUMBER_WIDGETS } from "@/components/widgets/registry-number";
import { BalanceScale } from "@/components/widgets/BalanceScale";
import { DoubleNumberLine } from "@/components/widgets/DoubleNumberLine";
import { FractionBars } from "@/components/widgets/FractionBars";
import { NumberGrid } from "@/components/widgets/NumberGrid";
import { PlaceValue } from "@/components/widgets/PlaceValue";
import { TenFrame } from "@/components/widgets/TenFrame";
import { clampInt, gcd, lcm, oneOf } from "@/components/widgets/lib/number-common";
import { add, compare, decimalText, fracText, mixedText, parseList, parseValue, reduce, sub, withDenominator } from "@/components/widgets/lib/number-fraction";
import {
  COLUMN_W,
  additionSteps,
  bundle,
  digitsOf,
  isGhost,
  layoutColumn,
  layoutRun,
  liveCount,
  nudge,
  subtractionSteps,
  totalOf,
  unbundle,
  type Walkthrough,
} from "@/components/widgets/lib/number-place";
import { euclidSquares, euclidSteps, factorPairs, factorsOf, isPrime, multiplesOf, sieveSteps } from "@/components/widgets/lib/number-grid";
import { applyMove, equationText, isolatedValue, readSide, sideText, solve, stuckFraction, type Side } from "@/components/widgets/lib/number-balance";
import { matchBottom, rationalText, simplestRatio, sliderStep } from "@/components/widgets/lib/number-ratio";
import { countFacts, makeTenCounters, makeTenPlan } from "@/components/widgets/lib/number-tenframe";

/* ------------------------------------------------------------------ common */

describe("number-common", () => {
  it("clamps and coerces MDX props", () => {
    expect(clampInt(5, 0, 10, 3)).toBe(5);
    expect(clampInt(50, 0, 10, 3)).toBe(10);
    expect(clampInt(-4, 0, 10, 3)).toBe(0);
    expect(clampInt(2.6, 0, 10, 3)).toBe(3);
    expect(clampInt("7", 0, 10, 3)).toBe(7);
    expect(clampInt("lots", 0, 10, 3)).toBe(3);
    expect(clampInt(undefined, 0, 10, 30)).toBe(10);
    expect(clampInt(NaN, 0, 10, 3)).toBe(3);
    expect(clampInt(Infinity, 0, 10, 3)).toBe(3);
  });
  it("accepts only listed options", () => {
    expect(oneOf("add", ["add", "build"] as const, "build")).toBe("add");
    expect(oneOf("nope", ["add", "build"] as const, "build")).toBe("build");
    expect(oneOf(3, ["add", "build"] as const, "build")).toBe("build");
  });
  it("computes gcd and lcm", () => {
    expect(gcd(48, 18)).toBe(6);
    expect(gcd(-12, 8)).toBe(4);
    expect(gcd(7, 0)).toBe(7);
    expect(lcm(4, 6)).toBe(12);
    expect(lcm(0, 5)).toBe(0);
  });
});

/* ------------------------------------------------------------------ fractions */

describe("number-fraction", () => {
  it("parses fractions, mixed numbers, wholes and decimals exactly", () => {
    expect(parseValue("3/4")).toMatchObject({ frac: { n: 3, d: 4 }, kind: "fraction", label: "3/4" });
    expect(parseValue(" 1 1/2 ")).toMatchObject({ frac: { n: 3, d: 2 }, kind: "mixed", label: "1 1/2" });
    expect(parseValue("2")).toMatchObject({ frac: { n: 2, d: 1 }, kind: "whole" });
    expect(parseValue("0.75")).toMatchObject({ frac: { n: 3, d: 4 }, kind: "decimal", label: "0.75" });
    expect(parseValue(".5")?.frac).toEqual({ n: 1, d: 2 });
    expect(parseValue("0,25")?.frac).toEqual({ n: 1, d: 4 });
    expect(parseValue("6/8")?.frac).toEqual({ n: 6, d: 8 }); // kept as written
    expect(parseValue(0.2)?.frac).toEqual({ n: 1, d: 5 });
    expect(parseValue("3 ⁄ 5")?.frac).toEqual({ n: 3, d: 5 });
  });
  it("rejects malformed and negative input", () => {
    for (const bad of ["", "abc", "-1/2", "3/0", "1/2/3", "1.2.3", "x", null, undefined, {}, "1e3"]) expect(parseValue(bad), String(bad)).toBeNull();
  });
  it("splits a list into good values and bad entries", () => {
    const r = parseList(["1/2", "oops", "0.5", 3]);
    expect(r.values.map((v) => fracText(v.frac))).toEqual(["1/2", "1/2", "3"]);
    expect(r.bad).toEqual(["oops"]);
    expect(parseList(undefined)).toEqual({ values: [], bad: [] });
    expect(parseList("2/3").values).toHaveLength(1);
  });
  it("compares, adds and subtracts exactly", () => {
    expect(compare({ n: 3, d: 4 }, { n: 2, d: 3 })).toBe(1);
    expect(compare({ n: 2, d: 4 }, { n: 1, d: 2 })).toBe(0);
    expect(compare({ n: 1, d: 3 }, { n: 1, d: 2 })).toBe(-1);
    expect(add({ n: 1, d: 2 }, { n: 1, d: 3 })).toEqual({ n: 5, d: 6 });
    expect(add({ n: 3, d: 4 }, { n: 3, d: 4 })).toEqual({ n: 3, d: 2 });
    expect(sub({ n: 1, d: 2 }, { n: 1, d: 3 })).toEqual({ n: 1, d: 6 });
    expect(sub({ n: 1, d: 3 }, { n: 1, d: 2 })).toEqual({ n: -1, d: 6 });
    expect(withDenominator({ n: 2, d: 3 }, 12)).toEqual({ n: 8, d: 12 });
    expect(reduce({ n: 12, d: 18 })).toEqual({ n: 2, d: 3 });
  });
  it("prints decimals only when they terminate", () => {
    expect(decimalText({ n: 1, d: 4 })).toBe("0.25");
    expect(decimalText({ n: 5, d: 2 })).toBe("2.5");
    expect(decimalText({ n: 3, d: 1 })).toBe("3");
    expect(decimalText({ n: 1, d: 3 })).toBeNull();
    expect(decimalText({ n: 1, d: 64 }, 4)).toBeNull(); // 0.015625 needs 6 places
    expect(decimalText({ n: 3, d: 40 })).toBe("0.075");
    expect(mixedText({ n: 7, d: 4 })).toBe("1 3/4");
    expect(mixedText({ n: 8, d: 4 })).toBe("2");
    expect(mixedText({ n: 2, d: 6 })).toBe("1/3");
  });
});

/* ------------------------------------------------------------------ place value */

const finalAnswer = (w: Walkthrough) => {
  const last = w.steps[w.steps.length - 1];
  return last.written.answer.reduce<number>((s, d, i) => s + (d ?? 0) * 10 ** i, 0);
};

describe("number-place", () => {
  it("reads digits and totals (counts may exceed 9)", () => {
    expect(digitsOf(347, 4)).toEqual([7, 4, 3, 0]);
    expect(totalOf([17, 4, 3])).toBe(357);
  });
  it("regroups only when allowed and preserves the total", () => {
    const c = [12, 3, 0];
    const b = bundle(c, 0)!;
    expect(b).toEqual([2, 4, 0]);
    expect(totalOf(b)).toBe(totalOf(c));
    expect(bundle([9, 3, 0], 0)).toBeNull();
    expect(bundle([10, 0], 1)).toBeNull(); // no higher column
    const u = unbundle([2, 4, 0], 1)!;
    expect(u).toEqual([12, 3, 0]);
    expect(unbundle([12, 3, 0], 1)).toBeNull(); // would exceed 19 in the ones
    expect(unbundle([5, 0], 1)).toBeNull();
    expect(nudge([9, 9, 9], 0, 1, 999)).toBeNull(); // over max
    expect(nudge([0, 0], 0, -1, 99)).toBeNull();
    expect(nudge([3, 1], 1, 1, 99)).toEqual([3, 2]);
  });
  it("walks through 47 + 38 with one carry", () => {
    const w = additionSteps(47, 38);
    expect(w.steps.map((s) => s.kind)).toEqual(["start", "combine", "regroup", "combine", "done"]);
    expect(w.steps[1].vars).toMatchObject({ a: 7, b: 8, total: 15 });
    expect(w.steps[2].written.carries[1]).toBe(1);
    expect(w.steps[2].written.answer[0]).toBe(5);
    expect(w.steps[3].vars).toMatchObject({ a: 4, b: 3, carry: 1, total: 8 });
    expect(finalAnswer(w)).toBe(85);
    // The regroup step shows 10 ghost blocks leaving the ones and a carried block arriving in the tens.
    const g = w.steps[2].columns;
    expect(g[0].items.filter((t) => t === "traded")).toHaveLength(10);
    expect(g[1].items.filter((t) => t === "carry")).toHaveLength(1);
  });
  it("carries through a chain: 999 + 1 = 1000", () => {
    const w = additionSteps(999, 1);
    expect(w.cols).toBe(4);
    expect(w.steps.filter((s) => s.kind === "regroup")).toHaveLength(3);
    expect(finalAnswer(w)).toBe(1000);
  });
  it("borrows across a zero: 503 − 127", () => {
    const w = subtractionSteps(503, 127);
    expect(w.steps.map((s) => s.kind)).toEqual(["start", "borrow", "borrow", "takeaway", "takeaway", "takeaway", "done"]);
    const firstBorrow = w.steps[1];
    expect(firstBorrow.from).toBe(2); // tens are empty, so a hundred is broken first
    expect(firstBorrow.firstBreak).toBe(true);
    expect(w.steps[2].from).toBe(1);
    const top = w.steps[w.steps.length - 1].written.top;
    expect(top.map((c) => c.value)).toEqual([13, 9, 4]);
    expect(top[1].crossed).toEqual([0, 10]);
    expect(finalAnswer(w)).toBe(376);
  });
  it("swaps when the second number is larger", () => {
    const w = subtractionSteps(27, 52);
    expect(w.swapped).toBe(true);
    expect(w.result).toBe(25);
  });
  it("agrees with ordinary arithmetic on many inputs, block for block", () => {
    for (let a = 0; a <= 400; a += 7) {
      for (let b = 0; b <= 400; b += 9) {
        const s = additionSteps(a, b);
        expect(finalAnswer(s), `${a}+${b}`).toBe(a + b);
        const last = s.steps[s.steps.length - 1];
        expect(last.columns.map(liveCount), `${a}+${b} blocks`).toEqual(digitsOf(a + b, s.cols));
        const d = subtractionSteps(a, b);
        expect(finalAnswer(d), `${a}-${b}`).toBe(Math.abs(a - b));
        const dl = d.steps[d.steps.length - 1];
        expect(dl.columns.map(liveCount), `${a}-${b} blocks`).toEqual(digitsOf(Math.abs(a - b), d.cols));
        // Every snapshot keeps every column within the drawable cap.
        for (const st of [...s.steps, ...d.steps]) for (const c of st.columns) expect(c.items.length).toBeLessThanOrEqual(20);
      }
    }
    for (const [a, b] of [
      [9999, 0],
      [4567, 5432],
      [1000, 1],
      [8000, 7999],
      [6205, 3478],
    ])
      expect(finalAnswer(subtractionSteps(a, b))).toBe(Math.abs(a - b));
    expect(finalAnswer(additionSteps(4567, 5432))).toBe(9999);
  });
  it("lays out blocks inside the column", () => {
    for (let kind = 0; kind < 4; kind++)
      for (let n = 0; n <= 19; n++) {
        const { pos, height } = layoutRun(kind, n);
        expect(pos).toHaveLength(n);
        for (const p of pos) {
          expect(p.x).toBeGreaterThanOrEqual(0);
          expect(p.x).toBeLessThanOrEqual(COLUMN_W);
          expect(p.y).toBeLessThanOrEqual(height);
        }
      }
    const lay = layoutColumn(0, { items: ["a", "a", "b"], breaks: [2] });
    expect(lay.separators).toHaveLength(1);
    expect(lay.pos[2].y).toBeGreaterThan(lay.pos[1].y);
    expect(isGhost("taken")).toBe(true);
    // Rods: groups sit side by side (wrapping inside the column); stacks fan downwards.
    const rods = layoutColumn(1, { items: [...Array(6).fill("a"), ...Array(7).fill("b"), "carry"], breaks: [6, 13] });
    expect(rods.pos).toHaveLength(14);
    for (const p of rods.pos) expect(p.x + 8).toBeLessThanOrEqual(COLUMN_W);
    expect(new Set(rods.pos.map((p) => `${p.x},${p.y}`)).size).toBe(14);
    const flats = layoutColumn(2, { items: ["a", "a", "b", "carry"], breaks: [2, 3] });
    expect(flats.pos.map((p) => p.y)).toEqual([0, 8, 26, 44]);
  });
});

/* ------------------------------------------------------------------ grid */

describe("number-grid", () => {
  it("lists multiples", () => {
    expect(multiplesOf(7, 30)).toEqual([7, 14, 21, 28]);
    expect(multiplesOf(0, 30)).toEqual([]);
  });
  it("sieves exactly the primes, one prime per step", () => {
    const { steps, primes } = sieveSteps(100);
    expect(primes).toHaveLength(25);
    expect(primes.every(isPrime)).toBe(true);
    expect(steps.map((s) => s.kind)).toEqual(["start", "one", "prime", "prime", "prime", "prime", "done"]);
    expect(steps.filter((s) => s.p).map((s) => s.p)).toEqual([2, 3, 5, 7]);
    const crossed = steps.flatMap((s) => s.crossed);
    expect(new Set(crossed).size).toBe(crossed.length); // each number crossed once
    for (let m = 1; m <= 100; m++) expect(crossed.includes(m), String(m)).toBe(!isPrime(m));
    // the step for p crosses nothing below p²
    for (const s of steps) if (s.p) expect(Math.min(...s.crossed)).toBe(s.p * s.p);
    for (const size of [10, 37, 250, 400]) expect(sieveSteps(size).primes).toEqual(Array.from({ length: size }, (_, i) => i + 1).filter(isPrime));
  });
  it("finds factor pairs and factors", () => {
    expect(factorPairs(24)).toEqual([
      [1, 24],
      [2, 12],
      [3, 8],
      [4, 6],
    ]);
    expect(factorsOf(36)).toEqual([1, 2, 3, 4, 6, 9, 12, 18, 36]);
    expect(factorsOf(1)).toEqual([1]);
    expect(factorsOf(13)).toEqual([1, 13]);
  });
  it("runs Euclid's algorithm and tiles the rectangle with its squares", () => {
    expect(euclidSteps(36, 15)).toEqual([
      { big: 36, small: 15, q: 2, r: 6 },
      { big: 15, small: 6, q: 2, r: 3 },
      { big: 6, small: 3, q: 2, r: 0 },
    ]);
    for (const [a, b] of [
      [36, 15],
      [15, 36],
      [21, 13],
      [100, 1],
      [7, 7],
      [288, 120],
    ]) {
      const sq = euclidSquares(a, b);
      const steps = euclidSteps(a, b);
      expect(sq.reduce((s, q) => s + q.size * q.size, 0)).toBe(a * b);
      for (const q of sq) {
        expect(q.x + q.size).toBeLessThanOrEqual(a);
        expect(q.y + q.size).toBeLessThanOrEqual(b);
        expect(q.size).toBe(steps[q.step].small);
      }
      steps.forEach((s, i) => expect(sq.filter((q) => q.step === i)).toHaveLength(s.q));
      expect(sq[sq.length - 1].size).toBe(gcd(a, b));
    }
  });
});

/* ------------------------------------------------------------------ balance */

describe("number-balance", () => {
  const L: Side = { x: 2, units: 3 };
  const R: Side = { x: 0, units: 11 };
  it("reads sides defensively", () => {
    expect(readSide({ x: 2, units: 3 }, R)).toEqual({ x: 2, units: 3 });
    expect(readSide({ x: "two", units: 99 }, R)).toEqual({ x: 0, units: 20 });
    expect(readSide(null, R)).toEqual(R);
    expect(readSide("2x+3", R)).toEqual(R);
  });
  it("solves 2x + 3 = 11 by legal moves and keeps the solution", () => {
    let l = L;
    let r = R;
    for (let i = 0; i < 3; i++) {
      const m = applyMove(l, r, { kind: "subUnit" }, false);
      if (!m.ok) throw new Error(m.reason);
      ({ left: l, right: r } = m);
      expect(solve(l, r)).toEqual({ kind: "unique", n: 4, d: 1 });
    }
    expect(equationText(l, r)).toBe("2x = 8");
    expect(applyMove(l, r, { kind: "divide", k: 3 }, false)).toEqual({ ok: false, reason: "notDivisible" });
    const d = applyMove(l, r, { kind: "divide", k: 2 }, false);
    expect(d).toEqual({ ok: true, left: { x: 1, units: 0 }, right: { x: 0, units: 4 } });
    if (d.ok) expect(isolatedValue(d.left, d.right)).toBe(4);
  });
  it("rejects moves that are not the same on both sides or go negative", () => {
    expect(applyMove({ x: 1, units: 0 }, { x: 0, units: 5 }, { kind: "subUnit" }, false)).toEqual({ ok: false, reason: "noUnits" });
    expect(applyMove({ x: 1, units: 2 }, { x: 0, units: 5 }, { kind: "subX" }, false)).toEqual({ ok: false, reason: "noX" });
    expect(applyMove({ x: 1, units: 0 }, { x: 0, units: 5 }, { kind: "subUnit" }, true)).toMatchObject({ ok: true, left: { x: 1, units: -1 } });
    expect(applyMove({ x: 1, units: 20 }, { x: 0, units: 5 }, { kind: "addUnit" }, false)).toEqual({ ok: false, reason: "limit" });
    expect(applyMove(L, R, { kind: "divide", k: 1 }, false)).toEqual({ ok: false, reason: "badDivisor" });
  });
  it("classifies equations", () => {
    expect(solve({ x: 3, units: -2 }, { x: 1, units: 6 })).toEqual({ kind: "unique", n: 4, d: 1 });
    expect(solve({ x: 1, units: 5 }, { x: 0, units: 3 })).toEqual({ kind: "unique", n: -2, d: 1 });
    expect(solve({ x: 2, units: 0 }, { x: 0, units: 7 })).toEqual({ kind: "unique", n: 7, d: 2 });
    expect(solve({ x: 1, units: 2 }, { x: 1, units: 5 })).toEqual({ kind: "none" });
    expect(solve({ x: 2, units: 1 }, { x: 2, units: 1 })).toEqual({ kind: "all" });
    expect(stuckFraction({ x: 2, units: 0 }, { x: 0, units: 7 })).toEqual({ k: 2, c: 7 });
    expect(stuckFraction({ x: 2, units: 0 }, { x: 0, units: 8 })).toBeNull();
    expect(isolatedValue({ x: 0, units: -3 }, { x: 1, units: 0 })).toBe(-3);
  });
  it("prints sides like a textbook", () => {
    expect(sideText({ x: 2, units: 3 })).toBe("2x + 3");
    expect(sideText({ x: 1, units: 0 })).toBe("x");
    expect(sideText({ x: -1, units: -4 })).toBe("−x − 4");
    expect(sideText({ x: 0, units: -2 })).toBe("−2");
    expect(sideText({ x: 0, units: 0 })).toBe("0");
  });
});

/* ------------------------------------------------------------------ ratio, ten frame */

describe("number-ratio", () => {
  it("matches amounts exactly and prints them kindly", () => {
    expect(matchBottom(6, 3, 24)).toEqual({ n: 48, d: 1 });
    expect(rationalText(matchBottom(1, 2, 15))).toBe("7.5");
    expect(rationalText(matchBottom(4, 3, 2))).toBe("2 2/3");
    expect(rationalText({ n: 1, d: 3 })).toBe("1/3");
    expect(simplestRatio(6, 8)).toEqual({ p: 3, q: 4, g: 2 });
  });
  it("chooses a slider step that reaches every multiple", () => {
    expect(sliderStep(3, 5)).toBe(1);
    for (const [a, max] of [
      [1000, 12],
      [250, 5],
      [97, 12],
      [64, 10],
    ]) {
      const step = sliderStep(a, max);
      expect(Number.isInteger(step)).toBe(true);
      expect(a % step).toBe(0);
      expect((max * a) / step).toBeLessThanOrEqual(Math.max(240, max));
    }
  });
});

describe("number-tenframe", () => {
  it("plans make-ten moves", () => {
    expect(makeTenPlan(8, 5)).toEqual({ a: 8, b: 5, toTen: 2, rest: 3, total: 13 });
    expect(makeTenPlan(3, 4)).toMatchObject({ toTen: 4, rest: 0 });
    expect(makeTenPlan(10, 6)).toMatchObject({ toTen: 0, rest: 6 });
  });
  it("never puts two counters in one cell", () => {
    for (let a = 0; a <= 10; a++)
      for (let b = 0; b <= 10; b++)
        for (const moved of [false, true]) {
          const cs = makeTenCounters(a, b, moved);
          expect(cs).toHaveLength(a + b);
          expect(new Set(cs.map((c) => `${c.frame}:${c.cell}`)).size).toBe(a + b);
          for (const c of cs) expect(c.cell).toBeLessThan(10);
          if (moved) expect(cs.filter((c) => c.frame === 0)).toHaveLength(Math.min(10, a + b));
        }
  });
  it("counts facts", () => {
    expect(countFacts(7, 10)).toMatchObject({ toNextTen: 3, full: false });
    expect(countFacts(13, 20)).toMatchObject({ tens: 1, ones: 3, toNextTen: 7 });
    expect(countFacts(20, 20)).toMatchObject({ full: true, toNextTen: 0 });
  });
});

/* ------------------------------------------------------------------ server-render smoke tests */

const render = (C: ComponentType<any>, props: Record<string, unknown> = {}, locale: "en" | "ar" = "en") => // eslint-disable-line @typescript-eslint/no-explicit-any
  renderToString(createElement(I18nProvider, { locale, messages: locale === "en" ? en : { ...en, ...ar, w: { ...en.w, ...ar.w } }, children: createElement(C, props) }));

const UNRESOLVED = /w\.(tenFrame|placeValue|fractions|numberGrid|balance|doubleLine)\./;

const cases: [string, ComponentType<any>, Record<string, unknown>[]][] = [ // eslint-disable-line @typescript-eslint/no-explicit-any
  ["TenFrame", TenFrame, [{}, { count: 13, frames: 2 }, { mode: "make-ten", a: 7, b: 6 }, { mode: "make-ten", a: 10, b: 0 }, { count: "lots", frames: 9, mode: "???" }]],
  ["PlaceValue", PlaceValue, [{}, { mode: "build", start: 1234, max: 9999 }, { mode: "add", a: 368, b: 275 }, { mode: "subtract", a: 503, b: 127 }, { mode: "subtract", a: 20, b: 45 }, { mode: "add", a: 9000, b: 5000 }, { mode: "zzz", a: -5, b: "abc", max: 1e9 }]],
  [
    "FractionBars",
    FractionBars,
    [
      {},
      { mode: "compare", fractions: ["1/2", "2/4", "3/5"] },
      { mode: "compare", fractions: ["7/4", "5/2", "nonsense"] },
      { mode: "equivalent", fractions: ["6/8"], maxDenominator: 16 },
      { mode: "add", fractions: ["1/2", "1/3"] },
      { mode: "add", fractions: ["1/4", "2/3"], op: "-" },
      { mode: "line", fractions: ["0.75", "3/4", "1 1/2", "oops", "5"] },
      { mode: "line", fractions: [] },
      { fractions: "3/4", maxDenominator: "big" },
    ],
  ],
  ["NumberGrid", NumberGrid, [{}, { mode: "multiples", k: 4, k2: 6 }, { mode: "multiples", k: 7, columns: 7, size: 49 }, { mode: "sieve", size: 120 }, { mode: "factors", n: 36 }, { mode: "factors", n: 1 }, { mode: "gcd", a: 36, b: 15 }, { mode: "gcd", a: 1071, b: 462 }, { mode: "gcd", a: 0, b: -3 }]],
  ["BalanceScale", BalanceScale, [{}, { left: { x: 3, units: -2 }, right: { x: 1, units: 6 } }, { left: { x: 1, units: 2 }, right: { x: 1, units: 5 } }, { left: { x: 2, units: 0 }, right: { x: 0, units: 7 } }, { left: { x: 1, units: 5 }, right: { x: 0, units: 3 } }, { left: "2x+3", right: null, allowNegative: "yes" }]],
  ["DoubleNumberLine", DoubleNumberLine, [{}, { a: 2, b: 5, labels: ["cups of rice", "servings"], max: 8, table: true }, { a: 1000, b: 7, max: 12 }, { a: -1, b: 0, labels: "nope", max: 99 }]],
];

describe("number widgets render on the server", () => {
  it("registers every widget under its tag name", () => {
    expect(Object.keys(NUMBER_WIDGETS).sort()).toEqual(["BalanceScale", "DoubleNumberLine", "FractionBars", "NumberGrid", "PlaceValue", "TenFrame"]);
  });
  for (const [name, C, propsList] of cases) {
    it(`${name}: default and example props`, () => {
      for (const props of propsList) {
        const html = render(C, props);
        expect(html.length, JSON.stringify(props)).toBeGreaterThan(200);
        expect(html, `${name} ${JSON.stringify(props)} has an untranslated key`).not.toMatch(UNRESOLVED);
        expect(render(C, props), "deterministic render").toBe(html);
      }
    });
    it(`${name}: renders in Arabic and accepts title overrides`, () => {
      const html = render(C, { ...propsList[1], title: "Custom title", subtitle: "Custom subtitle" }, "ar");
      expect(html).toContain("Custom title");
      expect(html).toContain("Custom subtitle");
      expect(html).not.toMatch(UNRESOLVED);
    });
  }
  it("shows the right answers in the initial render", () => {
    expect(render(FractionBars, { mode: "compare", fractions: ["3/4", "2/3"] })).toContain("&gt;");
    expect(render(FractionBars, { mode: "line", fractions: ["0.75", "3/4"] })).toContain("0.75 = 3/4");
    expect(render(FractionBars, { mode: "compare", fractions: ["1/2", "oops"] })).toContain("oops");
    expect(render(NumberGrid, { mode: "factors", n: 36 })).toContain("1, 2, 3, 4, 6, 9, 12, 18, 36");
    expect(render(BalanceScale, { left: { x: 2, units: 3 }, right: { x: 0, units: 11 } })).toContain("2x + 3 = 11");
    expect(render(PlaceValue, { mode: "build", start: 347 })).toContain("300 + 40 + 7");
    expect(render(DoubleNumberLine, { a: 3, b: 24 })).toContain("1 : 8");
    expect(render(TenFrame, { mode: "make-ten", a: 8, b: 5 })).toContain("8 + 5 = ?");
  });
});
