import { createElement, type ComponentType } from "react";
import * as runtime from "react/jsx-runtime";
import { renderToString } from "react-dom/server";
import { evaluate } from "@mdx-js/mdx";
import { describe, expect, it } from "vitest";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import ar from "@/i18n/messages/ar.json";
import { SHAPE_DATA_WIDGETS } from "@/components/widgets/registry-shape-data";
import { ShapeExplorer } from "@/components/widgets/ShapeExplorer";
import { AreaGrid } from "@/components/widgets/AreaGrid";
import { AnalogClock } from "@/components/widgets/AnalogClock";
import { RulerMeasure } from "@/components/widgets/RulerMeasure";
import { PatternMaker } from "@/components/widgets/PatternMaker";
import { DataChart } from "@/components/widgets/DataChart";
import { Spinner } from "@/components/widgets/Spinner";
import { asNumber, listOf, nextRandom, oneOf, seedFrom, simplify, toInt } from "@/components/widgets/lib/shape-util";
import {
  angleSum,
  diagonalCount,
  diagonals,
  equalMarks,
  fanTriangles,
  fitToBox,
  formatAngle,
  getShape,
  interiorAngles,
  irregularPolygon,
  parallelPairCount,
  regularPolygon,
  resolveGallery,
  rotationOrder,
  roundPreservingSum,
  sideLengths,
  symmetryAxes,
} from "@/components/widgets/lib/shape-geometry";
import { AREA_12_PRESETS, DRAW_H, DRAW_W, area, boundaryEdges, cellsFromRows, perimeter, pieces, rectPerimeter, triangleArea } from "@/components/widgets/lib/shape-grid";
import { elapsedJumps, format24, handAngles, hourHandDelta, minuteFromAngle, minuteHandDelta, parts12, setMinuteHand, splitDuration, timeWords, toTime } from "@/components/widgets/lib/shape-clock";
import { OBJECTS, RULER_CM, clampStart, fitWords, judge, unitFit } from "@/components/widgets/lib/shape-ruler";
import { clampCoefficients, differences, formatRule, formatTerm, growLayout, growTerm, parseCore, parseSymbol, repeatPosition } from "@/components/widgets/lib/shape-pattern";
import { binWidthOptions, countTicks, fairShare, frequency, histogram, mean, median, medianInfo, modalCategories, modes, niceStep, parseData, parseValues, pictographKeys, statText, tally } from "@/components/widgets/lib/shape-stats";
import { DEFAULT_SECTORS, cumulative, parseSectors, sectorAt, sectorFraction, sectorPath, spinMany } from "@/components/widgets/lib/shape-spinner";
import { read } from "./helpers";

/* ------------------------------------------------------------------ util */

describe("shape-util", () => {
  it("coerces MDX props safely", () => {
    expect(toInt(7.6, 1, 0, 10)).toBe(8);
    expect(toInt("3", 1, 0, 10)).toBe(3);
    expect(toInt("x", 4, 0, 10)).toBe(4);
    expect(toInt(99, 4, 0, 10)).toBe(10);
    expect(toInt(undefined, 4, 0, 10)).toBe(4);
    expect(asNumber(null)).toBeNaN();
    expect(oneOf("polygon", ["gallery", "polygon"] as const, "gallery")).toBe("polygon");
    expect(oneOf("nope", ["gallery", "polygon"] as const, "gallery")).toBe("gallery");
    expect(listOf(["a", "z", "b", "a", 3], ["a", "b"] as const)).toEqual(["a", "b"]);
    expect(listOf("a", ["a"] as const)).toEqual([]);
    expect(simplify(6, 8)).toEqual([3, 4]);
    expect(simplify(5, 5)).toEqual([1, 1]);
  });
  it("has a deterministic PRNG in [0, 1)", () => {
    let s = seedFrom(1);
    const a: number[] = [];
    for (let i = 0; i < 1000; i++) {
      const [u, next] = nextRandom(s);
      expect(u).toBeGreaterThanOrEqual(0);
      expect(u).toBeLessThan(1);
      a.push(u);
      s = next;
    }
    let s2 = seedFrom(1);
    const [u0] = nextRandom(s2);
    expect(u0).toBe(a[0]);
    s2 = seedFrom(2);
    expect(nextRandom(s2)[0]).not.toBe(a[0]);
    const avg = a.reduce((x, y) => x + y, 0) / a.length;
    expect(avg).toBeGreaterThan(0.45);
    expect(avg).toBeLessThan(0.55);
  });
});

/* ------------------------------------------------------------------ geometry */

describe("shape-geometry", () => {
  const facts: Record<string, { axes: number; order: number; pairs: number }> = {
    equilateral: { axes: 3, order: 3, pairs: 0 },
    isosceles: { axes: 1, order: 1, pairs: 0 },
    scalene: { axes: 0, order: 1, pairs: 0 },
    right: { axes: 0, order: 1, pairs: 0 },
    "right-isosceles": { axes: 1, order: 1, pairs: 0 },
    obtuse: { axes: 0, order: 1, pairs: 0 },
    square: { axes: 4, order: 4, pairs: 2 },
    rectangle: { axes: 2, order: 2, pairs: 2 },
    rhombus: { axes: 2, order: 2, pairs: 2 },
    parallelogram: { axes: 0, order: 2, pairs: 2 },
    trapezoid: { axes: 0, order: 1, pairs: 1 },
    "isosceles-trapezoid": { axes: 1, order: 1, pairs: 1 },
    kite: { axes: 1, order: 1, pairs: 0 },
    pentagon: { axes: 5, order: 5, pairs: 0 },
    hexagon: { axes: 6, order: 6, pairs: 3 },
    octagon: { axes: 8, order: 8, pairs: 4 },
  };
  for (const [id, f] of Object.entries(facts)) {
    it(`${id}: symmetry, rotation and parallel sides`, () => {
      const s = getShape(id)!;
      expect(s).not.toBeNull();
      const { points } = fitToBox(s.vertices, 360, 290, 50);
      expect(symmetryAxes(points)).toHaveLength(f.axes);
      expect(rotationOrder(points)).toBe(f.order);
      expect(parallelPairCount(points)).toBe(f.pairs);
      // Analysis does not depend on the y-flip into SVG coordinates.
      expect(symmetryAxes(s.vertices)).toHaveLength(f.axes);
    });
  }

  it("gives every named non-regular shape whole-degree angles adding to (n − 2) × 180°", () => {
    for (const id of ["equilateral", "isosceles", "scalene", "right", "right-isosceles", "obtuse", "square", "rectangle", "rhombus", "parallelogram", "trapezoid", "isosceles-trapezoid", "kite", "hexagon", "octagon", "pentagon"]) {
      const v = getShape(id)!.vertices;
      const angles = interiorAngles(v);
      for (const a of angles) expect(Math.abs(a - Math.round(a)), `${id} ${a}`).toBeLessThan(1e-9);
      expect(angles.reduce((s, a) => s + a, 0)).toBeCloseTo(angleSum(v.length), 9);
    }
    expect(interiorAngles(getShape("kite")!.vertices).map(Math.round)).toEqual([50, 100, 110, 100]);
    expect(interiorAngles(getShape("trapezoid")!.vertices).map(Math.round)).toEqual([60, 75, 105, 120]);
    expect(interiorAngles(getShape("obtuse")!.vertices).map(Math.round).sort((a, b) => a - b)).toEqual([25, 35, 120]);
    expect(interiorAngles(getShape("right")!.vertices).map(Math.round)).toEqual([90, 30, 60]);
  });

  it("marks equal sides", () => {
    expect(equalMarks(sideLengths(getShape("rectangle")!.vertices))).toEqual([1, 2, 1, 2]);
    expect(equalMarks(sideLengths(getShape("equilateral")!.vertices))).toEqual([1, 1, 1]);
    expect(equalMarks(sideLengths(getShape("scalene")!.vertices))).toEqual([0, 0, 0]);
    // The general trapezium is not secretly isosceles or partly equilateral: no two sides are equal.
    expect(equalMarks(sideLengths(getShape("trapezoid")!.vertices))).toEqual([0, 0, 0, 0]);
    expect(equalMarks(sideLengths(getShape("isosceles-trapezoid")!.vertices))).toEqual([0, 1, 0, 1]);
    expect(equalMarks(sideLengths(getShape("parallelogram")!.vertices))).toEqual([1, 2, 1, 2]);
    const kite = equalMarks(sideLengths(getShape("kite")!.vertices));
    expect(kite[0]).toBe(kite[3]);
    expect(kite[1]).toBe(kite[2]);
    expect(kite[0]).not.toBe(kite[1]);
  });

  it("counts diagonals and fan triangles", () => {
    for (let n = 3; n <= 12; n++) {
      expect(diagonals(n)).toHaveLength(diagonalCount(n));
      expect(fanTriangles(n)).toHaveLength(n - 2);
    }
    expect(diagonalCount(6)).toBe(9);
  });

  it("builds regular and convex irregular polygons with the right angle sum", () => {
    for (let n = 3; n <= 12; n++) {
      const reg = interiorAngles(regularPolygon(n));
      for (const a of reg) expect(a).toBeCloseTo(angleSum(n) / n, 9);
      for (const seed of [1, 2, 3]) {
        const irr = irregularPolygon(n, seed);
        const angles = interiorAngles(irr);
        for (const a of angles) expect(a).toBeLessThan(180);
        expect(angles.reduce((s, a) => s + a, 0)).toBeCloseTo(angleSum(n), 9);
      }
      expect(irregularPolygon(n, 5)).toEqual(irregularPolygon(n, 5));
    }
  });

  it("rounds angles honestly while keeping their exact sum", () => {
    const angles = interiorAngles(irregularPolygon(7, 3));
    const r = roundPreservingSum(angles, 1, 900);
    expect(r.reduce((s, a) => s + a, 0)).toBeCloseTo(900, 9);
    r.forEach((x, i) => expect(Math.abs(x - angles[i])).toBeLessThanOrEqual(0.1 + 1e-9));
    expect(formatAngle(60)).toBe("60°");
    expect(formatAngle(900 / 7)).toBe("≈128.6°");
  });

  it("resolves ids, aliases and bad input", () => {
    expect(getShape("trapezium")!.key).toBe("trapezoid");
    expect(getShape("regular-7")!.key).toBe("heptagon");
    expect(getShape("regular-11")!.regularN).toBe(11);
    expect(getShape("regular-4")!.key).toBe("square");
    expect(getShape("regular-13")).toBeNull();
    expect(getShape("blob")).toBeNull();
    expect(resolveGallery(["square", "nope", "square", "circle"]).map((s) => s.key)).toEqual(["square", "circle"]);
    expect(resolveGallery("square").length).toBeGreaterThan(10);
    expect(resolveGallery([])[0].key).toBe("equilateral");
  });

  it("fits shapes inside the box", () => {
    const { points } = fitToBox(getShape("kite")!.vertices, 360, 290, 50);
    for (const p of points) {
      expect(p.x).toBeGreaterThanOrEqual(50 - 1e-9);
      expect(p.x).toBeLessThanOrEqual(310 + 1e-9);
      expect(p.y).toBeGreaterThanOrEqual(50 - 1e-9);
      expect(p.y).toBeLessThanOrEqual(240 + 1e-9);
    }
  });
});

/* ------------------------------------------------------------------ grid */

describe("shape-grid", () => {
  it("measures the equal-area presets", () => {
    const shapes = AREA_12_PRESETS.map((rows) => cellsFromRows(rows, DRAW_W, DRAW_H));
    expect(shapes.map(area)).toEqual([12, 12, 12]);
    expect(shapes.map(perimeter)).toEqual([14, 16, 26]);
    expect(shapes.map(pieces)).toEqual([1, 1, 1]);
    for (const s of shapes) expect(boundaryEdges(s)).toHaveLength(perimeter(s));
  });
  it("counts holes and separate pieces in the perimeter", () => {
    const ring = cellsFromRows(["###", "#.#", "###"], 3, 3);
    expect(area(ring)).toBe(8);
    expect(perimeter(ring)).toBe(16);
    const two = cellsFromRows(["#.#"], 3, 1);
    expect(pieces(two)).toBe(2);
    expect(perimeter(two)).toBe(8);
    const diag = cellsFromRows(["#.", ".#"], 2, 2);
    expect(pieces(diag)).toBe(2);
  });
  it("matches the rectangle and triangle formulas", () => {
    for (let w = 1; w <= 12; w++)
      for (let h = 1; h <= 10; h++) {
        const c = cellsFromRows(Array.from({ length: h }, () => "#".repeat(w)), w, h);
        expect(area(c)).toBe(w * h);
        expect(perimeter(c)).toBe(rectPerimeter(w, h));
      }
    expect(triangleArea(5, 3)).toBe(7.5);
  });
});

/* ------------------------------------------------------------------ clock */

describe("shape-clock", () => {
  it("keeps the hands consistent", () => {
    expect(handAngles(toTime(3, 0))).toEqual({ minute: 0, hour: 90 });
    expect(handAngles(toTime(3, 30))).toEqual({ minute: 180, hour: 105 });
    expect(handAngles(toTime(15, 30))).toEqual({ minute: 180, hour: 105 });
    expect(handAngles(toTime(12, 0)).hour).toBe(0);
  });
  it("formats 12- and 24-hour time", () => {
    expect(format24(toTime(15, 5))).toBe("15:05");
    expect(format24(toTime(0, 0))).toBe("00:00");
    expect(parts12(toTime(0, 0))).toEqual({ h: 12, mm: "00", period: "am" });
    expect(parts12(toTime(12, 0))).toEqual({ h: 12, mm: "00", period: "pm" });
    expect(parts12(toTime(23, 59))).toEqual({ h: 11, mm: "59", period: "pm" });
    expect(format24(toTime(25, 0))).toBe("01:00");
    expect(format24(-1)).toBe("23:59");
  });
  it("carries the hour when the minute hand passes 12", () => {
    expect(minuteFromAngle(0)).toBe(0);
    expect(minuteFromAngle(359)).toBe(0);
    expect(minuteFromAngle(90)).toBe(15);
    expect(minuteFromAngle(-90)).toBe(45);
    expect(minuteHandDelta(toTime(3, 55), 5)).toBe(10);
    expect(setMinuteHand(toTime(3, 55), 5)).toBe(toTime(4, 5));
    expect(minuteHandDelta(toTime(4, 5), 55)).toBe(-10);
    expect(setMinuteHand(toTime(0, 5), 55)).toBe(toTime(23, 55));
    expect(hourHandDelta(toTime(3, 0), 105)).toBe(30);
    expect(hourHandDelta(toTime(11, 30), 15)).toBe(60);
  });
  it("says the time in words", () => {
    expect(timeWords(toTime(3, 0))).toEqual({ key: "oclock", vars: { h: 3 } });
    expect(timeWords(toTime(15, 15)).key).toBe("quarterPast");
    expect(timeWords(toTime(3, 30)).key).toBe("halfPast");
    expect(timeWords(toTime(3, 45))).toEqual({ key: "quarterTo", vars: { h: 4 } });
    expect(timeWords(toTime(12, 50))).toEqual({ key: "to", vars: { m: 10, h: 1 } });
    expect(timeWords(toTime(0, 20))).toEqual({ key: "past", vars: { m: 20, h: 12 } });
    expect(timeWords(toTime(6, 1)).key).toBe("minutePast");
    expect(timeWords(toTime(6, 59)).key).toBe("minuteTo");
  });
  it("splits elapsed time into count-on jumps", () => {
    expect(elapsedJumps(toTime(14, 45), 50)).toEqual([
      { from: toTime(14, 45), to: toTime(15, 0), minutes: 15 },
      { from: toTime(15, 0), to: toTime(15, 35), minutes: 35 },
    ]);
    expect(elapsedJumps(toTime(2, 0), 125).map((j) => j.minutes)).toEqual([120, 5]);
    expect(elapsedJumps(toTime(2, 50), 5).map((j) => j.minutes)).toEqual([5]);
    expect(elapsedJumps(toTime(23, 40), 100).map((j) => j.minutes)).toEqual([20, 60, 20]);
    expect(elapsedJumps(toTime(9, 0), 0)).toEqual([]);
    for (const [s, m] of [
      [0, 719],
      [37, 61],
      [601, 300],
    ])
      expect(elapsedJumps(s, m).reduce((a, j) => a + j.minutes, 0)).toBe(m);
    expect(splitDuration(95)).toEqual({ h: 1, m: 35 });
  });
});

/* ------------------------------------------------------------------ ruler */

describe("shape-ruler", () => {
  it("judges answers and names the classic mistakes", () => {
    expect(judge(7, 3, 7)).toBe("correct");
    expect(judge(10, 3, 7)).toBe("endReading");
    expect(judge(8, 0, 7)).toBe("countedMarks");
    expect(judge(8, 3, 7)).toBe("countedMarks");
    expect(judge(2, 3, 7)).toBe("wrong");
    expect(judge(NaN, 3, 7)).toBe("wrong");
  });
  it("keeps objects on the ruler", () => {
    for (const len of Object.values(OBJECTS)) {
      expect(clampStart(-4, len)).toBe(0);
      expect(clampStart(100, len)).toBe(RULER_CM - len);
      expect(clampStart(2.4, len)).toBe(2);
    }
  });
  it("describes non-standard measurements honestly", () => {
    expect(fitWords(15, 3)).toEqual({ key: "exactly", k: 5 });
    expect(fitWords(15, 5)).toEqual({ key: "exactly", k: 3 });
    expect(fitWords(15, 12)).toEqual({ key: "moreThan", k: 1 });
    expect(fitWords(15, 18)).toEqual({ key: "lessThanOne", k: 1 });
    expect(fitWords(7, 3)).toEqual({ key: "moreThan", k: 2 });
    expect(fitWords(8, 3)).toEqual({ key: "lessThan", k: 3 });
    expect(unitFit(9, 3)).toMatchObject({ whole: 3, exact: true });
  });
});

/* ------------------------------------------------------------------ patterns */

describe("shape-pattern", () => {
  it("parses symbols and cores", () => {
    expect(parseSymbol("triangle")).toEqual({ id: "triangle", shape: "triangle", colour: "blue" });
    expect(parseSymbol("triangle-red")).toEqual({ id: "triangle-red", shape: "triangle", colour: "red" });
    expect(parseSymbol("triangle-blue")!.id).toBe("triangle");
    expect(parseSymbol("blob")).toBeNull();
    expect(parseSymbol("circle-pink")).toBeNull();
    expect(parseSymbol(3)).toBeNull();
    expect(parseCore(["star", "nope", "heart"]).map((s) => s.id)).toEqual(["star", "heart"]);
    expect(parseCore("x").map((s) => s.id)).toEqual(["circle", "triangle", "square"]);
    expect(parseCore(Array(10).fill("star"))).toHaveLength(6);
  });
  it("finds item k with the remainder", () => {
    expect(repeatPosition(20, 3)).toEqual({ q: 6, r: 2, pos: 2 });
    expect(repeatPosition(12, 4)).toEqual({ q: 3, r: 0, pos: 4 });
    expect(repeatPosition(1, 5)).toEqual({ q: 0, r: 1, pos: 1 });
  });
  it("writes rules", () => {
    expect(formatRule(0, 2, 1)).toBe("2n + 1");
    expect(formatRule(1, 0, 0)).toBe("n²");
    expect(formatRule(1, 2, 1)).toBe("n² + 2n + 1");
    expect(formatRule(0, -1, 10)).toBe("−n + 10");
    expect(formatRule(2, -3, -1)).toBe("2n² − 3n − 1");
    expect(formatRule(0, 0, 3)).toBe("3");
    expect(formatRule(0, 0, 0)).toBe("0");
    expect(formatTerm(-1, "n")).toBe("−n");
    expect(differences([3, 5, 7, 9])).toEqual([2, 2, 2]);
    expect(clampCoefficients(9, -99, 50)).toEqual({ a: 3, b: -10, c: 20 });
  });
  it("draws exactly a·n² + b·n + c tiles", () => {
    for (const [a, b, c] of [
      [0, 2, 1],
      [1, 0, 0],
      [1, 1, 0],
      [2, 3, 4],
      [1, -1, 0],
      [1, 2, -1],
      [0, -1, 10],
      [-1, 6, 0],
      [0, 0, 5],
    ])
      for (let n = 1; n <= 6; n++) {
        const lay = growLayout(a, b, c, n);
        const term = growTerm(a, b, c, n);
        if (term < 0) expect(lay).toBeNull();
        else expect(lay!.tiles.filter((t) => !t.removed)).toHaveLength(term);
      }
    expect(growLayout(0, -2, 1, 1)).toBeNull();
  });
});

/* ------------------------------------------------------------------ stats */

describe("shape-stats", () => {
  it("computes mean, median and mode", () => {
    const xs = [3, 5, 5, 6, 8, 9, 9, 9, 12];
    expect(mean(xs)).toBeCloseTo(66 / 9, 12);
    expect(median(xs)).toBe(8);
    expect(medianInfo(xs).positions).toEqual([5]);
    expect(medianInfo([4, 1, 3, 2]).median).toBe(2.5);
    expect(medianInfo([4, 1, 3, 2]).positions).toEqual([2, 3]);
    expect(modes(xs)).toEqual({ values: [9], count: 3 });
    expect(modes([1, 1, 2, 2, 3]).values).toEqual([1, 2]);
    expect(modes([1, 2, 3]).values).toEqual([]);
    expect(modes([7]).values).toEqual([7]);
    expect(frequency([2, 1, 2])).toEqual([
      { value: 1, count: 1 },
      { value: 2, count: 2 },
    ]);
    expect(modalCategories([
      { label: "a", value: 3 },
      { label: "b", value: 5 },
      { label: "c", value: 5 },
    ])).toEqual(["b", "c"]);
    expect(modalCategories([{ label: "a", value: 0 }])).toEqual([]);
  });
  it("bins histograms with left-closed bins", () => {
    const xs = [3, 5, 5, 6, 8, 9, 9, 9, 12];
    const bins = histogram(xs, 2);
    expect(bins[0]).toEqual({ lo: 2, hi: 4, count: 1 });
    expect(bins.find((b) => b.lo === 8)!.count).toBe(4);
    expect(bins[bins.length - 1]).toEqual({ lo: 12, hi: 14, count: 1 });
    expect(bins.reduce((s, b) => s + b.count, 0)).toBe(xs.length);
    const dec = histogram([0.1, 0.2, 0.3, 0.7], 0.2);
    expect(dec.reduce((s, b) => s + b.count, 0)).toBe(4);
    expect(dec.map((b) => b.lo)).toEqual([0, 0.2, 0.4, 0.6]);
    const { options, preferred } = binWidthOptions(xs);
    expect(options).toContain(preferred);
    for (const w of options) expect(histogram(xs, w).length).toBeLessThanOrEqual(20);
  });
  it("makes tallies, ticks and pictograph keys", () => {
    expect(tally(13)).toEqual({ fives: 2, ones: 3 });
    expect(tally(0)).toEqual({ fives: 0, ones: 0 });
    expect(countTicks(7)).toEqual([0, 2, 4, 6, 8]);
    expect(countTicks(3)).toEqual([0, 1, 2, 3]);
    expect(niceStep(100, 5)).toBe(20);
    expect(pictographKeys(7).preferred).toBe(1);
    expect(pictographKeys(24).preferred).toBe(5);
    expect(pictographKeys(400).options).toEqual([10]);
  });
  it("parses data defensively", () => {
    expect(parseData([{ label: "Cats", value: 3 }, { label: "", value: 2 }, { label: "Dogs", value: -1 }, { label: "Fish", value: "4" }, null, "x"])).toEqual([
      { label: "Cats", value: 3 },
      { label: "Fish", value: 4 },
    ]);
    expect(parseData("nope")).toEqual([]);
    expect(parseValues([1, "2", "x", NaN, Infinity, 3.5])).toEqual([1, 2, 3.5]);
    expect(parseValues(Array(500).fill(1))).toHaveLength(120);
  });
  it("levels towers to the mean", () => {
    const fs = fairShare([3, 5, 2, 6, 7]);
    expect(fs.mean).toBeCloseTo(4.6, 12);
    expect(fs.received.reduce((s, x) => s + x, 0)).toBeCloseTo(fs.given.reduce((s, x) => s + x, 0), 12);
    expect(statText(66 / 9)).toEqual({ value: 7.33, approx: true });
    expect(statText(4.5)).toEqual({ value: 4.5, approx: false });
  });
});

/* ------------------------------------------------------------------ spinner */

describe("shape-spinner", () => {
  it("parses sectors and assigns distinct colours", () => {
    const s = parseSectors([{ label: "Win", weight: 1, color: "green" }, { label: "Lose", weight: 3 }, { label: "", weight: 2 }, { label: "Zero", weight: 0 }, "x"])!;
    expect(s.map((x) => x.label)).toEqual(["Win", "Lose"]);
    expect(s[0].colour).toBe("green");
    expect(s[1].colour).not.toBe("green");
    expect(parseSectors([])).toBeNull();
    expect(parseSectors("nope")).toBeNull();
    expect(parseSectors([{ label: "A" }])![0].weight).toBe(1);
  });
  it("finds the sector under the pointer", () => {
    const w = [1, 1, 2];
    expect(cumulative(w)).toEqual([0, 0.25, 0.5, 1]);
    expect(sectorAt(0, w)).toBe(0);
    expect(sectorAt(0.2499, w)).toBe(0);
    expect(sectorAt(0.25, w)).toBe(1);
    expect(sectorAt(0.75, w)).toBe(2);
    expect(sectorAt(0.999999, w)).toBe(2);
    expect(sectorFraction(w, 2)).toBe("1/2");
    expect(sectorFraction([1, 3], 0)).toBe("1/4");
    expect(sectorFraction([0.5, 1.5], 0)).toBeNull();
    expect(sectorPath(120, 120, 100, 0, 1)).toContain("A100 100");
    expect(sectorPath(120, 120, 100, 0, 0.25)).toMatch(/^M120 120 L/);
  });
  it("spins reproducibly, and many spins land close to the sector fractions", () => {
    const w = DEFAULT_SECTORS.map((s) => s.weight);
    const a = spinMany(seedFrom(1), 50, w);
    const b = spinMany(seedFrom(1), 50, w);
    expect(a).toEqual(b);
    const big = spinMany(seedFrom(7), 20000, w);
    const counts = [0, 0, 0];
    for (const o of big.outcomes) counts[o]++;
    expect(counts[0] / 20000).toBeCloseTo(0.25, 1);
    expect(counts[2] / 20000).toBeCloseTo(0.5, 1);
  });
});

/* ------------------------------------------------------------------ smoke renders */

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function render(C: ComponentType<any>, props: Record<string, unknown> = {}, locale: "en" | "ar" = "en") {
  const messages = locale === "en" ? en : { ...en, ...ar, w: { ...en.w, ...ar.w } };
  return renderToString(createElement(I18nProvider, { locale, messages: messages as typeof en, children: createElement(C, props) }));
}

const UNRESOLVED = /w\.(shapes|area|clock2|ruler|pattern|data|spinner)\./;

describe("shape-data widgets render on the server", () => {
  it("registers all seven tags", () => {
    expect(Object.keys(SHAPE_DATA_WIDGETS).sort()).toEqual(["AnalogClock", "AreaGrid", "DataChart", "PatternMaker", "RulerMeasure", "ShapeExplorer", "Spinner"]);
  });

  const cases: [string, ComponentType<Record<string, unknown>>, Record<string, unknown>[]][] = [
    [
      "ShapeExplorer",
      ShapeExplorer as ComponentType<Record<string, unknown>>,
      [
        {},
        { shapes: ["square", "kite", "regular-7", "bogus", "circle"], show: ["symmetry", "angles", "rotation", "diagonals", "sides", "vertices"] },
        { shapes: ["circle"], show: ["sides", "vertices", "angles", "symmetry", "rotation", "diagonals"] },
        { mode: "polygon", n: 9, title: "Angle sums" },
        { mode: "polygon", n: "x", shapes: "nope", show: 5 },
      ],
    ],
    [
      "AreaGrid",
      AreaGrid as ComponentType<Record<string, unknown>>,
      [{}, { mode: "draw" }, { mode: "split", width: 7, height: 3, split: 4 }, { mode: "triangle", width: 5, height: 3 }, { mode: "rectangle", width: 99, height: -3, unit: "cm" }, { modes: ["split"], width: "x" }],
    ],
    [
      "AnalogClock",
      AnalogClock as ComponentType<Record<string, unknown>>,
      [{}, { hours: 14, minutes: 45, mode: "elapsed", elapsed: 50, step: 15 }, { hours: "x", minutes: 999, step: 0, digital: false, mode: "zzz" }],
    ],
    [
      "RulerMeasure",
      RulerMeasure as ComponentType<Record<string, unknown>>,
      [{}, { units: "both", object: "leaf", start: 4 }, { units: "clips", object: "pencil" }, { object: "rocket", objects: ["key", "pencil", "x"], start: 99 }],
    ],
    [
      "PatternMaker",
      PatternMaker as ComponentType<Record<string, unknown>>,
      [{}, { core: ["star", "heart-blue", "star", "bogus"], steps: 10 }, { mode: "grow", a: 1, b: 0, c: 0, steps: 4 }, { mode: "grow", a: 0, b: -1, c: 3 }, { mode: "grow", a: 0, b: -2, c: 1 }, { mode: "grow", a: 3, b: 10, c: 20, steps: 6 }, { core: "x", a: "y" }],
    ],
    [
      "DataChart",
      DataChart as ComponentType<Record<string, unknown>>,
      [
        {},
        { data: [{ label: "Cats", value: 5 }, { label: "Dogs", value: 7 }, { label: "Fish", value: 2 }, { bad: 1 }], view: "pictograph", per: 2, showMean: true, showMedian: true, showMode: true },
        { values: [3, 5, 5, 6, 8, 9, 9, 9, 12], view: "histogram", binWidth: 2, showMean: true, showMedian: true, showMode: true, unit: "cm" },
        { values: [2, 4, 6, 3], view: "fair", showMean: true },
        { values: [1.5, 2.25, 2.25, 3.75], view: "dot", showMode: true, showMedian: true },
        { data: "nonsense", values: "x", view: "nope" },
        { data: [{ label: "A", value: 2.5 }, { label: "B", value: 1 }], view: "tally" },
      ],
    ],
    [
      "Spinner",
      Spinner as ComponentType<Record<string, unknown>>,
      [{}, { sectors: [{ label: "Win", weight: 1, color: "green" }, { label: "Lose", weight: 3 }], spins: 100 }, { sectors: [], spins: -5 }, { sectors: [{ label: "A", weight: 0.5 }, { label: "B", weight: 1.5 }], seed: 42 }, { sectors: [{ label: "Only", weight: 1 }] }],
    ],
  ];

  for (const [name, C, propsList] of cases) {
    it(`${name}: default and example props, in English and Arabic`, () => {
      for (const props of propsList) {
        const html = render(C, props);
        expect(html.length, JSON.stringify(props)).toBeGreaterThan(200);
        expect(html, JSON.stringify(props)).not.toMatch(UNRESOLVED);
        expect(html).not.toContain("NaN");
      }
      expect(render(C, propsList[1], "ar")).not.toMatch(UNRESOLVED);
    });
  }

  it("DataChart renders every view it offers", () => {
    for (const view of ["tally", "pictograph", "bar", "dot", "fair"]) {
      const html = render(DataChart as ComponentType<Record<string, unknown>>, { view, showMean: true, showMedian: true, showMode: true });
      expect(html).not.toMatch(UNRESOLVED);
      expect(html).toContain('aria-pressed="true"');
    }
    for (const view of ["dot", "histogram", "tally", "fair"]) {
      const html = render(DataChart as ComponentType<Record<string, unknown>>, { values: [1, 2, 2, 3, 5, 8], view, showMean: true, showMedian: true, showMode: true });
      expect(html).not.toMatch(UNRESOLVED);
    }
  });

  it("uses the author's title and English text overrides", () => {
    expect(render(Spinner as ComponentType<Record<string, unknown>>, { title: "Fair game?", subtitle: "Spin it." })).toContain("Fair game?");
    expect(render(ShapeExplorer as ComponentType<Record<string, unknown>>, { title: "Quadrilaterals" })).toContain("Quadrilaterals");
  });
});

describe("docs/widgets/shape-data.md", () => {
  const doc = read("docs/widgets/shape-data.md");
  const blocks = [...doc.matchAll(/```mdx\n([\s\S]*?)```/g)].map((m) => m[1]);
  it("has copy-pasteable examples for every widget", () => {
    for (const tag of Object.keys(SHAPE_DATA_WIDGETS)) {
      const n = blocks.join("\n").split(`<${tag}`).length - 1;
      expect(n, tag).toBeGreaterThanOrEqual(2);
    }
  });
  it("examples compile as MDX and render with the registered widgets", async () => {
    for (const block of blocks) {
      for (const example of block.split("\n\n").map((x) => x.trim()).filter(Boolean)) {
        const { default: Content } = await evaluate(example, { ...runtime, development: false });
        const html = renderToString(createElement(I18nProvider, { locale: "en", messages: en, children: createElement(Content, { components: SHAPE_DATA_WIDGETS }) }));
        expect(html, example).not.toMatch(UNRESOLVED);
        expect(html.length, example).toBeGreaterThan(200);
      }
    }
  });
});
