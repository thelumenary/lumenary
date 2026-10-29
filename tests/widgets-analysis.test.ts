import { describe, expect, it } from "vitest";
import { createElement, type ComponentType } from "react";
import { renderToString } from "react-dom/server";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import { compileExpr, evalExpr, isValidName, prettyExpr, stripLhs, toNumber, toParams, toRange } from "@/components/widgets/lib/expr";
import { autoRange, clipPolylines, fitEqualAspect, fmt, integrate, looksLikePiRange, niceStep, niceTicks, pathD, piLabel, piTicks, sampleFunction, sampleParametric, type Pt } from "@/components/widgets/lib/plot-core";
import { FunctionPlot, parseCurves, parsePoints } from "@/components/widgets/FunctionPlot";
import { MatrixTransform } from "@/components/widgets/MatrixTransform";
import { apply, det, eigen, equalM, IDENTITY, mul, orientationArc, presetMatrix, rotationAngle, toMatrix, toPresetList, trace, type Mat2 } from "@/components/widgets/lib/plot-matrix";
import { SequenceLab, resolveSeqModes } from "@/components/widgets/SequenceLab";
import {
  EULER_GAMMA,
  GIBBS_FRACTION,
  classifyOrbit,
  epsilonIndex,
  fixedPoints,
  fourierPartial,
  gibbsOvershoot,
  harmonicNumber,
  iterate,
  looksHarmonic,
  maxFourierError,
  partialSums,
  sequenceTerms,
  termsDoNotVanish,
  waveValue,
} from "@/components/widgets/lib/plot-seq";
import { ComplexPlane } from "@/components/widgets/ComplexPlane";
import * as cx from "@/components/widgets/lib/plot-complex";
import { CalculusLab, calcModes } from "@/components/widgets/CalculusLab";
import {
  TAYLOR,
  checkDelta,
  derivativeAt,
  differenceQuotient,
  inConvergence,
  largestDelta,
  logSliderPosition,
  logSliderValue,
  riemannSum,
  taylorCoefficient,
  taylorFormula,
  taylorPolynomial,
} from "@/components/widgets/lib/plot-calc";
import { VectorField, analyseSystem, parseStartPoints, resolveModes } from "@/components/widgets/VectorField";
import * as vf from "@/components/widgets/lib/plot-field";
import { evaluate } from "@mdx-js/mdx";
import * as runtime from "react/jsx-runtime";
import { ANALYSIS_WIDGETS } from "@/components/widgets/registry-analysis";
import { read } from "./helpers";
// @@imports (one block per widget; keep this marker)

/* ---------------------------------------------------------------------------
 * Helpers
 * ------------------------------------------------------------------------- */

const ev = (src: string, vars: Record<string, number> = {}, allowed = Object.keys(vars)) => {
  const r = compileExpr(src, allowed);
  if (!r.ok) throw new Error(`${src}: ${r.error.code} at ${r.error.pos}`);
  return r.fn(vars);
};
const err = (src: string, allowed: string[] = ["x"]) => {
  const r = compileExpr(src, allowed);
  if (r.ok) throw new Error(`${src} should not compile`);
  return r.error;
};

/** Server-render a widget inside the English i18n provider. */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function render(C: ComponentType<any>, props: Record<string, unknown> = {}) {
  return renderToString(createElement(I18nProvider, { locale: "en", messages: en, children: createElement(C, props) }));
}

/* ---------------------------------------------------------------------------
 * lib/expr.ts
 * ------------------------------------------------------------------------- */

describe("expr: numbers and precedence", () => {
  it("reads integers, decimals and scientific notation", () => {
    expect(ev("42")).toBe(42);
    expect(ev("3.25")).toBe(3.25);
    expect(ev(".5")).toBe(0.5);
    expect(ev("1e3")).toBe(1000);
    expect(ev("2.5E-2")).toBeCloseTo(0.025, 15);
    expect(ev("6.02e+23")).toBeCloseTo(6.02e23, -10);
  });
  it("respects + - * / precedence and left associativity", () => {
    expect(ev("1 + 2 * 3")).toBe(7);
    expect(ev("(1 + 2) * 3")).toBe(9);
    expect(ev("10 - 4 - 3")).toBe(3);
    expect(ev("24 / 4 / 3")).toBe(2);
    expect(ev("2 * 3 / 4")).toBe(1.5);
  });
  it("makes ^ right-associative and tighter than unary minus", () => {
    expect(ev("2^3^2")).toBe(512);
    expect(ev("-x^2", { x: 3 })).toBe(-9);
    expect(ev("(-x)^2", { x: 3 })).toBe(9);
    expect(ev("2^-1")).toBe(0.5);
    expect(ev("-2^2")).toBe(-4);
    expect(ev("2*-3")).toBe(-6);
    expect(ev("--2")).toBe(2);
    expect(ev("+2")).toBe(2);
    expect(ev("2**3")).toBe(8);
  });
  it("supports factorial as a postfix operator", () => {
    expect(ev("5!")).toBe(120);
    expect(ev("0!")).toBe(1);
    expect(ev("-3!")).toBe(-6);
    expect(ev("2^3!")).toBe(64);
    expect(ev("n!/(n-2)!", { n: 6 })).toBe(30);
    expect(Number.isNaN(ev("2.5!"))).toBe(true);
    expect(Number.isNaN(ev("(-1)!"))).toBe(true);
  });
  it("accepts typographic operators", () => {
    expect(ev("6 × 7")).toBe(42);
    expect(ev("6 · 7")).toBe(42);
    expect(ev("8 ÷ 2")).toBe(4);
    expect(ev("5 − 7")).toBe(-2);
  });
});

describe("expr: names, constants and functions", () => {
  it("knows pi, π, tau and e", () => {
    expect(ev("pi")).toBe(Math.PI);
    expect(ev("π/2")).toBe(Math.PI / 2);
    expect(ev("tau")).toBe(2 * Math.PI);
    expect(ev("e")).toBe(Math.E);
    expect(ev("e^1")).toBe(Math.E);
  });
  it("evaluates every listed function", () => {
    const x = 0.3;
    const cases: [string, number][] = [
      ["sin(x)", Math.sin(x)],
      ["cos(x)", Math.cos(x)],
      ["tan(x)", Math.tan(x)],
      ["asin(x)", Math.asin(x)],
      ["acos(x)", Math.acos(x)],
      ["atan(x)", Math.atan(x)],
      ["sinh(x)", Math.sinh(x)],
      ["cosh(x)", Math.cosh(x)],
      ["tanh(x)", Math.tanh(x)],
      ["exp(x)", Math.exp(x)],
      ["ln(x)", Math.log(x)],
      ["log(x)", Math.log(x)],
      ["log10(x)", Math.log10(x)],
      ["sqrt(x)", Math.sqrt(x)],
      ["abs(-x)", x],
      ["floor(x + 2)", 2],
      ["ceil(x)", 1],
      ["sign(-x)", -1],
      ["min(x, 0.1)", 0.1],
      ["max(x, 0.1)", x],
      ["sec(x)", 1 / Math.cos(x)],
      ["cbrt(-8)", -2],
      ["atan2(1, 1)", Math.PI / 4],
      ["mod(-1, 3)", 2],
    ];
    for (const [src, want] of cases) expect(ev(src, { x }), src).toBeCloseTo(want, 12);
    expect(ev("sign(0)")).toBe(0);
  });
  it("returns NaN outside a real domain instead of throwing", () => {
    expect(Number.isNaN(ev("sqrt(-1)"))).toBe(true);
    expect(Number.isNaN(ev("ln(-1)"))).toBe(true);
    expect(Number.isNaN(ev("(-8)^(1/3)"))).toBe(true);
    expect(ev("1/0")).toBe(Infinity);
  });
  it("binds allowed variables and parameters and reports which were used", () => {
    const r = compileExpr("a*x^2 + b", ["x", "a", "b", "c"]);
    expect(r.ok).toBe(true);
    if (r.ok) {
      expect(r.fn({ x: 2, a: 3, b: 1 })).toBe(13);
      expect(r.vars.sort()).toEqual(["a", "b", "x"]);
      expect(Number.isNaN(r.fn({ x: 2 }))).toBe(true);
    }
  });
  it("lets a variable shadow a constant only when explicitly allowed", () => {
    expect(ev("e + 1", { e: 1 })).toBe(2);
    expect(ev("e + 1", {}, [])).toBeCloseTo(Math.E + 1, 12);
  });
  it("evaluates nested and composite expressions", () => {
    expect(ev("sin(pi/6)^2 + cos(pi/6)^2")).toBeCloseTo(1, 14);
    expect(ev("exp(ln(5))")).toBeCloseTo(5, 13);
    expect(ev("max(min(3, 7), 2)")).toBe(3);
    expect(ev("(-1)^(n+1)/n", { n: 4 })).toBe(-0.25);
    expect(ev("r*x*(1-x)", { r: 4, x: 0.5 })).toBe(1);
  });
});

describe("expr: friendly errors with positions", () => {
  it("rejects empty input", () => expect(err("   ").code).toBe("empty"));
  it("asks for explicit multiplication", () => {
    expect(err("2x")).toMatchObject({ code: "implicitMul", pos: 1 });
    expect(err("x(x+1)")).toMatchObject({ code: "implicitMul", pos: 1 });
    expect(err("(x+1)(x-1)")).toMatchObject({ code: "implicitMul", pos: 5 });
    expect(err("2pi")).toMatchObject({ code: "implicitMul", pos: 1 });
    expect(err("xy", ["x", "y"])).toMatchObject({ code: "implicitMul", pos: 1 });
    expect(err("2 3")).toMatchObject({ code: "implicitMul", pos: 2 });
  });
  it("names unknown variables and lists the allowed ones", () => {
    const e = err("x + q");
    expect(e).toMatchObject({ code: "unknownName", pos: 4 });
    expect(e.params).toMatchObject({ name: "q", allowed: "x, pi, e" });
  });
  it("requires parentheses after functions and the right number of inputs", () => {
    expect(err("sin x")).toMatchObject({ code: "needParen", pos: 0 });
    expect(err("sin(1, 2)")).toMatchObject({ code: "arity", params: { name: "sin", count: 1 } });
    expect(err("max(1)")).toMatchObject({ code: "arity", params: { name: "max", count: 2 } });
    expect(err("sin()")).toMatchObject({ code: "arity" });
    expect(err("pi(2)")).toMatchObject({ code: "notFunction" });
  });
  it("finds unbalanced parentheses and dangling operators", () => {
    expect(err("(x + 1")).toMatchObject({ code: "missingClose", pos: 0 });
    expect(err("sin(x")).toMatchObject({ code: "missingClose", pos: 3 });
    expect(err("x + 1)")).toMatchObject({ code: "unexpected", pos: 5 });
    expect(err("x +")).toMatchObject({ code: "unexpectedEnd", pos: 3 });
    expect(err("x ^")).toMatchObject({ code: "unexpectedEnd" });
    expect(err("* x")).toMatchObject({ code: "unexpected", pos: 0 });
    expect(err("()")).toMatchObject({ code: "unexpected" });
  });
  it("rejects stray characters and malformed numbers", () => {
    expect(err("x $ 2")).toMatchObject({ code: "badChar", pos: 2, params: { char: "$" } });
    expect(err("1.2.3")).toMatchObject({ code: "badNumber", pos: 0 });
    expect(err("x = 2")).toMatchObject({ code: "badChar" });
  });
  it("cannot be abused: no property access, no huge inputs, no deep nesting", () => {
    expect(err("constructor", [])).toMatchObject({ code: "unknownName" });
    expect(err("toString(1)", [])).toMatchObject({ code: "unknownName" });
    expect(err("__proto__", [])).toMatchObject({ code: "unknownName" });
    expect(err("x".repeat(700)).code).toBe("tooLong");
    expect(err("(".repeat(100) + "1" + ")".repeat(100)).code).toBe("tooDeep");
    expect(compileExpr(undefined).ok).toBe(false);
    expect(compileExpr({ evil: true }).ok).toBe(false);
  });
});

describe("expr: prop helpers", () => {
  it("strips a left-hand side", () => {
    expect(stripLhs("y = x^2")).toBe(" x^2");
    expect(stripLhs("f(x) = sin(x)")).toBe(" sin(x)");
    expect(stripLhs("r = 1 + cos(t)")).toBe(" 1 + cos(t)");
    expect(stripLhs("dy/dx = x - y")).toBe(" x - y");
    expect(stripLhs("x' = -y")).toBe(" -y");
    expect(stripLhs("x^2 + 1")).toBe("x^2 + 1");
  });
  it("prettifies expressions for display", () => {
    expect(prettyExpr("a*x^2 - 2*pi")).toBe("a·x² − 2·π");
    expect(prettyExpr("x^(1/2) + 2^10")).toBe("x^(1/2) + 2¹⁰");
    expect(prettyExpr("r = 1 + cos(theta)")).toBe("r = 1 + cos(θ)");
  });
  it("reads numbers or constant expressions, with fallbacks", () => {
    expect(toNumber(2, 0)).toBe(2);
    expect(toNumber("pi/2", 0)).toBe(Math.PI / 2);
    expect(toNumber("nonsense", 7)).toBe(7);
    expect(toNumber(NaN, 7)).toBe(7);
    expect(toNumber(null, 7)).toBe(7);
    expect(evalExpr("a + 1", { a: 2 })).toBe(3);
  });
  it("reads windows, swapping reversed bounds and widening empty ones", () => {
    expect(toRange([-1, 1], [0, 1])).toEqual([-1, 1]);
    expect(toRange(["-pi", "pi"], [0, 1])).toEqual([-Math.PI, Math.PI]);
    expect(toRange([3, -3], [0, 1])).toEqual([-3, 3]);
    expect(toRange("bad", [0, 1])).toEqual([0, 1]);
    expect(toRange([1], [0, 1])).toEqual([0, 1]);
    const r = toRange([2, 2], [0, 1]);
    expect(r[0]).toBeLessThan(2);
    expect(r[1]).toBeGreaterThan(2);
  });
  it("validates parameter specs", () => {
    const ps = toParams([
      { name: "a", min: -3, max: 3, step: 0.1, value: 1 },
      { name: "b", min: 5, max: 1, value: 99 },
      { name: "sin", min: 0, max: 1 },
      { name: "x", min: 0, max: 1 },
      { name: "a", min: 0, max: 1 },
      "junk",
      { name: "2bad" },
    ], ["x"]);
    expect(ps.map((p) => p.name)).toEqual(["a", "b"]);
    expect(ps[1]).toMatchObject({ min: 1, max: 5, value: 5 });
    expect(isValidName("theta")).toBe(true);
    expect(isValidName("pi")).toBe(false);
    expect(toParams("nope")).toEqual([]);
  });
});

/* ---------------------------------------------------------------------------
 * lib/plot-core.ts
 * ------------------------------------------------------------------------- */

describe("plot-core: ticks and formatting", () => {
  it("chooses 1-2-5 steps", () => {
    expect(niceStep(10, 10)).toBe(1);
    expect(niceStep(10, 5)).toBe(2);
    expect(niceStep(1, 4)).toBe(0.2);
    expect(niceStep(100, 4)).toBe(20);
    expect(niceStep(7, 8)).toBe(1);
  });
  it("produces exact tick values and clean labels", () => {
    const t = niceTicks(-1, 1, 10);
    expect(t.step).toBeCloseTo(0.2, 12);
    expect(t.values).toContain(0.6);
    expect(t.labels).toContain("−0.4");
    expect(t.labels).toContain("0");
    expect(t.labels).not.toContain("-0");
    expect(niceTicks(0, 10, 5).values).toEqual([0, 2, 4, 6, 8, 10]);
  });
  it("labels multiples of π", () => {
    expect(piLabel(1, 2)).toBe("π/2");
    expect(piLabel(-3, 4)).toBe("−3π/4");
    expect(piLabel(2, 1)).toBe("2π");
    expect(piLabel(2, 4)).toBe("π/2");
    expect(piLabel(0, 3)).toBe("0");
    const t = piTicks(-2 * Math.PI, 2 * Math.PI, 8);
    expect(t.labels).toEqual(["−2π", "−3π/2", "−π", "−π/2", "0", "π/2", "π", "3π/2", "2π"]);
    expect(looksLikePiRange(-2 * Math.PI, 2 * Math.PI)).toBe(true);
    expect(looksLikePiRange(0, Math.PI)).toBe(true);
    expect(looksLikePiRange(-5, 5)).toBe(false);
    expect(looksLikePiRange(0, 4)).toBe(false);
  });
  it("formats numbers compactly with a true minus sign", () => {
    expect(fmt(2)).toBe("2");
    expect(fmt(-0.5)).toBe("−0.5");
    expect(fmt(1 / 3)).toBe("0.333");
    expect(fmt(2.5, 0)).toBe("3");
    expect(fmt(-0.0001)).toBe("−1×10⁻⁴");
    expect(fmt(1.5e7)).toBe("1.5×10⁷");
    expect(fmt(Math.sin(Math.PI))).toBe("0");
    expect(fmt(-1e-20)).toBe("0");
    expect(fmt(Infinity)).toBe("∞");
  });
});

describe("plot-core: windows", () => {
  it("expands one axis for equal aspect", () => {
    const r = fitEqualAspect([-1, 1], [-1, 1], 400, 200);
    expect(r.y).toEqual([-1, 1]);
    expect(r.x[1] - r.x[0]).toBeCloseTo(4, 12);
  });
  it("finds a robust automatic window that ignores poles", () => {
    const xs = Array.from({ length: 401 }, (_, i) => -2 + i / 100);
    const r = autoRange(xs.map((x) => x * x));
    expect(r[0]).toBeLessThanOrEqual(0);
    expect(r[1]).toBeGreaterThanOrEqual(4);
    const tan = autoRange(xs.map((x) => Math.tan(x)), [-5, 5]);
    expect(tan[1] - tan[0]).toBeLessThan(200);
    expect(autoRange([], [-2, 2])).toEqual([-2, 2]);
    const flat = autoRange([3, 3, 3]);
    expect(flat[0]).toBeLessThan(3);
    expect(flat[1]).toBeGreaterThan(3);
  });
});

describe("plot-core: sampling", () => {
  const maxVerticalJump = (lines: Pt[][]) => Math.max(0, ...lines.flatMap((l) => l.slice(1).map((p, i) => Math.abs(p[1] - l[i][1]))));
  it("draws a continuous function as one piece", () => {
    const lines = sampleFunction(Math.sin, [-Math.PI, Math.PI], { y: [-1.5, 1.5] });
    expect(lines).toHaveLength(1);
    expect(lines[0].length).toBeGreaterThan(500);
  });
  it("breaks tan(x) at its poles instead of drawing vertical lines", () => {
    const lines = sampleFunction(Math.tan, [-5, 5], { y: [-4, 4] });
    // Poles at ±π/2 and ±3π/2 give five branches.
    expect(lines.length).toBe(5);
    expect(maxVerticalJump(lines)).toBeLessThan(4);
    for (const l of lines) for (const p of l) expect(Math.abs(p[1])).toBeLessThanOrEqual(12 + 1e-9);
  });
  it("breaks at jump discontinuities (floor, sign) and keeps one-sided limits", () => {
    const lines = sampleFunction(Math.floor, [-2.5, 2.5], { y: [-4, 4] });
    expect(lines.length).toBe(6);
    expect(maxVerticalJump(lines)).toBeLessThan(0.05);
    const sgn = sampleFunction((x) => Math.sign(x), [-1, 1], { y: [-2, 2] });
    expect(sgn.length).toBeGreaterThanOrEqual(2);
  });
  it("does not break steep but continuous functions", () => {
    const lines = sampleFunction((x) => Math.atan(200 * x), [-1, 1], { y: [-2, 2] });
    expect(lines).toHaveLength(1);
    const cube = sampleFunction((x) => x ** 3, [-10, 10], { y: [-5, 5] });
    expect(cube).toHaveLength(1);
  });
  it("finds the edge of the domain (sqrt starts at 0, ln stays clipped)", () => {
    const lines = sampleFunction(Math.sqrt, [-1, 4], { y: [-1, 3] });
    expect(lines).toHaveLength(1);
    expect(lines[0][0][0]).toBeLessThan(1e-6);
    expect(lines[0][0][0]).toBeGreaterThanOrEqual(0);
    const ln = sampleFunction(Math.log, [-1, 4], { y: [-3, 3] });
    expect(ln).toHaveLength(1);
    expect(Math.min(...ln[0].map((p) => p[1]))).toBeGreaterThanOrEqual(-9 - 1e-9);
  });
  it("handles 1/x (exact pole at a sample) and undefined functions", () => {
    expect(sampleFunction((x) => 1 / x, [-2, 2], { y: [-5, 5] })).toHaveLength(2);
    expect(sampleFunction(() => NaN, [-2, 2], { y: [-5, 5] })).toHaveLength(0);
  });
  it("samples parametric curves, closing a circle and breaking at jumps", () => {
    const circle = sampleParametric(Math.cos, Math.sin, [0, 2 * Math.PI], { x: [-2, 2], y: [-2, 2] });
    expect(circle).toHaveLength(1);
    const first = circle[0][0];
    const last = circle[0][circle[0].length - 1];
    expect(Math.hypot(first[0] - last[0], first[1] - last[1])).toBeLessThan(1e-9);
    const jumpy = sampleParametric((t) => t, (t) => (t < 0 ? -1 : 1), [-1, 1], { x: [-2, 2], y: [-2, 2] });
    expect(jumpy.length).toBe(2);
  });
  it("clips polylines to a box", () => {
    const out = clipPolylines([[[0, 0], [10, 0]]], { x: [2, 5], y: [-1, 1] });
    expect(out).toEqual([[[2, 0], [5, 0]]]);
    const cross = clipPolylines([[[-2, 0], [0, 5], [2, 0]]], { x: [-3, 3], y: [-1, 1] });
    expect(cross).toHaveLength(2);
  });
  it("writes SVG path data", () => {
    expect(pathD([[[0, 0], [1, 1]]], (v) => v * 10, (v) => -v * 10)).toBe("M0.00 0.00L10.00 -10.00");
  });
});

describe("plot-core: integration", () => {
  it("integrates smooth functions accurately", () => {
    expect(integrate(Math.sin, 0, Math.PI)).toBeCloseTo(2, 9);
    expect(integrate((x) => x * x, 0, 3)).toBeCloseTo(9, 9);
    expect(integrate(Math.exp, 0, 1)).toBeCloseTo(Math.E - 1, 9);
    expect(integrate((x) => 1 / (1 + x * x), -1, 1)).toBeCloseTo(Math.PI / 2, 9);
    expect(integrate(Math.sin, Math.PI, 0)).toBeCloseTo(-2, 9);
  });
  it("returns NaN when the integrand is undefined", () => {
    expect(Number.isNaN(integrate(Math.log, -1, 1))).toBe(true);
  });
});

/* ---------------------------------------------------------------------------
 * FunctionPlot
 * ------------------------------------------------------------------------- */

describe("FunctionPlot", () => {
  it("parses curves for each mode", () => {
    expect(parseCurves(["x^2", "y = sin(x)"], "graph", [])).toHaveLength(2);
    const par = parseCurves([["cos(t)", "sin(t)"]], "parametric", []);
    expect(par).toHaveLength(1);
    expect(par[0].ok).toBe(true);
    expect(parseCurves(["cos(t)", "sin(t)", "t", "t^2"], "parametric", [])).toHaveLength(2);
    const polar = parseCurves(["r = 1 + cos(theta)"], "polar", []);
    expect(polar[0].ok).toBe(true);
    expect(parseCurves("x^3", "graph", [])).toHaveLength(1);
    expect(parseCurves(["2x"], "graph", [])[0].ok).toBe(false);
    expect(parseCurves([42, null, {}], "graph", []).length).toBeLessThanOrEqual(3);
  });
  it("parses points, including expressions in parameters", () => {
    const pts = parsePoints([[1, 2], ["a", "a^2", "P"], { x: 0, y: 1, label: "Q" }, "junk", [1]], ["a"]);
    expect(pts).toHaveLength(3);
    expect(pts[1].x({ a: 2 })).toBe(2);
    expect(pts[1].y({ a: 2 })).toBe(4);
    expect(pts[1].label).toBe("P");
  });
  it("server-renders with defaults and with representative props", () => {
    expect(render(FunctionPlot)).toContain("<svg");
    const html = render(FunctionPlot, {
      fns: ["a*sin(x)", "x^2/4"],
      x: ["-2*pi", "2*pi"],
      params: [{ name: "a", min: -3, max: 3, step: 0.1, value: 1 }],
      points: [[0, 0]],
      shade: 0,
      labels: ["a sin x", "x²/4"],
    });
    expect(html).toContain("<svg");
    expect(render(FunctionPlot, { mode: "parametric", fns: [["cos(3*t)", "sin(2*t)"]], t: [0, "2*pi"] })).toContain("<svg");
    expect(render(FunctionPlot, { mode: "polar", fns: ["1 + cos(t)"], aspect: "equal" })).toContain("<svg");
    expect(render(FunctionPlot, { fns: ["2x", "tan(x)"], x: "bad", params: "bad", points: 5, shade: 9 })).toContain("<svg");
  });
});

/* ---------------------------------------------------------------------------
 * MatrixTransform
 * ------------------------------------------------------------------------- */

describe("MatrixTransform", () => {
  const close = (A: Mat2, B: Mat2) => expect(equalM(A, B, 1e-9), `${JSON.stringify(A)} vs ${JSON.stringify(B)}`).toBe(true);
  it("reads matrix props in several forms, with fallbacks and clamping", () => {
    expect(toMatrix([[1, 2], [3, 4]], IDENTITY)).toEqual([[1, 2], [3, 4]]);
    expect(toMatrix([1, 2, 3, 4], IDENTITY)).toEqual([[1, 2], [3, 4]]);
    close(toMatrix([["cos(pi/3)", "-sin(pi/3)"], ["sin(pi/3)", "cos(pi/3)"]], IDENTITY), presetMatrix("rotation", { theta: 60 }));
    expect(toMatrix("nope", IDENTITY)).toEqual(IDENTITY);
    expect(toMatrix([[1, "x"], [0, 1]], IDENTITY)).toEqual(IDENTITY);
    expect(toMatrix([[1e9, 0], [0, 1]], IDENTITY)[0][0]).toBe(100);
  });
  it("multiplies in the right order and composes linear maps", () => {
    const A: Mat2 = [[0, -1], [1, 0]];
    const B: Mat2 = [[1, 0], [0, -1]];
    expect(mul(B, A)).toEqual([[0, -1], [-1, 0]]);
    expect(mul(A, B)).toEqual([[0, 1], [1, 0]]);
    const v: [number, number] = [2, 3];
    expect(apply(mul(B, A), v)).toEqual(apply(B, apply(A, v)));
    expect(det(mul(A, B))).toBeCloseTo(det(A) * det(B), 12);
    expect(trace([[2, 7], [1, 3]])).toBe(5);
  });
  it("finds two real eigenvalues with their directions", () => {
    const e = eigen([[1, 1], [0.5, 1.5]]);
    expect(e.kind).toBe("distinct");
    if (e.kind === "distinct") {
      expect(e.values[0]).toBeCloseTo(2, 12);
      expect(e.values[1]).toBeCloseTo(0.5, 12);
      expect(e.vectors[0][0]).toBeCloseTo(1, 12);
      expect(e.vectors[0][1]).toBeCloseTo(1, 12);
      expect(e.vectors[1][0]).toBeCloseTo(1, 12);
      expect(e.vectors[1][1]).toBeCloseTo(-0.5, 12);
    }
    const diag = eigen([[3, 0], [0, -2]]);
    expect(diag).toEqual({ kind: "distinct", values: [3, -2], vectors: [[1, 0], [0, 1]] });
    const sing = eigen(presetMatrix("singular"));
    expect(sing.kind === "distinct" && sing.values[1]).toBe(0);
  });
  it("recognises scalar, defective and complex cases", () => {
    expect(eigen([[2, 0], [0, 2]])).toEqual({ kind: "scalar", value: 2 });
    expect(eigen(presetMatrix("shear", { k: 1 }))).toEqual({ kind: "defective", value: 1, vector: [1, 0] });
    const r = eigen(presetMatrix("rotation", { theta: 30 }));
    expect(r.kind).toBe("complex");
    if (r.kind === "complex") {
      expect(r.re).toBeCloseTo(Math.cos(Math.PI / 6), 12);
      expect(r.im).toBeCloseTo(Math.sin(Math.PI / 6), 12);
    }
    const refl = eigen([[0, 1], [1, 0]]);
    expect(refl.kind === "distinct" && refl.values).toEqual([1, -1]);
  });
  it("builds correct preset matrices", () => {
    close(presetMatrix("rotation", { theta: 90 }), [[0, -1], [1, 0]]);
    close(presetMatrix("reflection", { phi: 0 }), [[1, 0], [0, -1]]);
    close(presetMatrix("reflection", { phi: 45 }), [[0, 1], [1, 0]]);
    close(presetMatrix("projection", { phi: 0 }), [[1, 0], [0, 0]]);
    const P = presetMatrix("projection", { phi: 30 });
    close(mul(P, P), P);
    const F = presetMatrix("reflection", { phi: 20 });
    close(mul(F, F), IDENTITY);
    expect(det(presetMatrix("rotation", { theta: 73 }))).toBeCloseTo(1, 12);
    expect(det(F)).toBeCloseTo(-1, 12);
    expect(det(presetMatrix("singular"))).toBe(0);
    expect(presetMatrix("scale", { sx: 2, sy: 0.5 })).toEqual([[2, 0], [0, 0.5]]);
    expect(rotationAngle(presetMatrix("rotation", { theta: -120 }))! * (180 / Math.PI)).toBeCloseTo(-120, 9);
    expect(rotationAngle(F)).toBeNull();
  });
  it("shows orientation reversal: the image of the quarter arc turns clockwise when det < 0", () => {
    const signedArea = (pts: [number, number][]) => pts.slice(1).reduce((s, p, i) => s + (pts[i][0] * p[1] - p[0] * pts[i][1]), 0);
    expect(signedArea(orientationArc(IDENTITY))).toBeGreaterThan(0);
    expect(signedArea(orientationArc([[0, 1], [1, 0]]))).toBeLessThan(0);
    expect(signedArea(orientationArc(presetMatrix("rotation", { theta: 150 })))).toBeGreaterThan(0);
  });
  it("filters the presets prop", () => {
    expect(toPresetList(["rotation", "bogus", "shear", "rotation"])).toEqual(["rotation", "shear"]);
    expect(toPresetList(undefined)).toHaveLength(7);
  });
  it("server-renders with defaults and with representative props", () => {
    expect(render(MatrixTransform)).toContain("<svg");
    expect(render(MatrixTransform, { matrix: [[0, 1], [1, 0]], mode: "single", presets: ["reflection", "rotation"] })).toContain("<svg");
    expect(render(MatrixTransform, { mode: "compose", matrix: [[1, 1], [0, 1]], matrix2: [[0, -1], [1, 0]] })).toContain("<svg");
    expect(render(MatrixTransform, { matrix: "bad", matrix2: 7, mode: "weird", modes: ["compose", "x"], presets: "all", range: "huge", showEigen: false })).toContain("<svg");
  });
});

/* ---------------------------------------------------------------------------
 * SequenceLab (lib/plot-seq.ts)
 * ------------------------------------------------------------------------- */

describe("SequenceLab", () => {
  const logistic = (r: number) => (x: number) => r * x * (1 - x);

  it("finds the ε-index of a convergent sequence, and refuses wrong limits", () => {
    const a = (n: number) => 1 + (-1) ** n / n;
    expect(sequenceTerms(a, 3)).toEqual([0, 1.5, 1 - 1 / 3]);
    // |(-1)^n / n| < 0.1 exactly when n > 10.
    expect(epsilonIndex(sequenceTerms(a, 2000), 1, 0.1)).toMatchObject({ index: 11, lastOutside: 10, checked: 2000 });
    expect(epsilonIndex(sequenceTerms(a, 2000), 1, 0.01).index).toBe(101);
    // Needs n > 10000: not visible in 2000 terms, so no index is claimed.
    expect(epsilonIndex(sequenceTerms(a, 2000), 1, 0.0001).index).toBeNull();
    expect(epsilonIndex(sequenceTerms(a, 2000), 2, 0.5).index).toBeNull();
    expect(epsilonIndex(sequenceTerms(Math.sin, 2000), 0, 0.5).index).toBeNull();
    expect(epsilonIndex(sequenceTerms(() => 3, 50), 3, 1e-9).index).toBe(1);
    // A late excursion must not produce an unconvincing index near the end.
    expect(epsilonIndex(sequenceTerms((n) => (n === 1500 ? 9 : 0), 2000), 0, 0.1).index).toBeNull();
    expect(epsilonIndex(sequenceTerms((n) => 1 / (n - 3), 100), 0, 0.5)).toMatchObject({ firstUndefined: 3 });
  });

  it("sums series accurately and stops at undefined terms", () => {
    const s = partialSums(sequenceTerms((n) => 1 / n ** 2, 1000));
    // Tail of Σ 1/n² after N terms is about 1/N − 1/(2N²).
    expect(s[999]).toBeCloseTo(Math.PI ** 2 / 6 - 1 / 1000 + 1 / 2e6, 8);
    expect(partialSums(sequenceTerms((n) => (-1) ** (n + 1) / n, 100000))[99999]).toBeCloseTo(Math.LN2, 4);
    expect(partialSums(sequenceTerms((n) => 1 / 2 ** n, 60))[59]).toBeCloseTo(1, 15);
    const broken = partialSums([1, 2, NaN, 4]);
    expect(broken.slice(0, 2)).toEqual([1, 3]);
    expect(Number.isNaN(broken[3])).toBe(true);
  });

  it("recognises the harmonic series and backs the numbers quoted in the text", () => {
    expect(looksHarmonic((n) => 1 / n)).toBe(true);
    expect(looksHarmonic((n) => 1 / n ** 2)).toBe(false);
    expect(looksHarmonic((n) => 2 / n)).toBe(false);
    expect(harmonicNumber(1000)).toBeCloseTo(7.4854708606, 9);
    expect(harmonicNumber(1e7)).toBeCloseTo(Math.log(1e7) + EULER_GAMMA, 6);
    // S_n ≈ ln n + γ passes 100 near n = e^(100 − γ) ≈ 1.5 × 10^43.
    const n100 = Math.exp(100 - EULER_GAMMA);
    expect(n100).toBeGreaterThan(1.5e43);
    expect(n100).toBeLessThan(1.52e43);
  });

  it("applies the term test only when terms clearly do not shrink", () => {
    expect(termsDoNotVanish(sequenceTerms((n) => (-1) ** n, 1000))).toBe(true);
    expect(termsDoNotVanish(sequenceTerms((n) => n / (n + 1), 1000))).toBe(true);
    expect(termsDoNotVanish(sequenceTerms((n) => 1 / n, 1000))).toBe(false);
    expect(termsDoNotVanish(sequenceTerms((n) => 1 / Math.sqrt(n), 1000))).toBe(false);
    expect(termsDoNotVanish([1, 1, 1])).toBe(false);
  });

  it("iterates maps and classifies orbits (numerically)", () => {
    expect(iterate((x) => 2 * x, 1, 3)).toEqual({ xs: [1, 2, 4, 8], stop: "ok" });
    expect(iterate((x) => Math.sqrt(x - 3), 1, 5).stop).toBe("undefined");
    expect(iterate((x) => x * x, 10, 10).stop).toBe("escape");
    const fixed = classifyOrbit(logistic(2.8), 0.2);
    expect(fixed.kind).toBe("fixed");
    if (fixed.kind === "fixed") expect(fixed.value).toBeCloseTo(1 - 1 / 2.8, 6);
    expect(classifyOrbit(logistic(3.2), 0.2)).toMatchObject({ kind: "cycle", period: 2 });
    expect(classifyOrbit(logistic(3.5), 0.2)).toMatchObject({ kind: "cycle", period: 4 });
    expect(classifyOrbit(logistic(3.56), 0.2)).toMatchObject({ kind: "cycle", period: 8 });
    expect(classifyOrbit(logistic(3.9), 0.2).kind).toBe("chaos");
    expect(classifyOrbit(logistic(4.5), 0.2).kind).toBe("escape");
    expect(classifyOrbit(logistic(1), 0.2).kind).toBe("slow");
    expect(classifyOrbit((x) => Math.sqrt(x - 3), 1).kind).toBe("undefined");
    const dottie = classifyOrbit(Math.cos, 1);
    expect(dottie.kind === "fixed" && dottie.value).toBeCloseTo(0.7390851332, 8);
  });

  it("finds fixed points with their stability, ignoring poles", () => {
    const fps = fixedPoints(logistic(2.8), [0, 1]);
    expect(fps.map((p) => p.kind)).toEqual(["repelling", "attracting"]);
    expect(fps[0].x).toBeCloseTo(0, 9);
    expect(fps[1].x).toBeCloseTo(1 - 1 / 2.8, 9);
    expect(fps[1].slope).toBeCloseTo(2 - 2.8, 4);
    expect(fixedPoints((x) => 1 / (x - 0.5), [0, 1])).toEqual([]);
    expect(fixedPoints(logistic(1), [0, 1])).toMatchObject([{ kind: "neutral" }]);
  });

  it("builds Fourier partial sums of the three waves", () => {
    expect(waveValue("square", 1)).toBe(1);
    expect(waveValue("square", -1)).toBe(-1);
    expect(waveValue("square", 0)).toBe(0);
    expect(waveValue("sawtooth", 3)).toBe(3);
    expect(waveValue("sawtooth", 4)).toBeCloseTo(4 - 2 * Math.PI, 12);
    expect(waveValue("triangle", Math.PI / 2)).toBeCloseTo(1, 12);
    expect(fourierPartial("square", 1, Math.PI / 2)).toBeCloseTo(4 / Math.PI, 12);
    // At the corner the error is about 2/(π²N).
    expect(fourierPartial("triangle", 2000, Math.PI / 2)).toBeCloseTo(1, 3);
    expect(fourierPartial("sawtooth", 2000, 1)).toBeCloseTo(1, 2);
  });

  it("measures the Gibbs overshoot: about 8.95 % of the jump, not shrinking, only narrowing", () => {
    // Si(π)/π − 1/2, checked against a numerical integral.
    expect(integrate((t) => Math.sin(t) / t, 1e-12, Math.PI) / Math.PI - 0.5).toBeCloseTo(GIBBS_FRACTION, 9);
    expect(GIBBS_FRACTION).toBeCloseTo(0.0895, 4);
    const g10 = gibbsOvershoot("square", 10)!;
    const g100 = gibbsOvershoot("square", 100)!;
    expect(g10.peak).toBeCloseTo(1.1798, 3);
    expect(Math.abs(g100.fraction - GIBBS_FRACTION)).toBeLessThan(5e-4);
    expect(Math.abs(g10.fraction - g100.fraction)).toBeLessThan(1e-3);
    expect(g100.x).toBeLessThan(g10.x / 5);
    const s20 = gibbsOvershoot("sawtooth", 20)!;
    const s200 = gibbsOvershoot("sawtooth", 200)!;
    expect(s200.fraction).toBeGreaterThan(s20.fraction);
    expect(s200.fraction).toBeLessThan(GIBBS_FRACTION + 2e-3);
    expect(gibbsOvershoot("triangle", 10)).toBeNull();
  });

  it("shows the triangle wave converging uniformly", () => {
    const e1 = maxFourierError("triangle", 1);
    const e10 = maxFourierError("triangle", 10);
    expect(e10).toBeLessThan(e1 / 5);
    expect(maxFourierError("triangle", 50)).toBeLessThan(0.005);
  });

  it("chooses which mode tabs to offer", () => {
    expect(resolveSeqModes(undefined, undefined)).toEqual({ initial: "sequence", offered: ["sequence", "series", "cobweb", "fourier"] });
    expect(resolveSeqModes("cobweb", undefined)).toEqual({ initial: "cobweb", offered: ["cobweb"] });
    expect(resolveSeqModes("series", ["sequence", "series", "bogus"])).toEqual({ initial: "series", offered: ["sequence", "series"] });
    expect(resolveSeqModes("bogus", 7)).toEqual({ initial: "sequence", offered: ["sequence", "series", "cobweb", "fourier"] });
  });

  it("server-renders with defaults and with representative props", () => {
    const def = render(SequenceLab);
    expect(def).toContain("<svg");
    expect(def).toMatch(/N = (<!-- -->)?11/);
    expect(render(SequenceLab, { mode: "sequence", term: "(1 + 1/n)^n", limit: "e", epsilon: 0.05, N: 60 })).toContain("<svg");
    expect(render(SequenceLab, { mode: "series", term: "1/n", N: 500 })).toContain("<svg");
    expect(render(SequenceLab, { mode: "series", term: "1/n^p", params: [{ name: "p", min: 0.5, max: 3, step: 0.1, value: 2 }] })).toContain("<svg");
    expect(render(SequenceLab, { mode: "cobweb", fn: "cos(x)", x: [0, 1.5], x0: 0.1, N: 40 })).toContain("<svg");
    expect(render(SequenceLab, { mode: "fourier", wave: "sawtooth", N: 20 })).toContain("<svg");
    expect(render(SequenceLab, { mode: "nope", term: "2n", limit: "oops", N: "many", params: "junk", wave: 7, x: "bad", epsilon: -1 })).toContain("<svg");
  });
});

/* ---------------------------------------------------------------------------
 * ComplexPlane
 * ------------------------------------------------------------------------- */

describe("ComplexPlane", () => {
  const close = (a: cx.C, b: cx.C, eps = 1e-9) => Math.hypot(a[0] - b[0], a[1] - b[1]) < eps;

  it("does complex arithmetic and polar form", () => {
    expect(cx.mul([1, 2], [3, -1])).toEqual([5, 5]);
    expect(close(cx.div([5, 5], [3, -1]), [1, 2])).toBe(true);
    expect(cx.div([1, 0], [0, 0]).every(Number.isNaN)).toBe(true);
    expect(cx.conj([2, -3])).toEqual([2, 3]);
    expect(cx.abs([3, 4])).toBe(5);
    expect(cx.arg([0, 1])).toBeCloseTo(Math.PI / 2, 12);
    expect(cx.arg([-1, 0])).toBeCloseTo(Math.PI, 12);
    expect(Number.isNaN(cx.arg([0, 0]))).toBe(true);
    expect(close(cx.fromPolar(2, Math.PI / 2), [0, 2])).toBe(true);
    expect(close(cx.cexp([0, Math.PI]), [-1, 0])).toBe(true);
    expect(cx.principal(3 * Math.PI)).toBeCloseTo(Math.PI, 12);
    expect(cx.principal(-3 * Math.PI / 2)).toBeCloseTo(Math.PI / 2, 12);
    // Lengths multiply, angles add (mod 2π).
    const z: cx.C = [1.5, 0.5];
    const w: cx.C = [-0.5, 1];
    expect(cx.abs(cx.mul(z, w))).toBeCloseTo(cx.abs(z) * cx.abs(w), 12);
    expect(cx.arg(cx.mul(z, w))).toBeCloseTo(cx.principal(cx.arg(z) + cx.arg(w)), 12);
  });

  it("formats complex numbers and angles", () => {
    expect(cx.fmtC([1, 2])).toBe("1 + 2i");
    expect(cx.fmtC([-0.5, -1])).toBe("−0.5 − i");
    expect(cx.fmtC([3, 0])).toBe("3");
    expect(cx.fmtC([0, 2])).toBe("2i");
    expect(cx.fmtC([0, -1])).toBe("−i");
    expect(cx.fmtC([0, 0])).toBe("0");
    expect(cx.fmtC([1, 1e-14])).toBe("1");
    expect(cx.fmtC([NaN, 1])).toBe("undefined");
    expect(cx.fmtAngle(Math.PI / 4)).toEqual({ deg: "45°", rad: "π/4" });
    expect(cx.fmtAngle(-Math.PI / 2)).toEqual({ deg: "−90°", rad: "−π/2" });
    expect(cx.fmtAngle(0.3).rad).toBe("0.3 rad");
  });

  it("reads complex props", () => {
    expect(cx.toComplex([1, "sqrt(2)"], [0, 0])).toEqual([1, Math.SQRT2]);
    expect(cx.toComplex(2, [0, 0])).toEqual([2, 0]);
    expect(cx.toComplex("pi", [0, 0])).toEqual([Math.PI, 0]);
    expect(cx.toComplex("nope", [7, 8])).toEqual([7, 8]);
    expect(cx.toComplex([1], [7, 8])).toEqual([7, 8]);
    expect(cx.toMapId("z+1/z")).toBe("joukowski");
    expect(cx.toMapId("e^z")).toBe("exp");
    expect(cx.toMapId("Möbius")).toBe("mobius");
    expect(cx.toMapId("sin", "1/z")).toBe("1/z");
    expect(cx.toCurveId("figure8")).toBe("figure8");
    expect(cx.toCurveId(7)).toBe("doubleLoop");
  });

  it("finds the n-th roots on a circle, summing to 0", () => {
    for (const [c, n] of [[[1, 0], 6], [[0, 2], 3], [[-8, 0], 3], [[1, 1], 5]] as [cx.C, number][]) {
      const roots = cx.nthRoots(c, n);
      expect(roots).toHaveLength(n);
      for (const r of roots) {
        let p: cx.C = [1, 0];
        for (let k = 0; k < n; k++) p = cx.mul(p, r);
        expect(close(p, c, 1e-9)).toBe(true);
        expect(cx.abs(r)).toBeCloseTo(Math.pow(cx.abs(c), 1 / n), 12);
      }
      const sum = roots.reduce((s, r) => cx.add(s, r), [0, 0] as cx.C);
      expect(cx.abs(sum)).toBeLessThan(1e-9);
    }
    expect(close(cx.nthRoots([0, 1], 2)[0], [Math.SQRT1_2, Math.SQRT1_2])).toBe(true);
    expect(close(cx.nthRoots([-8, 0], 3)[1], [-2, 0])).toBe(true);
    expect(cx.nthRoots([0, 0], 4).every((r) => cx.abs(r) === 0)).toBe(true);
  });

  it("has map presets whose derivatives match numerical ones", () => {
    const pts: cx.C[] = [[0.7, 0.4], [-1.3, 0.9], [0.2, -1.6], [1.9, 1.1]];
    for (const id of cx.MAP_IDS) {
      const m = cx.MAPS[id];
      expect(cx.isFiniteC(m.f(m.probe)), id).toBe(true);
      for (const z of pts) {
        const h = 1e-6;
        const num = cx.scale(cx.sub(m.f(cx.add(z, [h, 0])), m.f(cx.sub(z, [h, 0]))), 1 / (2 * h));
        expect(close(num, m.df(z), 1e-5), `${id} at ${z}`).toBe(true);
      }
      for (const c of m.critical) expect(cx.abs(m.df(c.z)), id).toBeLessThan(1e-12);
      for (const p of m.poles) expect(cx.isFiniteC(m.f(p)), id).toBe(false);
      expect(cx.gridLines(m, "cartesian").length).toBeGreaterThan(8);
      expect(cx.gridLines(m, "polar").length).toBeGreaterThan(6);
    }
  });

  it("shows conformality: right angles stay right except at critical points", () => {
    expect(cx.imageAngle(cx.MAPS["z^2"].f, [1, 0.5])).toBeCloseTo(90, 3);
    expect(cx.imageAngle(cx.MAPS.exp.f, [-0.4, 2])).toBeCloseTo(90, 3);
    expect(cx.imageAngle(cx.MAPS["1/z"].f, [0.3, -0.8])).toBeCloseTo(90, 3);
    expect(cx.imageAngle(cx.MAPS["z^2"].f, [0, 0])).toBeCloseTo(180, 6);
    expect(cx.imageAngle(cx.MAPS["z^3"].f, [0, 0])).toBeCloseTo(270, 6);
    expect(cx.imageAngle(cx.MAPS.joukowski.f, [1, 0])).toBeCloseTo(180, 1);
    expect(cx.probeStatus(cx.MAPS["z^2"], [0, 0])).toEqual({ kind: "critical", order: 2 });
    expect(cx.probeStatus(cx.MAPS["1/z"], [0, 0])).toEqual({ kind: "pole" });
    expect(cx.probeStatus(cx.MAPS.mobius, [-1, 0])).toEqual({ kind: "pole" });
    expect(cx.probeStatus(cx.MAPS.exp, [0, 0])).toEqual({ kind: "conformal" });
  });

  it("samples images of grid lines (e^z sends the imaginary axis to the unit circle)", () => {
    const view = { x: [-3, 3] as [number, number], y: [-3, 3] as [number, number] };
    const img = cx.imageCurve(cx.MAPS.exp.f, (t) => [0, t], [-Math.PI, Math.PI], view);
    expect(img).toHaveLength(1);
    for (const p of img[0]) expect(Math.hypot(p[0], p[1])).toBeCloseTo(1, 9);
    // 1/z of the line x = 1 is the circle |w − 1/2| = 1/2, broken where it passes infinity.
    const inv = cx.imageCurve(cx.MAPS["1/z"].f, (t) => [1, t], [-50, 50], view);
    for (const line of inv) for (const p of line) expect(Math.hypot(p[0] - 0.5, p[1])).toBeCloseTo(0.5, 6);
  });

  it("computes winding numbers two ways that agree", () => {
    const poly = (id: cx.CurveId, rev = false) => cx.curvePolygon(cx.CURVES[id], 720, rev);
    const cases: [cx.CurveId, cx.C, number][] = [
      ["circle", [0, 0], 1],
      ["circle", [2.5, 0.3], 0],
      ["ellipse", [1, 0.5], 1],
      ["doubleLoop", [0, 0], 2],
      ["doubleLoop", [1.5, 0.2], 1],
      ["doubleLoop", [2.8, 0], 0],
      ["figure8", [1.2, 0.1], -1],
      ["figure8", [-1.2, 0.1], 1],
      ["square", [0, 0], 1],
      ["square", [0.5, -1.5 + 1e-3], 1],
      ["cardioid", [0.5, 0], 1],
      ["cardioid", [-1.5, 0], 0],
    ];
    for (const [id, p, k] of cases) {
      const info = cx.winding(poly(id), p, 1e-6);
      expect(info.onCurve, `${id} ${p}`).toBe(false);
      expect(cx.windingInteger(info), `${id} ${p} by angle`).toBe(k);
      expect(Math.abs(info.byAngle - k), `${id} ${p} integer`).toBeLessThan(1e-9);
      expect(info.byRay, `${id} ${p} by ray`).toBe(k);
    }
    expect(Math.round(cx.windingByAngle(poly("circle", true), [0, 0]))).toBe(-1);
    expect(cx.winding(poly("circle"), [1.8, 0], 0.03).onCurve).toBe(true);
    // A ray through a vertex of the square is counted once (half-open rule).
    expect(cx.rayCrossings(poly("square"), [0, 1.5 - 1e-12]).length).toBeLessThanOrEqual(1);
  });

  it("finds regions of constant winding number", () => {
    const runs = cx.windingRuns(cx.curvePolygon(cx.CURVES.doubleLoop, 720), 80);
    expect(new Set(runs.map((r) => r.k))).toEqual(new Set([1, 2]));
    const eight = cx.windingRuns(cx.curvePolygon(cx.CURVES.figure8, 720), 80);
    expect(new Set(eight.map((r) => r.k))).toEqual(new Set([-1, 1]));
    for (const r of runs) expect(r.x1).toBeGreaterThan(r.x0);
  });

  it("server-renders every mode with defaults and representative props", () => {
    const def = render(ComplexPlane);
    expect(def).toContain("<svg");
    expect(def).toContain('aria-pressed="true"');
    expect(render(ComplexPlane, { mode: "arithmetic", op: "product", z: [1.5, 0.5], w: ["sqrt(2)/2", "sqrt(2)/2"] })).toContain("<svg");
    expect(render(ComplexPlane, { mode: "arithmetic", op: "quotient", w: [0, 0] })).toContain("<svg");
    expect(render(ComplexPlane, { mode: "roots", z: [0, 2], n: 3 })).toContain("<svg");
    const map = render(ComplexPlane, { mode: "map", map: "joukowski", grid: "cartesian", z: [1, 0] });
    expect((map.match(/<svg/g) ?? []).length).toBeGreaterThanOrEqual(2);
    expect(render(ComplexPlane, { mode: "map", map: "1/z", z: [0, 0] })).toContain("<svg");
    expect(render(ComplexPlane, { mode: "winding", curve: "figure8", z: [1.2, 0.2] })).toContain("<svg");
    expect(render(ComplexPlane, { modes: ["roots", "winding"], n: 0, curve: "nope", range: "huge" })).toContain("<svg");
    expect(render(ComplexPlane, { mode: "nope", z: "bad", w: [1], n: 99, map: 5, grid: "hex", op: "pow", modes: "junk" })).toContain("<svg");
  });
});

/* ---------------------------------------------------------------------------
 * CalculusLab
 * ------------------------------------------------------------------------- */

describe("CalculusLab", () => {
  describe("derivatives", () => {
    it("computes difference quotients", () => {
      expect(differenceQuotient((x) => x * x, 1, 0.5)).toBeCloseTo(2.5, 12);
      expect(differenceQuotient((x) => x * x, 1, -0.5)).toBeCloseTo(1.5, 12);
      expect(Number.isNaN(differenceQuotient((x) => x, 1, 0))).toBe(true);
    });
    it("finds the derivative at smooth points", () => {
      const sq = derivativeAt((x) => x * x, 1);
      expect(sq.kind).toBe("smooth");
      if (sq.kind === "smooth") expect(sq.slope).toBeCloseTo(2, 7);
      const s = derivativeAt(Math.sin, 0);
      if (s.kind === "smooth") expect(s.slope).toBeCloseTo(1, 7);
      else throw new Error("sin should be smooth at 0");
      const cube = derivativeAt((x) => x ** 3, 0);
      expect(cube.kind).toBe("smooth");
      const fast = derivativeAt((x) => Math.sin(1000 * x), 0.3);
      expect(fast.kind).toBe("smooth");
      if (fast.kind === "smooth") expect(fast.slope).toBeCloseTo(1000 * Math.cos(300), 2);
      const steep = derivativeAt((x) => 1 / x, 0.001);
      if (steep.kind === "smooth") expect(steep.slope / -1e6).toBeCloseTo(1, 4);
      else throw new Error("1/x should be smooth at 0.001");
    });
    it("diagnoses corners, jumps, vertical tangents and undefined points honestly", () => {
      expect(derivativeAt(Math.abs, 0)).toMatchObject({ kind: "corner" });
      const c = derivativeAt((x) => Math.abs(x - 1), 1);
      if (c.kind !== "corner") throw new Error("corner expected");
      expect(c.left).toBeCloseTo(-1, 6);
      expect(c.right).toBeCloseTo(1, 6);
      expect(derivativeAt(Math.sign, 0).kind).toBe("jump");
      expect(derivativeAt(Math.floor, 1).kind).toBe("jump");
      expect(derivativeAt(Math.cbrt, 0).kind).toBe("vertical");
      expect(derivativeAt((x) => Math.sqrt(Math.abs(x)), 0).kind).toBe("vertical");
      expect(derivativeAt(Math.sqrt, 0).kind).toBe("undefined");
      expect(derivativeAt((x) => 1 / x, 0).kind).toBe("undefined");
    });
  });

  describe("Riemann sums", () => {
    const sq = (x: number) => x * x;
    it("matches hand computations for x² on [0, 2] with n = 4", () => {
      expect(riemannSum(sq, 0, 2, 4, "left").sum).toBeCloseTo(1.75, 12);
      expect(riemannSum(sq, 0, 2, 4, "right").sum).toBeCloseTo(3.75, 12);
      expect(riemannSum(sq, 0, 2, 4, "midpoint").sum).toBeCloseTo(2.625, 12);
      expect(riemannSum(sq, 0, 2, 4, "trapezoid").sum).toBeCloseTo(2.75, 12);
      const r = riemannSum(sq, 0, 2, 4, "midpoint");
      expect(r.pieces).toHaveLength(4);
      expect(r.pieces[0]).toMatchObject({ x0: 0, x1: 0.5, h0: 0.0625, h1: 0.0625, samples: [0.25] });
    });
    it("converges to the integral, midpoint and trapezoid much faster", () => {
      const exact = 8 / 3;
      const err = (m: "left" | "midpoint" | "trapezoid", n: number) => Math.abs(riemannSum(sq, 0, 2, n, m).sum - exact);
      expect(err("left", 200)).toBeLessThan(0.03);
      expect(err("midpoint", 200)).toBeLessThan(1e-4);
      expect(err("trapezoid", 200)).toBeLessThan(1e-4);
      expect(err("left", 100) / err("left", 200)).toBeCloseTo(2, 1);
      expect(err("midpoint", 100) / err("midpoint", 200)).toBeCloseTo(4, 1);
    });
    it("handles signed area, undefined integrands and bad n", () => {
      expect(riemannSum(Math.sin, 0, 2 * Math.PI, 100, "midpoint").sum).toBeCloseTo(0, 10);
      const bad = riemannSum(Math.log, -1, 1, 10, "left");
      expect(bad.ok).toBe(false);
      expect(Number.isNaN(bad.sum)).toBe(true);
      expect(riemannSum(sq, 0, 1, 0, "left").pieces).toHaveLength(1);
      expect(riemannSum(sq, 0, 1, NaN, "left").pieces).toHaveLength(1);
      expect(riemannSum(sq, 0, 1, 1e9, "left").pieces.length).toBeLessThanOrEqual(2000);
    });
  });

  describe("Taylor polynomials", () => {
    it("has the exact Maclaurin coefficients", () => {
      expect(taylorCoefficient(TAYLOR.sin, 1)).toBe(1);
      expect(taylorCoefficient(TAYLOR.sin, 2)).toBe(0);
      expect(taylorCoefficient(TAYLOR.sin, 3)).toBeCloseTo(-1 / 6, 15);
      expect(taylorCoefficient(TAYLOR.sin, 5)).toBeCloseTo(1 / 120, 15);
      expect(taylorCoefficient(TAYLOR.cos, 0)).toBe(1);
      expect(taylorCoefficient(TAYLOR.cos, 2)).toBe(-0.5);
      expect(taylorCoefficient(TAYLOR.exp, 4)).toBeCloseTo(1 / 24, 15);
      expect(taylorCoefficient(TAYLOR.ln1p, 0)).toBe(0);
      expect(taylorCoefficient(TAYLOR.ln1p, 2)).toBe(-0.5);
      expect(taylorCoefficient(TAYLOR.ln1p, 3)).toBeCloseTo(1 / 3, 15);
      expect(taylorCoefficient(TAYLOR.geometric, 7)).toBe(1);
      expect(taylorCoefficient(TAYLOR.atan, 3)).toBeCloseTo(-1 / 3, 15);
      expect(taylorCoefficient(TAYLOR.atan, 4)).toBe(0);
    });
    it("approximates inside the interval of convergence and diverges outside", () => {
      expect(taylorPolynomial(TAYLOR.sin, 9)(0.5)).toBeCloseTo(Math.sin(0.5), 10);
      expect(taylorPolynomial(TAYLOR.exp, 20)(3)).toBeCloseTo(Math.exp(3), 6);
      expect(taylorPolynomial(TAYLOR.geometric, 10)(0.5)).toBeCloseTo((1 - 0.5 ** 11) / 0.5, 12);
      expect(Math.abs(taylorPolynomial(TAYLOR.geometric, 20)(2))).toBeGreaterThan(1e6);
      const lnErr = (n: number, x: number) => Math.abs(taylorPolynomial(TAYLOR.ln1p, n)(x) - Math.log1p(x));
      expect(lnErr(30, 0.5)).toBeLessThan(lnErr(10, 0.5));
      expect(lnErr(30, 1.5)).toBeGreaterThan(lnErr(10, 1.5));
      expect(taylorPolynomial(TAYLOR.cos, 0)(5)).toBe(1);
    });
    it("writes readable formulas", () => {
      expect(taylorFormula(TAYLOR.sin, 5)).toBe("x − x³/3! + x⁵/5!");
      expect(taylorFormula(TAYLOR.sin, 6)).toBe("x − x³/3! + x⁵/5!");
      expect(taylorFormula(TAYLOR.exp, 2)).toBe("1 + x + x²/2!");
      expect(taylorFormula(TAYLOR.ln1p, 3)).toBe("x − x²/2 + x³/3");
      expect(taylorFormula(TAYLOR.geometric, 20)).toBe("1 + x + x² + x³ + ⋯ + x²⁰");
      expect(taylorFormula(TAYLOR.cos, 2)).toBe("1 − x²/2!");
      expect(taylorFormula(TAYLOR.cos, 0)).toBe("1");
      expect(taylorFormula(TAYLOR.sin, 0)).toBe("0");
    });
    it("knows the intervals of convergence, including endpoints", () => {
      expect(inConvergence(TAYLOR.ln1p, 1)).toBe(true);
      expect(inConvergence(TAYLOR.ln1p, -1)).toBe(false);
      expect(inConvergence(TAYLOR.geometric, 1)).toBe(false);
      expect(inConvergence(TAYLOR.geometric, -0.99)).toBe(true);
      expect(inConvergence(TAYLOR.atan, -1)).toBe(true);
      expect(inConvergence(TAYLOR.atan, 1.01)).toBe(false);
      expect(inConvergence(TAYLOR.sin, 100)).toBe(true);
    });
  });

  describe("the ε–δ game", () => {
    const sq = (x: number) => x * x;
    const jump = (x: number) => x / 2 + Math.sign(x);
    it("checks a proposed δ by sampling the punctured neighbourhood", () => {
      const ok = checkDelta(sq, 1, 1, 0.5, 0.2);
      expect(ok.ok).toBe(true);
      expect(ok.checked).toBeGreaterThan(2000);
      const bad = checkDelta(sq, 1, 1, 0.5, 0.3);
      expect(bad.ok).toBe(false);
      expect(bad.badX!).toBeCloseTo(Math.sqrt(1.5), 2);
      expect(bad.gap).toBeGreaterThanOrEqual(0.5);
      expect(checkDelta(jump, 0, 1, 0.5, 0.001).ok).toBe(false);
      expect(checkDelta(sq, 1, 1, 0.5, 0).ok).toBe(false);
      // The point x = a itself is excluded: a removable hole does not matter.
      const hole = (x: number) => (x === 1 ? 100 : x);
      expect(checkDelta(hole, 1, 1, 0.1, 0.05).ok).toBe(true);
    });
    it("finds the largest δ that works, or reports that none does", () => {
      expect(largestDelta(sq, 1, 1, 0.5, 2)!).toBeCloseTo(Math.sqrt(1.5) - 1, 6);
      expect(largestDelta(sq, 1, 1, 0.1, 2)!).toBeCloseTo(Math.sqrt(1.1) - 1, 6);
      expect(largestDelta(jump, 0, 1, 0.5, 2)).toBeNull();
      expect(largestDelta(sq, 1, 1.5, 0.1, 2)).toBeNull();
      expect(largestDelta(() => 3, 0, 3, 0.1, 2)).toBe(2);
    });
    it("maps the logarithmic sliders both ways", () => {
      expect(logSliderValue(0, 2, 0.001)).toBeCloseTo(2, 12);
      expect(logSliderValue(100, 2, 0.001)).toBeCloseTo(0.001, 12);
      expect(logSliderValue(logSliderPosition(0.25, 2, 0.001), 2, 0.001)).toBeCloseTo(0.25, 10);
      expect(logSliderPosition(-0.25, 2, 0.001)).toBeCloseTo(logSliderPosition(0.25, 2, 0.001), 12);
      expect(logSliderPosition(99, 2, 0.001)).toBe(0);
    });
  });

  it("chooses which mode tabs to offer", () => {
    expect(calcModes(undefined, undefined)).toEqual(["tangent", "riemann", "taylor", "epsilon-delta"]);
    expect(calcModes("taylor", undefined)).toEqual(["taylor"]);
    expect(calcModes("taylor", ["riemann", "taylor", "nope", "taylor"])).toEqual(["riemann", "taylor"]);
    expect(calcModes("bogus", [])).toEqual(["tangent", "riemann", "taylor", "epsilon-delta"]);
  });

  it("server-renders with defaults and with representative props", () => {
    expect(render(CalculusLab)).toContain("<svg");
    expect(render(CalculusLab, { mode: "tangent", fn: "sin(x)", x0: "pi/4", x: ["-pi", "pi"] })).toContain("<svg");
    // The corner diagnosis replaces the tangent slope (key name before the catalogues are merged, text after).
    expect(render(CalculusLab, { mode: "tangent", fn: "abs(x - 1)", x0: 1 })).toMatch(/w\.calc\.tan\.corner|not differentiable/);
    expect(render(CalculusLab, { mode: "riemann", fn: "x^2", interval: [0, 2], exact: "8/3", n: 8, method: "midpoint" })).toContain("<svg");
    expect(render(CalculusLab, { mode: "taylor", preset: "ln1p", degree: 7 })).toContain("<svg");
    expect(render(CalculusLab, { mode: "epsilon-delta", fn: "x^2", a: 1, L: 1, epsilon: 0.1 })).toContain("<svg");
    expect(render(CalculusLab, { mode: "epsilon-delta", preset: "jump" })).toContain("<svg");
    expect(render(CalculusLab, { modes: ["riemann", "taylor"], preset: "atan" })).toContain("aria-pressed");
  });

  it("never crashes on malformed props", () => {
    const html = render(CalculusLab, { mode: "riemann", fn: "2x", interval: "nope", n: -4, method: "weird", exact: {}, x: [1], y: "no" });
    expect(html).toContain("<svg");
    expect(render(CalculusLab, { mode: "tangent", fn: 42, x0: "zzz", x: [5, 5] })).toContain("<svg");
    expect(render(CalculusLab, { mode: "taylor", preset: "nope", degree: 999 })).toContain("<svg");
    expect(render(CalculusLab, { mode: "epsilon-delta", fn: "sqrt(x)", a: -5, epsilon: -1 })).toContain("<svg");
  });
});

describe("VectorField", () => {
  const box: vf.Box = { x: [-4, 4], y: [-4, 4] };
  const F = (f: (x: number, y: number) => [number, number]): vf.Field2 => f;
  const centre = F((x, y) => [-y, x]);
  const near = (a: number, b: number, tol: number) => Math.abs(a - b) <= tol;

  it("integrates with fourth-order Runge–Kutta", () => {
    let p: Pt = [1, 0];
    for (let i = 0; i < 10; i++) p = vf.rk4(F((x) => [-x, 0]), p, 0.1);
    expect(p[0]).toBeCloseTo(Math.exp(-1), 6);
  });

  it("stops trajectories for honest reasons", () => {
    const c = vf.orbit(centre, [2, 0], box);
    expect(c.reason).toBe("closed");
    for (const q of c.points) expect(Math.hypot(q[0], q[1])).toBeCloseTo(2, 3);
    const sink = F((x, y) => [-0.25 * x - y, x - 0.25 * y]);
    const s = vf.orbit(sink, [3.8, 0], box);
    expect(s.reason).toBe("equilibrium");
    const end = s.points[s.points.length - 1];
    expect(Math.hypot(end[0], end[1])).toBeLessThan(0.2);
    expect(vf.orbit(sink, [3.8, 0], box, { dir: -1 }).reason).toBe("left");
    expect(vf.orbit(F((x, y) => [x, -y]), [0.15, 3.8], box).reason).toBe("left");
    expect(vf.orbit(F(() => [0, 0]), [1, 1], box).reason).toBe("equilibrium");
    expect(vf.orbit(F(() => [NaN, 0]), [1, 1], box).reason).toBe("undefined");
  });

  it("recognises the van der Pol limit cycle", () => {
    const vdp = F((x, y) => [y, (1 - x * x) * y - x]);
    for (const start of [[0.1, 0], [3.5, 3.5]] as Pt[]) {
      const o = vf.orbit(vdp, start, box);
      expect(o.reason).toBe("cycle");
      const tail = o.points.slice(-200);
      // The limit cycle reaches |x| ≈ 2.
      expect(Math.max(...tail.map((q) => Math.abs(q[0])))).toBeGreaterThan(1.8);
      expect(Math.max(...tail.map((q) => Math.abs(q[0])))).toBeLessThan(2.2);
    }
  });

  it("solves dy/dx = f(x, y) and ends solutions at vertical tangents", () => {
    const e = vf.slopeSolution((_x, y) => y, [0, 1], box, { ds: 0.005 });
    const at1 = e.points.reduce((best, q) => (Math.abs(q[0] - 1) < Math.abs(best[0] - 1) ? q : best));
    expect(at1[1]).toBeCloseTo(Math.exp(at1[0]), 4);
    const circ = vf.slopeSolution((x, y) => -x / y, [0, 2], box);
    expect(circ.reason).toBe("vertical");
    const last = circ.points[circ.points.length - 1];
    expect(last[0]).toBeCloseTo(2, 3);
    for (const q of circ.points) expect(Math.hypot(q[0], q[1])).toBeCloseTo(2, 6);
    expect(vf.slopeSolution((x, y) => -x / y, [0, 2], box, { dir: -1 }).points[1][0]).toBeLessThan(0);
    expect(vf.slopeSolution((x, y) => x * x + y * y, [0, 0], box).reason).toBe("left");
    expect(vf.slopeSolution(() => NaN, [0, 0], box).reason).toBe("undefined");
  });

  it("classifies linear systems by trace and determinant", () => {
    const k = (A: vf.Mat2) => vf.classify(A).kind;
    expect(k([[0, -1], [1, 0]])).toBe("center");
    expect(k([[1, 0], [0, -1]])).toBe("saddle");
    expect(k([[-0.25, -1], [1, -0.25]])).toBe("spiralSink");
    expect(k([[0.2, -1], [1, 0.2]])).toBe("spiralSource");
    expect(k([[-2, 1], [1, -2]])).toBe("nodeSink");
    expect(k([[2, 1], [1, 2]])).toBe("nodeSource");
    expect(k([[-1, 1], [0, -1]])).toBe("improperSink");
    expect(k([[3, 0], [0, 3]])).toBe("improperSource");
    expect(k([[1, 2], [2, 4]])).toBe("degenerate");
    const c = vf.classify([[-2, 1], [1, -2]]);
    expect(c).toMatchObject({ trace: -4, det: 3, disc: 4 });
    expect(c.eig.re).toEqual([-3, -1]);
    expect(vf.classify([[0, -2], [2, 0]]).eig).toEqual({ re: [0, 0], im: 2 });
  });

  it("detects linear systems and locates equilibria", () => {
    expect(vf.linearFit(F((x, y) => [-2 * x + y, x - 2 * y]), 4)).toEqual({ A: [[-2, 1], [1, -2]], b: [0, 0] });
    expect(vf.linearFit(F((x, y) => [y, -Math.sin(x)]), 4)).toBeNull();
    const affine = analyseSystem(F((x, y) => [x - 1, -y + 2]), box);
    expect(affine.linear).toBe(true);
    expect(affine.eq[0].p).toEqual([1, 2]);
    expect(affine.eq[0].c.kind).toBe("saddle");
    const pend = analyseSystem(F((x, y) => [y, -Math.sin(x)]), { x: [-2 * Math.PI, 2 * Math.PI], y: [-3.2, 3.2] });
    expect(pend.linear).toBe(false);
    expect(pend.eq.map((e) => e.p[0] / Math.PI).map(Math.round)).toEqual([-2, -1, 0, 1, 2]);
    expect(pend.eq.map((e) => e.c.kind)).toEqual(["center", "saddle", "center", "saddle", "center"]);
    const lv = vf.findEquilibria(F((x, y) => [x * (1 - 0.5 * y), y * (0.5 * x - 1)]), { x: [0, 6], y: [0, 6] });
    expect(lv).toEqual([[0, 0], [2, 2]]);
  });

  it("checks Green's theorem numerically, and notices when it cannot apply", () => {
    const fields: [vf.Field2, Pt][] = [
      [centre, [0.5, 0.3]],
      [F((x, y) => [x, y]), [1, -1]],
      [F((x, y) => [x * y * y, x * x + y]), [-0.7, 0.4]],
      [F((x, y) => [Math.sin(y), Math.cos(x) * y]), [0.3, 0.2]],
    ];
    for (const [G, c] of fields) {
      const line = vf.loopIntegrals(G, c, 1.3);
      const disk = vf.diskIntegrals(G, c, 1.3);
      expect(near(line.circulation, disk.curl, 1e-6)).toBe(true);
      expect(near(line.flux, disk.div, 1e-6)).toBe(true);
    }
    expect(vf.loopIntegrals(centre, [0, 0], 1.5).circulation).toBeCloseTo(2 * Math.PI * 1.5 * 1.5, 9);
    const vortex = F((x, y) => [-y / (x * x + y * y), x / (x * x + y * y)]);
    expect(vf.loopIntegrals(vortex, [0.2, 0], 1).circulation).toBeCloseTo(2 * Math.PI, 9);
    expect(Math.abs(vf.diskIntegrals(vortex, [0.2, 0], 1).curl)).toBeLessThan(0.5);
    const gl = vf.gaussLegendre(6);
    expect(gl.x.reduce((a, x, i) => a + gl.w[i] * x ** 10, 0)).toBeCloseTo(2 / 11, 12);
  });

  it("computes the index of each preset field around its default loop", () => {
    const want: Record<string, number> = { rotation: 1, source: 1, sink: 1, saddleField: -1, dipole: 2, uniform: 0, shear: 0 };
    for (const [id, p] of Object.entries(vf.FIELD_PRESETS)) {
      const fr = compileExpr(p.f, ["x", "y"]);
      const gr = compileExpr(p.g, ["x", "y"]);
      if (!fr.ok || !gr.ok) throw new Error(id);
      const G: vf.Field2 = (x, y) => [fr.fn({ x, y }), gr.fn({ x, y })];
      const r = vf.fieldIndex(G, [p.loop[0], p.loop[1]], p.loop[2]);
      expect(r.status, id).toBe("ok");
      expect(r.index, id).toBe(want[id]);
      expect(r.turning[r.turning.length - 1] / (2 * Math.PI)).toBeCloseTo(want[id], 6);
    }
    expect(vf.fieldIndex(centre, [3, 3], 0.5).index).toBe(0);
    expect(vf.fieldIndex(F((x, y) => [y, 0]), [0, 0], 1).status).not.toBe("ok");
    expect(vf.fieldIndex(F((x, y) => [x, y]), [1, 0], 1).status).toBe("zero");
    expect(vf.fieldIndex(F(() => [NaN, 1]), [0, 0], 1).status).toBe("undefined");
  });

  it("compiles every preset and places arrowheads along curves", () => {
    for (const p of [...Object.values(vf.SLOPE_PRESETS)]) expect(compileExpr(p.f, ["x", "y"]).ok).toBe(true);
    for (const p of [...Object.values(vf.PHASE_PRESETS), ...Object.values(vf.FIELD_PRESETS)]) {
      expect(compileExpr(p.f, ["x", "y"]).ok).toBe(true);
      expect(compileExpr(p.g, ["x", "y"]).ok).toBe(true);
    }
    const marks = vf.arrowMarks([[0, 0], [100, 0], [100, 100]], 50);
    expect(marks.map((m) => [m.x, m.y])).toEqual([[25, 0], [75, 0], [100, 25], [100, 75]]);
    expect(marks[2].angle).toBeCloseTo(Math.PI / 2, 12);
  });

  it("resolves modes and start points from props", () => {
    expect(resolveModes({})).toEqual({ offered: ["slope", "phase", "field"], initial: "slope" });
    expect(resolveModes({ mode: "phase" })).toEqual({ offered: ["phase"], initial: "phase" });
    expect(resolveModes({ preset: "dipole" }).initial).toBe("field");
    expect(resolveModes({ preset: "centre" }).initial).toBe("phase");
    expect(resolveModes({ g: "x" }).initial).toBe("phase");
    expect(resolveModes({ modes: ["field", "phase"], preset: "center" })).toEqual({ offered: ["phase", "field"], initial: "phase" });
    expect(resolveModes({ modes: ["junk"], mode: "slope" })).toEqual({ offered: ["slope"], initial: "slope" });
    expect(vf.presetMode("logistic")).toBe("slope");
    expect(vf.presetMode("nope")).toBeNull();
    expect(parseStartPoints([[1, 2], ["pi", "-1"], [1], "x", [NaN, 0], null])).toEqual([[1, 2], [Math.PI, -1]]);
    expect(parseStartPoints("bad")).toEqual([]);
  });

  it("server-renders every mode, with defaults and representative props", () => {
    expect(render(VectorField)).toContain("<svg");
    expect(render(VectorField, { mode: "slope", preset: "logistic" })).toContain("<svg");
    expect(render(VectorField, { mode: "slope", f: "dy/dx = x^2 - y", points: [[0, 0], [-2, 1]], x: [-3, 3], y: [-3, 3] })).toContain("<svg");
    expect(render(VectorField, { mode: "phase", preset: "pendulum", points: [[0, 1]] })).toContain("<svg");
    expect(render(VectorField, { mode: "phase", f: "x' = x - y", g: "y' = x + y" })).toContain("<svg");
    expect(render(VectorField, { mode: "field", preset: "dipole" })).toContain("<svg");
    expect(render(VectorField, { modes: ["phase", "field"], f: "-y/(x^2+y^2)", g: "x/(x^2+y^2)" })).toContain("<svg");
    const bad = render(VectorField, { mode: "phase", f: "2x", g: "y +", x: "bad", y: [3], points: 7, preset: 12, modes: "nope" });
    expect(bad).toContain("<svg");
    expect(bad).toContain('role="alert"');
  });
});

/* ---------------------------------------------------------------------------
 * Documentation examples: every ```mdx block in docs/widgets/analysis.md must
 * compile, render, and contain no expression errors.
 * ------------------------------------------------------------------------- */

describe("docs/widgets/analysis.md examples", () => {
  const doc = read("docs/widgets/analysis.md");
  const blocks = [...doc.matchAll(/```mdx\n([\s\S]*?)```/g)].map((m) => m[1]);
  it("documents every registered widget with at least two examples", () => {
    for (const tag of Object.keys(ANALYSIS_WIDGETS)) expect(blocks.filter((b) => b.includes(`<${tag}`)).length, tag).toBeGreaterThanOrEqual(2);
  });
  blocks.forEach((src, i) => {
    const tag = /<([A-Z][A-Za-z]+)/.exec(src)?.[1] ?? "?";
    it(`example ${i + 1} (${tag}) compiles and renders without expression errors`, async () => {
      const { default: Content } = await evaluate(src, { ...runtime, development: false });
      const html = renderToString(createElement(I18nProvider, { locale: "en", messages: en, children: createElement(Content, { components: ANALYSIS_WIDGETS }) }));
      expect(html).toContain("<svg");
      expect(html).not.toContain('role="alert"');
    });
  });
});

// @@tests (one block per widget; keep this marker)
