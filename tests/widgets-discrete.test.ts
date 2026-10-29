import { describe, expect, it } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { createElement } from "react";
import * as runtime from "react/jsx-runtime";
import { evaluate as evaluateMdx } from "@mdx-js/mdx";
import { renderToString } from "react-dom/server";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import ar from "@/i18n/messages/ar.json";
import { GraphExplorer } from "@/components/widgets/GraphExplorer";
import { TruthTable } from "@/components/widgets/TruthTable";
import { ChanceLab, EXPERIMENTS } from "@/components/widgets/ChanceLab";
import { CommutativeDiagram } from "@/components/widgets/CommutativeDiagram";
import { DISCRETE_WIDGETS } from "@/components/widgets/registry-discrete";
import {
  PRESET_IDS,
  adjacencyMatrix,
  analyseWalk,
  bfsTree,
  bigDet,
  buildGraph,
  chromaticNumber,
  colourInfo,
  degrees,
  edgeShapes,
  emptyWalk,
  eulerInfo,
  extendWalk,
  greedyColouring,
  isConnected,
  isSimple,
  listWalks,
  matPow,
  presetGraph,
  spanningInfo,
  spanningTreeCount,
  walkVertices,
  type Walk,
} from "@/components/widgets/lib/graph-core";
import { assignments, classify, differences, evaluate, parseFormula, show, showFull, subformulas, truthTable } from "@/components/widgets/lib/logic-core";
import {
  binomialCoefficient,
  binomialPmf,
  birthdayExact,
  birthdayGroups,
  buffonEstimate,
  dropNeedles,
  flipCoins,
  galton,
  montyGame,
  montyHall,
  mulberry32,
  randomWalks,
  rollDice,
  runningProportion,
  seedFor,
  tally,
  trialSteps,
  twoDiceExact,
} from "@/components/widgets/lib/chance-core";
import { bezier, describeDiagram, layoutDiagram, measureTex, normaliseDiagram, repairTex, texToText } from "@/components/widgets/lib/diagram-core";

/* ------------------------------------------------------------------------ */
/* Graphs                                                                    */
/* ------------------------------------------------------------------------ */

describe("graph presets", () => {
  const expected: Record<string, { v: number; e: number; chi: number; tau: bigint }> = {
    konigsberg: { v: 4, e: 7, chi: 3, tau: 21n },
    k4: { v: 4, e: 6, chi: 4, tau: 16n },
    k5: { v: 5, e: 10, chi: 5, tau: 125n },
    k33: { v: 6, e: 9, chi: 2, tau: 81n },
    petersen: { v: 10, e: 15, chi: 3, tau: 2000n },
    cube: { v: 8, e: 12, chi: 2, tau: 384n },
    cycle6: { v: 6, e: 6, chi: 2, tau: 6n },
    tree: { v: 7, e: 6, chi: 2, tau: 1n },
    wheel: { v: 6, e: 10, chi: 4, tau: 121n },
  };
  for (const id of PRESET_IDS) {
    it(`${id}: size, chromatic number and spanning-tree count`, () => {
      const g = presetGraph(id);
      expect(g.labels).toHaveLength(expected[id].v);
      expect(g.edges).toHaveLength(expected[id].e);
      expect(chromaticNumber(g)).toBe(expected[id].chi);
      expect(spanningTreeCount(g)).toBe(expected[id].tau);
      // handshake lemma
      expect(degrees(g).reduce((s, d) => s + d, 0)).toBe(2 * g.edges.length);
      // positions fit inside the drawing
      for (const p of g.pos) {
        expect(p.x).toBeGreaterThanOrEqual(0);
        expect(p.x).toBeLessThanOrEqual(360);
        expect(p.y).toBeGreaterThanOrEqual(0);
        expect(p.y).toBeLessThanOrEqual(300);
      }
    });
  }
  it("Königsberg has four odd vertices and no Euler trail", () => {
    const g = presetGraph("konigsberg");
    expect(degrees(g)).toEqual([3, 3, 5, 3]);
    const e = eulerInfo(g);
    expect(e.odd).toHaveLength(4);
    expect(e.trail).toBe(false);
    expect(isSimple(g)).toBe(false);
  });
  it("Petersen is 3-regular; the cube is bipartite; K₅ needs 5 colours", () => {
    expect(new Set(degrees(presetGraph("petersen")))).toEqual(new Set([3]));
    expect(chromaticNumber(presetGraph("cube"))).toBe(2);
    expect(chromaticNumber(presetGraph("k5"))).toBe(5);
  });
  it("Euler circuits and trails are recognised", () => {
    expect(eulerInfo(presetGraph("cycle6")).circuit).toBe(true);
    const path = buildGraph({ nodes: ["A", "B", "C"], edges: [["A", "B"], ["B", "C"]] }).graph;
    const e = eulerInfo(path);
    expect(e.circuit).toBe(false);
    expect(e.trail).toBe(true);
    expect(e.odd).toEqual([0, 2]);
    const twoPieces = buildGraph({ edges: [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3]] }).graph;
    expect(eulerInfo(twoPieces).edgesConnected).toBe(false);
    expect(eulerInfo(twoPieces).trail).toBe(false);
  });
});

describe("graph input parsing", () => {
  it("accepts labels, indices and positions, and skips bad entries", () => {
    const { graph, ignored, custom } = buildGraph({
      nodes: ["P", "Q", "R"],
      edges: [["P", "Q"], [1, 2], ["R", "nope"], ["P", "P"], "junk", [0]],
      positions: [[0, 0], [1, 0], [0.5, 1]],
    });
    expect(custom).toBe(true);
    expect(graph.labels).toEqual(["P", "Q", "R"]);
    expect(graph.edges).toEqual([
      [0, 1],
      [1, 2],
    ]);
    expect(ignored).toBe(4);
    expect(graph.pos[0].y).toBeCloseTo(graph.pos[1].y);
    expect(graph.pos[2].y).toBeGreaterThan(graph.pos[0].y);
  });
  it("infers vertices from edges when no nodes are given", () => {
    expect(buildGraph({ edges: [[0, 1], [1, 3]] }).graph.labels).toEqual(["0", "1", "2", "3"]);
    expect(buildGraph({ edges: [["x", "y"], ["y", "z"]] }).graph.labels).toEqual(["x", "y", "z"]);
  });
  it("falls back to circular layout for malformed positions and to Königsberg for unknown presets", () => {
    const g = buildGraph({ nodes: ["a", "b"], edges: [["a", "b"]], positions: [[0, 0], ["x", 1]] }).graph;
    expect(g.pos).toHaveLength(2);
    expect(buildGraph({ preset: "nonsense" }).graph.edges).toHaveLength(7);
    expect(buildGraph({ preset: "k4" }).custom).toBe(false);
  });
  it("draws parallel edges as distinct curves", () => {
    const g = presetGraph("konigsberg");
    const shapes = edgeShapes(g);
    expect(shapes[0].d).not.toBe(shapes[1].d);
    expect(shapes[0].d).toContain("Q");
    expect(shapes[4].d).toContain("L");
  });
});

describe("walks", () => {
  const g = presetGraph("cycle6"); // edges i–(i+1)
  it("builds a walk edge by edge, flipping the first edge if needed", () => {
    let w: Walk = emptyWalk;
    const r1 = extendWalk(g, w, 0); // A–B
    expect(r1.ok).toBe(true);
    w = (r1 as { ok: true; walk: Walk }).walk;
    const r2 = extendWalk(g, w, 5); // F–A touches A, so the walk becomes B → A → F
    expect(r2.ok).toBe(true);
    w = (r2 as { ok: true; walk: Walk }).walk;
    expect(walkVertices(g, w)).toEqual([1, 0, 5]);
    expect(extendWalk(g, w, 2).ok).toBe(false); // C–D does not touch F
  });
  it("classifies trails, circuits and Euler circuits", () => {
    const w: Walk = { start: 0, edges: [0, 1, 2, 3, 4, 5], flexible: false };
    const info = analyseWalk(g, w);
    expect(info.closed && info.trail && info.circuit && info.eulerCircuit).toBe(true);
    const back: Walk = { start: 0, edges: [0, 0], flexible: false };
    const b = analyseWalk(g, back);
    expect(b.closed).toBe(true);
    expect(b.trail).toBe(false);
    expect(b.circuit).toBe(false);
  });
});

describe("colourings and spanning trees", () => {
  it("greedy colourings are proper", () => {
    for (const id of PRESET_IDS) {
      const g = presetGraph(id);
      expect(colourInfo(g, greedyColouring(g)).proper, id).toBe(true);
    }
  });
  it("reports clashes and uncoloured vertices", () => {
    const g = presetGraph("k4");
    const info = colourInfo(g, [0, 0, 1, null]);
    expect(info.conflicts).toEqual([0]);
    expect(info.uncoloured).toBe(1);
    expect(info.used).toBe(2);
    expect(info.proper).toBe(false);
  });
  it("checks spanning trees and finds cycles", () => {
    const g = presetGraph("k4"); // edges: 01 02 03 12 13 23
    const tree = spanningInfo(g, [0, 1, 2]);
    expect(tree.isTree).toBe(true);
    const cyc = spanningInfo(g, [0, 3, 1]);
    expect(cyc.cycle?.sort()).toEqual([0, 1, 3]);
    expect(cyc.isTree).toBe(false);
    expect(spanningInfo(g, [0]).pieces).toBe(3);
    expect(spanningInfo(g, bfsTree(g)).isTree).toBe(true);
    expect(isConnected(buildGraph({ nodes: ["a", "b", "c"], edges: [["a", "b"]] }).graph)).toBe(false);
  });
  it("computes exact determinants", () => {
    expect(bigDet([[2n, 0n], [0n, 3n]])).toBe(6n);
    expect(bigDet([[0n, 1n], [1n, 0n]])).toBe(-1n);
    expect(bigDet([[1n, 2n, 3n], [4n, 5n, 6n], [7n, 8n, 10n]])).toBe(-3n);
  });
});

describe("adjacency matrices", () => {
  it("counts walks with powers of A", () => {
    const g = presetGraph("k4");
    const A = adjacencyMatrix(g);
    const A2 = matPow(A, 2);
    expect(A2.map((r, i) => r[i])).toEqual([3, 3, 3, 3]);
    expect(A2[0][1]).toBe(2);
    const A3 = matPow(A, 3);
    expect(A3.reduce((s, r, i) => s + r[i], 0) / 6).toBe(4); // K4 has 4 triangles
    expect(listWalks(g, 0, 1, 2)).toHaveLength(2);
    expect(matPow(A, 0)).toEqual([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
  });
  it("counts multi-edges", () => {
    expect(adjacencyMatrix(presetGraph("konigsberg"))[0][2]).toBe(2);
  });
});

/* ------------------------------------------------------------------------ */
/* Logic                                                                     */
/* ------------------------------------------------------------------------ */

describe("logic parser", () => {
  const p = (s: string) => {
    const r = parseFormula(s);
    if (!r.ok) throw new Error(`parse failed: ${s} (${r.error.code})`);
    return r.formula;
  };
  it("respects precedence and associativity", () => {
    expect(showFull(p("p ∧ q → r"))).toBe("(p ∧ q) → r");
    expect(showFull(p("p ∨ q ∧ r"))).toBe("p ∨ (q ∧ r)");
    expect(showFull(p("p → q → r"))).toBe("p → (q → r)");
    expect(showFull(p("p ↔ q → r"))).toBe("p ↔ (q → r)");
    expect(showFull(p("¬p ∧ q"))).toBe("¬p ∧ q");
    expect(showFull(p("¬(p ∧ q)"))).toBe("¬(p ∧ q)");
  });
  it("accepts words, ASCII and symbols alike", () => {
    const forms = ["not p or q implies r iff s", "~p | q -> r <-> s", "¬p ∨ q → r ↔ s", "!p || q => r <=> s", "¬p \\/ q → r ⇔ s"];
    const shown = forms.map((f) => show(p(f)));
    expect(new Set(shown).size).toBe(1);
    expect(show(p("p & q && r /\\ s"))).toBe("((p ∧ q) ∧ r) ∧ s");
    expect(evaluate(p("T ∧ ¬F ∧ 1 ∧ ¬0 ∧ true ∧ ⊤"), {})).toBe(true);
  });
  it("reports errors with positions", () => {
    const err = (s: string) => {
      const r = parseFormula(s);
      return r.ok ? null : r.error;
    };
    expect(err("")?.code).toBe("empty");
    expect(err("p ∧")).toEqual({ code: "missingOperand", pos: 3 });
    expect(err("(p ∨ q")).toEqual({ code: "missingClose", pos: 0 });
    expect(err("p q")).toEqual({ code: "unexpected", symbol: "q", pos: 2 });
    expect(err("p # q")).toEqual({ code: "unknownSymbol", symbol: "#", pos: 2 });
    expect(err("pq ∧ r")).toEqual({ code: "unknownWord", word: "pq", pos: 0 });
    expect(err("p ∧ q ∧ r ∧ s ∧ t ∧ u ∧ v")?.code).toBe("tooManyVars");
    expect(err("(".repeat(40) + "p" + ")".repeat(40))?.code).toBe("tooDeep");
    expect(err("p".repeat(201))?.code).toBe("tooLong");
  });
  it("builds truth tables with sub-formulas in textbook order", () => {
    const table = truthTable(p("(p → q) ∧ ¬q"));
    expect(table.vars).toEqual(["p", "q"]);
    expect(table.rows.map((r) => [r.p, r.q])).toEqual([
      [true, true],
      [true, false],
      [false, true],
      [false, false],
    ]);
    expect(table.columns.map((c) => c.label)).toEqual(["p → q", "¬q", "(p → q) ∧ ¬q"]);
    expect(table.main).toEqual([false, false, false, true]);
    expect(table.classification).toBe("contingent");
    expect(subformulas(p("p ∧ p"))).toHaveLength(1);
  });
  it("classifies tautologies and contradictions and tests equivalence", () => {
    expect(truthTable(p("p ∨ ¬p")).classification).toBe("tautology");
    expect(truthTable(p("p ∧ ¬p")).classification).toBe("contradiction");
    expect(classify([true, false])).toBe("contingent");
    expect(differences(p("¬(p ∧ q)"), p("¬p ∨ ¬q")).rows).toEqual([]);
    expect(differences(p("p → q"), p("¬q → ¬p")).rows).toEqual([]);
    expect(differences(p("p → q"), p("q → p")).rows).toEqual([1, 2]);
    expect(differences(p("p ∧ (q ∨ r)"), p("(p ∧ q) ∨ (p ∧ r)")).rows).toEqual([]);
    expect(assignments(["a", "b", "c"])).toHaveLength(8);
    expect(evaluate(p("p ⊕ q"), { p: true, q: true })).toBe(false);
  });
});

/* ------------------------------------------------------------------------ */
/* Probability                                                               */
/* ------------------------------------------------------------------------ */

describe("seeded simulations", () => {
  it("are deterministic per seed and differ between seeds", () => {
    const a = mulberry32(42);
    const b = mulberry32(42);
    const xs = Array.from({ length: 5 }, () => a());
    expect(Array.from({ length: 5 }, () => b())).toEqual(xs);
    for (const x of xs) expect(x >= 0 && x < 1).toBe(true);
    expect(seedFor("coin", 0)).not.toBe(seedFor("coin", 1));
    expect(seedFor("coin", 0)).not.toBe(seedFor("dice", 0));
    expect(Array.from(flipCoins(7, 50))).toEqual(Array.from(flipCoins(7, 50)));
  });
  it("converge towards the exact values (fixed seeds, large samples)", () => {
    const heads = flipCoins(1, 20000).reduce((s, v) => s + v, 0) / 20000;
    expect(Math.abs(heads - 0.5)).toBeLessThan(0.02);
    const faces = tally(rollDice(2, 30000), 30000, 1, 6).map((c) => c / 30000);
    for (const f of faces) expect(Math.abs(f - 1 / 6)).toBeLessThan(0.02);
    const sums = tally(rollDice(3, 36000, 2), 36000, 2, 12);
    expect(Math.abs(sums[5] / 36000 - 6 / 36)).toBeLessThan(0.015);
    const stick = montyHall(4, 20000).reduce((s, v) => s + v, 0) / 20000;
    expect(Math.abs(stick - 1 / 3)).toBeLessThan(0.02);
    const shared = birthdayGroups(5, 5000, 23).reduce((s, v) => s + v, 0) / 5000;
    expect(Math.abs(shared - birthdayExact(23))).toBeLessThan(0.03);
    const n = dropNeedles(6, 20000);
    const crossings = n.crosses.reduce((s, v) => s + v, 0);
    const est = buffonEstimate(crossings, 20000);
    expect(Math.abs((est.estimate ?? 0) - Math.PI)).toBeLessThan(3 * (est.halfWidth ?? 1));
    const walks = randomWalks(7, 2000, 100, 3);
    expect(walks.paths).toHaveLength(3);
    expect(Math.abs(Math.sqrt(walks.sumSq[100] / 2000) - 10)).toBeLessThan(0.8);
    const board = galton(8, 4000, 10);
    const mean = board.bins.reduce((s, v) => s + v, 0) / 4000;
    expect(Math.abs(mean - 5)).toBeLessThan(0.15);
  });
  it("Monty Hall: the host never opens the pick or the car", () => {
    const rng = mulberry32(9);
    for (let i = 0; i < 300; i++) {
      const g = montyGame(rng);
      expect(g.opened).not.toBe(g.pick);
      expect(g.opened).not.toBe(g.car);
    }
    expect(montyGame(mulberry32(1), 2).pick).toBe(2);
  });
  it("running proportions end at the full proportion", () => {
    const bits = flipCoins(11, 777);
    const series = runningProportion(bits, 777);
    const last = series[series.length - 1];
    expect(last.n).toBe(777);
    expect(last.p).toBeCloseTo(bits.reduce((s, v) => s + v, 0) / 777);
    expect(series.length).toBeLessThan(250);
  });
});

describe("exact probabilities", () => {
  it("binomial and dice distributions sum to 1", () => {
    expect(binomialCoefficient(10, 5)).toBe(252);
    expect(binomialCoefficient(5, 7)).toBe(0);
    const total = Array.from({ length: 11 }, (_, k) => binomialPmf(10, k)).reduce((s, v) => s + v, 0);
    expect(total).toBeCloseTo(1, 12);
    const dice = Array.from({ length: 11 }, (_, i) => twoDiceExact(i + 2)).reduce((s, v) => s + v, 0);
    expect(dice).toBeCloseTo(1, 12);
    expect(twoDiceExact(7)).toBeCloseTo(1 / 6);
    expect(twoDiceExact(13)).toBe(0);
  });
  it("birthday problem", () => {
    expect(birthdayExact(1)).toBe(0);
    expect(birthdayExact(22)).toBeLessThan(0.5);
    expect(birthdayExact(23)).toBeCloseTo(0.5073, 4);
    expect(birthdayExact(366)).toBe(1);
  });
  it("Buffon estimate handles zero crossings", () => {
    expect(buffonEstimate(0, 10).estimate).toBeNull();
    expect(buffonEstimate(637, 1000).estimate).toBeCloseTo(3.1397, 3);
  });
  it("slider steps include an author's trial count", () => {
    expect(trialSteps(750)).toContain(750);
    expect(trialSteps(1e9)).toContain(10000);
    expect(trialSteps()).toEqual([10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000]);
  });
});

/* ------------------------------------------------------------------------ */
/* Commutative diagrams                                                      */
/* ------------------------------------------------------------------------ */

describe("diagram geometry", () => {
  const square = normaliseDiagram(
    [
      { id: "A", tex: "A", row: 0, col: 0 },
      { id: "B", tex: "B", row: 0, col: 1 },
      { id: "C", tex: "C", row: 1, col: 0 },
      { id: "D", tex: "D", row: 1, col: 1 },
    ],
    [
      { from: "A", to: "B", tex: "f" },
      { from: "A", to: "C", tex: "g", labelSide: "right" },
      { from: "B", to: "D", tex: "h" },
      { from: "C", to: "D", tex: "k", style: "dashed" },
    ],
  );
  it("normalises input and skips bad entries", () => {
    const n = normaliseDiagram(
      [{ id: "A", tex: "A", row: 0, col: 0 }, { id: "A", row: 1, col: 1 }, { id: "B", row: "x", col: 0 }, null, { id: "C", row: 2, col: 0 }],
      [{ from: "A", to: "C", style: "wavy", bend: 500 }, { from: "A", to: "Z" }, { from: "A", to: "A" }],
    );
    expect(n.objects.map((o) => o.id)).toEqual(["A", "C"]);
    expect(n.objects[1].tex).toBe("C");
    expect(n.arrows).toHaveLength(1);
    expect(n.arrows[0].style).toBe("solid");
    expect(n.arrows[0].bend).toBe(75);
    expect(n.ignored).toBe(5);
  });
  it("repairs backslashes swallowed by JavaScript string escapes", () => {
    expect(repairTex("A \to B")).toBe("A \\to B");
    expect(repairTex("\frac{1}{2}")).toBe("\\frac{1}{2}");
    expect(repairTex("\beta")).toBe("\\beta");
    expect(repairTex("\\alpha")).toBe("\\alpha");
  });
  it("stops arrows short of the object boxes", () => {
    const L = layoutDiagram(square.objects, square.arrows, "md");
    for (const s of L.arrows) {
      const from = L.nodes.find((n) => n.id === s.arrow.from)!;
      const to = L.nodes.find((n) => n.id === s.arrow.to)!;
      const outside = (p: { x: number; y: number }, n: typeof from) => Math.abs(p.x - n.cx) > n.hw || Math.abs(p.y - n.cy) > n.hh;
      expect(outside(s.start, from)).toBe(true);
      expect(outside(s.end, to)).toBe(true);
      expect(s.heads).toHaveLength(1);
    }
    // everything fits in the viewBox
    const vb = L.viewBox;
    for (const n of L.nodes) {
      expect(n.cx - n.hw).toBeGreaterThanOrEqual(vb.x);
      expect(n.cx + n.hw).toBeLessThanOrEqual(vb.x + vb.w);
    }
  });
  it("places labels on the requested side (tikz-cd convention)", () => {
    const L = layoutDiagram(square.objects, square.arrows, "md");
    const [f, g, h] = L.arrows;
    expect(f.label!.cy).toBeLessThan(f.start.y); // left of a rightward arrow = above
    expect(g.label!.cx).toBeLessThan(g.start.x); // right of a downward arrow = screen left
    expect(h.label!.cx).toBeGreaterThan(h.start.x); // left of a downward arrow = screen right
  });
  it("separates parallel pairs and puts their labels outside", () => {
    const n = normaliseDiagram(
      [
        { id: "A", tex: "A", row: 0, col: 0 },
        { id: "B", tex: "B", row: 0, col: 1 },
      ],
      [
        { from: "A", to: "B", tex: "f" },
        { from: "A", to: "B", tex: "g" },
      ],
    );
    const [f, g] = layoutDiagram(n.objects, n.arrows).arrows;
    expect(f.start.y).toBeLessThan(g.start.y); // first-listed on top
    expect(f.label!.cy).toBeLessThan(f.start.y);
    expect(g.label!.cy).toBeGreaterThan(g.start.y);
    // an adjunction pair in opposite directions also separates
    const adj = normaliseDiagram(n.objects, [
      { from: "A", to: "B", tex: "F" },
      { from: "B", to: "A", tex: "G" },
    ]);
    const [F, G] = layoutDiagram(adj.objects, adj.arrows).arrows;
    expect(F.start.y).toBeLessThan(G.start.y);
    expect(G.label!.cy).toBeGreaterThan(G.start.y);
  });
  it("bends arrows to the left for positive bend", () => {
    const n = normaliseDiagram(
      [
        { id: "A", tex: "A", row: 0, col: 0 },
        { id: "B", tex: "B", row: 0, col: 2 },
      ],
      [{ from: "A", to: "B", tex: "f", bend: 30 }],
    );
    const [f] = layoutDiagram(n.objects, n.arrows).arrows;
    const mid = bezier(f.start, f.control, f.end, 0.5);
    expect(mid.y).toBeLessThan(f.start.y - 10);
    expect(f.shafts[0]).toContain("Q");
  });
  it("draws every arrow style", () => {
    const objs = [
      { id: "A", tex: "A", row: 0, col: 0 },
      { id: "B", tex: "B", row: 0, col: 1 },
    ];
    const shape = (style: string) => {
      const n = normaliseDiagram(objs, [{ from: "A", to: "B", style }]);
      return layoutDiagram(n.objects, n.arrows).arrows[0];
    };
    expect(shape("double").shafts).toHaveLength(2);
    expect(shape("epi").heads).toHaveLength(2);
    expect(shape("hook").hook).toBeDefined();
    expect(shape("iso").iso).toBeDefined();
    expect(shape("solid").shafts).toHaveLength(1);
  });
  it("estimates TeX widths sensibly", () => {
    expect(measureTex("A").w).toBeLessThan(measureTex("A \\times B").w);
    expect(measureTex("A \\times B").w).toBeGreaterThan(2.3);
    expect(measureTex("A \\times B").w).toBeLessThan(3.2);
    expect(measureTex("X_1").tall).toBeGreaterThan(0);
    expect(measureTex("\\frac{a}{b}").tall).toBeGreaterThan(0.5);
    expect(measureTex("\\mathbb{Z}").w).toBeGreaterThan(0.5);
    expect(measureTex("{unbalanced").w).toBeGreaterThan(0);
  });
  it("reads TeX aloud as plain text", () => {
    expect(texToText("A \\times B")).toBe("A × B");
    expect(texToText("\\mathbb{Z}/n\\mathbb{Z}")).toBe("ℤ/nℤ");
    expect(texToText("X^2")).toBe("X²");
    expect(texToText("A_1")).toBe("A₁");
    expect(texToText("\\alpha \\circ \\beta")).toBe("α ∘ β");
    expect(texToText("\\ker f")).toBe("ker f");
    expect(texToText("f'")).toBe("f′");
    expect(describeDiagram(square.objects, square.arrows)).toContain("f from A to B");
    expect(describeDiagram(square.objects, square.arrows)).toContain("k (dashed) from C to D");
  });
});

/* ------------------------------------------------------------------------ */
/* Server-render smoke tests                                                 */
/* ------------------------------------------------------------------------ */

const render = (el: Parameters<typeof createElement>[0], props: Record<string, unknown> = {}, messages: Record<string, unknown> = en, locale: "en" | "ar" = "en") =>
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  renderToString(createElement(I18nProvider, { locale, messages: messages as any, children: createElement(el as never, props) }));

const noRawKeys = (html: string) => {
  expect(html).not.toMatch(/w\.(graphx|truth|chance)\./);
};

describe("widgets render on the server", () => {
  it("registers all four tags", () => {
    expect(Object.keys(DISCRETE_WIDGETS).sort()).toEqual(["ChanceLab", "CommutativeDiagram", "GraphExplorer", "TruthTable"]);
  });

  it("GraphExplorer: defaults, every preset and mode, and a custom graph", () => {
    const html = render(GraphExplorer);
    expect(html).toContain("<svg");
    noRawKeys(html);
    for (const preset of PRESET_IDS) for (const mode of ["degrees", "walk", "colour", "spanning", "matrix"]) noRawKeys(render(GraphExplorer, { preset, mode }));
    const custom = render(GraphExplorer, {
      nodes: ["Home", "School", "Park", "Shop"],
      edges: [["Home", "School"], ["School", "Park"], ["Park", "Home"], ["Park", "Shop"], ["bad"]],
      positions: [[0, 0], [2, 0], [1, 1.5], [2.5, 2]],
      mode: "walk",
      modes: ["walk", "degrees"],
      title: "Walking around town",
    });
    expect(custom).toContain("Walking around town");
    expect(custom).toContain("School");
    noRawKeys(custom);
    // bad props do not crash
    render(GraphExplorer, { preset: 5, nodes: "abc", edges: [[null, undefined]], positions: "x", mode: "nope", modes: [1, 2] });
    // RTL locale renders too
    noRawKeys(render(GraphExplorer, { preset: "petersen", mode: "colour" }, ar, "ar"));
  });

  it("TruthTable: defaults, comparisons and errors", () => {
    const html = render(TruthTable);
    expect(html).toContain("<table");
    noRawKeys(html);
    const cmp = render(TruthTable, { formula: "not (p and q)", compare: "~p | ~q", showSubformulas: false });
    expect(cmp).toContain("Equivalent");
    noRawKeys(cmp);
    const bad = render(TruthTable, { formula: "p ∧ (q", compare: 42 });
    expect(bad).toContain("never closed");
    noRawKeys(render(TruthTable, { formula: "p -> q", compare: "q -> p" }, ar, "ar"));
  });

  it("ChanceLab: every experiment, with props", () => {
    noRawKeys(render(ChanceLab));
    for (const experiment of EXPERIMENTS) {
      const html = render(ChanceLab, { experiment, experiments: [experiment], trials: 300, n: 12, k: 30 });
      expect(html).toContain("<svg");
      expect(html).toContain("Evidence, not proof");
      noRawKeys(html);
    }
    render(ChanceLab, { experiment: "nope", trials: -5, n: "x", k: 1e9, experiments: "coin" });
    noRawKeys(render(ChanceLab, { experiments: ["birthday", "monty-hall"] }, ar, "ar"));
  });

  it("CommutativeDiagram: defaults and the documented examples", () => {
    expect(renderToString(createElement(CommutativeDiagram, {}))).toContain("<svg");
    const html = renderToString(
      createElement(CommutativeDiagram, {
        objects: [
          { id: "P", tex: "A \\times B", row: 1, col: 1 },
          { id: "A", tex: "A", row: 1, col: 0 },
          { id: "B", tex: "B", row: 1, col: 2 },
          { id: "X", tex: "X", row: 0, col: 1 },
        ],
        arrows: [
          { from: "P", to: "A", tex: "\\pi_1", labelSide: "right" },
          { from: "P", to: "B", tex: "\\pi_2" },
          { from: "X", to: "A", tex: "f", labelSide: "right" },
          { from: "X", to: "B", tex: "g" },
          { from: "X", to: "P", tex: "\\langle f, g\\rangle", style: "dashed" },
        ],
        caption: "The product $A \\times B$.",
        size: "lg",
      }),
    );
    expect(html).toContain("katex");
    expect(html).toContain("foreignObject");
    expect(html).toContain("stroke-dasharray");
    expect(html).toContain("aria-label=\"Diagram with objects A × B, A, B, X.");
    const exact = renderToString(
      createElement(CommutativeDiagram, {
        objects: ["0", "A", "B", "C", "0'"].map((id, i) => ({ id, tex: id === "0'" ? "0" : id, row: 0, col: i })),
        arrows: [
          { from: "0", to: "A" },
          { from: "A", to: "B", tex: "f", style: "hook" },
          { from: "B", to: "C", tex: "g", style: "epi" },
          { from: "C", to: "0'" },
        ],
        size: "sm",
      }),
    );
    expect(exact).toContain("<path");
    const bad = renderToString(createElement(CommutativeDiagram, { objects: [{ id: "A" }, 5], arrows: [{ from: "A", to: "Q" }] }));
    expect(bad).toContain("skipped");
  });
});

describe("docs/widgets/discrete.md", () => {
  const doc = fs.readFileSync(path.resolve(import.meta.dirname, "../docs/widgets/discrete.md"), "utf8");
  const blocks = [...doc.matchAll(/```mdx\n([\s\S]*?)```/g)].map((m) => m[1]);
  it("has copy-pasteable examples for every widget", () => {
    for (const tag of Object.keys(DISCRETE_WIDGETS)) expect(blocks.some((b) => b.includes(`<${tag}`)), tag).toBe(true);
    expect(blocks.length).toBeGreaterThanOrEqual(16);
  });
  it("every example compiles as MDX and renders without skipped entries", async () => {
    for (const block of blocks) {
      const { default: Content } = await evaluateMdx(block, { ...runtime, development: false });
      const html = renderToString(
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        createElement(I18nProvider, { locale: "en", messages: en as any, children: createElement(Content, { components: DISCRETE_WIDGETS }) }),
      );
      expect(html, block).toMatch(/<svg|<table/);
      expect(html, block).not.toContain("skipped");
      expect(html, block).not.toContain("katex-error");
    }
  });
});
