import { describe, expect, it } from "vitest";
import { createElement } from "react";
import { renderToString } from "react-dom/server";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import ar from "@/i18n/messages/ar.json";
import { TOPOLOGY_WIDGETS } from "@/components/widgets/registry-topology";
import { SOLID_IDS, counts, getSolid, signedVolume, viewSolid, convexHullFaces } from "@/components/widgets/lib/topo-polyhedra";
import {
  planeAngles,
  fromLatLon,
  sphereAngles,
  sphereAreaNumeric,
  sphereAreaFormula,
  hypAngles,
  hypAreaNumeric,
  geodesic,
  hypEndpoints,
  hypSegment,
} from "@/components/widgets/lib/topo-curvedtri";
import { SURFACES, SURFACE_IDS, SIDES, applyAffine, detM2, isMirrored, makeWalker, move, partnerSide, sideArrow, squareEuler, turn, heading, toTile } from "@/components/widgets/lib/topo-gluing";
import { KNOT_IDS, KNOT_INFO, allColourings, checkColouring, getDiagram, linkingNumber, type Colour } from "@/components/widgets/lib/topo-knots";
import { LOOP_IDS, DEFAULT_PUNCTURES, contourIntegral, presetLoop, resampleClosed, windingNumber, windingTurns } from "@/components/widgets/lib/topo-winding";
import { CURVES, DEFAULT_PARAMS, frameAt, sampleCurve, sanitizeParams } from "@/components/widgets/lib/topo-curves";
import { IDENTITY3, dragRotate, mul3, transpose3, type V2, type V3 } from "@/components/widgets/lib/topo-vec";

const PI = Math.PI;
const deg = (r: number) => (r * 180) / PI;

describe("polyhedra (EulerCounter)", () => {
  const expected: Record<string, [number, number, number, number]> = {
    tetrahedron: [4, 6, 4, 2],
    cube: [8, 12, 6, 2],
    octahedron: [6, 12, 8, 2],
    dodecahedron: [20, 30, 12, 2],
    icosahedron: [12, 30, 20, 2],
    prism: [6, 9, 5, 2],
    pyramid: [5, 8, 5, 2],
    torus: [16, 32, 16, 0],
    doubleTorus: [32, 64, 30, -2],
  };
  for (const id of SOLID_IDS) {
    it(`${id}: V, E, F and χ`, () => {
      const c = counts(getSolid(id));
      expect([c.V, c.E, c.F, c.chi]).toEqual(expected[id]);
      expect(c.chi).toBe(2 - 2 * getSolid(id).genus);
    });
    it(`${id}: closed, consistently oriented outward`, () => {
      const s = getSolid(id);
      // every directed edge appears exactly once, and its reverse exactly once
      const directed = new Map<string, number>();
      for (const f of s.faces) f.forEach((a, i) => {
        const k = `${a}>${f[(i + 1) % f.length]}`;
        directed.set(k, (directed.get(k) ?? 0) + 1);
      });
      for (const [k, n] of directed) {
        expect(n, k).toBe(1);
        const [a, b] = k.split(">");
        expect(directed.get(`${b}>${a}`), k).toBe(1);
      }
      expect(signedVolume(s.vertices, s.faces)).toBeGreaterThan(0);
      expect(Math.max(...s.vertices.map((v) => Math.hypot(...v)))).toBeCloseTo(1, 9);
    });
  }
  it("faces of the regular solids are regular polygons of the right size", () => {
    expect(getSolid("dodecahedron").faces.every((f) => f.length === 5)).toBe(true);
    expect(getSolid("icosahedron").faces.every((f) => f.length === 3)).toBe(true);
    expect(getSolid("cube").faces.every((f) => f.length === 4)).toBe(true);
  });
  it("convex hull ignores interior points", () => {
    const pts: V3[] = [[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1], [0, 0, 0]];
    expect(convexHullFaces(pts)).toHaveLength(4);
  });
  it("viewing a convex solid: front faces never overlap and back edges are hidden", () => {
    const s = getSolid("cube");
    const v = viewSolid(s, dragRotate(dragRotate(IDENTITY3, 0.5, 0), 0, 0.4)); // a general view: three faces visible
    expect(v.front.filter(Boolean)).toHaveLength(3);
    expect(v.hiddenEdge.filter(Boolean)).toHaveLength(3);
    expect(v.vertexFront.filter((x) => !x)).toHaveLength(1);
  });
  it("drag rotations stay orthonormal", () => {
    let m = IDENTITY3;
    for (let i = 0; i < 500; i++) m = dragRotate(m, 0.037, -0.021);
    const p = mul3(m, transpose3(m));
    IDENTITY3.forEach((x, i) => expect(p[i]).toBeCloseTo(x, 9));
  });
});

describe("curved triangles", () => {
  it("plane: angle sum is π", () => {
    const tris: [V2, V2, V2][] = [
      [[0, 0], [4, 0], [1, 3]],
      [[-2, -1], [3, 2], [0.5, 4]],
      [[0, 0], [1, 0], [0, 1]],
    ];
    for (const [a, b, c] of tris) {
      const s = planeAngles(a, b, c).reduce((x, y) => x + y, 0);
      expect(s).toBeCloseTo(PI, 12);
    }
  });
  it("sphere: the octant triangle has three right angles and area π/2 (1/8 of 4π)", () => {
    const A = fromLatLon(90, 0);
    const B = fromLatLon(0, 0);
    const C = fromLatLon(0, 90);
    const angles = sphereAngles(A, B, C);
    angles.forEach((x) => expect(deg(x)).toBeCloseTo(90, 9));
    expect(sphereAreaNumeric(A, B, C)).toBeCloseTo(PI / 2, 4);
    expect(sphereAreaFormula(A, B, C)).toBeCloseTo(PI / 2, 12);
  });
  it("sphere: angle excess equals area (Girard) for assorted triangles", () => {
    const cases: [number, number][][] = [
      [[10, 0], [-5, 20], [30, 40]],
      [[60, -30], [-20, 10], [5, 120]],
      [[1, 0], [0, 1], [0, 0]],
      [[-70, 0], [-10, 100], [40, -120]],
    ];
    for (const c of cases) {
      const [A, B, C] = c.map(([la, lo]) => fromLatLon(la, lo));
      const excess = sphereAngles(A, B, C).reduce((x, y) => x + y, 0) - PI;
      expect(excess).toBeGreaterThan(0);
      expect(sphereAreaNumeric(A, B, C)).toBeCloseTo(excess, 3);
      expect(sphereAreaFormula(A, B, C)).toBeCloseTo(excess, 9);
    }
  });
  it("hyperbolic: geodesics are orthogonal to the boundary circle", () => {
    const p: V2 = [0.3, 0.2];
    const q: V2 = [-0.5, 0.4];
    const g = geodesic(p, q);
    expect(g.kind).toBe("arc");
    if (g.kind === "arc") {
      expect(Math.hypot(p[0] - g.c[0], p[1] - g.c[1])).toBeCloseTo(g.r, 9);
      expect(Math.hypot(q[0] - g.c[0], q[1] - g.c[1])).toBeCloseTo(g.r, 9);
      expect(g.c[0] ** 2 + g.c[1] ** 2).toBeCloseTo(1 + g.r ** 2, 9); // orthogonality
    }
    for (const e of hypEndpoints(p, q)) expect(Math.hypot(...e)).toBeCloseTo(1, 9);
    for (const pt of hypSegment(p, q)) expect(Math.hypot(...pt)).toBeLessThan(1);
  });
  it("hyperbolic: angle defect equals area (curvature −1)", () => {
    const cases: [V2, V2, V2][] = [
      [[0, 0], [0.5, 0], [0, 0.5]],
      [[0.6, 0.1], [-0.4, 0.55], [-0.3, -0.6]],
      [[0.85, 0], [-0.42, 0.74], [-0.42, -0.74]],
      [[0.01, 0.02], [0.05, 0.01], [0.03, 0.06]],
    ];
    for (const [a, b, c] of cases) {
      const sum = hypAngles(a, b, c).reduce((x, y) => x + y, 0);
      expect(sum).toBeLessThan(PI);
      expect(hypAreaNumeric(a, b, c)).toBeCloseTo(PI - sum, 3);
    }
  });
  it("hyperbolic: a right-angled triangle at the origin matches the exact formula", () => {
    // legs along the axes from the origin: angle at the origin is exactly 90°
    const [a0] = hypAngles([0, 0], [0.5, 0], [0, 0.5]);
    expect(deg(a0)).toBeCloseTo(90, 9);
  });
});

describe("surface gluing", () => {
  it("re-entry maps glue each side to its partner along the arrows", () => {
    for (const id of SURFACE_IDS) {
      const def = SURFACES[id];
      SIDES.forEach((side, i) => {
        const other = partnerSide(def, side);
        const [p0, p1] = sideArrow(side, def.word[i].exp);
        const [q0, q1] = sideArrow(other, def.word[SIDES.indexOf(other)].exp);
        for (const s of [0, 0.25, 0.7, 1]) {
          const pt: V2 = [p0[0] + (p1[0] - p0[0]) * s, p0[1] + (p1[1] - p0[1]) * s];
          const img = applyAffine(def.exit[side], pt);
          expect(img[0], `${id} ${side} ${s}`).toBeCloseTo(q0[0] + (q1[0] - q0[0]) * s, 12);
          expect(img[1], `${id} ${side} ${s}`).toBeCloseTo(q0[1] + (q1[1] - q0[1]) * s, 12);
        }
        // a point just outside `side` lands just inside `other`
        const mid: V2 = [(p0[0] + p1[0]) / 2, (p0[1] + p1[1]) / 2];
        const out: V2 = [mid[0] + (side === "right" ? 0.01 : side === "left" ? -0.01 : 0), mid[1] + (side === "top" ? 0.01 : side === "bottom" ? -0.01 : 0)];
        const img = applyAffine(def.exit[side], out);
        expect(img[0] >= 0 && img[0] <= 1 && img[1] >= 0 && img[1] <= 1, `${id} ${side}`).toBe(true);
      });
    }
  });
  it("orientability and Euler characteristic", () => {
    const want = { torus: [true, 0], klein: [false, 0], sphere: [true, 2], rp2: [false, 1] } as const;
    for (const id of SURFACE_IDS) {
      const def = SURFACES[id];
      const orientable = SIDES.every((s) => detM2(def.exit[s].m) === 1);
      expect(orientable, id).toBe(want[id][0]);
      expect(def.orientable).toBe(want[id][0]);
      expect(squareEuler(def).chi, id).toBe(want[id][1]);
      expect(def.chi).toBe(want[id][1]);
    }
  });
  it("walking across the Klein bottle's flipped side mirrors the walker; on the torus it never does", () => {
    const k = SURFACES.klein;
    let w = makeWalker([0.9, 0.3], 0);
    const r = move(k, w, [0.2, 0]);
    expect(r.crossings).toHaveLength(1);
    expect(r.walker.p[0]).toBeCloseTo(0.1, 12);
    expect(r.walker.p[1]).toBeCloseTo(0.7, 12);
    expect(isMirrored(r.walker)).toBe(true);
    // crossing back restores it
    expect(move(k, r.walker, [0.2, 0]).crossings).toHaveLength(0);
    w = move(k, r.walker, [1, 0]).walker;
    expect(isMirrored(w)).toBe(false);
    expect(w.p[1]).toBeCloseTo(0.3, 12);
    // torus
    let t = makeWalker([0.5, 0.5], 0.7);
    for (let i = 0; i < 300; i++) t = move(SURFACES.torus, t, [0.05 * heading(t)[0], 0.05 * heading(t)[1]]).walker;
    expect(isMirrored(t)).toBe(false);
  });
  it("the sphere's folds rotate the walker but never mirror it", () => {
    let w = makeWalker([0.4, 0.05], -PI / 2); // heading down
    const r = move(SURFACES.sphere, w, [0, -0.1]);
    expect(r.crossings[0].from).toBe("bottom");
    expect(r.crossings[0].to).toBe("right");
    expect(r.walker.p[0]).toBeCloseTo(0.95, 12);
    expect(r.walker.p[1]).toBeCloseTo(0.6, 12);
    expect(isMirrored(r.walker)).toBe(false);
    w = turn(r.walker, 0.3);
    expect(isMirrored(w)).toBe(false);
  });
  it("the tiling view is consistent: stepping across a side lands in the neighbouring copy", () => {
    for (const id of ["torus", "klein"] as const) {
      const def = SURFACES[id];
      const eps = 0.01;
      const cases: [V2, V2, number, number][] = [
        [[1 + eps, 0.3], [1, 0], 1, 0],
        [[-eps, 0.3], [-1, 0], -1, 0],
        [[0.4, 1 + eps], [0, 1], 0, 1],
        [[0.4, -eps], [0, -1], 0, -1],
      ];
      for (const [outside, , i, j] of cases) {
        const side = outside[0] > 1 ? "right" : outside[0] < 0 ? "left" : outside[1] > 1 ? "top" : "bottom";
        const inside = applyAffine(def.exit[side], outside);
        const plane = toTile(id, i, j, inside);
        expect(plane[0], `${id} ${side}`).toBeCloseTo(outside[0], 12);
        expect(plane[1], `${id} ${side}`).toBeCloseTo(outside[1], 12);
      }
    }
  });
  it("a long walk stays inside the square on every surface", () => {
    for (const id of SURFACE_IDS) {
      let w = makeWalker([0.31, 0.27], 0.61);
      for (let i = 0; i < 2000; i++) {
        const h = heading(w);
        w = move(SURFACES[id], w, [0.037 * h[0], 0.037 * h[1]]).walker;
        expect(w.p[0] >= 0 && w.p[0] <= 1 && w.p[1] >= 0 && w.p[1] <= 1).toBe(true);
        expect(Math.abs(Math.abs(detM2(w.frame)) - 1)).toBeLessThan(1e-9);
      }
    }
  });
});

describe("knot diagrams and tricolouring", () => {
  const want = { unknot: [1, 1, 3], trefoil: [3, 3, 9], figureEight: [4, 4, 3], hopf: [2, 2, 3], cinquefoil: [5, 5, 3] } as const;
  for (const id of KNOT_IDS) {
    it(`${id}: crossings, arcs, number of 3-colourings`, () => {
      const d = getDiagram(id);
      expect(d.crossings).toHaveLength(want[id][0]);
      expect(d.arcs).toHaveLength(want[id][1]);
      expect(allColourings(d)).toHaveLength(want[id][2]);
      expect(d.alternating).toBe(true);
      expect(new Set(d.arcs.map((a) => a.component)).size).toBe(KNOT_INFO[id].components);
      for (const c of d.crossings) for (const a of [c.over, c.underIn, c.underOut]) expect(a >= 0 && a < d.arcs.length).toBe(true);
    });
  }
  it("the trefoil has a non-trivial colouring; the figure-eight knot does not", () => {
    const tre = allColourings(getDiagram("trefoil"));
    expect(tre.some((c) => new Set(c).size === 3)).toBe(true);
    const fig = allColourings(getDiagram("figureEight"));
    expect(fig.every((c) => new Set(c).size === 1)).toBe(true);
  });
  it("checkColouring flags bad crossings and accepts good ones", () => {
    const d = getDiagram("trefoil");
    expect(checkColouring(d, [1, 1, 1]).valid).toBe(true);
    expect(checkColouring(d, [1, 1, 1]).nontrivial).toBe(false);
    expect(checkColouring(d, [1, 2, 3]).nontrivial).toBe(true);
    expect(checkColouring(d, [1, 1, 2]).valid).toBe(false);
    expect(checkColouring(d, [1, 1, 2]).bad).toBeGreaterThan(0);
    expect(checkColouring(d, [0, 0, 0] as Colour[]).complete).toBe(false);
  });
  it("Hopf link has linking number ±1; knots have none", () => {
    expect(Math.abs(linkingNumber(getDiagram("hopf")))).toBe(1);
    expect(linkingNumber(getDiagram("trefoil"))).toBe(0);
  });
});

describe("winding numbers", () => {
  const [p1, p2] = DEFAULT_PUNCTURES;
  it("preset loops wind as designed around the default punctures", () => {
    const want: Record<string, [number, number]> = { circle: [1, 1], figureEight: [-1, 1], twice: [2, 0], miss: [0, 0] };
    for (const id of LOOP_IDS) {
      const loop = presetLoop(id);
      expect(windingNumber(loop, p1), `${id} p1`).toBe(want[id][0]);
      expect(windingNumber(loop, p2), `${id} p2`).toBe(want[id][1]);
    }
  });
  it("argument sum is (numerically) an integer and matches the contour integral", () => {
    for (const id of LOOP_IDS) {
      const loop = presetLoop(id);
      for (const a of [p1, p2, [0.3, 3.9] as V2]) {
        const w = windingTurns(loop, a);
        expect(Math.abs(w - Math.round(w))).toBeLessThan(1e-9);
        const [re, im] = contourIntegral(loop, a);
        expect(re).toBeCloseTo(Math.round(w), 2);
        expect(im).toBeCloseTo(0, 2);
      }
    }
  });
  it("clockwise loops wind negatively; a loop through the puncture has no winding number", () => {
    const cw = presetLoop("circle").reverse();
    expect(windingNumber(cw, [0, 0])).toBe(-1);
    expect(windingNumber(presetLoop("circle"), [3.3, 0])).toBeNull();
  });
  it("resampling preserves the winding number", () => {
    const loop = resampleClosed(presetLoop("twice"), 120);
    expect(loop).toHaveLength(120);
    expect(windingNumber(loop, p1)).toBe(2);
  });
});

describe("curvature of plane curves", () => {
  const P = DEFAULT_PARAMS;
  it("circle of radius R has κ = 1/R and total curvature 2π", () => {
    const smp = sampleCurve(CURVES.circle, { ...P, R: 1.5 });
    smp.kappa.forEach((k) => expect(k).toBeCloseTo(1 / 1.5, 6));
    expect(smp.length).toBeCloseTo(2 * PI * 1.5, 4);
    expect(smp.totalCurvature).toBeCloseTo(2 * PI, 6);
  });
  it("ellipse: curvature at the vertices is a/b² and b/a²", () => {
    const b = 1.1;
    const smp = sampleCurve(CURVES.ellipse, { ...P, b });
    const max = Math.max(...smp.kappa);
    const min = Math.min(...smp.kappa);
    expect(max).toBeCloseTo(2 / (b * b), 3);
    expect(min).toBeCloseTo(b / 4, 3);
    expect(smp.totalCurvature).toBeCloseTo(2 * PI, 6);
  });
  it("Umlaufsatz: turning numbers 1 (limaçon without loop), 2 (with inner loop), 0 (figure-eight)", () => {
    expect(sampleCurve(CURVES.limacon, { ...P, c: 0.5 }).totalCurvature / (2 * PI)).toBeCloseTo(1, 5);
    expect(sampleCurve(CURVES.limacon, { ...P, c: 2 }).totalCurvature / (2 * PI)).toBeCloseTo(2, 5);
    expect(sampleCurve(CURVES.lemniscate, P).totalCurvature / (2 * PI)).toBeCloseTo(0, 5);
    const lim = sampleCurve(CURVES.limacon, { ...P, c: 2 });
    expect(lim.tangentTurn).toBeCloseTo(lim.totalCurvature, 3);
  });
  it("cardioid: cusp detected; the smooth part turns by 3π", () => {
    const smp = sampleCurve(CURVES.cardioid, P);
    expect(smp.singular).toBe(true);
    expect(smp.totalCurvature).toBeCloseTo(3 * PI, 4);
    expect(sampleCurve(CURVES.circle, P).singular).toBe(false);
  });
  it("parabola: total curvature is the change of tangent angle", () => {
    const k = 0.5;
    const smp = sampleCurve(CURVES.parabola, { ...P, k });
    expect(smp.totalCurvature).toBeCloseTo(2 * Math.atan(2 * k * 2.2), 6);
    // vertex curvature 2k
    expect(frameAt(CURVES.parabola, { ...P, k }, smp, 0.5).kappa).toBeCloseTo(2 * k, 4);
  });
  it("osculating circle centre is at distance 1/κ along the normal", () => {
    const smp = sampleCurve(CURVES.circle, { ...P, R: 2 });
    const f = frameAt(CURVES.circle, { ...P, R: 2 }, smp, 0.3);
    const centre = [f.r[0] + f.N[0] / f.kappa, f.r[1] + f.N[1] / f.kappa];
    expect(centre[0]).toBeCloseTo(0, 6);
    expect(centre[1]).toBeCloseTo(0, 6);
  });
  it("sanitizeParams clamps nonsense", () => {
    const p = sanitizeParams({ R: -5, b: Number.NaN, c: 99, ctrl: [[0, 0]] as unknown as [V2, V2, V2, V2] });
    expect(p.R).toBe(0.4);
    expect(p.b).toBe(DEFAULT_PARAMS.b);
    expect(p.c).toBe(2.5);
    expect(p.ctrl).toEqual(DEFAULT_PARAMS.ctrl);
  });
});

// ---------------------------------------------------------------- server rendering (smoke tests)

type Msgs = Parameters<typeof I18nProvider>[0]["messages"];
const render = (tag: string, props: Record<string, unknown>, locale: "en" | "ar" = "en") =>
  renderToString(
    createElement(I18nProvider, {
      locale,
      messages: (locale === "en" ? en : { ...en, ...ar, w: { ...en.w, ...ar.w } }) as Msgs,
      children: createElement(TOPOLOGY_WIDGETS[tag], props),
    }),
  );
const W = (en as unknown as { w: Record<string, { title: string }> }).w;

describe("topology widgets render on the server", () => {
  it("registers all six tags", () => {
    expect(Object.keys(TOPOLOGY_WIDGETS).sort()).toEqual(["CurveCurvature", "CurvedTriangles", "EulerCounter", "KnotColoring", "SurfaceGluing", "WindingNumber"]);
  });
  const ns: Record<string, string> = { EulerCounter: "euler", CurvedTriangles: "curved", SurfaceGluing: "gluing", KnotColoring: "knot", WindingNumber: "winding", CurveCurvature: "curvature" };
  const examples: [string, Record<string, unknown>][] = [
    ["EulerCounter", { solids: ["cube", "torus", "doubleTorus"], askCount: false }],
    ["EulerCounter", { tab: "surfaces", subtitle: "Genus and χ" }],
    ["CurvedTriangles", { mode: "sphere", modes: ["sphere", "hyperbolic"], vertices: [[90, 0], [0, 0], [0, 90]] }],
    ["CurvedTriangles", { mode: "hyperbolic", vertices: { hyperbolic: [[0, 0], [0.5, 0], [0, 0.5]], plane: [[0, 0], [3, 0], [0, 2]] } }],
    ["SurfaceGluing", { surface: "klein", surfaces: ["torus", "klein"], showTiling: true }],
    ["SurfaceGluing", { surface: "rp2" }],
    ["KnotColoring", { knot: "figureEight", knots: ["unknot", "trefoil", "figureEight"] }],
    ["KnotColoring", { knot: "hopf" }],
    ["WindingNumber", { punctures: [[-1.6, 0], [1.6, 0]], loop: "figureEight" }],
    ["WindingNumber", { loop: "twice", loops: ["circle", "twice"] }],
    ["CurveCurvature", { curve: "limacon", curves: ["circle", "limacon", "lemniscate"], showOsculating: false }],
    ["CurveCurvature", { curve: "bezier", params: { ctrl: [[-2, -1], [-1, 2], [1, -2], [2, 1]] } }],
  ];
  for (const tag of Object.keys(ns)) {
    it(`${tag} with default props`, () => {
      const html = render(tag, {});
      expect(html).toContain(W[ns[tag]].title);
      expect(html).toContain("<svg");
    });
  }
  examples.forEach(([tag, props], i) => {
    it(`${tag} with example props #${i + 1}`, () => {
      const html = render(tag, props);
      expect(html.length).toBeGreaterThan(500);
      if (props.subtitle) expect(html).toContain(String(props.subtitle));
    });
  });
  it("uses a custom title and survives nonsense props", () => {
    expect(render("EulerCounter", { title: "Count them!" })).toContain("Count them!");
    const junk: [string, Record<string, unknown>][] = [
      ["EulerCounter", { solids: ["nope", 3], tab: "weird", askCount: "maybe" }],
      ["CurvedTriangles", { mode: "elliptic", modes: "all", vertices: [[1, "x"], null] }],
      ["SurfaceGluing", { surface: "mobius", surfaces: [1, 2] }],
      ["KnotColoring", { knot: "granny", knots: {} }],
      ["WindingNumber", { punctures: [[Number.NaN, 1], "x", [99, -99]], loop: "spiral" }],
      ["CurveCurvature", { curve: "spiral", params: { R: -3, c: "big", ctrl: [[0, 0]] } }],
    ];
    for (const [tag, props] of junk) expect(render(tag, props).length, tag).toBeGreaterThan(500);
  });
  it("renders in Arabic (right-to-left) too", () => {
    for (const tag of Object.keys(ns)) expect(render(tag, {}, "ar"), tag).toContain('dir="ltr"');
  });
});
