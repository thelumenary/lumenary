import { createElement, type ComponentType } from "react";
import type { ExperimentId } from "@/lib/experiments";
import { SortingGame } from "@/components/widgets/SortingGame";
import { VennExplorer } from "@/components/widgets/VennExplorer";
import { IntegerLine } from "@/components/widgets/IntegerLine";
import { ArrowDiagram } from "@/components/widgets/ArrowDiagram";
import { CompositionMachine } from "@/components/widgets/CompositionMachine";
import { InverseFinder } from "@/components/widgets/InverseFinder";
import { ClockLab } from "@/components/widgets/ClockLab";
import { RemainderColors } from "@/components/widgets/RemainderColors";
import { BoxesNesting } from "@/components/widgets/BoxesNesting";
import { ArrowComposer } from "@/components/widgets/ArrowComposer";
import { ProductMaps } from "@/components/widgets/ProductMaps";
import { DiagonalBuilder } from "@/components/widgets/DiagonalBuilder";
import { NUMBER_WIDGETS } from "@/components/widgets/registry-number";
import { SHAPE_DATA_WIDGETS } from "@/components/widgets/registry-shape-data";
import { ANALYSIS_WIDGETS } from "@/components/widgets/registry-analysis";
import { DISCRETE_WIDGETS } from "@/components/widgets/registry-discrete";
import { TOPOLOGY_WIDGETS } from "@/components/widgets/registry-topology";


/**
 * Every interactive exploration lessons may use, keyed by its MDX tag name. Kept free of
 * server-only imports so the lesson tests can render lessons with exactly these components.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const WIDGETS: Record<string, ComponentType<any>> = {
  SortingGame,
  VennExplorer,
  IntegerLine,
  ArrowDiagram,
  CompositionMachine,
  InverseFinder,
  ClockLab,
  RemainderColors,
  BoxesNesting,
  ArrowComposer,
  ProductMaps,
  DiagonalBuilder,
  ...NUMBER_WIDGETS,
  ...SHAPE_DATA_WIDGETS,
  ...ANALYSIS_WIDGETS,
  ...DISCRETE_WIDGETS,
  ...TOPOLOGY_WIDGETS,
};

/** A trail experiment: a generic widget with fixed props (trail pages render experiments without props). */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function preset(Widget: ComponentType<any> | undefined, props: Record<string, unknown>, name: string): ComponentType {
  if (!Widget) throw new Error(`trail experiment ${name}: widget is not registered`);
  const Preset = () => createElement(Widget, props);
  Preset.displayName = `Trail(${name})`;
  return Preset;
}

/** Interactive experiments that Wonder Trails can embed by id (see src/lib/experiments.ts). */
export const EXPERIMENTS: Record<ExperimentId, ComponentType> = {
  "inverse-finder": InverseFinder,
  "clock-lab": ClockLab,
  "remainder-colors": RemainderColors,
  "boxes-nesting": BoxesNesting,
  "arrow-composer": ArrowComposer,
  "product-maps": ProductMaps,
  "diagonal-builder": DiagonalBuilder,
  "euler-counter": preset(TOPOLOGY_WIDGETS.EulerCounter, { solids: ["tetrahedron", "cube", "octahedron", "dodecahedron", "icosahedron", "pyramid", "torus"] }, "euler-counter"),
  "sphere-triangles": preset(TOPOLOGY_WIDGETS.CurvedTriangles, { mode: "sphere", modes: ["plane", "sphere", "hyperbolic"] }, "sphere-triangles"),
  "torus-world": preset(TOPOLOGY_WIDGETS.SurfaceGluing, { surface: "torus", surfaces: ["torus", "klein", "sphere", "rp2"] }, "torus-world"),
  "knot-colours": preset(TOPOLOGY_WIDGETS.KnotColoring, {}, "knot-colours"),
  "winding-loops": preset(TOPOLOGY_WIDGETS.WindingNumber, {}, "winding-loops"),
  "halving-series": preset(ANALYSIS_WIDGETS.SequenceLab, { mode: "series", term: "1/2^n", N: 30 }, "halving-series"),
  "prime-sieve": preset(NUMBER_WIDGETS.NumberGrid, { mode: "sieve", size: 120 }, "prime-sieve"),
  "random-walk": preset(DISCRETE_WIDGETS.ChanceLab, { experiment: "random-walk" }, "random-walk"),
  "square-symmetries": preset(SHAPE_DATA_WIDGETS.ShapeExplorer, { shapes: ["square", "equilateral", "rectangle", "hexagon"], show: ["symmetry", "rotation"] }, "square-symmetries"),
  "osculating-circles": preset(TOPOLOGY_WIDGETS.CurveCurvature, { curve: "ellipse" }, "osculating-circles"),
  "kepler-orbits": preset(
    ANALYSIS_WIDGETS.FunctionPlot,
    { mode: "polar", fns: ["1/(1+e*cos(theta))"], params: [{ name: "e", min: 0, max: 0.9, step: 0.05, value: 0.5 }], x: [-11, 3], y: [-5, 5], aspect: "equal", labels: ["orbit, Sun at the origin"] },
    "kepler-orbits",
  ),
};
