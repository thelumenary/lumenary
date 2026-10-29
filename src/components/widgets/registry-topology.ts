import type { ComponentType } from "react";
import { EulerCounter } from "./EulerCounter";
import { CurvedTriangles } from "./CurvedTriangles";
import { SurfaceGluing } from "./SurfaceGluing";
import { KnotColoring } from "./KnotColoring";
import { WindingNumber } from "./WindingNumber";
import { CurveCurvature } from "./CurveCurvature";

/**
 * Topology and geometry explorations: Euler characteristic, curvature, surfaces, knots, winding numbers.
 * Each key is the tag name lessons use in MDX; props are documented in docs/widgets/topology.md.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const TOPOLOGY_WIDGETS: Record<string, ComponentType<any>> = {
  EulerCounter,
  CurvedTriangles,
  SurfaceGluing,
  KnotColoring,
  WindingNumber,
  CurveCurvature,
};
