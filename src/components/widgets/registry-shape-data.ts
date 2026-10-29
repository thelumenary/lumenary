import type { ComponentType } from "react";
import { AnalogClock } from "./AnalogClock";
import { AreaGrid } from "./AreaGrid";
import { DataChart } from "./DataChart";
import { PatternMaker } from "./PatternMaker";
import { RulerMeasure } from "./RulerMeasure";
import { ShapeExplorer } from "./ShapeExplorer";
import { Spinner } from "./Spinner";

/**
 * Generic geometry, measurement, pattern and data explorations (K–8).
 * Each key is the tag name lessons use in MDX; props are documented in docs/widgets/shape-data.md.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const SHAPE_DATA_WIDGETS: Record<string, ComponentType<any>> = {
  ShapeExplorer,
  AreaGrid,
  AnalogClock,
  RulerMeasure,
  PatternMaker,
  DataChart,
  Spinner,
};
