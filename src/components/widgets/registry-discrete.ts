import type { ComponentType } from "react";
import { GraphExplorer } from "./GraphExplorer";
import { TruthTable } from "./TruthTable";
import { ChanceLab } from "./ChanceLab";
import { CommutativeDiagram } from "./CommutativeDiagram";

/**
 * Graph, logic, probability explorations and commutative diagrams.
 * Each key is the tag name lessons use in MDX; props are documented in docs/widgets/discrete.md.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const DISCRETE_WIDGETS: Record<string, ComponentType<any>> = {
  GraphExplorer,
  TruthTable,
  ChanceLab,
  CommutativeDiagram,
};
