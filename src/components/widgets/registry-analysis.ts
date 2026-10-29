import type { ComponentType } from "react";
import { CalculusLab } from "./CalculusLab";
import { ComplexPlane } from "./ComplexPlane";
import { FunctionPlot } from "./FunctionPlot";
import { MatrixTransform } from "./MatrixTransform";
import { SequenceLab } from "./SequenceLab";
import { VectorField } from "./VectorField";

/**
 * Function, calculus, sequence, vector-field, complex-plane and matrix explorations.
 * Each key is the tag name lessons use in MDX; props are documented in docs/widgets/analysis.md.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const ANALYSIS_WIDGETS: Record<string, ComponentType<any>> = {
  FunctionPlot,
  CalculusLab,
  SequenceLab,
  VectorField,
  ComplexPlane,
  MatrixTransform,
};
