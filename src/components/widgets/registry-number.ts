import type { ComponentType } from "react";
import { BalanceScale } from "./BalanceScale";
import { DoubleNumberLine } from "./DoubleNumberLine";
import { FractionBars } from "./FractionBars";
import { NumberGrid } from "./NumberGrid";
import { PlaceValue } from "./PlaceValue";
import { TenFrame } from "./TenFrame";

/**
 * Generic number and arithmetic explorations (K–8).
 * Each key is the tag name lessons use in MDX; props are documented in docs/widgets/number.md.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const NUMBER_WIDGETS: Record<string, ComponentType<any>> = {
  TenFrame,
  PlaceValue,
  FractionBars,
  NumberGrid,
  BalanceScale,
  DoubleNumberLine,
};
