import type { Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import type { MdxComponents } from "@/lib/mdx";
import type { RenderedExercise } from "@/components/exercises/types";
import { makeBlocks } from "./blocks";
import { LeanBlock } from "./LeanBlock";
import { PythonBlock } from "./PythonBlock";
import { TrailCard } from "./TrailCard";
import { ExerciseList } from "./Exercises";
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

import type { ExperimentId } from "@/lib/experiments";

export const EXPERIMENTS: Record<ExperimentId, React.ComponentType> = {
  "inverse-finder": InverseFinder,
  "clock-lab": ClockLab,
  "remainder-colors": RemainderColors,
  "boxes-nesting": BoxesNesting,
  "arrow-composer": ArrowComposer,
  "product-maps": ProductMaps,
  "diagonal-builder": DiagonalBuilder,
};

export function makeMdxComponents({ locale, t, exercises = [] }: { locale: Locale; t: TFunction; exercises?: RenderedExercise[] }): MdxComponents {
  return {
    ...makeBlocks(t),
    Lean: (p: { decl?: string; region?: string; title?: string }) => <LeanBlock t={t} {...p} />,
    Python: (p: { id: string; title?: string }) => <PythonBlock t={t} {...p} />,
    Trail: (p: { slug: string }) => <TrailCard locale={locale} t={t} slug={p.slug} />,
    Exercises: () => <ExerciseList exercises={exercises} />,
    SortingGame,
    VennExplorer,
    IntegerLine,
    ArrowDiagram,
    CompositionMachine,
    ...EXPERIMENTS,
    InverseFinder,
    ClockLab,
    RemainderColors,
    BoxesNesting,
    ArrowComposer,
    ProductMaps,
    DiagonalBuilder,
  };
}
