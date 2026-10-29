import type { Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import type { MdxComponents } from "@/lib/mdx";
import type { RenderedExercise } from "@/components/exercises/types";
import { makeBlocks } from "./blocks";
import { LeanBlock } from "./LeanBlock";
import { PythonBlock } from "./PythonBlock";
import { TrailCard } from "./TrailCard";
import { ExerciseList } from "./Exercises";
import { TopicLink } from "./TopicLink";
import { WIDGETS } from "./widget-map";

export { EXPERIMENTS } from "./widget-map";

export function makeMdxComponents({ locale, t, exercises = [] }: { locale: Locale; t: TFunction; exercises?: RenderedExercise[] }): MdxComponents {
  return {
    ...makeBlocks(t),
    Lean: (p: { decl?: string; region?: string; title?: string }) => <LeanBlock t={t} {...p} />,
    Python: (p: { id: string; title?: string }) => <PythonBlock t={t} {...p} />,
    Trail: (p: { slug: string }) => <TrailCard locale={locale} t={t} slug={p.slug} />,
    Exercises: () => <ExerciseList exercises={exercises} />,
    TopicLink: (p: { id: string; children?: React.ReactNode }) => <TopicLink locale={locale} {...p} />,
    ...WIDGETS,
  };
}
