import { AlertTriangle, Atom, Binary, BookOpen, Boxes, Compass, Cpu, Dices, Donut, Eye, Feather, Globe2, Grid3x3, Hash, Infinity as InfinityIcon, Library, Lightbulb, MousePointerClick, Network, PencilLine, PencilRuler, ShieldCheck, Sparkles, Terminal, Triangle, Variable } from "lucide-react";
import type { Mode } from "@/components/ui/ModeBadge";

export const SECTION_KINDS = {
  motivation: { mode: "H", Icon: Compass },
  intuition: { mode: "H", Icon: Lightbulb },
  definitions: { mode: "H", Icon: BookOpen },
  examples: { mode: "H", Icon: PencilLine },
  human: { mode: "H", Icon: Feather },
  proof: { mode: "H", Icon: Feather },
  formal: { mode: "F", Icon: ShieldCheck },
  computation: { mode: "C", Icon: Terminal },
  visualization: { mode: null, Icon: MousePointerClick },
  exercises: { mode: null, Icon: PencilRuler },
  misconceptions: { mode: "H", Icon: AlertTriangle },
  trails: { mode: null, Icon: Sparkles },
  sets: { mode: "H", Icon: Boxes },
  categories: { mode: "H", Icon: Network },
  viewpoints: { mode: "H", Icon: Eye },
  history: { mode: null, Icon: Globe2 },
  reading: { mode: null, Icon: Library },
} as const satisfies Record<string, { mode: Mode | null; Icon: unknown }>;

export type SectionKind = keyof typeof SECTION_KINDS;

/**
 * Mathematical viewpoints a lesson can be seen through (the `<Viewpoint lens="…">` block).
 * Higher-level lessons must not see everything through set theory and category theory alone:
 * the topologist's, geometer's, analyst's, algebraist's and other views are first-class.
 */
export const LENSES = {
  sets: { Icon: Boxes },
  categories: { Icon: Network },
  topology: { Icon: Donut },
  geometry: { Icon: Triangle },
  analysis: { Icon: InfinityIcon },
  algebra: { Icon: Variable },
  "number-theory": { Icon: Hash },
  combinatorics: { Icon: Grid3x3 },
  probability: { Icon: Dices },
  logic: { Icon: Binary },
  computation: { Icon: Cpu },
  physics: { Icon: Atom },
} as const;

export type Lens = keyof typeof LENSES;
