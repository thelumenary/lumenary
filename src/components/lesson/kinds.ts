import { AlertTriangle, BookOpen, Boxes, Compass, Feather, Globe2, Library, Lightbulb, MousePointerClick, Network, PencilLine, PencilRuler, ShieldCheck, Sparkles, Terminal } from "lucide-react";
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
  history: { mode: null, Icon: Globe2 },
  reading: { mode: null, Icon: Library },
} as const satisfies Record<string, { mode: Mode | null; Icon: unknown }>;

export type SectionKind = keyof typeof SECTION_KINDS;
