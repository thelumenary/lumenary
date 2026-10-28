import { Calculator, Lightbulb, ShieldCheck } from "lucide-react";

export type Mode = "H" | "F" | "C";

export const MODE_STYLE: Record<Mode, { fg: string; bg: string; border: string; Icon: typeof Lightbulb }> = {
  H: { fg: "text-human", bg: "bg-human-soft", border: "border-human", Icon: Lightbulb },
  F: { fg: "text-formal", bg: "bg-formal-soft", border: "border-formal", Icon: ShieldCheck },
  C: { fg: "text-compute", bg: "bg-compute-soft", border: "border-compute", Icon: Calculator },
};

export function ModeBadge({ mode, label, compact = false }: { mode: Mode; label: string; compact?: boolean }) {
  const { fg, bg, Icon } = MODE_STYLE[mode];
  return (
    <span className={`inline-flex items-center gap-1.5 rounded-full ${bg} ${fg} ${compact ? "px-1.5 py-0.5" : "px-2.5 py-0.5"} text-xs font-bold tracking-wide`}>
      <Icon size={13} aria-hidden="true" />
      {compact ? <span aria-label={label}>{mode}</span> : label}
    </span>
  );
}

export function ModeDot({ mode }: { mode: Mode }) {
  const color = { H: "bg-human", F: "bg-formal", C: "bg-compute" }[mode];
  return <span className={`inline-block h-2 w-2 rounded-full ${color}`} aria-hidden="true" />;
}
