import { AlertTriangle, BadgeCheck, Bot, CircleDashed, FlaskConical, Languages, ShieldCheck, UserCheck } from "lucide-react";
import type { VerificationLabel } from "@/lib/schema";

const STYLE: Record<VerificationLabel | "awaiting", { cls: string; Icon: typeof ShieldCheck }> = {
  "formally-verified": { cls: "bg-formal-soft text-formal border-formal/30", Icon: ShieldCheck },
  "computationally-tested": { cls: "bg-compute-soft text-compute border-compute/30", Icon: FlaskConical },
  "mathematically-reviewed": { cls: "bg-good-soft text-good border-good/30", Icon: UserCheck },
  "pedagogically-reviewed": { cls: "bg-good-soft text-good border-good/30", Icon: UserCheck },
  "machine-translated": { cls: "bg-warn-soft text-warn border-warn/30", Icon: Languages },
  "translation-reviewed": { cls: "bg-good-soft text-good border-good/30", Icon: Languages },
  experimental: { cls: "bg-warn-soft text-warn border-warn/30", Icon: FlaskConical },
  incomplete: { cls: "bg-paper-2 text-muted border-line", Icon: CircleDashed },
  "ai-drafted": { cls: "bg-paper-2 text-ink-2 border-line-2", Icon: Bot },
  awaiting: { cls: "bg-paper-2 text-muted border-line border-dashed", Icon: AlertTriangle },
};

export function VerificationBadge({ label, text, title }: { label: VerificationLabel | "awaiting"; text: string; title?: string }) {
  const { cls, Icon } = STYLE[label];
  return (
    <span title={title} className={`inline-flex items-center gap-1.5 rounded-full border px-2.5 py-0.5 text-xs font-semibold ${cls}`}>
      <Icon size={13} aria-hidden="true" />
      {text}
    </span>
  );
}

export function StatusDot({ status }: { status: "implemented" | "draft" | "planned" }) {
  if (status === "implemented") return <BadgeCheck size={15} className="text-gold-ink" aria-hidden="true" />;
  return <CircleDashed size={15} className="text-muted" aria-hidden="true" />;
}
