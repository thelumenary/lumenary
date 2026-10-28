"use client";

import { Lightbulb } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";

export function ProgressiveHints({ hints }: { hints: string[] }) {
  const { t } = useI18n();
  const [shown, setShown] = useState(0);
  return (
    <div>
      <ol className="space-y-2.5" aria-live="polite">
        {hints.slice(0, shown).map((h, i) => (
          <li key={i} className="flex gap-3 rounded-xl border border-gold/30 bg-card px-4 py-3 animate-float-up">
            <span className="flex h-6 w-6 shrink-0 items-center justify-center rounded-full bg-gold-soft text-xs font-bold text-gold-ink">{i + 1}</span>
            <span className="text-[0.98rem] leading-relaxed text-ink" dangerouslySetInnerHTML={{ __html: h }} />
          </li>
        ))}
      </ol>
      {shown < hints.length && (
        <button type="button" className="btn btn-ghost btn-sm mt-3" onClick={() => setShown((s) => s + 1)}>
          <Lightbulb size={14} aria-hidden="true" /> {t("trail.revealHint", { n: shown + 1 })}
        </button>
      )}
    </div>
  );
}
