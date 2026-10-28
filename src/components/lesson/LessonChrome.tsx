"use client";

import { useEffect, useState } from "react";
import { useI18n } from "@/i18n/client";
import { recordLesson, recordTrail } from "@/lib/progress";
import { MODE_STYLE, type Mode } from "@/components/ui/ModeBadge";

/** Wraps lesson content and lets the learner highlight one reasoning mode. */
export function LensArticle({ children }: { children: React.ReactNode }) {
  const [lens, setLens] = useState<Mode | null>(null);
  return (
    <div data-lens={lens ?? undefined}>
      <LensControl lens={lens} setLens={setLens} />
      {children}
    </div>
  );
}

function LensControl({ lens, setLens }: { lens: Mode | null; setLens: (m: Mode | null) => void }) {
  const { t } = useI18n();
  return (
    <div className="no-print sticky top-[4.5rem] z-20 mb-2 flex w-fit max-w-full flex-nowrap items-center gap-1 overflow-x-auto rounded-full border border-line bg-paper/95 px-1.5 py-1.5 shadow-[var(--shadow)] backdrop-blur-md" role="group" aria-label={t("modes.lensHelp")}>
      <span className="hidden px-2 text-xs font-semibold uppercase tracking-wide text-muted sm:inline">{t("modes.lens")}</span>
      <button type="button" aria-pressed={lens === null} onClick={() => setLens(null)} className={`shrink-0 rounded-full px-3 py-1 text-xs font-semibold ${lens === null ? "bg-ink text-paper" : "text-ink-2 hover:bg-paper-2"}`}>
        {t("modes.all")}
      </button>
      {(["H", "F", "C"] as Mode[]).map((m) => {
        const { Icon, fg, bg } = MODE_STYLE[m];
        return (
          <button key={m} type="button" aria-pressed={lens === m} onClick={() => setLens(lens === m ? null : m)} className={`inline-flex shrink-0 items-center gap-1 rounded-full px-2.5 py-1 text-xs font-semibold ${lens === m ? `${bg} ${fg} ring-1 ring-current` : "text-ink-2 hover:bg-paper-2"}`}>
            <Icon size={13} aria-hidden="true" /> {t(`modes.${m}`)}
          </button>
        );
      })}
    </div>
  );
}

/** Scroll-spy table of contents. */
export function Toc({ entries, title }: { entries: { id: string; title: string }[]; title: string }) {
  const [active, setActive] = useState<string | null>(entries[0]?.id ?? null);
  useEffect(() => {
    // The active section is the last one whose top has scrolled above 30% of the viewport.
    const onScroll = () => {
      const line = window.innerHeight * 0.3;
      let current = entries[0]?.id ?? null;
      for (const e of entries) {
        const el = document.getElementById(e.id);
        if (el && el.getBoundingClientRect().top <= line) current = e.id;
      }
      setActive(current);
    };
    onScroll();
    window.addEventListener("scroll", onScroll, { passive: true });
    return () => window.removeEventListener("scroll", onScroll);
  }, [entries]);
  return (
    <nav aria-label={title}>
      <p className="eyebrow mb-3">{title}</p>
      <ol className="space-y-0.5 border-s border-line">
        {entries.map((e) => (
          <li key={e.id}>
            <a
              href={`#${e.id}`}
              aria-current={active === e.id ? "location" : undefined}
              className={`-ms-px block border-s-2 py-1 ps-3 text-[0.84rem] leading-snug transition-colors ${active === e.id ? "border-gold font-semibold text-ink" : "border-transparent text-muted hover:text-ink"}`}
            >
              {e.title}
            </a>
          </li>
        ))}
      </ol>
    </nav>
  );
}

export function RecordVisit({ kind, slug }: { kind: "lesson" | "trail"; slug: string }) {
  useEffect(() => {
    if (kind === "lesson") recordLesson(slug);
    else recordTrail(slug);
  }, [kind, slug]);
  return null;
}
