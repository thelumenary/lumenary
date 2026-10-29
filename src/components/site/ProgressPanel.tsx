"use client";

import { Download, ShieldCheck, Trash2, Upload } from "lucide-react";
import Link from "next/link";
import { useRef } from "react";
import { useI18n } from "@/i18n/client";
import { href } from "@/lib/href";
import { clearAll, replaceAll, setEnabled, useProgress, type ProgressStore } from "@/lib/progress";

export function ProgressPanel({ lessons, trails, exerciseCount }: { lessons: { slug: string; title: string }[]; trails: { slug: string; title: string }[]; exerciseCount: number }) {
  const { t, locale, n } = useI18n();
  const { enabled, store } = useProgress();
  const file = useRef<HTMLInputElement>(null);
  const solved = Object.values(store.exercises).filter((e) => e.solved).length;

  const download = () => {
    const blob = new Blob([JSON.stringify(store, null, 2)], { type: "application/json" });
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = "lumenary-progress.json";
    a.click();
    URL.revokeObjectURL(a.href);
  };

  return (
    <div className="space-y-8">
      <div className="card flex flex-wrap items-center gap-4 p-5">
        <ShieldCheck size={22} className={enabled ? "text-good" : "text-muted"} aria-hidden="true" />
        <label className="flex flex-1 cursor-pointer items-center gap-3 font-semibold text-ink">
          <input type="checkbox" className="h-5 w-5 accent-[var(--good)]" checked={enabled} onChange={(e) => setEnabled(e.target.checked)} />
          {t("progress.enable")}
        </label>
        <p className="w-full text-sm text-ink-2">{enabled ? t("progress.enabled") : t("progress.disabled")}</p>
      </div>

      {enabled && (
        <>
          <dl className="grid gap-4 sm:grid-cols-3">
            {[
              [t("progress.lessonsVisited"), `${n(Object.keys(store.lessons).length)} / ${n(lessons.length)}`],
              [t("progress.exercisesSolved"), `${n(solved)} / ${n(exerciseCount)}`],
              [t("progress.trailsExplored"), `${n(Object.keys(store.trails).length)} / ${n(trails.length)}`],
            ].map(([label, value]) => (
              <div key={label} className="card p-5">
                <dt className="text-sm text-muted">{label}</dt>
                <dd className="mt-1 font-display text-3xl font-semibold text-ink">{value}</dd>
              </div>
            ))}
          </dl>
          <div className="grid gap-4 md:grid-cols-2">
            <div className="card p-5">
              <p className="eyebrow">{t("progress.lessonsVisited")}</p>
              <ul className="mt-3 space-y-1.5 text-sm">
                {lessons.map((l) => (
                  <li key={l.slug} className="flex items-center justify-between">
                    <Link prefetch={false} href={href(locale, `math/lessons/${l.slug}`)} className="link">
                      {l.title}
                    </Link>
                    <span className="text-muted">{store.lessons[l.slug] ? "✓" : "—"}</span>
                  </li>
                ))}
              </ul>
            </div>
            <div className="card p-5">
              <p className="eyebrow">{t("progress.trailsExplored")}</p>
              <ul className="mt-3 space-y-1.5 text-sm">
                {trails.map((l) => (
                  <li key={l.slug} className="flex items-center justify-between">
                    <Link prefetch={false} href={href(locale, `math/trails/${l.slug}`)} className="link">
                      {l.title}
                    </Link>
                    <span className="text-muted">{store.trails[l.slug] ? "✓" : "—"}</span>
                  </li>
                ))}
              </ul>
            </div>
          </div>
          <div className="flex flex-wrap gap-2">
            <button type="button" className="btn btn-ghost btn-sm" onClick={download}>
              <Download size={14} /> {t("progress.export")}
            </button>
            <button type="button" className="btn btn-ghost btn-sm" onClick={() => file.current?.click()}>
              <Upload size={14} /> {t("progress.import")}
            </button>
            <input
              ref={file}
              type="file"
              accept="application/json"
              className="hidden"
              onChange={async (e) => {
                const f = e.target.files?.[0];
                if (!f) return;
                try {
                  replaceAll(JSON.parse(await f.text()) as ProgressStore);
                } catch {}
              }}
            />
            <button
              type="button"
              className="btn btn-ghost btn-sm text-bad"
              onClick={() => {
                if (window.confirm(t("progress.clearConfirm"))) clearAll();
              }}
            >
              <Trash2 size={14} /> {t("progress.clear")}
            </button>
          </div>
        </>
      )}
      <p className="text-sm text-muted">{t("progress.noRankings")}</p>
    </div>
  );
}
