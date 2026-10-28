"use client";

import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";

export interface LangRow {
  tag: string;
  name: string;
  nativeName: string;
  script: string;
  direction: string;
  inclusion: string[];
  translationStatus: string;
  reviewStatus: string;
  regions: string[];
  variantOf?: string;
}

const STATUS_STYLE: Record<string, string> = {
  canonical: "bg-sky-soft text-sky-ink",
  "machine-draft": "bg-warn-soft text-warn",
  none: "bg-paper-2 text-muted",
  partial: "bg-warn-soft text-warn",
  "human-reviewed": "bg-good-soft text-good",
  "math-reviewed": "bg-good-soft text-good",
};

export function LanguageTable({ rows }: { rows: LangRow[] }) {
  const { t, n } = useI18n();
  const [q, setQ] = useState("");
  const [filter, setFilter] = useState<"all" | "demo" | "variety" | "regional-indigenous">("all");
  const list = useMemo(() => {
    const needle = q.trim().toLocaleLowerCase();
    return rows.filter(
      (r) =>
        (filter === "all" || r.inclusion.includes(filter)) &&
        (!needle || [r.tag, r.name, r.nativeName, ...r.regions].some((s) => s.toLocaleLowerCase().includes(needle))),
    );
  }, [rows, q, filter]);
  const filters = [
    ["all", t("languages.filterAll")],
    ["demo", t("languages.filterDemo")],
    ["variety", t("languages.filterVarieties")],
    ["regional-indigenous", t("languages.filterIndigenous")],
  ] as const;
  return (
    <div>
      <div className="flex flex-wrap items-center gap-2">
        <input className="input max-w-xs" placeholder={t("languages.search")} value={q} onChange={(e) => setQ(e.target.value)} aria-label={t("languages.search")} />
        {filters.map(([id, label]) => (
          <button key={id} type="button" aria-pressed={filter === id} onClick={() => setFilter(id)} className={`btn btn-sm ${filter === id ? "btn-primary" : "btn-ghost"}`}>
            {label}
          </button>
        ))}
        <span className="ms-auto text-sm text-muted">{t("languages.total", { n: n(list.length) })}</span>
      </div>
      <div className="mt-4 max-h-[36rem] overflow-auto rounded-xl border border-line bg-card">
        <table className="w-full min-w-[46rem] text-sm">
          <thead className="sticky top-0 bg-paper-2">
            <tr className="text-start text-ink-2">
              {["colLanguage", "colTag", "colScript", "colDir", "colStatus", "colReview", "colRegions"].map((k) => (
                <th key={k} className="px-3 py-2.5 text-start font-semibold">
                  {t(`languages.${k}`)}
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {list.map((r) => (
              <tr key={r.tag} className="border-t border-line">
                <td className="px-3 py-2">
                  <span className="block font-semibold text-ink" lang={r.tag} dir={r.direction}>
                    {r.nativeName}
                  </span>
                  <span className="text-xs text-muted">
                    {r.name}
                    {r.variantOf && ` · ${r.variantOf}`}
                  </span>
                </td>
                <td className="px-3 py-2 font-mono text-xs" dir="ltr">
                  {r.tag}
                </td>
                <td className="px-3 py-2 font-mono text-xs">{r.script}</td>
                <td className="px-3 py-2 text-xs uppercase">{r.direction}</td>
                <td className="px-3 py-2">
                  <span className={`rounded-full px-2 py-0.5 text-xs font-semibold ${STATUS_STYLE[r.translationStatus] ?? ""}`}>{r.translationStatus}</span>
                </td>
                <td className="px-3 py-2 text-xs text-muted">{r.reviewStatus}</td>
                <td className="px-3 py-2 text-xs text-muted">{r.regions.slice(0, 8).join(" ")}{r.regions.length > 8 ? " …" : ""}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}
