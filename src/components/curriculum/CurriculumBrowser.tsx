"use client";

import { BadgeCheck, CircleDashed, Search } from "lucide-react";
import Link from "next/link";
import { useEffect, useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { href } from "@/lib/href";

export interface BrowserTopic {
  id: string;
  title: string;
  level: string;
  subject: string;
  status: "implemented" | "draft" | "planned";
  summary: string;
  objectives: string[];
  lesson?: string;
}

interface Props {
  topics: BrowserTopic[];
  levels: { id: string; title: string }[];
  subjects: { id: string; title: string }[];
  pathways: { id: string; title: string; milestones: string[] }[];
}

export function CurriculumBrowser({ topics, levels, subjects, pathways }: Props) {
  const { t, locale, n } = useI18n();
  const [q, setQ] = useState("");
  const [level, setLevel] = useState("");
  const [subject, setSubject] = useState("");
  const [pathway, setPathway] = useState("");
  const [status, setStatus] = useState("");

  useEffect(() => {
    const p = new URLSearchParams(window.location.search);
    setLevel(p.get("level") ?? "");
    setSubject(p.get("subject") ?? "");
    setPathway(p.get("pathway") ?? "");
  }, []);

  const filtered = useMemo(() => {
    const needle = q.trim().toLocaleLowerCase();
    const ms = pathway ? pathways.find((p) => p.id === pathway)?.milestones ?? [] : null;
    const list = topics.filter(
      (x) =>
        (!level || x.level === level) &&
        (!subject || x.subject === subject) &&
        (!status || x.status === status) &&
        (!ms || ms.includes(x.id)) &&
        (!needle || [x.title, x.summary, ...x.objectives].some((s) => s.toLocaleLowerCase().includes(needle))),
    );
    if (ms) list.sort((a, b) => ms.indexOf(a.id) - ms.indexOf(b.id));
    return list;
  }, [topics, q, level, subject, pathway, status, pathways]);

  const select = (label: string, value: string, set: (v: string) => void, options: { id: string; title: string }[]) => (
    <label className="text-sm font-semibold text-ink-2">
      {label}
      <select className="input mt-1" value={value} onChange={(e) => set(e.target.value)}>
        <option value="">{t("curriculum.any")}</option>
        {options.map((o) => (
          <option key={o.id} value={o.id}>
            {o.title}
          </option>
        ))}
      </select>
    </label>
  );

  const ms = pathway ? pathways.find((p) => p.id === pathway)?.milestones : null;
  const subjectTitle = (id: string) => subjects.find((s) => s.id === id)?.title ?? id;

  return (
    <div>
      <div className="card grid gap-3 p-4 md:grid-cols-[2fr_1fr_1fr_1fr_1fr]">
        <label className="relative text-sm font-semibold text-ink-2">
          <span className="sr-only">{t("curriculum.searchPlaceholder")}</span>
          <Search size={16} className="pointer-events-none absolute start-3 top-[2.05rem] text-muted md:top-[2.05rem]" aria-hidden="true" />
          <span aria-hidden="true">&nbsp;</span>
          <input className="input mt-1 ps-9" placeholder={t("curriculum.searchPlaceholder")} value={q} onChange={(e) => setQ(e.target.value)} />
        </label>
        {select(t("curriculum.filterLevel"), level, setLevel, levels)}
        {select(t("curriculum.filterSubject"), subject, setSubject, subjects)}
        {select(t("curriculum.filterPathway"), pathway, setPathway, pathways)}
        {select(t("curriculum.filterStatus"), status, setStatus, [
          { id: "implemented", title: t("status.implemented") },
          { id: "planned", title: t("status.planned") },
        ])}
      </div>
      <p className="mt-4 text-sm text-muted" aria-live="polite">
        {t("curriculum.results", { n: n(filtered.length) })}
      </p>
      {filtered.length === 0 && <p className="mt-6 text-ink-2">{t("curriculum.noResults")}</p>}

      {ms ? (
        <ol className="mt-4 space-y-2">
          {filtered.map((x) => (
            <li key={x.id}>
              <TopicRow x={x} index={ms.indexOf(x.id) + 1} subject={subjectTitle(x.subject)} locale={locale} t={t} />
            </li>
          ))}
        </ol>
      ) : (
        <div className="mt-4 space-y-10">
          {levels.map((l) => {
            const here = filtered.filter((x) => x.level === l.id);
            if (!here.length) return null;
            return (
              <section key={l.id}>
                <h2 className="sticky top-16 z-10 -mx-1 bg-paper/90 px-1 py-2 font-display text-2xl font-semibold text-ink backdrop-blur">
                  {l.title} <span className="text-base font-normal text-muted">· {n(here.length)}</span>
                </h2>
                <ul className="mt-3 grid gap-3 md:grid-cols-2 xl:grid-cols-3">
                  {here.map((x) => (
                    <li key={x.id}>
                      <TopicRow x={x} subject={subjectTitle(x.subject)} locale={locale} t={t} />
                    </li>
                  ))}
                </ul>
              </section>
            );
          })}
        </div>
      )}
    </div>
  );
}

function TopicRow({ x, subject, locale, t, index }: { x: BrowserTopic; subject: string; locale: string; t: (k: string) => string; index?: number }) {
  const impl = x.status === "implemented";
  return (
    <Link prefetch={false}
      href={x.lesson ? href(locale, `math/lessons/${x.lesson}`) : href(locale, `math/topics/${x.id}`)}
      className={`group flex h-full gap-3 rounded-xl border p-4 transition-shadow hover:shadow-[var(--shadow-lg)] ${impl ? "border-gold/50 bg-gradient-to-br from-gold-soft/70 to-card" : "border-line bg-card"}`}
    >
      {index !== undefined && <span className="flex h-7 w-7 shrink-0 items-center justify-center rounded-full bg-sky text-xs font-bold text-paper">{index}</span>}
      <span className="min-w-0">
        <span className="flex items-center gap-1.5 text-xs font-semibold text-muted">
          {impl ? <BadgeCheck size={14} className="text-gold-ink" aria-hidden="true" /> : <CircleDashed size={14} aria-hidden="true" />}
          {subject} · {impl ? t("status.implemented") : t("status.planned")}
        </span>
        <span className="mt-1 block font-semibold text-ink group-hover:underline">{x.title}</span>
        <span className="mt-1 line-clamp-2 block text-sm leading-snug text-ink-2">{x.summary}</span>
      </span>
    </Link>
  );
}
