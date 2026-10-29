import type { Metadata } from "next";
import fs from "node:fs";
import path from "node:path";
import Link from "next/link";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import type { Locale } from "@/i18n/config";
import type { TFunction } from "@/i18n/dictionary";
import { getComputeReport, getGraph, getLeanReport, getLessonsByLevel, getPage, getTrailList, ROOT } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";
import { LEVEL_IDS } from "@/lib/schema";
import { ProsePage } from "@/components/site/ProsePage";
import { PrintButton } from "@/components/site/PrintButton";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  return { title: getPage("overview", await resolveLocale(params)).frontmatter.title };
}

function components(locale: Locale, t: TFunction) {
  const graph = getGraph();
  return {
    CurriculumSummary: () => {
      const byLevel = LEVEL_IDS.map((l) => ({ l, all: graph.topics.filter((x) => x.level === l), done: graph.topics.filter((x) => x.level === l && x.status === "implemented") }));
      return (
        <table className="not-prose w-full text-sm">
          <thead>
            <tr className="text-start text-muted">
              <th className="py-1.5 text-start">{t("curriculum.filterLevel")}</th>
              <th className="text-start">{t("home.statTopics")}</th>
              <th className="text-start">{t("status.implemented")}</th>
            </tr>
          </thead>
          <tbody>
            {byLevel.map(({ l, all, done }) => (
              <tr key={l} className="border-t border-line">
                <td className="py-1.5 font-semibold text-ink">{t(`levels.${l}`)}</td>
                <td>{all.length}</td>
                <td>{done.length ? done.map((x) => x.title).join(", ") : "—"}</td>
              </tr>
            ))}
          </tbody>
        </table>
      );
    },
    Progression: ({ subject }: { subject: string }) => {
      const s = graph.subjects.find((x) => x.id === subject);
      return (
        <div className="not-prose">
          <h3 className="mt-6 font-display text-lg font-semibold text-ink">{s?.title}</h3>
          <ol className="mt-2 space-y-1 text-sm">
            {LEVEL_IDS.map((l) => {
              const here = graph.topics.filter((x) => x.subject === subject && x.level === l);
              if (!here.length) return null;
              return (
                <li key={l} className="grid grid-cols-[9rem_1fr] gap-3">
                  <span className="font-semibold text-muted">{t(`levels.${l}`)}</span>
                  <span className="text-ink-2">{here.map((x) => x.title).join(" · ")}</span>
                </li>
              );
            })}
          </ol>
        </div>
      );
    },
    LessonList: () => (
      <div className="not-prose space-y-5">
        {getLessonsByLevel(locale).map(({ level, lessons }) => (
          <div key={level}>
            <p className="text-sm font-bold text-ink">
              {t(`levels.${level}`)} <span className="font-normal text-muted">· {lessons.length}</span>
            </p>
            <ul className="mt-1.5 flex flex-wrap gap-1.5">
              {lessons.map((l) => (
                <li key={l.slug}>
                  <Link prefetch={false} href={href(locale, `math/lessons/${l.slug}`)} className="chip hover:text-ink" title={`${l.lean.length} Lean · ${l.compute.length} Python`}>
                    {l.title}
                  </Link>
                </li>
              ))}
            </ul>
          </div>
        ))}
      </div>
    ),
    TrailList: () => (
      <ul className="not-prose grid gap-2 sm:grid-cols-2">
        {getTrailList(locale).map(({ frontmatter: tr }) => (
          <li key={tr.slug} className="rounded-xl border border-gold/40 bg-gold-soft/40 px-4 py-3">
            <Link prefetch={false} href={href(locale, `math/trails/${tr.slug}`)} className="font-semibold text-ink hover:underline">
              {tr.title}
            </Link>
            <p className="mt-1 text-xs text-ink-2">→ {tr.deeper.map((id) => graph.topics.find((x) => x.id === id)?.title ?? id).join(", ")}</p>
          </li>
        ))}
      </ul>
    ),
    Screenshots: () => {
      const dir = path.join(ROOT, "public/educators/screenshots");
      const files = fs.existsSync(dir) ? fs.readdirSync(dir).filter((f) => f.endsWith(".png")).sort() : [];
      if (!files.length) return <p>Screenshots have not been generated yet (run <code>npm run screenshots</code>).</p>;
      return (
        <div className="not-prose grid gap-4 sm:grid-cols-2">
          {files.map((f) => (
            <figure key={f} className="overflow-hidden rounded-xl border border-line bg-card">
              {/* eslint-disable-next-line @next/next/no-img-element */}
              <img src={`/educators/screenshots/${f}`} alt={f.replace(/^\d+-/, "").replace(/\.png$/, "").replaceAll("-", " ")} loading="lazy" className="w-full" />
              <figcaption className="px-3 py-2 text-xs text-muted">{f.replace(/^\d+-/, "").replace(/\.png$/, "").replaceAll("-", " ")}</figcaption>
            </figure>
          ))}
        </div>
      );
    },
    VerificationSummary: () => {
      const lean = getLeanReport();
      const compute = getComputeReport();
      return (
        <ul>
          <li>
            <strong>Lean:</strong>{" "}
            {lean
              ? `${lean.build.success ? "build succeeded" : "build FAILED"} with ${lean.toolchain} on ${lean.generatedAt.slice(0, 10)}; ${lean.declarations.length} declarations, ${lean.declarations.filter((d) => d.usesSorry).length} using sorry; ${lean.exercises.length} exercises elaborate with sorry placeholders.`
              : "no report."}
          </li>
          <li>
            <strong>Python:</strong>{" "}
            {compute
              ? `${compute.experiments.filter((e) => e.ran && e.testsPassed).length} of ${compute.experiments.length} experiments ran and passed their tests; pytest ${compute.pytest.passed} passed, ${compute.pytest.failed} failed (Python ${compute.python}, ${compute.generatedAt.slice(0, 10)}).`
              : "no report."}
          </li>
          <li>
            <strong>Human review:</strong> none yet. See <Link href={href(locale, "verification")}>the verification page</Link>.
          </li>
        </ul>
      );
    },
  };
}

export default async function OverviewPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  return (
    <Messages locale={locale} ns={["educators"]}>
    <ProsePage slug="overview" locale={locale} t={t} eyebrow={t("educators.overview")} components={components(locale, t)}>
      <div className="mx-auto mt-10 max-w-3xl">
        <PrintButton />
      </div>
    </ProsePage>
    </Messages>
  );
}
