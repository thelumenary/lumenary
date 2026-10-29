import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, BookOpen, CheckCircle2, ChevronDown, ExternalLink, XCircle } from "lucide-react";
import { LOCALES } from "@/i18n/config";
import { getT, resolveLocale } from "@/i18n/server";
import { getLeanReport, leanRegions, lessonsByLeanFile } from "@/lib/content";
import { highlight } from "@/lib/highlight";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";
import { LeanBlock, webEditorUrl } from "@/components/lesson/LeanBlock";

export const dynamicParams = false;

const moduleOf = (file: string) => file.replace(/^(formal\/)?Lumenary\//, "").replace(/\.lean$/, "");

function moduleNames(): string[] {
  return [...new Set((getLeanReport()?.declarations ?? []).map((d) => moduleOf(d.file)))];
}

export function generateStaticParams() {
  // Module pages are generated in English only; links from other locales point here.
  return moduleNames().map((module) => ({ locale: "en", module }));
}

type Params = { params: Promise<{ locale: string; module: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { module } = await params;
  return { title: `Lumenary.${module}` };
}

export default async function FormalModulePage({ params }: Params) {
  const { module } = await params;
  const locale = await resolveLocale(params);
  if (!moduleNames().includes(module)) notFound();
  const t = await getT(locale);
  const report = getLeanReport()!;
  const decls = report.declarations.filter((d) => moduleOf(d.file) === module);
  const lesson = lessonsByLeanFile(locale).get(`Lumenary/${module}.lean`);
  const regions = leanRegions();
  const exercises = await Promise.all(
    report.exercises
      .filter((e) => e.file === `formal/LumenaryExercises/${module}.lean`)
      .map(async (ex) => {
        const region = ex.region ? regions.get(ex.region) : undefined;
        return { ex, region, html: region ? await highlight(region.code, "lean4") : "" };
      }),
  );
  const mathlib = decls.some((d) => d.foundation === "mathlib");

  return (
    <>
      <PageHeader eyebrow={t("formal.title")} title={`Lumenary.${module}`} lead={lesson?.title}>
        <div className="mt-6 flex flex-wrap items-center gap-2">
          <Link href={href(locale, "formal")} className="btn btn-ghost btn-sm">
            <ArrowLeft size={14} className="rtl:rotate-180" aria-hidden="true" /> {t("formal.back")}
          </Link>
          {lesson && (
            <Link prefetch={false} href={href(locale, `math/lessons/${lesson.slug}`)} className="btn btn-ghost btn-sm">
              <BookOpen size={14} aria-hidden="true" /> {t("formal.openLesson")}
            </Link>
          )}
          <span className="chip">{t(`formal.foundation.${mathlib ? "mathlib" : "core"}`)}</span>
        </div>
      </PageHeader>
      <div className="container-page max-w-5xl space-y-14 py-10">
        <section>
          <h2 className="text-2xl font-semibold text-ink">{t("formal.library")}</h2>
          <ul className="mt-4 divide-y divide-line overflow-hidden rounded-xl border border-line bg-card">
            {decls.map((d) => (
              <li key={d.name}>
                <details className="group">
                  <summary className="flex cursor-pointer list-none flex-wrap items-center gap-x-3 gap-y-1 px-4 py-2.5 text-sm [&::-webkit-details-marker]:hidden">
                    {!d.usesSorry && report.build.success ? <CheckCircle2 size={15} className="text-formal" aria-label={t("verify.formally-verified")} /> : <XCircle size={15} className="text-bad" />}
                    <span className="font-mono font-semibold text-ink" dir="ltr">
                      {d.name.replace(`Lumenary.${module}.`, "")}
                    </span>
                    <span className="text-xs text-muted">{d.kind}</span>
                    <span className="chip">{t(`verify.${d.provenance}`)}</span>
                    <span className="ms-auto font-mono text-xs text-muted" dir="ltr">
                      {d.axioms.length ? d.axioms.join(", ") : t("verify.noAxioms")}
                    </span>
                    <ChevronDown size={15} className="text-muted transition-transform group-open:rotate-180" />
                  </summary>
                  <div className="px-3 pb-3">
                    <LeanBlock t={t} decl={d.name} />
                  </div>
                </details>
              </li>
            ))}
          </ul>
        </section>

        {exercises.length > 0 && (
          <section>
            <h2 className="text-2xl font-semibold text-ink">{t("formal.exercises")}</h2>
            <p className="mt-3 max-w-3xl text-ink-2">{t("formal.exercisesLead")}</p>
            <div className="mt-6 grid gap-5 lg:grid-cols-2">
              {exercises.map(({ ex, region, html }) => (
                <article key={ex.name} className="overflow-hidden rounded-xl border border-formal/25 bg-card shadow-[var(--shadow)]">
                  <header className="flex flex-wrap items-center gap-2 border-b border-formal/20 bg-formal-soft/60 px-4 py-2.5">
                    <span className="font-mono text-sm font-semibold text-ink" dir="ltr">
                      {ex.name.split(".").pop()}
                    </span>
                    <span className="chip">{ex.elaborates ? `sorry × ${ex.sorryCount}` : t("formal.failure")}</span>
                    {region && (
                      <a href={webEditorUrl(region.file)} target="_blank" rel="noopener noreferrer" className="link ms-auto inline-flex items-center gap-1 text-xs">
                        {t("verify.openInLean")} <ExternalLink size={12} />
                      </a>
                    )}
                  </header>
                  <div className="code-frame" dangerouslySetInnerHTML={{ __html: html }} />
                  {ex.solution && (
                    <details className="group border-t border-line">
                      <summary className="flex cursor-pointer list-none items-center gap-2 px-4 py-2.5 text-sm font-semibold text-formal [&::-webkit-details-marker]:hidden">
                        <ChevronDown size={15} className="transition-transform group-open:rotate-180" /> {t("formal.showSolution")}
                      </summary>
                      <div className="px-3 pb-3">
                        <LeanBlock t={t} decl={ex.solution} />
                      </div>
                    </details>
                  )}
                </article>
              ))}
            </div>
          </section>
        )}
      </div>
    </>
  );
}
