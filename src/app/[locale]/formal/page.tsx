import type { Metadata } from "next";
import { CheckCircle2, ChevronDown, ExternalLink, XCircle } from "lucide-react";
import { getT, resolveLocale, formatNumber } from "@/i18n/server";
import { getLeanReport, leanRegions } from "@/lib/content";
import { highlight } from "@/lib/highlight";
import { PageHeader } from "@/components/ui/PageHeader";
import { LeanBlock, webEditorUrl } from "@/components/lesson/LeanBlock";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("formal.title") };
}

export default async function FormalPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const report = getLeanReport();
  const regions = leanRegions();
  const modules = new Map<string, NonNullable<typeof report>["declarations"]>();
  for (const d of report?.declarations ?? []) {
    const mod = d.file.replace(/^Lumenary\//, "").replace(/\.lean$/, "");
    modules.set(mod, [...(modules.get(mod) ?? []), d]);
  }
  const exercises = await Promise.all(
    (report?.exercises ?? []).map(async (ex) => {
      const region = ex.region ? regions.get(ex.region) : undefined;
      return { ex, region, html: region ? await highlight(region.code, "lean4") : "" };
    }),
  );
  const counts = {
    total: report?.declarations.length ?? 0,
    library: report?.declarations.filter((d) => d.provenance === "library").length ?? 0,
    independent: report?.declarations.filter((d) => d.provenance === "independent").length ?? 0,
    definition: report?.declarations.filter((d) => d.provenance === "definition").length ?? 0,
  };

  return (
    <>
      <PageHeader eyebrow={t("modes.F")} title={t("formal.title")} lead={t("formal.lead")} />
      <div className="container-page space-y-16 py-12">
        <section className="grid gap-6 lg:grid-cols-[1.2fr_1fr]">
          <div className="card p-6">
            <h2 className="text-2xl font-semibold text-ink">{t("formal.whatIs")}</h2>
            <p className="mt-3 leading-relaxed text-ink-2">{t("formal.whatIsText")}</p>
            <p className="mt-4 rounded-xl bg-paper-2 px-4 py-3 text-sm text-ink-2">{t("formal.scope")}</p>
          </div>
          <div className="card p-6">
            <h2 className="text-2xl font-semibold text-ink">{t("formal.reportTitle")}</h2>
            {report ? (
              <dl className="mt-4 grid grid-cols-[auto_1fr] gap-x-4 gap-y-2 text-sm">
                <dt className="text-muted">{t("formal.result")}</dt>
                <dd className={`flex items-center gap-1.5 font-semibold ${report.build.success ? "text-good" : "text-bad"}`}>
                  {report.build.success ? <CheckCircle2 size={16} /> : <XCircle size={16} />}
                  {report.build.success ? t("formal.success") : t("formal.failure")}
                </dd>
                <dt className="text-muted">{t("formal.toolchain")}</dt>
                <dd className="font-mono text-ink" dir="ltr">
                  {report.toolchain}
                </dd>
                <dt className="text-muted">Mathlib</dt>
                <dd className="text-ink">{report.mathlib ?? "—"}</dd>
                <dt className="text-muted">{t("formal.generated")}</dt>
                <dd className="text-ink">{new Date(report.generatedAt).toISOString().slice(0, 16).replace("T", " ")} UTC</dd>
                <dt className="text-muted">{t("formal.library")}</dt>
                <dd className="text-ink">
                  {formatNumber(locale, counts.total)} · {t("verify.independent")}: {counts.independent} · {t("verify.library")}: {counts.library} · {t("verify.definition")}: {counts.definition}
                </dd>
                <dt className="text-muted">sorry</dt>
                <dd className="text-ink">{report.declarations.filter((d) => d.usesSorry).length}</dd>
              </dl>
            ) : (
              <p className="mt-3 text-ink-2">{t("verify.noReport")}</p>
            )}
          </div>
        </section>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("formal.exercises")}</h2>
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

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("formal.library")}</h2>
          <div className="mt-6 space-y-8">
            {[...modules.entries()].map(([mod, decls]) => (
              <div key={mod}>
                <h3 className="font-display text-xl font-semibold text-ink">
                  {t("formal.module")} <span className="font-mono text-lg">Lumenary.{mod}</span>
                </h3>
                <ul className="mt-3 divide-y divide-line overflow-hidden rounded-xl border border-line bg-card">
                  {decls.map((d) => (
                    <li key={d.name}>
                      <details className="group">
                        <summary className="flex cursor-pointer list-none flex-wrap items-center gap-x-3 gap-y-1 px-4 py-2.5 text-sm [&::-webkit-details-marker]:hidden">
                          {!d.usesSorry && report?.build.success ? <CheckCircle2 size={15} className="text-formal" aria-label={t("verify.formally-verified")} /> : <XCircle size={15} className="text-bad" />}
                          <span className="font-mono font-semibold text-ink" dir="ltr">
                            {d.name.replace("Lumenary.", "")}
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
              </div>
            ))}
          </div>
        </section>
      </div>
    </>
  );
}
