import type { Metadata } from "next";
import Link from "next/link";
import { CheckCircle2, XCircle } from "lucide-react";
import { getT, resolveLocale, formatNumber } from "@/i18n/server";
import { getLeanReport, lessonsByLeanFile } from "@/lib/content";
import { href } from "@/lib/href";
import { LEVEL_IDS } from "@/lib/schema";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("formal.title") };
}

export default async function FormalPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const report = getLeanReport();
  const modules = new Map<string, NonNullable<typeof report>["declarations"]>();
  for (const d of report?.declarations ?? []) {
    const mod = d.file.replace(/^(formal\/)?Lumenary\//, "").replace(/\.lean$/, "");
    modules.set(mod, [...(modules.get(mod) ?? []), d]);
  }
  // Modules grouped by the level of the lesson that cites them.
  const byFile = lessonsByLeanFile(locale);
  const groupMap = new Map<string, { mod: string; decls: NonNullable<typeof report>["declarations"]; lesson?: { title: string; level: string }; exercises: number }[]>();
  for (const [mod, decls] of modules) {
    const lesson = byFile.get(`Lumenary/${mod}.lean`);
    const exercises = (report?.exercises ?? []).filter((e) => e.file === `formal/LumenaryExercises/${mod}.lean`).length;
    const key = lesson?.level ?? "other";
    groupMap.set(key, [...(groupMap.get(key) ?? []), { mod, decls, lesson, exercises }]);
  }
  const groups = [...LEVEL_IDS, "other"].filter((l) => groupMap.has(l)).map((level) => ({ level, mods: groupMap.get(level)! }));
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
          <h2 className="text-3xl font-semibold text-ink">{t("formal.library")}</h2>
          <p className="mt-3 max-w-3xl text-ink-2">{t("formal.modulesLead")}</p>
          <div className="mt-6 space-y-10">
            {groups.map(({ level, mods }) => (
              <div key={level}>
                <h3 className="font-display text-xl font-semibold text-ink">{level === "other" ? t("formal.otherModules") : t(`levels.${level}`)}</h3>
                <ul className="mt-3 grid gap-3 md:grid-cols-2 lg:grid-cols-3">
                  {mods.map(({ mod, decls, lesson, exercises: nEx }) => {
                    const ok = report?.build.success && decls.every((d) => !d.usesSorry);
                    return (
                      <li key={mod}>
                        <Link prefetch={false} href={href(locale, `formal/${mod}`)} className="card flex h-full flex-col gap-2 p-4 hover:shadow-[var(--shadow-lg)]">
                          <span className="flex items-center gap-2">
                            {ok ? <CheckCircle2 size={15} className="shrink-0 text-formal" aria-label={t("verify.formally-verified")} /> : <XCircle size={15} className="shrink-0 text-bad" />}
                            <span className="font-mono text-sm font-semibold text-ink" dir="ltr">
                              Lumenary.{mod}
                            </span>
                          </span>
                          {lesson && <span className="text-sm text-ink-2">{lesson.title}</span>}
                          <span className="mt-auto flex flex-wrap gap-1.5 text-xs">
                            <span className="chip">{t("formal.declarationCount", { n: formatNumber(locale, decls.length) })}</span>
                            {nEx > 0 && <span className="chip">{t("formal.exerciseCount", { n: formatNumber(locale, nEx) })}</span>}
                            <span className="chip">{t(`formal.foundation.${decls.some((d) => d.foundation === "mathlib") ? "mathlib" : "core"}`)}</span>
                          </span>
                        </Link>
                      </li>
                    );
                  })}
                </ul>
              </div>
            ))}
          </div>
        </section>
      </div>
    </>
  );
}
