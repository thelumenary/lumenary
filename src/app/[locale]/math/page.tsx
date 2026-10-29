import type { Metadata } from "next";
import Link from "next/link";
import { ChevronDown, Map as MapIcon } from "lucide-react";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getGraph, getLessonsByLevel, getPathways } from "@/lib/content";
import { href } from "@/lib/href";
import { CurriculumBrowser } from "@/components/curriculum/CurriculumBrowser";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("curriculum.title") };
}

export default async function CurriculumPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const graph = getGraph();
  const groups = getLessonsByLevel(locale);
  const pathways = getPathways();
  return (
    <Messages locale={locale} ns={["curriculum"]}>
    <>
      <PageHeader eyebrow={t("meta.siteName")} title={t("curriculum.title")} lead={t("curriculum.lead")}>
        <div className="mt-6 flex flex-wrap gap-3">
          <Link href={href(locale, "math/graph")} className="btn btn-primary">
            <MapIcon size={16} aria-hidden="true" /> {t("nav.graph")}
          </Link>
          <Link prefetch={false} href={href(locale, "math/trails")} className="btn btn-ghost">
            {t("nav.trails")}
          </Link>
        </div>
      </PageHeader>
      <div className="container-page py-12">
        <section>
          <h2 className="text-2xl font-semibold text-ink">{t("curriculum.lessonsAvailable")}</h2>
          <div className="mt-4 divide-y divide-line overflow-hidden rounded-xl border border-line bg-card">
            {groups.map(({ level, lessons }) => (
              <details key={level} className="group" id={`lessons-${level}`}>
                <summary className="flex cursor-pointer list-none items-center gap-3 px-5 py-3.5 [&::-webkit-details-marker]:hidden">
                  <span className="font-display text-lg font-semibold text-ink">{t(`levels.${level}`)}</span>
                  <span className="chip">{lessons.length}</span>
                  <ChevronDown size={16} className="ms-auto text-muted transition-transform group-open:rotate-180" aria-hidden="true" />
                </summary>
                <ol className="grid gap-2 px-5 pb-5 sm:grid-cols-2 lg:grid-cols-3">
                  {lessons.map((l) => (
                    <li key={l.slug}>
                      <Link prefetch={false} href={href(locale, `math/lessons/${l.slug}`)} className="flex items-center justify-between gap-2 rounded-lg border border-line px-3 py-2 text-sm font-semibold text-ink hover:bg-paper-2">
                        <span>{l.title}</span>
                        {locale !== "en" && href(locale, `math/lessons/${l.slug}`).startsWith("/en/") && (
                          <span className="chip shrink-0 text-xs font-normal" lang="en">
                            EN<span className="sr-only"> · {t("curriculum.englishOnly")}</span>
                          </span>
                        )}
                      </Link>
                    </li>
                  ))}
                </ol>
              </details>
            ))}
          </div>
        </section>

        <section className="mt-14">
          <CurriculumBrowser
            topics={graph.topics.map((x) => ({ id: x.id, title: x.title, level: x.level, subject: x.subject, status: x.status, summary: x.summary, objectives: x.objectives, lesson: x.lesson }))}
            levels={graph.levels.map((l) => ({ id: l.id, title: t(`levels.${l.id}`) }))}
            subjects={graph.subjects.map((s) => ({ id: s.id, title: s.title }))}
            pathways={pathways.map((p) => ({ id: p.id, title: p.title, milestones: p.milestones }))}
          />
        </section>

        <section className="mt-16">
          <h2 className="text-3xl font-semibold text-ink">{t("curriculum.pathways")}</h2>
          <p className="mt-3 max-w-2xl text-ink-2">{t("curriculum.pathwaysLead")}</p>
          <div className="mt-6 grid gap-4 md:grid-cols-2">
            {pathways.map((p) => (
              <article key={p.id} className="card p-5">
                <p className="text-xs font-semibold text-gold-ink">{p.audience}</p>
                <h3 className="mt-1 font-display text-xl font-semibold text-ink">{p.title}</h3>
                <p className="mt-2 text-sm leading-relaxed text-ink-2">{p.description}</p>
                <div className="mt-4 flex flex-wrap items-center gap-3 text-sm">
                  <span className="text-muted">{t("curriculum.milestones", { n: p.milestones.length })}</span>
                  <Link href={`${href(locale, "math/graph")}?pathway=${p.id}`} className="link">
                    {t("nav.graph")} →
                  </Link>
                  <Link href={`${href(locale, "math")}?pathway=${p.id}`} className="link">
                    {t("curriculum.filterPathway")} →
                  </Link>
                </div>
              </article>
            ))}
          </div>
        </section>
      </div>
    </>
    </Messages>
  );
}
