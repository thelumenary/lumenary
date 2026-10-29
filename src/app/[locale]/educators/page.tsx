import type { Metadata } from "next";
import Link from "next/link";
import { ArrowRight, FileText, Presentation } from "lucide-react";
import { getT, resolveLocale } from "@/i18n/server";
import { getGraph, getLessonsByLevel, getPage } from "@/lib/content";
import { href } from "@/lib/href";
import { ProsePage } from "@/components/site/ProsePage";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  return { title: getPage("educators", await resolveLocale(params)).frontmatter.title };
}

export default async function EducatorsPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const groups = getLessonsByLevel(locale);
  const graph = getGraph();
  return (
    <ProsePage slug="educators" locale={locale} t={t}>
      <div className="mx-auto mt-14 max-w-5xl space-y-14">
        <Link href={href(locale, "educators/overview")} className="card group flex items-center gap-5 p-6 hover:shadow-[var(--shadow-lg)]">
          <span className="flex h-12 w-12 shrink-0 items-center justify-center rounded-xl bg-gold-soft text-gold-ink">
            <Presentation size={24} />
          </span>
          <span>
            <span className="block font-display text-xl font-semibold text-ink">{t("educators.overview")}</span>
            <span className="mt-1 block text-sm text-ink-2">{t("educators.overviewLead")}</span>
          </span>
          <ArrowRight size={18} className="ms-auto shrink-0 text-muted transition-transform group-hover:translate-x-0.5 rtl:rotate-180" />
        </Link>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("educators.worksheets")}</h2>
          <p className="mt-2 text-ink-2">{t("educators.worksheetsLead")}</p>
          {groups.map(({ level, lessons }) => (
            <div key={level} className="mt-8">
              <h3 className="font-display text-xl font-semibold text-ink">{t(`levels.${level}`)}</h3>
              <ul className="mt-3 grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
                {lessons.map((l) => (
                  <li key={l.slug}>
                    <Link prefetch={false} href={href(locale, `educators/worksheets/${l.slug}`)} className="card flex h-full items-center gap-3 p-4 hover:shadow-[var(--shadow-lg)]">
                      <FileText size={20} className="shrink-0 text-sky" />
                      <span>
                        <span className="block font-semibold text-ink">{l.title}</span>
                        <span className="text-xs text-muted">{l.ages}</span>
                      </span>
                    </Link>
                  </li>
                ))}
              </ul>
            </div>
          ))}
        </section>

        <section>
          <h2 className="text-3xl font-semibold text-ink">{t("educators.map")}</h2>
          <p className="mt-2 text-ink-2">{t("educators.mapLead")}</p>
          <div className="mt-5 overflow-x-auto rounded-xl border border-line bg-card">
            <table className="w-full min-w-[56rem] text-start text-sm">
              <thead className="bg-paper-2">
                <tr>
                  <th className="px-3 py-2.5 text-start font-semibold text-ink-2">{t("curriculum.filterSubject")}</th>
                  {graph.levels.map((l) => (
                    <th key={l.id} className="px-3 py-2.5 text-start font-semibold text-ink-2">
                      {l.short}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {graph.subjects.map((s) => (
                  <tr key={s.id} className="border-t border-line align-top">
                    <th className="px-3 py-2.5 text-start font-semibold text-ink">{s.title}</th>
                    {graph.levels.map((l) => {
                      const here = graph.topics.filter((x) => x.subject === s.id && x.level === l.id);
                      return (
                        <td key={l.id} className="px-3 py-2.5">
                          <ul className="space-y-1">
                            {here.map((x) => (
                              <li key={x.id}>
                                <Link prefetch={false} href={x.lesson ? href(locale, `math/lessons/${x.lesson}`) : href(locale, `math/topics/${x.id}`)} className={`text-xs leading-snug hover:underline ${x.status === "implemented" ? "font-bold text-gold-ink" : "text-ink-2"}`}>
                                  {x.title}
                                </Link>
                              </li>
                            ))}
                          </ul>
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </section>
      </div>
    </ProsePage>
  );
}
