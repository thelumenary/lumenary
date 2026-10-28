import type { Metadata } from "next";
import Link from "next/link";
import { ArrowRight, Sparkles } from "lucide-react";
import { getT, resolveLocale } from "@/i18n/server";
import { getGraph, getLesson, getTrailList } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("home.trailsTitle") };
}

export default async function TrailsPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const trails = getTrailList(locale).map((x) => x.frontmatter);
  const topics = new Map(getGraph().topics.map((x) => [x.id, x]));
  return (
    <>
      <PageHeader eyebrow={t("trail.optional")} title={t("home.trailsTitle")} lead={t("home.trailsLead")} />
      <div className="container-page py-12">
        <ul className="grid gap-5 md:grid-cols-2">
          {trails.map((tr) => {
            const lesson = getLesson(tr.from.lesson, locale).frontmatter;
            return (
              <li key={tr.slug}>
                <Link
                  href={href(locale, `math/trails/${tr.slug}`)}
                  className="group relative flex h-full flex-col overflow-hidden rounded-2xl border border-gold/35 bg-gradient-to-br from-gold-soft/80 via-card to-card p-6 shadow-[var(--shadow)] transition-shadow hover:shadow-[var(--shadow-lg)]"
                >
                  <span className="flex items-center gap-2 text-xs font-bold uppercase tracking-[0.12em] text-gold-ink">
                    <Sparkles size={14} aria-hidden="true" /> {t(`levels.${tr.level}`)}
                  </span>
                  <span className="mt-2 font-display text-2xl font-semibold text-ink">{tr.title}</span>
                  <span className="mt-2 text-[0.98rem] leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(tr.question) }} />
                  <span className="mt-4 flex flex-wrap items-center gap-1.5 text-xs text-muted">
                    {t("trail.from")} <span className="chip">{lesson.title}</span> →
                    {tr.deeper.slice(0, 3).map((id) => (
                      <span key={id} className="chip">
                        {topics.get(id)?.title ?? id}
                      </span>
                    ))}
                  </span>
                  <span className="mt-auto inline-flex items-center gap-1 pt-5 text-sm font-semibold text-gold-ink">
                    {t("trail.begin")} <ArrowRight size={15} className="transition-transform group-hover:translate-x-0.5 rtl:rotate-180" aria-hidden="true" />
                  </span>
                </Link>
              </li>
            );
          })}
        </ul>
      </div>
    </>
  );
}
