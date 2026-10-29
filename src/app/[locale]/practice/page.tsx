import type { Metadata } from "next";
import Link from "next/link";
import { PencilRuler } from "lucide-react";
import { getT, resolveLocale, formatNumber } from "@/i18n/server";
import { getExercises, getLessonsByLevel } from "@/lib/content";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("practice.title") };
}

export default async function PracticePage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const groups = getLessonsByLevel(locale);
  return (
    <>
      <PageHeader eyebrow={t("meta.siteName")} title={t("practice.title")} lead={t("practice.lead")} />
      <div className="container-page space-y-12 py-10">
        <p className="max-w-3xl text-ink-2">{t("practice.chooseLesson")}</p>
        {groups.map(({ level, lessons }) => (
          <section key={level} aria-labelledby={`practice-${level}`}>
            <h2 id={`practice-${level}`} className="text-2xl font-semibold text-ink">
              {t(`levels.${level}`)}
            </h2>
            <ul className="mt-4 grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
              {lessons.map((l) => {
                const n = getExercises(l.slug, locale).exercises.length;
                return (
                  <li key={l.slug}>
                    <Link prefetch={false} href={href(locale, `practice/${l.slug}`)} className="card flex h-full items-start gap-3 p-4 hover:shadow-[var(--shadow-lg)]">
                      <PencilRuler size={18} className="mt-0.5 shrink-0 text-sky" aria-hidden="true" />
                      <span>
                        <span className="block font-semibold text-ink">{l.title}</span>
                        <span className="text-xs text-muted">{t("practice.exerciseCount", { n: formatNumber(locale, n) })}</span>
                      </span>
                    </Link>
                  </li>
                );
              })}
            </ul>
          </section>
        ))}
      </div>
    </>
  );
}
