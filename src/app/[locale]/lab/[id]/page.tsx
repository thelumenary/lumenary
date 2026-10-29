import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, BookOpen, Sparkles } from "lucide-react";
import { LOCALES } from "@/i18n/config";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getComputeReport, getLesson, getTrail, lessonSlugs, trailSlugs } from "@/lib/content";
import { href } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";
import { PythonBlock } from "@/components/lesson/PythonBlock";

export const dynamicParams = false;

export function generateStaticParams() {
  const ids = (getComputeReport()?.experiments ?? []).map((e) => e.id);
  // Experiment pages are generated in English only; links from other locales point here.
  return ids.map((id) => ({ locale: "en", id }));
}

type Params = { params: Promise<{ locale: string; id: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { id } = await params;
  const exp = getComputeReport()?.experiments.find((e) => e.id === id);
  return { title: exp?.title ?? id, description: exp?.summary };
}

export default async function ExperimentPage({ params }: Params) {
  const { id } = await params;
  const locale = await resolveLocale(params);
  const exp = getComputeReport()?.experiments.find((e) => e.id === id);
  if (!exp) notFound();
  const t = await getT(locale);
  const lessons = new Set(lessonSlugs());
  const trails = new Set(trailSlugs());
  return (
    <Messages locale={locale} ns={["python", "exercise"]}>
    <>
      <PageHeader eyebrow={t("lab.title")} title={exp.title} lead={exp.summary}>
        <div className="mt-6 flex flex-wrap items-center gap-2">
          <Link href={href(locale, "lab")} className="btn btn-ghost btn-sm">
            <ArrowLeft size={14} className="rtl:rotate-180" aria-hidden="true" /> {t("lab.back")}
          </Link>
          {exp.evidence.map((ev) => (
            <span key={ev} className="chip">
              {t(`evidence.${ev}`)}
            </span>
          ))}
        </div>
      </PageHeader>
      <div className="container-page max-w-4xl space-y-8 py-10">
        <PythonBlock t={t} id={exp.id} />
        <section>
          <h2 className="text-xl font-semibold text-ink">{t("lab.usedIn")}</h2>
          <ul className="mt-3 flex flex-wrap gap-2">
            {exp.lessons.map((slug) =>
              lessons.has(slug) ? (
                <li key={slug}>
                  <Link prefetch={false} href={href(locale, `math/lessons/${slug}`)} className="chip hover:text-ink">
                    <BookOpen size={12} aria-hidden="true" /> {getLesson(slug, locale).frontmatter.title}
                  </Link>
                </li>
              ) : trails.has(slug) ? (
                <li key={slug}>
                  <Link prefetch={false} href={href(locale, `math/trails/${slug}`)} className="chip hover:text-ink">
                    <Sparkles size={12} aria-hidden="true" /> {getTrail(slug, locale).frontmatter.title}
                  </Link>
                </li>
              ) : null,
            )}
          </ul>
        </section>
      </div>
    </>
    </Messages>
  );
}
