import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, BookOpen } from "lucide-react";
import { LOCALES } from "@/i18n/config";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getLesson, lessonSlugs } from "@/lib/content";
import { renderExercises } from "@/lib/exercises";
import { href, pageLocale } from "@/lib/href";
import { PageHeader } from "@/components/ui/PageHeader";
import { PracticeBoard } from "@/components/exercises/PracticeBoard";

export const dynamicParams = false;

export function generateStaticParams() {
  return LOCALES.flatMap((locale) => lessonSlugs().filter((slug) => pageLocale(locale, `practice/${slug}`) === locale).map((slug) => ({ locale, slug })));
}

type Params = { params: Promise<{ locale: string; slug: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  return { title: `${t("practice.title")}: ${getLesson(slug, locale).frontmatter.title}` };
}

export default async function LessonPracticePage({ params }: Params) {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  if (!lessonSlugs().includes(slug)) notFound();
  const t = await getT(locale);
  const fm = getLesson(slug, locale).frontmatter;
  const exercises = renderExercises(slug, locale);
  return (
    <Messages locale={locale} ns={["practice", "exercise", "python", "progress"]}>
    <>
      <PageHeader eyebrow={`${t("practice.title")} · ${t(`levels.${fm.level}`)}`} title={fm.title}>
        <div className="mt-6 flex flex-wrap gap-3">
          <Link href={href(locale, "practice")} className="btn btn-ghost btn-sm">
            <ArrowLeft size={14} className="rtl:rotate-180" aria-hidden="true" /> {t("practice.allLessons")}
          </Link>
          <Link prefetch={false} href={href(locale, `math/lessons/${slug}`)} className="btn btn-ghost btn-sm">
            <BookOpen size={14} aria-hidden="true" /> {t("practice.openLesson")}
          </Link>
        </div>
      </PageHeader>
      <div className="container-page py-10">
        <PracticeBoard exercises={exercises} lessons={[{ slug, title: fm.title }]} />
      </div>
    </>
    </Messages>
  );
}
