import type { Metadata } from "next";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getExercises, getLessonList, getTrailList } from "@/lib/content";
import { PageHeader } from "@/components/ui/PageHeader";
import { ProgressPanel } from "@/components/site/ProgressPanel";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("progress.title") };
}

export default async function ProgressPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const lessons = getLessonList(locale).map((l) => ({ slug: l.frontmatter.slug, title: l.frontmatter.title }));
  const trails = getTrailList(locale).map((l) => ({ slug: l.frontmatter.slug, title: l.frontmatter.title }));
  const exerciseCount = lessons.reduce((n, l) => n + getExercises(l.slug, locale).exercises.length, 0);
  return (
    <Messages locale={locale} ns={["progress"]}>
    <>
      <PageHeader title={t("progress.title")} lead={t("progress.lead")} />
      <div className="container-page max-w-4xl py-10">
        <ProgressPanel lessons={lessons} trails={trails} exerciseCount={exerciseCount} />
      </div>
    </>
    </Messages>
  );
}
