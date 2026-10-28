import type { Metadata } from "next";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getLessonList } from "@/lib/content";
import { renderExercises } from "@/lib/exercises";
import { PageHeader } from "@/components/ui/PageHeader";
import { PracticeBoard } from "@/components/exercises/PracticeBoard";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("practice.title") };
}

export default async function PracticePage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const lessons = getLessonList(locale).map((l) => ({ slug: l.frontmatter.slug, title: l.frontmatter.title }));
  const exercises = lessons.flatMap((l) => renderExercises(l.slug, locale));
  return (
    <Messages locale={locale} ns={["practice", "exercise", "python", "progress"]}>
    <>
      <PageHeader eyebrow={t("meta.siteName")} title={t("practice.title")} lead={t("practice.lead")} />
      <div className="container-page py-10">
        <PracticeBoard exercises={exercises} lessons={lessons} />
      </div>
    </>
    </Messages>
  );
}
