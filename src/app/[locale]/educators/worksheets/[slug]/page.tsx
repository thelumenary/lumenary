import type { Metadata } from "next";
import { notFound } from "next/navigation";
import { LOCALES } from "@/i18n/config";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getLesson, lessonSlugs } from "@/lib/content";
import { pageLocale } from "@/lib/href";
import { renderExercises } from "@/lib/exercises";
import { mdInline } from "@/lib/markdown";
import { LogoMark } from "@/components/brand/Logo";
import { PrintButton } from "@/components/site/PrintButton";

export const dynamicParams = false;

export function generateStaticParams() {
  return LOCALES.flatMap((locale) => lessonSlugs().filter((slug) => pageLocale(locale, `educators/worksheets/${slug}`) === locale).map((slug) => ({ locale, slug })));
}

type Params = { params: Promise<{ locale: string; slug: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  return { title: `${getLesson(slug, locale).frontmatter.title} — worksheet` };
}

export default async function WorksheetPage({ params }: Params) {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  if (!lessonSlugs().includes(slug)) notFound();
  const t = await getT(locale);
  const lesson = getLesson(slug, locale).frontmatter;
  const exercises = renderExercises(slug, locale);
  return (
    <Messages locale={locale} ns={["educators"]}>
    <div className="container-page max-w-3xl py-10 print:max-w-none print:py-0">
      <div className="no-print mb-8 flex flex-wrap items-center justify-between gap-3">
        <p className="text-sm text-muted">{t("educators.worksheetsLead")}</p>
        <PrintButton />
      </div>
      <article className="rounded-2xl border border-line bg-card p-8 print:border-0 print:p-0">
        <header className="flex items-start justify-between gap-4 border-b border-line pb-5">
          <div>
            <p className="text-xs font-semibold uppercase tracking-widest text-muted">
              {t("meta.siteName")} · {t(`levels.${lesson.level}`)}
            </p>
            <h1 className="mt-1 text-3xl font-semibold text-ink">{lesson.title}</h1>
          </div>
          <LogoMark size={36} />
        </header>
        <div className="mt-4 grid grid-cols-2 gap-6 text-sm text-ink-2">
          <p>{t("educators.name")}: ______________________</p>
          <p>{t("educators.date")}: ______________________</p>
        </div>
        <section className="mt-6">
          <p className="text-sm font-semibold text-ink">{t("lesson.objectives")}</p>
          <ul className="mt-2 list-disc ps-5 text-sm text-ink-2">
            {lesson.objectives.map((o) => (
              <li key={o} dangerouslySetInnerHTML={{ __html: mdInline(o) }} />
            ))}
          </ul>
        </section>
        <ol className="mt-8 space-y-8">
          {exercises.map((ex, i) => (
            <li key={ex.id} className="break-inside-avoid">
              <div className="flex gap-3">
                <span className="font-display text-lg font-semibold text-ink">{i + 1}.</span>
                <div className="flex-1">
                  <div className="prose-lumen text-[1rem]" dangerouslySetInnerHTML={{ __html: ex.promptHtml }} />
                  {ex.type === "choice" && (
                    <ul className="mt-2 space-y-1.5 text-[0.95rem]">
                      {ex.options.map((o, k) => (
                        <li key={o.id} className="flex gap-2">
                          <span className="font-semibold">{String.fromCharCode(65 + k)}.</span>
                          <span dangerouslySetInnerHTML={{ __html: o.labelHtml }} />
                        </li>
                      ))}
                    </ul>
                  )}
                  {ex.type === "python" ? (
                    <p className="mt-2 text-xs italic text-muted">{t("modes.C")} — {t("nav.practice")}</p>
                  ) : (
                    <div className="mt-3 h-16 rounded-lg border border-dashed border-line-2" aria-hidden="true" />
                  )}
                </div>
              </div>
            </li>
          ))}
        </ol>
        <footer className="mt-8 border-t border-line pt-3 text-[0.7rem] text-muted">{t("footer.license")}</footer>
      </article>

      <article className="print-break mt-10 rounded-2xl border border-line bg-card p-8 print:border-0 print:p-0">
        <h2 className="text-2xl font-semibold text-ink">
          {t("educators.answerKey")} — {lesson.title}
        </h2>
        <ol className="mt-6 space-y-6">
          {exercises.map((ex, i) => (
            <li key={ex.id} className="break-inside-avoid">
              <p className="font-semibold text-ink">{i + 1}.</p>
              <div className="prose-lumen text-[0.95rem]" dangerouslySetInnerHTML={{ __html: ex.solutionHtml }} />
            </li>
          ))}
        </ol>
      </article>
    </div>
    </Messages>
  );
}
