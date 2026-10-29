import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, ArrowRight, Check, Clock, Printer } from "lucide-react";
import { LOCALES, LOCALE_META } from "@/i18n/config";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { deriveVerification, getLesson, getLessonList, getTopic, lessonSlugs } from "@/lib/content";
import { renderExercises } from "@/lib/exercises";
import { href, pageLocale } from "@/lib/href";
import { mdInline } from "@/lib/markdown";
import { extractToc, renderMdx } from "@/lib/mdx";
import { widgetMessageNamespaces } from "@/lib/widget-messages";
import { makeMdxComponents } from "@/components/lesson/mdx-components";
import { LensArticle, RecordVisit, Toc } from "@/components/lesson/LessonChrome";
import { TranslationNotice } from "@/components/lesson/TranslationNotice";
import { NarratorAvatar } from "@/components/brand/Narrators";
import { VerificationBadge } from "@/components/ui/Badges";

export const dynamicParams = false;

export function generateStaticParams() {
  // English, plus the locales a lesson is translated into (links elsewhere point to English).
  return LOCALES.flatMap((locale) => lessonSlugs().filter((slug) => pageLocale(locale, `math/lessons/${slug}`) === locale).map((slug) => ({ locale, slug })));
}

type Params = { params: Promise<{ locale: string; slug: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  const { frontmatter } = getLesson(slug, locale);
  return { title: frontmatter.title, description: frontmatter.subtitle };
}

export default async function LessonPage({ params }: Params) {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  if (!lessonSlugs().includes(slug)) notFound();
  const t = await getT(locale);
  const lesson = getLesson(slug, locale);
  const fm = lesson.frontmatter;
  const exercises = renderExercises(slug, locale);
  const content = await renderMdx(lesson.body, makeMdxComponents({ locale, t, exercises }));
  const toc = extractToc(lesson.body);
  const list = getLessonList(locale);
  const index = list.findIndex((l) => l.frontmatter.slug === slug);
  const prev = list[index - 1]?.frontmatter;
  const next = list[index + 1]?.frontmatter;
  // The sidebar lists the lessons of this level; prev/next walk the whole curriculum in order.
  const levelList = list.filter((l) => l.frontmatter.level === fm.level);
  const levelIndex = levelList.findIndex((l) => l.frontmatter.slug === slug);
  const topic = getTopic(fm.topic);
  const prereqs = (topic?.prerequisites ?? []).map((id) => getTopic(id)).filter(Boolean);
  const v = deriveVerification(fm.lean, fm.compute);
  // Content may fall back to another language than the UI: mark it so screen readers and bidi get it right.
  const contentLang = { lang: lesson.locale, dir: LOCALE_META[lesson.locale].dir };

  return (
    <Messages locale={locale} ns={["exercise", "python", "lesson", ...widgetMessageNamespaces(lesson.body)]}>
    <div>
      <RecordVisit kind="lesson" slug={slug} />
      {/* Lesson header */}
      <header className="relative overflow-hidden border-b border-line">
        <div className="bg-grid pointer-events-none absolute inset-0 opacity-40 [mask-image:radial-gradient(ellipse_at_top_right,black,transparent_65%)]" aria-hidden="true" />
        <div className="container-page relative py-10 sm:py-14">
          <nav className="flex flex-wrap items-center gap-2 text-sm text-muted" aria-label="Breadcrumb">
            <Link href={href(locale, "math")} className="hover:text-ink">
              {t("curriculum.title")}
            </Link>
            <span aria-hidden="true">/</span>
            <Link href={`${href(locale, "math")}?level=${fm.level}`} className="hover:text-ink">
              {t(`levels.${fm.level}`)}
            </Link>
            <span aria-hidden="true">/</span>
            <span className="text-ink-2">
              {levelIndex + 1} · {fm.title}
            </span>
          </nav>
          <div className="mt-6 grid gap-10 lg:grid-cols-[1.5fr_1fr]">
            <div>
              <div className="flex flex-wrap items-center gap-2">
                <span className="chip bg-ink text-paper border-ink">{t(`levels.${fm.level}`)}</span>
                <span className="chip">{fm.ages}</span>
                <span className="chip">
                  <Clock size={12} aria-hidden="true" /> {t("lesson.minutes", { n: fm.minutes })}
                </span>
              </div>
              <h1 {...contentLang} className="mt-4 text-4xl font-semibold leading-[1.08] text-ink sm:text-[3.4rem]">{fm.title}</h1>
              <p {...contentLang} className="mt-4 max-w-2xl font-serif text-xl leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(fm.subtitle) }} />
              <div className="mt-6 flex flex-wrap items-center gap-2">
                {v.formallyVerified && <VerificationBadge label="formally-verified" text={`${t("verify.formally-verified")} · ${v.leanVerifiedCount} Lean`} />}
                {v.computationallyTested && <VerificationBadge label="computationally-tested" text={`${t("verify.computationally-tested")} · ${v.computeVerifiedCount} Python`} />}
                <VerificationBadge label="ai-drafted" text={t("verify.ai-drafted")} />
                <VerificationBadge label="awaiting" text={`${t("verify.mathematically-reviewed")}: ${t("verify.awaitingReview")}`} />
              </div>
              {fm.narrators.length > 0 && (
                <div className="mt-6 flex items-center gap-3">
                  <div className="flex -space-x-2 rtl:space-x-reverse">
                    {fm.narrators.map((n) => (
                      <NarratorAvatar key={n} who={n} size={36} className="rounded-full ring-2 ring-paper" />
                    ))}
                  </div>
                  <p className="text-sm text-muted">
                    {t("lesson.narrators")}: {fm.narrators.map((n) => t(`narrators.${n}`)).join(", ")}
                  </p>
                </div>
              )}
            </div>
            <aside className="card self-start p-5">
              <p className="eyebrow">{t("lesson.objectives")}</p>
              <ul {...contentLang} className="mt-3 space-y-2">
                {fm.objectives.map((o) => (
                  <li key={o} className="flex gap-2.5 text-[0.95rem] leading-snug text-ink">
                    <Check size={16} className="mt-0.5 shrink-0 text-good" aria-hidden="true" />
                    <span dangerouslySetInnerHTML={{ __html: mdInline(o) }} />
                  </li>
                ))}
              </ul>
              <p className="eyebrow mt-5">{t("lesson.prerequisites")}</p>
              {prereqs.length === 0 ? (
                <p className="mt-2 text-sm text-ink-2">{t("lesson.noPrerequisites")}</p>
              ) : (
                <ul className="mt-2 flex flex-wrap gap-1.5">
                  {prereqs.map((p) => (
                    <li key={p!.id}>
                      <Link prefetch={false} href={p!.lesson ? href(locale, `math/lessons/${p!.lesson}`) : href(locale, `math/topics/${p!.id}`)} className="chip hover:border-line-2 hover:text-ink">
                        {p!.title}
                        {p!.status !== "implemented" && <span className="text-muted">· {t("status.planned")}</span>}
                      </Link>
                    </li>
                  ))}
                </ul>
              )}
            </aside>
          </div>
          <div className="mt-6 max-w-3xl">
            <TranslationNotice t={t} requested={locale} rendered={lesson.locale} fallback={lesson.fallback} stale={lesson.stale} status={fm.translation.status} />
          </div>
        </div>
      </header>

      <div className="container-page grid gap-10 py-8 lg:grid-cols-[15rem_minmax(0,1fr)] xl:grid-cols-[16rem_minmax(0,46rem)_1fr]">
        {/* Sidebar */}
        <aside className="no-print hidden lg:block">
          <div className="sticky top-24 space-y-8">
            <nav aria-label={t(`levels.${fm.level}`)}>
              <p className="eyebrow mb-3">{t(`levels.${fm.level}`)}</p>
              <ol className="max-h-[50vh] space-y-1 overflow-y-auto pe-1">
                {levelList.map((l, i) => {
                  const current = l.frontmatter.slug === slug;
                  return (
                    <li key={l.frontmatter.slug}>
                      <Link prefetch={false}
                        href={href(locale, `math/lessons/${l.frontmatter.slug}`)}
                        aria-current={current ? "page" : undefined}
                        className={`flex items-center gap-2.5 rounded-lg px-2 py-1.5 text-sm ${current ? "bg-ink text-paper" : "text-ink-2 hover:bg-paper-2"}`}
                      >
                        <span className={`flex h-6 w-6 shrink-0 items-center justify-center rounded-full text-xs font-bold ${current ? "bg-gold text-[#1b1406]" : "bg-paper-2 text-muted"}`}>{i + 1}</span>
                        {l.frontmatter.title}
                      </Link>
                    </li>
                  );
                })}
              </ol>
            </nav>
            <Toc entries={toc} title={t("lesson.contents")} />
            <Link prefetch={false} href={href(locale, `educators/worksheets/${slug}`)} className="btn btn-ghost btn-sm">
              <Printer size={14} aria-hidden="true" /> {t("lesson.printable")}
            </Link>
          </div>
        </aside>

        <article className="min-w-0" {...contentLang}>
          <LensArticle>{content}</LensArticle>
          <nav className="no-print mt-12 grid gap-3 border-t border-line pt-8 sm:grid-cols-2" aria-label={t("lesson.sequence")}>
            {prev ? (
              <Link prefetch={false} href={href(locale, `math/lessons/${prev.slug}`)} className="card group flex items-center gap-3 p-4 hover:shadow-[var(--shadow-lg)]">
                <ArrowLeft size={18} className="text-muted transition-transform group-hover:-translate-x-0.5 rtl:rotate-180" aria-hidden="true" />
                <span>
                  <span className="block text-xs text-muted">{t("lesson.previous")}</span>
                  <span className="font-display text-lg font-semibold text-ink">{prev.title}</span>
                </span>
              </Link>
            ) : (
              <span />
            )}
            {next && (
              <Link prefetch={false} href={href(locale, `math/lessons/${next.slug}`)} className="card group flex items-center justify-end gap-3 p-4 text-end hover:shadow-[var(--shadow-lg)]">
                <span>
                  <span className="block text-xs text-muted">{t("lesson.next")}</span>
                  <span className="font-display text-lg font-semibold text-ink">{next.title}</span>
                </span>
                <ArrowRight size={18} className="text-muted transition-transform group-hover:translate-x-0.5 rtl:rotate-180" aria-hidden="true" />
              </Link>
            )}
          </nav>
        </article>
      </div>
    </div>
    </Messages>
  );
}
