import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, ChevronDown, Compass, Sparkles } from "lucide-react";
import { LOCALES, LOCALE_META } from "@/i18n/config";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { deriveVerification, getLesson, getTopic, getTrail, trailSlugs } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";
import { renderMdx } from "@/lib/mdx";
import { EXPERIMENTS, makeMdxComponents } from "@/components/lesson/mdx-components";
import { ProgressiveHints } from "@/components/lesson/ProgressiveHints";
import { RecordVisit } from "@/components/lesson/LessonChrome";
import { TranslationNotice } from "@/components/lesson/TranslationNotice";
import { VerificationBadge } from "@/components/ui/Badges";

export const dynamicParams = false;

export function generateStaticParams() {
  return LOCALES.flatMap((locale) => trailSlugs().map((slug) => ({ locale, slug })));
}

type Params = { params: Promise<{ locale: string; slug: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  const { frontmatter } = getTrail(slug, locale);
  return { title: frontmatter.title };
}

function Step({ n, title, children }: { n: number; title: string; children: React.ReactNode }) {
  return (
    <section className="relative ps-12">
      <span className="absolute start-0 top-0 flex h-8 w-8 items-center justify-center rounded-full border-2 border-gold bg-card font-display text-sm font-bold text-gold-ink">{n}</span>
      <h2 className="font-display text-2xl font-semibold text-ink">{title}</h2>
      <div className="mt-4">{children}</div>
    </section>
  );
}

export default async function TrailPage({ params }: Params) {
  const { slug } = await params;
  const locale = await resolveLocale(params);
  if (!trailSlugs().includes(slug)) notFound();
  const t = await getT(locale);
  const trail = getTrail(slug, locale);
  const fm = trail.frontmatter;
  const lesson = getLesson(fm.from.lesson, locale).frontmatter;
  const body = await renderMdx(trail.body, makeMdxComponents({ locale, t }));
  const Experiment = EXPERIMENTS[fm.experiment as keyof typeof EXPERIMENTS];
  const v = deriveVerification(fm.lean, fm.compute);
  const returnHref = href(locale, `math/lessons/${fm.from.lesson}#${fm.from.label}`);
  const contentLang = { lang: trail.locale, dir: LOCALE_META[trail.locale].dir };

  return (
    <Messages locale={locale} ns={["w", "trail", "python", "exercise"]}>
    <div>
      <RecordVisit kind="trail" slug={slug} />
      <header className="relative overflow-hidden border-b border-gold/30 bg-gradient-to-b from-gold-soft/70 to-paper">
        <div className="pointer-events-none absolute -end-24 -top-24 h-72 w-72 rounded-full bg-gold/20 blur-3xl" aria-hidden="true" />
        <div className="container-page relative max-w-4xl py-12 sm:py-16">
          <div className="flex flex-wrap items-center gap-3 text-sm">
            <span className="inline-flex items-center gap-1.5 font-bold uppercase tracking-[0.14em] text-gold-ink">
              <Sparkles size={15} aria-hidden="true" /> {t("trail.badge")}
            </span>
            <span className="chip">{t("trail.optional")}</span>
            <span className="text-muted">
              {t("trail.from")}{" "}
              <Link href={returnHref} className="link">
                {lesson.title}
              </Link>
            </span>
          </div>
          <h1 {...contentLang} className="mt-4 text-4xl font-semibold leading-tight text-ink sm:text-5xl">
            {fm.title}
          </h1>
          <div className="mt-6">
            <TranslationNotice t={t} requested={locale} rendered={trail.locale} fallback={trail.fallback} stale={trail.stale} status={fm.translation.status} />
          </div>
        </div>
      </header>

      <div className="container-page max-w-4xl space-y-14 py-12" {...contentLang}>
        <Step n={1} title={t("trail.question")}>
          <p className="font-serif text-2xl leading-relaxed text-ink" dangerouslySetInnerHTML={{ __html: mdInline(fm.question) }} />
          <p className="mt-3 text-sm text-muted">{t("trail.takeYourTime")}</p>
        </Step>

        <Step n={2} title={t("trail.experiment")}>
          {Experiment ? <Experiment /> : <p className="text-muted">Experiment “{fm.experiment}” not found.</p>}
        </Step>

        <Step n={3} title={t("trail.hints")}>
          <ProgressiveHints hints={fm.hints.map(mdInline)} />
        </Step>

        <Step n={4} title={t("trail.explanation")}>
          <details className="group rounded-2xl border border-line bg-card">
            <summary className="flex cursor-pointer list-none items-center justify-between gap-3 px-5 py-4 font-semibold text-ink [&::-webkit-details-marker]:hidden">
              <span className="inline-flex items-center gap-2">
                <Compass size={17} className="text-gold-ink" aria-hidden="true" />
                {t("trail.explanation")}
              </span>
              <ChevronDown size={18} className="text-muted transition-transform group-open:rotate-180" aria-hidden="true" />
            </summary>
            <div className="prose-lumen border-t border-line px-5 py-5">{body}</div>
          </details>
          {fm.analogyNote && (
            <p className="mt-3 rounded-xl border border-dashed border-gold/60 px-4 py-3 text-sm text-ink-2">
              <strong className="text-gold-ink">{t("blocks.analogy")}:</strong> {fm.analogyNote}
            </p>
          )}
          <div className="mt-4 flex flex-wrap gap-2">
            {v.formallyVerified && <VerificationBadge label="formally-verified" text={`${t("verify.formally-verified")} · ${v.leanVerifiedCount} Lean`} />}
            {v.computationallyTested && <VerificationBadge label="computationally-tested" text={t("verify.computationally-tested")} />}
            <VerificationBadge label="ai-drafted" text={t("verify.ai-drafted")} />
          </div>
        </Step>

        <Step n={5} title={t("trail.deeper")}>
          <ul className="grid gap-3 sm:grid-cols-2">
            {fm.deeper.map((id) => {
              const topic = getTopic(id);
              if (!topic) return null;
              return (
                <li key={id}>
                  <Link href={topic.lesson ? href(locale, `math/lessons/${topic.lesson}`) : href(locale, `math/topics/${id}`)} className="card block h-full p-4 hover:shadow-[var(--shadow-lg)]">
                    <span className="text-xs font-semibold text-muted">
                      {t(`levels.${topic.level}`)} · {topic.status === "implemented" ? t("status.implemented") : t("status.planned")}
                    </span>
                    <span className="mt-1 block font-display text-lg font-semibold text-ink">{topic.title}</span>
                    <span className="mt-1 block text-sm leading-snug text-ink-2">{topic.summary}</span>
                  </Link>
                </li>
              );
            })}
          </ul>
        </Step>

        <div className="flex flex-wrap items-center gap-3 border-t border-line pt-8">
          <Link href={returnHref} className="btn btn-primary">
            <ArrowLeft size={16} className="rtl:rotate-180" aria-hidden="true" /> {t("trail.return", { lesson: lesson.title })}
          </Link>
          <Link href={href(locale, "math/trails")} className="btn btn-ghost">
            {t("trail.allTrails")}
          </Link>
        </div>
      </div>
    </div>
    </Messages>
  );
}
