import Link from "next/link";
import { ArrowRight, BookOpen, Compass, GraduationCap, Heart, Library, School, Sparkles, Sprout, Users } from "lucide-react";
import { getT, resolveLocale, formatNumber } from "@/i18n/server";
import { LOCALES } from "@/i18n/config";
import { getComputeReport, getGraph, getLeanReport, getLessonList, getTrailList } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";
import { HeroConstellation } from "@/components/site/HeroConstellation";
import { NarratorAvatar } from "@/components/brand/Narrators";
import { MODE_STYLE } from "@/components/ui/ModeBadge";

const FIRST_SEQUENCE = ["collections", "sets", "integers", "functions", "composition"];

export default async function HomePage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  // The first learning sequence shown on the home page (the curriculum has many more lessons).
  const all = getLessonList(locale).map((l) => l.frontmatter);
  const lessons = FIRST_SEQUENCE.map((slug) => all.find((l) => l.slug === slug)).filter((l) => l !== undefined);
  const trails = getTrailList(locale).map((l) => l.frontmatter);
  const graph = getGraph();
  const lean = getLeanReport();
  const compute = getComputeReport();
  const leanCompiled = lean?.build.success ? lean.declarations.filter((d) => !d.usesSorry).length : 0;
  const experimentsTested = compute?.experiments.filter((e) => e.ran && e.testsPassed).length ?? 0;
  const fmt = (n: number) => formatNumber(locale, n);

  const modes = [
    { m: "H" as const, who: "chloe" as const },
    { m: "F" as const, who: "gideon" as const },
    { m: "C" as const, who: "margaret" as const },
  ];

  const entries = [
    { key: "young", Icon: Sprout, to: "math/lessons/collections" },
    { key: "explorers", Icon: Compass, to: "math/lessons/sets" },
    { key: "secondary", Icon: BookOpen, to: "math/lessons/functions" },
    { key: "university", Icon: School, to: "math?level=ug1" },
    { key: "graduate", Icon: GraduationCap, to: "math?pathway=research-prep" },
    { key: "adult", Icon: Users, to: "math?pathway=adult-beginner" },
    { key: "educators", Icon: Library, to: "educators" },
  ];

  const future = [t("home.future.categories"), t("home.future.groups"), t("home.future.infinity")];

  return (
    <>
      {/* Hero */}
      <section className="relative overflow-hidden">
        <div className="bg-grid pointer-events-none absolute inset-0 opacity-60 [mask-image:radial-gradient(ellipse_at_70%_30%,black,transparent_70%)]" aria-hidden="true" />
        <div className="pointer-events-none absolute -top-40 end-[-10%] h-[36rem] w-[36rem] rounded-full bg-gold/15 blur-3xl" aria-hidden="true" />
        <div className="container-page relative grid items-center gap-10 py-14 sm:py-20 lg:grid-cols-[1.1fr_1fr]">
          <div className="animate-float-up">
            <p className="eyebrow">{t("home.eyebrow")}</p>
            <h1 className="mt-4 text-[2.6rem] font-semibold leading-[1.05] tracking-tight text-ink sm:text-6xl">{t("home.title")}</h1>
            <p className="mt-6 max-w-xl text-lg leading-relaxed text-ink-2">{t("home.lead")}</p>
            <div className="mt-8 flex flex-wrap gap-3">
              <Link prefetch={false} href={href(locale, "math/lessons/collections")} className="btn btn-primary px-5 py-3 text-base">
                {t("home.start")} <ArrowRight size={18} className="rtl:rotate-180" aria-hidden="true" />
              </Link>
              <Link href={href(locale, "math/graph")} className="btn btn-ghost px-5 py-3 text-base">
                {t("home.explore")}
              </Link>
            </div>
            <p className="mt-8 font-display text-xl italic text-ink-2">{t("meta.tagline")}</p>
          </div>
          <div className="relative mx-auto w-full max-w-xl" dir="ltr">
            <HeroConstellation lessons={lessons.map((l) => l.title)} future={[...future, t("levels.research")]} />
          </div>
        </div>
      </section>

      {/* Principle */}
      <section className="border-y border-line bg-ink text-paper">
        <div className="container-page flex flex-col items-center gap-3 py-10 text-center">
          <Sparkles size={20} className="text-gold" aria-hidden="true" />
          <p className="max-w-3xl font-display text-2xl leading-snug sm:text-3xl">{t("home.principleQuote")}</p>
        </div>
      </section>

      {/* Three modes */}
      <section className="container-page py-20">
        <div className="max-w-2xl">
          <h2 className="text-3xl font-semibold text-ink sm:text-4xl">{t("home.modesTitle")}</h2>
          <p className="mt-4 text-lg leading-relaxed text-ink-2">{t("home.modesLead")}</p>
        </div>
        <div className="mt-10 grid gap-5 md:grid-cols-3">
          {modes.map(({ m, who }) => {
            const { Icon, fg, bg } = MODE_STYLE[m];
            return (
              <article key={m} className="card relative overflow-hidden p-6">
                <div className={`absolute inset-x-0 top-0 h-1 ${{ H: "bg-human", F: "bg-formal", C: "bg-compute" }[m]}`} aria-hidden="true" />
                <div className="flex items-center justify-between">
                  <span className={`inline-flex h-11 w-11 items-center justify-center rounded-xl ${bg} ${fg}`}>
                    <Icon size={22} aria-hidden="true" />
                  </span>
                  <NarratorAvatar who={who} size={44} />
                </div>
                <p className={`mt-5 text-xs font-bold uppercase tracking-[0.14em] ${fg}`}>{t(`home.mode${m}`)}</p>
                <h3 className="mt-1 text-2xl font-semibold text-ink">{t(`home.mode${m}Verb`)}</h3>
                <p className="mt-3 leading-relaxed text-ink-2">{t(`home.mode${m}Text`)}</p>
                <p className="mt-5 border-t border-line pt-4 text-sm text-muted">
                  <span className="font-semibold text-ink-2">{t(`narrators.${who}`)}</span>, {t(`narrators.${who}Role`).toLowerCase()}: <em>“{t(`narrators.${who}Q`)}”</em>
                </p>
              </article>
            );
          })}
        </div>
      </section>

      {/* First path */}
      <section className="border-y border-line bg-paper-2/60">
        <div className="container-page py-20">
          <div className="flex flex-wrap items-end justify-between gap-4">
            <div className="max-w-2xl">
              <h2 className="text-3xl font-semibold text-ink sm:text-4xl">{t("home.sequenceTitle")}</h2>
              <p className="mt-4 text-lg leading-relaxed text-ink-2">{t("home.sequenceLead")}</p>
            </div>
            <Link href={href(locale, "math")} className="btn btn-ghost">
              {t("nav.learn")} <ArrowRight size={16} className="rtl:rotate-180" aria-hidden="true" />
            </Link>
          </div>
          <ol className="mt-10 grid gap-4 md:grid-cols-5">
            {lessons.map((l, i) => (
              <li key={l.slug} className="relative">
                {i < lessons.length - 1 && <span className="absolute start-[calc(100%-0.5rem)] top-10 z-0 hidden h-px w-6 bg-gold md:block" aria-hidden="true" />}
                <Link prefetch={false} href={href(locale, `math/lessons/${l.slug}`)} className="card group relative z-10 flex h-full flex-col p-5 transition-shadow hover:shadow-[var(--shadow-lg)]">
                  <span className="flex items-center justify-between">
                    <span className="flex h-9 w-9 items-center justify-center rounded-full bg-gold font-display font-bold text-[#1b1406]">{fmt(i + 1)}</span>
                    <span className="text-xs font-semibold text-muted">{t(`levels.${l.level}`)}</span>
                  </span>
                  <span className="mt-4 font-display text-xl font-semibold text-ink">{l.title}</span>
                  <span className="mt-2 line-clamp-4 text-sm leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(l.subtitle) }} />
                  <span className="mt-auto pt-4 text-xs text-muted">{l.ages}</span>
                </Link>
              </li>
            ))}
          </ol>
        </div>
      </section>

      {/* Wonder Trails */}
      <section className="container-page py-20">
        <div className="flex flex-wrap items-end justify-between gap-4">
          <div className="max-w-2xl">
            <p className="eyebrow inline-flex items-center gap-1.5">
              <Sparkles size={14} aria-hidden="true" /> {t("trail.optional")}
            </p>
            <h2 className="mt-2 text-3xl font-semibold text-ink sm:text-4xl">{t("home.trailsTitle")}</h2>
            <p className="mt-4 text-lg leading-relaxed text-ink-2">{t("home.trailsLead")}</p>
          </div>
          <Link prefetch={false} href={href(locale, "math/trails")} className="btn btn-ghost">
            {t("home.trailsCta")} <ArrowRight size={16} className="rtl:rotate-180" aria-hidden="true" />
          </Link>
        </div>
        <div className="mt-10 grid gap-4 sm:grid-cols-2 lg:grid-cols-3">
          {trails.slice(0, 6).map((tr) => (
            <Link prefetch={false}
              key={tr.slug}
              href={href(locale, `math/trails/${tr.slug}`)}
              className="group relative overflow-hidden rounded-2xl border border-gold/35 bg-gradient-to-br from-gold-soft/80 via-card to-card p-6 shadow-[var(--shadow)] transition-shadow hover:shadow-[var(--shadow-lg)]"
            >
              <span className="pointer-events-none absolute -end-10 -top-10 h-28 w-28 rounded-full bg-gold/20 blur-2xl" aria-hidden="true" />
              <span className="text-xs font-semibold text-gold-ink">{t(`levels.${tr.level}`)}</span>
              <span className="mt-1 block font-display text-xl font-semibold text-ink">{tr.title}</span>
              <span className="mt-2 block text-sm leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(tr.question) }} />
              <span className="mt-4 inline-flex items-center gap-1 text-sm font-semibold text-gold-ink">
                {t("trail.begin")} <ArrowRight size={14} className="transition-transform group-hover:translate-x-0.5 rtl:rotate-180" aria-hidden="true" />
              </span>
            </Link>
          ))}
        </div>
      </section>

      {/* Entry points */}
      <section className="border-y border-line bg-paper-2/60">
        <div className="container-page py-20">
          <div className="max-w-2xl">
            <h2 className="text-3xl font-semibold text-ink sm:text-4xl">{t("home.entryTitle")}</h2>
            <p className="mt-4 text-lg leading-relaxed text-ink-2">{t("home.entryLead")}</p>
          </div>
          <div className="mt-10 grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {entries.map(({ key, Icon, to }) => (
              <Link key={key} href={href(locale, to.split("?")[0]) + (to.includes("?") ? `?${to.split("?")[1]}` : "")} className="card group flex items-start gap-4 p-5 transition-shadow hover:shadow-[var(--shadow-lg)]">
                <span className="flex h-11 w-11 shrink-0 items-center justify-center rounded-xl bg-sky-soft text-sky-ink">
                  <Icon size={21} aria-hidden="true" />
                </span>
                <span>
                  <span className="block font-semibold text-ink">{t(`home.entry.${key}`)}</span>
                  <span className="block text-xs font-medium text-gold-ink">{t(`home.entry.${key}Ages`)}</span>
                  <span className="mt-1 block text-sm leading-snug text-ink-2">{t(`home.entry.${key}Text`)}</span>
                </span>
              </Link>
            ))}
          </div>
        </div>
      </section>

      {/* Honest status */}
      <section className="container-page py-20">
        <div className="grid gap-10 lg:grid-cols-[1fr_1.4fr]">
          <div>
            <h2 className="text-3xl font-semibold text-ink sm:text-4xl">{t("home.honestTitle")}</h2>
            <p className="mt-4 text-lg leading-relaxed text-ink-2">{t("home.honestLead")}</p>
            <p className="mt-6 rounded-xl border border-warn/30 bg-warn-soft px-4 py-3 text-sm leading-relaxed text-ink">{t("home.notYetReviewed")}</p>
            <Link href={href(locale, "verification")} className="btn btn-ghost mt-6">
              {t("home.seeVerification")} <ArrowRight size={16} className="rtl:rotate-180" aria-hidden="true" />
            </Link>
          </div>
          <dl className="grid grid-cols-2 gap-4 sm:grid-cols-3">
            {[
              [all.length, t("home.statLessons")],
              [trails.length, t("home.statTrails")],
              [graph.topics.length, t("home.statTopics")],
              [leanCompiled, t("home.statLean")],
              [experimentsTested, t("home.statExperiments")],
              [LOCALES.length, t("home.statLanguages")],
            ].map(([n, label]) => (
              <div key={label as string} className="card p-5">
                <dt className="text-sm text-muted">{label}</dt>
                <dd className="mt-1 font-display text-4xl font-semibold text-ink">{fmt(n as number)}</dd>
              </div>
            ))}
          </dl>
        </div>
      </section>

      {/* Values */}
      <section className="container-page pb-4">
        <div className="relative overflow-hidden rounded-3xl bg-ink px-6 py-14 text-paper sm:px-12">
          <div className="pointer-events-none absolute -bottom-24 -end-24 h-80 w-80 rounded-full bg-gold/25 blur-3xl" aria-hidden="true" />
          <div className="relative max-w-2xl">
            <Heart size={22} className="text-gold" aria-hidden="true" />
            <h2 className="mt-4 text-3xl font-semibold sm:text-4xl">{t("home.valuesTitle")}</h2>
            <p className="mt-4 text-lg leading-relaxed opacity-85">{t("home.valuesLead")}</p>
            <Link href={href(locale, "about")} className="btn btn-gold mt-8">
              {t("home.readAbout")} <ArrowRight size={16} className="rtl:rotate-180" aria-hidden="true" />
            </Link>
          </div>
        </div>
      </section>
    </>
  );
}
