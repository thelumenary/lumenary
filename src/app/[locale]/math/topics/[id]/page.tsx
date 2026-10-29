import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowRight, BookOpen, CircleDashed, Map as MapIcon, Sparkles } from "lucide-react";
import { LOCALES } from "@/i18n/config";
import { getT, resolveLocale } from "@/i18n/server";
import { getGraph, getPathways, getTopic, prerequisiteClosure } from "@/lib/content";
import { href } from "@/lib/href";
import { mdInline } from "@/lib/markdown";

export const dynamicParams = false;

export function generateStaticParams() {
  return LOCALES.flatMap((locale) => getGraph().topics.map((t) => ({ locale, id: t.id })));
}

type Params = { params: Promise<{ locale: string; id: string }> };

export async function generateMetadata({ params }: Params): Promise<Metadata> {
  const { id } = await params;
  return { title: getTopic(id)?.title ?? id };
}

export default async function TopicPage({ params }: Params) {
  const { id } = await params;
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const topic = getTopic(id);
  if (!topic) notFound();
  const graph = getGraph();
  const subject = graph.subjects.find((s) => s.id === topic.subject);
  const leadsTo = graph.topics.filter((x) => x.prerequisites.includes(id));
  const discoveredFrom = graph.topics.filter((x) => x.discoveries.some((d) => d.to === id));
  const pathways = getPathways().filter((p) => p.milestones.includes(id));
  const closure = prerequisiteClosure(id);

  const TopicLink = ({ tid }: { tid: string }) => {
    const x = getTopic(tid);
    if (!x) return null;
    return (
      <Link prefetch={false} href={x.lesson ? href(locale, `math/lessons/${x.lesson}`) : href(locale, `math/topics/${x.id}`)} className={`chip hover:border-line-2 hover:text-ink ${x.status === "implemented" ? "border-gold/50 bg-gold-soft text-ink" : ""}`}>
        {x.title}
      </Link>
    );
  };

  const List = ({ title, items }: { title: string; items: string[] }) =>
    items.length ? (
      <section>
        <h2 className="text-xl font-semibold text-ink">{title}</h2>
        <ul className="prose-ui mt-3 list-disc ps-5">
          {items.map((x) => (
            <li key={x} dangerouslySetInnerHTML={{ __html: mdInline(x) }} />
          ))}
        </ul>
      </section>
    ) : null;

  return (
    <div className="container-page max-w-4xl py-12">
      <nav className="text-sm text-muted" aria-label="Breadcrumb">
        <Link href={href(locale, "math")} className="hover:text-ink">
          {t("curriculum.title")}
        </Link>{" "}
        / {subject?.title}
      </nav>
      <div className="mt-5 flex flex-wrap gap-2">
        <span className="chip border-ink bg-ink text-paper">{t(`levels.${topic.level}`)}</span>
        <span className="chip">{subject?.title}</span>
        <span className="chip">
          {topic.status === "implemented" ? <BookOpen size={12} /> : <CircleDashed size={12} />}
          {t(`status.${topic.status}`)}
        </span>
      </div>
      <h1 className="mt-4 text-4xl font-semibold leading-tight text-ink sm:text-5xl">{topic.title}</h1>
      <p className="mt-4 font-serif text-xl leading-relaxed text-ink-2" dangerouslySetInnerHTML={{ __html: mdInline(topic.summary) }} />
      <p className="mt-2 font-mono text-xs text-muted" dir="ltr">
        {topic.id}
      </p>

      <div className="mt-6 flex flex-wrap gap-2">
        {topic.lesson && (
          <Link prefetch={false} href={href(locale, `math/lessons/${topic.lesson}`)} className="btn btn-primary">
            {t("curriculum.openLesson")} <ArrowRight size={16} className="rtl:rotate-180" />
          </Link>
        )}
        <Link href={`${href(locale, "math/graph")}?topic=${encodeURIComponent(topic.id)}`} className="btn btn-ghost">
          <MapIcon size={16} /> {t("graph.highlightPath")}
        </Link>
      </div>

      {topic.status !== "implemented" && <p className="mt-8 rounded-xl border border-line bg-paper-2 px-4 py-3 text-sm text-ink-2">{t("curriculum.plannedNote")}</p>}

      <div className="mt-10 grid gap-10">
        <section>
          <h2 className="text-xl font-semibold text-ink">{t("lesson.prerequisites")}</h2>
          {topic.prerequisites.length ? (
            <>
              <div className="mt-3 flex flex-wrap gap-1.5">
                {topic.prerequisites.map((p) => (
                  <TopicLink key={p} tid={p} />
                ))}
              </div>
              <p className="mt-2 text-xs text-muted">{t("graph.prereqCount", { n: closure.size })}</p>
            </>
          ) : (
            <p className="mt-2 text-sm text-ink-2">{t("lesson.noPrerequisites")}</p>
          )}
        </section>
        <List title={t("lesson.objectives")} items={topic.objectives} />
        <List title={t("blocks.definition")} items={topic.definitions} />
        <List title={t("blocks.theorem")} items={topic.keyResults} />
        <List title={t("sections.misconceptions")} items={topic.misconceptions} />
        {leadsTo.length > 0 && (
          <section>
            <h2 className="text-xl font-semibold text-ink">{t("graph.unlocks")}</h2>
            <div className="mt-3 flex flex-wrap gap-1.5">
              {leadsTo.map((x) => (
                <TopicLink key={x.id} tid={x.id} />
              ))}
            </div>
          </section>
        )}
        {(topic.discoveries.length > 0 || discoveredFrom.length > 0) && (
          <section>
            <h2 className="inline-flex items-center gap-2 text-xl font-semibold text-ink">
              <Sparkles size={18} className="text-gold-ink" /> {t("graph.discoveries")}
            </h2>
            <ul className="mt-3 space-y-2">
              {topic.discoveries.map((d) => (
                <li key={d.to} className="text-sm text-ink-2">
                  <TopicLink tid={d.to} /> {d.note && <span className="ms-1">{d.note}</span>}
                  {d.trail && (
                    <Link prefetch={false} href={href(locale, `math/trails/${d.trail}`)} className="link ms-2">
                      {t("trail.badge")} →
                    </Link>
                  )}
                </li>
              ))}
              {discoveredFrom.map((x) => (
                <li key={x.id} className="text-sm text-ink-2">
                  ← <TopicLink tid={x.id} />
                </li>
              ))}
            </ul>
          </section>
        )}
        {pathways.length > 0 && (
          <section>
            <h2 className="text-xl font-semibold text-ink">{t("curriculum.pathways")}</h2>
            <ul className="mt-3 flex flex-wrap gap-1.5">
              {pathways.map((p) => (
                <li key={p.id}>
                  <Link href={`${href(locale, "math/graph")}?pathway=${p.id}`} className="chip hover:text-ink">
                    {p.title}
                  </Link>
                </li>
              ))}
            </ul>
          </section>
        )}
        {topic.references.length > 0 && (
          <section>
            <h2 className="text-xl font-semibold text-ink">{t("sections.reading")}</h2>
            <ul className="prose-ui mt-3 list-disc ps-5">
              {topic.references.map((r) => (
                <li key={r.title}>
                  {r.author && `${r.author}, `}
                  {r.url ? (
                    <a href={r.url} rel="noopener noreferrer">
                      <em>{r.title}</em>
                    </a>
                  ) : (
                    <em>{r.title}</em>
                  )}
                  {r.year && ` (${r.year})`}
                  {r.note && ` — ${r.note}`}
                </li>
              ))}
            </ul>
          </section>
        )}
      </div>
    </div>
  );
}
