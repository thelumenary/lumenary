import type { Metadata } from "next";
import { Messages } from "@/i18n/Messages";
import { getT, resolveLocale } from "@/i18n/server";
import { getGraph, getPathways } from "@/lib/content";
import { layoutGraph } from "@/lib/graph-layout";
import { KnowledgeGraph } from "@/components/graph/KnowledgeGraph";
import { PageHeader } from "@/components/ui/PageHeader";

export async function generateMetadata({ params }: { params: Promise<{ locale: string }> }): Promise<Metadata> {
  const t = await getT(await resolveLocale(params));
  return { title: t("graph.title") };
}

export default async function GraphPage({ params }: { params: Promise<{ locale: string }> }) {
  const locale = await resolveLocale(params);
  const t = await getT(locale);
  const graph = getGraph();
  const layout = layoutGraph(graph.topics);
  const required = graph.topics.reduce((n, x) => n + x.prerequisites.length, 0);
  const optional = graph.topics.reduce((n, x) => n + x.discoveries.length, 0);
  return (
    <Messages locale={locale} ns={["graph", "curriculum", "lesson", "trail"]}>
    <>
      <PageHeader eyebrow="Lumenary Math" title={t("graph.title")} lead={t("graph.lead")}>
        <p className="mt-4 text-sm text-muted">{t("graph.counts", { topics: graph.topics.length, required, optional })}</p>
      </PageHeader>
      <div className="mx-auto w-full max-w-[110rem] px-4 py-8 sm:px-6">
        <KnowledgeGraph
          topics={graph.topics.map((x) => ({
            id: x.id,
            title: x.title,
            level: x.level,
            subject: x.subject,
            status: x.status,
            summary: x.summary,
            prerequisites: x.prerequisites,
            discoveries: x.discoveries,
            lesson: x.lesson,
          }))}
          layout={layout}
          subjects={graph.subjects.map((s) => ({ id: s.id, title: s.title }))}
          levels={graph.levels.map((l) => ({ id: l.id, short: l.short }))}
          pathways={getPathways().map((p) => ({ id: p.id, title: p.title, milestones: p.milestones }))}
        />
        <p className="mx-auto mt-8 max-w-3xl rounded-xl border border-dashed border-gold/50 px-5 py-4 text-sm leading-relaxed text-ink-2">{t("graph.categoryNote")}</p>
      </div>
    </>
    </Messages>
  );
}
