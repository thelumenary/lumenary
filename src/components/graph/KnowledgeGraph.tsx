"use client";

import { ArrowRight, BadgeCheck, CircleDashed, List, Map as MapIcon, Maximize2, Minus, Plus, Sparkles, X } from "lucide-react";
import Link from "next/link";
import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { href } from "@/lib/href";
import { ancestors, type LayoutResult } from "@/lib/graph-layout";

export interface GraphTopic {
  id: string;
  title: string;
  level: string;
  subject: string;
  status: "implemented" | "draft" | "planned";
  summary: string;
  prerequisites: string[];
  discoveries: { to: string; trail?: string; note?: string }[];
  lesson?: string;
}

interface Props {
  topics: GraphTopic[];
  layout: LayoutResult;
  subjects: { id: string; title: string }[];
  levels: { id: string; short: string }[];
  pathways: { id: string; title: string; milestones: string[] }[];
}

const truncate = (s: string, n = 25) => (s.length > n ? `${s.slice(0, n - 1)}…` : s);

export function KnowledgeGraph({ topics, layout, subjects, levels, pathways }: Props) {
  const { t, locale } = useI18n();
  const byId = useMemo(() => new Map(topics.map((x) => [x.id, x])), [topics]);
  const prereqMap = useMemo(() => new Map(topics.map((x) => [x.id, x.prerequisites])), [topics]);
  const children = useMemo(() => {
    const m = new Map<string, string[]>();
    for (const x of topics) for (const p of x.prerequisites) m.set(p, [...(m.get(p) ?? []), x.id]);
    return m;
  }, [topics]);

  const [view, setView] = useState<"map" | "list">("map");
  const [selected, setSelected] = useState<string | null>(null);
  const [pathway, setPathway] = useState<string>("");
  const [showOptional, setShowOptional] = useState(false);
  const [tf, setTf] = useState({ k: 0.6, x: 0, y: 0 });
  const box = useRef<HTMLDivElement>(null);
  const drag = useRef<{ x: number; y: number; tx: number; ty: number; moved: boolean } | null>(null);

  const fit = useCallback(() => {
    const el = box.current;
    if (!el) return;
    const k = Math.min(el.clientWidth / layout.width, el.clientHeight / layout.height) * 0.98;
    setTf({ k, x: (el.clientWidth - layout.width * k) / 2, y: 8 });
  }, [layout]);

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const p = params.get("pathway");
    if (p && pathways.some((x) => x.id === p)) setPathway(p);
    const s = params.get("topic");
    if (s && byId.has(s)) setSelected(s);
    // Start readable: fill the width, but never so small that labels become illegible.
    const el = box.current;
    if (el) {
      const k = Math.min(1, Math.max(0.62, el.clientWidth / layout.width));
      setTf({ k, x: Math.max(0, (el.clientWidth - layout.width * k) / 2), y: 4 });
    }
  }, [pathways, byId, layout]);

  useEffect(() => {
    const el = box.current;
    if (!el) return;
    const onWheel = (e: WheelEvent) => {
      e.preventDefault();
      const rect = el.getBoundingClientRect();
      const mx = e.clientX - rect.left;
      const my = e.clientY - rect.top;
      setTf((prev) => {
        const k = Math.min(2.5, Math.max(0.25, prev.k * Math.exp(-e.deltaY * 0.0015)));
        return { k, x: mx - ((mx - prev.x) * k) / prev.k, y: my - ((my - prev.y) * k) / prev.k };
      });
    };
    el.addEventListener("wheel", onWheel, { passive: false });
    return () => el.removeEventListener("wheel", onWheel);
  }, [view]);

  const zoom = (factor: number) => {
    const el = box.current;
    if (!el) return;
    const cx = el.clientWidth / 2;
    const cy = el.clientHeight / 2;
    setTf((prev) => {
      const k = Math.min(2.5, Math.max(0.25, prev.k * factor));
      return { k, x: cx - ((cx - prev.x) * k) / prev.k, y: cy - ((cy - prev.y) * k) / prev.k };
    });
  };

  const focusSet = useMemo(() => {
    if (selected) {
      const a = ancestors(selected, prereqMap);
      a.add(selected);
      return a;
    }
    if (pathway) return new Set(pathways.find((p) => p.id === pathway)?.milestones ?? []);
    return null;
  }, [selected, pathway, prereqMap, pathways]);

  const milestoneIndex = useMemo(() => {
    const p = pathways.find((x) => x.id === pathway);
    return new Map((p?.milestones ?? []).map((id, i) => [id, i + 1]));
  }, [pathway, pathways]);

  const sel = selected ? byId.get(selected) : null;
  const W = layout.nodeWidth;
  const H = layout.nodeHeight;
  const edgePath = (from: string, to: string) => {
    const a = layout.nodes[from];
    const b = layout.nodes[to];
    if (!a || !b) return "";
    const x1 = a.x + W;
    const y1 = a.y + H / 2;
    const x2 = b.x;
    const y2 = b.y + H / 2;
    if (x2 <= x1) {
      // Same column: route around the right side.
      const bend = Math.max(x1, x2 + W) + 26;
      return `M${a.x + W} ${y1} C${bend} ${y1}, ${bend} ${y2}, ${b.x + W} ${y2}`;
    }
    const dx = Math.max(30, (x2 - x1) * 0.5);
    return `M${x1} ${y1} C${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}`;
  };

  return (
    <div className="font-sans">
      <div className="mb-3 flex flex-wrap items-center gap-2">
        <div className="flex rounded-full border border-line bg-card p-0.5">
          {(["map", "list"] as const).map((v) => (
            <button key={v} type="button" aria-pressed={view === v} onClick={() => setView(v)} className={`inline-flex items-center gap-1.5 rounded-full px-3 py-1.5 text-sm font-semibold ${view === v ? "bg-ink text-paper" : "text-ink-2"}`}>
              {v === "map" ? <MapIcon size={14} /> : <List size={14} />}
              {v === "map" ? t("graph.mapView") : t("graph.listView")}
            </button>
          ))}
        </div>
        <label className="flex items-center gap-2 text-sm text-ink-2">
          <span className="font-semibold">{t("graph.pathway")}</span>
          <select
            className="input w-auto py-1.5"
            value={pathway}
            onChange={(e) => {
              setPathway(e.target.value);
              setSelected(null);
            }}
          >
            <option value="">{t("graph.none")}</option>
            {pathways.map((p) => (
              <option key={p.id} value={p.id}>
                {p.title}
              </option>
            ))}
          </select>
        </label>
        <label className="flex items-center gap-2 text-sm text-ink-2">
          <input type="checkbox" checked={showOptional} onChange={(e) => setShowOptional(e.target.checked)} className="accent-[var(--gold)]" />
          {t("graph.optional")}
        </label>
        <div className="ms-auto flex items-center gap-3 text-xs text-muted">
          <span className="inline-flex items-center gap-1.5">
            <span className="h-0.5 w-6 bg-ink-2" /> {t("graph.required")}
          </span>
          <span className="inline-flex items-center gap-1.5">
            <span className="h-0 w-6 border-t-2 border-dashed border-gold" /> {t("graph.optional")}
          </span>
          <span className="inline-flex items-center gap-1.5">
            <span className="h-3 w-4 rounded border-2 border-gold bg-gold-soft" /> {t("graph.implemented")}
          </span>
          <span className="inline-flex items-center gap-1.5">
            <span className="h-3 w-4 rounded border border-line-2 bg-card" /> {t("graph.planned")}
          </span>
        </div>
      </div>

      {view === "map" ? (
        <div className="relative">
          <div
            ref={box}
            className="relative h-[72vh] min-h-[480px] touch-none overflow-hidden rounded-2xl border border-line bg-card"
            dir="ltr"
            onPointerDown={(e) => {
              (e.target as Element).setPointerCapture?.(e.pointerId);
              drag.current = { x: e.clientX, y: e.clientY, tx: tf.x, ty: tf.y, moved: false };
            }}
            onPointerMove={(e) => {
              const d = drag.current;
              if (!d) return;
              const dx = e.clientX - d.x;
              const dy = e.clientY - d.y;
              if (Math.abs(dx) + Math.abs(dy) > 3) d.moved = true;
              setTf((prev) => ({ ...prev, x: d.tx + dx, y: d.ty + dy }));
            }}
            onPointerUp={() => {
              setTimeout(() => (drag.current = null), 0);
            }}
          >
            <svg width="100%" height="100%" className="block cursor-grab active:cursor-grabbing" role="application" aria-label={t("graph.title")}>
              <defs>
                <marker id="kg-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
                  <path d="M0 0 10 5 0 10z" fill="var(--line-2)" />
                </marker>
                <marker id="kg-arrow-hi" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
                  <path d="M0 0 10 5 0 10z" fill="var(--sky)" />
                </marker>
              </defs>
              <g transform={`translate(${tf.x} ${tf.y}) scale(${tf.k})`}>
                {/* Lanes and columns */}
                {layout.lanes.map((lane, i) => (
                  <g key={lane.subject}>
                    <rect x={0} y={lane.y} width={layout.width} height={lane.height} fill={i % 2 ? "var(--paper-2)" : "transparent"} opacity="0.55" />
                    <text x={14} y={lane.y + 24} fontSize="13" fontWeight="700" fill="var(--ink-2)">
                      {subjects.find((s) => s.id === lane.subject)?.title}
                    </text>
                  </g>
                ))}
                {layout.columns.map((c) => (
                  <g key={c.level}>
                    <line x1={c.x} y1={0} x2={c.x} y2={layout.height} stroke="var(--line)" strokeDasharray="3 5" />
                    <text x={c.x + c.width / 2} y={26} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--gold-ink)">
                      {levels.find((l) => l.id === c.level)?.short}
                    </text>
                  </g>
                ))}
                {/* Optional discovery edges */}
                {topics.flatMap((x) =>
                  x.discoveries.map((d) => {
                    // The selected topic's own discoveries are always shown; the rest only on request.
                    const own = selected === x.id || selected === d.to;
                    if (!showOptional && !own) return null;
                    const on = own || !focusSet || (focusSet.has(x.id) && focusSet.has(d.to));
                    return <path key={`d-${x.id}-${d.to}`} d={edgePath(x.id, d.to)} fill="none" stroke="var(--gold)" strokeWidth={own ? 2 : 1.3} strokeDasharray="5 5" opacity={on ? 0.8 : 0.08} />;
                  }),
                )}
                {/* Required edges */}
                {topics.flatMap((x) =>
                  x.prerequisites.map((p) => {
                    const hi = focusSet?.has(x.id) && focusSet?.has(p);
                    return (
                      <path
                        key={`r-${p}-${x.id}`}
                        d={edgePath(p, x.id)}
                        fill="none"
                        stroke={hi ? "var(--sky)" : "var(--line-2)"}
                        strokeWidth={hi ? 2.2 : 1.2}
                        opacity={hi ? 1 : focusSet ? 0.12 : 0.45}
                        markerEnd={hi ? "url(#kg-arrow-hi)" : "url(#kg-arrow)"}
                      />
                    );
                  }),
                )}
                {/* Nodes */}
                {topics.map((x) => {
                  const p = layout.nodes[x.id];
                  if (!p) return null;
                  const dim = focusSet && !focusSet.has(x.id);
                  const isSel = selected === x.id;
                  const impl = x.status === "implemented";
                  const ms = milestoneIndex.get(x.id);
                  return (
                    <g
                      key={x.id}
                      transform={`translate(${p.x} ${p.y})`}
                      opacity={dim ? 0.28 : 1}
                      className="cursor-pointer outline-none [&:focus-visible>rect]:stroke-[var(--sky)]"
                      tabIndex={0}
                      role="button"
                      aria-label={`${x.title} (${levels.find((l) => l.id === x.level)?.short})`}
                      aria-pressed={isSel}
                      onClick={() => {
                        if (drag.current?.moved) return;
                        setSelected(isSel ? null : x.id);
                      }}
                      onKeyDown={(e) => {
                        if (e.key === "Enter" || e.key === " ") {
                          e.preventDefault();
                          setSelected(isSel ? null : x.id);
                        }
                      }}
                    >
                      <title>{x.title}</title>
                      <rect
                        width={W}
                        height={H}
                        rx={9}
                        fill={impl ? "var(--gold-soft)" : "var(--card)"}
                        stroke={isSel ? "var(--sky)" : impl ? "var(--gold)" : "var(--line-2)"}
                        strokeWidth={isSel ? 3 : impl ? 2 : 1.2}
                        strokeDasharray={x.status === "planned" ? undefined : undefined}
                      />
                      <text x={impl ? 26 : 10} y={H / 2 + 4.5} fontSize="12.5" fontWeight={impl ? 700 : 500} fill="var(--ink)">
                        {truncate(x.title, impl ? 22 : 25)}
                      </text>
                      {impl && <circle cx={14} cy={H / 2} r={4.5} fill="var(--gold)" />}
                      {ms && (
                        <g transform={`translate(${W - 4} -6)`}>
                          <circle r={10} fill="var(--sky)" />
                          <text textAnchor="middle" y={4} fontSize="10.5" fontWeight="700" fill="var(--paper)">
                            {ms}
                          </text>
                        </g>
                      )}
                    </g>
                  );
                })}
              </g>
            </svg>
            <div className="absolute bottom-3 start-3 flex flex-col gap-1.5">
              {[
                [Plus, () => zoom(1.25), t("graph.zoomIn")],
                [Minus, () => zoom(0.8), t("graph.zoomOut")],
                [Maximize2, fit, t("graph.fit")],
              ].map(([Icon, fn, label], i) => {
                const I = Icon as typeof Plus;
                return (
                  <button key={i} type="button" onClick={fn as () => void} aria-label={label as string} title={label as string} className="flex h-9 w-9 items-center justify-center rounded-lg border border-line bg-card text-ink-2 shadow-[var(--shadow)] hover:text-ink">
                    <I size={16} />
                  </button>
                );
              })}
            </div>
            {!sel && <p className="pointer-events-none absolute bottom-3 end-3 rounded-lg bg-card/90 px-3 py-1.5 text-xs text-muted shadow-[var(--shadow)]">{t("graph.selectHint")}</p>}
          </div>
          {sel && <TopicPanel topic={sel} byId={byId} children={children.get(sel.id) ?? []} closure={ancestors(sel.id, prereqMap).size} onSelect={setSelected} onClose={() => setSelected(null)} locale={locale} />}
        </div>
      ) : (
        <ListView topics={topics} levels={levels} subjects={subjects} byId={byId} locale={locale} />
      )}
    </div>
  );
}

function TopicPanel({ topic, byId, children, closure, onSelect, onClose, locale }: { topic: GraphTopic; byId: Map<string, GraphTopic>; children: string[]; closure: number; onSelect: (id: string) => void; onClose: () => void; locale: string }) {
  const { t } = useI18n();
  const Chip = ({ id }: { id: string }) => {
    const x = byId.get(id);
    if (!x) return null;
    return (
      <button type="button" onClick={() => onSelect(id)} className={`chip hover:border-line-2 ${x.status === "implemented" ? "border-gold/50 bg-gold-soft text-ink" : ""}`}>
        {x.title}
      </button>
    );
  };
  return (
    <aside className="card mt-3 p-5 lg:absolute lg:end-3 lg:top-3 lg:mt-0 lg:max-h-[calc(72vh-1.5rem)] lg:w-[23rem] lg:overflow-auto" aria-live="polite">
      <div className="flex items-start justify-between gap-3">
        <div>
          <p className="text-xs font-semibold text-muted">
            {t(`levels.${topic.level}`)} · {topic.status === "implemented" ? t("status.implemented") : t("status.planned")}
          </p>
          <h2 className="mt-1 font-display text-xl font-semibold text-ink">{topic.title}</h2>
        </div>
        <button type="button" onClick={onClose} className="rounded-full p-1 text-muted hover:bg-paper-2" aria-label={t("nav.close")}>
          <X size={18} />
        </button>
      </div>
      <p className="mt-2 text-sm leading-relaxed text-ink-2">{topic.summary}</p>
      <p className="mt-3 text-xs font-semibold text-sky-ink">{t("graph.prereqCount", { n: closure })}</p>
      {topic.prerequisites.length > 0 && (
        <div className="mt-3">
          <p className="mb-1.5 text-xs font-semibold uppercase tracking-wide text-muted">{t("lesson.prerequisites")}</p>
          <div className="flex flex-wrap gap-1.5">
            {topic.prerequisites.map((p) => (
              <Chip key={p} id={p} />
            ))}
          </div>
        </div>
      )}
      {children.length > 0 && (
        <div className="mt-3">
          <p className="mb-1.5 text-xs font-semibold uppercase tracking-wide text-muted">{t("graph.unlocks")}</p>
          <div className="flex flex-wrap gap-1.5">
            {children.map((p) => (
              <Chip key={p} id={p} />
            ))}
          </div>
        </div>
      )}
      {topic.discoveries.length > 0 && (
        <div className="mt-3">
          <p className="mb-1.5 inline-flex items-center gap-1 text-xs font-semibold uppercase tracking-wide text-gold-ink">
            <Sparkles size={12} /> {t("graph.discoveries")}
          </p>
          <ul className="space-y-1.5">
            {topic.discoveries.map((d) => (
              <li key={d.to} className="text-sm">
                <Chip id={d.to} />
                {d.trail && (
                  <Link prefetch={false} href={href(locale, `math/trails/${d.trail}`)} className="link ms-2 text-xs">
                    {t("trail.badge")} →
                  </Link>
                )}
                {d.note && <p className="mt-0.5 text-xs leading-snug text-muted">{d.note}</p>}
              </li>
            ))}
          </ul>
        </div>
      )}
      <Link prefetch={false} href={topic.lesson ? href(locale, `math/lessons/${topic.lesson}`) : href(locale, `math/topics/${topic.id}`)} className="btn btn-primary btn-sm mt-5">
        {topic.lesson ? t("curriculum.openLesson") : t("curriculum.viewTopic")} <ArrowRight size={14} className="rtl:rotate-180" />
      </Link>
    </aside>
  );
}

function ListView({ topics, levels, subjects, byId, locale }: { topics: GraphTopic[]; levels: { id: string; short: string }[]; subjects: { id: string; title: string }[]; byId: Map<string, GraphTopic>; locale: string }) {
  const { t } = useI18n();
  return (
    <div className="space-y-8">
      {levels.map((l) => {
        const here = topics.filter((x) => x.level === l.id);
        if (!here.length) return null;
        return (
          <section key={l.id}>
            <h2 className="font-display text-2xl font-semibold text-ink">{t(`levels.${l.id}`)}</h2>
            <ul className="mt-3 grid gap-2 md:grid-cols-2">
              {here.map((x) => (
                <li key={x.id} className="rounded-xl border border-line bg-card px-4 py-3">
                  <Link prefetch={false} href={x.lesson ? href(locale, `math/lessons/${x.lesson}`) : href(locale, `math/topics/${x.id}`)} className="flex items-center gap-2 font-semibold text-ink hover:underline">
                    {x.status === "implemented" ? <BadgeCheck size={15} className="text-gold-ink" /> : <CircleDashed size={15} className="text-muted" />}
                    {x.title}
                  </Link>
                  <p className="mt-0.5 text-xs text-muted">{subjects.find((s) => s.id === x.subject)?.title}</p>
                  {x.prerequisites.length > 0 && (
                    <p className="mt-1 text-xs text-ink-2">
                      {t("lesson.prerequisites")}: {x.prerequisites.map((p) => byId.get(p)?.title ?? p).join(", ")}
                    </p>
                  )}
                </li>
              ))}
            </ul>
          </section>
        );
      })}
    </div>
  );
}
