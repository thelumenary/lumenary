"use client";

import { Check, RotateCcw, Sparkles, Undo2, Wand2, X } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  DRAW_H,
  DRAW_W,
  PRESET_IDS,
  adjacencyMatrix,
  analyseWalk,
  bfsTree,
  buildGraph,
  chromaticNumber,
  colourInfo,
  degrees,
  edgeShapes,
  emptyWalk,
  eulerInfo,
  extendWalk,
  greedyColouring,
  isConnected,
  isPresetId,
  isSimple,
  listWalks,
  matPow,
  presetGraph,
  spanningInfo,
  spanningTreeCount,
  walkVertices,
  type Graph,
  type PresetId,
  type Walk,
} from "./lib/graph-core";

const MODES = ["degrees", "walk", "colour", "spanning", "matrix"] as const;
type Mode = (typeof MODES)[number];
const isMode = (v: unknown): v is Mode => typeof v === "string" && (MODES as readonly string[]).includes(v);

/** Six vertex colours; each also carries a number so colour is never the only cue. */
const PALETTE = ["var(--human)", "var(--compute)", "var(--formal)", "var(--gold-ink)", "var(--sky)", "var(--ink-2)"];
const MAX_K = 6;

export interface GraphExplorerProps {
  preset?: string;
  nodes?: (string | number)[];
  edges?: (string | number)[][];
  positions?: ([number, number] | { x: number; y: number })[];
  mode?: string;
  modes?: string[];
  /** Presets to offer in a picker (default: all, when no graph is pinned). */
  presets?: string[];
  title?: string;
  subtitle?: string;
}

/** Finite graphs: degrees and the handshake lemma, walks and Euler trails, colourings, spanning trees, adjacency matrices. */
export function GraphExplorer({ preset, nodes, edges, positions, mode, modes, presets, title, subtitle }: GraphExplorerProps) {
  const { t } = useI18n();
  const custom = (Array.isArray(nodes) && nodes.length > 0) || Array.isArray(edges);
  const offered = useMemo<Mode[]>(() => {
    const list = Array.isArray(modes) ? [...new Set(modes.filter(isMode))] : [];
    return list.length ? list : [...MODES];
  }, [modes]);
  const pickable = useMemo<PresetId[]>(() => {
    if (custom) return [];
    if (Array.isArray(presets)) return [...new Set(presets.filter(isPresetId))];
    return isPresetId(preset) ? [] : [...PRESET_IDS];
  }, [custom, presets, preset]);
  const [presetId, setPresetId] = useState<PresetId>(isPresetId(preset) ? preset : (pickable[0] ?? "konigsberg"));
  const [tab, setTab] = useState<Mode>(isMode(mode) && offered.includes(mode) ? mode : offered[0]);
  const built = useMemo(() => (custom ? buildGraph({ nodes, edges, positions }) : { graph: presetGraph(presetId), ignored: 0, custom: false }), [custom, nodes, edges, positions, presetId]);
  const graph = built.graph;
  const options = pickable.includes(presetId) || pickable.length === 0 ? pickable : [presetId, ...pickable];

  return (
    <WidgetFrame title={title ?? t("w.graphx.title")} subtitle={subtitle ?? t("w.graphx.subtitle")}>
      <div className="flex flex-wrap items-center gap-2">
        {offered.length > 1 &&
          offered.map((m) => (
            <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
              {t(`w.graphx.mode.${m}`)}
            </button>
          ))}
        {options.length > 1 && (
          <label className="ms-auto flex items-center gap-2 text-sm font-semibold text-ink-2">
            {t("w.graphx.graph")}
            <select className="input w-auto py-1.5 text-sm" value={presetId} onChange={(e) => isPresetId(e.target.value) && setPresetId(e.target.value)}>
              {options.map((p) => (
                <option key={p} value={p}>
                  {t(`w.graphx.preset.${p}`)}
                </option>
              ))}
            </select>
          </label>
        )}
      </div>
      {built.ignored > 0 && <p className="mt-3 rounded-lg bg-warn-soft px-3 py-2 text-sm text-ink">{t("w.graphx.ignored", { count: built.ignored })}</p>}
      <Explorer key={custom ? "custom" : presetId} graph={graph} mode={tab} planar={custom ? undefined : graph.planar} />
    </WidgetFrame>
  );
}

function Explorer({ graph, mode, planar }: { graph: Graph; mode: Mode; planar?: boolean }) {
  const { t, n } = useI18n();
  const V = graph.labels.length;
  const E = graph.edges.length;
  const lab = (i: number) => graph.labels[i] ?? "?";
  const shapes = useMemo(() => edgeShapes(graph), [graph]);
  const deg = useMemo(() => degrees(graph), [graph]);
  const euler = useMemo(() => eulerInfo(graph), [graph]);
  const centre = useMemo(() => {
    const cx = graph.pos.reduce((s, p) => s + p.x, 0) / Math.max(1, V);
    const cy = graph.pos.reduce((s, p) => s + p.y, 0) / Math.max(1, V);
    return { x: cx, y: cy };
  }, [graph, V]);

  // Per-mode state
  const [selected, setSelected] = useState<number | null>(null);
  const [walk, setWalk] = useState<Walk>(emptyWalk);
  const [walkError, setWalkError] = useState<string | null>(null);
  const [colours, setColours] = useState<(number | null)[]>(() => graph.labels.map(() => null));
  const [colourNote, setColourNote] = useState<string | null>(null);
  const [showChi, setShowChi] = useState(false);
  const [chosen, setChosen] = useState<number[]>([]);
  const [power, setPower] = useState(1);
  const [cell, setCell] = useState<[number, number] | null>(null);

  const walkInfo = useMemo(() => analyseWalk(graph, walk), [graph, walk]);
  const colInfo = useMemo(() => colourInfo(graph, colours), [graph, colours]);
  const span = useMemo(() => spanningInfo(graph, chosen), [graph, chosen]);
  const connected = useMemo(() => isConnected(graph), [graph]);
  const tau = useMemo(() => spanningTreeCount(graph), [graph]);
  const simple = useMemo(() => isSimple(graph), [graph]);
  const A = useMemo(() => adjacencyMatrix(graph), [graph]);
  const Ak = useMemo(() => matPow(A, power), [A, power]);
  const chi = useMemo(() => (showChi ? chromaticNumber(graph) : null), [graph, showChi]);

  const fmtBig = (b: bigint) => (b <= BigInt(Number.MAX_SAFE_INTEGER) ? n(Number(b)) : b.toString());
  const edgeName = (ei: number) => `${lab(graph.edges[ei][0])}–${lab(graph.edges[ei][1])}`;

  /* ---------- interactions ---------- */
  const vertexAction = (v: number) => {
    if (mode === "degrees") setSelected((s) => (s === v ? null : v));
    else if (mode === "walk") {
      if (walk.edges.length === 0) {
        setWalk({ start: v, edges: [], flexible: false });
        setWalkError(null);
      }
    } else if (mode === "colour") {
      setColours((cs) => cs.map((c, i) => (i === v ? (c === null ? 0 : c + 1 < PALETTE.length ? c + 1 : null) : c)));
      setColourNote(null);
    }
  };
  const edgeAction = (ei: number) => {
    if (mode === "walk") {
      const res = extendWalk(graph, walk, ei);
      if (res.ok) {
        setWalk(res.walk);
        setWalkError(null);
      } else setWalkError(t("w.graphx.walk.notIncident", { v: lab(res.at) }));
    } else if (mode === "spanning") setChosen((c) => (c.includes(ei) ? c.filter((x) => x !== ei) : [...c, ei]));
  };
  const vertexInteractive = mode === "degrees" || mode === "colour" || (mode === "walk" && walk.edges.length === 0);
  const edgeInteractive = mode === "walk" || mode === "spanning";

  /* ---------- styling per mode ---------- */
  const walkSteps = useMemo(() => {
    const m = new Map<number, number[]>();
    walk.edges.forEach((ei, k) => m.set(ei, [...(m.get(ei) ?? []), k + 1]));
    return m;
  }, [walk]);
  const walkVs = walkInfo.vertices;
  const current = walkVs.length ? walkVs[walkVs.length - 1] : null;
  const cycleSet = new Set(span.cycle ?? []);
  const conflictSet = new Set(colInfo.conflicts);

  const edgeStyle = (ei: number): { stroke: string; width: number; dash?: string } => {
    const [a, b] = graph.edges[ei];
    const base = { stroke: "var(--muted)", width: 2 };
    if (mode === "degrees" && selected !== null) return a === selected || b === selected ? { stroke: "var(--sky)", width: 4 } : { ...base, stroke: "var(--line-2)" };
    if (mode === "walk" && walkSteps.has(ei)) return { stroke: "var(--human)", width: 4 };
    if (mode === "colour" && conflictSet.has(ei)) return { stroke: "var(--bad)", width: 3.5, dash: "6 4" };
    if (mode === "spanning") {
      if (cycleSet.has(ei)) return { stroke: "var(--bad)", width: 4.5, dash: "7 4" };
      if (chosen.includes(ei)) return { stroke: "var(--compute)", width: 4.5 };
      return { stroke: "var(--line-2)", width: 2, dash: "2 4" };
    }
    if (mode === "matrix" && cell && power === 1 && ((a === cell[0] && b === cell[1]) || (a === cell[1] && b === cell[0]))) return { stroke: "var(--formal)", width: 4 };
    return base;
  };

  const badgeFor = (v: number): { text: string; fill: string; ink: string } | null => {
    if (mode === "degrees") return { text: String(deg[v]), fill: deg[v] % 2 ? "var(--warn-soft)" : "var(--paper-2)", ink: deg[v] % 2 ? "var(--warn)" : "var(--ink-2)" };
    if (mode === "colour" && colours[v] !== null) return { text: String((colours[v] as number) + 1), fill: PALETTE[colours[v] as number], ink: "var(--paper)" };
    return null;
  };

  const r = V > 12 ? 13 : 15;
  const labelSize = (s: string) => (s.length >= 3 ? 10 : s.length === 2 ? 11.5 : 13);
  const outward = (v: number) => {
    const p = graph.pos[v];
    const dx = p.x - centre.x;
    const dy = p.y - centre.y;
    const len = Math.hypot(dx, dy);
    return len < 1 ? { x: 0.7071, y: -0.7071 } : { x: dx / len, y: dy / len };
  };

  /* ---------- drawing ---------- */
  const drawing = (
    <svg viewBox={`0 0 ${DRAW_W} ${DRAW_H}`} className="w-full select-none" role="group" aria-label={t("w.graphx.drawing", { v: V, e: E })}>
      {graph.edges.map((_, ei) => {
        const st = edgeStyle(ei);
        const sh = shapes[ei];
        const pressed = mode === "spanning" ? chosen.includes(ei) : undefined;
        const steps = walkSteps.get(ei);
        const aria = `${t("w.graphx.edgeAria", { k: ei + 1, a: lab(graph.edges[ei][0]), b: lab(graph.edges[ei][1]) })}${steps ? ` · ${t("w.graphx.walk.stepsAria", { steps: steps.join(", ") })}` : ""}`;
        return (
          <g
            key={ei}
            {...(edgeInteractive
              ? {
                  role: "button",
                  tabIndex: 0,
                  "aria-label": aria,
                  "aria-pressed": pressed,
                  onClick: () => edgeAction(ei),
                  onKeyDown: (e: React.KeyboardEvent) => {
                    if (e.key === "Enter" || e.key === " ") {
                      e.preventDefault();
                      edgeAction(ei);
                    }
                  },
                  className: "group cursor-pointer outline-none",
                }
              : { "aria-hidden": true })}
          >
            {edgeInteractive && <path d={sh.d} fill="none" stroke="var(--sky)" strokeWidth={10} strokeLinecap="round" className="opacity-0 transition-opacity group-hover:opacity-20 group-focus-visible:opacity-50" />}
            <path d={sh.d} fill="none" stroke={st.stroke} strokeWidth={st.width} strokeDasharray={st.dash} strokeLinecap="round" style={{ transition: "stroke .2s, stroke-width .2s" }} />
            {edgeInteractive && <path d={sh.d} fill="none" stroke="transparent" strokeWidth={24} pointerEvents="stroke" />}
          </g>
        );
      })}
      {mode === "walk" &&
        [...walkSteps.entries()].map(([ei, steps]) => {
          const m = shapes[ei].mid;
          const text = steps.length > 3 ? `${steps.slice(0, 3).join(",")}…` : steps.join(",");
          const w = Math.max(17, 7 + text.length * 6.2);
          return (
            <g key={`s${ei}`} aria-hidden="true" pointerEvents="none">
              <rect x={m.x - w / 2} y={m.y - 8.5} width={w} height={17} rx={8.5} fill="var(--human)" />
              <text x={m.x} y={m.y + 3.8} textAnchor="middle" fontSize="10.5" fontWeight="700" fill="var(--paper)">
                {text}
              </text>
            </g>
          );
        })}
      {graph.labels.map((label, v) => {
        const p = graph.pos[v];
        const colour = mode === "colour" ? colours[v] : null;
        const isSel = (mode === "degrees" && selected === v) || (mode === "matrix" && cell !== null && (cell[0] === v || cell[1] === v));
        const isStart = mode === "walk" && walk.start === v;
        const isCurrent = mode === "walk" && current === v;
        const fill = colour !== null ? PALETTE[colour] : isSel ? "var(--sky-soft)" : "var(--card)";
        const ink = colour !== null ? "var(--paper)" : "var(--ink)";
        const stroke = isStart ? "var(--human)" : isSel ? (mode === "matrix" && cell && cell[1] === v && cell[0] !== v ? "var(--gold)" : "var(--sky)") : colour !== null ? PALETTE[colour] : "var(--ink-2)";
        const badge = badgeFor(v);
        const o = outward(v);
        const bx = p.x + o.x * (r + 12);
        const by = p.y + o.y * (r + 12);
        const ariaParts = [t("w.graphx.vertexAria", { v: label, d: deg[v] })];
        if (mode === "colour") ariaParts.push(colour === null ? t("w.graphx.colour.none") : t("w.graphx.colour.nth", { k: colour + 1 }));
        if (isStart) ariaParts.push(t("w.graphx.walk.start"));
        if (isCurrent && walk.edges.length) ariaParts.push(t("w.graphx.walk.here"));
        return (
          <g
            key={v}
            {...(vertexInteractive
              ? {
                  role: "button",
                  tabIndex: 0,
                  "aria-label": ariaParts.join(", "),
                  "aria-pressed": mode === "degrees" ? selected === v : undefined,
                  onClick: () => vertexAction(v),
                  onKeyDown: (e: React.KeyboardEvent) => {
                    if (e.key === "Enter" || e.key === " ") {
                      e.preventDefault();
                      vertexAction(v);
                    } else if (mode === "colour" && (e.key === "Delete" || e.key === "Backspace")) {
                      e.preventDefault();
                      setColours((cs) => cs.map((c, i) => (i === v ? null : c)));
                    }
                  },
                  className: "group cursor-pointer outline-none",
                }
              : { "aria-hidden": true })}
          >
            <circle cx={p.x} cy={p.y} r={r + 5} fill="none" stroke="var(--sky)" strokeWidth={3} className="opacity-0 transition-opacity group-focus-visible:opacity-100" />
            {isCurrent && walk.start !== null && <circle cx={p.x} cy={p.y} r={r + 5} fill="var(--gold-soft)" stroke="var(--gold)" strokeWidth={3} />}
            <circle cx={p.x} cy={p.y} r={r} fill={fill} stroke={stroke} strokeWidth={isStart || isSel ? 3 : 1.8} style={{ transition: "fill .2s, stroke .2s" }} />
            <text x={p.x} y={p.y + labelSize(label) * 0.36} textAnchor="middle" fontSize={labelSize(label)} fontWeight="700" fill={ink} className={label.length >= 3 ? "font-mono" : ""}>
              {label}
            </text>
            {badge && (
              <g pointerEvents="none">
                <circle cx={bx} cy={by} r={9} fill={badge.fill} stroke="var(--card)" strokeWidth={1.5} />
                <text x={bx} y={by + 3.6} textAnchor="middle" fontSize="10.5" fontWeight="700" fill={badge.ink}>
                  {badge.text}
                </text>
              </g>
            )}
            {vertexInteractive && <circle cx={p.x} cy={p.y} r={24} fill="transparent" />}
          </g>
        );
      })}
    </svg>
  );

  const hint = t(`w.graphx.hint.${mode}`);

  /* ---------- side panels ---------- */
  let panel: React.ReactNode = null;
  if (mode === "degrees") {
    const sum = deg.reduce((s, d) => s + d, 0);
    const odd = deg.filter((d) => d % 2).length;
    panel = (
      <div className="space-y-3">
        <div className="flex flex-wrap gap-1.5" dir="ltr">
          {deg.map((d, v) => (
            <span key={v} className={`chip ${d % 2 ? "!border-warn/40 !bg-warn-soft" : ""}`}>
              deg({lab(v)}) = {d}
            </span>
          ))}
        </div>
        <p className="rounded-xl bg-paper-2 px-4 py-3 font-serif text-lg leading-relaxed text-ink" dir="ltr">
          {deg.length <= 12 ? deg.join(" + ") : "Σ deg(v)"} = <strong>{sum}</strong> = 2 × {E}
        </p>
        <div aria-live="polite" className="space-y-2 text-sm text-ink-2">
          {selected !== null && (
            <p className="font-semibold text-ink">
              {t("w.graphx.deg.selected", { v: lab(selected), d: deg[selected] })}
            </p>
          )}
          <p>{t("w.graphx.deg.handshake", { sum, e: E })}</p>
          <p>{t("w.graphx.deg.odd", { count: odd })}</p>
        </div>
      </div>
    );
  } else if (mode === "walk") {
    const oddNames = euler.odd.map(lab).join(", ");
    let verdict: string;
    if (E === 0) verdict = t("w.graphx.euler.noEdges");
    else if (!euler.edgesConnected) verdict = t("w.graphx.euler.disconnected");
    else if (euler.odd.length === 0) verdict = t("w.graphx.euler.circuit");
    else if (euler.odd.length === 2) verdict = t("w.graphx.euler.trail", { a: lab(euler.odd[0]), b: lab(euler.odd[1]) });
    else verdict = t("w.graphx.euler.none", { count: euler.odd.length });
    panel = (
      <div className="space-y-3">
        <p className="min-h-[3rem] rounded-xl bg-paper-2 px-4 py-3 font-serif text-lg text-ink" dir="ltr">
          {walk.start === null ? <span className="font-sans text-sm text-muted">{t("w.graphx.walk.empty")}</span> : walkVertices(graph, walk).map(lab).join(" → ")}
        </p>
        <div className="flex flex-wrap gap-2">
          <button
            type="button"
            className="btn btn-sm btn-ghost"
            disabled={walk.start === null}
            onClick={() => {
              setWalkError(null);
              setWalk((w) => (w.edges.length === 0 || (w.edges.length === 1 && w.flexible) ? emptyWalk : { ...w, edges: w.edges.slice(0, -1) }));
            }}
          >
            <Undo2 size={14} aria-hidden="true" /> {t("w.graphx.undo")}
          </button>
          <button type="button" className="btn btn-sm btn-ghost" disabled={walk.start === null} onClick={() => {
            setWalk(emptyWalk);
            setWalkError(null);
          }}>
            <RotateCcw size={14} aria-hidden="true" /> {t("w.graphx.clear")}
          </button>
        </div>
        <div aria-live="polite" className="space-y-3">
          {walkError && <p className="rounded-lg bg-bad-soft px-3 py-2 text-sm text-ink">{walkError}</p>}
          {walk.edges.length > 0 && (
            <ul className="!ps-0 space-y-2">
              <Verdict ok={walkInfo.trail} label={t("w.graphx.walk.trail")} why={walkInfo.trail ? undefined : t("w.graphx.walk.repeated")} />
              <Verdict ok={walkInfo.closed} label={t("w.graphx.walk.closed")} why={walkInfo.circuit ? t("w.graphx.walk.circuit") : undefined} />
              <Verdict
                ok={walkInfo.eulerTrail}
                label={walkInfo.eulerCircuit ? t("w.graphx.walk.eulerCircuit") : t("w.graphx.walk.eulerTrail")}
                why={t("w.graphx.walk.progress", { used: walkInfo.usedEdges, total: E, length: walkInfo.length })}
              />
            </ul>
          )}
          <div className="rounded-xl border border-line px-4 py-3 text-sm text-ink-2">
            <p className="font-semibold text-ink">{euler.odd.length === 0 ? t("w.graphx.euler.oddNone") : t("w.graphx.euler.oddList", { count: euler.odd.length, list: oddNames })}</p>
            <p className="mt-1">{verdict}</p>
          </div>
        </div>
      </div>
    );
  } else if (mode === "colour") {
    panel = (
      <div className="space-y-3">
        <div className="grid grid-cols-3 gap-2 text-center">
          <Stat label={t("w.graphx.colour.used")} value={n(colInfo.used)} />
          <Stat label={t("w.graphx.colour.clashes")} value={n(colInfo.conflicts.length)} bad={colInfo.conflicts.length > 0} />
          <Stat label={t("w.graphx.colour.uncoloured")} value={n(colInfo.uncoloured)} />
        </div>
        <div className="flex flex-wrap gap-2">
          <button type="button" className="btn btn-sm btn-gold" onClick={() => {
            const g = greedyColouring(graph);
            setColours(g.map((c) => (c < PALETTE.length ? c : PALETTE.length - 1)));
            setColourNote(t("w.graphx.colour.greedyNote", { k: new Set(g).size }));
          }}>
            <Wand2 size={14} aria-hidden="true" /> {t("w.graphx.colour.greedy")}
          </button>
          <button type="button" className="btn btn-sm btn-ghost" aria-pressed={showChi} onClick={() => setShowChi((s) => !s)}>
            <Sparkles size={14} aria-hidden="true" /> {t("w.graphx.colour.fewest")}
          </button>
          <button type="button" className="btn btn-sm btn-ghost" onClick={() => {
            setColours(graph.labels.map(() => null));
            setColourNote(null);
          }}>
            <RotateCcw size={14} aria-hidden="true" /> {t("w.graphx.clear")}
          </button>
        </div>
        <div aria-live="polite" className="space-y-2 text-sm text-ink-2">
          {colInfo.proper ? (
            <p className="rounded-lg bg-good-soft px-3 py-2 font-semibold text-ink">{t("w.graphx.colour.proper", { k: colInfo.used })}</p>
          ) : colInfo.conflicts.length > 0 ? (
            <p className="rounded-lg bg-bad-soft px-3 py-2 text-ink">{t("w.graphx.colour.clash", { list: colInfo.conflicts.slice(0, 4).map(edgeName).join(", ") })}</p>
          ) : (
            <p>{t("w.graphx.colour.keepGoing")}</p>
          )}
          {colourNote && <p>{colourNote}</p>}
          {showChi && <p className="font-semibold text-ink">{chi === null ? t("w.graphx.colour.tooBig") : t("w.graphx.colour.chi", { k: chi })}</p>}
        </div>
        {planar !== undefined && <p className="rounded-xl bg-gold-soft px-4 py-3 text-sm text-ink">{planar ? t("w.graphx.colour.fourColour") : t("w.graphx.colour.notPlanar")}</p>}
      </div>
    );
  } else if (mode === "spanning") {
    panel = (
      <div className="space-y-3">
        <p className="rounded-xl bg-paper-2 px-4 py-3 text-sm text-ink-2">
          {t("w.graphx.span.count", { c: span.count, v: V, need: span.needed })}
        </p>
        <div className="flex flex-wrap gap-2">
          <button type="button" className="btn btn-sm btn-gold" onClick={() => setChosen(bfsTree(graph))}>
            <Wand2 size={14} aria-hidden="true" /> {t("w.graphx.span.showOne")}
          </button>
          <button type="button" className="btn btn-sm btn-ghost" disabled={chosen.length === 0} onClick={() => setChosen([])}>
            <RotateCcw size={14} aria-hidden="true" /> {t("w.graphx.clear")}
          </button>
        </div>
        <div aria-live="polite" className="space-y-3">
          {!connected ? (
            <p className="rounded-lg bg-warn-soft px-3 py-2 text-sm text-ink">{t("w.graphx.span.disconnectedGraph")}</p>
          ) : (
            <ul className="!ps-0 space-y-2">
              <Verdict
                ok={span.cycle === null}
                label={t("w.graphx.span.acyclic")}
                why={span.cycle ? t("w.graphx.span.cycle", { list: cycleText(graph, span.cycle, lab) }) : undefined}
              />
              <Verdict ok={span.pieces === 1} label={t("w.graphx.span.connected")} why={span.pieces > 1 ? t("w.graphx.span.pieces", { count: span.pieces }) : undefined} />
              <Verdict ok={span.isTree} label={t("w.graphx.span.tree")} why={span.isTree ? t("w.graphx.span.treeYes", { need: span.needed }) : undefined} />
            </ul>
          )}
        </div>
        {connected && <p className="text-sm text-muted">{t("w.graphx.span.tau", { tau: fmtBig(tau) })}</p>}
      </div>
    );
  } else {
    const [ci, cj] = cell ?? [-1, -1];
    const val = cell ? Ak[ci][cj] : 0;
    const walksList = cell && simple && power >= 2 && val > 0 && val <= 8 ? listWalks(graph, ci, cj, power, 8) : [];
    const trace3 = matPow(A, 3).reduce((s, row, i) => s + row[i], 0);
    panel = (
      <div className="space-y-3">
        <label className="block text-sm font-semibold text-ink-2">
          <span className="flex items-center justify-between">
            {t("w.graphx.matrix.power")}
            <span className="font-mono text-ink" dir="ltr">
              k = {power}
            </span>
          </span>
          <input type="range" min={1} max={MAX_K} value={power} onChange={(e) => setPower(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--formal)]" dir="ltr" />
        </label>
        <div aria-live="polite" className="space-y-2 text-sm text-ink-2">
          {cell ? (
            <>
              <p className="font-semibold text-ink">
                {power === 1 ? t("w.graphx.matrix.edges", { a: lab(ci), b: lab(cj), count: val }) : t("w.graphx.matrix.walks", { a: lab(ci), b: lab(cj), count: val, k: power })}
              </p>
              {walksList.length > 0 && (
                <p className="font-mono text-xs leading-relaxed text-ink-2" dir="ltr">
                  {walksList.map((w) => w.map(lab).join("→")).join(" · ")}
                </p>
              )}
            </>
          ) : (
            <p>{t("w.graphx.matrix.pick")}</p>
          )}
          {power === 1 && <p>{t("w.graphx.matrix.rowSums")}</p>}
          {power === 2 && simple && <p>{t("w.graphx.matrix.diag2")}</p>}
          {power === 3 && simple && <p>{t("w.graphx.matrix.triangles", { trace: trace3, count: trace3 / 6 })}</p>}
        </div>
      </div>
    );
  }

  const matrixTable =
    mode === "matrix" ? (
      <div className="mt-4 overflow-x-auto" dir="ltr">
        <table className="mx-auto !w-auto border-separate border-spacing-0.5 text-center font-mono text-sm [&_td]:!border-0 [&_td]:!p-0 [&_th]:!border-0 [&_th]:!p-0.5 [&_th]:!text-center">
          <caption className="pb-2 text-start font-sans text-xs font-semibold text-muted">{power === 1 ? "A" : `A^${power}`}</caption>
          <thead>
            <tr>
              <th className="h-9 min-w-9" aria-hidden="true" />
              {graph.labels.map((l, j) => (
                <th key={j} scope="col" className={`h-9 min-w-9 px-1 text-xs ${cell && cell[1] === j ? "text-gold-ink" : "text-muted"}`}>
                  {l}
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {Ak.map((row, i) => (
              <tr key={i}>
                <th scope="row" className={`h-9 min-w-9 px-1 text-xs ${cell && cell[0] === i ? "text-formal" : "text-muted"}`}>
                  {lab(i)}
                </th>
                {row.map((v, j) => {
                  const on = cell !== null && cell[0] === i && cell[1] === j;
                  return (
                    <td key={j} className="p-0">
                      <button
                        type="button"
                        aria-pressed={on}
                        aria-label={t("w.graphx.matrix.cellAria", { a: lab(i), b: lab(j), count: v })}
                        onClick={() => setCell(on ? null : [i, j])}
                        className={`h-9 min-w-9 rounded-md px-1.5 transition-colors ${on ? "bg-formal font-bold text-paper" : v === 0 ? "bg-paper-2 text-muted hover:bg-line" : "bg-formal-soft text-ink hover:bg-line"} ${i === j && !on ? "ring-1 ring-line-2" : ""}`}
                      >
                        {v}
                      </button>
                    </td>
                  );
                })}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    ) : null;

  return (
    <>
      <div className="mt-4 grid gap-5 md:grid-cols-[minmax(0,1.25fr)_minmax(0,1fr)]">
        <div>
          <div dir="ltr" className="rounded-xl border border-line bg-paper/40">
            {drawing}
          </div>
          <div className="mt-2 flex flex-wrap items-center gap-2">
            <span className="chip" dir="ltr">
              |V| = {V}
            </span>
            <span className="chip" dir="ltr">
              |E| = {E}
            </span>
            <span className="text-xs text-muted">{hint}</span>
          </div>
        </div>
        <div>{panel}</div>
      </div>
      {matrixTable}
    </>
  );
}

function cycleText(g: Graph, cycle: number[], lab: (i: number) => string): string {
  // Walk the cycle's edges in order to list its vertices.
  if (cycle.length === 0) return "";
  const [a0, b0] = g.edges[cycle[0]];
  const second = cycle.length > 1 ? g.edges[cycle[1]] : null;
  let cur = second && (second[0] === b0 || second[1] === b0) ? a0 : b0;
  const vs = [cur];
  for (const ei of cycle) {
    const [a, b] = g.edges[ei];
    cur = cur === a ? b : a;
    vs.push(cur);
  }
  return vs.map(lab).join("–");
}

function Verdict({ ok, label, why }: { ok: boolean; label: string; why?: string }) {
  return (
    <li className="flex items-start gap-2.5">
      <span className={`mt-0.5 flex h-5 w-5 shrink-0 items-center justify-center rounded-full ${ok ? "bg-good-soft text-good" : "bg-paper-2 text-muted"}`}>
        {ok ? <Check size={13} aria-hidden="true" /> : <X size={13} aria-hidden="true" />}
      </span>
      <span className="text-sm">
        <span className={`font-semibold ${ok ? "text-ink" : "text-ink-2"}`}>{label}</span>
        <span className="sr-only">{ok ? " ✓" : " ✗"}</span>
        {why && <span className="block text-muted">{why}</span>}
      </span>
    </li>
  );
}

function Stat({ label, value, bad }: { label: string; value: string; bad?: boolean }) {
  return (
    <div className={`rounded-xl px-2 py-2 ${bad ? "bg-bad-soft" : "bg-paper-2"}`}>
      <p className="text-xl font-bold text-ink">{value}</p>
      <p className="text-xs leading-tight text-muted">{label}</p>
    </div>
  );
}
