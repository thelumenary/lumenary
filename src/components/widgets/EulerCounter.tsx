"use client";

import { ArrowDown, ArrowLeft, ArrowRight, ArrowUp, Check, Eye, RotateCcw, X } from "lucide-react";
import { useId, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { SOLID_IDS, counts, getSolid, isSolidId, viewSolid, type SolidId } from "./lib/topo-polyhedra";
import { IDENTITY3, dragRotate, r2, type M3 } from "./lib/topo-vec";
import { useAnimationLoop, useReducedMotion } from "./lib/topo-dom";

type Tab = "solids" | "surfaces";
type Field = "V" | "E" | "F";
const FIELDS: Field[] = ["V", "E", "F"];

const W = 320;
const H = 290;
/** Frames are flat, so they can be drawn a little larger. */
const scaleOf = (id: SolidId) => (id === "torus" || id === "doubleTorus" ? 136 : 118);

const fmt = (v: number) => (v < 0 ? `−${-v}` : `${v}`);

/** A starting view for each solid, chosen so that some edges are visibly at the back. */
const VIEWS: Record<SolidId, [number, number]> = {
  tetrahedron: [-0.35, 0.3],
  cube: [-0.62, 0.42],
  octahedron: [-0.62, 0.42],
  dodecahedron: [-0.62, 0.42],
  icosahedron: [-0.62, 0.42],
  prism: [-0.5, 0.62],
  pyramid: [-0.62, 0.42],
  torus: [-0.5, 0.85],
  doubleTorus: [-0.32, 0.92],
};
function initialView(id: SolidId): M3 {
  const [yaw, pitch] = VIEWS[id];
  return dragRotate(dragRotate(IDENTITY3, yaw, 0), 0, pitch);
}

export interface EulerCounterProps {
  solids?: string[];
  tab?: Tab;
  askCount?: boolean;
  title?: string;
  subtitle?: string;
}

/**
 * Euler characteristic V − E + F: count on rotatable wireframe solids (convex
 * ones give 2, picture-frame tori give 0 and −2), then relate χ = 2 − 2g to the
 * genus of closed orientable surfaces and see that re-cutting never changes χ.
 */
export function EulerCounter({ solids, tab: initialTab, askCount = true, title, subtitle }: EulerCounterProps) {
  const { t } = useI18n();
  const gallery = useMemo<SolidId[]>(() => {
    const list = Array.isArray(solids) ? solids.filter(isSolidId) : [];
    return list.length ? [...new Set(list)] : [...SOLID_IDS];
  }, [solids]);
  const [tab, setTab] = useState<Tab>(initialTab === "surfaces" ? "surfaces" : "solids");

  return (
    <WidgetFrame title={title ?? t("w.euler.title")} subtitle={subtitle ?? t("w.euler.subtitle")}>
      <div className="flex flex-wrap gap-2" role="group" aria-label={t("w.euler.tabs")}>
        {(["solids", "surfaces"] as const).map((k) => (
          <button key={k} type="button" aria-pressed={tab === k} className={`btn btn-sm ${tab === k ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(k)}>
            {t(`w.euler.tab.${k}`)}
          </button>
        ))}
      </div>
      {tab === "solids" ? <SolidsPanel gallery={gallery} askCount={askCount !== false} /> : <SurfacesPanel />}
    </WidgetFrame>
  );
}

// ------------------------------------------------------------------ solids

type Answers = Record<Field, string>;
const EMPTY: Answers = { V: "", E: "", F: "" };

function SolidsPanel({ gallery, askCount }: { gallery: SolidId[]; askCount: boolean }) {
  const { t, n } = useI18n();
  const reduced = useReducedMotion();
  const [id, setId] = useState<SolidId>(gallery[0]);
  const [views, setViews] = useState<Partial<Record<SolidId, M3>>>({});
  const [answers, setAnswers] = useState<Partial<Record<SolidId, Answers>>>({});
  const [checked, setChecked] = useState<Partial<Record<SolidId, boolean>>>({});
  const [revealed, setRevealed] = useState<Partial<Record<SolidId, boolean>>>({});
  const [focus, setFocus] = useState<Field | null>(null);
  const [spin, setSpin] = useState<[number, number] | null>(null);
  const drag = useRef<{ x: number; y: number; pid: number } | null>(null);
  const uid = useId();

  const solid = getSolid(id);
  const c = counts(solid);
  const m = views[id] ?? initialView(id);
  const setM = (next: M3) => setViews((v) => ({ ...v, [id]: next }));
  const view = useMemo(() => viewSolid(solid, m), [solid, m]);
  const ans = answers[id] ?? EMPTY;
  const truth: Record<Field, number> = { V: c.V, E: c.E, F: c.F };
  const correct = (f: Field) => ans[f].trim() !== "" && Number(ans[f]) === truth[f];
  const solved = !askCount || revealed[id] || FIELDS.every(correct);

  // smooth rotation for the arrow buttons
  useAnimationLoop(spin !== null, (dt) => {
    if (!spin) return;
    const speed = 3.2 * dt;
    const sx = Math.sign(spin[0]) * Math.min(Math.abs(spin[0]), speed);
    const sy = Math.sign(spin[1]) * Math.min(Math.abs(spin[1]), speed);
    setViews((v) => ({ ...v, [id]: dragRotate(v[id] ?? initialView(id), sx, sy) }));
    const rest: [number, number] = [spin[0] - sx, spin[1] - sy];
    setSpin(Math.abs(rest[0]) < 1e-4 && Math.abs(rest[1]) < 1e-4 ? null : rest);
  });
  const rotate = (dx: number, dy: number) => {
    if (reduced) setM(dragRotate(m, dx, dy));
    else setSpin((s) => [(s?.[0] ?? 0) + dx, (s?.[1] ?? 0) + dy]);
  };

  const S = scaleOf(id);
  const P = (i: number) => [r2(W / 2 + S * view.pts[i][0]), r2(H / 2 - S * view.pts[i][1])] as const;
  const poly = (f: number[]) => f.map((i) => P(i).join(",")).join(" ");
  const done = (s: SolidId) => !askCount || revealed[s] || FIELDS.every((f) => {
    const a = answers[s]?.[f] ?? "";
    const cc = counts(getSolid(s));
    return a.trim() !== "" && Number(a) === cc[f];
  });

  const holeNote = solid.genus === 0 ? t("w.euler.noHoles") : solid.genus === 1 ? t("w.euler.oneHole") : t("w.euler.twoHoles");
  const name = t(`w.euler.solid.${id}`);

  return (
    <div className="mt-4">
      <div className="flex flex-wrap gap-1.5" role="group" aria-label={t("w.euler.chooseSolid")}>
        {gallery.map((s) => (
          <button
            key={s}
            type="button"
            aria-pressed={s === id}
            className={`btn btn-sm ${s === id ? "btn-primary" : "btn-ghost"}`}
            onClick={() => {
              setId(s);
              setFocus(null);
              setSpin(null);
            }}
          >
            {t(`w.euler.solid.${s}`)}
            {done(s) && <Check size={13} aria-hidden="true" className="text-good" />}
          </button>
        ))}
      </div>

      <div className="mt-4 grid gap-5 md:grid-cols-[1.1fr_1fr]">
        <div>
          <div dir="ltr" className="mx-auto max-w-[440px] rounded-2xl border border-line bg-paper-2/60">
            <svg
              viewBox={`0 0 ${W} ${H}`}
              className="w-full cursor-grab touch-none select-none active:cursor-grabbing"
              role="img"
              aria-label={t("w.euler.diagram", { name })}
              onPointerDown={(e) => {
                drag.current = { x: e.clientX, y: e.clientY, pid: e.pointerId };
                e.currentTarget.setPointerCapture(e.pointerId);
                setSpin(null);
              }}
              onPointerMove={(e) => {
                const d = drag.current;
                if (!d || d.pid !== e.pointerId) return;
                const dx = e.clientX - d.x;
                const dy = e.clientY - d.y;
                drag.current = { ...d, x: e.clientX, y: e.clientY };
                setViews((v) => ({ ...v, [id]: dragRotate(v[id] ?? initialView(id), dx * 0.011, dy * 0.011) }));
              }}
              onPointerUp={() => (drag.current = null)}
              onPointerCancel={() => (drag.current = null)}
            >
              {view.order.map((fi) => {
                const f = solid.faces[fi];
                return (
                  <g key={fi}>
                    <polygon points={poly(f)} fill="var(--card)" />
                    <polygon
                      points={poly(f)}
                      fill={focus === "F" ? "var(--gold)" : "var(--formal)"}
                      fillOpacity={focus === "F" ? 0.18 + 0.3 * view.shade[fi] : 0.05 + 0.22 * view.shade[fi]}
                      stroke={focus === "E" ? "var(--gold)" : "var(--formal)"}
                      strokeWidth={focus === "E" ? 2.6 : 1.7}
                      strokeLinejoin="round"
                    />
                    {f.map((i) => {
                      const [x, y] = P(i);
                      return focus === "V" ? (
                        <circle key={i} cx={x} cy={y} r={4.6} fill="var(--gold)" stroke="var(--card)" strokeWidth={1.5} />
                      ) : (
                        <circle key={i} cx={x} cy={y} r={2.5} fill="var(--ink-2)" />
                      );
                    })}
                  </g>
                );
              })}
              {solid.edges.map(([a, b], ei) =>
                view.hiddenEdge[ei] ? (
                  <line
                    key={ei}
                    x1={P(a)[0]}
                    y1={P(a)[1]}
                    x2={P(b)[0]}
                    y2={P(b)[1]}
                    stroke={focus === "E" ? "var(--gold-ink)" : "var(--muted)"}
                    strokeWidth={focus === "E" ? 1.8 : 1.2}
                    strokeDasharray="4 4"
                    opacity={0.85}
                  />
                ) : null,
              )}
              {solid.vertices.map((_, i) =>
                view.vertexFront[i] ? null : (
                  <circle key={i} cx={P(i)[0]} cy={P(i)[1]} r={focus === "V" ? 4 : 2.2} fill="var(--card)" stroke={focus === "V" ? "var(--gold-ink)" : "var(--muted)"} strokeWidth={1.3} />
                ),
              )}
            </svg>
          </div>
          <div className="mt-2 flex flex-wrap items-center justify-between gap-2">
            <p className="text-xs text-muted">{t("w.euler.dragHint")}</p>
            <div dir="ltr" className="flex gap-1">
              {(
                [
                  ["left", ArrowLeft, -0.3, 0],
                  ["up", ArrowUp, 0, -0.3],
                  ["down", ArrowDown, 0, 0.3],
                  ["right", ArrowRight, 0.3, 0],
                ] as const
              ).map(([k, Icon, dx, dy]) => (
                <button key={k} type="button" className="btn btn-sm btn-ghost px-2" aria-label={t(`w.euler.rotate.${k}`)} title={t(`w.euler.rotate.${k}`)} onClick={() => rotate(dx, dy)}>
                  <Icon size={15} aria-hidden="true" />
                </button>
              ))}
              <button
                type="button"
                className="btn btn-sm btn-ghost px-2"
                aria-label={t("w.euler.rotate.reset")}
                title={t("w.euler.rotate.reset")}
                onClick={() => {
                  setSpin(null);
                  setM(initialView(id));
                }}
              >
                <RotateCcw size={15} aria-hidden="true" />
              </button>
            </div>
          </div>
        </div>

        <div>
          <p className="font-semibold text-ink">{name}</p>
          {askCount ? (
            <>
              <p className="mt-1 text-sm text-ink-2">{t("w.euler.countPrompt")}</p>
              <div className="mt-3 grid grid-cols-3 gap-2">
                {FIELDS.map((f) => (
                  <label key={f} className="block text-sm font-semibold text-ink-2">
                    <span className="block">
                      {t(`w.euler.count.${f}`)} <span className="font-serif italic text-ink">{f}</span>
                    </span>
                    <input
                      type="number"
                      inputMode="numeric"
                      min={0}
                      max={999}
                      className="input mt-1 text-center font-mono"
                      dir="ltr"
                      value={revealed[id] ? String(truth[f]) : ans[f]}
                      readOnly={!!revealed[id]}
                      onFocus={() => setFocus(f)}
                      onBlur={() => setFocus((x) => (x === f ? null : x))}
                      onChange={(e) => {
                        setAnswers((a) => ({ ...a, [id]: { ...(a[id] ?? EMPTY), [f]: e.target.value.slice(0, 4) } }));
                        setChecked((cc) => ({ ...cc, [id]: false }));
                      }}
                      aria-describedby={`${uid}-${f}`}
                    />
                    <span id={`${uid}-${f}`} className="mt-1 flex h-5 items-center gap-1 text-xs font-medium">
                      {(checked[id] || revealed[id]) &&
                        (correct(f) || revealed[id] ? (
                          <span className="flex items-center gap-1 text-good">
                            <Check size={12} aria-hidden="true" /> {t("w.euler.right")}
                          </span>
                        ) : (
                          <span className="flex items-center gap-1 text-bad">
                            <X size={12} aria-hidden="true" /> {t("w.euler.notYet")}
                          </span>
                        ))}
                    </span>
                  </label>
                ))}
              </div>
              <div className="mt-1 flex flex-wrap gap-2">
                <button type="button" className="btn btn-sm btn-primary" disabled={!!revealed[id]} onClick={() => setChecked((cc) => ({ ...cc, [id]: true }))}>
                  <Check size={14} aria-hidden="true" /> {t("w.euler.check")}
                </button>
                <button type="button" className="btn btn-sm btn-ghost" disabled={!!revealed[id]} onClick={() => setRevealed((r) => ({ ...r, [id]: true }))}>
                  <Eye size={14} aria-hidden="true" /> {t("w.euler.reveal")}
                </button>
              </div>
            </>
          ) : (
            <dl className="mt-3 grid grid-cols-3 gap-2 text-center">
              {FIELDS.map((f) => (
                <div key={f} className="rounded-xl bg-paper-2 px-2 py-2">
                  <dt className="text-xs font-semibold text-ink-2">{t(`w.euler.count.${f}`)}</dt>
                  <dd className="font-mono text-xl text-ink" dir="ltr">
                    {truth[f]}
                  </dd>
                </div>
              ))}
            </dl>
          )}

          <div aria-live="polite" className="mt-4">
            {solved ? (
              <div className="rounded-xl bg-gold-soft px-4 py-3">
                <p className="font-serif text-xl text-ink" dir="ltr">
                  V − E + F = {c.V} − {c.E} + {c.F} = <strong className="text-gold-ink">{fmt(c.chi)}</strong>
                </p>
                <p className="mt-1 text-sm text-ink">{holeNote}</p>
              </div>
            ) : checked[id] && FIELDS.some((f) => !correct(f)) ? (
              <p className="text-sm text-ink-2">{t("w.euler.keepCounting")}</p>
            ) : null}
          </div>
        </div>
      </div>

      <div className="mt-5 overflow-x-auto">
        <table className="w-full min-w-[300px] text-sm">
          <caption className="mb-1.5 text-start text-sm font-semibold text-ink">{t("w.euler.table.title")}</caption>
          <thead>
            <tr className="border-b border-line text-ink-2">
              <th scope="col" className="py-1.5 pe-2 text-start font-semibold">
                {t("w.euler.table.solid")}
              </th>
              {FIELDS.map((f) => (
                <th key={f} scope="col" className="px-2 py-1.5 text-center font-serif font-semibold italic">
                  {f}
                </th>
              ))}
              <th scope="col" className="ps-2 py-1.5 text-center font-serif font-semibold" dir="ltr">
                V − E + F
              </th>
            </tr>
          </thead>
          <tbody>
            {gallery.map((s) => {
              const cc = counts(getSolid(s));
              const ok = done(s);
              return (
                <tr key={s} className={`border-b border-line/60 ${s === id ? "bg-paper-2/70" : ""}`}>
                  <th scope="row" className="py-1.5 pe-2 text-start font-medium text-ink">
                    {t(`w.euler.solid.${s}`)}
                  </th>
                  {FIELDS.map((f) => (
                    <td key={f} className="px-2 py-1.5 text-center font-mono text-ink-2" dir="ltr">
                      {ok ? cc[f] : "?"}
                    </td>
                  ))}
                  <td className={`ps-2 py-1.5 text-center font-mono font-bold ${ok ? (cc.chi === 2 ? "text-good" : "text-formal") : "text-muted"}`} dir="ltr">
                    {ok ? fmt(cc.chi) : "?"}
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
        <p className="mt-2 text-xs text-muted">
          {t("w.euler.table.note", { done: n(gallery.filter(done).length), total: n(gallery.length) })}
        </p>
      </div>
    </div>
  );
}

// ------------------------------------------------------------------ surfaces

const MODELS: Record<number, SolidId | null> = { 0: "cube", 1: "torus", 2: "doubleTorus", 3: null };
type Move = "edge" | "diagonal" | "star";
const MOVES: Record<Move, [number, number, number]> = { edge: [1, 1, 0], diagonal: [0, 1, 1], star: [1, 3, 2] };

function SurfacesPanel() {
  const { t, n } = useI18n();
  const [g, setG] = useState(1);
  const [extra, setExtra] = useState<[number, number, number]>([0, 0, 0]);
  const [history, setHistory] = useState<Move[]>([]);
  const model = MODELS[g];
  const base = model ? counts(getSolid(model)) : null;
  const chi = 2 - 2 * g;
  const cur = base ? { V: base.V + extra[0], E: base.E + extra[1], F: base.F + extra[2] } : null;

  return (
    <div className="mt-4">
      <p className="text-sm text-ink-2">{t("w.euler.surf.intro")}</p>
      <div className="mt-3 flex flex-wrap gap-1.5" role="group" aria-label={t("w.euler.surf.choose")}>
        {[0, 1, 2, 3].map((k) => (
          <button
            key={k}
            type="button"
            aria-pressed={g === k}
            className={`btn btn-sm ${g === k ? "btn-primary" : "btn-ghost"}`}
            onClick={() => {
              setG(k);
              setExtra([0, 0, 0]);
              setHistory([]);
            }}
          >
            {t(`w.euler.surf.name.${k}`)}
          </button>
        ))}
      </div>
      <div className="mt-4 grid items-center gap-5 md:grid-cols-[1.1fr_1fr]">
        <div dir="ltr" className="rounded-2xl border border-line bg-paper-2/60 px-2 py-3">
          <SurfaceDrawing g={g} label={`${t(`w.euler.surf.name.${g}`)}: ${t("w.euler.surf.genus", { g: n(g) })}`} />
        </div>
        <div aria-live="polite">
          <p className="chip">{t("w.euler.surf.genus", { g: n(g) })}</p>
          <p className="mt-2 font-serif text-2xl text-ink" dir="ltr">
            χ = 2 − 2g = 2 − 2·{g} = <strong className="text-gold-ink">{fmt(chi)}</strong>
          </p>
          <p className="mt-2 text-sm text-ink-2">{t("w.euler.surf.handles")}</p>
          {model && base ? (
            <p className="mt-2 text-sm text-ink-2">
              {t("w.euler.surf.model", { name: t(`w.euler.solid.${model}`) })}{" "}
              <span className="font-mono text-ink" dir="ltr">
                V = {base.V}, E = {base.E}, F = {base.F}
              </span>
            </p>
          ) : (
            <p className="mt-2 text-sm text-ink-2">{t("w.euler.surf.noModel")}</p>
          )}
        </div>
      </div>

      {cur && (
        <div className="mt-5 rounded-2xl border border-line p-4">
          <p className="font-semibold text-ink">{t("w.euler.moves.title")}</p>
          <p className="mt-1 text-sm text-ink-2">{t("w.euler.moves.intro")}</p>
          <div className="mt-3 flex flex-wrap gap-2">
            {(Object.keys(MOVES) as Move[]).map((mv) => (
              <button
                key={mv}
                type="button"
                className="btn btn-sm btn-ghost"
                onClick={() => {
                  const d = MOVES[mv];
                  setExtra((x) => [x[0] + d[0], x[1] + d[1], x[2] + d[2]]);
                  setHistory((h) => [...h, mv].slice(-40));
                }}
              >
                {t(`w.euler.moves.${mv}`)}
                <span className="font-mono text-xs text-muted" dir="ltr">
                  {MOVES[mv][0] ? `V+${MOVES[mv][0]} ` : ""}E+{MOVES[mv][1]}
                  {MOVES[mv][2] ? ` F+${MOVES[mv][2]}` : ""}
                </span>
              </button>
            ))}
            <button
              type="button"
              className="btn btn-sm btn-ghost"
              disabled={history.length === 0}
              onClick={() => {
                setExtra([0, 0, 0]);
                setHistory([]);
              }}
            >
              <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
            </button>
          </div>
          <p className="mt-3 rounded-xl bg-paper-2 px-4 py-2.5 font-serif text-xl text-ink" dir="ltr" aria-live="polite">
            V − E + F = {cur.V} − {cur.E} + {cur.F} = <strong className="text-gold-ink">{fmt(cur.V - cur.E + cur.F)}</strong>
          </p>
          <p className="mt-2 text-sm text-ink-2">{history.length ? t("w.euler.moves.after", { k: n(history.length) }) : t("w.euler.moves.note")}</p>
        </div>
      )}

      <div className="mt-4 space-y-2 text-sm text-ink-2">
        <p>{t("w.euler.surf.invariant")}</p>
        <p className="rounded-xl bg-warn-soft px-4 py-3 text-ink">{t("w.euler.surf.honest")}</p>
        <p className="text-xs text-muted">{t("w.euler.surf.orientable")}</p>
      </div>
    </div>
  );
}

/** A schematic closed orientable surface of genus g (0–3). */
function SurfaceDrawing({ g, label }: { g: number; label: string }) {
  const Wd = 360;
  const Hd = 180;
  const cy = Hd / 2;
  if (g === 0) {
    return (
      <svg viewBox={`0 0 ${Wd} ${Hd}`} className="mx-auto w-full max-w-[360px]" role="img" aria-label={label}>
        <circle cx={Wd / 2} cy={cy} r={72} fill="var(--formal-soft)" stroke="var(--formal)" strokeWidth={2} />
        <path d={`M${Wd / 2 - 72} ${cy} A72 20 0 0 0 ${Wd / 2 + 72} ${cy}`} fill="none" stroke="var(--formal)" strokeWidth={1.4} />
        <path d={`M${Wd / 2 - 72} ${cy} A72 20 0 0 1 ${Wd / 2 + 72} ${cy}`} fill="none" stroke="var(--formal)" strokeWidth={1.2} strokeDasharray="4 4" opacity={0.6} />
        <ellipse cx={Wd / 2 - 26} cy={cy - 34} rx={16} ry={9} fill="var(--card)" opacity={0.55} transform={`rotate(-30 ${Wd / 2 - 26} ${cy - 34})`} />
      </svg>
    );
  }
  const d = g === 3 ? 92 : 104;
  const rx = d / 2 + (g === 1 ? 60 : 26);
  const ry = g === 1 ? 64 : 62;
  const xs = Array.from({ length: g }, (_, i) => Wd / 2 + (i - (g - 1) / 2) * d);
  let outline: string;
  if (g === 1) {
    outline = `M${xs[0] - rx} ${cy} A${rx} ${ry} 0 0 1 ${xs[0] + rx} ${cy} A${rx} ${ry} 0 0 1 ${xs[0] - rx} ${cy}Z`;
  } else {
    const ym = ry * Math.sqrt(1 - (d / 2 / rx) ** 2);
    let p = `M${r2(xs[0] - rx)} ${cy}`;
    for (let i = 0; i < g; i++) {
      const end = i === g - 1 ? [xs[i] + rx, cy] : [(xs[i] + xs[i + 1]) / 2, cy - ym];
      p += ` A${rx} ${ry} 0 0 1 ${r2(end[0])} ${r2(end[1])}`;
    }
    for (let i = g - 1; i >= 0; i--) {
      const end = i === 0 ? [xs[0] - rx, cy] : [(xs[i] + xs[i - 1]) / 2, cy + ym];
      p += ` A${rx} ${ry} 0 0 1 ${r2(end[0])} ${r2(end[1])}`;
    }
    outline = `${p}Z`;
  }
  return (
    <svg viewBox={`0 0 ${Wd} ${Hd}`} className="mx-auto w-full max-w-[360px]" role="img" aria-label={label}>
      <path d={outline} fill="var(--formal-soft)" stroke="var(--formal)" strokeWidth={2} strokeLinejoin="round" />
      {xs.map((x, i) => {
        const hw = g === 1 ? 46 : 31;
        return (
          <g key={i} fill="none" stroke="var(--formal)" strokeWidth={2} strokeLinecap="round">
            <path d={`M${x - hw} ${cy - 4} Q${x} ${cy + hw * 0.62} ${x + hw} ${cy - 4}`} fill="var(--card)" fillOpacity={0.35} />
            <path d={`M${x - hw * 0.7} ${cy + hw * 0.12} Q${x} ${cy - hw * 0.34} ${x + hw * 0.7} ${cy + hw * 0.12}`} />
          </g>
        );
      })}
    </svg>
  );
}
