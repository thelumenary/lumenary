"use client";

import { ArrowDown, ArrowUp, Eraser, Grid3x3, Pause, Play, RotateCcw, RotateCw } from "lucide-react";
import { useId, useMemo, useReducer, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  SIDES,
  SURFACES,
  SURFACE_IDS,
  applyAffine,
  applyLinear,
  detM2,
  heading,
  isMirrored,
  isSurfaceId,
  makeWalker,
  move,
  mulM2,
  sideArrow,
  squareEuler,
  tileMirrored,
  toTile,
  turn,
  type Crossing,
  type M2,
  type Side,
  type SurfaceDef,
  type SurfaceId,
  type Walker,
} from "./lib/topo-gluing";
import { r2, type V2 } from "./lib/topo-vec";
import { useAnimationLoop } from "./lib/topo-dom";

const STEP = 0.035;
const TURN = Math.PI / 12;
const MAX_POINTS = 2400;

interface Polyline {
  pts: V2[];
  mirrored: boolean;
}
interface Sim {
  walker: Walker;
  trail: Polyline[];
  crossings: number;
  last: Crossing | null;
  dragChart: M2;
}
type Action = { type: "move"; def: SurfaceDef; d: V2 } | { type: "drag"; def: SurfaceDef; d: V2 } | { type: "dragStart" } | { type: "turn"; a: number } | { type: "reset" } | { type: "clear" };

function initialSim(): Sim {
  const walker = makeWalker([0.3, 0.36], 0.35);
  return { walker, trail: [{ pts: [walker.p], mirrored: false }], crossings: 0, last: null, dragChart: [1, 0, 0, 1] };
}

function capTrail(trail: Polyline[]): Polyline[] {
  let total = trail.reduce((a, p) => a + p.pts.length, 0);
  const out = [...trail];
  while (total > MAX_POINTS && out.length > 1) total -= out.shift()!.pts.length;
  if (total > MAX_POINTS) out[0] = { ...out[0], pts: out[0].pts.slice(total - MAX_POINTS) };
  return out;
}

function advance(s: Sim, def: SurfaceDef, d: V2, chartFor?: M2): Sim {
  const r = move(def, s.walker, d);
  const trail = s.trail.slice(0, -1);
  const lastLine = s.trail[s.trail.length - 1];
  let cur: Polyline = { pts: [...lastLine.pts], mirrored: lastLine.mirrored };
  let frame = s.walker.frame;
  for (const c of r.crossings) {
    cur.pts.push(c.out);
    trail.push(cur);
    frame = mulM2(def.exit[c.from].m, frame);
    // each new piece of trail remembers whether the walker was mirrored while drawing it
    cur = { pts: [c.in], mirrored: detM2(frame) < 0 };
  }
  cur.pts.push(r.walker.p);
  trail.push(cur);
  return {
    walker: r.walker,
    trail: capTrail(trail),
    crossings: s.crossings + r.crossings.length,
    last: r.crossings.length ? r.crossings[r.crossings.length - 1] : s.last,
    dragChart: chartFor ? mulM2(r.chart, chartFor) : s.dragChart,
  };
}

function reducer(s: Sim, a: Action): Sim {
  switch (a.type) {
    case "move":
      return advance(s, a.def, a.d);
    case "drag":
      return advance(s, a.def, applyLinear(s.dragChart, a.d), s.dragChart);
    case "dragStart":
      return { ...s, dragChart: [1, 0, 0, 1] };
    case "turn":
      return { ...s, walker: turn(s.walker, a.a) };
    case "clear":
      return { ...s, trail: [{ pts: [s.walker.p], mirrored: isMirrored(s.walker) }], crossings: 0, last: null };
    case "reset":
      return initialSim();
  }
}

export interface SurfaceGluingProps {
  surface?: SurfaceId;
  surfaces?: SurfaceId[];
  showTiling?: boolean;
  title?: string;
  subtitle?: string;
}

/**
 * Surfaces from a square with glued edges (torus, Klein bottle, sphere,
 * projective plane). A flatlander with a flag in its left hand walks around;
 * crossing an edge brings it back through the partner edge — mirrored when the
 * gluing reverses orientation.
 */
export function SurfaceGluing({ surface, surfaces, showTiling = false, title, subtitle }: SurfaceGluingProps) {
  const { t, n } = useI18n();
  const allowed = useMemo<SurfaceId[]>(() => {
    const list = Array.isArray(surfaces) ? SURFACE_IDS.filter((s) => surfaces.includes(s)) : [];
    return list.length ? list : [...SURFACE_IDS];
  }, [surfaces]);
  const [id, setId] = useState<SurfaceId>(isSurfaceId(surface) && allowed.includes(surface) ? surface : allowed[0]);
  const [sim, dispatch] = useReducer(reducer, undefined, initialSim);
  const [walking, setWalking] = useState(false);
  const [tiling, setTiling] = useState(!!showTiling);
  const svgRef = useRef<SVGSVGElement>(null);
  const drag = useRef<{ x: number; y: number; pid: number } | null>(null);
  const def = SURFACES[id];
  const euler = squareEuler(def);
  const mirrored = isMirrored(sim.walker);
  const tilingOn = tiling && def.tiles;

  useAnimationLoop(walking, (dt) => {
    const h = heading(sim.walker);
    dispatch({ type: "move", def, d: [h[0] * 0.28 * dt, h[1] * 0.28 * dt] });
  });

  const forward = (k: number) => {
    const h = heading(sim.walker);
    dispatch({ type: "move", def, d: [h[0] * STEP * k, h[1] * STEP * k] });
  };

  const onKey = (e: React.KeyboardEvent) => {
    const actions: Record<string, () => void> = {
      ArrowUp: () => forward(1),
      ArrowDown: () => forward(-1),
      ArrowLeft: () => dispatch({ type: "turn", a: TURN }),
      ArrowRight: () => dispatch({ type: "turn", a: -TURN }),
      " ": () => setWalking((w) => !w),
    };
    const f = actions[e.key];
    if (f) {
      e.preventDefault();
      f();
    }
  };

  const status = mirrored ? t("w.gluing.status.mirrored") : t("w.gluing.status.normal");
  const word = def.word.map((l) => `${l.name}${l.exp === -1 ? "⁻¹" : ""}`).join(" ");

  return (
    <WidgetFrame title={title ?? t("w.gluing.title")} subtitle={subtitle ?? t("w.gluing.subtitle")}>
      {allowed.length > 1 && (
        <div className="flex flex-wrap gap-2" role="group" aria-label={t("w.gluing.choose")}>
          {allowed.map((s) => (
            <button
              key={s}
              type="button"
              aria-pressed={id === s}
              className={`btn btn-sm ${id === s ? "btn-primary" : "btn-ghost"}`}
              onClick={() => {
                setId(s);
                setWalking(false);
                dispatch({ type: "reset" });
              }}
            >
              {t(`w.gluing.surface.${s}`)}
            </button>
          ))}
        </div>
      )}
      <div className="mt-4 grid gap-5 md:grid-cols-[1.15fr_1fr]">
        <div>
          <div dir="ltr" className="mx-auto max-w-[420px]">
            <svg
              ref={svgRef}
              viewBox="0 0 400 400"
              className="w-full touch-none select-none rounded-2xl border border-line bg-paper-2/60 outline-none focus-visible:ring-2 focus-visible:ring-[var(--sky)]"
              role="application"
              tabIndex={0}
              aria-roledescription={t("w.gluing.roledesc")}
              aria-label={`${t(`w.gluing.surface.${id}`)}. ${t("w.gluing.keys")}`}
              onKeyDown={onKey}
              onPointerDown={(e) => {
                drag.current = { x: e.clientX, y: e.clientY, pid: e.pointerId };
                e.currentTarget.setPointerCapture(e.pointerId);
                dispatch({ type: "dragStart" });
              }}
              onPointerMove={(e) => {
                const d = drag.current;
                if (!d || d.pid !== e.pointerId) return;
                const rect = svgRef.current?.getBoundingClientRect();
                if (!rect || !rect.width) return;
                const unit = (tilingOn ? 110 : 300) * (rect.width / 400);
                const dx = (e.clientX - d.x) / unit;
                const dy = -(e.clientY - d.y) / unit;
                drag.current = { ...d, x: e.clientX, y: e.clientY };
                if (dx || dy) dispatch({ type: "drag", def, d: [dx, dy] });
              }}
              onPointerUp={() => (drag.current = null)}
              onPointerCancel={() => (drag.current = null)}
            >
              {tilingOn ? <TilingView id={id} sim={sim} /> : <SquareView def={def} sim={sim} />}
            </svg>
          </div>
          <div className="mt-3 flex flex-wrap items-center justify-center gap-1.5">
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => dispatch({ type: "turn", a: TURN })}>
              <RotateCcw size={15} aria-hidden="true" /> {t("w.gluing.turnLeft")}
            </button>
            <button type="button" className="btn btn-sm btn-primary" onClick={() => forward(1)}>
              <ArrowUp size={15} aria-hidden="true" /> {t("w.gluing.forward")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => dispatch({ type: "turn", a: -TURN })}>
              <RotateCw size={15} aria-hidden="true" /> {t("w.gluing.turnRight")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => forward(-1)}>
              <ArrowDown size={15} aria-hidden="true" /> {t("w.gluing.back")}
            </button>
          </div>
          <div className="mt-2 flex flex-wrap items-center justify-center gap-1.5">
            <button type="button" className="btn btn-sm btn-gold" aria-pressed={walking} onClick={() => setWalking((w) => !w)}>
              {walking ? <Pause size={15} aria-hidden="true" /> : <Play size={15} aria-hidden="true" />} {walking ? t("w.gluing.stop") : t("w.gluing.walk")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => dispatch({ type: "clear" })}>
              <Eraser size={15} aria-hidden="true" /> {t("w.gluing.clear")}
            </button>
            {def.tiles && (
              <button type="button" className="btn btn-sm btn-ghost" aria-pressed={tiling} onClick={() => setTiling((v) => !v)}>
                <Grid3x3 size={15} aria-hidden="true" /> {t("w.gluing.tiling")}
              </button>
            )}
          </div>
          <p className="mt-2 text-center text-xs text-muted">{t("w.gluing.keys")}</p>
        </div>

        <div className="space-y-3">
          <div className="flex flex-wrap items-center gap-2">
            <span className="font-semibold text-ink">{t(`w.gluing.surface.${id}`)}</span>
            <span className="chip font-serif" dir="ltr">
              {word}
            </span>
          </div>
          <dl className="grid grid-cols-2 gap-2 text-center">
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.gluing.orientable")}</dt>
              <dd className={`font-semibold ${def.orientable ? "text-good" : "text-formal"}`}>{def.orientable ? t("w.gluing.yes") : t("w.gluing.no")}</dd>
            </div>
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.gluing.euler")}</dt>
              <dd className="font-serif text-lg text-ink" dir="ltr">
                χ = {def.chi}
              </dd>
            </div>
          </dl>
          <p className="text-xs text-muted">
            {t("w.gluing.chiWhy", { v: n(euler.V) })}{" "}
            <span className="font-mono text-ink-2" dir="ltr">
              V − E + F = {euler.V} − 2 + 1 = {euler.chi}
            </span>
          </p>
          <div aria-live="polite" className={`rounded-xl px-4 py-3 text-sm ${mirrored ? "bg-formal-soft" : "bg-gold-soft"}`}>
            <p className="flex items-center gap-2 font-semibold text-ink">
              <svg viewBox="-1.9 -1.9 3.8 3.8" className="h-10 w-10 shrink-0" aria-hidden="true">
                <g transform={mirrored ? "scale(-1,-1) rotate(90)" : "scale(1,-1) rotate(90)"}>
                  <Creature />
                </g>
              </svg>
              {status}
            </p>
            <p className="mt-1 text-ink-2">{t("w.gluing.crossed", { k: n(sim.crossings) })}</p>
            {sim.last && (
              <p className="mt-1 text-ink-2">
                {t("w.gluing.lastCrossing", { from: t(`w.gluing.side.${sim.last.from}`), to: t(`w.gluing.side.${sim.last.to}`) })}
              </p>
            )}
          </div>
          <p className="text-sm text-ink-2">{t(`w.gluing.about.${id}`)}</p>
          {mirrored && <p className="text-sm text-ink-2">{t("w.gluing.turnNote")}</p>}
          {tiling && def.tiles && <p className="text-sm text-ink-2">{t(`w.gluing.tilingNote.${id}`)}</p>}
          {tiling && !def.tiles && <p className="text-sm text-muted">{t("w.gluing.noTiling")}</p>}
        </div>
      </div>
    </WidgetFrame>
  );
}

// ------------------------------------------------------------------ drawing

const LETTER_COLOUR: Record<"a" | "b", string> = { a: "var(--human)", b: "var(--compute)" };

/** A little flatlander, facing +x, with a flag in its left hand (+y). Drawn in unit coordinates. */
function Creature() {
  return (
    <g strokeLinejoin="round" strokeLinecap="round">
      <line x1={0.15} y1={0.55} x2={0.55} y2={1.15} stroke="var(--ink)" strokeWidth={0.13} />
      <line x1={0.55} y1={1.15} x2={0.55} y2={1.75} stroke="var(--ink)" strokeWidth={0.09} />
      <path d="M0.55 1.75 L1.25 1.55 L0.55 1.35 Z" fill="var(--human)" stroke="var(--ink)" strokeWidth={0.06} />
      <ellipse cx={0} cy={0} rx={0.95} ry={0.72} fill="var(--gold)" stroke="var(--ink)" strokeWidth={0.1} />
      <circle cx={0.52} cy={0.26} r={0.17} fill="var(--card)" stroke="var(--ink)" strokeWidth={0.05} />
      <circle cx={0.52} cy={-0.26} r={0.17} fill="var(--card)" stroke="var(--ink)" strokeWidth={0.05} />
      <circle cx={0.6} cy={0.26} r={0.08} fill="var(--ink)" />
      <circle cx={0.6} cy={-0.26} r={0.08} fill="var(--ink)" />
      <circle cx={0.55} cy={1.15} r={0.16} fill="var(--human)" stroke="var(--ink)" strokeWidth={0.05} />
    </g>
  );
}

/**
 * Draw trail + walker with a given map from square coordinates to screen (and its linear part).
 * Near a side, a "ghost" of the walker is also drawn where it re-enters, so it visibly passes through the seam.
 */
function Layer({ def, sim, toScreen, lin, size }: { def: SurfaceDef; sim: Sim; toScreen: (p: V2) => V2; lin: M2; size: number }) {
  const w = sim.walker;
  const reach = size * 2.2;
  const near: Record<Side, boolean> = { left: w.p[0] < reach, right: w.p[0] > 1 - reach, bottom: w.p[1] < reach, top: w.p[1] > 1 - reach };
  const copies: { p: V2; frame: M2 }[] = [{ p: w.p, frame: w.frame }];
  for (const side of SIDES) if (near[side]) copies.push({ p: applyAffine(def.exit[side], w.p), frame: mulM2(def.exit[side].m, w.frame) });
  return (
    <g>
      {sim.trail.map((line, i) =>
        line.pts.length > 1 ? (
          <path
            key={i}
            d={line.pts.map((q, j) => `${j ? "L" : "M"}${r2(toScreen(q)[0])} ${r2(toScreen(q)[1])}`).join("")}
            fill="none"
            stroke={line.mirrored ? "var(--formal)" : "var(--gold)"}
            strokeWidth={2.4}
            strokeDasharray={line.mirrored ? "5 4" : undefined}
            strokeLinecap="round"
            opacity={0.85}
          />
        ) : null,
      )}
      {copies.map((c, k) => {
        const p = toScreen(c.p);
        const F = c.frame;
        // local (forward, left) → square: F · size; square → screen: lin
        const m = mulM2(lin, [F[0] * size, F[1] * size, F[2] * size, F[3] * size]);
        return (
          <g key={k} transform={`matrix(${r2(m[0])} ${r2(m[2])} ${r2(m[1])} ${r2(m[3])} ${r2(p[0])} ${r2(p[1])})`}>
            <Creature />
          </g>
        );
      })}
    </g>
  );
}

function Arrowheads({ from, to, count, colour }: { from: V2; to: V2; count: number; colour: string }) {
  const d: V2 = [to[0] - from[0], to[1] - from[1]];
  const L = Math.hypot(d[0], d[1]);
  const u: V2 = [d[0] / L, d[1] / L];
  const nrm: V2 = [-u[1], u[0]];
  const mid: V2 = [(from[0] + to[0]) / 2, (from[1] + to[1]) / 2];
  return (
    <g fill="none" stroke={colour} strokeWidth={3} strokeLinecap="round" strokeLinejoin="round">
      {Array.from({ length: count }, (_, k) => {
        const off = (k - (count - 1) / 2) * 11 + 6;
        const tip: V2 = [mid[0] + u[0] * off, mid[1] + u[1] * off];
        const a: V2 = [tip[0] - u[0] * 10 + nrm[0] * 8, tip[1] - u[1] * 10 + nrm[1] * 8];
        const b: V2 = [tip[0] - u[0] * 10 - nrm[0] * 8, tip[1] - u[1] * 10 - nrm[1] * 8];
        return <path key={k} d={`M${r2(a[0])} ${r2(a[1])}L${r2(tip[0])} ${r2(tip[1])}L${r2(b[0])} ${r2(b[1])}`} />;
      })}
    </g>
  );
}

function SquareView({ def, sim }: { def: SurfaceDef; sim: Sim }) {
  const clip = `${useId().replace(/:/g, "")}-sq`;
  const X0 = 50;
  const S = 300;
  const toScreen = (p: V2): V2 => [X0 + S * p[0], X0 + S * (1 - p[1])];
  const outward: Record<Side, V2> = { bottom: [0, 1], top: [0, -1], left: [-1, 0], right: [1, 0] };
  const lastSides = sim.last ? [sim.last.from, sim.last.to] : [];
  return (
    <g>
      <rect x={X0} y={X0} width={S} height={S} fill="var(--card)" />
      <defs>
        <clipPath id={clip}>
          <rect x={X0} y={X0} width={S} height={S} />
        </clipPath>
      </defs>
      <g clipPath={`url(#${clip})`}>
        <Layer def={def} sim={sim} toScreen={toScreen} lin={[S, 0, 0, -S]} size={0.072} />
      </g>
      {SIDES.map((side, i) => {
        const L = def.word[i];
        const [a, b] = sideArrow(side, L.exp).map(toScreen);
        const ccw = sideArrow(side, 1).map(toScreen);
        const colour = LETTER_COLOUR[L.name];
        const o = outward[side];
        const mid: V2 = [(ccw[0][0] + ccw[1][0]) / 2 + o[0] * 24, (ccw[0][1] + ccw[1][1]) / 2 + o[1] * 24];
        const hot = lastSides.includes(side);
        return (
          <g key={side}>
            {hot && <line x1={ccw[0][0]} y1={ccw[0][1]} x2={ccw[1][0]} y2={ccw[1][1]} stroke={colour} strokeWidth={10} opacity={0.25} strokeLinecap="round" />}
            <line x1={ccw[0][0]} y1={ccw[0][1]} x2={ccw[1][0]} y2={ccw[1][1]} stroke={colour} strokeWidth={3} strokeLinecap="round" />
            <Arrowheads from={a} to={b} count={L.name === "a" ? 1 : 2} colour={colour} />
            <text x={mid[0]} y={mid[1] + 6} textAnchor="middle" fontSize="19" fontStyle="italic" fontWeight={700} fill={colour} style={{ fontFamily: "var(--font-serif)" }}>
              {L.name}
            </text>
          </g>
        );
      })}
    </g>
  );
}

function TilingView({ id, sim }: { id: SurfaceId; sim: Sim }) {
  const uid = useId().replace(/:/g, "");
  const T = 110;
  const X0 = 35;
  const tiles: [number, number][] = [];
  for (let j = 1; j >= -1; j--) for (let i = -1; i <= 1; i++) tiles.push([i, j]);
  return (
    <g>
      <defs>
        {tiles.map(([i, j]) => (
          <clipPath key={`${i},${j}`} id={`${uid}-t${i + 1}${j + 1}`}>
            <rect x={X0 + (i + 1) * T} y={X0 + (1 - j) * T} width={T} height={T} />
          </clipPath>
        ))}
      </defs>
      {tiles.map(([i, j]) => {
        const mirrored = tileMirrored(id, i);
        // square coordinates → position in the tiled plane → screen (tile (0, 0) is the centre one)
        const toScreen = (p: V2): V2 => {
          const [x, y] = toTile(id, i, j, p);
          return [X0 + (x + 1) * T, X0 + (2 - y) * T];
        };
        const centre = i === 0 && j === 0;
        return (
          <g key={`${i},${j}`}>
            <rect x={X0 + (i + 1) * T} y={X0 + (1 - j) * T} width={T} height={T} fill="var(--card)" opacity={centre ? 1 : 0.75} />
            <g clipPath={`url(#${uid}-t${i + 1}${j + 1})`} opacity={centre ? 1 : 0.7}>
              <Layer def={SURFACES[id]} sim={sim} toScreen={toScreen} lin={[T, 0, 0, mirrored ? T : -T]} size={0.13} />
            </g>
            <rect x={X0 + (i + 1) * T} y={X0 + (1 - j) * T} width={T} height={T} fill="none" stroke={centre ? "var(--gold)" : "var(--line-2)"} strokeWidth={centre ? 2.5 : 1} />
            {mirrored && (
              <text x={X0 + (i + 1) * T + T - 6} y={X0 + (1 - j) * T + 14} textAnchor="end" fontSize="10" fill="var(--muted)">
                ↕
              </text>
            )}
          </g>
        );
      })}
    </g>
  );
}
