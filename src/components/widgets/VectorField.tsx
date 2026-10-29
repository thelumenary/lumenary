"use client";

import { Pencil, Plus, Trash2 } from "lucide-react";
import { useMemo, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { compileExpr, prettyExpr, stripLhs, toNumber, toRange, type CompileResult } from "./lib/expr";
import { clamp, fmt, type Pt, type Range } from "./lib/plot-core";
import { Plot, PlotHandle, arrowPath, type PlotView } from "./lib/plot-svg";
import { ExprErrorNote, ExprField, LegendSwatch, ModeTabs, NumberField, Readout, Slider, seriesColor } from "./lib/plot-ui";
import {
  FIELD_PRESETS,
  PHASE_PRESETS,
  SLOPE_PRESETS,
  arrowMarks,
  classify,
  curlDiv,
  diskIntegrals,
  fieldIndex,
  findEquilibria,
  jacobian,
  linearFit,
  loopIntegrals,
  orbit,
  presetMode,
  resolvePreset,
  slopeSolution,
  type Classification,
  type CurveResult,
  type Field2,
  type Mat2,
} from "./lib/plot-field";

type Mode = "slope" | "phase" | "field";
const MODES: readonly Mode[] = ["slope", "phase", "field"];
const VARS = ["x", "y"];
const MAX_CURVES = 10;

interface VectorFieldProps {
  mode?: string;
  modes?: unknown;
  f?: unknown;
  g?: unknown;
  preset?: unknown;
  x?: unknown;
  y?: unknown;
  points?: unknown;
  title?: string;
  subtitle?: string;
}

/* ---------------------------------------------------------------------------
 * Prop handling
 * ------------------------------------------------------------------------- */

const exprProp = (v: unknown): string | null => (typeof v === "string" ? v : typeof v === "number" && Number.isFinite(v) ? String(v) : null);

/** Read initial points [[x0, y0], …] (numbers or constant expressions). */
export function parseStartPoints(v: unknown, max = MAX_CURVES): Pt[] {
  if (!Array.isArray(v)) return [];
  const out: Pt[] = [];
  for (const p of v) {
    if (!Array.isArray(p) || p.length < 2) continue;
    const x = toNumber(p[0], NaN);
    const y = toNumber(p[1], NaN);
    if (Number.isFinite(x) && Number.isFinite(y) && Math.abs(x) < 1e6 && Math.abs(y) < 1e6) out.push([x, y]);
    if (out.length >= max) break;
  }
  return out;
}

/** The mode a VectorField starts in and the tabs it offers (exported for tests). */
export function resolveModes(props: Pick<VectorFieldProps, "mode" | "modes" | "preset" | "g">): { offered: Mode[]; initial: Mode } {
  const modeProp = MODES.includes(props.mode as Mode) ? (props.mode as Mode) : null;
  const inferred: Mode | null = modeProp ?? presetMode(props.preset) ?? (props.g !== undefined ? "phase" : null);
  let offered: Mode[];
  if (Array.isArray(props.modes)) {
    offered = MODES.filter((m) => (props.modes as unknown[]).includes(m));
    if (offered.length === 0) offered = modeProp ? [modeProp] : [...MODES];
  } else offered = modeProp ? [modeProp] : [...MODES];
  const initial = inferred && offered.includes(inferred) ? inferred : offered[0];
  return { offered, initial };
}

interface Init {
  preset: string | null;
  f: string;
  g: string;
  x: Range;
  y: Range;
  points: Pt[];
  loop: [number, number, number];
}

function initFor(mode: Mode, props: VectorFieldProps, useProps: boolean): Init {
  const pid = useProps ? resolvePreset(props.preset) : null;
  const f = useProps ? exprProp(props.f) : null;
  const g = useProps ? exprProp(props.g) : null;
  const custom = f !== null || g !== null;
  if (mode === "slope") {
    const id = pid && pid in SLOPE_PRESETS ? pid : custom ? null : "linear";
    const p = SLOPE_PRESETS[id ?? "linear"];
    const x = useProps ? toRange(props.x, id ? p.x : [-4, 4]) : p.x;
    const y = useProps ? toRange(props.y, id ? p.y : [-4, 4]) : p.y;
    const pts = useProps && Array.isArray(props.points) ? parseStartPoints(props.points) : id && !custom ? p.points : [];
    return { preset: custom ? null : id, f: f ?? p.f, g: "", x, y, points: pts, loop: [0, 0, 1] };
  }
  if (mode === "phase") {
    const id = pid && pid in PHASE_PRESETS ? pid : custom ? null : "spiralSink";
    const p = PHASE_PRESETS[id ?? "spiralSink"];
    const x = useProps ? toRange(props.x, id ? p.x : [-4, 4]) : p.x;
    const y = useProps ? toRange(props.y, id ? p.y : [-4, 4]) : p.y;
    const pts = useProps && Array.isArray(props.points) ? parseStartPoints(props.points) : id && !custom ? p.points : [];
    return { preset: custom ? null : id, f: custom ? (f ?? "0") : p.f, g: custom ? (g ?? "0") : p.g, x, y, points: pts, loop: [0, 0, 1] };
  }
  const id = pid && pid in FIELD_PRESETS ? pid : custom ? null : "rotation";
  const p = FIELD_PRESETS[id ?? "rotation"];
  const x = useProps ? toRange(props.x, id ? p.x : [-4, 4]) : p.x;
  const y = useProps ? toRange(props.y, id ? p.y : [-4, 4]) : p.y;
  const span = Math.min(x[1] - x[0], y[1] - y[0]);
  const loop: [number, number, number] = id ? p.loop : [(x[0] + x[1]) / 2 + span * 0.06, (y[0] + y[1]) / 2 + span * 0.04, span / 5];
  return { preset: custom ? null : id, f: custom ? (f ?? "0") : p.f, g: custom ? (g ?? "0") : p.g, x, y, points: [], loop };
}

const compile = (src: string): CompileResult => compileExpr(stripLhs(src), VARS);

function makeField(fr: CompileResult, gr: CompileResult): Field2 | null {
  if (!fr.ok || !gr.ok) return null;
  const f = fr.fn;
  const g = gr.fn;
  return (x, y) => {
    const v = { x, y };
    return [f(v), g(v)];
  };
}

/* ---------------------------------------------------------------------------
 * Widget
 * ------------------------------------------------------------------------- */

/**
 * Slope fields, phase portraits and loops in a vector field: RK4 solution
 * curves from clicked points, equilibria and their classification,
 * circulation and flux with Green's theorem, and the index of a field.
 */
export function VectorField(props: VectorFieldProps) {
  const { t } = useI18n();
  const { offered, initial } = resolveModes(props);
  const [mode, setMode] = useState<Mode>(initial);
  const inits = useMemo(
    () => Object.fromEntries(offered.map((m) => [m, initFor(m, props, m === initial)])) as Record<Mode, Init>,
    [offered.join(","), initial], // eslint-disable-line react-hooks/exhaustive-deps
  );
  const active = offered.includes(mode) ? mode : initial;
  return (
    <WidgetFrame title={props.title ?? t(`w.field.title.${active}`)} subtitle={props.subtitle ?? t(`w.field.subtitle.${active}`)}>
      {offered.length > 1 && (
        <div className="mb-4">
          <ModeTabs value={active} options={offered} onChange={setMode} label={t("w.field.modes.label")} render={(m) => t(`w.field.modes.${m}`)} />
        </div>
      )}
      {offered.map((m) => (
        <div key={m} hidden={m !== active}>
          {m === "slope" ? <SlopePanel init={inits[m]} /> : m === "phase" ? <PhasePanel init={inits[m]} /> : <FieldPanel init={inits[m]} />}
        </div>
      ))}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------------------
 * Shared pieces
 * ------------------------------------------------------------------------- */

function PresetBar({ ids, active, onPick }: { ids: string[]; active: string | null; onPick: (id: string) => void }) {
  const { t } = useI18n();
  return (
    <div role="group" aria-label={t("w.field.examples")} className="flex flex-wrap items-center gap-1.5">
      <span className="me-1 text-xs font-semibold uppercase tracking-wide text-muted">{t("w.field.examples")}</span>
      {ids.map((id) => (
        <button key={id} type="button" aria-pressed={active === id} className={`btn btn-sm ${active === id ? "btn-primary" : "btn-ghost"}`} onClick={() => onPick(id)}>
          {t(`w.field.preset.${id}`)}
        </button>
      ))}
    </div>
  );
}

/** Equation line, with an edit toggle revealing expression fields. */
function Equations({ display, fields, errors }: { display: ReactNode; fields: ReactNode; errors: ReactNode }) {
  const { t } = useI18n();
  const [editing, setEditing] = useState(false);
  return (
    <div className="mt-3">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <p className="ltr min-w-0 font-serif text-lg text-ink" dir="ltr">
          {display}
        </p>
        <button type="button" className="btn btn-sm btn-ghost" aria-expanded={editing} onClick={() => setEditing((e) => !e)}>
          <Pencil size={14} aria-hidden="true" /> {editing ? t("w.field.doneEditing") : t("w.field.edit")}
        </button>
      </div>
      {editing ? (
        <div className="mt-2 grid gap-3 sm:grid-cols-2">
          {fields}
          <p className="text-xs text-muted sm:col-span-2">{t("w.plot.syntax", { vars: "x, y" })}</p>
        </div>
      ) : (
        errors
      )}
    </div>
  );
}

/** A grid of arrows with normalised length; darkness and length grow with the magnitude. */
function ArrowGrid({ view, F }: { view: PlotView; F: Field2 | null }) {
  const { W, H, x, y, sx, sy } = view;
  const buckets = useMemo(() => {
    const out = Array.from({ length: 5 }, () => ({ line: "", head: "" }));
    let dots = "";
    if (!F) return { out, dots };
    const n = clamp(Math.round(W / 42), 9, 20);
    const cellX = W / n;
    const m = Math.max(4, Math.round(H / cellX));
    const cellY = H / m;
    const cell = Math.min(cellX, cellY);
    const kx = W / (x[1] - x[0]);
    const ky = H / (y[1] - y[0]);
    const samples: { px: number; py: number; vx: number; vy: number; mag: number }[] = [];
    for (let i = 0; i < n; i++)
      for (let j = 0; j < m; j++) {
        const px = (i + 0.5) * cellX;
        const py = (j + 0.5) * cellY;
        const v = F(sx.invert(px), sy.invert(py));
        if (!Number.isFinite(v[0]) || !Number.isFinite(v[1])) continue;
        samples.push({ px, py, vx: v[0] * kx, vy: -v[1] * ky, mag: Math.hypot(v[0], v[1]) });
      }
    const mags = samples.map((s) => s.mag).sort((a, b) => a - b);
    const ref = mags.length ? mags[Math.floor(0.9 * (mags.length - 1))] || mags[mags.length - 1] : 0;
    for (const s of samples) {
      const pl = Math.hypot(s.vx, s.vy);
      if (!(pl > 0) || !(ref > 0)) {
        dots += `M${s.px.toFixed(1)} ${s.py.toFixed(1)}h0.01`;
        continue;
      }
      const r = Math.min(1, s.mag / ref);
      const q = Math.sqrt(r);
      const len = cell * 0.78 * (0.42 + 0.58 * q);
      const ux = s.vx / pl;
      const uy = s.vy / pl;
      const a = arrowPath(s.px - (ux * len) / 2, s.py - (uy * len) / 2, s.px + (ux * len) / 2, s.py + (uy * len) / 2, Math.min(7, len * 0.42));
      const b = out[Math.min(4, Math.floor(q * 5))];
      b.line += a.line;
      b.head += a.head;
    }
    return { out, dots };
  }, [F, W, H, x[0], x[1], y[0], y[1]]); // eslint-disable-line react-hooks/exhaustive-deps
  const OP = [0.22, 0.36, 0.52, 0.7, 0.88];
  return (
    <g aria-hidden="true">
      {buckets.out.map((b, i) => (
        <g key={i} opacity={OP[i]}>
          <path d={b.line} stroke="var(--ink-2)" strokeWidth={1.4} strokeLinecap="round" fill="none" />
          <path d={b.head} fill="var(--ink-2)" />
        </g>
      ))}
      {buckets.dots && <path d={buckets.dots} stroke="var(--ink-2)" strokeWidth={3} strokeLinecap="round" opacity={0.6} />}
    </g>
  );
}

function SpeedLegend() {
  const { t } = useI18n();
  return (
    <span className="inline-flex items-center gap-2 text-xs text-muted">
      <svg width="56" height="14" viewBox="0 0 56 14" aria-hidden="true">
        {[0.25, 0.55, 0.88].map((o, i) => {
          const len = 10 + i * 3;
          const x0 = 4 + i * 18;
          const a = arrowPath(x0, 7, x0 + len, 7, 5);
          return (
            <g key={i} opacity={o}>
              <path d={a.line} stroke="var(--ink-2)" strokeWidth={1.4} />
              <path d={a.head} fill="var(--ink-2)" />
            </g>
          );
        })}
      </svg>
      {t("w.field.legend.speed")}
    </span>
  );
}

interface Traj {
  start: Pt;
  forward: CurveResult;
  backward: CurveResult;
}

/** Curves through the start points, drawn with optional direction arrowheads and a faint backward half. */
function CurveLayer({ view, curves, arrows }: { view: PlotView; curves: Traj[]; arrows: boolean }) {
  const { sx, sy } = view;
  const toPx = (pts: Pt[]) => pts.map((p) => [sx(p[0]), sy(p[1])] as Pt);
  const d = (pts: Pt[]) => {
    let s = "";
    pts.forEach((p, i) => {
      const X = sx(p[0]);
      const Y = sy(p[1]);
      if (Number.isFinite(X) && Number.isFinite(Y)) s += `${i === 0 ? "M" : "L"}${X.toFixed(2)} ${Y.toFixed(2)}`;
    });
    return s;
  };
  return (
    <g>
      {curves.map((c, i) => {
        const color = seriesColor(i);
        const heads = arrows
          ? arrowMarks(toPx(c.forward.points), 95, 45)
              .map((m) => {
                const L = 9;
                const w = 4.5;
                const cx = Math.cos(m.angle);
                const sn = Math.sin(m.angle);
                const tx = m.x + cx * L * 0.5;
                const ty = m.y + sn * L * 0.5;
                const bx = m.x - cx * L * 0.5;
                const by = m.y - sn * L * 0.5;
                return `M${tx.toFixed(1)} ${ty.toFixed(1)}L${(bx - sn * w).toFixed(1)} ${(by + cx * w).toFixed(1)}L${(bx + sn * w).toFixed(1)} ${(by - cx * w).toFixed(1)}Z`;
              })
              .join("")
          : "";
        return (
          <g key={i}>
            {arrows ? (
              <>
                <path d={d(c.backward.points)} fill="none" stroke={color} strokeWidth={2} strokeDasharray="5 4" strokeOpacity={0.6} strokeLinecap="round" />
                <path d={d(c.forward.points)} fill="none" stroke={color} strokeWidth={2.5} strokeLinejoin="round" strokeLinecap="round" />
                <path d={heads} fill={color} />
              </>
            ) : (
              <path d={d([...c.backward.points].reverse().concat(c.forward.points.slice(1)))} fill="none" stroke={color} strokeWidth={2.5} strokeLinejoin="round" strokeLinecap="round" />
            )}
            <circle cx={sx(c.start[0])} cy={sy(c.start[1])} r={4.5} fill={color} stroke="var(--card)" strokeWidth={2} />
          </g>
        );
      })}
    </g>
  );
}

/** Start-point entry for keyboard users, plus clear. */
function StartControls({ win, onAdd, onClear, count, addLabel }: { win: { x: Range; y: Range }; onAdd: (p: Pt) => void; onClear: () => void; count: number; addLabel: string }) {
  const { t } = useI18n();
  const [x0, setX0] = useState(Number(((win.x[0] + win.x[1]) / 2 + (win.x[1] - win.x[0]) * 0.2).toFixed(2)));
  const [y0, setY0] = useState(Number(((win.y[0] + win.y[1]) / 2 + (win.y[1] - win.y[0]) * 0.15).toFixed(2)));
  return (
    <div className="flex flex-wrap items-center gap-x-3 gap-y-2">
      <span className="text-sm font-semibold text-ink-2">{t("w.field.start")}</span>
      <NumberField label={<i className="font-serif">x₀</i>} value={x0} onChange={setX0} inputClassName="w-20" />
      <NumberField label={<i className="font-serif">y₀</i>} value={y0} onChange={setY0} inputClassName="w-20" />
      <button type="button" className="btn btn-sm btn-primary" onClick={() => onAdd([x0, y0])}>
        <Plus size={14} aria-hidden="true" /> {addLabel}
      </button>
      <button type="button" className="btn btn-sm btn-ghost" onClick={onClear} disabled={count === 0}>
        <Trash2 size={14} aria-hidden="true" /> {t("w.field.clear")}
      </button>
    </div>
  );
}

function useStartPoints(initial: Pt[]) {
  const [points, setPoints] = useState<Pt[]>(initial);
  const add = (p: Pt) => setPoints((old) => [...old, p].slice(-MAX_CURVES));
  return { points, setPoints, add, clear: () => setPoints([]) };
}

const fmtPt = (p: Pt, d = 2) => `(${fmt(p[0], d)}, ${fmt(p[1], d)})`;

/* ---------------------------------------------------------------------------
 * Slope field
 * ------------------------------------------------------------------------- */

function SlopeSegments({ view, f }: { view: PlotView; f: ((x: number, y: number) => number) | null }) {
  const { W, H, x, y, sx, sy } = view;
  const d = useMemo(() => {
    if (!f) return "";
    const n = clamp(Math.round(W / 32), 12, 24);
    const cellX = W / n;
    const m = Math.max(5, Math.round(H / cellX));
    const cellY = H / m;
    const half = Math.min(cellX, cellY) * 0.36;
    const kx = W / (x[1] - x[0]);
    const ky = H / (y[1] - y[0]);
    let s = "";
    for (let i = 0; i < n; i++)
      for (let j = 0; j < m; j++) {
        const px = (i + 0.5) * cellX;
        const py = (j + 0.5) * cellY;
        const k = f(sx.invert(px), sy.invert(py));
        let ux: number;
        let uy: number;
        if (Number.isFinite(k)) {
          const vx = kx;
          const vy = -k * ky;
          const l = Math.hypot(vx, vy);
          ux = vx / l;
          uy = vy / l;
        } else if (k === Infinity || k === -Infinity) {
          ux = 0;
          uy = 1;
        } else continue;
        s += `M${(px - ux * half).toFixed(1)} ${(py - uy * half).toFixed(1)}L${(px + ux * half).toFixed(1)} ${(py + uy * half).toFixed(1)}`;
      }
    return s;
  }, [f, W, H, x[0], x[1], y[0], y[1]]); // eslint-disable-line react-hooks/exhaustive-deps
  return <path d={d} stroke="var(--ink-2)" strokeOpacity={0.55} strokeWidth={1.5} strokeLinecap="round" fill="none" aria-hidden="true" />;
}

/** Generous integration box: the plot may show more than the requested window (equal aspect). */
const integrationBox = (win: { x: Range; y: Range }) => {
  const w = win.x[1] - win.x[0];
  const h = win.y[1] - win.y[0];
  const s = Math.max(w, h);
  const cx = (win.x[0] + win.x[1]) / 2;
  const cy = (win.y[0] + win.y[1]) / 2;
  return { x: [cx - s, cx + s] as Range, y: [cy - s, cy + s] as Range };
};
const stepFor = (win: { x: Range; y: Range }) => Math.hypot(win.x[1] - win.x[0], win.y[1] - win.y[0]) / 500;

function SlopePanel({ init }: { init: Init }) {
  const { t, n } = useI18n();
  const [src, setSrc] = useState(init.f);
  const [preset, setPreset] = useState<string | null>(init.preset);
  const [win, setWin] = useState({ x: init.x, y: init.y });
  const { points, setPoints, add, clear } = useStartPoints(init.points);
  const [hover, setHover] = useState<Pt | null>(null);
  const res = useMemo(() => compile(src), [src]);
  const f = useMemo(() => (res.ok ? (x: number, y: number) => res.fn({ x, y }) : null), [res]);
  const curves = useMemo<Traj[]>(() => {
    if (!f) return [];
    const box = integrationBox(win);
    const ds = stepFor(win);
    return points.map((p) => ({ start: p, forward: slopeSolution(f, p, box, { dir: 1, ds }), backward: slopeSolution(f, p, box, { dir: -1, ds }) }));
  }, [f, points, win]);
  const pick = (id: string) => {
    const p = SLOPE_PRESETS[id];
    setPreset(id);
    setSrc(p.f);
    setWin({ x: p.x, y: p.y });
    setPoints(p.points);
  };
  const last = curves[curves.length - 1];
  const ends = last ? [last.backward.reason, last.forward.reason] : [];
  const pretty = prettyExpr(stripLhs(src));
  const hoverSlope = hover && f ? f(hover[0], hover[1]) : NaN;
  return (
    <div>
      <PresetBar ids={Object.keys(SLOPE_PRESETS)} active={preset} onPick={pick} />
      <Equations
        display={
          <>
            <i>dy</i>/<i>dx</i> = {pretty}
          </>
        }
        fields={
          <ExprField
            label={t("w.field.label.slope")}
            prefix="dy/dx ="
            value={src}
            onChange={(v) => {
              setSrc(v);
              setPreset(null);
            }}
            result={res}
            className="sm:col-span-2"
          />
        }
        errors={!res.ok ? <ExprErrorNote error={res.error} source={res.source} /> : null}
      />
      <div className="mt-3">
        <Plot
          x={win.x}
          y={win.y}
          aspect="equal"
          xLabel="x"
          yLabel="y"
          ariaLabel={t("w.field.aria.slope", { f: pretty, count: curves.length })}
          onHover={setHover}
          onPress={(p) => add(p)}
          readout={hover ? <span>{`${fmtPt(hover)} · dy/dx = ${fmt(hoverSlope, 3)}`}</span> : null}
        >
          {(view) => (
            <>
              <SlopeSegments view={view} f={f} />
              <CurveLayer view={view} curves={curves} arrows={false} />
            </>
          )}
        </Plot>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.field.hint.slope")}</p>
      <div className="mt-3">
        <StartControls win={win} onAdd={add} onClear={clear} count={points.length} addLabel={t("w.field.draw.slope")} />
      </div>
      <Readout className="mt-3 text-sm">
        <p>
          {t("w.field.curves", { count: n(curves.length) })} <span className="text-ink-2">{t("w.field.rk4")}</span>
        </p>
        {last && (
          <p className="mt-1 text-ink-2">
            {t("w.field.lastThrough")}{" "}
            <span className="ltr font-mono text-ink" dir="ltr">
              {fmtPt(last.start)}
            </span>
            .{ends.includes("vertical") && <> {t("w.field.end.vertical")}</>}
            {ends.includes("blowup") && <> {t("w.field.end.blowup")}</>}
            {ends.includes("undefined") && <> {t("w.field.end.undefined")}</>}
          </p>
        )}
      </Readout>
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Phase portrait
 * ------------------------------------------------------------------------- */

interface EquilibriumInfo {
  p: Pt;
  c: Classification;
  A: Mat2;
}

/** Equilibria and classification: exact for linear systems, by linearisation otherwise. */
export function analyseSystem(F: Field2, win: { x: Range; y: Range }): { linear: boolean; A?: Mat2; eq: EquilibriumInfo[] } {
  const scale = Math.max(Math.abs(win.x[0]), Math.abs(win.x[1]), Math.abs(win.y[0]), Math.abs(win.y[1]), 1);
  const lin = linearFit(F, scale);
  if (lin) {
    const { A, b } = lin;
    const c = classify(A);
    const det = A[0][0] * A[1][1] - A[0][1] * A[1][0];
    if (c.kind === "degenerate" || det === 0) return { linear: true, A, eq: [{ p: [NaN, NaN], c, A }] };
    const p: Pt = [-(A[1][1] * b[0] - A[0][1] * b[1]) / det, -(-A[1][0] * b[0] + A[0][0] * b[1]) / det];
    return { linear: true, A, eq: [{ p: [p[0] + 0, p[1] + 0], c, A }] };
  }
  const eqs = findEquilibria(F, win, 7, 6);
  return {
    linear: false,
    eq: eqs.map((p) => {
      const A = jacobian(F, p, 1e-5 * scale);
      return { p, A, c: classify(A, 1e-6) };
    }),
  };
}

const fmtMat = (A: Mat2) => [A[0].map((v) => fmt(v, 3)), A[1].map((v) => fmt(v, 3))];

function MatrixView({ A }: { A: Mat2 }) {
  const m = fmtMat(A);
  return (
    <span className="ltr inline-flex items-center gap-1 align-middle font-serif" dir="ltr">
      <span className="text-2xl font-light leading-none text-muted">[</span>
      <span className="grid grid-cols-2 gap-x-3 text-center text-sm leading-tight">
        <span>{m[0][0]}</span>
        <span>{m[0][1]}</span>
        <span>{m[1][0]}</span>
        <span>{m[1][1]}</span>
      </span>
      <span className="text-2xl font-light leading-none text-muted">]</span>
    </span>
  );
}

const eigText = (c: Classification) =>
  c.eig.im > 0 ? `λ = ${fmt(c.eig.re[0], 3)} ± ${fmt(c.eig.im, 3)}i` : c.eig.re[0] === c.eig.re[1] ? `λ = ${fmt(c.eig.re[0], 3)} (×2)` : `λ = ${fmt(c.eig.re[0], 3)}, ${fmt(c.eig.re[1], 3)}`;

/** The trace–determinant plane with the parabola D = T²/4 and the classified points. */
function TDPlane({ items }: { items: Classification[] }) {
  const { t } = useI18n();
  const W = 220;
  const H = 150;
  const Tm = Math.max(2.5, ...items.map((c) => Math.abs(c.trace) * 1.35));
  const Dm = Math.max((Tm * Tm) / 4, ...items.map((c) => Math.abs(c.det) * 1.35), 1.5);
  const X = (v: number) => W / 2 + (v / Tm) * (W / 2 - 8);
  const Y = (v: number) => H * 0.62 - (v / Dm) * (H * 0.62 - 8);
  // Equilibria with the same trace and determinant share one dot ("1, 3, 5").
  const groups: { trace: number; det: number; labels: number[] }[] = [];
  items.forEach((c, i) => {
    const g = groups.find((q) => Math.abs(q.trace - c.trace) < 1e-6 && Math.abs(q.det - c.det) < 1e-6);
    if (g) g.labels.push(i + 1);
    else groups.push({ trace: c.trace, det: c.det, labels: [i + 1] });
  });
  let para = "";
  for (let i = 0; i <= 60; i++) {
    const T = -Tm + (2 * Tm * i) / 60;
    para += `${i === 0 ? "M" : "L"}${X(T).toFixed(1)} ${Y((T * T) / 4).toFixed(1)}`;
  }
  return (
    <figure className="flex shrink-0 flex-col gap-2 sm:flex-row sm:items-start md:flex-col">
      <svg viewBox={`0 0 ${W} ${H}`} className="w-[220px] max-w-full" role="img" aria-label={t("w.field.td.aria")} style={{ direction: "ltr" }}>
        <rect x={0.5} y={0.5} width={W - 1} height={H - 1} rx={8} fill="var(--paper)" stroke="var(--line)" />
        <rect x={0} y={Y(0)} width={W} height={H - Y(0)} fill="var(--human)" fillOpacity={0.07} />
        <line x1={0} x2={W} y1={Y(0)} y2={Y(0)} stroke="var(--ink-2)" strokeOpacity={0.6} />
        <line x1={X(0)} x2={X(0)} y1={0} y2={H} stroke="var(--ink-2)" strokeOpacity={0.6} />
        <line x1={X(0)} x2={X(0)} y1={Y(0)} y2={4} stroke="var(--formal)" strokeWidth={2.5} strokeOpacity={0.55} />
        <path d={para} fill="none" stroke="var(--compute)" strokeWidth={1.5} strokeDasharray="4 3" />
        <text x={W - 8} y={Y(0) + 14} textAnchor="end" fontSize={12} fontStyle="italic" fill="var(--ink-2)" className="font-serif">
          T
        </text>
        <text x={X(0) + 5} y={13} fontSize={12} fontStyle="italic" fill="var(--ink-2)" className="font-serif">
          D
        </text>
        <text x={X(Tm * 0.5) + 7} y={Y((Tm * Tm) / 16) + 4} fontSize={9.5} fill="var(--compute)" className="font-serif">
          D = T²/4
        </text>
        {groups.map((gr, i) => {
          const cx = clamp(X(gr.trace), 6, W - 6);
          const cy = clamp(Y(gr.det), 6, H - 6);
          return (
            <g key={i}>
              <circle cx={cx} cy={cy} r={5.5} fill="var(--gold)" stroke="var(--card)" strokeWidth={2} />
              {items.length > 1 && (
                <text x={cx + 8} y={cy + 4} fontSize={10} fontWeight={700} fill="var(--gold-ink)" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                  {gr.labels.join(", ")}
                </text>
              )}
            </g>
          );
        })}
      </svg>
      <figcaption className="text-xs leading-snug text-muted sm:max-w-[30rem] md:max-w-[220px]">{t("w.field.td.caption")}</figcaption>
    </figure>
  );
}

function PhasePanel({ init }: { init: Init }) {
  const { t, n } = useI18n();
  const [fs, setFs] = useState(init.f);
  const [gs, setGs] = useState(init.g);
  const [preset, setPreset] = useState<string | null>(init.preset);
  const [win, setWin] = useState({ x: init.x, y: init.y });
  const { points, setPoints, add, clear } = useStartPoints(init.points);
  const [hover, setHover] = useState<Pt | null>(null);
  const fr = useMemo(() => compile(fs), [fs]);
  const gr = useMemo(() => compile(gs), [gs]);
  const F = useMemo(() => makeField(fr, gr), [fr, gr]);
  const curves = useMemo<Traj[]>(() => {
    if (!F) return [];
    const box = integrationBox(win);
    const ds = stepFor(win);
    return points.map((p) => {
      const forward = orbit(F, p, box, { dir: 1, ds });
      const backward: CurveResult = forward.reason === "closed" ? { points: [p], reason: "closed" } : orbit(F, p, box, { dir: -1, ds });
      return { start: p, forward, backward };
    });
  }, [F, points, win]);
  const analysis = useMemo(() => (F ? analyseSystem(F, win) : null), [F, win]);
  const pick = (id: string) => {
    const p = PHASE_PRESETS[id];
    setPreset(id);
    setFs(p.f);
    setGs(p.g);
    setWin({ x: p.x, y: p.y });
    setPoints(p.points);
  };
  const pf = prettyExpr(stripLhs(fs));
  const pg = prettyExpr(stripLhs(gs));
  const hv = hover && F ? F(hover[0], hover[1]) : null;
  const last = curves[curves.length - 1];
  return (
    <div>
      <PresetBar ids={Object.keys(PHASE_PRESETS)} active={preset} onPick={pick} />
      <Equations
        display={
          <>
            <i>x</i>′ = {pf}, <span className="ms-2" />
            <i>y</i>′ = {pg}
          </>
        }
        fields={
          <>
            <ExprField label={t("w.field.label.phaseX")} prefix="x′ =" value={fs} onChange={(v) => (setFs(v), setPreset(null))} result={fr} />
            <ExprField label={t("w.field.label.phaseY")} prefix="y′ =" value={gs} onChange={(v) => (setGs(v), setPreset(null))} result={gr} />
          </>
        }
        errors={
          <>
            {!fr.ok && <ExprErrorNote error={fr.error} source={fr.source} />}
            {!gr.ok && <ExprErrorNote error={gr.error} source={gr.source} />}
          </>
        }
      />
      <div className="mt-3">
        <Plot
          x={win.x}
          y={win.y}
          aspect="equal"
          xLabel="x"
          yLabel="y"
          ariaLabel={t("w.field.aria.phase", { f: pf, g: pg, count: curves.length })}
          onHover={setHover}
          onPress={(p) => add(p)}
          readout={hover && hv ? <span>{`${fmtPt(hover)} → (x′, y′) = ${fmtPt(hv)}`}</span> : null}
        >
          {(view) => (
            <>
              <ArrowGrid view={view} F={F} />
              <CurveLayer view={view} curves={curves} arrows />
              {analysis?.eq.map((e, i) =>
                Number.isFinite(e.p[0]) ? (
                  <g key={i} aria-hidden="true">
                    <circle cx={view.sx(e.p[0])} cy={view.sy(e.p[1])} r={5} fill={e.c.kind.endsWith("Sink") || e.c.kind === "center" ? "var(--card)" : "var(--ink)"} stroke="var(--ink)" strokeWidth={2} />
                    {analysis.eq.length > 1 && (
                      <text x={view.sx(e.p[0]) + 7} y={view.sy(e.p[1]) - 7} fontSize={11} fontWeight={700} fill="var(--gold-ink)" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                        {i + 1}
                      </text>
                    )}
                  </g>
                ) : null,
              )}
            </>
          )}
        </Plot>
      </div>
      <div className="mt-2 flex flex-wrap items-center gap-x-4 gap-y-1">
        <SpeedLegend />
        <span className="inline-flex items-center gap-1.5 text-xs text-muted">
          <LegendSwatch color="var(--ink-2)" /> {t("w.field.legend.forward")}
        </span>
        <span className="inline-flex items-center gap-1.5 text-xs text-muted">
          <LegendSwatch color="var(--ink-2)" dash="5 4" width={2} /> {t("w.field.legend.backward")}
        </span>
        <span className="inline-flex items-center gap-1.5 text-xs text-muted">
          <svg width="12" height="12" aria-hidden="true">
            <circle cx="6" cy="6" r="4" fill="var(--ink)" stroke="var(--ink)" strokeWidth="1.5" />
          </svg>
          {t("w.field.legend.equilibrium")}
        </span>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.field.hint.phase")}</p>
      <div className="mt-3">
        <StartControls win={win} onAdd={add} onClear={clear} count={points.length} addLabel={t("w.field.draw.phase")} />
      </div>

      <div className="mt-3 grid gap-4 md:grid-cols-[minmax(0,1fr)_auto]">
        <Readout className="text-sm">
          <p>
            {t("w.field.trajectories", { count: n(curves.length) })} <span className="text-ink-2">{t("w.field.rk4")}</span>
            {last?.forward.reason === "closed" && <> {t("w.field.end.closed")}</>}
            {last?.forward.reason === "cycle" && <> {t("w.field.end.cycle")}</>}
          </p>
          {analysis && analysis.linear && analysis.A && (
            <div className="mt-2 space-y-1.5">
              <p className="flex flex-wrap items-center gap-x-3 gap-y-1">
                <span className="font-semibold text-ink">{t("w.field.linear")}</span>
                <span className="ltr font-serif" dir="ltr">
                  <i>A</i> = <MatrixView A={analysis.A} />
                </span>
              </p>
              <p className="ltr font-serif text-ink-2" dir="ltr">
                T = {fmt(analysis.eq[0].c.trace, 3)}, D = {fmt(analysis.eq[0].c.det, 3)}, T² − 4D = {fmt(analysis.eq[0].c.disc, 3)}; {eigText(analysis.eq[0].c)}
              </p>
              <p>
                {Number.isFinite(analysis.eq[0].p[0]) ? (
                  <>
                    {t("w.field.equilibriumAt")}{" "}
                    <span className="ltr font-mono" dir="ltr">
                      {fmtPt(analysis.eq[0].p, 3)}
                    </span>
                    : <strong>{t(`w.field.kind.${analysis.eq[0].c.kind}`)}</strong>
                  </>
                ) : (
                  <strong>{t("w.field.kind.degenerate")}</strong>
                )}
              </p>
            </div>
          )}
          {analysis && !analysis.linear && (
            <div className="mt-2 space-y-1">
              <p className="font-semibold text-ink">{t("w.field.nonlinear")}</p>
              {analysis.eq.length === 0 && <p className="text-ink-2">{t("w.field.noEquilibria")}</p>}
              <ol className="space-y-0.5">
                {analysis.eq.map((e, i) => (
                  <li key={i}>
                    <span className="font-bold text-gold-ink">{i + 1}.</span>{" "}
                    <span className="ltr font-mono" dir="ltr">
                      {fmtPt(e.p, 3)}
                    </span>
                    : {t(`w.field.kind.${e.c.kind}`)} <span className="ltr font-serif text-ink-2" dir="ltr">({eigText(e.c)})</span>
                  </li>
                ))}
              </ol>
              {analysis.eq.some((e) => e.c.kind === "center") && <p className="text-ink-2">{t("w.field.centerCaveat")}</p>}
            </div>
          )}
        </Readout>
        {analysis && analysis.eq.length > 0 && <TDPlane items={analysis.eq.map((e) => e.c)} />}
      </div>
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Loop in a field: circulation, flux, index
 * ------------------------------------------------------------------------- */

function Compass({ theta, phi, label }: { theta: number; phi: number; label: string }) {
  const C = 56;
  const R = 44;
  const wx = C + R * Math.cos(theta);
  const wy = C - R * Math.sin(theta);
  const ok = Number.isFinite(phi);
  const a = ok ? arrowPath(C - 22 * Math.cos(phi), C + 22 * Math.sin(phi), C + 30 * Math.cos(phi), C - 30 * Math.sin(phi), 10) : null;
  return (
    <svg viewBox="0 0 112 112" className="h-28 w-28 shrink-0" role="img" aria-label={label} style={{ direction: "ltr" }}>
      <circle cx={C} cy={C} r={R} fill="var(--gold-soft)" fillOpacity={0.5} stroke="var(--gold-ink)" strokeOpacity={0.6} strokeWidth={1.5} />
      {[0, 1, 2, 3].map((k) => (
        <line key={k} x1={C + (R - 5) * Math.cos((k * Math.PI) / 2)} y1={C - (R - 5) * Math.sin((k * Math.PI) / 2)} x2={C + R * Math.cos((k * Math.PI) / 2)} y2={C - R * Math.sin((k * Math.PI) / 2)} stroke="var(--gold-ink)" strokeOpacity={0.6} />
      ))}
      {a && (
        <>
          <path d={a.line} stroke="var(--formal)" strokeWidth={3.5} strokeLinecap="round" />
          <path d={a.head} fill="var(--formal)" />
        </>
      )}
      <circle cx={C} cy={C} r={3} fill="var(--ink)" />
      <circle cx={wx} cy={wy} r={5} fill="var(--gold)" stroke="var(--card)" strokeWidth={2} />
    </svg>
  );
}

function FieldPanel({ init }: { init: Init }) {
  const { t } = useI18n();
  const [fs, setFs] = useState(init.f);
  const [gs, setGs] = useState(init.g);
  const [preset, setPreset] = useState<string | null>(init.preset);
  const [win, setWin] = useState({ x: init.x, y: init.y });
  const [centre, setCentre] = useState<Pt>([init.loop[0], init.loop[1]]);
  const [radius, setRadius] = useState(init.loop[2]);
  const [walk, setWalk] = useState(0.125);
  const [hover, setHover] = useState<Pt | null>(null);
  const fr = useMemo(() => compile(fs), [fs]);
  const gr = useMemo(() => compile(gs), [gs]);
  const F = useMemo(() => makeField(fr, gr), [fr, gr]);
  const span = Math.min(win.x[1] - win.x[0], win.y[1] - win.y[0]);
  const rMin = Number((span / 40).toPrecision(2));
  const rMax = Number((span / 2.5).toPrecision(2));
  const rStep = Number((span / 400).toPrecision(1));
  const r = clamp(radius, rMin, rMax);

  const stats = useMemo(() => {
    if (!F) return null;
    const line = loopIntegrals(F, centre, r);
    const idx = fieldIndex(F, centre, r);
    // Finite-difference values carry rounding noise of order 1e-9 × |F|: show it as 0.
    const noise = 1e-6 * (1 + (Number.isFinite(idx.maxMag) ? idx.maxMag : 0));
    const snap = (v: number, k = 1) => (Math.abs(v) < noise * k ? 0 : v);
    const d = diskIntegrals(F, centre, r);
    const l = curlDiv(F, centre, 1e-5 * Math.max(1, r));
    const area = Math.PI * r * r;
    return {
      line: { circulation: snap(line.circulation, r), flux: snap(line.flux, r) },
      disk: { curl: snap(d.curl, area), div: snap(d.div, area) },
      idx,
      local: { curl: snap(l.curl), div: snap(l.div) },
    };
  }, [F, centre, r]);

  const pick = (id: string) => {
    const p = FIELD_PRESETS[id];
    setPreset(id);
    setFs(p.f);
    setGs(p.g);
    setWin({ x: p.x, y: p.y });
    setCentre([p.loop[0], p.loop[1]]);
    setRadius(p.loop[2]);
  };

  const pf = prettyExpr(stripLhs(fs));
  const pg = prettyExpr(stripLhs(gs));
  const theta = walk * 2 * Math.PI;
  const wp: Pt = [centre[0] + r * Math.cos(theta), centre[1] + r * Math.sin(theta)];
  const wv = F ? F(wp[0], wp[1]) : ([NaN, NaN] as Pt);
  const phi = Number.isFinite(wv[0]) && Number.isFinite(wv[1]) && Math.hypot(wv[0], wv[1]) > 0 ? Math.atan2(wv[1], wv[0]) : NaN;
  const turning = stats?.idx.turning ?? [];
  const turnsSoFar = turning.length > 1 ? turning[Math.round(walk * (turning.length - 1))] / (2 * Math.PI) : NaN;

  const agree = (a: number, b: number) => Number.isFinite(a) && Number.isFinite(b) && Math.abs(a - b) <= 1e-4 * (1 + Math.abs(a) + Math.abs(b));
  const greenOk = stats ? agree(stats.line.circulation, stats.disk.curl) && agree(stats.line.flux, stats.disk.div) : false;
  const idx = stats?.idx;
  const hv = hover && F ? F(hover[0], hover[1]) : null;

  const indexText = !idx
    ? ""
    : idx.status === "undefined"
      ? t("w.field.index.undefinedF")
      : idx.status === "zero"
        ? t("w.field.index.zero")
        : `${idx.status === "near" ? `${t("w.field.index.near")} ` : ""}${idx.index !== 0 ? t(greenOk ? "w.field.index.nonzero" : "w.field.index.nonzeroSingular", { index: idx.index }) : t("w.field.index.none")}`;

  return (
    <div>
      <PresetBar ids={Object.keys(FIELD_PRESETS)} active={preset} onPick={pick} />
      <Equations
        display={
          <>
            <b>F</b>(<i>x</i>, <i>y</i>) = ({pf}, {pg})
          </>
        }
        fields={
          <>
            <ExprField label={t("w.field.label.fieldP")} prefix="P =" value={fs} onChange={(v) => (setFs(v), setPreset(null))} result={fr} />
            <ExprField label={t("w.field.label.fieldQ")} prefix="Q =" value={gs} onChange={(v) => (setGs(v), setPreset(null))} result={gr} />
          </>
        }
        errors={
          <>
            {!fr.ok && <ExprErrorNote error={fr.error} source={fr.source} />}
            {!gr.ok && <ExprErrorNote error={gr.error} source={gr.source} />}
          </>
        }
      />
      <div className="mt-3">
        <Plot
          x={win.x}
          y={win.y}
          aspect="equal"
          xLabel="x"
          yLabel="y"
          ariaLabel={t("w.field.aria.field", { f: pf, g: pg, r: fmt(r, 2), cx: fmt(centre[0], 2), cy: fmt(centre[1], 2), index: idx && (idx.status === "ok" || idx.status === "near") ? idx.index : "—" })}
          onHover={setHover}
          onPress={(p) => setCentre(p)}
          readout={hover && hv ? <span>{`${fmtPt(hover)} → F = ${fmtPt(hv)}`}</span> : null}
          above={(view) => (
            <PlotHandle
              x={centre[0]}
              y={centre[1]}
              onMove={setCentre}
              label={t("w.field.loopCentre")}
              color="var(--gold-ink)"
              r={6}
              step={Number((span / 80).toPrecision(1))}
              constrain={(p) => [clamp(p[0], view.x[0], view.x[1]), clamp(p[1], view.y[0], view.y[1])]}
            />
          )}
        >
          {(view) => <LoopLayer view={view} F={F} centre={centre} r={r} theta={theta} />}
        </Plot>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.field.hint.field")}</p>

      <div className="mt-3 grid gap-x-6 gap-y-3 sm:grid-cols-2">
        <Slider label={t("w.field.radius")} value={r} min={rMin} max={rMax} step={rStep} onChange={setRadius} display={`r = ${fmt(r, 2)}`} />
        <Slider label={t("w.field.walk")} value={walk} min={0} max={1} step={1 / 240} onChange={setWalk} display={`${Math.round(walk * 360)}°`} accent="var(--formal)" />
      </div>

      {stats && (
        <div className="mt-4 grid gap-4 sm:grid-cols-[auto_minmax(0,1fr)] sm:items-start">
          <div className="flex items-center gap-3 sm:flex-col sm:items-center">
            <Compass theta={theta} phi={phi} label={t("w.field.compassAria", { turns: Number.isFinite(turnsSoFar) ? fmt(turnsSoFar, 2) : "—" })} />
            <p className="text-center text-xs text-ink-2">
              {t("w.field.turnsSoFar")}{" "}
              <span className="ltr font-mono text-sm text-ink" dir="ltr">
                {Number.isFinite(turnsSoFar) ? fmt(turnsSoFar, 2) : "—"}
              </span>
            </p>
          </div>
          <Readout className="text-sm">
            <dl className="grid grid-cols-[auto_minmax(0,1fr)] gap-x-3 gap-y-1">
              <dt className="text-ink-2">{t("w.field.circulation")}</dt>
              <dd className="ltr font-serif" dir="ltr">
                <span className="whitespace-nowrap">∮ <b>F</b>·d<b>r</b> ≈ {fmt(stats.line.circulation, 4)}</span> <span className="text-ink-2">|</span>{" "}
                <span className="whitespace-nowrap">∬ curl <b>F</b> dA ≈ {fmt(stats.disk.curl, 4)}</span>
              </dd>
              <dt className="text-ink-2">{t("w.field.flux")}</dt>
              <dd className="ltr font-serif" dir="ltr">
                <span className="whitespace-nowrap">∮ <b>F</b>·<b>n</b> ds ≈ {fmt(stats.line.flux, 4)}</span> <span className="text-ink-2">|</span>{" "}
                <span className="whitespace-nowrap">∬ div <b>F</b> dA ≈ {fmt(stats.disk.div, 4)}</span>
              </dd>
              <dt className="text-ink-2">{t("w.field.atCentre")}</dt>
              <dd className="ltr font-serif" dir="ltr">
                <span className="whitespace-nowrap">curl <b>F</b> ≈ {fmt(stats.local.curl, 3)},</span> <span className="whitespace-nowrap">div <b>F</b> ≈ {fmt(stats.local.div, 3)},</span>{" "}
                <span className="whitespace-nowrap">πr² ≈ {fmt(Math.PI * r * r, 3)}</span>
              </dd>
              <dt className="text-ink-2">{t("w.field.indexLabel")}</dt>
              <dd className="ltr font-serif text-base font-semibold text-ink" dir="ltr">
                {idx && (idx.status === "ok" || idx.status === "near") ? idx.index : "—"}
              </dd>
            </dl>
            <p className="mt-2 text-xs text-muted">{t("w.field.numerical")}</p>
          </Readout>
        </div>
      )}
      {stats && (
        <div className="mt-3 space-y-2 text-sm text-ink-2" aria-live="polite">
          <p className={`rounded-xl px-4 py-2.5 ${greenOk ? "bg-good-soft" : "bg-warn-soft"} text-ink`}>
            <strong>{greenOk ? t("w.field.green.okTitle") : t("w.field.green.failTitle")}</strong> {greenOk ? t("w.field.green.ok") : t("w.field.green.fail")}
          </p>
          <p className="rounded-xl bg-paper-2 px-4 py-2.5 text-ink">{indexText}</p>
        </div>
      )}
    </div>
  );
}

function LoopLayer({ view, F, centre, r, theta }: { view: PlotView; F: Field2 | null; centre: Pt; r: number; theta: number }) {
  const { sx, sy } = view;
  const kx = view.W / (view.x[1] - view.x[0]);
  const rPx = r * kx;
  const samples = useMemo(() => {
    if (!F) return { line: "", head: "" };
    let line = "";
    let head = "";
    const N = 16;
    for (let k = 0; k < N; k++) {
      const s = (2 * Math.PI * k) / N;
      const p: Pt = [centre[0] + r * Math.cos(s), centre[1] + r * Math.sin(s)];
      const v = F(p[0], p[1]);
      const m = Math.hypot(v[0], v[1]);
      if (!(m > 0) || !Number.isFinite(m)) continue;
      const X = sx(p[0]);
      const Y = sy(p[1]);
      const a = arrowPath(X, Y, X + (v[0] / m) * 22, Y - (v[1] / m) * 22, 7);
      line += a.line;
      head += a.head;
    }
    return { line, head };
  }, [F, centre, r, sx, sy]);
  const wp: Pt = [centre[0] + r * Math.cos(theta), centre[1] + r * Math.sin(theta)];
  const wv = F ? F(wp[0], wp[1]) : ([NaN, NaN] as Pt);
  const wm = Math.hypot(wv[0], wv[1]);
  const WX = sx(wp[0]);
  const WY = sy(wp[1]);
  const wa = wm > 0 && Number.isFinite(wm) ? arrowPath(WX, WY, WX + (wv[0] / wm) * 34, WY - (wv[1] / wm) * 34, 10) : null;
  // A small arc arrow showing the anticlockwise direction of traversal.
  const a0 = 0.15;
  const a1 = 0.55;
  const arc = `M${(sx(centre[0]) + (rPx + 9) * Math.cos(a0)).toFixed(1)} ${(sy(centre[1]) - (rPx + 9) * Math.sin(a0)).toFixed(1)}A${(rPx + 9).toFixed(1)} ${(rPx + 9).toFixed(1)} 0 0 0 ${(sx(centre[0]) + (rPx + 9) * Math.cos(a1)).toFixed(1)} ${(sy(centre[1]) - (rPx + 9) * Math.sin(a1)).toFixed(1)}`;
  const tip = arrowPath(sx(centre[0]) + (rPx + 9) * Math.cos(a1 - 0.08), sy(centre[1]) - (rPx + 9) * Math.sin(a1 - 0.08), sx(centre[0]) + (rPx + 9) * Math.cos(a1), sy(centre[1]) - (rPx + 9) * Math.sin(a1), 7);
  return (
    <>
      <ArrowGrid view={view} F={F} />
      <circle cx={sx(centre[0])} cy={sy(centre[1])} r={rPx} fill="var(--gold)" fillOpacity={0.1} stroke="var(--gold-ink)" strokeWidth={2.5} />
      <path d={arc} fill="none" stroke="var(--gold-ink)" strokeWidth={1.5} />
      <path d={tip.head} fill="var(--gold-ink)" />
      <g aria-hidden="true">
        <path d={samples.line} stroke="var(--formal)" strokeWidth={2} strokeLinecap="round" fill="none" opacity={0.75} />
        <path d={samples.head} fill="var(--formal)" opacity={0.75} />
      </g>
      {wa && (
        <g aria-hidden="true">
          <path d={wa.line} stroke="var(--formal)" strokeWidth={3.5} strokeLinecap="round" />
          <path d={wa.head} fill="var(--formal)" />
        </g>
      )}
      <circle cx={WX} cy={WY} r={5} fill="var(--gold)" stroke="var(--card)" strokeWidth={2} aria-hidden="true" />
    </>
  );
}

