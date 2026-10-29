"use client";

import { Pencil, RotateCcw } from "lucide-react";
import { useId, useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { compileExpr, prettyExpr, stripLhs, toParams, toRange, type CompiledExpr, type ExprError, type ParamSpec, type Vars } from "./lib/expr";
import { autoRange, fmt, integrate, pathD, sampleFunction, sampleParametric, type Pt, type Range } from "./lib/plot-core";
import { Plot, type PlotView } from "./lib/plot-svg";
import { ExprErrorNote, ExprField, LegendSwatch, Readout, Slider, seriesColor, seriesDash } from "./lib/plot-ui";

export type CurveMode = "graph" | "parametric" | "polar";
const MODES: readonly CurveMode[] = ["graph", "parametric", "polar"];
const MAX_CURVES = 6;
const MAX_POINTS = 24;

export type Curve =
  | { ok: true; kind: "graph"; source: string; f: CompiledExpr }
  | { ok: true; kind: "parametric"; source: string; fx: CompiledExpr; fy: CompiledExpr }
  | { ok: true; kind: "polar"; source: string; r: CompiledExpr }
  | { ok: false; source: string; error: ExprError; errorSource: string };

const VARS: Record<CurveMode, string[]> = { graph: ["x"], parametric: ["t"], polar: ["t", "theta", "θ"] };

/** Group the `fns` prop into curve sources: strings for graph/polar, [x(t), y(t)] pairs for parametric. */
function curveSources(fns: unknown, mode: CurveMode): (string | [string, string])[] {
  const list = Array.isArray(fns) ? fns : typeof fns === "string" ? [fns] : [];
  const str = (v: unknown) => (typeof v === "string" ? v : typeof v === "number" && Number.isFinite(v) ? String(v) : null);
  if (mode !== "parametric") return list.map(str).filter((s): s is string => s !== null).slice(0, MAX_CURVES);
  const out: [string, string][] = [];
  if (list.every((v) => Array.isArray(v))) {
    for (const p of list as unknown[][]) {
      const a = str(p[0]);
      const b = str(p[1]);
      if (a !== null && b !== null) out.push([a, b]);
    }
  } else {
    const flat = list.map(str);
    for (let i = 0; i + 1 < flat.length; i += 2) if (flat[i] !== null && flat[i + 1] !== null) out.push([flat[i]!, flat[i + 1]!]);
  }
  return out.slice(0, MAX_CURVES);
}

/** Compile the curves of a FunctionPlot (exported for tests). */
export function parseCurves(fns: unknown, mode: CurveMode, paramNames: readonly string[]): Curve[] {
  const allowed = [...VARS[mode], ...paramNames];
  return curveSources(fns, mode).map((src): Curve => {
    if (Array.isArray(src)) {
      const a = compileExpr(stripLhs(src[0]), allowed);
      const b = compileExpr(stripLhs(src[1]), allowed);
      const source = `${src[0]}, ${src[1]}`;
      if (!a.ok) return { ok: false, source, error: a.error, errorSource: a.source };
      if (!b.ok) return { ok: false, source, error: b.error, errorSource: b.source };
      return { ok: true, kind: "parametric", source, fx: a.fn, fy: b.fn };
    }
    const r = compileExpr(stripLhs(src), allowed);
    if (!r.ok) return { ok: false, source: src, error: r.error, errorSource: r.source };
    return mode === "polar" ? { ok: true, kind: "polar", source: src, r: r.fn } : { ok: true, kind: "graph", source: src, f: r.fn };
  });
}

export interface PlotPoint {
  x: CompiledExpr;
  y: CompiledExpr;
  label?: string;
}

/** Read the `points` prop: [[x, y], [x, y, "label"], {x, y, label}]; coordinates may use parameters. */
export function parsePoints(points: unknown, paramNames: readonly string[]): PlotPoint[] {
  if (!Array.isArray(points)) return [];
  const out: PlotPoint[] = [];
  for (const p of points.slice(0, MAX_POINTS)) {
    let x: unknown;
    let y: unknown;
    let label: unknown;
    if (Array.isArray(p)) [x, y, label] = p;
    else if (p && typeof p === "object") ({ x, y, label } = p as Record<string, unknown>);
    else continue;
    const cx = compileExpr(typeof x === "number" ? String(x) : x, paramNames);
    const cy = compileExpr(typeof y === "number" ? String(y) : y, paramNames);
    if (!cx.ok || !cy.ok) continue;
    out.push({ x: cx.fn, y: cy.fn, label: typeof label === "string" ? label.slice(0, 40) : undefined });
  }
  return out;
}

const curveVars = (mode: CurveMode, v: number, params: Vars): Vars => (mode === "graph" ? { ...params, x: v } : { ...params, t: v, theta: v, θ: v });

function curveFns(c: Extract<Curve, { ok: true }>, params: Vars): { fx: (t: number) => number; fy: (t: number) => number } | { f: (x: number) => number } {
  if (c.kind === "graph") return { f: (x: number) => c.f({ ...params, x }) };
  if (c.kind === "parametric") return { fx: (t: number) => c.fx({ ...params, t }), fy: (t: number) => c.fy({ ...params, t }) };
  const r = (t: number) => c.r({ ...params, t, theta: t, θ: t });
  return { fx: (t: number) => r(t) * Math.cos(t), fy: (t: number) => r(t) * Math.sin(t) };
}

function sampleCurve(c: Extract<Curve, { ok: true }>, params: Vars, view: { x: Range; y: Range }, tRange: Range, n: number): Pt[][] {
  const fns = curveFns(c, params);
  if ("f" in fns) return sampleFunction(fns.f, view.x, { y: view.y, n });
  return sampleParametric(fns.fx, fns.fy, tRange, view, Math.max(1200, n * 2));
}

interface FunctionPlotProps {
  fns?: unknown;
  mode?: string;
  x?: unknown;
  y?: unknown;
  t?: unknown;
  params?: unknown;
  labels?: unknown;
  points?: unknown;
  shade?: unknown;
  shadeRange?: unknown;
  aspect?: unknown;
  editable?: boolean;
  xLabel?: string;
  yLabel?: string;
  title?: string;
  subtitle?: string;
}

const DEFAULT_FNS = ["sin(x)", "cos(x)"];

/**
 * Graphs of y = f(x), parametric curves (x(t), y(t)) and polar curves r(θ),
 * with parameter sliders, marked points, shading and a trace read-out.
 */
export function FunctionPlot(props: FunctionPlotProps) {
  const { t } = useI18n();
  const mode: CurveMode = MODES.includes(props.mode as CurveMode) ? (props.mode as CurveMode) : "graph";
  const usingDefault = props.fns === undefined;
  const specs = useMemo(() => toParams(props.params, [...VARS[mode]]), [props.params, mode]);
  const initialSources = useMemo(() => curveSources(usingDefault ? DEFAULT_FNS : props.fns, mode), [props.fns, usingDefault, mode]);
  const [sources, setSources] = useState(initialSources);
  const [values, setValues] = useState<Record<string, number>>(() => Object.fromEntries(specs.map((p) => [p.name, p.value])));
  const [editing, setEditing] = useState(false);
  const paramNames = specs.map((p) => p.name);
  const params: Vars = useMemo(() => Object.fromEntries(specs.map((p) => [p.name, values[p.name] ?? p.value])), [specs, values]);
  const curves = useMemo(() => parseCurves(sources, mode, paramNames), [sources, mode, paramNames.join(",")]); // eslint-disable-line react-hooks/exhaustive-deps
  const points = useMemo(() => parsePoints(props.points, paramNames), [props.points, paramNames.join(",")]); // eslint-disable-line react-hooks/exhaustive-deps
  const labels = Array.isArray(props.labels) ? props.labels.map((l) => (typeof l === "string" ? l.slice(0, 60) : null)) : [];

  const tRange = toRange(props.t, [0, 2 * Math.PI]);
  const defaultX: Range = usingDefault ? [-2 * Math.PI, 2 * Math.PI] : [-5, 5];
  const initialParams = useMemo(() => Object.fromEntries(specs.map((p) => [p.name, p.value])), [specs]);

  // Windows: given ones are used as-is; missing ones are found once from the initial curves (so sliders don't make axes jump).
  const xGiven = Array.isArray(props.x);
  const yGiven = Array.isArray(props.y);
  const xKey = JSON.stringify(props.x ?? null);
  const yKey = JSON.stringify(props.y ?? null);
  const [xWin, yWin] = useMemo((): [Range, Range] => {
    const initialCurves = parseCurves(initialSources, mode, paramNames).filter((c): c is Extract<Curve, { ok: true }> => c.ok);
    if (mode === "graph") {
      const xw = toRange(props.x, defaultX);
      if (yGiven) return [xw, toRange(props.y, [-5, 5])];
      const ys: number[] = [];
      for (const c of initialCurves) for (let i = 0; i <= 240; i++) {
        const xv = xw[0] + ((xw[1] - xw[0]) * i) / 240;
        ys.push((c as Extract<Curve, { kind: "graph" }>).f({ ...initialParams, x: xv }));
      }
      return [xw, autoRange(ys, [-5, 5], [0])];
    }
    const xs: number[] = [];
    const ys: number[] = [];
    for (const c of initialCurves) {
      const fns = curveFns(c, initialParams);
      if ("f" in fns) continue;
      for (let i = 0; i <= 600; i++) {
        const tv = tRange[0] + ((tRange[1] - tRange[0]) * i) / 600;
        xs.push(fns.fx(tv));
        ys.push(fns.fy(tv));
      }
    }
    return [xGiven ? toRange(props.x, [-3, 3]) : autoRange(xs, [-3, 3], [0]), yGiven ? toRange(props.y, [-3, 3]) : autoRange(ys, [-3, 3], [0])];
  }, [mode, initialSources, xKey, yKey, tRange[0], tRange[1], initialParams]); // eslint-disable-line react-hooks/exhaustive-deps

  const aspect = props.aspect === "equal" || (props.aspect === undefined && mode !== "graph") ? "equal" : 0.62;
  const shadeIndex = mode === "graph" && typeof props.shade === "number" && Number.isInteger(props.shade) ? props.shade : -1;
  const shadeCurve = shadeIndex >= 0 && curves[shadeIndex]?.ok ? (curves[shadeIndex] as Extract<Curve, { kind: "graph" }>) : null;
  const shadeRange = Array.isArray(props.shadeRange) ? toRange(props.shadeRange, xWin, params) : null;

  // Trace: x in graph mode, t (or θ) otherwise.
  const traceRange: Range = mode === "graph" ? xWin : tRange;
  const [trace, setTrace] = useState<number | null>(null);
  const traceValue = trace ?? (mode === "graph" ? clampTo(1, xWin) : tRange[0] + (tRange[1] - tRange[0]) / 8);
  const traceStep = (traceRange[1] - traceRange[0]) / 400;

  const okCurves = curves.map((c, i) => ({ c, i })).filter((e): e is { c: Extract<Curve, { ok: true }>; i: number } => e.c.ok);
  const tracePts = okCurves.map(({ c, i }) => {
    const fns = curveFns(c, params);
    const p: Pt = "f" in fns ? [traceValue, fns.f(traceValue)] : [fns.fx(traceValue), fns.fy(traceValue)];
    const r = c.kind === "polar" ? c.r(curveVars("polar", traceValue, params)) : NaN;
    return { i, p, r };
  });

  const shadeArea = useMemo(() => {
    if (!shadeCurve || !shadeRange) return null;
    const v = integrate((x) => shadeCurve.f({ ...params, x }), shadeRange[0], shadeRange[1], 1e-9);
    return Number.isFinite(v) ? v : null;
  }, [shadeCurve, shadeRange?.[0], shadeRange?.[1], params]); // eslint-disable-line react-hooks/exhaustive-deps

  const label = (i: number) => {
    if (labels[i]) return labels[i]!;
    const src = curves[i]?.source ?? "";
    if (mode === "graph") return `y = ${prettyExpr(stripLhs(src))}`;
    if (mode === "polar") return `r = ${prettyExpr(stripLhs(src))}`;
    return `(x, y) = (${prettyExpr(src)})`;
  };
  const varName = mode === "graph" ? "x" : mode === "polar" ? "θ" : "t";
  const ariaList = curves.map((_, i) => label(i)).join("; ");
  const aria = t(`w.plot.aria.${mode}`, { list: ariaList || "—", xmin: fmt(xWin[0], 2), xmax: fmt(xWin[1], 2) });

  const reset = () => {
    setSources(initialSources);
    setValues(Object.fromEntries(specs.map((p) => [p.name, p.value])));
    setTrace(null);
  };

  const patternId = `fp-hatch-${useId().replace(/[^a-zA-Z0-9_-]/g, "")}`;

  return (
    <WidgetFrame title={props.title ?? t(`w.plot.title.${mode}`)} subtitle={props.subtitle ?? t(`w.plot.subtitle.${mode}`)}>
      <Plot
        x={xWin}
        y={yWin}
        aspect={aspect}
        ariaLabel={aria}
        xLabel={props.xLabel ?? "x"}
        yLabel={props.yLabel ?? "y"}
        onHover={mode === "graph" ? (p) => p && setTrace(clampTo(p[0], xWin)) : undefined}
        readout={
          tracePts.length > 0 ? (
            <span>
              {varName} = {fmt(traceValue, 2)}
            </span>
          ) : null
        }
      >
        {(view) => (
          <>
            <defs>
              <pattern id={patternId} width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
                <line x1="0" y1="0" x2="0" y2="7" stroke="var(--human)" strokeWidth="2" strokeOpacity="0.45" />
              </pattern>
            </defs>
            {shadeCurve && <Shade view={view} f={(x) => shadeCurve.f({ ...params, x })} range={shadeRange ?? view.x} patternId={patternId} />}
            {mode === "polar" && <PolarRay view={view} pt={tracePts[0]?.p} />}
            {okCurves.map(({ c, i }) => (
              <CurvePath key={`${i}-${c.source}`} curve={c} params={params} view={view} tRange={tRange} color={seriesColor(i)} dash={seriesDash(i)} />
            ))}
            {mode === "graph" && Number.isFinite(view.sx(traceValue)) && (
              <line x1={view.sx(traceValue)} x2={view.sx(traceValue)} y1={0} y2={view.H} stroke="var(--muted)" strokeDasharray="3 4" strokeWidth={1} aria-hidden="true" />
            )}
            {tracePts.map(({ i, p }) =>
              Number.isFinite(p[0]) && Number.isFinite(p[1]) ? <circle key={i} cx={view.sx(p[0])} cy={view.sy(p[1])} r={5} fill={seriesColor(i)} stroke="var(--card)" strokeWidth={2} /> : null,
            )}
            {points.map((pt, k) => {
              const px = pt.x(params);
              const py = pt.y(params);
              if (!Number.isFinite(px) || !Number.isFinite(py)) return null;
              return (
                <g key={`pt${k}`}>
                  <circle cx={view.sx(px)} cy={view.sy(py)} r={4.5} fill="var(--ink)" stroke="var(--card)" strokeWidth={2} />
                  {pt.label && (
                    <text x={view.sx(px) + 8} y={view.sy(py) - 8} fontSize={13} fill="var(--ink)" className="font-serif" fontStyle="italic" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                      {pt.label}
                    </text>
                  )}
                </g>
              );
            })}
          </>
        )}
      </Plot>

      {/* Legend */}
      <ul className="mt-3 flex flex-wrap gap-x-4 gap-y-1.5 text-sm" dir="ltr" aria-label={t("w.plot.legend")}>
        {curves.map((c, i) => (
          <li key={i} className="flex min-w-0 items-center gap-2">
            <LegendSwatch color={c.ok ? seriesColor(i) : "var(--bad)"} dash={seriesDash(i)} />
            <span className={`truncate font-serif ${c.ok ? "text-ink" : "text-bad line-through"}`}>{label(i)}</span>
          </li>
        ))}
        {shadeCurve && (
          <li className="flex items-center gap-2 text-ink-2">
            <svg width="22" height="12" aria-hidden="true">
              <rect width="11" height="12" fill="var(--gold)" fillOpacity="0.3" />
              <rect x="11" width="11" height="12" fill={`url(#${patternId})`} />
            </svg>
            <span className="font-sans text-xs">{t("w.plot.shadeLegend")}</span>
          </li>
        )}
      </ul>
      {!editing && curves.map((c, i) => (!c.ok ? <ExprErrorNote key={`e${i}`} error={c.error} source={c.errorSource} /> : null))}

      {/* Parameters */}
      {specs.length > 0 && (
        <div className="mt-4 grid gap-x-6 gap-y-3 sm:grid-cols-2">
          {specs.map((p: ParamSpec) => (
            <Slider
              key={p.name}
              label={<span className="font-serif text-base italic text-ink">{p.label ?? p.name}</span>}
              value={values[p.name] ?? p.value}
              min={p.min}
              max={p.max}
              step={p.step}
              onChange={(v) => setValues((old) => ({ ...old, [p.name]: v }))}
              display={`${p.name} = ${fmt(values[p.name] ?? p.value, 3)}`}
            />
          ))}
        </div>
      )}

      {/* Trace */}
      <div className="mt-4 grid gap-3 sm:grid-cols-[minmax(0,1fr)_minmax(0,1.3fr)] sm:items-center">
        <Slider
          label={t(`w.plot.trace.${mode}`)}
          value={traceValue}
          min={traceRange[0]}
          max={traceRange[1]}
          step={traceStep}
          onChange={setTrace}
          display={`${varName} = ${fmt(traceValue, 2)}`}
          accent="var(--sky)"
        />
        <Readout className="font-serif text-[0.95rem]">
          <ul className="space-y-0.5" dir="ltr">
            {tracePts.length === 0 && <li className="font-sans text-sm text-muted">{t("w.plot.nothing")}</li>}
            {tracePts.map(({ i, p, r }) => (
              <li key={i} className="flex items-center gap-2">
                <LegendSwatch color={seriesColor(i)} dash={seriesDash(i)} width={2.5} />
                {mode === "graph" ? (
                  <span>
                    {labels[i] ? <span className="text-ink-2">{labels[i]}: </span> : null}
                    <i>y</i> = {Number.isFinite(p[1]) ? fmt(p[1], 4) : <span className="font-sans text-sm text-muted">{t("w.plot.undefined")}</span>}
                  </span>
                ) : (
                  <span>
                    {Number.isFinite(p[0]) && Number.isFinite(p[1]) ? `(${fmt(p[0], 3)}, ${fmt(p[1], 3)})` : <span className="font-sans text-sm text-muted">{t("w.plot.undefined")}</span>}
                    {mode === "polar" && Number.isFinite(r) && <span className="text-ink-2"> · r = {fmt(r, 3)}</span>}
                  </span>
                )}
              </li>
            ))}
            {shadeCurve && shadeRange && shadeArea !== null && (
              <li className="pt-1 font-sans text-sm text-ink-2">
                {t("w.plot.area", { a: fmt(shadeRange[0], 3), b: fmt(shadeRange[1], 3), value: fmt(shadeArea, 4) })}
              </li>
            )}
          </ul>
        </Readout>
      </div>

      {/* Edit + reset */}
      {(props.editable ?? true) && (
        <div className="mt-4 border-t border-line pt-3">
          <div className="flex flex-wrap items-center gap-2">
            <button type="button" className="btn btn-sm btn-ghost" aria-expanded={editing} onClick={() => setEditing((e) => !e)}>
              <Pencil size={14} aria-hidden="true" /> {editing ? t("w.plot.doneEditing") : t("w.plot.edit")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={reset}>
              <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
            </button>
          </div>
          {editing && (
            <div className="mt-3 space-y-3">
              {sources.map((src, i) =>
                Array.isArray(src) ? (
                  <div key={i} className="grid gap-3 sm:grid-cols-2">
                    {[0, 1].map((k) => (
                      <ExprField
                        key={k}
                        label={`${t("w.plot.curve", { n: i + 1 })} · ${k === 0 ? "x(t)" : "y(t)"}`}
                        prefix={k === 0 ? "x =" : "y ="}
                        value={src[k]}
                        onChange={(v) => setSources((old) => old.map((s, j) => (j === i && Array.isArray(s) ? ((k === 0 ? [v, s[1]] : [s[0], v]) as [string, string]) : s)))}
                        result={compileExpr(stripLhs(src[k]), [...VARS[mode], ...paramNames])}
                      />
                    ))}
                  </div>
                ) : (
                  <ExprField
                    key={i}
                    label={t("w.plot.curve", { n: i + 1 })}
                    prefix={mode === "polar" ? "r =" : "y ="}
                    value={src}
                    onChange={(v) => setSources((old) => old.map((s, j) => (j === i ? v : s)))}
                    result={compileExpr(stripLhs(src), [...VARS[mode], ...paramNames])}
                  />
                ),
              )}
              <p className="text-xs text-muted">{t("w.plot.syntax", { vars: [mode === "graph" ? "x" : mode === "polar" ? "t (θ)" : "t", ...paramNames].join(", ") })}</p>
            </div>
          )}
        </div>
      )}
    </WidgetFrame>
  );
}

function clampTo(v: number, r: Range) {
  return Math.min(r[1], Math.max(r[0], v));
}

function CurvePath({ curve, params, view, tRange, color, dash }: { curve: Extract<Curve, { ok: true }>; params: Vars; view: PlotView; tRange: Range; color: string; dash: string }) {
  const { x, y, W } = view;
  const d = useMemo(
    () => pathD(sampleCurve(curve, params, { x, y }, tRange, Math.max(400, W)), view.sx, view.sy),
    [curve, params, x[0], x[1], y[0], y[1], tRange[0], tRange[1], W], // eslint-disable-line react-hooks/exhaustive-deps
  );
  return <path d={d} fill="none" stroke={color} strokeWidth={2.5} strokeDasharray={dash || undefined} strokeLinecap="round" strokeLinejoin="round" />;
}

function Shade({ view, f, range, patternId }: { view: PlotView; f: (x: number) => number; range: Range; patternId: string }) {
  const lo = Math.max(range[0], view.x[0]);
  const hi = Math.min(range[1], view.x[1]);
  if (!(hi > lo)) return null;
  const lines = sampleFunction(f, [lo, hi], { y: view.y, n: Math.max(300, view.W / 2) });
  const Y0 = view.sy(0);
  let d = "";
  for (const line of lines) {
    if (line.length < 2) continue;
    d += `M${view.sx(line[0][0]).toFixed(2)} ${Y0.toFixed(2)}`;
    for (const [px, py] of line) d += `L${view.sx(px).toFixed(2)} ${view.sy(py).toFixed(2)}`;
    d += `L${view.sx(line[line.length - 1][0]).toFixed(2)} ${Y0.toFixed(2)}Z`;
  }
  const above = `${patternId}-up`;
  const below = `${patternId}-dn`;
  return (
    <g aria-hidden="true">
      <clipPath id={above}>
        <rect x={0} y={0} width={view.W} height={Math.max(0, Math.min(view.H, Y0))} />
      </clipPath>
      <clipPath id={below}>
        <rect x={0} y={Math.max(0, Math.min(view.H, Y0))} width={view.W} height={view.H} />
      </clipPath>
      <path d={d} fill="var(--gold)" fillOpacity={0.28} clipPath={`url(#${above})`} />
      <path d={d} fill={`url(#${patternId})`} clipPath={`url(#${below})`} />
      <path d={d} fill="var(--human)" fillOpacity={0.08} clipPath={`url(#${below})`} />
      {[lo, hi].map((v, k) => (
        <line key={k} x1={view.sx(v)} x2={view.sx(v)} y1={0} y2={view.H} stroke="var(--gold-ink)" strokeOpacity={0.5} strokeDasharray="2 4" />
      ))}
    </g>
  );
}

function PolarRay({ view, pt }: { view: PlotView; pt?: Pt }) {
  if (!pt || !Number.isFinite(pt[0]) || !Number.isFinite(pt[1])) return null;
  return <line x1={view.sx(0)} y1={view.sy(0)} x2={view.sx(pt[0])} y2={view.sy(pt[1])} stroke="var(--muted)" strokeWidth={1.25} strokeDasharray="4 4" aria-hidden="true" />;
}

