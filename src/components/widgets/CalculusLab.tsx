"use client";

import { Check, Pencil, Play, RotateCcw, Search, X, ZoomIn } from "lucide-react";
import { useEffect, useId, useMemo, useRef, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { compileExpr, prettyExpr, stripLhs, toNumber, toRange } from "./lib/expr";
import { autoRange, clamp, fmt, integrate, pathD, piLabel, sampleFunction, type Range } from "./lib/plot-core";
import { Plot, PlotHandle, type PlotView } from "./lib/plot-svg";
import { ExprErrorNote, ExprField, LegendSwatch, ModeTabs, NumberField, Readout, Slider, useReducedMotion } from "./lib/plot-ui";
import {
  RIEMANN_METHODS,
  TAYLOR,
  TAYLOR_IDS,
  checkDelta,
  derivativeAt,
  differenceQuotient,
  inConvergence,
  largestDelta,
  logSliderPosition,
  logSliderValue,
  riemannSum,
  taylorFormula,
  taylorPolynomial,
  type Fn,
  type RiemannMethod,
  type RiemannPiece,
  type TaylorId,
} from "./lib/plot-calc";

export type CalcMode = "tangent" | "riemann" | "taylor" | "epsilon-delta";
const MODES: readonly CalcMode[] = ["tangent", "riemann", "taylor", "epsilon-delta"];
const MODE_KEY: Record<CalcMode, string> = { tangent: "tangent", riemann: "riemann", taylor: "taylor", "epsilon-delta": "epsdelta" };

export interface CalculusLabProps {
  mode?: unknown;
  modes?: unknown;
  fn?: unknown;
  x0?: unknown;
  a?: unknown;
  L?: unknown;
  interval?: unknown;
  exact?: unknown;
  preset?: unknown;
  x?: unknown;
  y?: unknown;
  n?: unknown;
  method?: unknown;
  degree?: unknown;
  epsilon?: unknown;
  title?: string;
  subtitle?: string;
}

const isMode = (m: unknown): m is CalcMode => typeof m === "string" && (MODES as readonly string[]).includes(m);
const isTaylor = (p: unknown): p is TaylorId => typeof p === "string" && (TAYLOR_IDS as readonly string[]).includes(p);

/** Which mode tabs to offer: `modes` if given, else only `mode` if given, else all four. */
export function calcModes(mode: unknown, modes: unknown): CalcMode[] {
  if (Array.isArray(modes)) {
    const list = [...new Set(modes.filter(isMode))];
    if (list.length > 0) return list;
  }
  return isMode(mode) ? [mode] : [...MODES];
}

const fnSource = (v: unknown, fallback: string) => (typeof v === "string" && v.trim() !== "" ? v : typeof v === "number" && Number.isFinite(v) ? String(v) : fallback);
const intProp = (v: unknown, lo: number, hi: number, fallback: number) => {
  const x = toNumber(v, fallback);
  return clamp(Math.round(x), lo, hi);
};
const paren = (v: number, d = 4) => (v < 0 ? `(${fmt(v, d)})` : fmt(v, d));
/** fmt, but multiples of π/4 (that are not integers) are written with π: 3π/2. */
const fmtPi = (v: number, d = 3) => {
  const q = v / (Math.PI / 4);
  return Math.abs(q - Math.round(q)) < 1e-9 && Math.abs(v - Math.round(v)) > 1e-9 ? piLabel(Math.round(q), 4) : fmt(v, d);
};
const SUB: Record<string, string> = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉" };
const sub = (k: number) => String(k).replace(/\d/g, (d) => SUB[d]);

/**
 * CalculusLab — four classic pictures of calculus: secant → tangent,
 * Riemann sums, Taylor polynomials, and the ε–δ game for limits.
 */
export function CalculusLab(props: CalculusLabProps) {
  const { t } = useI18n();
  const offered = useMemo(() => calcModes(props.mode, props.modes), [props.mode, props.modes]);
  const initial: CalcMode = isMode(props.mode) && offered.includes(props.mode) ? props.mode : isTaylor(props.preset) && offered.includes("taylor") ? "taylor" : offered[0];
  const [mode, setMode] = useState<CalcMode>(initial);
  const key = MODE_KEY[mode];
  return (
    <WidgetFrame title={props.title ?? t(`w.calc.title.${key}`)} subtitle={props.subtitle ?? t(`w.calc.subtitle.${key}`)}>
      {offered.length > 1 && (
        <div className="mb-4">
          <ModeTabs value={mode} options={offered} onChange={setMode} label={t("w.calc.modesLabel")} render={(m) => t(`w.calc.mode.${MODE_KEY[m]}`)} />
        </div>
      )}
      {mode === "tangent" && <TangentMode {...props} />}
      {mode === "riemann" && <RiemannMode {...props} />}
      {mode === "taylor" && <TaylorMode {...props} />}
      {mode === "epsilon-delta" && <EpsDeltaMode {...props} />}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------------------
 * Shared pieces
 * ------------------------------------------------------------------------- */

function useFn(initial: string) {
  const [src, setSrc] = useState(initial);
  const [editing, setEditing] = useState(false);
  const compiled = useMemo(() => compileExpr(stripLhs(src), ["x"]), [src]);
  const f: Fn = useMemo(() => (compiled.ok ? (x: number) => compiled.fn({ x }) : () => NaN), [compiled]);
  return { src, setSrc, compiled, f, editing, setEditing };
}
type FnState = ReturnType<typeof useFn>;

/** Inline error for an unparsable function, shown under the legend while the editor is closed. */
function FnError({ fn }: { fn: FnState }) {
  return !fn.editing && !fn.compiled.ok ? <ExprErrorNote error={fn.compiled.error} source={fn.compiled.source} /> : null;
}

/** Automatic y-window from samples of f over the x-window (computed once per function/window). */
function autoY(f: Fn, x: Range, include: number[] = [0]): Range {
  const ys: number[] = [];
  for (let i = 0; i <= 300; i++) ys.push(f(x[0] + ((x[1] - x[0]) * i) / 300));
  return autoRange(ys, [-5, 5], include);
}

function Curve({ f, view, color = "var(--formal)", width = 2.5, dash, clipPath }: { f: Fn; view: PlotView; color?: string; width?: number; dash?: string; clipPath?: string }) {
  const { x, y, W } = view;
  const d = useMemo(
    () => pathD(sampleFunction(f, x, { y, n: Math.max(400, W) }), view.sx, view.sy),
    [f, x[0], x[1], y[0], y[1], W], // eslint-disable-line react-hooks/exhaustive-deps
  );
  return <path d={d} fill="none" stroke={color} strokeWidth={width} strokeDasharray={dash} strokeLinecap="round" strokeLinejoin="round" clipPath={clipPath} />;
}

/** A straight line y = y0 + m (x − x0) across the whole window. */
function FullLine({ view, x0, y0, m, color, width = 2, dash }: { view: PlotView; x0: number; y0: number; m: number; color: string; width?: number; dash?: string }) {
  if (![x0, y0, m].every(Number.isFinite)) return null;
  const [a, b] = view.x;
  const ya = y0 + m * (a - x0);
  const yb = y0 + m * (b - x0);
  return <line x1={view.sx(a)} y1={view.sy(ya)} x2={view.sx(b)} y2={view.sy(yb)} stroke={color} strokeWidth={width} strokeDasharray={dash} strokeLinecap="round" />;
}

function Legend({ items }: { items: { label: ReactNode; color: string; dash?: string; width?: number }[] }) {
  const { t } = useI18n();
  return (
    <ul className="mt-3 flex flex-wrap gap-x-5 gap-y-1.5 text-sm" aria-label={t("w.plot.legend")}>
      {items.map((it, i) => (
        <li key={i} className="flex min-w-0 items-center gap-2">
          <LegendSwatch color={it.color} dash={it.dash} width={it.width ?? 3} />
          <span className="min-w-0 text-ink-2">{it.label}</span>
        </li>
      ))}
    </ul>
  );
}

function FnEditor({ fn, onReset, children }: { fn: FnState; onReset: () => void; children?: ReactNode }) {
  const { t } = useI18n();
  const open = fn.editing;
  const setOpen = fn.setEditing;
  return (
    <div className="mt-4 border-t border-line pt-3">
      <div className="flex flex-wrap items-center gap-2">
        <button type="button" className="btn btn-sm btn-ghost" aria-expanded={open} onClick={() => setOpen((o) => !o)}>
          <Pencil size={14} aria-hidden="true" /> {open ? t("w.calc.doneEditing") : t("w.calc.editFn")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" onClick={onReset}>
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>
      {open && (
        <div className="mt-3 space-y-3">
          <ExprField label={t("w.calc.fnLabel")} prefix="f(x) =" value={fn.src} onChange={fn.setSrc} result={fn.compiled} />
          {children && <div className="flex flex-wrap items-center gap-x-5 gap-y-2">{children}</div>}
          <p className="text-xs text-muted">{t("w.plot.syntax", { vars: "x" })}</p>
        </div>
      )}
    </div>
  );
}

function Note({ tone, children }: { tone: "good" | "bad" | "warn" | "info"; children: ReactNode }) {
  const cls = tone === "good" ? "border-good/40 bg-good-soft" : tone === "bad" ? "border-bad/40 bg-bad-soft" : tone === "warn" ? "border-warn/40 bg-warn-soft" : "border-line bg-paper-2";
  return <div className={`rounded-xl border px-3.5 py-2.5 text-sm text-ink ${cls}`}>{children}</div>;
}

/* ---------------------------------------------------------------------------
 * Mode 1: secant → tangent
 * ------------------------------------------------------------------------- */

const H_MAX = 2;
const H_MIN = 0.001;

function TangentMode(props: CalculusLabProps) {
  const { t, n } = useI18n();
  const initialSrc = fnSource(props.fn, "x^3/3 - x");
  const fn = useFn(initialSrc);
  const { f } = fn;
  const xKey = JSON.stringify(props.x ?? null);
  const yKey = JSON.stringify(props.y ?? null);
  const xWin = useMemo(() => toRange(props.x, [-3, 3]), [xKey]); // eslint-disable-line react-hooks/exhaustive-deps
  const yWin = useMemo(() => (Array.isArray(props.y) ? toRange(props.y, [-4, 4]) : autoY(f, xWin)), [yKey, f, xWin]); // eslint-disable-line react-hooks/exhaustive-deps
  const x0Init = clamp(toNumber(props.x0, 1.5), xWin[0], xWin[1]);
  const [x0, setX0] = useState(x0Init);
  const [hPos, setHPos] = useState(() => logSliderPosition(1, H_MAX, H_MIN));
  const [neg, setNeg] = useState(false);
  const reduced = useReducedMotion();
  const raf = useRef<number | null>(null);
  useEffect(
    () => () => {
      if (raf.current !== null) cancelAnimationFrame(raf.current);
    },
    [],
  );
  const stop = () => {
    if (raf.current !== null) cancelAnimationFrame(raf.current);
    raf.current = null;
  };
  const animate = () => {
    stop();
    if (reduced) {
      setHPos(100);
      return;
    }
    const start = performance.now();
    const from = hPos >= 99.5 ? 0 : hPos;
    const dur = 2800;
    const step = (now: number) => {
      const u = Math.min(1, (now - start) / dur);
      const e = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2;
      setHPos(from + (100 - from) * e);
      raf.current = u < 1 ? requestAnimationFrame(step) : null;
    };
    raf.current = requestAnimationFrame(step);
  };

  const h = (neg ? -1 : 1) * logSliderValue(hPos, H_MAX, H_MIN);
  const y0 = f(x0);
  const x1 = x0 + h;
  const y1 = f(x1);
  const m = (y1 - y0) / h;
  const info = useMemo(() => derivativeAt(f, x0), [f, x0]);
  const slope = info.kind === "smooth" ? info.slope : NaN;
  const table = [1, 0.1, 0.01, 0.001].map((hh) => {
    const s = neg ? -hh : hh;
    return { h: s, q: differenceQuotient(f, x0, s) };
  });
  const pretty = prettyExpr(stripLhs(fn.src));
  const reset = () => {
    stop();
    fn.setSrc(initialSrc);
    setX0(x0Init);
    setHPos(logSliderPosition(1, H_MAX, H_MIN));
    setNeg(false);
  };
  const xStr = n(x0);
  const problem =
    info.kind === "corner"
      ? t("w.calc.tan.corner", { x: xStr, l: n(info.left), r: n(info.right) })
      : info.kind === "jump"
        ? t("w.calc.tan.jump", { x: xStr })
        : info.kind === "vertical"
          ? t("w.calc.tan.vertical", { x: xStr })
          : info.kind === "undefined"
            ? t("w.calc.tan.undef", { x: xStr })
            : null;

  return (
    <div>
      <Plot
        x={xWin}
        y={yWin}
        ariaLabel={t("w.calc.tan.aria", { f: pretty, x0: fmt(x0, 3), x1: fmt(x1, 3), m: fmt(m, 3) })}
        xLabel="x"
        yLabel="y"
        above={(view) => (
          <>
            {Number.isFinite(y0) && (
              <PlotHandle x={x0} y={y0} color="var(--formal)" tag="P" label={t("w.calc.tan.pointP")} constrain={(p) => [p[0], f(p[0])]} onMove={(p) => setX0(p[0])} />
            )}
            {Number.isFinite(y1) && (
              <PlotHandle
                x={x1}
                y={y1}
                color="var(--human)"
                tag="Q"
                label={t("w.calc.tan.pointQ")}
                constrain={(p) => [p[0], f(p[0])]}
                onMove={(p) => {
                  stop();
                  const dh = p[0] - x0;
                  if (Math.abs(dh) < 1e-12) return;
                  setNeg(dh < 0);
                  setHPos(logSliderPosition(dh, H_MAX, H_MIN));
                }}
              />
            )}
          </>
        )}
      >
        {(view) => (
          <>
            {info.kind === "smooth" && <FullLine view={view} x0={x0} y0={y0} m={slope} color="var(--compute)" width={2} dash="8 5" />}
            <Curve f={f} view={view} />
            {Number.isFinite(m) && <FullLine view={view} x0={x0} y0={y0} m={m} color="var(--human)" width={2.25} />}
            {Number.isFinite(y0) && Number.isFinite(y1) && <SlopeTriangle view={view} x0={x0} y0={y0} x1={x1} y1={y1} />}
          </>
        )}
      </Plot>
      <Legend
        items={[
          { label: <span className="font-serif text-ink" dir="ltr">f(x) = {pretty}</span>, color: "var(--formal)" },
          { label: t("w.calc.tan.secant"), color: "var(--human)", width: 2.5 },
          ...(info.kind === "smooth" ? [{ label: t("w.calc.tan.tangent"), color: "var(--compute)", dash: "8 5", width: 2.5 }] : []),
        ]}
      />
      <FnError fn={fn} />

      <div className="mt-4 grid gap-x-6 gap-y-3 sm:grid-cols-2">
        <Slider label={t("w.calc.tan.x0")} value={x0} min={xWin[0]} max={xWin[1]} step={(xWin[1] - xWin[0]) / 400} onChange={setX0} display={`x₀ = ${fmt(x0, 2)}`} accent="var(--formal)" />
        <Slider
          label={t("w.calc.tan.h")}
          value={hPos}
          min={0}
          max={100}
          step={0.5}
          onChange={(v) => {
            stop();
            setHPos(v);
          }}
          display={`h = ${fmt(h, h === 0 ? 0 : Math.abs(h) < 0.01 ? 4 : 3)}`}
          accent="var(--human)"
        />
      </div>
      <div className="mt-3 flex flex-wrap items-center gap-2">
        <ModeTabs value={neg ? "neg" : "pos"} options={["pos", "neg"] as const} onChange={(v) => setNeg(v === "neg")} label={t("w.calc.tan.sign")} render={(v) => t(v === "neg" ? "w.calc.tan.hNeg" : "w.calc.tan.hPos")} />
        <button type="button" className="btn btn-sm btn-gold ms-auto" onClick={animate}>
          <Play size={14} aria-hidden="true" /> {t("w.calc.tan.animate")}
        </button>
      </div>

      <div className="mt-4 grid gap-4 md:grid-cols-[minmax(0,1.25fr)_minmax(0,1fr)]">
        <Readout>
          <p className="text-sm font-semibold text-ink-2">{t("w.calc.tan.secantSlope")}</p>
          <p className="mt-0.5 font-serif text-[1.05rem] leading-relaxed" dir="ltr">
            {Number.isFinite(y1) ? (
              <>
                <span className="text-ink-2">
                  (f(x₀ + h) − f(x₀)) / h = ({fmt(y1, 4)} − {paren(y0)}) / {paren(h)} =
                </span>{" "}
                <strong className="whitespace-nowrap">{fmt(m, 4)}</strong>
              </>
            ) : (
              <span className="font-sans text-sm text-muted">{t("w.calc.tan.qUndefined")}</span>
            )}
          </p>
          <div className="mt-3 border-t border-line pt-2">
            <p className="text-sm font-semibold text-ink-2">{t("w.calc.tan.tangentSlope")}</p>
            {info.kind === "smooth" ? (
              <>
                <p className="mt-0.5 font-serif text-[1.05rem]" dir="ltr">
                  f′({fmt(x0, 3)}) ≈ <strong>{fmt(slope, 4)}</strong>
                </p>
                <p className="text-xs text-muted">{t("w.calc.tan.numerical")}</p>
              </>
            ) : (
              <div className="mt-1">
                <Note tone="warn">{problem}</Note>
              </div>
            )}
          </div>
        </Readout>
        <div>
          <p className="text-sm font-semibold text-ink-2">{t("w.calc.tan.table")}</p>
          <table className="mt-1.5 w-full border-separate border-spacing-0 text-sm" dir="ltr">
            <thead>
              <tr className="text-muted">
                <th className="border-b border-line px-2 py-1 text-start font-serif font-normal italic">h</th>
                <th className="border-b border-line px-2 py-1 text-end font-serif font-normal">(f(x₀ + h) − f(x₀)) / h</th>
              </tr>
            </thead>
            <tbody className="font-mono">
              {table.map((r) => (
                <tr key={r.h}>
                  <td className="border-b border-line/60 px-2 py-1 text-start">{fmt(r.h, 3)}</td>
                  <td className="border-b border-line/60 px-2 py-1 text-end">{Number.isFinite(r.q) ? fmt(r.q, 5) : "—"}</td>
                </tr>
              ))}
            </tbody>
          </table>
          <p className="mt-2 text-sm text-ink-2">{t("w.calc.tan.hint")}</p>
        </div>
      </div>
      <FnEditor fn={fn} onReset={reset} />
    </div>
  );
}

function SlopeTriangle({ view, x0, y0, x1, y1 }: { view: PlotView; x0: number; y0: number; x1: number; y1: number }) {
  const X0 = view.sx(x0);
  const X1 = view.sx(x1);
  const Y0 = view.sy(y0);
  const Y1 = view.sy(y1);
  if (![X0, X1, Y0, Y1].every(Number.isFinite)) return null;
  const halo = { stroke: "var(--paper)", strokeWidth: 3, paintOrder: "stroke" as const };
  const below = Y1 < Y0; // Q above P on screen → put the h label under the leg
  return (
    <g aria-hidden="true">
      <path d={`M${X0} ${Y0}H${X1}V${Y1}`} fill="none" stroke="var(--ink-2)" strokeWidth={1.25} strokeDasharray="3 3" />
      {Math.abs(X1 - X0) > 26 && (
        <text x={(X0 + X1) / 2} y={Y0 + (below ? 15 : -7)} textAnchor="middle" fontSize={13} fontStyle="italic" fill="var(--ink-2)" className="font-serif" {...halo}>
          h
        </text>
      )}
      {Math.abs(Y1 - Y0) > 22 && (
        <text x={X1 + (X1 >= X0 ? 6 : -6)} y={(Y0 + Y1) / 2 + 4} textAnchor={X1 >= X0 ? "start" : "end"} fontSize={13} fontStyle="italic" fill="var(--ink-2)" className="font-serif" {...halo}>
          Δy
        </text>
      )}
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Mode 2: Riemann sums
 * ------------------------------------------------------------------------- */

const RULE_SYMBOL: Record<RiemannMethod, string> = { left: "L", right: "R", midpoint: "M", trapezoid: "T" };

function RiemannMode(props: CalculusLabProps) {
  const { t, n: num } = useI18n();
  const defaults = props.fn === undefined && props.interval === undefined && props.exact === undefined;
  const initialSrc = fnSource(props.fn, "sin(x)");
  const initialAB = useMemo(() => toRange(props.interval, [0, (3 * Math.PI) / 2]), [JSON.stringify(props.interval ?? null)]); // eslint-disable-line react-hooks/exhaustive-deps
  const exactGiven = defaults ? 1 : toNumber(props.exact, NaN);
  const fn = useFn(initialSrc);
  const { f } = fn;
  const [ab, setAb] = useState<Range>(initialAB);
  const [a, b] = ab;
  const [n, setN] = useState(() => intProp(props.n, 1, 200, 6));
  const [method, setMethod] = useState<RiemannMethod>(() => (typeof props.method === "string" && (RIEMANN_METHODS as readonly string[]).includes(props.method) ? (props.method as RiemannMethod) : "left"));
  const exactUsable = Number.isFinite(exactGiven) && fn.src === initialSrc && a === initialAB[0] && b === initialAB[1];

  const xKey = JSON.stringify(props.x ?? null);
  const yKey = JSON.stringify(props.y ?? null);
  const xWin = useMemo((): Range => {
    if (Array.isArray(props.x)) return toRange(props.x, [a - 1, b + 1]);
    const pad = (b - a) * 0.12;
    return [a - pad, b + pad];
  }, [xKey, a, b]); // eslint-disable-line react-hooks/exhaustive-deps
  const yWin = useMemo(() => (Array.isArray(props.y) ? toRange(props.y, [-2, 2]) : autoY(f, xWin)), [yKey, f, xWin]); // eslint-disable-line react-hooks/exhaustive-deps

  const result = useMemo(() => riemannSum(f, a, b, n, method), [f, a, b, n, method]);
  const all = useMemo(() => RIEMANN_METHODS.map((m) => ({ m, sum: riemannSum(f, a, b, n, m).sum })), [f, a, b, n]);
  const numeric = useMemo(() => integrate(f, a, b, 1e-11), [f, a, b]);
  const ref = exactUsable ? exactGiven : numeric;
  const pretty = prettyExpr(stripLhs(fn.src));
  const hatch = `calc-hatch-${useId().replace(/[^a-zA-Z0-9_-]/g, "")}`;
  const hasNegative = result.pieces.some((p) => p.h0 < 0 || p.h1 < 0);
  const reset = () => {
    fn.setSrc(initialSrc);
    setAb(initialAB);
    setN(intProp(props.n, 1, 200, 6));
  };
  const sym = (m: RiemannMethod) => (
    <span className="font-serif italic">
      {RULE_SYMBOL[m]}
      <sub className="not-italic">{n}</sub>
    </span>
  );

  return (
    <div>
      <div className="mb-3">
        <ModeTabs value={method} options={RIEMANN_METHODS} onChange={setMethod} label={t("w.calc.riem.rule")} render={(m) => t(`w.calc.riem.method.${m}`)} />
      </div>
      <Plot
        x={xWin}
        y={yWin}
        xLabel="x"
        yLabel="y"
        ariaLabel={t("w.calc.riem.aria", { n, rule: t(`w.calc.riem.method.${method}`), f: pretty, a: fmtPi(a), b: fmtPi(b), sum: fmt(result.sum, 4) })}
      >
        {(view) => (
          <>
            <Strips view={view} pieces={result.pieces} hatch={hatch} />
            <Curve f={f} view={view} />
            {n <= 50 &&
              result.pieces.flatMap((p, i) =>
                p.samples.map((xs, k) => {
                  const ys = f(xs);
                  return Number.isFinite(ys) ? <circle key={`${i}-${k}`} cx={view.sx(xs)} cy={view.sy(ys)} r={n <= 20 ? 3.5 : 2.5} fill="var(--card)" stroke="var(--ink)" strokeWidth={1.5} /> : null;
                }),
              )}
          </>
        )}
      </Plot>
      <Legend
        items={[
          { label: <span className="font-serif text-ink" dir="ltr">f(x) = {pretty}</span>, color: "var(--formal)" },
          ...(hasNegative ? [{ label: t("w.calc.riem.negative"), color: "var(--human)", dash: "3 3", width: 2 }] : []),
        ]}
      />
      <FnError fn={fn} />

      <div className="mt-4 flex flex-wrap items-end gap-3">
        <Slider className="min-w-48 flex-1" label={t("w.calc.riem.n")} value={n} min={1} max={200} step={1} onChange={(v) => setN(Math.round(v))} display={`n = ${n}`} accent="var(--compute)" />
        <div className="flex gap-2">
          <button type="button" className="btn btn-sm btn-ghost" disabled={n <= 1} onClick={() => setN((v) => Math.max(1, Math.round(v / 2)))}>
            {t("w.calc.riem.half")}
          </button>
          <button type="button" className="btn btn-sm btn-ghost" disabled={n >= 200} onClick={() => setN((v) => Math.min(200, v * 2))}>
            {t("w.calc.riem.double")}
          </button>
        </div>
      </div>

      <div className="mt-4 grid gap-4 md:grid-cols-[minmax(0,1fr)_minmax(0,1.1fr)]">
        <Readout>
          {!result.ok ? (
            <p className="text-sm">{t("w.calc.riem.undefined")}</p>
          ) : (
            <>
              <p className="text-sm font-semibold text-ink-2">{t("w.calc.riem.sumLabel", { rule: t(`w.calc.riem.method.${method}`), n: num(n) })}</p>
              <p className="font-serif text-2xl" dir="ltr">
                {sym(method)} = <strong>{fmt(result.sum, 6)}</strong>
              </p>
              <p className="mt-2 text-sm font-semibold text-ink-2">{exactUsable ? t("w.calc.riem.exact") : t("w.calc.riem.reference")}</p>
              <p className="font-serif text-lg" dir="ltr">
                ∫<sub>{fmtPi(a)}</sub>
                <sup>{fmtPi(b)}</sup> f(x) dx {exactUsable ? "=" : "≈"} {Number.isFinite(ref) ? fmt(ref, 6) : "—"}
              </p>
              <p className="mt-2 text-sm font-semibold text-ink-2">{t("w.calc.riem.error")}</p>
              <p className="font-mono text-base" dir="ltr">
                {Number.isFinite(ref) ? fmt(result.sum - ref, 6) : "—"}
              </p>
            </>
          )}
        </Readout>
        <div>
          <p className="text-sm font-semibold text-ink-2">{t("w.calc.riem.compare", { n: num(n) })}</p>
          <table className="mt-1.5 w-full border-separate border-spacing-0 text-sm">
            <thead>
              <tr className="text-muted">
                <th className="border-b border-line px-2 py-1 text-start font-semibold">{t("w.calc.riem.colRule")}</th>
                <th className="border-b border-line px-2 py-1 text-end font-semibold">{t("w.calc.riem.colSum")}</th>
                <th className="border-b border-line px-2 py-1 text-end font-semibold">{t("w.calc.riem.colError")}</th>
              </tr>
            </thead>
            <tbody>
              {all.map(({ m, sum }) => (
                <tr key={m} className={m === method ? "bg-gold-soft" : ""} aria-current={m === method ? "true" : undefined}>
                  <td className={`border-b border-line/60 px-2 py-1 ${m === method ? "font-semibold text-ink" : "text-ink-2"}`}>
                    {t(`w.calc.riem.method.${m}`)} <span dir="ltr">({sym(m)})</span>
                  </td>
                  <td className="border-b border-line/60 px-2 py-1 text-end font-mono" dir="ltr">
                    {Number.isFinite(sum) ? fmt(sum, 6) : "—"}
                  </td>
                  <td className="border-b border-line/60 px-2 py-1 text-end font-mono" dir="ltr">
                    {Number.isFinite(sum) && Number.isFinite(ref) ? fmt(sum - ref, 6) : "—"}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          <p className="mt-2 text-sm text-ink-2">{t("w.calc.riem.hint")}</p>
        </div>
      </div>
      <FnEditor fn={fn} onReset={reset}>
        <NumberField label={t("w.calc.riem.a")} value={a} onChange={(v) => v < b && setAb([v, b])} />
        <NumberField label={t("w.calc.riem.b")} value={b} onChange={(v) => v > a && setAb([a, v])} />
      </FnEditor>
    </div>
  );
}

function Strips({ view, pieces, hatch }: { view: PlotView; pieces: RiemannPiece[]; hatch: string }) {
  const span = view.y[1] - view.y[0];
  const lim = (v: number) => clamp(v, view.y[0] - span, view.y[1] + span);
  const Y0 = view.sy(0);
  let d = "";
  for (const p of pieces) {
    if (!Number.isFinite(p.h0) || !Number.isFinite(p.h1)) continue;
    const xa = view.sx(p.x0).toFixed(2);
    const xb = view.sx(p.x1).toFixed(2);
    d += `M${xa} ${Y0.toFixed(2)}L${xa} ${view.sy(lim(p.h0)).toFixed(2)}L${xb} ${view.sy(lim(p.h1)).toFixed(2)}L${xb} ${Y0.toFixed(2)}Z`;
  }
  const px = pieces.length ? Math.abs(view.sx(pieces[0].x1) - view.sx(pieces[0].x0)) : 10;
  const sw = px < 5 ? 0.5 : 1.25;
  const yAxis = clamp(Y0, 0, view.H);
  return (
    <g aria-hidden="true">
      <defs>
        <pattern id={hatch} width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
          <line x1="0" y1="0" x2="0" y2="7" stroke="var(--human)" strokeWidth="2" strokeOpacity="0.5" />
        </pattern>
        <clipPath id={`${hatch}-up`}>
          <rect x={0} y={0} width={view.W} height={yAxis} />
        </clipPath>
        <clipPath id={`${hatch}-dn`}>
          <rect x={0} y={yAxis} width={view.W} height={Math.max(0, view.H - yAxis)} />
        </clipPath>
      </defs>
      <g clipPath={`url(#${hatch}-up)`}>
        <path d={d} fill="var(--compute)" fillOpacity={0.2} stroke="var(--compute)" strokeWidth={sw} strokeLinejoin="round" />
      </g>
      <g clipPath={`url(#${hatch}-dn)`}>
        <path d={d} fill="var(--human)" fillOpacity={0.08} />
        <path d={d} fill={`url(#${hatch})`} stroke="var(--human)" strokeWidth={sw} strokeLinejoin="round" />
      </g>
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Mode 3: Taylor polynomials
 * ------------------------------------------------------------------------- */

const TAYLOR_WINDOWS: Record<TaylorId, { x: Range; y: Range; trace: number }> = {
  sin: { x: [-2 * Math.PI, 2 * Math.PI], y: [-3, 3], trace: 2 },
  cos: { x: [-2 * Math.PI, 2 * Math.PI], y: [-3, 3], trace: 2 },
  exp: { x: [-4, 3], y: [-3, 12], trace: 2 },
  ln1p: { x: [-1.5, 3], y: [-4, 3], trace: 0.5 },
  geometric: { x: [-2, 2], y: [-4, 8], trace: 0.5 },
  atan: { x: [-3, 3], y: [-2.5, 2.5], trace: 0.8 },
};

function TaylorMode(props: CalculusLabProps) {
  const { t } = useI18n();
  const initialPreset: TaylorId = isTaylor(props.preset) ? props.preset : "sin";
  const initialDeg = intProp(props.degree, 0, 20, 3);
  const [preset, setPreset] = useState<TaylorId>(initialPreset);
  const [deg, setDeg] = useState(initialDeg);
  const p = TAYLOR[preset];
  const win = TAYLOR_WINDOWS[preset];
  const xKey = JSON.stringify(props.x ?? null);
  const yKey = JSON.stringify(props.y ?? null);
  const xWin = useMemo(() => toRange(props.x, win.x), [xKey, preset]); // eslint-disable-line react-hooks/exhaustive-deps
  const yWin = useMemo(() => toRange(props.y, win.y), [yKey, preset]); // eslint-disable-line react-hooks/exhaustive-deps
  const [trace, setTrace] = useState<number | null>(null);
  const tx = clamp(trace ?? win.trace, xWin[0], xWin[1]);
  const Tn = useMemo(() => taylorPolynomial(p, deg), [p, deg]);
  const fx = p.f(tx);
  const tnx = Tn(tx);
  const inside = inConvergence(p, tx);
  const choose = (id: TaylorId) => {
    setPreset(id);
    setTrace(null);
  };

  return (
    <div>
      <div className="mb-3">
        <ModeTabs value={preset} options={TAYLOR_IDS} onChange={choose} label={t("w.calc.taylor.fn")} render={(id) => <span className="font-serif" dir="ltr">{TAYLOR[id].label}</span>} />
      </div>
      <Plot
        x={xWin}
        y={yWin}
        xLabel="x"
        yLabel="y"
        ariaLabel={t("w.calc.taylor.aria", { f: p.label, n: deg })}
        onHover={(q) => q && setTrace(clamp(q[0], xWin[0], xWin[1]))}
        readout={<span>x = {fmt(tx, 3)}</span>}
        above={(view) => (p.conv ? <ConvergenceMarks view={view} conv={p.conv} label={t("w.calc.taylor.interval")} /> : null)}
      >
        {(view) => (
          <>
            {p.conv && (
              <rect
                x={view.sx(p.conv.lo)}
                y={0}
                width={Math.max(0, view.sx(p.conv.hi) - view.sx(p.conv.lo))}
                height={view.H}
                fill="var(--sky-soft)"
                fillOpacity={0.5}
                aria-hidden="true"
              />
            )}
            <Curve f={p.f} view={view} color="var(--formal)" width={2.75} />
            <Curve f={Tn} view={view} color="var(--human)" width={2.5} dash="9 5" />
            <line x1={view.sx(tx)} x2={view.sx(tx)} y1={0} y2={view.H} stroke="var(--muted)" strokeDasharray="3 4" aria-hidden="true" />
            {Number.isFinite(fx) && <circle cx={view.sx(tx)} cy={view.sy(fx)} r={5} fill="var(--formal)" stroke="var(--card)" strokeWidth={2} />}
            {Number.isFinite(tnx) && <circle cx={view.sx(tx)} cy={view.sy(tnx)} r={5} fill="var(--human)" stroke="var(--card)" strokeWidth={2} />}
          </>
        )}
      </Plot>
      <Legend
        items={[
          { label: <span className="font-serif text-ink" dir="ltr">f(x) = {p.label}</span>, color: "var(--formal)" },
          {
            label: (
              <span>
                {t("w.calc.taylor.poly")}{" "}
                <span className="font-serif italic text-ink" dir="ltr">
                  T<sub className="not-italic">{deg}</sub>
                </span>
              </span>
            ),
            color: "var(--human)",
            dash: "9 5",
          },
          ...(p.conv ? [{ label: t("w.calc.taylor.interval"), color: "var(--sky)", dash: "4 3", width: 2 }] : []),
        ]}
      />
      <div className="mt-4 grid gap-x-6 gap-y-3 sm:grid-cols-2">
        <Slider label={t("w.calc.taylor.degree")} value={deg} min={0} max={20} step={1} onChange={(v) => setDeg(Math.round(v))} display={`n = ${deg}`} accent="var(--human)" />
        <Slider label={t("w.calc.taylor.trace")} value={tx} min={xWin[0]} max={xWin[1]} step={(xWin[1] - xWin[0]) / 400} onChange={setTrace} display={`x = ${fmt(tx, 2)}`} accent="var(--sky)" />
      </div>
      <div className="mt-4 grid gap-4 md:grid-cols-[minmax(0,1.3fr)_minmax(0,1fr)]">
        <div className="space-y-3">
          <p className="break-words rounded-xl bg-paper-2 px-4 py-3 font-serif text-lg leading-relaxed text-ink" dir="ltr">
            <span className="italic">T</span>
            <sub>{deg}</sub>(<span className="italic">x</span>) = {taylorFormula(p, deg)}
          </p>
          <Note tone="info">{p.conv ? t(`w.calc.taylor.conv.${preset}`) : t("w.calc.taylor.convAll", { f: p.label })}</Note>
        </div>
        <Readout className="font-serif">
          <ul className="space-y-0.5" dir="ltr">
            <li className="flex items-center gap-2">
              <LegendSwatch color="var(--formal)" width={2.5} />
              f({fmt(tx, 3)}) = {Number.isFinite(fx) ? fmt(fx, 5) : <span className="font-sans text-sm text-muted">{t("w.plot.undefined")}</span>}
            </li>
            <li className="flex items-center gap-2">
              <LegendSwatch color="var(--human)" dash="9 5" width={2.5} />
              <span>
                <i>T</i>
                <sub>{deg}</sub>({fmt(tx, 3)}) = {fmt(tnx, 5)}
              </span>
            </li>
            <li className="ps-9 text-ink-2">
              |f − <i>T</i>
              <sub>{deg}</sub>| = {Number.isFinite(fx) ? fmt(Math.abs(fx - tnx), 5) : "—"}
            </li>
          </ul>
          {!inside && <p className="mt-1 font-sans text-sm text-warn">{t("w.calc.taylor.outside")}</p>}
        </Readout>
      </div>
      <div className="mt-4 border-t border-line pt-3">
        <button
          type="button"
          className="btn btn-sm btn-ghost"
          onClick={() => {
            setPreset(initialPreset);
            setDeg(initialDeg);
            setTrace(null);
          }}
        >
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>
    </div>
  );
}

function ConvergenceMarks({ view, conv, label }: { view: PlotView; conv: { lo: number; hi: number; loClosed: boolean; hiClosed: boolean }; label: string }) {
  const Y = clamp(view.sy(0), 6, view.H - 6);
  const xs = [
    { x: conv.lo, closed: conv.loClosed },
    { x: conv.hi, closed: conv.hiClosed },
  ];
  const L = view.sx(conv.lo);
  const R = view.sx(conv.hi);
  return (
    <g aria-hidden="true">
      {xs.map(({ x }, i) => (
        <line key={`l${i}`} x1={view.sx(x)} x2={view.sx(x)} y1={0} y2={view.H} stroke="var(--sky)" strokeOpacity={0.7} strokeDasharray="4 3" />
      ))}
      {R - L > 60 && (
        <text x={(L + R) / 2} y={view.H - 8} textAnchor="middle" fontSize={11} fill="var(--sky-ink)" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
          {label}
        </text>
      )}
      {xs.map(({ x, closed }, i) => (
        <circle key={`c${i}`} cx={view.sx(x)} cy={Y} r={4.5} fill={closed ? "var(--sky)" : "var(--paper)"} stroke="var(--sky)" strokeWidth={2} />
      ))}
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Mode 4: the ε–δ game
 * ------------------------------------------------------------------------- */

const D_MAX = 2;
const D_MIN = 0.001;
const EPS_CHOICES = [1, 0.5, 0.2, 0.1, 0.05, 0.01];
const JUMP = { fn: "x/2 + sign(x)", a: 0, L: 1 };

function EpsDeltaMode(props: CalculusLabProps) {
  const { t, n } = useI18n();
  const base = useMemo(() => {
    const fnSrc = fnSource(props.fn, "x^2");
    const a = toNumber(props.a, 1);
    const c = compileExpr(stripLhs(fnSrc), ["x"]);
    const fa = c.ok ? c.fn({ x: a }) : NaN;
    const L = toNumber(props.L, Number.isFinite(fa) ? Math.round(fa * 1e6) / 1e6 : 0);
    return { fn: fnSrc, a, L };
  }, [props.fn, props.a, props.L]);
  const startJump = props.preset === "jump";
  const start = startJump ? JUMP : base;
  const fn = useFn(start.fn);
  const { f } = fn;
  const [jump, setJump] = useState(startJump);
  const [a, setA] = useState(start.a);
  const [L, setL] = useState(start.L);
  const epsInit = clamp(toNumber(props.epsilon, 0.5), 1e-4, 5);
  const epsList = useMemo(() => [...new Set([...EPS_CHOICES, epsInit])].sort((p, q) => q - p), [epsInit]);
  const [eps, setEps] = useState(epsInit);
  const [dPos, setDPos] = useState(() => logSliderPosition(0.5, D_MAX, D_MIN));
  const [revealed, setRevealed] = useState(false);
  const [zoom, setZoom] = useState(false);
  const delta = logSliderValue(dPos, D_MAX, D_MIN);
  const L0 = jump ? 0 : base.L;

  const check = useMemo(() => checkDelta(f, a, L, eps, delta), [f, a, L, eps, delta]);
  const best = useMemo(() => (revealed ? largestDelta(f, a, L, eps, D_MAX) : undefined), [revealed, f, a, L, eps]);

  const xKey = JSON.stringify(props.x ?? null);
  const yKey = JSON.stringify(props.y ?? null);
  const baseX = useMemo(() => toRange(jump ? undefined : props.x, [a - 2, a + 2]), [xKey, a, jump]); // eslint-disable-line react-hooks/exhaustive-deps
  const baseY = useMemo((): Range => {
    if (Array.isArray(props.y) && !jump) return toRange(props.y, [L - 2, L + 2]);
    // Keep the picture focused on the band: at most 4 units above and below L.
    const r = autoY(f, baseX, [L - 1.5, L + 1.5]);
    return [Math.max(r[0], Math.floor(L - 4)), Math.min(r[1], Math.ceil(L + 4))];
  }, [yKey, f, baseX, jump, L0]); // eslint-disable-line react-hooks/exhaustive-deps
  const xWin: Range = zoom ? [a - 2.5 * delta, a + 2.5 * delta] : baseX;
  const yWin: Range = zoom ? [L - 3 * eps, L + 3 * eps] : baseY;

  const pretty = prettyExpr(stripLhs(fn.src));
  const pn = (v: number) => (Math.abs(v) >= 0.0005 || v === 0 ? n(v) : fmt(v, 6));
  const clipId = `calc-eps-${useId().replace(/[^a-zA-Z0-9_-]/g, "")}`;
  const pickEps = (e: number) => {
    setEps(e);
    setRevealed(false);
  };
  const changeL = (v: number) => {
    setL(v);
    setRevealed(false);
  };
  const toggleJump = () => {
    const next = !jump;
    const s = next ? JUMP : base;
    setJump(next);
    fn.setSrc(s.fn);
    setA(s.a);
    setL(s.L);
    setRevealed(false);
  };
  const reset = () => {
    setJump(startJump);
    fn.setSrc(start.fn);
    setA(start.a);
    setL(start.L);
    setEps(epsInit);
    setDPos(logSliderPosition(0.5, D_MAX, D_MIN));
    setRevealed(false);
    setZoom(false);
  };
  const lRange: Range = [Math.floor(L0 - 2), Math.ceil(L0 + 2)];

  return (
    <div>
      <p className="mb-3 rounded-xl bg-paper-2 px-4 py-2.5 text-sm text-ink-2">
        <span className="font-semibold text-ink">{t("w.calc.eps.claim")}</span>{" "}
        <span className="font-serif text-base text-ink" dir="ltr">
          lim<sub>x→{fmt(a, 3)}</sub> ({pretty}) = {fmt(L, 3)}
        </span>
        <span className="mt-1 block">{t("w.calc.eps.goal")}</span>
      </p>
      <Plot
        x={xWin}
        y={yWin}
        xLabel="x"
        yLabel="y"
        ariaLabel={t("w.calc.eps.aria", { f: pretty, a: fmt(a, 3), lo: fmt(L - eps, 3), hi: fmt(L + eps, 3), left: fmt(a - delta, 3), right: fmt(a + delta, 3) })}
        above={(view) => <BandLabels view={view} a={a} L={L} eps={eps} delta={delta} />}
      >
        {(view) => {
          const top = clamp(view.sy(L + eps), 0, view.H);
          const bot = clamp(view.sy(L - eps), 0, view.H);
          const left = clamp(view.sx(a - delta), 0, view.W);
          const right = clamp(view.sx(a + delta), 0, view.W);
          const bad = check.badX;
          const fb = bad === null ? NaN : f(bad);
          return (
            <>
              <rect x={left} y={0} width={Math.max(0, right - left)} height={view.H} fill="var(--sky-soft)" fillOpacity={0.5} aria-hidden="true" />
              <rect x={0} y={top} width={view.W} height={Math.max(0, bot - top)} fill="var(--compute)" fillOpacity={0.14} aria-hidden="true" />
              <g aria-hidden="true" strokeDasharray="5 4" strokeWidth={1.25}>
                <line x1={left} x2={left} y1={0} y2={view.H} stroke="var(--sky)" />
                <line x1={right} x2={right} y1={0} y2={view.H} stroke="var(--sky)" />
                <line x1={0} x2={view.W} y1={top} y2={top} stroke="var(--compute)" />
                <line x1={0} x2={view.W} y1={bot} y2={bot} stroke="var(--compute)" />
              </g>
              <clipPath id={clipId}>
                <rect x={left} y={0} width={Math.max(0, right - left)} height={top} />
                <rect x={left} y={bot} width={Math.max(0, right - left)} height={Math.max(0, view.H - bot)} />
              </clipPath>
              <Curve f={f} view={view} />
              <Curve f={f} view={view} color="var(--bad)" width={5} dash="7 4" clipPath={`url(#${clipId})`} />
              <circle cx={view.sx(a)} cy={view.sy(L)} r={5} fill="var(--paper)" stroke="var(--ink)" strokeWidth={2} />
              {bad !== null && Number.isFinite(fb) && <circle cx={view.sx(bad)} cy={view.sy(fb)} r={7} fill="none" stroke="var(--bad)" strokeWidth={2.5} />}
            </>
          );
        }}
      </Plot>
      <Legend
        items={[
          { label: <span className="font-serif text-ink" dir="ltr">f(x) = {pretty}</span>, color: "var(--formal)" },
          { label: t("w.calc.eps.band"), color: "var(--compute)", dash: "5 4", width: 2 },
          { label: t("w.calc.eps.window"), color: "var(--sky)", dash: "5 4", width: 2 },
          { label: t("w.calc.eps.bad"), color: "var(--bad)", dash: "7 4", width: 4 },
        ]}
      />
      <FnError fn={fn} />

      <div className="mt-4 space-y-3">
        <div>
          <p className="text-sm font-semibold text-ink-2">{t("w.calc.eps.epsilon")}</p>
          <div className="mt-1.5" dir="ltr">
            <ModeTabs value={String(eps)} options={epsList.map(String)} onChange={(v) => pickEps(Number(v))} label={t("w.calc.eps.epsilon")} render={(v) => `ε = ${fmt(Number(v), 4)}`} />
          </div>
        </div>
        <div className="grid gap-x-6 gap-y-3 sm:grid-cols-2">
          <div>
            <Slider label={t("w.calc.eps.delta")} value={dPos} min={0} max={100} step={0.25} onChange={setDPos} display={`δ = ${fmt(delta, delta < 0.01 ? 4 : 3)}`} accent="var(--sky)" />
            <NumberField className="mt-2" label="δ =" value={Number(delta.toPrecision(4))} onChange={(v) => v > 0 && setDPos(logSliderPosition(v, D_MAX, D_MIN))} />
          </div>
          <Slider label={t("w.calc.eps.L")} value={L} min={lRange[0]} max={lRange[1]} step={0.05} onChange={changeL} display={`L = ${fmt(L, 3)}`} accent="var(--compute)" />
        </div>
        <div className="flex flex-wrap gap-2">
          <button type="button" className="btn btn-sm btn-ghost" onClick={() => setRevealed(true)} disabled={revealed}>
            <Search size={14} aria-hidden="true" /> {t("w.calc.eps.showBest")}
          </button>
          <button type="button" className={`btn btn-sm ${zoom ? "btn-primary" : "btn-ghost"}`} aria-pressed={zoom} onClick={() => setZoom((z) => !z)}>
            <ZoomIn size={14} aria-hidden="true" /> {t("w.calc.eps.zoom")}
          </button>
          <button type="button" className="btn btn-sm btn-gold" onClick={toggleJump}>
            {jump ? t("w.calc.eps.back") : t("w.calc.eps.jump")}
          </button>
        </div>
      </div>

      <div className="mt-4 space-y-2" aria-live="polite">
        {check.checked === 0 ? (
          <Note tone="warn">{t("w.plot.nothing")}</Note>
        ) : check.ok ? (
          <Note tone="good">
            <span className="flex items-start gap-2">
              <Check size={16} className="mt-0.5 shrink-0 text-good" aria-hidden="true" /> {t("w.calc.eps.works")}
            </span>
          </Note>
        ) : (
          <Note tone="bad">
            <span className="flex items-start gap-2">
              <X size={16} className="mt-0.5 shrink-0 text-bad" aria-hidden="true" />
              {t("w.calc.eps.fails", { x: pn(check.badX ?? a), gap: pn(check.gap) })}
            </span>
          </Note>
        )}
        <p className="text-xs text-muted">{t("w.calc.eps.evidence", { count: n(check.checked) })}</p>
        {revealed && best !== undefined && (
          <Note tone="info">
            <span className="flex flex-wrap items-center gap-x-3 gap-y-1.5">
              <span>{best === null ? t("w.calc.eps.noDelta", { L: n(L) }) : best >= D_MAX ? t("w.calc.eps.allWindow", { d: n(D_MAX) }) : t("w.calc.eps.best", { d: pn(best) })}</span>
              {best !== null && (
                <button type="button" className="btn btn-sm btn-ghost" onClick={() => setDPos(logSliderPosition(Math.max(D_MIN, Math.min(D_MAX, best * 0.99)), D_MAX, D_MIN))}>
                  {t("w.calc.eps.useBest")}
                </button>
              )}
            </span>
          </Note>
        )}
        {jump && <Note tone="warn">{t("w.calc.eps.jumpNote")}</Note>}
      </div>
      <FnEditor fn={fn} onReset={reset}>
        <NumberField label={t("w.calc.eps.aField")} value={a} onChange={(v) => setA(v)} />
      </FnEditor>
    </div>
  );
}

function BandLabels({ view, a, L, eps, delta }: { view: PlotView; a: number; L: number; eps: number; delta: number }) {
  const halo = { stroke: "var(--paper)", strokeWidth: 3, paintOrder: "stroke" as const };
  const top = view.sy(L + eps);
  const bot = view.sy(L - eps);
  const left = view.sx(a - delta);
  const right = view.sx(a + delta);
  const thin = bot - top < 26;
  const narrow = right - left < 64;
  const yOk = (y: number) => y > 10 && y < view.H - 4;
  const xOk = (x: number) => x > 14 && x < view.W - 14;
  return (
    <g aria-hidden="true" fontSize={11} className="font-serif" fontStyle="italic">
      {thin
        ? yOk((top + bot) / 2) && (
            <text x={view.W - 6} y={(top + bot) / 2 - 6} textAnchor="end" fill="var(--compute)" {...halo}>
              L ± ε
            </text>
          )
        : (
            <>
              {yOk(top) && (
                <text x={view.W - 6} y={top - 4} textAnchor="end" fill="var(--compute)" {...halo}>
                  L + ε
                </text>
              )}
              {yOk(bot + 12) && (
                <text x={view.W - 6} y={bot + 13} textAnchor="end" fill="var(--compute)" {...halo}>
                  L − ε
                </text>
              )}
            </>
          )}
      {narrow
        ? xOk((left + right) / 2) && (
            <text x={(left + right) / 2} y={view.H - 6} textAnchor="middle" fill="var(--sky-ink)" {...halo}>
              a ± δ
            </text>
          )
        : (
            <>
              {xOk(left) && (
                <text x={left} y={view.H - 6} textAnchor="middle" fill="var(--sky-ink)" {...halo}>
                  a − δ
                </text>
              )}
              {xOk(right) && (
                <text x={right} y={view.H - 6} textAnchor="middle" fill="var(--sky-ink)" {...halo}>
                  a + δ
                </text>
              )}
            </>
          )}
    </g>
  );
}
