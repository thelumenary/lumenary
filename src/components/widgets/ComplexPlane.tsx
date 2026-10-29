"use client";

import { Pause, Play, RotateCcw } from "lucide-react";
import { useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { toNumber } from "./lib/expr";
import { clamp, fmt, pathD, sampleParametric, type Pt, type Range } from "./lib/plot-core";
import { DataArrow, Plot, PlotHandle, arrowPath, type PlotView } from "./lib/plot-svg";
import { LegendSwatch, ModeTabs, NumberField, Readout, Slider, useReducedMotion } from "./lib/plot-ui";
import {
  CURVES,
  CURVE_IDS,
  MAPS,
  MAP_IDS,
  abs,
  add,
  arg,
  conj,
  curvePolygon,
  div,
  fmtAngle,
  fmtC,
  gridLines,
  imageAngle,
  imageCurve,
  isFiniteC,
  mul,
  nthRoots,
  probeStatus,
  sub,
  toComplex,
  toCurveId,
  toMapId,
  winding,
  windingByAngle,
  windingInteger,
  windingRuns,
  type C,
  type CurveId,
  type GridKind,
  type MapId,
  type MapSpec,
} from "./lib/plot-complex";

export type ComplexMode = "arithmetic" | "roots" | "map" | "winding";
const MODES: readonly ComplexMode[] = ["arithmetic", "roots", "map", "winding"];
export type ComplexOp = "sum" | "product" | "quotient" | "conjugate";
const OPS: readonly ComplexOp[] = ["sum", "product", "quotient", "conjugate"];
const MAP_KEY: Record<MapId, string> = { "z^2": "square", "z^3": "cube", "1/z": "inverse", exp: "exp", mobius: "mobius", joukowski: "joukowski" };
const SUBSCRIPT = "₀₁₂₃₄₅₆₇₈₉";
const sub_ = (k: number) => String(k).replace(/\d/g, (d) => SUBSCRIPT[Number(d)]);
const POLY_N = 720;

const COLOR_Z = "var(--formal)";
const COLOR_W = "var(--human)";
const COLOR_R = "var(--compute)";
const COLOR_C = "var(--gold)";

interface ComplexPlaneProps {
  mode?: string;
  modes?: unknown;
  z?: unknown;
  w?: unknown;
  n?: unknown;
  op?: string;
  map?: unknown;
  grid?: string;
  curve?: unknown;
  range?: unknown;
  title?: string;
  subtitle?: string;
}

/**
 * The complex plane: arithmetic as geometry, n-th roots as regular polygons,
 * complex functions as conformal maps of grids, and winding numbers.
 */
export function ComplexPlane(props: ComplexPlaneProps) {
  const { t } = useI18n();
  const modeGiven = MODES.includes(props.mode as ComplexMode);
  const offered = useMemo(() => {
    const list = Array.isArray(props.modes) ? MODES.filter((m) => (props.modes as unknown[]).includes(m)) : [];
    if (list.length) return list;
    return modeGiven ? [props.mode as ComplexMode] : [...MODES];
  }, [props.modes, props.mode, modeGiven]);
  const [mode, setMode] = useState<ComplexMode>(() => (modeGiven && offered.includes(props.mode as ComplexMode) ? (props.mode as ComplexMode) : offered[0]));
  const R = clamp(toNumber(props.range, 3), 1, 20);

  // State lives here so switching tabs keeps each exploration where the reader left it.
  const [z, setZ] = useState<C>(() => toComplex(props.z, [1.5, 0.5]));
  const [w, setW] = useState<C>(() => toComplex(props.w, [0.5, 1]));
  const [op, setOp] = useState<ComplexOp>(OPS.includes(props.op as ComplexOp) ? (props.op as ComplexOp) : "sum");
  const [c, setC] = useState<C>(() => toComplex(props.z, [1, 0]));
  const [n, setN] = useState(() => clamp(Math.round(toNumber(props.n, 5)), 2, 12));
  const initialMap = toMapId(props.map);
  const [mapId, setMapId] = useState<MapId>(initialMap);
  const [grid, setGrid] = useState<GridKind>(props.grid === "cartesian" || props.grid === "polar" ? props.grid : MAPS[initialMap].defaultGrid);
  const [probe, setProbe] = useState<C>(() => (props.z !== undefined && modeGiven && props.mode === "map" ? toComplex(props.z, MAPS[initialMap].probe) : MAPS[initialMap].probe));
  const [curve, setCurve] = useState<CurveId>(() => toCurveId(props.curve));
  const [p, setP] = useState<C>(() => (props.z !== undefined && props.mode === "winding" ? toComplex(props.z, [0, 0]) : [0, 0]));

  const chooseMap = (id: MapId) => {
    setMapId(id);
    if (props.grid !== "cartesian" && props.grid !== "polar") setGrid(MAPS[id].defaultGrid);
    setProbe(MAPS[id].probe);
  };

  return (
    <WidgetFrame title={props.title ?? t(`w.complex.title.${mode}`)} subtitle={props.subtitle ?? t(`w.complex.subtitle.${mode}`)}>
      {offered.length > 1 && (
        <div className="mb-4">
          <ModeTabs value={mode} options={offered} onChange={setMode} label={t("w.complex.modes")} render={(m) => t(`w.complex.mode.${m}`)} />
        </div>
      )}
      {mode === "arithmetic" && <ArithmeticView z={z} w={w} setZ={setZ} setW={setW} op={op} setOp={setOp} R={R} />}
      {mode === "roots" && <RootsView c={c} setC={setC} n={n} setN={setN} R={R} />}
      {mode === "map" && <MapView id={mapId} setId={chooseMap} grid={grid} setGrid={setGrid} probe={probe} setProbe={setProbe} />}
      {mode === "winding" && <WindingView curve={curve} setCurve={setCurve} p={p} setP={setP} R={R} />}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------------------
 * Shared pieces
 * ------------------------------------------------------------------------- */

const snap = (step: number) => (q: Pt): Pt => [Math.round(q[0] / step) * step, Math.round(q[1] / step) * step];

function MathLabel({ view, at, text, color = "var(--ink)", dx = 8, dy = -8, anchor = "start", size = 14 }: { view: PlotView; at: C; text: string; color?: string; dx?: number; dy?: number; anchor?: "start" | "middle" | "end"; size?: number }) {
  const X = view.sx(at[0]);
  const Y = view.sy(at[1]);
  if (!Number.isFinite(X) || !Number.isFinite(Y)) return null;
  return (
    <text x={X + dx} y={Y + dy} textAnchor={anchor} fontSize={size} fontStyle="italic" fontWeight={600} fill={color} className="font-serif" stroke="var(--paper)" strokeWidth={3.5} paintOrder="stroke" strokeLinejoin="round" style={{ pointerEvents: "none" }}>
      {text}
    </text>
  );
}

/** Label placed just beyond the tip of the vector 0 → at, in the vector's direction. */
function TipLabel({ view, at, text, color }: { view: PlotView; at: C; text: string; color: string }) {
  const len = Math.hypot(at[0], at[1]);
  const ux = len > 1e-9 ? at[0] / len : 1;
  const uy = len > 1e-9 ? at[1] / len : 0;
  return <MathLabel view={view} at={at} text={text} color={color} dx={ux * 14} dy={-uy * 14 + 5} anchor={ux < -0.3 ? "end" : ux > 0.3 ? "start" : "middle"} />;
}

/** Arc of radius r (data units) around the origin from angle a0 to a1. */
function arcD(view: PlotView, r: number, a0: number, a1: number, center: C = [0, 0]): string {
  if (![r, a0, a1].every(Number.isFinite)) return "";
  const pts: Pt[] = [];
  const n = Math.max(8, Math.ceil(Math.abs(a1 - a0) * 16));
  for (let k = 0; k <= n; k++) {
    const a = a0 + ((a1 - a0) * k) / n;
    pts.push([center[0] + r * Math.cos(a), center[1] + r * Math.sin(a)]);
  }
  return pathD([pts], view.sx, view.sy);
}

/** Pixels per data unit (equal aspect). */
const ppu = (view: PlotView) => view.W / (view.x[1] - view.x[0]);

function Circle({ view, r, center = [0, 0], color = "var(--muted)", dash = "4 5", width = 1.25, opacity = 0.8 }: { view: PlotView; r: number; center?: C; color?: string; dash?: string; width?: number; opacity?: number }) {
  if (!(r > 0)) return null;
  return <circle cx={view.sx(center[0])} cy={view.sy(center[1])} r={r * ppu(view)} fill="none" stroke={color} strokeDasharray={dash} strokeWidth={width} opacity={opacity} />;
}

function ComplexInput({ name, value, onChange, color }: { name: string; value: C; onChange: (v: C) => void; color: string }) {
  return (
    <div className="flex flex-wrap items-center gap-x-2 gap-y-1" dir="ltr">
      <span className="font-serif text-lg font-semibold italic" style={{ color }}>
        {name} =
      </span>
      <NumberField label={<span><span className="sr-only">{name}: </span>Re</span>} value={value[0]} onChange={(v) => onChange([v, value[1]])} inputClassName="w-20" />
      <span className="font-serif text-ink-2">+</span>
      <NumberField label={<span><span className="sr-only">{name}: </span>Im</span>} value={value[1]} onChange={(v) => onChange([value[0], v])} inputClassName="w-20" />
      <span className="font-serif italic text-ink-2">i</span>
    </div>
  );
}

function PolarRow({ name, value, color }: { name: ReactNode; value: C; color: string }) {
  const { t } = useI18n();
  const ok = isFiniteC(value);
  const a = fmtAngle(arg(value));
  return (
    <tr className="border-t border-line/70">
      <th scope="row" className="py-1 pe-3 text-start font-serif text-base font-semibold italic" style={{ color }}>
        {name}
      </th>
      <td className="py-1 pe-3 font-serif text-base text-ink">{ok ? fmtC(value, 3) : t("w.plot.undefined")}</td>
      <td className="py-1 pe-3 font-mono text-xs text-ink-2">{ok ? fmt(abs(value), 3) : "—"}</td>
      <td className="py-1 font-mono text-xs text-ink-2">
        {ok && abs(value) > 1e-12 ? (
          <>
            <span className="block">{a.deg}</span>
            <span className="block text-muted">{a.rad}</span>
          </>
        ) : (
          "—"
        )}
      </td>
    </tr>
  );
}

function PolarTable({ rows }: { rows: { name: ReactNode; value: C; color: string }[] }) {
  const { t } = useI18n();
  return (
    <div className="overflow-x-auto" dir="ltr">
      <table className="w-full min-w-[270px] text-sm">
        <thead>
          <tr className="text-start text-xs text-muted">
            <th className="pb-1 pe-3 text-start font-semibold" />
            <th className="pb-1 pe-3 text-start font-semibold">{t("w.complex.table.number")}</th>
            <th className="pb-1 pe-3 text-start font-semibold">{t("w.complex.table.modulus")}</th>
            <th className="pb-1 text-start font-semibold">{t("w.complex.table.argument")}</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r, i) => (
            <PolarRow key={i} {...r} />
          ))}
        </tbody>
      </table>
    </div>
  );
}

const inView = (view: PlotView, q: C) => q[0] >= view.x[0] && q[0] <= view.x[1] && q[1] >= view.y[0] && q[1] <= view.y[1];

/* ---------------------------------------------------------------------------
 * Arithmetic
 * ------------------------------------------------------------------------- */

function ArithmeticView({ z, w, setZ, setW, op, setOp, R }: { z: C; w: C; setZ: (v: C) => void; setW: (v: C) => void; op: ComplexOp; setOp: (o: ComplexOp) => void; R: number }) {
  const { t } = useI18n();
  const result: C = op === "sum" ? add(z, w) : op === "product" ? mul(z, w) : op === "quotient" ? div(z, w) : conj(z);
  const resultName = op === "sum" ? "z + w" : op === "product" ? "zw" : op === "quotient" ? "z/w" : "z̄";
  const showW = op !== "conjugate";
  const win: Range = [-R, R];
  const aria = t("w.complex.aria.arithmetic", { z: fmtC(z), w: showW ? fmtC(w) : "—", op: resultName, r: fmtC(result) });
  const step = R <= 4 ? 0.5 : 1;

  const az = arg(z);
  const aw = arg(w);
  const ar = arg(result);

  return (
    <div>
      <ModeTabs
        value={op}
        options={OPS}
        onChange={setOp}
        label={t("w.complex.ops")}
        render={(o) => (
          <span>
            {t(`w.complex.op.${o}`)} <span className="ms-1 font-serif italic opacity-80">{o === "sum" ? "z + w" : o === "product" ? "z·w" : o === "quotient" ? "z / w" : "z̄"}</span>
          </span>
        )}
      />
      <div className="mt-4">
        <Plot x={win} y={win} aspect="equal" maxHeight={460} ariaLabel={aria} xLabel="Re" yLabel="Im" above={() => (
          <>
            <PlotHandle x={z[0]} y={z[1]} onMove={(q) => setZ(q)} label="z" valueText={fmtC(z)} color={COLOR_Z} step={step} constrain={snap(0.05)} />
            {showW && <PlotHandle x={w[0]} y={w[1]} onMove={(q) => setW(q)} label="w" valueText={fmtC(w)} color={COLOR_W} step={step} constrain={snap(0.05)} />}
          </>
        )}>
          {(view) => (
            <>
              {(op === "product" || op === "quotient") && <Circle view={view} r={1} />}
              {op === "sum" && isFiniteC(result) && (
                <>
                  <path
                    d={pathD([[[0, 0], z, result, w, [0, 0]]], view.sx, view.sy)}
                    fill="var(--gold-soft)"
                    fillOpacity={0.55}
                    stroke="none"
                  />
                  <path d={pathD([[z, result]], view.sx, view.sy)} stroke={COLOR_W} strokeDasharray="6 5" strokeWidth={1.75} fill="none" />
                  <path d={pathD([[w, result]], view.sx, view.sy)} stroke={COLOR_Z} strokeDasharray="6 5" strokeWidth={1.75} fill="none" />
                </>
              )}
              {op === "conjugate" && <path d={pathD([[z, result]], view.sx, view.sy)} stroke="var(--muted)" strokeDasharray="3 4" strokeWidth={1.5} fill="none" />}
              {(op === "product" || op === "quotient") && (
                <g>
                  {(
                    [
                      [az, R * 0.17, COLOR_Z, undefined],
                      [aw, R * 0.27, COLOR_W, "5 3"],
                      [ar, R * 0.37, COLOR_R, "1.5 3"],
                    ] as [number, number, string, string | undefined][]
                  ).map(([a, r, col, dash], i) =>
                    Number.isFinite(a) && Math.abs(a) > 1e-9 ? (
                      <g key={i}>
                        <path d={arcD(view, r, 0, a)} fill="none" stroke={col} strokeWidth={i === 2 ? 2.5 : 2} strokeDasharray={dash} strokeLinecap="round" />
                        <MathLabel view={view} at={[(r + R * 0.06) * Math.cos(a / 2), (r + R * 0.06) * Math.sin(a / 2)]} text={fmtAngle(a).deg} color={col} dx={0} dy={4} anchor="middle" size={11} />
                      </g>
                    ) : null,
                  )}
                </g>
              )}
              <DataArrow from={[0, 0]} to={z} color={COLOR_Z} width={2.5} />
              {showW && <DataArrow from={[0, 0]} to={w} color={COLOR_W} width={2.5} dash="7 4" />}
              {isFiniteC(result) && <DataArrow from={[0, 0]} to={result} color={COLOR_R} width={3} />}
              <TipLabel view={view} at={z} text="z" color={COLOR_Z} />
              {showW && <TipLabel view={view} at={w} text="w" color={COLOR_W} />}
              {isFiniteC(result) && <TipLabel view={view} at={result} text={resultName} color={COLOR_R} />}
            </>
          )}
        </Plot>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.plot.ui.dragHint")}</p>
      <div className="mt-3 flex flex-wrap gap-x-6 gap-y-2">
        <ComplexInput name="z" value={z} onChange={setZ} color={COLOR_Z} />
        {showW && <ComplexInput name="w" value={w} onChange={setW} color={COLOR_W} />}
      </div>
      <Readout className="mt-4">
        <PolarTable
          rows={[
            { name: "z", value: z, color: COLOR_Z },
            ...(showW ? [{ name: "w", value: w, color: COLOR_W }] : []),
            { name: resultName, value: result, color: COLOR_R },
          ]}
        />
        <ArithmeticNote op={op} z={z} w={w} result={result} R={R} />
      </Readout>
    </div>
  );
}

function ArithmeticNote({ op, z, w, result, R }: { op: ComplexOp; z: C; w: C; result: C; R: number }) {
  const { t } = useI18n();
  const out = isFiniteC(result) && (Math.abs(result[0]) > R * 1.4 || Math.abs(result[1]) > R);
  const outside = out ? <p className="mt-1 text-sm text-warn">{t("w.complex.outside", { name: op === "product" ? "zw" : op === "quotient" ? "z/w" : op === "sum" ? "z + w" : "z̄" })}</p> : null;
  if (op === "sum") {
    return (
      <div className="mt-3 space-y-1 text-sm text-ink-2">
        <p className="font-serif text-base text-ink" dir="ltr">
          z + w = ({fmt(z[0], 3)} + {fmt(w[0], 3)}) + ({fmt(z[1], 3)} + {fmt(w[1], 3)})<i>i</i> = {fmtC(result, 3)}
        </p>
        <p>{t("w.complex.note.sum")}</p>
        {outside}
      </div>
    );
  }
  if (op === "conjugate") {
    return (
      <div className="mt-3 space-y-1 text-sm text-ink-2">
        <p className="font-serif text-base text-ink" dir="ltr">
          z · z̄ = |z|² = {fmt(abs(z) ** 2, 3)}
        </p>
        <p>{t("w.complex.note.conjugate")}</p>
      </div>
    );
  }
  if (op === "quotient" && abs(w) === 0) return <p className="mt-3 text-sm font-semibold text-bad">{t("w.complex.divZero")}</p>;
  const az = arg(z);
  const aw = arg(w);
  const ar = arg(result);
  const raw = op === "product" ? az + aw : az - aw;
  const wrapped = Number.isFinite(raw) && Math.abs(raw - ar) > 1e-9;
  const sym = op === "product" ? "×" : "÷";
  const asym = op === "product" ? "+" : "−";
  return (
    <div className="mt-3 space-y-1 text-sm text-ink-2">
      {abs(z) === 0 || abs(w) === 0 ? (
        <p>{t("w.complex.argZero")}</p>
      ) : (
        <>
          <p>
            <span className="font-semibold text-ink">{t(`w.complex.lengths.${op}`)}</span>{" "}
            <span className="font-serif text-base text-ink" dir="ltr">
              {fmt(abs(z), 3)} {sym} {fmt(abs(w), 3)} = {fmt(abs(result), 3)}
            </span>
          </p>
          <p>
            <span className="font-semibold text-ink">{t(`w.complex.angles.${op}`)}</span>{" "}
            <span className="font-serif text-base text-ink" dir="ltr">
              {fmtAngle(az).deg} {asym} {fmtAngle(aw).deg} = {fmtAngle(raw).deg}
              {wrapped && <> ≡ {fmtAngle(ar).deg}</>}
            </span>
          </p>
          {wrapped && <p className="text-xs text-muted">{t("w.complex.wrap")}</p>}
        </>
      )}
      <p>{t(`w.complex.note.${op}`)}</p>
      {outside}
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Roots
 * ------------------------------------------------------------------------- */

function RootsView({ c, setC, n, setN, R }: { c: C; setC: (v: C) => void; n: number; setN: (v: number) => void; R: number }) {
  const { t, n: num } = useI18n();
  const roots = nthRoots(c, n);
  const rho = Math.pow(abs(c), 1 / n);
  const win: Range = [-R, R];
  const isOne = Math.abs(c[0] - 1) < 1e-9 && Math.abs(c[1]) < 1e-9;
  const isZero = abs(c) < 1e-12;
  const step = R <= 4 ? 0.5 : 1;
  const aria = t("w.complex.aria.roots", { n, c: fmtC(c), r: fmt(rho, 3) });
  const quick: [string, C][] = [
    ["1", [1, 0]],
    ["−1", [-1, 0]],
    ["i", [0, 1]],
    ["1 + i", [1, 1]],
  ];

  return (
    <div>
      <div className="grid gap-4 sm:grid-cols-[minmax(0,1fr)_auto] sm:items-end">
        <Slider label={t("w.complex.roots.n")} value={n} min={2} max={12} step={1} onChange={(v) => setN(Math.round(v))} display={`n = ${n}`} accent="var(--formal)" />
        <div role="group" aria-label={t("w.complex.roots.quick")} className="flex flex-wrap items-center gap-2">
          <span className="text-sm font-semibold text-ink-2">{t("w.complex.roots.quick")}</span>
          {quick.map(([label, v]) => (
            <button key={label} type="button" aria-pressed={Math.abs(c[0] - v[0]) < 1e-9 && Math.abs(c[1] - v[1]) < 1e-9} className={`btn btn-sm ${Math.abs(c[0] - v[0]) < 1e-9 && Math.abs(c[1] - v[1]) < 1e-9 ? "btn-primary" : "btn-ghost"}`} onClick={() => setC(v)}>
              <span className="font-serif italic">c = {label}</span>
            </button>
          ))}
        </div>
      </div>
      <div className="mt-4">
        <Plot
          x={win}
          y={win}
          aspect="equal"
          maxHeight={460}
          ariaLabel={aria}
          xLabel="Re"
          yLabel="Im"
          above={() => <PlotHandle x={c[0]} y={c[1]} onMove={(q) => setC(q)} label="c" valueText={fmtC(c)} color={COLOR_C} step={step} constrain={snap(0.05)} />}
        >
          {(view) => (
            <>
              <Circle view={view} r={1} opacity={0.45} />
              {!isZero && <Circle view={view} r={rho} color="var(--formal)" dash="5 4" width={1.5} />}
              {!isZero && (
                <path d={pathD([[...roots, roots[0]]], view.sx, view.sy)} fill="var(--formal-soft)" fillOpacity={0.6} stroke="var(--formal)" strokeWidth={2} strokeLinejoin="round" />
              )}
              {!isZero &&
                roots.map((q, k) => <path key={`ray${k}`} d={pathD([[[0, 0], q]], view.sx, view.sy)} stroke="var(--formal)" strokeOpacity={0.35} strokeWidth={1} />)}
              {!isZero && (
                <>
                  <path d={arcD(view, Math.min(0.5, rho * 0.45), arg(roots[0]), arg(roots[0]) + (2 * Math.PI) / n)} fill="none" stroke="var(--gold-ink)" strokeWidth={1.75} />
                  <MathLabel
                    view={view}
                    at={[Math.min(0.5, rho * 0.45) * 1.9 * Math.cos(arg(roots[0]) + Math.PI / n), Math.min(0.5, rho * 0.45) * 1.9 * Math.sin(arg(roots[0]) + Math.PI / n)]}
                    text={`${fmt(360 / n, 1)}°`}
                    color="var(--gold-ink)"
                    dx={0}
                    dy={4}
                    anchor="middle"
                    size={11}
                  />
                </>
              )}
              <path d={pathD([[[0, 0], c]], view.sx, view.sy)} stroke={COLOR_C} strokeWidth={1.5} strokeDasharray="2 4" fill="none" />
              {roots.map((q, k) => (
                <g key={k}>
                  <circle cx={view.sx(q[0])} cy={view.sy(q[1])} r={k === 0 ? 6 : 5} fill={k === 0 ? "var(--formal)" : "var(--card)"} stroke="var(--formal)" strokeWidth={2.25} />
                  {!isZero && <TipLabel view={view} at={q} text={`w${sub_(k)}`} color="var(--formal)" />}
                </g>
              ))}
              <MathLabel view={view} at={c} text="c" color="var(--gold-ink)" dx={10} dy={18} />
            </>
          )}
        </Plot>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.plot.ui.dragHint")}</p>
      <div className="mt-3">
        <ComplexInput name="c" value={c} onChange={setC} color="var(--gold-ink)" />
      </div>
      <Readout className="mt-4">
        <p className="text-sm font-semibold text-ink-2">{t("w.complex.roots.heading", { n })}</p>
        <ul className="mt-2 grid gap-x-4 gap-y-1 font-serif text-[0.95rem] text-ink sm:grid-cols-2" dir="ltr">
          {roots.map((q, k) => (
            <li key={k}>
              <i>w</i>
              {sub_(k)} = {fmtC(q, 3)}
            </li>
          ))}
        </ul>
        <div className="mt-3 space-y-1 text-sm text-ink-2">
          {isZero ? (
            <p>{t("w.complex.roots.zero")}</p>
          ) : (
            <>
              <p>{t("w.complex.roots.radius", { r: num(Number(rho.toFixed(4))) })}</p>
              <p>{t("w.complex.roots.spacing", { deg: num(Number((360 / n).toFixed(2))), n })}</p>
              <p>{t("w.complex.roots.principal")}</p>
              {isOne && <p className="font-semibold text-ink">{t("w.complex.roots.unity", { n })}</p>}
              <p>{t("w.complex.roots.sum")}</p>
            </>
          )}
        </div>
      </Readout>
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Maps
 * ------------------------------------------------------------------------- */

function GridLayer({ spec, grid, view, side }: { spec: MapSpec; grid: GridKind; view: PlotView; side: "z" | "w" }) {
  const { x, y } = view;
  const paths = useMemo(() => {
    const lines = gridLines(spec, grid);
    const out: [string, string] = ["", ""];
    for (const L of lines) {
      const pieces = side === "z" ? sampleParametric((tt) => L.path(tt)[0], (tt) => L.path(tt)[1], L.t, { x, y }, 240) : imageCurve(spec.f, L.path, L.t, { x, y }, 900);
      out[L.family] += pathD(pieces, view.sx, view.sy);
    }
    return out;
  }, [spec, grid, side, x[0], x[1], y[0], y[1], view.W]); // eslint-disable-line react-hooks/exhaustive-deps
  return (
    <g fill="none" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <path d={paths[0]} stroke="var(--formal)" strokeWidth={1.6} strokeOpacity={0.85} />
      <path d={paths[1]} stroke="var(--human)" strokeWidth={1.6} strokeOpacity={0.85} strokeDasharray="6 4" />
    </g>
  );
}

function ProbeLegs({ spec, z0, view, side }: { spec: MapSpec; z0: C; view: PlotView; side: "z" | "w" }) {
  const eps = (spec.zView.x[1] - spec.zView.x[0]) * 0.07;
  const h = (s: number): C => [z0[0] + s, z0[1]];
  const v = (s: number): C => [z0[0], z0[1] + s];
  const box = { x: view.x, y: view.y };
  const legs =
    side === "z"
      ? [pathD([[h(-eps), h(eps)]], view.sx, view.sy), pathD([[v(-eps), v(eps)]], view.sx, view.sy)]
      : [pathD(imageCurve(spec.f, h, [-eps, eps], box, 80), view.sx, view.sy), pathD(imageCurve(spec.f, v, [-eps, eps], box, 80), view.sx, view.sy)];
  return (
    <g fill="none" strokeLinecap="round" aria-hidden="true">
      <path d={legs[0]} stroke="var(--gold)" strokeWidth={3.5} />
      <path d={legs[1]} stroke="var(--sky)" strokeWidth={3.5} strokeDasharray="5 3" />
    </g>
  );
}

/** Right-angle square (when the oriented angle is 90°) or an arc with its size in degrees. */
function AngleMark({ view, at, d1, angleDeg }: { view: PlotView; at: C; d1: C; angleDeg: number }) {
  if (!isFiniteC(at) || !Number.isFinite(angleDeg) || !inView(view, at)) return null;
  const s = 11 / ppu(view);
  const a0 = arg(d1);
  if (!Number.isFinite(a0)) return null;
  const a1 = a0 + (angleDeg * Math.PI) / 180;
  if (Math.abs(angleDeg - 90) < 0.5) {
    const u: C = [Math.cos(a0) * s, Math.sin(a0) * s];
    const v: C = [Math.cos(a1) * s, Math.sin(a1) * s];
    return <path d={pathD([[add(at, u), add(add(at, u), v), add(at, v)]], view.sx, view.sy)} fill="none" stroke="var(--ink)" strokeWidth={1.5} />;
  }
  const mid = (a0 + a1) / 2;
  return (
    <g>
      <path d={arcD(view, s * 1.5, a0, a1, at)} fill="none" stroke="var(--bad)" strokeWidth={2} />
      <MathLabel view={view} at={[at[0] + Math.cos(mid) * s * 3, at[1] + Math.sin(mid) * s * 3]} text={`${Math.round(angleDeg)}°`} color="var(--bad)" dx={0} dy={5} anchor="middle" size={13} />
    </g>
  );
}

const aspectOf = (v: { x: Range; y: Range }) => (v.y[1] - v.y[0]) / (v.x[1] - v.x[0]);
/** Widen the y-window (about its centre) so that height/width = ratio. */
function withAspect(v: { x: Range; y: Range }, ratio: number): { x: Range; y: Range } {
  const c = (v.y[0] + v.y[1]) / 2;
  const half = (ratio * (v.x[1] - v.x[0])) / 2;
  return { x: v.x, y: [Math.min(v.y[0], c - half), Math.max(v.y[1], c + half)] };
}

function MapView({ id, setId, grid, setGrid, probe, setProbe }: { id: MapId; setId: (m: MapId) => void; grid: GridKind; setGrid: (g: GridKind) => void; probe: C; setProbe: (z: C) => void }) {
  const { t } = useI18n();
  const spec = MAPS[id];
  const status = probeStatus(spec, probe);
  const w0 = status.kind === "pole" ? ([NaN, NaN] as C) : spec.f(probe);
  const d = status.kind === "pole" ? ([NaN, NaN] as C) : spec.df(probe);
  const angle = status.kind === "pole" ? NaN : status.kind === "critical" ? (status.order * 90) % 360 || 360 : imageAngle(spec.f, probe);
  // Direction of the image of the horizontal leg (for the angle mark).
  const hImg: C = status.kind === "critical" ? sub(spec.f([probe[0] + 1e-3, probe[1]]), w0) : d;
  const fam = grid === "cartesian" ? ["h", "v"] : ["circles", "rays"];
  // Give both panels the same shape so they line up side by side.
  // (Capped: panels are about 340 px wide and at most 420 px tall, so taller windows just get wider.)
  const ratio = Math.min(1.25, Math.max(aspectOf(spec.zView), aspectOf(spec.wView)));
  const zv = withAspect(spec.zView, ratio);
  const wv = withAspect(spec.wView, ratio);
  const formula = spec.formula;
  const step = 0.25;

  return (
    <div>
      <div className="flex flex-wrap items-center gap-x-5 gap-y-3">
        <div role="group" aria-label={t("w.complex.map.fn")} className="flex flex-wrap items-center gap-2">
          <span className="text-sm font-semibold text-ink-2">{t("w.complex.map.fn")}</span>
          {MAP_IDS.map((m) => (
            <button key={m} type="button" aria-pressed={m === id} className={`btn btn-sm ${m === id ? "btn-primary" : "btn-ghost"}`} onClick={() => setId(m)}>
              <span className="font-serif italic" dir="ltr">
                {MAPS[m].formula}
              </span>
            </button>
          ))}
        </div>
        <div role="group" aria-label={t("w.complex.map.grid")} className="flex flex-wrap items-center gap-2">
          <span className="text-sm font-semibold text-ink-2">{t("w.complex.map.grid")}</span>
          {(["cartesian", "polar"] as const).map((g) => (
            <button key={g} type="button" aria-pressed={g === grid} className={`btn btn-sm ${g === grid ? "btn-primary" : "btn-ghost"}`} onClick={() => setGrid(g)}>
              {t(`w.complex.map.gridKind.${g}`)}
            </button>
          ))}
        </div>
      </div>

      <div className="mt-4 grid gap-4 sm:grid-cols-2">
        <figure className="min-w-0">
          <figcaption className="mb-1.5 text-xs font-semibold uppercase tracking-wide text-muted">
            {t("w.complex.map.zPlane")}
          </figcaption>
          <Plot
            x={zv.x}
            y={zv.y}
            aspect="equal"
            defaultWidth={340}
            maxHeight={420}
            ariaLabel={t("w.complex.aria.zPlane", { grid: t(`w.complex.map.gridKind.${grid}`), z: fmtC(probe) })}
            xLabel="x"
            yLabel="y"
            above={() => <PlotHandle x={probe[0]} y={probe[1]} onMove={(q) => setProbe(q)} label="z₀" valueText={fmtC(probe)} color="var(--ink)" step={step} constrain={snap(0.025)} r={6} />}
          >
            {(view) => (
              <>
                <Circle view={view} r={1} opacity={0.5} />
                <GridLayer spec={spec} grid={grid} view={view} side="z" />
                {spec.poles.map((q, k) => (
                  <MathLabel key={`p${k}`} view={view} at={q} text="×" color="var(--bad)" dx={0} dy={5} anchor="middle" size={18} />
                ))}
                {spec.critical.map((q, k) => (
                  <circle key={`c${k}`} cx={view.sx(q.z[0])} cy={view.sy(q.z[1])} r={4} fill="var(--paper)" stroke="var(--bad)" strokeWidth={1.75} />
                ))}
                <ProbeLegs spec={spec} z0={probe} view={view} side="z" />
                <AngleMark view={view} at={probe} d1={[1, 0]} angleDeg={90} />
                <MathLabel view={view} at={probe} text="z₀" dx={10} dy={18} />
              </>
            )}
          </Plot>
        </figure>
        <figure className="min-w-0">
          <figcaption className="mb-1.5 text-xs font-semibold uppercase tracking-wide text-muted">
            {t("w.complex.map.wPlane")} ·{" "}
            <span className="font-serif text-sm normal-case italic tracking-normal text-ink" dir="ltr">
              w = {formula}
            </span>
          </figcaption>
          <Plot
            x={wv.x}
            y={wv.y}
            aspect="equal"
            defaultWidth={340}
            maxHeight={420}
            ariaLabel={t("w.complex.aria.wPlane", { f: formula, w: fmtC(w0) })}
            xLabel="u"
            yLabel="v"
          >
            {(view) => (
              <>
                <Circle view={view} r={1} opacity={0.5} />
                <GridLayer spec={spec} grid={grid} view={view} side="w" />
                {status.kind !== "pole" && <ProbeLegs spec={spec} z0={probe} view={view} side="w" />}
                {status.kind !== "pole" && inView(view, w0) && (
                  <>
                    <AngleMark view={view} at={w0} d1={hImg} angleDeg={angle} />
                    <circle cx={view.sx(w0[0])} cy={view.sy(w0[1])} r={5} fill="var(--ink)" stroke="var(--card)" strokeWidth={2} />
                    <MathLabel view={view} at={w0} text="f(z₀)" dx={10} dy={18} />
                  </>
                )}
              </>
            )}
          </Plot>
        </figure>
      </div>

      <ul className="mt-3 flex flex-wrap gap-x-5 gap-y-1.5 text-sm text-ink-2" aria-label={t("w.plot.legend")}>
        <li className="flex items-center gap-2">
          <LegendSwatch color="var(--formal)" />
          {t(`w.complex.map.family.${fam[0]}`)}
        </li>
        <li className="flex items-center gap-2">
          <LegendSwatch color="var(--human)" dash="6 4" />
          {t(`w.complex.map.family.${fam[1]}`)}
        </li>
        <li className="flex items-center gap-2">
          <LegendSwatch color="var(--gold)" width={3.5} />
          <LegendSwatch color="var(--sky)" dash="5 3" width={3.5} />
          {t("w.complex.map.legs")}
        </li>
      </ul>
      <p className="mt-1 text-xs text-muted">{t("w.plot.ui.dragHint")}</p>
      <div className="mt-3">
        <ComplexInput name="z₀" value={probe} onChange={setProbe} color="var(--ink)" />
      </div>

      <Readout className="mt-4">
        <dl className="grid gap-x-4 gap-y-1 text-sm sm:grid-cols-[auto_minmax(0,1fr)]">
          <dt className="font-serif italic text-ink-2">z₀</dt>
          <dd className="font-serif text-base text-ink" dir="ltr">{fmtC(probe, 3)}</dd>
          <dt className="font-serif italic text-ink-2">w₀ = f(z₀)</dt>
          <dd className="font-serif text-base text-ink" dir="ltr">{status.kind === "pole" ? t("w.plot.undefined") : fmtC(w0, 3)}</dd>
          {status.kind !== "pole" && (
            <>
              <dt className="font-serif italic text-ink-2">f′(z₀)</dt>
              <dd className="font-serif text-base text-ink" dir="ltr">{fmtC(d, 3)}</dd>
              <dt className="text-ink-2">{t("w.complex.map.scaling")}</dt>
              <dd className="font-mono text-ink" dir="ltr">{fmt(abs(d), 3)}</dd>
              {status.kind === "conformal" && (
                <>
                  <dt className="text-ink-2">{t("w.complex.map.rotation")}</dt>
                  <dd className="font-mono text-ink" dir="ltr">{fmtAngle(arg(d)).deg}</dd>
                </>
              )}
              <dt className="text-ink-2">{t("w.complex.map.angle")}</dt>
              <dd className="font-mono text-ink" dir="ltr">{Number.isFinite(angle) ? `${fmt(angle, 1)}°` : "—"}</dd>
            </>
          )}
        </dl>
        <p className={`mt-3 text-sm ${status.kind === "conformal" ? "text-ink-2" : "font-semibold text-bad"}`}>
          {status.kind === "pole"
            ? t("w.complex.map.pole")
            : status.kind === "critical"
              ? t("w.complex.map.critical", { k: status.order, deg: status.order * 90 })
              : t("w.complex.map.conformal", { rot: fmtAngle(arg(d)).deg, scale: fmt(abs(d), 3) })}
        </p>
        <p className="mt-2 text-sm text-ink-2">{t(`w.complex.map.note.${MAP_KEY[id]}`)}</p>
      </Readout>
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Winding
 * ------------------------------------------------------------------------- */

const REGION_STYLE = (k: number) => (k > 0 ? { fill: "var(--formal)", opacity: Math.min(0.12 * k, 0.4) } : { fill: "var(--human)", opacity: Math.min(0.14 * -k, 0.4) });

function WindingView({ curve, setCurve, p, setP, R }: { curve: CurveId; setCurve: (c: CurveId) => void; p: C; setP: (v: C) => void; R: number }) {
  const { t, n: num } = useI18n();
  const reduced = useReducedMotion();
  const [reversed, setReversed] = useState(false);
  const [regions, setRegions] = useState(true);
  const [tt, setTt] = useState(Math.PI / 3);
  const [playing, setPlaying] = useState(false);
  const poly = useMemo(() => curvePolygon(CURVES[curve], POLY_N, reversed), [curve, reversed]);
  const runs = useMemo(() => windingRuns(poly, 150), [poly]);
  const values = useMemo(() => [...new Set(runs.map((r) => r.k))].sort((a, b) => a - b), [runs]);
  const info = winding(poly, p, R * 0.012);
  const k = windingInteger(info);
  const win: Range = [-R, R];
  const step = R <= 4 ? 0.5 : 1;

  // Point moving along the curve and the turning of the arrow from p so far.
  const idx = clamp(Math.round((tt / (2 * Math.PI)) * POLY_N), 0, POLY_N);
  const moving = poly[idx];
  const turnedSoFar = Number(windingByAngle(poly.slice(0, idx + 1), p).toFixed(2)) || 0;

  const raf = useRef<number | null>(null);
  const ttRef = useRef(tt);
  ttRef.current = tt;
  useEffect(() => {
    if (!playing) return;
    let last = performance.now();
    const tick = (now: number) => {
      const dt = Math.min(0.05, (now - last) / 1000);
      last = now;
      const nv = Math.min(2 * Math.PI, ttRef.current + dt * 1.1);
      ttRef.current = nv;
      setTt(nv);
      if (nv >= 2 * Math.PI) setPlaying(false);
      else raf.current = requestAnimationFrame(tick);
    };
    raf.current = requestAnimationFrame(tick);
    return () => {
      if (raf.current !== null) cancelAnimationFrame(raf.current);
    };
  }, [playing]);

  const crossingText = info.crossings.length === 0 ? t("w.complex.winding.noCrossings") : `${info.crossings.map((q, i) => (i === 0 ? (q.sign > 0 ? "(+1)" : "(−1)") : q.sign > 0 ? " + (+1)" : " + (−1)")).join("")} = ${info.byRay < 0 ? "−" : ""}${Math.abs(info.byRay)}`;
  const aria = t("w.complex.aria.winding", { curve: t(`w.complex.winding.curves.${curve}`), p: fmtC(p), k: info.onCurve ? "—" : k });

  return (
    <div>
      <div role="group" aria-label={t("w.complex.winding.curve")} className="flex flex-wrap items-center gap-2">
        <span className="text-sm font-semibold text-ink-2">{t("w.complex.winding.curve")}</span>
        {CURVE_IDS.map((cv) => (
          <button key={cv} type="button" aria-pressed={cv === curve} className={`btn btn-sm ${cv === curve ? "btn-primary" : "btn-ghost"}`} onClick={() => setCurve(cv)}>
            {t(`w.complex.winding.curves.${cv}`)}
          </button>
        ))}
      </div>
      <div className="mt-2 flex flex-wrap gap-2">
        <button type="button" aria-pressed={reversed} className={`btn btn-sm ${reversed ? "btn-gold" : "btn-ghost"}`} onClick={() => setReversed((r) => !r)}>
          <RotateCcw size={14} aria-hidden="true" /> {t("w.complex.winding.reverse")}
        </button>
        <button type="button" aria-pressed={regions} className={`btn btn-sm ${regions ? "btn-gold" : "btn-ghost"}`} onClick={() => setRegions((r) => !r)}>
          {t("w.complex.winding.regions")}
        </button>
      </div>

      <div className="mt-4">
        <Plot
          x={win}
          y={win}
          aspect="equal"
          maxHeight={460}
          ariaLabel={aria}
          xLabel="Re"
          yLabel="Im"
          above={() => <PlotHandle x={p[0]} y={p[1]} onMove={(q) => setP(q)} label="p" valueText={fmtC(p)} color={COLOR_C} step={step} constrain={snap(0.05)} />}
        >
          {(view) => (
            <>
              {regions && <RegionLayer view={view} runs={runs} values={values} />}
              <CurveWithArrows view={view} poly={poly} />
              {/* Ray from p to the right, with signed crossings. */}
              <line x1={view.sx(p[0])} y1={view.sy(p[1])} x2={view.W} y2={view.sy(p[1])} stroke="var(--sky)" strokeWidth={1.75} strokeDasharray="6 4" />
              {!info.onCurve &&
                info.crossings.map((q, i) => (
                  <g key={i}>
                    <circle cx={view.sx(q.x)} cy={view.sy(p[1])} r={5} fill={q.sign > 0 ? "var(--good)" : "var(--bad)"} stroke="var(--card)" strokeWidth={1.5} />
                    <text x={view.sx(q.x)} y={view.sy(p[1]) - 10} textAnchor="middle" fontSize={12} fontWeight={700} fill={q.sign > 0 ? "var(--good)" : "var(--bad)"} stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                      {q.sign > 0 ? "+1" : "−1"}
                    </text>
                  </g>
                ))}
              {/* Arrow from p to the moving point. */}
              {isFiniteC(moving) && <DataArrow from={p} to={moving} color="var(--gold-ink)" width={2} head={8} />}
              {isFiniteC(moving) && <circle cx={view.sx(moving[0])} cy={view.sy(moving[1])} r={4.5} fill="var(--gold-ink)" stroke="var(--card)" strokeWidth={1.5} />}
              <MathLabel view={view} at={p} text="p" color="var(--gold-ink)" dx={-12} dy={18} anchor="end" />
            </>
          )}
        </Plot>
      </div>
      {regions && values.length > 0 && (
        <ul className="mt-2 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-2" aria-label={t("w.plot.legend")}>
          {values.map((v) => {
            const st = REGION_STYLE(v);
            return (
              <li key={v} className="flex items-center gap-1.5">
                <svg width="14" height="14" aria-hidden="true">
                  <rect width="14" height="14" rx="3" fill={st.fill} fillOpacity={st.opacity + 0.05} stroke="var(--line-2)" />
                </svg>
                {t("w.complex.winding.region", { k: num(v) })}
              </li>
            );
          })}
        </ul>
      )}
      <p className="mt-1 text-xs text-muted">{t("w.plot.ui.dragHint")}</p>

      <div className="mt-3 grid gap-3 sm:grid-cols-[minmax(0,1fr)_auto] sm:items-end">
        <Slider
          label={t("w.complex.winding.t")}
          value={tt}
          min={0}
          max={2 * Math.PI}
          step={(2 * Math.PI) / 360}
          onChange={(v) => {
            setPlaying(false);
            setTt(v);
          }}
          display={t("w.complex.winding.turned", { turns: num(turnedSoFar) })}
          accent="var(--gold)"
        />
        {!reduced && (
          <button
            type="button"
            className="btn btn-sm btn-ghost"
            onClick={() => {
              if (playing) setPlaying(false);
              else {
                if (tt >= 2 * Math.PI - 1e-6) setTt(0);
                setPlaying(true);
              }
            }}
          >
            {playing ? <Pause size={14} aria-hidden="true" /> : <Play size={14} aria-hidden="true" />} {playing ? t("w.complex.winding.pause") : t("w.complex.winding.play")}
          </button>
        )}
      </div>
      <div className="mt-3">
        <ComplexInput name="p" value={p} onChange={setP} color="var(--gold-ink)" />
      </div>

      <Readout className="mt-4">
        {info.onCurve ? (
          <p className="font-semibold text-bad">{t("w.complex.winding.onCurve")}</p>
        ) : (
          <>
            <p className="font-serif text-xl text-ink">{t("w.complex.winding.result", { k: num(k) })}</p>
            <p className="mt-2 text-sm text-ink-2">{t("w.complex.winding.byAngle", { k: num(k) })}</p>
            <p className="mt-1 text-sm text-ink-2">
              {t("w.complex.winding.byRay")}{" "}
              <span className="font-serif text-base text-ink" dir="ltr">
                {crossingText}
              </span>
            </p>
          </>
        )}
        <p className="mt-2 text-xs text-muted">{t("w.complex.winding.rayRule")}</p>
        <p className="mt-1 text-xs text-muted">{t("w.complex.winding.sampled", { count: num(POLY_N) })}</p>
      </Readout>
    </div>
  );
}

/** One path per winding value, so overlapping scan-line strips do not darken each other. */
function RegionLayer({ view, runs, values }: { view: PlotView; runs: ReturnType<typeof windingRuns>; values: number[] }) {
  const f = (v: number) => v.toFixed(2);
  return (
    <g aria-hidden="true">
      {values.map((k) => {
        let d = "";
        for (const r of runs) {
          if (r.k !== k) continue;
          const x0 = view.sx(r.x0);
          const x1 = view.sx(r.x1);
          const y0 = view.sy(r.y1) - 0.5;
          const y1 = view.sy(r.y0) + 0.5;
          d += `M${f(x0)} ${f(y0)}H${f(x1)}V${f(y1)}H${f(x0)}Z`;
        }
        const st = REGION_STYLE(k);
        return <path key={k} d={d} fill={st.fill} fillOpacity={st.opacity} />;
      })}
    </g>
  );
}

function CurveWithArrows({ view, poly }: { view: PlotView; poly: C[] }) {
  const d = pathD([poly], view.sx, view.sy);
  const heads: string[] = [];
  const N = poly.length - 1;
  for (let j = 0; j < 6; j++) {
    const i = Math.floor(((j + 0.35) / 6) * N);
    const a = poly[Math.max(0, i - 2)];
    const b = poly[Math.min(N, i + 2)];
    const X = view.sx(poly[i][0]);
    const Y = view.sy(poly[i][1]);
    const dx = view.sx(b[0]) - view.sx(a[0]);
    const dy = view.sy(b[1]) - view.sy(a[1]);
    const L = Math.hypot(dx, dy);
    if (!(L > 0.01)) continue;
    const ux = dx / L;
    const uy = dy / L;
    heads.push(arrowPath(X - ux * 8, Y - uy * 8, X + ux * 6, Y + uy * 6, 11).head);
  }
  return (
    <g aria-hidden="true">
      <path d={d} fill="none" stroke="var(--ink-2)" strokeWidth={2.5} strokeLinejoin="round" />
      <path d={heads.join("")} fill="var(--ink-2)" />
    </g>
  );
}
