"use client";

import { RotateCcw } from "lucide-react";
import { useMemo, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { compileExpr, prettyExpr, stripLhs, toNumber, toParams, toRange, type ParamSpec, type Vars } from "./lib/expr";
import { autoRange, clamp, fmt, pathD, sampleFunction, type Pt, type Range } from "./lib/plot-core";
import { Plot, PlotHandle, type PlotView } from "./lib/plot-svg";
import { ExprField, LegendSwatch, ModeTabs, NumberField, Readout, Slider } from "./lib/plot-ui";
import {
  EULER_GAMMA,
  WAVES,
  classifyOrbit,
  epsilonIndex,
  fixedPoints,
  fourierPartial,
  gibbsOvershoot,
  iterate,
  looksHarmonic,
  maxFourierError,
  partialSums,
  sequenceTerms,
  termsDoNotVanish,
  waveValue,
  type Wave,
} from "./lib/plot-seq";

export type SeqMode = "sequence" | "series" | "cobweb" | "fourier";
const MODES: readonly SeqMode[] = ["sequence", "series", "cobweb", "fourier"];

interface SequenceLabProps {
  mode?: unknown;
  modes?: unknown;
  term?: unknown;
  limit?: unknown;
  fn?: unknown;
  x0?: unknown;
  params?: unknown;
  wave?: unknown;
  N?: unknown;
  x?: unknown;
  y?: unknown;
  epsilon?: unknown;
  editable?: boolean;
  title?: string;
  subtitle?: string;
}

/** Which mode tabs to show: `modes` if valid; otherwise only `mode` when given; otherwise all. */
export function resolveSeqModes(mode: unknown, modes: unknown): { initial: SeqMode; offered: SeqMode[] } {
  const isMode = (m: unknown): m is SeqMode => MODES.includes(m as SeqMode);
  const listed = Array.isArray(modes) ? MODES.filter((m) => modes.includes(m)) : [];
  const initial: SeqMode = isMode(mode) ? mode : listed[0] ?? "sequence";
  if (listed.length > 0) return { initial, offered: listed.includes(initial) ? listed : [initial, ...listed] };
  return { initial, offered: isMode(mode) ? [mode] : [...MODES] };
}

const str = (v: unknown): string | null => (typeof v === "string" ? v.slice(0, 300) : typeof v === "number" && Number.isFinite(v) ? String(v) : null);
const intIn = (v: unknown, lo: number, hi: number, fallback: number) => Math.round(clamp(toNumber(v, fallback), lo, hi));

/**
 * Sequences and series lab: ε-bands for limits of sequences, partial sums of
 * series, cobweb diagrams of iterated maps and Fourier partial sums.
 */
export function SequenceLab(props: SequenceLabProps) {
  const { t } = useI18n();
  const { initial, offered } = resolveSeqModes(props.mode, props.modes);
  const [mode, setMode] = useState<SeqMode>(initial);
  const editable = props.editable ?? true;
  const termGiven = str(props.term);
  const limitGiven = str(props.limit);

  return (
    <WidgetFrame title={props.title ?? t(`w.seq.title.${mode}`)} subtitle={props.subtitle ?? t(`w.seq.subtitle.${mode}`)}>
      {offered.length > 1 && (
        <div className="mb-4">
          <ModeTabs value={mode} options={offered} onChange={setMode} label={t("w.seq.modes")} render={(m) => t(`w.seq.mode.${m}`)} />
        </div>
      )}
      {mode === "sequence" && (
        <SequencePanel
          term={termGiven ?? "1 + (-1)^n/n"}
          limit={termGiven ? limitGiven : (limitGiven ?? "1")}
          N={intIn(props.N, 1, 200, 30)}
          epsilon={toNumber(props.epsilon, 0.1)}
          params={props.params}
          x={props.x}
          y={props.y}
          editable={editable}
        />
      )}
      {mode === "series" && (
        <SeriesPanel
          term={termGiven ?? "1/n^2"}
          limit={termGiven ? limitGiven : (limitGiven ?? "pi^2/6")}
          N={intIn(props.N, 1, 1000, 100)}
          params={props.params}
          x={props.x}
          y={props.y}
          editable={editable}
        />
      )}
      {mode === "cobweb" && <CobwebPanel fn={str(props.fn)} x0={props.x0} N={intIn(props.N, 1, 200, 30)} params={props.params} x={props.x} y={props.y} editable={editable} />}
      {mode === "fourier" && <FourierPanel wave={WAVES.includes(props.wave as Wave) ? (props.wave as Wave) : "square"} N={intIn(props.N, 1, 100, 5)} x={props.x} y={props.y} />}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------------------
 * Shared pieces
 * ------------------------------------------------------------------------- */

function useParamValues(specs: ParamSpec[]) {
  const [values, setValues] = useState<Record<string, number>>(() => Object.fromEntries(specs.map((p) => [p.name, p.value])));
  const params: Vars = useMemo(() => Object.fromEntries(specs.map((p) => [p.name, values[p.name] ?? p.value])), [specs, values]);
  const reset = () => setValues(Object.fromEntries(specs.map((p) => [p.name, p.value])));
  const set = (name: string, v: number) => setValues((old) => ({ ...old, [name]: v }));
  return { params, reset, set };
}

function ParamSliders({ specs, params, onChange }: { specs: ParamSpec[]; params: Vars; onChange: (name: string, v: number) => void }) {
  if (specs.length === 0) return null;
  return (
    <div className="grid gap-x-6 gap-y-3 sm:grid-cols-2">
      {specs.map((p) => (
        <Slider
          key={p.name}
          label={<span className="font-serif text-base italic text-ink">{p.label ?? p.name}</span>}
          value={params[p.name] ?? p.value}
          min={p.min}
          max={p.max}
          step={p.step}
          onChange={(v) => onChange(p.name, v)}
          display={`${p.name} = ${fmt(params[p.name] ?? p.value, 3)}`}
        />
      ))}
    </div>
  );
}

function ToggleButton({ pressed, onClick, children }: { pressed: boolean; onClick: () => void; children: ReactNode }) {
  return (
    <button type="button" aria-pressed={pressed} className={`btn btn-sm ${pressed ? "btn-primary" : "btn-ghost"}`} onClick={onClick}>
      {children}
    </button>
  );
}

function ResetButton({ onClick }: { onClick: () => void }) {
  const { t } = useI18n();
  return (
    <button type="button" className="btn btn-sm btn-ghost" onClick={onClick}>
      <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
    </button>
  );
}

/** Leave room left of the y-axis for its tick labels. */
const padLeft = ([lo, hi]: Range): Range => [lo - (hi - lo) * 0.1, hi];
/** A little room on both sides (so points on the window's edge stay visible). */
const pad = ([lo, hi]: Range): Range => [lo - (hi - lo) * 0.07, hi + (hi - lo) * 0.03];

/** Integers through the locale formatter, everything else as a compact decimal. */
function useNum() {
  const { n } = useI18n();
  return (v: number) => (Number.isInteger(v) && Math.abs(v) < 1e15 ? n(v) : fmt(v, 4));
}

/** Read-only display of an expression (when `editable` is false). */
function FormulaLine({ prefix, src }: { prefix: ReactNode; src: string }) {
  return (
    <p className="font-serif text-lg text-ink" dir="ltr">
      <span className="italic">{prefix}</span> {prettyExpr(stripLhs(src))}
    </p>
  );
}

/* ---------------------------------------------------------------------------
 * Sequence: terms and an ε-band
 * ------------------------------------------------------------------------- */

function SequencePanel(props: { term: string; limit: string | null; N: number; epsilon: number; params: unknown; x: unknown; y: unknown; editable: boolean }) {
  const { t } = useI18n();
  const num = useNum();
  const specs = useMemo(() => toParams(props.params, ["n"]), [props.params]);
  const { params, reset: resetParams, set } = useParamValues(specs);
  const names = specs.map((p) => p.name);
  const limit0 = props.limit !== null ? toNumber(props.limit, NaN) : NaN;
  const [term, setTerm] = useState(props.term);
  const [N, setN] = useState(props.N);
  const [showLimit, setShowLimit] = useState(Number.isFinite(limit0));
  const [L, setL] = useState(Number.isFinite(limit0) ? limit0 : 0);
  const eps0 = props.epsilon > 0 ? props.epsilon : 0.1;
  const [logEps, setLogEps] = useState(Math.log10(eps0));
  const eps = Math.pow(10, logEps);
  const [hover, setHover] = useState<number | null>(null);

  const compiled = useMemo(() => compileExpr(stripLhs(term), ["n", ...names]), [term, names.join(",")]); // eslint-disable-line react-hooks/exhaustive-deps
  const a = useMemo(() => (compiled.ok ? (n: number) => compiled.fn({ ...params, n }) : () => NaN), [compiled, params]);
  const terms = useMemo(() => sequenceTerms(a, N), [a, N]);
  const M = clamp(10 * N, 2000, 20000);
  const checkTerms = useMemo(() => sequenceTerms(a, M), [a, M]);
  const result = showLimit ? epsilonIndex(checkTerms, L, eps) : null;
  const firstUndefined = terms.findIndex((v) => !Number.isFinite(v));

  const xWin: Range = Array.isArray(props.x) ? toRange(props.x, [0, N + 1]) : padLeft([0, N + Math.max(1, N * 0.04)]);
  const yWin: Range = useMemo(
    () => (Array.isArray(props.y) ? toRange(props.y, [-2, 2]) : autoRange([...terms, ...(showLimit ? [L] : [])], [-2, 2], [0])),
    [props.y, terms, showLimit, L],
  );
  const epsMax = Math.max(1, (yWin[1] - yWin[0]) / 2);
  const epsRange: Range = [Math.log10(epsMax) - 4, Math.log10(epsMax)];

  const inBand = (v: number) => Number.isFinite(v) && Math.abs(v - L) < eps;
  const shownTerm = prettyExpr(stripLhs(term));
  const hoverN = hover !== null && hover >= 1 && hover <= N ? hover : null;
  const reset = () => {
    setTerm(props.term);
    setN(props.N);
    setShowLimit(Number.isFinite(limit0));
    setL(Number.isFinite(limit0) ? limit0 : 0);
    setLogEps(Math.log10(eps0));
    resetParams();
  };

  return (
    <div className="space-y-4">
      {props.editable ? (
        <ExprField label={t("w.seq.term")} prefix={<>a<sub>n</sub> =</>} value={term} onChange={setTerm} result={compiled} />
      ) : (
        <FormulaLine prefix={<>a<sub>n</sub> =</>} src={term} />
      )}
      <Plot
        x={xWin}
        y={yWin}
        ariaLabel={t("w.seq.aria.sequence", { term: shownTerm, count: N })}
        xLabel="n"
        yLabel="aₙ"
        onHover={(p) => setHover(p ? Math.round(p[0]) : null)}
        readout={
          hoverN !== null ? (
            <span>
              a<sub>{hoverN}</sub> = {fmt(terms[hoverN - 1], 4)}
            </span>
          ) : null
        }
      >
        {(view) => (
          <>
            {showLimit && (
              <g aria-hidden="true">
                <rect x={0} width={view.W} y={view.sy(L + eps)} height={Math.max(0, view.sy(L - eps) - view.sy(L + eps))} fill="var(--gold-soft)" opacity={0.6} />
                {[L + eps, L - eps].map((v, k) => (
                  <line key={k} x1={0} x2={view.W} y1={view.sy(v)} y2={view.sy(v)} stroke="var(--gold)" strokeDasharray="5 4" strokeWidth={1} />
                ))}
                <line x1={0} x2={view.W} y1={view.sy(L)} y2={view.sy(L)} stroke="var(--gold-ink)" strokeWidth={1.75} />
              </g>
            )}
            {result?.index != null && result.index <= N && (
              <g aria-hidden="true">
                <line x1={view.sx(result.index - 0.5)} x2={view.sx(result.index - 0.5)} y1={0} y2={view.H} stroke="var(--sky)" strokeWidth={1.5} strokeDasharray="4 3" />
                <text x={view.sx(result.index - 0.5) + 5} y={16} fontSize={12} fill="var(--sky-ink)" fontWeight={600} stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                  N = {result.index}
                </text>
              </g>
            )}
            <SequenceDots view={view} terms={terms} band={showLimit ? inBand : null} hoverN={hoverN} />
          </>
        )}
      </Plot>
      {showLimit && (
        <ul className="flex flex-wrap gap-x-5 gap-y-1 text-xs text-ink-2" aria-label={t("w.seq.legend")}>
          <li className="flex items-center gap-1.5">
            <svg width="12" height="12" aria-hidden="true">
              <circle cx="6" cy="6" r="4" fill="var(--formal)" />
            </svg>
            {t("w.seq.inside")}
          </li>
          <li className="flex items-center gap-1.5">
            <svg width="12" height="12" aria-hidden="true">
              <path d="M6 1.5 10.5 6 6 10.5 1.5 6z" fill="var(--card)" stroke="var(--human)" strokeWidth="1.6" />
            </svg>
            {t("w.seq.outside")}
          </li>
          <li className="flex items-center gap-1.5">
            <svg width="22" height="12" aria-hidden="true">
              <rect width="22" height="12" fill="var(--gold-soft)" />
              <line x1="0" x2="22" y1="6" y2="6" stroke="var(--gold-ink)" strokeWidth="1.75" />
            </svg>
            {t("w.seq.band")}
          </li>
        </ul>
      )}

      <div className="grid gap-x-6 gap-y-3 sm:grid-cols-2">
        <Slider label={t("w.seq.count")} value={N} min={1} max={200} step={1} onChange={setN} display={`N = ${N}`} accent="var(--formal)" />
        <Slider
          label={t("w.seq.epsilon")}
          value={clamp(logEps, epsRange[0], epsRange[1])}
          min={epsRange[0]}
          max={epsRange[1]}
          step={0.01}
          onChange={setLogEps}
          display={`ε = ${fmt(eps, eps < 0.01 ? 5 : 3)}`}
          disabled={!showLimit}
        />
      </div>
      <div className="flex flex-wrap items-center gap-3">
        <ToggleButton pressed={showLimit} onClick={() => setShowLimit((s) => !s)}>
          {t("w.seq.testLimit")}
        </ToggleButton>
        {showLimit && <NumberField label={t("w.seq.limit")} value={L} onChange={setL} inputClassName="w-28" />}
      </div>
      <ParamSliders specs={specs} params={params} onChange={set} />

      <Readout className="space-y-2 text-sm leading-relaxed">
        {compiled.ok && (
          <p className="font-serif text-base" dir="ltr">
            a<sub>{N}</sub> = {Number.isFinite(terms[N - 1]) ? fmt(terms[N - 1], 6) : <span className="font-sans text-sm text-muted">{t("w.plot.undefined")}</span>}
          </p>
        )}
        {compiled.ok && firstUndefined >= 0 && <p className="text-ink-2">{t("w.seq.undefinedAt", { n: num(firstUndefined + 1) })}</p>}
        {!showLimit && <p className="text-ink-2">{t("w.seq.noLimit")}</p>}
        {compiled.ok && result && result.index !== null && (
          <p>
            {t("w.seq.found", { N: num(result.index), M: num(result.checked), eps: fmt(eps, 5), L: fmt(L, 5) })}
            {result.index > N && <> {t("w.seq.beyond", { count: num(N) })}</>}
          </p>
        )}
        {compiled.ok && result && result.index === null && <p>{t("w.seq.notFound", { M: num(result.checked), n: num(result.lastOutside ?? result.checked) })}</p>}
        {showLimit && <p className="text-xs text-muted">{t("w.seq.evidence")}</p>}
      </Readout>
      <ResetButton onClick={reset} />
    </div>
  );
}

function SequenceDots({ view, terms, band, hoverN }: { view: PlotView; terms: number[]; band: ((v: number) => boolean) | null; hoverN: number | null }) {
  const spacing = Math.abs(view.sx(2) - view.sx(1));
  const r = clamp(spacing * 0.38, 1.6, 4.2);
  const pts: Pt[] = terms.map((v, i) => [i + 1, v]);
  const line = pathD(
    pts.reduce<Pt[][]>((acc, p) => {
      if (Number.isFinite(p[1])) acc[acc.length - 1].push(p);
      else if (acc[acc.length - 1].length) acc.push([]);
      return acc;
    }, [[]]),
    view.sx,
    view.sy,
  );
  return (
    <g>
      <path d={line} fill="none" stroke="var(--ink-2)" strokeOpacity={0.22} strokeWidth={1} />
      {pts.map(([n, v]) => {
        if (!Number.isFinite(v)) return null;
        const X = view.sx(n);
        const Y = view.sy(v);
        if (Y < -20 || Y > view.H + 20) return null;
        const inside = band ? band(v) : true;
        return inside ? (
          <circle key={n} cx={X} cy={Y} r={r} fill="var(--formal)" />
        ) : (
          <path key={n} d={`M${X} ${Y - r * 1.25}L${X + r * 1.25} ${Y}L${X} ${Y + r * 1.25}L${X - r * 1.25} ${Y}Z`} fill="var(--card)" stroke="var(--human)" strokeWidth={1.5} />
        );
      })}
      {hoverN !== null && Number.isFinite(terms[hoverN - 1]) && <circle cx={view.sx(hoverN)} cy={view.sy(terms[hoverN - 1])} r={r + 4} fill="none" stroke="var(--sky)" strokeWidth={2} />}
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Series: partial sums
 * ------------------------------------------------------------------------- */

const SERIES_PRESETS: { term: string; limit: string | null; label: string }[] = [
  { term: "1/n^2", limit: "pi^2/6", label: "1/n²" },
  { term: "(-1)^(n+1)/n", limit: "ln(2)", label: "(−1)ⁿ⁺¹/n" },
  { term: "1/n", limit: null, label: "1/n" },
  { term: "1/2^n", limit: "1", label: "1/2ⁿ" },
  { term: "1/n!", limit: "e - 1", label: "1/n!" },
];

function SeriesPanel(props: { term: string; limit: string | null; N: number; params: unknown; x: unknown; y: unknown; editable: boolean }) {
  const { t } = useI18n();
  const num = useNum();
  const specs = useMemo(() => toParams(props.params, ["n"]), [props.params]);
  const { params, reset: resetParams, set } = useParamValues(specs);
  const names = specs.map((p) => p.name);
  const [term, setTerm] = useState(props.term);
  const [limitSrc, setLimitSrc] = useState<string | null>(props.limit);
  const [N, setN] = useState(props.N);
  const [showTerms, setShowTerms] = useState(true);
  const [logAxis, setLogAxis] = useState(false);

  const compiled = useMemo(() => compileExpr(stripLhs(term), ["n", ...names]), [term, names.join(",")]); // eslint-disable-line react-hooks/exhaustive-deps
  const a = useMemo(() => (compiled.ok ? (n: number) => compiled.fn({ ...params, n }) : () => NaN), [compiled, params]);
  const CHECK = Math.max(N, 2000);
  const allTerms = useMemo(() => sequenceTerms(a, CHECK), [a, CHECK]);
  const terms = allTerms.slice(0, N);
  const sums = useMemo(() => partialSums(allTerms.slice(0, N)), [allTerms, N]);
  const L = limitSrc !== null ? toNumber(limitSrc, NaN, params) : NaN;
  const harmonic = useMemo(() => compiled.ok && looksHarmonic(a), [compiled, a]);
  const noVanish = useMemo(() => termsDoNotVanish(allTerms), [allTerms]);
  const SN = sums[N - 1];

  const X = (n: number) => (logAxis ? Math.log10(n) : n);
  const xWin: Range = Array.isArray(props.x) && !logAxis ? toRange(props.x, [0, N + 1]) : padLeft(logAxis ? [0, Math.log10(Math.max(N, 2)) + 0.08] : [0, N + Math.max(1, N * 0.04)]);
  const yWin: Range = useMemo(
    () => (Array.isArray(props.y) ? toRange(props.y, [-2, 2]) : autoRange([...sums, ...(showTerms ? terms : []), ...(Number.isFinite(L) ? [L] : []), 0], [-1, 2], [0])),
    [props.y, sums, terms, showTerms, L],
  );
  const shownTerm = prettyExpr(stripLhs(term));
  const presetActive = (p: (typeof SERIES_PRESETS)[number]) => stripLhs(term).replace(/\s+/g, "") === p.term;
  const reset = () => {
    setTerm(props.term);
    setLimitSrc(props.limit);
    setN(props.N);
    setShowTerms(true);
    setLogAxis(false);
    resetParams();
  };

  return (
    <div className="space-y-4">
      {props.editable && (
        <div className="flex flex-wrap items-center gap-2" role="group" aria-label={t("w.seq.presets")}>
          <span className="text-sm font-semibold text-ink-2">{t("w.seq.presets")}</span>
          {SERIES_PRESETS.map((p) => (
            <button
              key={p.term}
              type="button"
              aria-pressed={presetActive(p)}
              className={`btn btn-sm font-serif ${presetActive(p) ? "btn-primary" : "btn-ghost"}`}
              onClick={() => {
                setTerm(p.term);
                setLimitSrc(p.limit);
              }}
            >
              <span dir="ltr">Σ {p.label}</span>
            </button>
          ))}
        </div>
      )}
      {props.editable ? (
        <ExprField label={t("w.seq.termSeries")} prefix={<>a<sub>n</sub> =</>} value={term} onChange={(v) => { setTerm(v); setLimitSrc(null); }} result={compiled} />
      ) : (
        <FormulaLine prefix={<>a<sub>n</sub> =</>} src={term} />
      )}
      <Plot
        x={xWin}
        y={yWin}
        xTicks={logAxis ? "none" : "auto"}
        ariaLabel={t("w.seq.aria.series", { term: shownTerm, count: N })}
        xLabel="n"
        yLabel="Sₙ"
      >
        {(view) => (
          <>
            {logAxis && <LogTicks view={view} N={N} />}
            {Number.isFinite(L) && (
              <g aria-hidden="true">
                <line x1={0} x2={view.W} y1={view.sy(L)} y2={view.sy(L)} stroke="var(--gold-ink)" strokeWidth={1.5} strokeDasharray="7 5" />
                <text x={view.W - 8} y={view.sy(L) - 6} textAnchor="end" fontSize={12} fill="var(--gold-ink)" fontWeight={600} stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
                  L ≈ {fmt(L, 4)}
                </text>
              </g>
            )}
            {showTerms && <TermBars view={view} terms={terms} X={X} />}
            <SumsPath view={view} sums={sums} X={X} />
            {harmonic && <HarmonicCurve view={view} N={N} logAxis={logAxis} />}
          </>
        )}
      </Plot>
      <ul className="flex flex-wrap gap-x-5 gap-y-1 text-xs text-ink-2" aria-label={t("w.seq.legend")}>
        <li className="flex items-center gap-1.5">
          <LegendSwatch color="var(--formal)" />
          {t("w.seq.partialSums")}
        </li>
        {showTerms && (
          <li className="flex items-center gap-1.5">
            <svg width="14" height="12" aria-hidden="true">
              <rect x="5" y="1" width="3" height="11" fill="var(--compute)" opacity="0.6" />
            </svg>
            {t("w.seq.termsLegend")}
          </li>
        )}
        {Number.isFinite(L) && (
          <li className="flex items-center gap-1.5">
            <LegendSwatch color="var(--gold-ink)" dash="7 5" width={2} />
            {t("w.seq.knownSum")}
          </li>
        )}
        {harmonic && (
          <li className="flex items-center gap-1.5">
            <LegendSwatch color="var(--sky)" dash="3 4" width={2} />
            <span dir="ltr">{t("w.seq.harmonicCurve")}</span>
          </li>
        )}
      </ul>

      <Slider label={t("w.seq.sumsUpTo")} value={N} min={1} max={1000} step={1} onChange={setN} display={`N = ${N}`} accent="var(--formal)" />
      <div className="flex flex-wrap gap-2">
        <ToggleButton pressed={showTerms} onClick={() => setShowTerms((s) => !s)}>
          {t("w.seq.showTerms")}
        </ToggleButton>
        <ToggleButton pressed={logAxis} onClick={() => setLogAxis((s) => !s)}>
          {t("w.seq.logAxis")}
        </ToggleButton>
      </div>
      <ParamSliders specs={specs} params={params} onChange={set} />

      <Readout className="space-y-2 text-sm leading-relaxed">
        {compiled.ok && (
          <p className="font-serif text-base" dir="ltr">
            S<sub>{N}</sub> = a<sub>1</sub> + … + a<sub>{N}</sub> = {Number.isFinite(SN) ? <strong>{fmt(SN, 6)}</strong> : <span className="font-sans text-sm text-muted">{t("w.plot.undefined")}</span>}
          </p>
        )}
        {compiled.ok && Number.isFinite(L) && (
          <p className="text-ink-2">
            {t("w.seq.knownSum")}:{" "}
            <span dir="ltr" className="font-serif text-base">
              L = {limitSrc !== null && !/^\s*-?[\d.]+\s*$/.test(limitSrc) ? `${prettyExpr(limitSrc)} ≈ ` : ""}
              {fmt(L, 6)}
            </span>
            {Number.isFinite(SN) && (
              <>
                {" · "}
                {t("w.seq.gap")}:{" "}
                <span dir="ltr" className="font-serif text-base">
                  L − S<sub>{N}</sub> ≈ {fmt(L - SN, 6)}
                </span>
              </>
            )}
          </p>
        )}
        {harmonic && <p>{t("w.seq.harmonic")}</p>}
        {compiled.ok && noVanish && !harmonic && <p>{t("w.seq.termTest", { v: fmt(Math.abs(allTerms[allTerms.length - 1]), 3), n: num(allTerms.length) })}</p>}
        <p className="text-xs text-muted">{t("w.seq.seriesEvidence")}</p>
      </Readout>
      <ResetButton onClick={reset} />
    </div>
  );
}

function LogTicks({ view, N }: { view: PlotView; N: number }) {
  const lines: { u: number; major: boolean; label?: string }[] = [];
  for (let k = 0; Math.pow(10, k) <= Math.max(N, 10) * 1.0001 && k <= 6; k++) {
    for (let m = 1; m <= 9; m++) {
      const v = m * Math.pow(10, k);
      if (v > N * 1.2 && m > 1) break;
      lines.push({ u: Math.log10(v), major: m === 1, label: m === 1 ? String(v) : undefined });
    }
  }
  const Y0 = view.sy(0);
  const ly = Y0 >= 0 && Y0 <= view.H ? (Y0 + 16 > view.H - 4 ? Y0 - 6 : Y0 + 15) : view.H - 6;
  return (
    <g aria-hidden="true">
      {lines.map((l) => (
        <line key={l.u} x1={view.sx(l.u)} x2={view.sx(l.u)} y1={0} y2={view.H} stroke="var(--line)" strokeOpacity={l.major ? 1 : 0.5} strokeWidth={l.major ? 1 : 0.75} />
      ))}
      {lines
        .filter((l) => l.label && l.u > 0 && view.sx(l.u) > 10 && view.sx(l.u) < view.W - 10)
        .map((l) => (
          <text key={`t${l.u}`} x={view.sx(l.u)} y={ly} textAnchor="middle" fontSize={11} fill="var(--muted)" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
            {l.label}
          </text>
        ))}
    </g>
  );
}

function TermBars({ view, terms, X }: { view: PlotView; terms: number[]; X: (n: number) => number }) {
  const Y0 = view.sy(0);
  let d = "";
  terms.forEach((v, i) => {
    if (!Number.isFinite(v)) return;
    const px = view.sx(X(i + 1)).toFixed(2);
    d += `M${px} ${Y0.toFixed(2)}V${clamp(view.sy(v), -10, view.H + 10).toFixed(2)}`;
  });
  const spacing = terms.length > 1 ? Math.abs(view.sx(X(terms.length)) - view.sx(X(terms.length - 1))) : 8;
  return <path d={d} stroke="var(--compute)" strokeOpacity={0.55} strokeWidth={clamp(spacing * 0.45, 1, 5)} fill="none" aria-hidden="true" />;
}

function SumsPath({ view, sums, X }: { view: PlotView; sums: number[]; X: (n: number) => number }) {
  const pts: Pt[][] = [[]];
  sums.forEach((v, i) => {
    if (Number.isFinite(v)) pts[pts.length - 1].push([X(i + 1), v]);
    else if (pts[pts.length - 1].length) pts.push([]);
  });
  const dots = sums.length <= 150;
  return (
    <g>
      <path d={pathD(pts, view.sx, view.sy)} fill="none" stroke="var(--formal)" strokeWidth={dots ? 1.25 : 2.5} strokeOpacity={dots ? 0.5 : 1} strokeLinejoin="round" />
      {dots && sums.map((v, i) => (Number.isFinite(v) ? <circle key={i} cx={view.sx(X(i + 1))} cy={view.sy(v)} r={sums.length > 60 ? 2.2 : 3.2} fill="var(--formal)" /> : null))}
    </g>
  );
}

function HarmonicCurve({ view, N, logAxis }: { view: PlotView; N: number; logAxis: boolean }) {
  const f = (u: number) => {
    const n = logAxis ? Math.pow(10, u) : u;
    return n >= 1 ? Math.log(n) + EULER_GAMMA : NaN;
  };
  const lines = sampleFunction(f, [logAxis ? 0 : 1, logAxis ? Math.log10(Math.max(N, 2)) : N], { y: view.y, n: 300 });
  return <path d={pathD(lines, view.sx, view.sy)} fill="none" stroke="var(--sky)" strokeWidth={2} strokeDasharray="3 4" aria-hidden="true" />;
}

/* ---------------------------------------------------------------------------
 * Cobweb: iterating a map
 * ------------------------------------------------------------------------- */

const LOGISTIC_PARAMS = [{ name: "r", min: 0, max: 4, step: 0.01, value: 2.8 }];

function CobwebPanel(props: { fn: string | null; x0: unknown; N: number; params: unknown; x: unknown; y: unknown; editable: boolean }) {
  const { t } = useI18n();
  const num = useNum();
  const fn0 = props.fn ?? "r*x*(1-x)";
  const specs = useMemo(() => toParams(props.params ?? (props.fn === null ? LOGISTIC_PARAMS : undefined), ["x"]), [props.params, props.fn]);
  const { params, reset: resetParams, set } = useParamValues(specs);
  const names = specs.map((p) => p.name);
  const xWin = toRange(props.x, [0, 1]);
  const yWin = Array.isArray(props.y) ? toRange(props.y, xWin) : xWin;
  const x00 = clamp(toNumber(props.x0, xWin[0] + 0.2 * (xWin[1] - xWin[0])), xWin[0], xWin[1]);
  const [fnSrc, setFnSrc] = useState(fn0);
  const [x0, setX0] = useState(x00);
  const [K, setK] = useState(props.N);

  const compiled = useMemo(() => compileExpr(stripLhs(fnSrc), ["x", ...names]), [fnSrc, names.join(",")]); // eslint-disable-line react-hooks/exhaustive-deps
  const f = useMemo(() => (compiled.ok ? (x: number) => compiled.fn({ ...params, x }) : () => NaN), [compiled, params]);
  const run = useMemo(() => iterate(f, x0, K), [f, x0, K]);
  const orbit = useMemo(() => (compiled.ok ? classifyOrbit(f, x0) : null), [compiled, f, x0]);
  const fps = useMemo(() => (compiled.ok ? fixedPoints(f, xWin) : []), [compiled, f, xWin[0], xWin[1]]); // eslint-disable-line react-hooks/exhaustive-deps
  const xs = run.xs;
  const yBase = clamp(0, yWin[0], yWin[1]);
  const shownFn = prettyExpr(stripLhs(fnSrc));
  const last = xs.slice(-3).map((v, i) => ({ k: xs.length - Math.min(3, xs.length) + i, v }));
  const reset = () => {
    setFnSrc(fn0);
    setX0(x00);
    setK(props.N);
    resetParams();
  };

  const orbitText = (() => {
    if (!orbit) return null;
    switch (orbit.kind) {
      case "fixed":
        return t("w.seq.orbit.fixed", { x: fmt(orbit.value, 5) });
      case "cycle":
        return t("w.seq.orbit.cycle", { p: num(orbit.period), values: orbit.values.map((v) => fmt(v, 4)).join(", ") });
      case "slow":
        return t("w.seq.orbit.slow", { x: fmt(orbit.value, 4) });
      case "chaos":
        return t("w.seq.orbit.chaos", { k: num(orbit.iterations) });
      case "escape":
        return t("w.seq.orbit.escape");
      default:
        return t("w.seq.orbit.undefined");
    }
  })();

  return (
    <div className="space-y-4">
      {props.editable ? (
        <ExprField label={t("w.seq.fn")} prefix="f(x) =" value={fnSrc} onChange={setFnSrc} result={compiled} />
      ) : (
        <FormulaLine prefix="f(x) =" src={fnSrc} />
      )}
      <div className="grid gap-4 md:grid-cols-[minmax(0,1fr)_minmax(0,1fr)] md:items-start">
        <div className="mx-auto w-full max-w-[420px]">
          <Plot x={pad(xWin)} y={pad(yWin)} aspect="equal" minHeight={200} maxHeight={420} defaultWidth={380} ariaLabel={t("w.seq.aria.cobweb", { fn: shownFn, x0: fmt(x0, 3), k: K })} xLabel="x" yLabel="y" above={() => <PlotHandle x={x0} y={yBase} label="x₀" tag="x₀" color="var(--human)" constrain={(p) => [p[0], yBase]} onMove={(p) => setX0(p[0])} step={(xWin[1] - xWin[0]) / 100} />}>
            {(view) => <CobwebLayer view={view} f={f} xs={xs} yBase={yBase} fps={fps} />}
          </Plot>
        </div>
        <div className="space-y-2">
          <p className="text-sm font-semibold text-ink-2">{t("w.seq.timeSeries")}</p>
          <Plot x={padLeft([0, Math.max(K, 1) + 0.5])} y={pad(yWin)} aspect={0.55} minHeight={150} maxHeight={260} defaultWidth={380} ariaLabel={t("w.seq.aria.timeSeries", { k: K })} xLabel="k" yLabel="xₖ">
            {(view) => <TimeSeries view={view} xs={xs} />}
          </Plot>
          <ul className="flex flex-wrap gap-x-4 gap-y-1 pt-1 text-xs text-ink-2" aria-label={t("w.seq.legend")}>
            <li className="flex items-center gap-1.5">
              <LegendSwatch color="var(--formal)" />
              <span dir="ltr" className="font-serif">y = f(x)</span>
            </li>
            <li className="flex items-center gap-1.5">
              <LegendSwatch color="var(--muted)" dash="4 4" width={1.5} />
              <span dir="ltr" className="font-serif">y = x</span>
            </li>
            <li className="flex items-center gap-1.5">
              <LegendSwatch color="var(--human)" width={1.75} />
              {t("w.seq.cobwebPath")}
            </li>
          </ul>
        </div>
      </div>

      <div className="grid gap-x-6 gap-y-3 sm:grid-cols-2">
        <Slider label={t("w.seq.x0")} value={x0} min={xWin[0]} max={xWin[1]} step={(xWin[1] - xWin[0]) / 500} onChange={setX0} display={`x₀ = ${fmt(x0, 3)}`} accent="var(--human)" />
        <Slider label={t("w.seq.steps")} value={K} min={1} max={200} step={1} onChange={setK} display={`k = ${K}`} accent="var(--formal)" />
      </div>
      <ParamSliders specs={specs} params={params} onChange={set} />

      <Readout className="space-y-2 text-sm leading-relaxed">
        {xs.length > 0 && (
          <p className="text-ink-2">
            {t("w.seq.lastIterates")}:{" "}
            <span dir="ltr" className="font-serif text-base text-ink">
              {last.map(({ k, v }, i) => (
                <span key={k} className="whitespace-nowrap">
                  {i > 0 && ", "}x<sub>{k}</sub> = {fmt(v, 5)}
                </span>
              ))}
            </span>
          </p>
        )}
        {orbitText && <p>{orbitText}</p>}
        {compiled.ok && (
          <p className="text-ink-2">
            <span className="font-semibold">{t("w.seq.fixedPoints")}:</span>{" "}
            {fps.length === 0
              ? t("w.seq.noFixed")
              : fps.map((p, i) => (
                  <span key={i}>
                    {i > 0 && "; "}
                    <span dir="ltr" className="font-serif">
                      x* = {fmt(p.x, 4)}
                    </span>{" "}
                    ({t(`w.seq.fp.${p.kind}`)})
                  </span>
                ))}
          </p>
        )}
        <p className="text-xs text-muted">{t("w.seq.orbitNote", { k: num(3000) })}</p>
      </Readout>
      <ResetButton onClick={reset} />
    </div>
  );
}

function CobwebLayer({ view, f, xs, yBase, fps }: { view: PlotView; f: (x: number) => number; xs: number[]; yBase: number; fps: { x: number; kind: string }[] }) {
  const { sx, sy } = view;
  const curve = useMemo(() => pathD(sampleFunction(f, view.x, { y: view.y, n: 500 }), sx, sy), [f, view.x[0], view.x[1], view.y[0], view.y[1], view.W]); // eslint-disable-line react-hooks/exhaustive-deps
  const lo = Math.min(view.x[0], view.y[0]);
  const hi = Math.max(view.x[1], view.y[1]);
  const segs: { d: string; o: number }[] = [];
  if (xs.length > 0) {
    const steps = xs.length - 1;
    const op = (k: number) => (steps <= 1 ? 1 : 0.45 + (0.55 * k) / (steps - 1));
    segs.push({ d: `M${sx(xs[0])} ${sy(yBase)}V${sy(xs[1] ?? yBase)}`, o: op(0) });
    for (let k = 1; k < xs.length - 1; k++) {
      segs.push({ d: `M${sx(xs[k - 1])} ${sy(xs[k])}H${sx(xs[k])}V${sy(xs[k + 1])}`, o: op(k) });
    }
    if (xs.length >= 2) segs.push({ d: `M${sx(xs[xs.length - 2])} ${sy(xs[xs.length - 1])}H${sx(xs[xs.length - 1])}`, o: 1 });
  }
  return (
    <g>
      <line x1={sx(lo)} y1={sy(lo)} x2={sx(hi)} y2={sy(hi)} stroke="var(--muted)" strokeWidth={1.5} strokeDasharray="4 4" />
      <path d={curve} fill="none" stroke="var(--formal)" strokeWidth={2.5} strokeLinejoin="round" />
      {segs.map((s, i) => (
        <path key={i} d={s.d} fill="none" stroke="var(--human)" strokeWidth={1.6} strokeOpacity={s.o} strokeLinejoin="round" />
      ))}
      {fps.map((p, i) => (
        <circle key={i} cx={sx(p.x)} cy={sy(p.x)} r={5} fill={p.kind === "attracting" ? "var(--ink)" : "var(--card)"} stroke="var(--ink)" strokeWidth={2} />
      ))}
    </g>
  );
}

function TimeSeries({ view, xs }: { view: PlotView; xs: number[] }) {
  const pts: Pt[] = xs.map((v, k) => [k, v]);
  const r = clamp(Math.abs(view.sx(1) - view.sx(0)) * 0.35, 1.4, 3.5);
  return (
    <g>
      <path d={pathD([pts], view.sx, view.sy)} fill="none" stroke="var(--human)" strokeWidth={1.4} strokeOpacity={0.6} strokeLinejoin="round" />
      {pts.map(([k, v]) => (
        <circle key={k} cx={view.sx(k)} cy={view.sy(v)} r={r} fill={k === 0 ? "var(--card)" : "var(--human)"} stroke="var(--human)" strokeWidth={k === 0 ? 1.5 : 0} />
      ))}
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Fourier partial sums
 * ------------------------------------------------------------------------- */

const WAVE_Y: Record<Wave, Range> = { square: [-1.6, 1.6], sawtooth: [-4.6, 4.6], triangle: [-1.5, 1.5] };

function FourierFormula({ wave }: { wave: Wave }) {
  const sum = (
    <span className="mx-0.5 inline-flex flex-col items-center align-middle leading-none">
      <span className="text-[0.62em]">N</span>
      <span className="text-[1.25em] leading-none">Σ</span>
      <span className="text-[0.62em]">k=1</span>
    </span>
  );
  if (wave === "square")
    return (
      <>
        S<sub>N</sub>(x) = (4/π) {sum} sin((2k − 1)x) / (2k − 1)
      </>
    );
  if (wave === "sawtooth")
    return (
      <>
        S<sub>N</sub>(x) = 2 {sum} (−1)<sup>k+1</sup> sin(kx) / k
      </>
    );
  return (
    <>
      S<sub>N</sub>(x) = (8/π²) {sum} (−1)<sup>k−1</sup> sin((2k − 1)x) / (2k − 1)²
    </>
  );
}

function FourierPanel(props: { wave: Wave; N: number; x: unknown; y: unknown }) {
  const { t } = useI18n();
  const [wave, setWave] = useState<Wave>(props.wave);
  const [N, setN] = useState(props.N);
  const xWin = toRange(props.x, [-2 * Math.PI, 2 * Math.PI]);
  const yWin = Array.isArray(props.y) ? toRange(props.y, WAVE_Y[wave]) : WAVE_Y[wave];
  const gibbs = useMemo(() => gibbsOvershoot(wave, N), [wave, N]);
  const err = useMemo(() => (wave === "triangle" ? maxFourierError(wave, N) : NaN), [wave, N]);
  const jump = wave === "square" ? "2" : "2π";

  return (
    <div className="space-y-4">
      <ModeTabs value={wave} options={WAVES} onChange={setWave} label={t("w.seq.waves")} render={(w) => t(`w.seq.wave.${w}`)} />
      <Plot x={xWin} y={yWin} ariaLabel={t("w.seq.aria.fourier", { wave: t(`w.seq.wave.${wave}`), count: N })} xLabel="x" yLabel="y">
        {(view) => <FourierLayer view={view} wave={wave} N={N} gibbs={gibbs} />}
      </Plot>
      <ul className="flex flex-wrap gap-x-5 gap-y-1 text-xs text-ink-2" aria-label={t("w.seq.legend")}>
        <li className="flex items-center gap-1.5">
          <LegendSwatch color="var(--ink-2)" dash="6 4" width={2} />
          {t("w.seq.target")}
        </li>
        <li className="flex items-center gap-1.5">
          <LegendSwatch color="var(--formal)" />
          {t("w.seq.partial")}
        </li>
        {gibbs && gibbs.overshoot > 0 && (
          <li className="flex items-center gap-1.5">
            <svg width="12" height="12" aria-hidden="true">
              <circle cx="6" cy="6" r="4" fill="var(--human)" />
            </svg>
            {t("w.seq.peak")}
          </li>
        )}
      </ul>
      <Slider label={t("w.seq.harmonics")} value={N} min={1} max={100} step={1} onChange={setN} display={`N = ${N}`} accent="var(--formal)" />
      <Readout className="space-y-2 text-sm leading-relaxed">
        <p className="overflow-x-auto font-serif text-base" dir="ltr">
          <FourierFormula wave={wave} />
        </p>
        <p className="text-ink-2">{t(`w.seq.def.${wave}`)}</p>
        {gibbs && gibbs.overshoot > 0 && (
          <p>{t("w.seq.gibbs", { peak: fmt(gibbs.peak, 4), over: fmt(gibbs.overshoot, 4), pct: (gibbs.fraction * 100).toFixed(1), jump })}</p>
        )}
        {gibbs && gibbs.overshoot <= 0 && <p>{t("w.seq.gibbsNone")}</p>}
        {gibbs && <p className="text-ink-2">{t("w.seq.gibbsNote")}</p>}
        {wave === "triangle" && <p>{t("w.seq.uniform", { err: fmt(err, 4) })}</p>}
      </Readout>
    </div>
  );
}

function FourierLayer({ view, wave, N, gibbs }: { view: PlotView; wave: Wave; N: number; gibbs: { x: number; peak: number; overshoot: number } | null }) {
  const { sx, sy } = view;
  const target = useMemo(() => pathD(sampleFunction((x) => waveValue(wave, x), view.x, { y: view.y, n: 600 }), sx, sy), [wave, view.x[0], view.x[1], view.y[0], view.y[1], view.W]); // eslint-disable-line react-hooks/exhaustive-deps
  const partial = useMemo(
    () => pathD(sampleFunction((x) => fourierPartial(wave, N, x), view.x, { y: view.y, n: clamp(30 * N, 800, 3200) }), sx, sy),
    [wave, N, view.x[0], view.x[1], view.y[0], view.y[1], view.W], // eslint-disable-line react-hooks/exhaustive-deps
  );
  return (
    <g>
      <path d={target} fill="none" stroke="var(--ink-2)" strokeWidth={2} strokeDasharray="6 4" strokeOpacity={0.8} />
      <path d={partial} fill="none" stroke="var(--formal)" strokeWidth={2.25} strokeLinejoin="round" />
      {gibbs && gibbs.overshoot > 0 && (
        <g aria-hidden="true">
          <line x1={sx(gibbs.x) - 40} x2={sx(gibbs.x) + 40} y1={sy(gibbs.peak)} y2={sy(gibbs.peak)} stroke="var(--human)" strokeWidth={1.25} strokeDasharray="2 3" />
          <circle cx={sx(gibbs.x)} cy={sy(gibbs.peak)} r={4.5} fill="var(--human)" stroke="var(--card)" strokeWidth={2} />
          <text x={sx(gibbs.x) + (wave === "sawtooth" ? -10 : 10)} y={sy(gibbs.peak) - 9} textAnchor={wave === "sawtooth" ? "end" : "start"} fontSize={12} fontWeight={600} fill="var(--human)" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke">
            {fmt(gibbs.peak, 3)}
          </text>
        </g>
      )}
    </g>
  );
}
