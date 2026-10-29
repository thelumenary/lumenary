"use client";

import { Car, Dices, Play, RotateCcw } from "lucide-react";
import { useEffect, useId, useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  binomialPmf,
  birthdayExact,
  birthdayGroups,
  buffonEstimate,
  ci95,
  dropNeedles,
  flipCoins,
  galton,
  montyGame,
  montyHall,
  mulberry32,
  normalPdf,
  randomWalks,
  rollDice,
  runningProportion,
  seedFor,
  tally,
  trialSteps,
  twoDiceExact,
} from "./lib/chance-core";

export const EXPERIMENTS = ["coin", "dice", "two-dice", "galton", "random-walk", "birthday", "monty-hall", "buffon"] as const;
export type Experiment = (typeof EXPERIMENTS)[number];
const isExperiment = (v: unknown): v is Experiment => typeof v === "string" && (EXPERIMENTS as readonly string[]).includes(v);

const DEFAULT_TRIALS: Record<Experiment, number> = { coin: 500, dice: 600, "two-dice": 1000, galton: 500, "random-walk": 200, birthday: 1000, "monty-hall": 500, buffon: 500 };
const SIM = "var(--compute)";
const EXACT = "var(--formal)";

export interface ChanceLabProps {
  experiment?: string;
  experiments?: string[];
  trials?: number;
  n?: number;
  k?: number;
  title?: string;
  subtitle?: string;
}

const clampInt = (v: unknown, lo: number, hi: number, dflt: number) => {
  const x = typeof v === "number" ? v : typeof v === "string" ? Number(v) : NaN;
  return Number.isFinite(x) ? Math.round(Math.min(hi, Math.max(lo, x))) : dflt;
};

/** Probability experiments: a seeded simulation always shown beside the exact value. */
export function ChanceLab({ experiment, experiments, trials, n, k, title, subtitle }: ChanceLabProps) {
  const { t } = useI18n();
  const offered = useMemo<Experiment[]>(() => {
    const list = Array.isArray(experiments) ? [...new Set(experiments.filter(isExperiment))] : [];
    if (list.length) return list;
    return isExperiment(experiment) && !Array.isArray(experiments) && experiment ? [experiment] : [...EXPERIMENTS];
  }, [experiments, experiment]);
  const [exp, setExp] = useState<Experiment>(isExperiment(experiment) && offered.includes(experiment) ? experiment : offered[0]);

  return (
    <WidgetFrame title={title ?? t("w.chance.title")} subtitle={subtitle ?? t(`w.chance.sub.${exp}`)}>
      {offered.length > 1 && (
        <div className="mb-4 flex flex-wrap gap-2">
          {offered.map((e) => (
            <button key={e} type="button" aria-pressed={exp === e} className={`btn btn-sm ${exp === e ? "btn-primary" : "btn-ghost"}`} onClick={() => setExp(e)}>
              {t(`w.chance.exp.${e}`)}
            </button>
          ))}
        </div>
      )}
      <Lab key={exp} exp={exp} trials={trials} n={n} k={k} />
    </WidgetFrame>
  );
}

/* ------------------------------------------------------------------------ */
/* Run / replay animation                                                    */
/* ------------------------------------------------------------------------ */

function useRun() {
  const [run, setRun] = useState(0);
  const [frac, setFrac] = useState(1);
  const [playing, setPlaying] = useState(false);
  useEffect(() => {
    if (!playing) return;
    let raf = 0;
    const t0 = performance.now();
    const tick = (now: number) => {
      const f = Math.min(1, (now - t0) / 1800);
      setFrac(f);
      if (f < 1) raf = requestAnimationFrame(tick);
      else setPlaying(false);
    };
    raf = requestAnimationFrame(tick);
    return () => cancelAnimationFrame(raf);
  }, [playing, run]);
  const start = (next: boolean) => {
    if (next) setRun((r) => r + 1);
    const reduce = typeof window !== "undefined" && typeof window.matchMedia === "function" && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    if (reduce) {
      setFrac(1);
      setPlaying(false);
    } else {
      setFrac(0);
      setPlaying(true);
    }
  };
  return { run, frac, playing, newRun: () => start(true), replay: () => start(false) };
}

/* ------------------------------------------------------------------------ */
/* Chart helpers                                                             */
/* ------------------------------------------------------------------------ */

interface Frame {
  W: number;
  H: number;
  L: number;
  R: number;
  T: number;
  B: number;
  x0: number;
  x1: number;
  y0: number;
  y1: number;
}
const X = (f: Frame, v: number) => f.L + ((v - f.x0) / (f.x1 - f.x0 || 1)) * (f.W - f.L - f.R);
const Y = (f: Frame, v: number) => f.H - f.B - ((v - f.y0) / (f.y1 - f.y0 || 1)) * (f.H - f.T - f.B);
const frame = (x0: number, x1: number, y0: number, y1: number, W = 420, H = 260): Frame => ({ W, H, L: 50, R: 14, T: 12, B: 40, x0, x1, y0, y1 });
const pts = (list: [number, number][]) => list.map(([x, y]) => `${x.toFixed(1)},${y.toFixed(1)}`).join(" ");

function niceTicks(lo: number, hi: number, count = 5): number[] {
  const span = hi - lo;
  if (span <= 0) return [lo];
  const raw = span / count;
  const mag = 10 ** Math.floor(Math.log10(raw));
  const step = [1, 2, 2.5, 5, 10].map((m) => m * mag).find((s) => span / s <= count) ?? 10 * mag;
  const out: number[] = [];
  for (let v = Math.ceil(lo / step) * step; v <= hi + 1e-9; v += step) out.push(Math.round(v * 1e6) / 1e6);
  return out;
}

function Axes({ f, xTicks, yTicks, fx, fy, xLabel, yLabel }: { f: Frame; xTicks: number[]; yTicks: number[]; fx: (v: number) => string; fy: (v: number) => string; xLabel?: string; yLabel?: string }) {
  return (
    <g fontSize="12" fill="var(--muted)">
      {yTicks.map((v) => (
        <g key={`y${v}`}>
          <line x1={f.L} x2={f.W - f.R} y1={Y(f, v)} y2={Y(f, v)} stroke="var(--line)" strokeWidth="1" />
          <text x={f.L - 6} y={Y(f, v) + 4} textAnchor="end">
            {fy(v)}
          </text>
        </g>
      ))}
      {xTicks.map((v) => (
        <text key={`x${v}`} x={X(f, v)} y={f.H - f.B + 16} textAnchor="middle">
          {fx(v)}
        </text>
      ))}
      <line x1={f.L} x2={f.W - f.R} y1={f.H - f.B} y2={f.H - f.B} stroke="var(--ink-2)" strokeWidth="1" />
      {xLabel && (
        <text x={(f.L + f.W - f.R) / 2} y={f.H - 4} textAnchor="middle" fontSize="12.5" fill="var(--ink-2)">
          {xLabel}
        </text>
      )}
      {yLabel && (
        <text transform="rotate(-90)" x={-(f.T + f.H - f.B) / 2} y={12} textAnchor="middle" fontSize="12.5" fill="var(--ink-2)">
          {yLabel}
        </text>
      )}
    </g>
  );
}

type LegendItem = { kind: "bar" | "line" | "dash" | "dot" | "band"; color: string; label: string };
function Legend({ items }: { items: LegendItem[] }) {
  return (
    <ul className="mt-2 flex list-none flex-wrap gap-x-4 gap-y-1 !ps-0 text-xs text-ink-2">
      {items.map((it) => (
        <li key={it.label} className="flex items-center gap-1.5">
          <svg width="22" height="10" aria-hidden="true">
            {it.kind === "bar" && <rect x="5" y="0" width="12" height="10" rx="2" fill={it.color} opacity="0.75" />}
            {it.kind === "band" && <rect x="0" y="1" width="22" height="8" rx="2" fill={it.color} opacity="0.18" />}
            {it.kind === "line" && <line x1="0" y1="5" x2="22" y2="5" stroke={it.color} strokeWidth="2.5" />}
            {it.kind === "dash" && <line x1="0" y1="5" x2="22" y2="5" stroke={it.color} strokeWidth="2" strokeDasharray="5 3" />}
            {it.kind === "dot" && <path d="M11 0.5 15.5 5 11 9.5 6.5 5z" fill="var(--card)" stroke={it.color} strokeWidth="1.8" />}
          </svg>
          {it.label}
        </li>
      ))}
    </ul>
  );
}

function Row({ label, sim, exact }: { label: string; sim: React.ReactNode; exact?: React.ReactNode }) {
  const { t } = useI18n();
  return (
    <div className="rounded-xl bg-paper-2 px-3.5 py-2.5">
      <p className="text-xs font-semibold text-muted">{label}</p>
      <div className="mt-1 grid grid-cols-2 gap-2 text-sm">
        <p>
          <span className="block text-[0.7rem] font-semibold uppercase tracking-wide text-compute">{t("w.chance.simulated")}</span>
          <span className="font-mono text-base text-ink" dir="ltr">
            {sim}
          </span>
        </p>
        {exact !== undefined && (
          <p>
            <span className="block text-[0.7rem] font-semibold uppercase tracking-wide text-formal">{t("w.chance.exact")}</span>
            <span className="font-mono text-base text-ink" dir="ltr">
              {exact}
            </span>
          </p>
        )}
      </div>
    </div>
  );
}

function Slider({ label, value, display, min, max, onChange, step = 1 }: { label: string; value: number; display: string; min: number; max: number; step?: number; onChange: (v: number) => void }) {
  return (
    <label className="block text-sm font-semibold text-ink-2">
      <span className="flex items-center justify-between gap-2">
        {label}
        <span className="font-mono text-ink" dir="ltr">
          {display}
        </span>
      </span>
      <input type="range" min={min} max={max} step={step} value={value} onChange={(e) => onChange(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--compute)]" dir="ltr" />
    </label>
  );
}

/* ------------------------------------------------------------------------ */
/* One experiment                                                            */
/* ------------------------------------------------------------------------ */

function Lab({ exp, trials, n: nProp, k: kProp }: { exp: Experiment; trials?: number; n?: number; k?: number }) {
  const { t, n } = useI18n();
  // Random walks cost walkers × steps, so they stop at 2,000 walkers.
  const steps = useMemo(() => trialSteps(typeof trials === "number" ? trials : undefined).filter((s) => exp !== "random-walk" || s <= 2000), [trials, exp]);
  const initialTrials = clampInt(trials, 10, exp === "random-walk" ? 2000 : 10000, DEFAULT_TRIALS[exp]);
  const [tIdx, setTIdx] = useState(() => {
    const i = steps.findIndex((s) => s >= initialTrials);
    return i < 0 ? steps.length - 1 : i;
  });
  const total = steps[tIdx];
  const [rows, setRows] = useState(clampInt(nProp, 1, 20, 10));
  const [walkSteps, setWalkSteps] = useState(Math.round(clampInt(nProp, 10, 1000, 100) / 10) * 10);
  const [group, setGroup] = useState(clampInt(kProp, 2, 100, 23));
  const { run, frac, playing, newRun, replay } = useRun();
  const sim = useMemo(() => simulate(exp, run, total, rows, walkSteps, group), [exp, run, total, rows, walkSteps, group]);
  const shown = Math.max(1, Math.ceil(total * frac * frac));
  const pct = (x: number) => t("w.chance.percent", { value: n(Math.round(x * 1000) / 10) });
  const dec = (x: number, d = 3) => n(Math.round(x * 10 ** d) / 10 ** d);

  let chart: React.ReactNode = null;
  let legend: LegendItem[] = [];
  let stats: React.ReactNode = null;
  let summary = "";
  let extraControls: React.ReactNode = null;
  let note = "";

  const unit = t(`w.chance.unit.${exp}`);

  if (sim.exp === "coin") {
    const { flips, earlier } = sim;
    const series = runningProportion(flips, shown, 200);
    const heads = series.length ? Math.round(series[series.length - 1].p * series[series.length - 1].n) : 0;
    const p = heads / shown;
    const f = frame(0, total, 0, 1);
    const band: [number, number][] = [];
    const bandLow: [number, number][] = [];
    for (let i = 0; i <= 80; i++) {
      const m = Math.max(1, (total * i) / 80);
      const h = 1 / Math.sqrt(m);
      band.push([X(f, m), Y(f, Math.min(1, 0.5 + h))]);
      bandLow.push([X(f, m), Y(f, Math.max(0, 0.5 - h))]);
    }
    chart = (
      <svg viewBox={`0 0 ${f.W} ${f.H}`} className="w-full" role="img" aria-label={t("w.chance.aria.coin", { n: shown, p: dec(p) })}>
        <Axes f={f} xTicks={niceTicks(0, total)} yTicks={[0, 0.25, 0.5, 0.75, 1]} fx={(v) => n(v)} fy={(v) => n(v)} xLabel={t("w.chance.axis.flips")} yLabel={t("w.chance.axis.propHeads")} />
        <polygon points={pts([...band, ...bandLow.reverse()])} fill={EXACT} opacity="0.12" />
        <line x1={X(f, 0)} x2={X(f, total)} y1={Y(f, 0.5)} y2={Y(f, 0.5)} stroke={EXACT} strokeWidth="2" strokeDasharray="6 4" />
        {earlier.map((s, i) => (
          <polyline key={i} points={pts(s.map((d) => [X(f, d.n), Y(f, d.p)]))} fill="none" stroke="var(--muted)" strokeWidth="1.2" opacity="0.45" />
        ))}
        <polyline points={pts(series.map((d) => [X(f, d.n), Y(f, d.p)]))} fill="none" stroke={SIM} strokeWidth="2.2" strokeLinejoin="round" />
      </svg>
    );
    legend = [
      { kind: "line", color: SIM, label: t("w.chance.legend.thisRun") },
      ...(earlier.length ? [{ kind: "line" as const, color: "var(--muted)", label: t("w.chance.legend.earlier") }] : []),
      { kind: "dash", color: EXACT, label: t("w.chance.legend.exactHalf") },
      { kind: "band", color: EXACT, label: t("w.chance.legend.band") },
    ];
    stats = <Row label={t("w.chance.stat.heads", { h: n(heads), n: n(shown) })} sim={dec(p)} exact={<span className="font-serif">1/2 = 0.5</span>} />;
    summary = t("w.chance.summary.coin", { n: n(total), h: n(heads), p: dec(p) });
    note = t("w.chance.note.coin");
  } else if (sim.exp === "dice" || sim.exp === "two-dice") {
    const two = sim.exp === "two-dice";
    const lo = two ? 2 : 1;
    const hi = two ? 12 : 6;
    const rolls = sim.rolls;
    const counts = tally(rolls, shown, lo, hi);
    const exactP = (v: number) => (two ? twoDiceExact(v) : 1 / 6);
    const freqs = counts.map((c) => c / shown);
    const yMax = Math.max(two ? 0.25 : 0.3, ...freqs.map((x) => x * 1.12));
    const f = frame(lo - 0.6, hi + 0.6, 0, yMax);
    const bw = ((f.W - f.L - f.R) / (hi - lo + 1.2)) * 0.72;
    const exactLine: [number, number][] = [];
    for (let v = lo; v <= hi; v++) exactLine.push([X(f, v), Y(f, exactP(v))]);
    chart = (
      <svg viewBox={`0 0 ${f.W} ${f.H}`} className="w-full" role="img" aria-label={t(two ? "w.chance.aria.twoDice" : "w.chance.aria.dice", { n: shown })}>
        <Axes f={f} xTicks={Array.from({ length: hi - lo + 1 }, (_, i) => lo + i)} yTicks={niceTicks(0, yMax, 4)} fx={(v) => n(v)} fy={(v) => pct(v)} xLabel={t(two ? "w.chance.axis.sum" : "w.chance.axis.face")} />
        {counts.map((c, i) => {
          const v = lo + i;
          const y = Y(f, freqs[i]);
          return (
            <g key={v}>
              <rect x={X(f, v) - bw / 2} y={y} width={bw} height={Math.max(0, f.H - f.B - y)} rx="3" fill={SIM} opacity="0.72" />
              {f.H - f.B - y >= 18 && (two ? c < 1000 : c < 100000) && (
                <text x={X(f, v)} y={f.H - f.B - 6} textAnchor="middle" fontSize={two ? 10 : 12} fontWeight="600" fill="var(--paper)">
                  {n(c)}
                </text>
              )}
            </g>
          );
        })}
        {two ? (
          <>
            <polyline points={pts(exactLine)} fill="none" stroke={EXACT} strokeWidth="1.8" strokeDasharray="5 4" />
            {exactLine.map(([x, y], i) => (
              <path key={i} d={`M${x} ${y - 4.5} ${x + 4.5} ${y} ${x} ${y + 4.5} ${x - 4.5} ${y}z`} fill="var(--card)" stroke={EXACT} strokeWidth="1.8" />
            ))}
          </>
        ) : (
          <line x1={f.L} x2={f.W - f.R} y1={Y(f, 1 / 6)} y2={Y(f, 1 / 6)} stroke={EXACT} strokeWidth="2" strokeDasharray="6 4" />
        )}
      </svg>
    );
    legend = [
      { kind: "bar", color: SIM, label: t("w.chance.legend.simFreq") },
      { kind: two ? "dot" : "dash", color: EXACT, label: t(two ? "w.chance.legend.exactTwoDice" : "w.chance.legend.exactSixth") },
    ];
    if (two) {
      stats = (
        <>
          <Row label={t("w.chance.stat.seven")} sim={pct(freqs[5])} exact={<span><span className="font-serif">6/36</span> ≈ {pct(6 / 36)}</span>} />
          <Row label={t("w.chance.stat.twelve")} sim={pct(freqs[10])} exact={<span><span className="font-serif">1/36</span> ≈ {pct(1 / 36)}</span>} />
        </>
      );
      summary = t("w.chance.summary.twoDice", { n: n(total), p: pct(counts[5] / Math.max(1, shown)) });
      note = t("w.chance.note.twoDice");
    } else {
      const maxDev = Math.max(...freqs.map((x) => Math.abs(x - 1 / 6)));
      stats = (
        <>
          <Row label={t("w.chance.stat.eachFace")} sim={`${pct(Math.min(...freqs))} – ${pct(Math.max(...freqs))}`} exact={<span><span className="font-serif">1/6</span> ≈ {pct(1 / 6)}</span>} />
          <Row label={t("w.chance.stat.maxDev")} sim={pct(maxDev)} />
        </>
      );
      summary = t("w.chance.summary.dice", { n: n(total), lo: pct(Math.min(...freqs)), hi: pct(Math.max(...freqs)) });
      note = t("w.chance.note.dice");
    }
  } else if (sim.exp === "galton") {
    const data = sim.data;
    const counts = tally(data.bins, shown, 0, rows);
    const W = 420;
    const H = 330;
    const cx = W / 2;
    const dx = Math.min(34, (W - 40) / (rows + 1));
    const rowH = Math.min(13, 130 / rows);
    const top = 16;
    const histTop = top + rows * rowH + 22;
    const base = H - 30;
    const expected = Array.from({ length: rows + 1 }, (_, j) => shown * binomialPmf(rows, j));
    const yMax = Math.max(...counts, ...expected) * 1.1 || 1;
    const Yh = (v: number) => base - (v / yMax) * (base - histTop);
    const binX = (j: number) => cx + (j - rows / 2) * dx;
    const ball = Math.min(shown, total) - 1;
    const path: [number, number][] = [[cx, top - 10]];
    let rights = 0;
    for (let r = 0; r < rows; r++) {
      path.push([cx + (rights - r / 2) * dx, top + r * rowH]);
      rights += data.choices[ball * rows + r];
    }
    path.push([binX(rights), histTop - 6]);
    const sd = Math.sqrt(rows) / 2;
    const curve: [number, number][] = [];
    for (let i = 0; i <= 120; i++) {
      const x = -0.5 + ((rows + 1) * i) / 120;
      curve.push([binX(x), Yh(shown * normalPdf(x, rows / 2, sd))]);
    }
    const mean = counts.reduce((s, c, j) => s + c * j, 0) / shown;
    chart = (
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={t("w.chance.aria.galton", { n: shown, rows })}>
        {Array.from({ length: rows }, (_, r) =>
          Array.from({ length: r + 1 }, (_, j) => <circle key={`${r}-${j}`} cx={cx + (j - r / 2) * dx} cy={top + r * rowH} r={Math.min(2.6, rowH / 4)} fill="var(--ink-2)" opacity="0.55" />),
        )}
        <polyline points={pts(path)} fill="none" stroke="var(--human)" strokeWidth="1.8" strokeLinejoin="round" opacity="0.9" />
        <circle cx={path[path.length - 1][0]} cy={path[path.length - 1][1]} r="4" fill="var(--human)" />
        <line x1={20} x2={W - 20} y1={base} y2={base} stroke="var(--ink-2)" />
        {counts.map((c, j) => (
          <rect key={j} x={binX(j) - dx * 0.4} y={Yh(c)} width={dx * 0.8} height={base - Yh(c)} rx="2" fill={SIM} opacity="0.72" />
        ))}
        <polyline points={pts(curve)} fill="none" stroke="var(--gold)" strokeWidth="2" strokeDasharray="5 3" />
        {expected.map((e, j) => (
          <path key={j} d={`M${binX(j)} ${Yh(e) - 4} ${binX(j) + 4} ${Yh(e)} ${binX(j)} ${Yh(e) + 4} ${binX(j) - 4} ${Yh(e)}z`} fill="var(--card)" stroke={EXACT} strokeWidth="1.6" />
        ))}
        {Array.from({ length: rows + 1 }, (_, j) =>
          rows <= 12 || j % 2 === 0 ? (
            <text key={j} x={binX(j)} y={base + 15} textAnchor="middle" fontSize="12" fill="var(--muted)">
              {n(j)}
            </text>
          ) : null,
        )}
        <text x={W / 2} y={H - 2} textAnchor="middle" fontSize="12.5" fill="var(--ink-2)">
          {t("w.chance.axis.rights")}
        </text>
      </svg>
    );
    legend = [
      { kind: "bar", color: SIM, label: t("w.chance.legend.balls") },
      { kind: "dot", color: EXACT, label: t("w.chance.legend.binomial") },
      { kind: "dash", color: "var(--gold)", label: t("w.chance.legend.normal") },
      { kind: "line", color: "var(--human)", label: t("w.chance.legend.lastBall") },
    ];
    extraControls = <Slider label={t("w.chance.control.rows")} value={rows} display={n(rows)} min={1} max={20} onChange={setRows} />;
    stats = (
      <>
        <Row label={t("w.chance.stat.meanBin")} sim={dec(mean, 2)} exact={<span className="font-serif">n/2 = {n(rows / 2)}</span>} />
        <Row label={t("w.chance.stat.middle", { j: n(Math.floor(rows / 2)) })} sim={n(counts[Math.floor(rows / 2)])} exact={`≈ ${dec(expected[Math.floor(rows / 2)], 1)}`} />
      </>
    );
    summary = t("w.chance.summary.galton", { n: n(total), rows: n(rows), mean: dec(mean, 2) });
    note = t("w.chance.note.galton");
  } else if (sim.exp === "random-walk") {
    const data = sim.data;
    const sShown = Math.max(1, Math.ceil(walkSteps * frac));
    let maxAbs = 0;
    for (const p of data.paths) for (let s = 0; s <= walkSteps; s++) maxAbs = Math.max(maxAbs, Math.abs(p[s]));
    const yMax = Math.max(3 * Math.sqrt(walkSteps), maxAbs + 1);
    const f = frame(0, walkSteps, -yMax, yMax);
    const every = Math.max(1, Math.floor(walkSteps / 200));
    const line = (fn: (s: number) => number, upto: number): [number, number][] => {
      const out: [number, number][] = [];
      for (let s = 0; s <= upto; s += every) out.push([X(f, s), Y(f, fn(s))]);
      if ((upto % every) !== 0) out.push([X(f, upto), Y(f, fn(upto))]);
      return out;
    };
    const rms = Math.sqrt(data.sumSq[sShown] / total);
    chart = (
      <svg viewBox={`0 0 ${f.W} ${f.H}`} className="w-full" role="img" aria-label={t("w.chance.aria.walk", { w: total, n: sShown })}>
        <Axes f={f} xTicks={niceTicks(0, walkSteps)} yTicks={niceTicks(-yMax, yMax, 4)} fx={(v) => n(v)} fy={(v) => n(v)} xLabel={t("w.chance.axis.steps")} yLabel={t("w.chance.axis.position")} />
        <line x1={f.L} x2={f.W - f.R} y1={Y(f, 0)} y2={Y(f, 0)} stroke="var(--line-2)" />
        {data.paths.map((p, i) => (
          <polyline key={i} points={pts(line((s) => p[s], sShown))} fill="none" stroke={SIM} strokeWidth={i === 0 ? 2 : 1.1} opacity={i === 0 ? 0.95 : 0.4} strokeLinejoin="round" />
        ))}
        {[1, -1].map((sg) => (
          <polyline key={sg} points={pts(line((s) => sg * Math.sqrt(s), walkSteps))} fill="none" stroke={EXACT} strokeWidth="2" strokeDasharray="6 4" />
        ))}
        <polyline points={pts(line((s) => Math.sqrt(data.sumSq[s] / total), sShown))} fill="none" stroke="var(--human)" strokeWidth="2.2" />
      </svg>
    );
    legend = [
      { kind: "line", color: SIM, label: t("w.chance.legend.walks", { k: n(data.paths.length) }) },
      { kind: "line", color: "var(--human)", label: t("w.chance.legend.rms", { w: n(total) }) },
      { kind: "dash", color: EXACT, label: t("w.chance.legend.sqrtN") },
    ];
    extraControls = <Slider label={t("w.chance.control.steps")} value={walkSteps} display={n(walkSteps)} min={10} max={1000} step={10} onChange={setWalkSteps} />;
    stats = <Row label={t("w.chance.stat.rms", { n: n(sShown) })} sim={dec(rms, 2)} exact={<span className="font-serif">√{n(sShown)} ≈ {dec(Math.sqrt(sShown), 2)}</span>} />;
    summary = t("w.chance.summary.walk", { w: n(total), n: n(walkSteps), rms: dec(Math.sqrt(data.sumSq[walkSteps] / total), 2), sqrt: dec(Math.sqrt(walkSteps), 2) });
    note = t("w.chance.note.walk");
  } else if (sim.exp === "birthday") {
    const data = sim.data;
    let shared = 0;
    for (let i = 0; i < shown; i++) shared += data[i];
    const p = shared / shown;
    const exact = birthdayExact(group);
    const kMax = Math.max(60, Math.min(100, group + 5));
    const f = frame(1, kMax, 0, 1);
    const curve: [number, number][] = [];
    for (let kk = 1; kk <= kMax; kk++) curve.push([X(f, kk), Y(f, birthdayExact(kk))]);
    const hw = ci95(p, shown);
    chart = (
      <svg viewBox={`0 0 ${f.W} ${f.H}`} className="w-full" role="img" aria-label={t("w.chance.aria.birthday", { k: group, p: pct(p), e: pct(exact) })}>
        <Axes f={f} xTicks={niceTicks(0, kMax).filter((v) => v >= 1)} yTicks={[0, 0.25, 0.5, 0.75, 1]} fx={(v) => n(v)} fy={(v) => pct(v)} xLabel={t("w.chance.axis.groupSize")} yLabel={t("w.chance.axis.probShared")} />
        <line x1={X(f, group)} x2={X(f, group)} y1={f.T} y2={f.H - f.B} stroke="var(--line-2)" strokeDasharray="3 3" />
        <polyline points={pts(curve)} fill="none" stroke={EXACT} strokeWidth="2.2" />
        <line x1={X(f, group)} x2={X(f, group)} y1={Y(f, Math.min(1, p + hw))} y2={Y(f, Math.max(0, p - hw))} stroke={SIM} strokeWidth="2.5" />
        {[p + hw, p - hw].map((v, i) => (
          <line key={i} x1={X(f, group) - 5} x2={X(f, group) + 5} y1={Y(f, Math.min(1, Math.max(0, v)))} y2={Y(f, Math.min(1, Math.max(0, v)))} stroke={SIM} strokeWidth="2" />
        ))}
        <circle cx={X(f, group)} cy={Y(f, p)} r="5" fill={SIM} stroke="var(--card)" strokeWidth="1.5" />
      </svg>
    );
    legend = [
      { kind: "line", color: EXACT, label: t("w.chance.legend.exactBirthday") },
      { kind: "line", color: SIM, label: t("w.chance.legend.simPoint") },
    ];
    extraControls = <Slider label={t("w.chance.control.group")} value={group} display={n(group)} min={2} max={100} onChange={setGroup} />;
    stats = <Row label={t("w.chance.stat.shared", { c: n(shared), g: n(shown), k: n(group) })} sim={`${pct(p)} ± ${pct(hw)}`} exact={pct(exact)} />;
    summary = t("w.chance.summary.birthday", { k: n(group), p: pct(p), e: pct(exact) });
    note = t("w.chance.note.birthday");
  } else if (sim.exp === "monty-hall") {
    const data = sim.data;
    const stickSeries = runningProportion(data, shown, 200);
    const stick = stickSeries.length ? stickSeries[stickSeries.length - 1].p : 0;
    const f = frame(0, total, 0, 1);
    chart = (
      <svg viewBox={`0 0 ${f.W} ${f.H}`} className="w-full" role="img" aria-label={t("w.chance.aria.monty", { n: shown, stick: pct(stick), sw: pct(1 - stick) })}>
        <Axes f={f} xTicks={niceTicks(0, total)} yTicks={[0, 0.25, 0.5, 0.75, 1]} fx={(v) => n(v)} fy={(v) => pct(v)} xLabel={t("w.chance.axis.games")} yLabel={t("w.chance.axis.winRate")} />
        {[1 / 3, 2 / 3].map((v) => (
          <line key={v} x1={X(f, 0)} x2={X(f, total)} y1={Y(f, v)} y2={Y(f, v)} stroke={EXACT} strokeWidth="1.8" strokeDasharray="6 4" />
        ))}
        <polyline points={pts(stickSeries.map((d) => [X(f, d.n), Y(f, 1 - d.p)]))} fill="none" stroke={SIM} strokeWidth="2.2" />
        <polyline points={pts(stickSeries.map((d) => [X(f, d.n), Y(f, d.p)]))} fill="none" stroke="var(--human)" strokeWidth="2.2" strokeDasharray="7 3" />
      </svg>
    );
    legend = [
      { kind: "line", color: SIM, label: t("w.chance.legend.switch") },
      { kind: "dash", color: "var(--human)", label: t("w.chance.legend.stick") },
      { kind: "dash", color: EXACT, label: t("w.chance.legend.exactThirds") },
    ];
    stats = (
      <>
        <Row label={t("w.chance.stat.switchWins")} sim={pct(1 - stick)} exact={<span><span className="font-serif">2/3</span> ≈ {pct(2 / 3)}</span>} />
        <Row label={t("w.chance.stat.stickWins")} sim={pct(stick)} exact={<span><span className="font-serif">1/3</span> ≈ {pct(1 / 3)}</span>} />
      </>
    );
    summary = t("w.chance.summary.monty", { n: n(total), sw: pct(1 - stick), stick: pct(stick) });
    note = t("w.chance.note.monty");
  } else {
    const data = sim.data;
    let crossings = 0;
    for (let i = 0; i < shown; i++) crossings += data.crosses[i];
    const est = buffonEstimate(crossings, shown);
    const W = 420;
    const H = 290;
    const s = (W - 24) / 6;
    const ox = 12;
    const oy = (H - 4 * s) / 2;
    const drawn = Math.min(shown, 400);
    chart = <BuffonField data={data} drawn={drawn} W={W} H={H} s={s} ox={ox} oy={oy} label={t("w.chance.aria.buffon", { n: shown, c: crossings })} />;
    legend = [
      { kind: "line", color: "var(--human)", label: t("w.chance.legend.crossing") },
      { kind: "line", color: "var(--muted)", label: t("w.chance.legend.notCrossing") },
    ];
    stats = (
      <>
        <Row label={t("w.chance.stat.crossProb", { c: n(crossings), n: n(shown) })} sim={dec(crossings / shown)} exact={<span><span className="font-serif">2/π</span> ≈ {dec(2 / Math.PI)}</span>} />
        <Row
          label={t("w.chance.stat.piEstimate")}
          sim={est.estimate === null ? "—" : `${dec(est.estimate)} ± ${dec(est.halfWidth ?? 0, 2)}`}
          exact={<span><span className="font-serif">π</span> ≈ 3.14159</span>}
        />
        {est.estimate !== null && <p className="text-xs text-muted">{t("w.chance.stat.piError", { err: dec(Math.abs(est.estimate - Math.PI)) })}</p>}
      </>
    );
    summary = t("w.chance.summary.buffon", { n: n(total), est: est.estimate === null ? "—" : dec(est.estimate) });
    note = t("w.chance.note.buffon");
  }

  return (
    <div>
      <div className="grid gap-5 md:grid-cols-[minmax(0,1.45fr)_minmax(0,1fr)]">
        <div>
          <div dir="ltr" className="rounded-xl border border-line bg-paper/40 p-1.5">
            {chart}
          </div>
          <Legend items={legend} />
        </div>
        <div className="space-y-3">
          <div className="flex flex-wrap gap-2">
            <button type="button" className="btn btn-sm btn-gold" onClick={newRun}>
              <Dices size={15} aria-hidden="true" /> {t("w.chance.newRun")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={replay} disabled={playing}>
              <Play size={14} aria-hidden="true" /> {t("w.chance.replay")}
            </button>
          </div>
          <Slider label={t(`w.chance.trials.${exp}`)} value={tIdx} display={n(total)} min={0} max={steps.length - 1} onChange={setTIdx} />
          {extraControls}
          {stats}
          <p className="sr-only" aria-live="polite">
            {playing ? "" : summary}
          </p>
        </div>
      </div>
      {exp === "monty-hall" && <MontyPlay />}
      <div className="mt-4 rounded-xl border border-dashed border-line-2 px-4 py-3 text-sm text-ink-2">
        <p>
          <span className="chip me-2 !border-compute/40 !bg-compute-soft !text-compute">{t("w.chance.evidenceChip")}</span>
          {t("w.chance.evidence", { count: n(shown), unit, run: n(run + 1) })}
        </p>
        {note && <p className="mt-2">{note}</p>}
      </div>
    </div>
  );
}

type Sim =
  | { exp: "coin"; flips: Uint8Array; earlier: { n: number; p: number }[][] }
  | { exp: "dice"; rolls: Uint8Array }
  | { exp: "two-dice"; rolls: Uint8Array }
  | { exp: "galton"; data: ReturnType<typeof galton> }
  | { exp: "random-walk"; data: ReturnType<typeof randomWalks> }
  | { exp: "birthday"; data: Uint8Array }
  | { exp: "monty-hall"; data: Uint8Array }
  | { exp: "buffon"; data: ReturnType<typeof dropNeedles> };

/** Run the whole simulation for a seed; the animation only reveals a prefix of it. */
function simulate(exp: Experiment, run: number, total: number, rows: number, walkSteps: number, group: number): Sim {
  const seed = seedFor(exp, run);
  switch (exp) {
    case "coin":
      return {
        exp,
        flips: flipCoins(seed, total),
        earlier: [1, 2, 3].filter((d) => run - d >= 0).map((d) => runningProportion(flipCoins(seedFor(exp, run - d), total), total, 160)),
      };
    case "dice":
      return { exp, rolls: rollDice(seed, total, 1) };
    case "two-dice":
      return { exp, rolls: rollDice(seed, total, 2) };
    case "galton":
      return { exp, data: galton(seed, total, rows) };
    case "random-walk":
      return { exp, data: randomWalks(seed, total, walkSteps, 8) };
    case "birthday":
      return { exp, data: birthdayGroups(seed, total, group) };
    case "monty-hall":
      return { exp, data: montyHall(seed, total) };
    case "buffon":
      return { exp, data: dropNeedles(seed, total) };
  }
}

function BuffonField({ data, drawn, W, H, s, ox, oy, label }: { data: ReturnType<typeof dropNeedles>; drawn: number; W: number; H: number; s: number; ox: number; oy: number; label: string }) {
  const clip = useId().replace(/:/g, "");
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={label}>
      <defs>
        <clipPath id={`bf-${clip}`}>
          <rect x={ox} y={oy - 14} width={6 * s} height={4 * s + 28} />
        </clipPath>
      </defs>
      <rect x={ox} y={oy} width={6 * s} height={4 * s} fill="var(--paper-2)" opacity="0.6" />
      {[0, 1, 2, 3, 4].map((i) => (
        <line key={i} x1={ox} x2={ox + 6 * s} y1={oy + i * s} y2={oy + i * s} stroke="var(--ink-2)" strokeWidth="1.4" />
      ))}
      <g clipPath={`url(#bf-${clip})`} strokeLinecap="round">
        {Array.from({ length: drawn }, (_, i) => {
          const cx = ox + data.x[i] * s;
          const cy = oy + data.y[i] * s;
          const hx = (data.dx[i] * s) / 2;
          const hy = (data.dy[i] * s) / 2;
          const c = data.crosses[i] === 1;
          return <line key={i} x1={cx - hx} y1={cy - hy} x2={cx + hx} y2={cy + hy} stroke={c ? "var(--human)" : "var(--muted)"} strokeWidth={c ? 1.6 : 1.1} opacity={c ? 0.85 : 0.5} />;
        })}
      </g>
    </svg>
  );
}

/** Play the Monty Hall game by hand: pick a door, watch the host open a goat door, then stick or switch. */
function MontyPlay() {
  const { t, n } = useI18n();
  const [gameNo, setGameNo] = useState(0);
  const [pick, setPick] = useState<number | null>(null);
  const [final, setFinal] = useState<number | null>(null);
  const [tally2, setTally] = useState({ stickW: 0, stickN: 0, switchW: 0, switchN: 0 });
  const game = pick === null ? null : montyGame(mulberry32(seedFor("monty-play", gameNo)), pick);
  const other = game ? [0, 1, 2].find((d) => d !== game.pick && d !== game.opened)! : null;

  const decide = (door: number) => {
    if (!game || final !== null) return;
    setFinal(door);
    const won = door === game.car;
    const switched = door !== game.pick;
    setTally((s) => (switched ? { ...s, switchN: s.switchN + 1, switchW: s.switchW + (won ? 1 : 0) } : { ...s, stickN: s.stickN + 1, stickW: s.stickW + (won ? 1 : 0) }));
  };
  const again = () => {
    setGameNo((g) => g + 1);
    setPick(null);
    setFinal(null);
  };

  let status: string;
  if (pick === null) status = t("w.chance.play.pick");
  else if (final === null) status = t("w.chance.play.opened", { opened: n(game!.opened + 1), other: n(other! + 1) });
  else status = final === game!.car ? t("w.chance.play.won", { door: n(final + 1) }) : t("w.chance.play.lost", { door: n(game!.car + 1) });

  return (
    <div className="mt-5 rounded-xl border border-line px-4 py-4">
      <p className="text-sm font-bold text-ink">{t("w.chance.play.title")}</p>
      <div className="mt-3 grid grid-cols-3 gap-2 sm:gap-3">
        {[0, 1, 2].map((d) => {
          const opened = game !== null && game.opened === d;
          const revealed = final !== null || opened;
          const isCar = game !== null && game.car === d;
          const chosen = final !== null ? final === d : pick === d;
          const clickable = pick === null || (final === null && !opened);
          return (
            <button
              key={d}
              type="button"
              disabled={!clickable}
              aria-pressed={chosen}
              onClick={() => (pick === null ? setPick(d) : decide(d))}
              className={`flex min-h-24 flex-col items-center justify-center gap-1 rounded-xl border-2 px-2 py-3 text-sm font-semibold transition-colors ${chosen ? "border-gold bg-gold-soft" : "border-line-2 bg-card"} ${clickable ? "cursor-pointer hover:bg-paper-2" : "cursor-default"} ${revealed && !isCar ? "opacity-80" : ""}`}
            >
              <span className="text-ink">{t("w.chance.play.door", { d: n(d + 1) })}</span>
              {revealed ? (
                isCar ? (
                  <span className="flex items-center gap-1 text-good">
                    <Car size={18} aria-hidden="true" /> {t("w.chance.play.car")}
                  </span>
                ) : (
                  <span className="text-muted">{t("w.chance.play.goat")}</span>
                )
              ) : (
                <span className="text-muted" aria-hidden="true">
                  ?
                </span>
              )}
            </button>
          );
        })}
      </div>
      <p className="mt-3 text-sm text-ink-2" aria-live="polite">
        {status}
      </p>
      <div className="mt-2 flex flex-wrap items-center gap-2">
        {final !== null && (
          <button type="button" className="btn btn-sm btn-primary" onClick={again}>
            <RotateCcw size={14} aria-hidden="true" /> {t("w.chance.play.again")}
          </button>
        )}
        <span className="chip">{t("w.chance.play.tallySwitch", { w: n(tally2.switchW), n: n(tally2.switchN) })}</span>
        <span className="chip">{t("w.chance.play.tallyStick", { w: n(tally2.stickW), n: n(tally2.stickN) })}</span>
      </div>
    </div>
  );
}
