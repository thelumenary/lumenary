"use client";

import { Minus, Plus, X } from "lucide-react";
import { useId, useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  MAX_VALUES,
  binWidthOptions,
  countTicks,
  fairShare,
  frequency,
  histogram,
  mean,
  medianInfo,
  modalCategories,
  modes,
  niceStep,
  parseData,
  parseValues,
  pictographKeys,
  roundClean,
  statText,
  sum,
  tally,
  type Datum,
} from "./lib/shape-stats";
import { asNumber, listOf, oneOf } from "./lib/shape-util";

const VIEWS = ["tally", "pictograph", "bar", "dot", "histogram", "fair"] as const;
type View = (typeof VIEWS)[number];

export interface DataChartProps {
  data?: { label: string; value: number }[];
  values?: number[];
  view?: View;
  views?: View[];
  showMean?: boolean;
  showMedian?: boolean;
  showMode?: boolean;
  per?: number;
  binWidth?: number;
  editable?: boolean;
  unit?: string;
  title?: string;
  subtitle?: string;
}

type T = (k: string, v?: Record<string, string | number>) => string;

const short = (s: string, k = 10) => (s.length > k ? `${s.slice(0, k - 1)}…` : s);
/** Numbers inside diagrams: up to 2 decimals, no floating-point noise. */
const num = (x: number) => String(Math.round(x * 100) / 100);
/** A statistic inside a diagram, marked "≈" when the 2-decimal rounding is not exact. */
const stat2 = (x: number) => `${statText(x).approx ? "≈" : ""}${num(x)}`;

/**
 * Data handling: categorical data (labelled counts) as tallies, pictographs, bar
 * charts and dot plots; numerical data as dot plots and histograms; mean as a
 * fair share (levelling towers), with median and mode on request.
 */
export function DataChart({ data, values, view, views, showMean, showMedian, showMode, per, binWidth, editable = true, unit, title, subtitle }: DataChartProps) {
  const { t, n } = useI18n();
  const parsedNums = useMemo(() => parseValues(values), [values]);
  const parsedCats = useMemo(() => parseData(data), [data]);
  const kind: "num" | "cat" = parsedNums.length ? "num" : "cat";
  const sample = useMemo<Datum[]>(
    () => [
      { label: t("w.data.sample.apples"), value: 6 },
      { label: t("w.data.sample.bananas"), value: 4 },
      { label: t("w.data.sample.grapes"), value: 7 },
      { label: t("w.data.sample.oranges"), value: 3 },
    ],
    [t],
  );
  const initialCats = parsedCats.length ? parsedCats : sample;
  const [cats, setCats] = useState<Datum[]>(initialCats);
  const [nums, setNums] = useState<number[]>(parsedNums);
  const [stat, setStat] = useState({ mean: !!showMean, median: !!showMedian, mode: !!showMode });
  const [editing, setEditing] = useState(false);
  const [draft, setDraft] = useState("");
  const [levelled, setLevelled] = useState(false);
  const u = typeof unit === "string" ? unit.trim().slice(0, 12) : "";

  const amounts = kind === "num" ? nums : cats.map((d) => d.value);
  const integers = amounts.every((v) => Number.isInteger(v));
  const supported: View[] =
    kind === "cat"
      ? (["tally", "pictograph", "bar", "dot", "fair"] as View[]).filter((v) => (v === "tally" || v === "pictograph" || v === "dot" ? integers : v === "fair" ? cats.length >= 2 && Math.max(...amounts) <= 60 : true))
      : (["dot", "histogram", "tally", "fair"] as View[]).filter((v) => (v === "fair" ? nums.length >= 2 && nums.length <= 20 && Math.min(...nums) >= 0 && Math.max(...nums) <= 40 : nums.length > 0));
  const allowed = listOf(views, VIEWS);
  const offered = allowed.length ? supported.filter((v) => allowed.includes(v)) : supported;
  const list = offered.length ? offered : supported.length ? supported : (["bar"] as View[]);
  const [chosen, setChosen] = useState<View>(oneOf(view, VIEWS, kind === "num" ? "dot" : "bar"));
  const active: View = list.includes(chosen) ? chosen : list[0];

  const maxAmount = Math.max(0, ...amounts);
  const auto = pictographKeys(maxAmount);
  const perRaw = asNumber(per);
  const perOk = Number.isInteger(perRaw) && perRaw >= 1 && perRaw <= 100 && maxAmount / perRaw <= 40;
  const keys = { options: perOk && !auto.options.includes(perRaw) ? [...auto.options, perRaw].sort((x, y) => x - y) : auto.options, preferred: perOk ? perRaw : auto.preferred };
  const [key, setKey] = useState(keys.preferred);
  const bw = binWidthOptions(nums);
  const bwRaw = asNumber(binWidth);
  const [width, setWidth] = useState(bwRaw > 0 ? bwRaw : bw.preferred);
  const authorWidthOk = bwRaw > 0 && width === bwRaw && histogram(nums, bwRaw).length <= 30;
  const binW = bw.options.includes(width) || authorWidthOk ? width : bw.preferred;

  const m = amounts.length ? mean(amounts) : NaN;
  const med = medianInfo(amounts);
  const mo = modes(amounts);
  const modeCats = kind === "cat" ? modalCategories(cats) : [];
  const fmtStat = (x: number) => {
    const s = statText(x);
    return `${s.approx ? "≈" : "="} ${n(s.value)}${u ? ` ${u}` : ""}`;
  };
  const freqRows = kind === "num" ? frequency(nums).map((f) => ({ label: num(f.value), value: f.count })) : cats;
  const ariaList = (kind === "cat" ? cats.map((d) => `${d.label} ${num(d.value)}`) : nums.map(num)).join(", ");

  const reset = () => {
    setCats(initialCats);
    setNums(parsedNums);
    setLevelled(false);
  };
  const bump = (i: number, d: number) => setCats((prev) => prev.map((x, j) => (j === i ? { ...x, value: Math.max(0, Math.min(99, roundClean(x.value + d))) } : x)));
  const addValue = (e: React.FormEvent) => {
    e.preventDefault();
    const v = Number(draft.replace(",", "."));
    if (!draft.trim() || !Number.isFinite(v) || Math.abs(v) > 1e6 || nums.length >= MAX_VALUES) return;
    setNums((prev) => [...prev, v]);
    setDraft("");
  };

  return (
    <WidgetFrame title={title ?? t("w.data.title")} subtitle={subtitle ?? t("w.data.subtitle")}>
      <div className="flex flex-wrap gap-2">
        {list.map((v) => (
          <button key={v} type="button" aria-pressed={active === v} className={`btn btn-sm ${active === v ? "btn-primary" : "btn-ghost"}`} onClick={() => setChosen(v)}>
            {t(`w.data.view.${v}`)}
          </button>
        ))}
      </div>
      {!parsedCats.length && kind === "cat" && <p className="mt-2 text-xs text-muted">{t("w.data.sampleNote")}</p>}

      <div className="mt-4">
        {amounts.length === 0 ? (
          <p className="rounded-xl bg-paper-2 px-4 py-6 text-center text-sm text-ink-2">{t("w.data.empty")}</p>
        ) : (
          <>
            {active === "bar" && <BarChart t={t} items={cats} showMean={stat.mean} showMedian={stat.median} mean={m} median={med.median} modeLabels={stat.mode ? modeCats : []} aria={`${t("w.data.view.bar")}: ${ariaList}`} />}
            {active === "tally" && <TallyTable t={t} rows={freqRows} modeLabels={stat.mode ? (kind === "cat" ? modeCats : mo.values.map(num)) : []} header={kind === "num" ? t("w.data.value") : t("w.data.category")} />}
            {active === "pictograph" && <Pictograph t={t} items={cats} k={keys.options.includes(key) ? key : keys.preferred} options={keys.options} setK={setKey} />}
            {active === "dot" && (kind === "cat" ? <CategoryDots t={t} items={cats} aria={`${t("w.data.view.dot")}: ${ariaList}`} modeLabels={stat.mode ? modeCats : []} /> : <NumberLineDots t={t} values={nums} showMean={stat.mean} showMedian={stat.median} modeValues={stat.mode ? mo.values : []} aria={`${t("w.data.view.dot")}: ${ariaList}`} />)}
            {active === "histogram" && (
              <div>
                <Histogram t={t} values={nums} width={binW} showMean={stat.mean} showMedian={stat.median} />
                {bw.options.length > 1 && (
                  <label className="mt-3 block max-w-sm">
                    <span className="flex items-center justify-between text-sm font-semibold text-ink-2">
                      {t("w.data.binWidth")}
                      <span className="font-mono text-ink" dir="ltr">
                        {num(binW)}
                      </span>
                    </span>
                    <input type="range" min={0} max={bw.options.length - 1} value={Math.max(0, bw.options.indexOf(binW))} onChange={(e) => setWidth(bw.options[Number(e.target.value)])} className="mt-1.5 w-full accent-[var(--sky)]" dir="ltr" />
                  </label>
                )}
                <p className="mt-2 text-xs text-muted">{t("w.data.binNote")}</p>
              </div>
            )}
            {active === "fair" && (
              <div>
                <FairShare t={t} items={kind === "cat" ? cats : nums.map((v, i) => ({ label: `#${i + 1}`, value: v }))} levelled={levelled} />
                <div className="mt-3 flex flex-wrap items-center gap-3">
                  <button type="button" aria-pressed={levelled} className={`btn btn-sm ${levelled ? "btn-gold" : "btn-ghost"}`} onClick={() => setLevelled((v) => !v)}>
                    {t("w.data.level")}
                  </button>
                </div>
                <p aria-live="polite" className="mt-2 text-sm text-ink-2">
                  {levelled ? t("w.data.fairDone", { total: n(roundClean(sum(amounts))), count: n(amounts.length), mean: fmtStat(m) }) : t("w.data.fairHint")}
                </p>
              </div>
            )}
          </>
        )}
      </div>

      {amounts.length > 0 && (
        <div className="mt-5">
          <div role="group" aria-label={t("w.data.statsLabel")} className="flex flex-wrap gap-2">
            {(["mean", "median", "mode"] as const).map((s) => (
              <button key={s} type="button" aria-pressed={stat[s]} className={`btn btn-sm ${stat[s] ? "btn-gold" : "btn-ghost"}`} onClick={() => setStat((p) => ({ ...p, [s]: !p[s] }))}>
                {t(`w.data.stat.${s}`)}
              </button>
            ))}
          </div>
          <div aria-live="polite" className="mt-3 space-y-2 text-sm">
            {stat.mean && (
              <div className="rounded-xl bg-formal-soft px-4 py-2.5">
                <p className="font-semibold text-ink">{t(kind === "cat" ? "w.data.meanCat" : "w.data.meanNum")}</p>
                <p className="font-serif text-lg text-ink" dir="ltr">
                  {num(sum(amounts))} ÷ {amounts.length} {fmtStat(m)}
                </p>
              </div>
            )}
            {stat.median && (
              <div className="rounded-xl bg-compute-soft px-4 py-2.5">
                <p className="font-semibold text-ink">
                  {t(kind === "cat" ? "w.data.medianCat" : "w.data.medianNum")} <span className="font-serif text-lg">{fmtStat(med.median)}</span>
                </p>
                <div className="mt-1.5 flex flex-wrap gap-1" dir="ltr">
                  {med.sorted.map((v, i) => (
                    <span key={i} className={`rounded-md px-1.5 py-0.5 font-mono text-xs ${med.positions.includes(i + 1) ? "bg-compute text-card" : "bg-card text-ink-2"}`}>
                      {num(v)}
                    </span>
                  ))}
                </div>
                <p className="mt-1 text-xs text-ink-2">{med.positions.length === 1 ? t("w.data.medianOdd", { p: n(med.positions[0]), k: n(amounts.length) }) : t("w.data.medianEven", { p: n(med.positions[0]), q: n(med.positions[1]), k: n(amounts.length) })}</p>
              </div>
            )}
            {stat.mode && (
              <div className="rounded-xl bg-good-soft px-4 py-2.5 text-ink">
                {kind === "cat" ? (
                  modeCats.length ? (
                    <p>
                      <span className="font-semibold">{t("w.data.modeCat")}</span> {modeCats.join(", ")} ({n(Math.max(...amounts))})
                    </p>
                  ) : (
                    <p>{t("w.data.modeCatNone")}</p>
                  )
                ) : mo.values.length ? (
                  <p>
                    <span className="font-semibold">{t("w.data.modeNum")}</span>{" "}
                    <span className="font-serif text-lg" dir="ltr">
                      {mo.values.map(num).join(", ")}
                    </span>{" "}
                    <span className="text-ink-2">({t(mo.values.length > 1 ? "w.data.modeTimesEach" : "w.data.modeTimes", { c: n(mo.count) })})</span>
                  </p>
                ) : (
                  <p>{t("w.data.modeNone")}</p>
                )}
              </div>
            )}
          </div>
        </div>
      )}

      {editable && (
        <div className="mt-5 border-t border-line pt-4">
          <div className="flex flex-wrap gap-2">
            <button type="button" aria-expanded={editing} className="btn btn-sm btn-ghost" onClick={() => setEditing((v) => !v)}>
              {t("w.data.edit")}
            </button>
            {editing && (
              <button type="button" className="btn btn-sm btn-ghost" onClick={reset}>
                {t("w.common.reset")}
              </button>
            )}
          </div>
          {editing &&
            (kind === "cat" ? (
              <ul className="mt-3 grid gap-2 sm:grid-cols-2">
                {cats.map((d, i) => (
                  <li key={i} className="flex items-center gap-2 rounded-lg bg-paper-2 px-3 py-1.5">
                    <span className="min-w-0 flex-1 truncate text-sm text-ink">{d.label}</span>
                    <button type="button" className="btn btn-sm btn-ghost !p-1.5" aria-label={t("w.data.less", { label: d.label })} disabled={d.value <= 0} onClick={() => bump(i, -1)}>
                      <Minus size={14} aria-hidden="true" />
                    </button>
                    <span className="w-8 text-center font-mono font-bold text-ink">{num(d.value)}</span>
                    <button type="button" className="btn btn-sm btn-ghost !p-1.5" aria-label={t("w.data.more", { label: d.label })} disabled={d.value >= 99} onClick={() => bump(i, 1)}>
                      <Plus size={14} aria-hidden="true" />
                    </button>
                  </li>
                ))}
              </ul>
            ) : (
              <div className="mt-3">
                <form onSubmit={addValue} className="flex flex-wrap items-end gap-2">
                  <label className="text-sm font-semibold text-ink-2">
                    {t("w.data.newValue")}
                    <input type="text" inputMode="decimal" value={draft} onChange={(e) => setDraft(e.target.value)} className="input mt-1 block w-28 py-1.5" dir="ltr" />
                  </label>
                  <button type="submit" className="btn btn-sm btn-primary" disabled={nums.length >= MAX_VALUES}>
                    <Plus size={14} aria-hidden="true" /> {t("w.data.add")}
                  </button>
                </form>
                <div className="mt-3 flex flex-wrap gap-1.5" dir="ltr">
                  {nums.map((v, i) => (
                    <button key={i} type="button" className="chip hover:bg-bad-soft" aria-label={t("w.data.remove", { v: num(v) })} onClick={() => setNums((prev) => prev.filter((_, j) => j !== i))}>
                      {num(v)} <X size={11} aria-hidden="true" />
                    </button>
                  ))}
                </div>
              </div>
            ))}
        </div>
      )}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------- views */

/** Charts keep a readable size: never squeezed below ~60% or stretched beyond ~135% of their natural width. */
function Scroll({ w, children }: { w: number; children: React.ReactNode }) {
  return (
    <div dir="ltr" className="overflow-x-auto">
      <div className="mx-auto" style={{ minWidth: `${Math.round(w * 0.62)}px`, maxWidth: `${Math.round(w * 1.35)}px` }}>
        {children}
      </div>
    </div>
  );
}

/** A soft outline behind chart labels so they stay readable over bars and lines. */
const HALO = { stroke: "var(--card)", strokeWidth: 4, strokeLinejoin: "round" as const, paintOrder: "stroke" };

function BarChart({ t, items, showMean, showMedian, mean, median, modeLabels, aria }: { t: T; items: Datum[]; showMean: boolean; showMedian: boolean; mean: number; median: number; modeLabels: string[]; aria: string }) {
  const W = Math.max(330, 60 + items.length * 66);
  const H = 250;
  const L = 44;
  const B = H - 40;
  const top = 26;
  const ticks = countTicks(Math.max(...items.map((d) => d.value), 1));
  const yMax = ticks[ticks.length - 1];
  const Y = (v: number) => B - (v / yMax) * (B - top);
  const slot = (W - L - 12) / items.length;
  const near = Math.abs(Y(mean) - Y(median)) < 14;
  return (
    <Scroll w={W}>
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={aria}>
        {ticks.map((v) => (
          <g key={v}>
            <line x1={L} y1={Y(v)} x2={W - 12} y2={Y(v)} stroke="var(--line)" strokeWidth="1" />
            <text x={L - 7} y={Y(v) + 4} textAnchor="end" fontSize="11" fill="var(--muted)">
              {v}
            </text>
          </g>
        ))}
        <text x={12} y={(top + B) / 2} fontSize="11" fill="var(--muted)" textAnchor="middle" transform={`rotate(-90 12 ${(top + B) / 2})`}>
          {t("w.data.frequency")}
        </text>
        {items.map((d, i) => {
          const x = L + i * slot + slot * 0.18;
          const bw = slot * 0.64;
          const isMode = modeLabels.includes(d.label);
          return (
            <g key={i}>
              <rect x={x} y={Y(d.value)} width={bw} height={B - Y(d.value)} rx={3} fill="var(--sky)" opacity={0.85} stroke={isMode ? "var(--good)" : "none"} strokeWidth="3" style={{ transition: "y .3s, height .3s" }}>
                <title>{`${d.label}: ${num(d.value)}`}</title>
              </rect>
              <text x={x + bw / 2} y={Y(d.value) - 6} textAnchor="middle" fontSize="12" fontWeight="700" fill="var(--ink)">
                {num(d.value)}
              </text>
              {isMode && (
                <text x={x + bw / 2} y={Y(d.value) - 20} textAnchor="middle" fontSize="10" fontWeight="700" fill="var(--good)" {...HALO}>
                  {t("w.data.modeShort")}
                </text>
              )}
              <text x={x + bw / 2} y={B + 17} textAnchor="middle" fontSize="11.5" fill="var(--ink-2)">
                {short(d.label)}
              </text>
            </g>
          );
        })}
        <line x1={L} y1={B} x2={W - 12} y2={B} stroke="var(--ink-2)" strokeWidth="1.5" />
        {showMean && Number.isFinite(mean) && (
          <g>
            <line x1={L} y1={Y(mean)} x2={W - 12} y2={Y(mean)} stroke="var(--formal)" strokeWidth="2" strokeDasharray="7 4" />
            <text x={W - 14} y={Y(mean) - 5} textAnchor="end" fontSize="11" fontWeight="700" fill="var(--formal)" {...HALO}>
              {t("w.data.meanShort")} {stat2(mean)}
            </text>
          </g>
        )}
        {showMedian && Number.isFinite(median) && (
          <g>
            <line x1={L} y1={Y(median)} x2={W - 12} y2={Y(median)} stroke="var(--compute)" strokeWidth="2" strokeDasharray="2 4" />
            <text x={L + 4} y={Y(median) + (near && showMean ? 14 : -5)} fontSize="11" fontWeight="700" fill="var(--compute)" {...HALO}>
              {t("w.data.medianShort")} {stat2(median)}
            </text>
          </g>
        )}
      </svg>
    </Scroll>
  );
}

function TallyMarks({ count }: { count: number }) {
  const { fives, ones } = tally(count);
  const gateW = 30;
  const w = fives * gateW + ones * 7 + 4;
  return (
    <svg viewBox={`0 0 ${Math.max(w, 8)} 22`} width={Math.max(w, 8)} height={22} aria-hidden="true">
      {Array.from({ length: fives }, (_, g) => (
        <g key={g} stroke="var(--ink)" strokeWidth="2" strokeLinecap="round">
          {[0, 1, 2, 3].map((k) => (
            <line key={k} x1={g * gateW + 3 + k * 6} y1={3} x2={g * gateW + 3 + k * 6} y2={19} />
          ))}
          <line x1={g * gateW} y1={16} x2={g * gateW + 24} y2={6} stroke="var(--human)" />
        </g>
      ))}
      {Array.from({ length: ones }, (_, k) => (
        <line key={k} x1={fives * gateW + 3 + k * 7} y1={3} x2={fives * gateW + 3 + k * 7} y2={19} stroke="var(--ink)" strokeWidth="2" strokeLinecap="round" />
      ))}
    </svg>
  );
}

function TallyTable({ t, rows, modeLabels, header }: { t: T; rows: Datum[]; modeLabels: string[]; header: string }) {
  return (
    <div className="overflow-x-auto">
      <table className="w-full text-sm">
        <thead>
          <tr className="text-xs text-muted">
            <th className="py-1.5 text-start font-semibold">{header}</th>
            <th className="py-1.5 text-start font-semibold">{t("w.data.tallyCol")}</th>
            <th className="py-1.5 text-end font-semibold">{t("w.data.frequency")}</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r, i) => (
            <tr key={i} className="border-t border-line">
              <td className="py-2 pe-3 text-ink">
                {r.label}
                {modeLabels.includes(r.label) && <span className="chip ms-2 !border-good !bg-good-soft !text-good">{t("w.data.modeShort")}</span>}
              </td>
              <td className="py-2" dir="ltr">
                <TallyMarks count={r.value} />
              </td>
              <td className="py-2 text-end font-mono font-bold text-ink">{r.value}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

function Star({ fraction = 1 }: { fraction?: number }) {
  const f = Math.max(0, Math.min(1, fraction));
  return (
    <span className="relative inline-block h-5 w-5 shrink-0">
      <svg viewBox="0 0 24 24" className="absolute inset-0 h-5 w-5" aria-hidden="true">
        <path d="M12 1.8l2.9 6.6 7.1.6-5.4 4.7 1.6 7-6.2-3.7-6.2 3.7 1.6-7L2 9l7.1-.6z" fill="none" stroke="var(--line-2)" strokeWidth="1" strokeDasharray={f < 1 ? "2 2" : undefined} opacity={f < 1 ? 1 : 0} />
      </svg>
      <span className="absolute inset-y-0 start-0 overflow-hidden" style={{ width: `${f * 100}%` }} dir="ltr">
        <svg viewBox="0 0 24 24" className="h-5 w-5" aria-hidden="true">
          <path d="M12 1.8l2.9 6.6 7.1.6-5.4 4.7 1.6 7-6.2-3.7-6.2 3.7 1.6-7L2 9l7.1-.6z" fill="var(--gold)" />
        </svg>
      </span>
    </span>
  );
}

function Pictograph({ t, items, k, options, setK }: { t: T; items: Datum[]; k: number; options: number[]; setK: (k: number) => void }) {
  const partial = k > 1 && items.some((d) => d.value % k !== 0);
  return (
    <div>
      <div className="space-y-1.5">
        {items.map((d, i) => {
          const whole = Math.floor(d.value / k);
          const rest = (d.value % k) / k;
          return (
            <div key={i} className="flex items-center gap-3 border-b border-line pb-1.5" role="img" aria-label={`${d.label}: ${d.value}`}>
              <span className="w-24 shrink-0 truncate text-sm text-ink">{d.label}</span>
              <span className="flex min-w-0 flex-1 flex-wrap gap-0.5" dir="ltr">
                {Array.from({ length: whole }, (_, j) => (
                  <Star key={j} />
                ))}
                {rest > 0 && <Star fraction={rest} />}
              </span>
            </div>
          );
        })}
      </div>
      <div className="mt-3 flex flex-wrap items-center gap-2 rounded-xl bg-paper-2 px-3 py-2 text-sm text-ink-2">
        <span className="font-semibold text-ink">{t("w.data.key")}</span>
        <Star />
        <span dir="ltr" className="font-mono">
          = {k}
        </span>
        {options.length > 1 && (
          <span className="ms-auto flex flex-wrap items-center gap-1.5">
            <span className="text-xs">{t("w.data.keyChoose")}</span>
            {options.map((o) => (
              <button key={o} type="button" aria-pressed={o === k} className={`btn btn-sm !px-2.5 !py-1 ${o === k ? "btn-primary" : "btn-ghost"}`} onClick={() => setK(o)}>
                {o}
              </button>
            ))}
          </span>
        )}
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.data.keyEach", { k })}</p>
      {partial && <p className="mt-1 text-xs text-muted">{t("w.data.partialNote", { k })}</p>}
    </div>
  );
}

function CategoryDots({ t, items, aria, modeLabels }: { t: T; items: Datum[]; aria: string; modeLabels: string[] }) {
  const max = Math.max(1, ...items.map((d) => d.value));
  const gap = Math.min(18, 170 / max);
  const r = Math.min(7, gap / 2.2);
  const W = Math.max(320, 30 + items.length * 66);
  const B = 40 + max * gap;
  const H = B + 32;
  const slot = (W - 30) / items.length;
  return (
    <Scroll w={W}>
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={aria}>
        <line x1={14} y1={B} x2={W - 14} y2={B} stroke="var(--ink-2)" strokeWidth="1.5" />
        {items.map((d, i) => {
          const cx = 15 + slot * (i + 0.5);
          return (
            <g key={i}>
              {Array.from({ length: d.value }, (_, j) => (
                <circle key={j} cx={cx} cy={B - gap / 2 - j * gap} r={r} fill={modeLabels.includes(d.label) ? "var(--good)" : "var(--sky)"} />
              ))}
              <text x={cx} y={B - d.value * gap - 6} textAnchor="middle" fontSize="11" fontWeight="700" fill="var(--ink)">
                {d.value}
              </text>
              <text x={cx} y={B + 18} textAnchor="middle" fontSize="11.5" fill="var(--ink-2)">
                {short(d.label)}
              </text>
            </g>
          );
        })}
        {modeLabels.length > 0 && (
          <text x={W - 14} y={14} textAnchor="end" fontSize="10.5" fontWeight="700" fill="var(--good)">
            ● {t("w.data.modeShort")}
          </text>
        )}
      </svg>
    </Scroll>
  );
}

/** A numerical axis with nice ticks covering the values. */
function axisFor(values: number[]) {
  let lo = Math.min(...values);
  let hi = Math.max(...values);
  if (lo === hi) {
    lo -= 1;
    hi += 1;
  }
  const integers = values.every((v) => Number.isInteger(v));
  const step = integers && hi - lo <= 20 ? 1 : niceStep(hi - lo, 8);
  const a = Math.floor(lo / step + 1e-9) * step;
  const b = Math.ceil(hi / step - 1e-9) * step;
  const ticks = Array.from({ length: Math.round((b - a) / step) + 1 }, (_, i) => roundClean(a + i * step));
  return { a, b, ticks };
}

function Markers({ t, X, y, mean, median, showMean, showMedian }: { t: T; X: (v: number) => number; y: number; mean: number; median: number; showMean: boolean; showMedian: boolean }) {
  const close = Math.abs(X(mean) - X(median)) < 56;
  return (
    <g fontSize="11" fontWeight="700">
      {showMean && (
        <g fill="var(--formal)">
          <path d={`M${X(mean)} ${y} l-6 10 h12 z`} />
          <text x={X(mean)} y={y + 22} textAnchor="middle">
            {t("w.data.meanShort")} {stat2(mean)}
          </text>
        </g>
      )}
      {showMedian && (
        <g fill="var(--compute)">
          <path d={`M${X(median)} ${y} l6 6 -6 6 -6 -6 z`} />
          <text x={X(median)} y={y + (showMean && close ? 36 : 22)} textAnchor="middle">
            {t("w.data.medianShort")} {stat2(median)}
          </text>
        </g>
      )}
    </g>
  );
}

function NumberLineDots({ t, values, showMean, showMedian, modeValues, aria }: { t: T; values: number[]; showMean: boolean; showMedian: boolean; modeValues: number[]; aria: string }) {
  const { a, b, ticks } = axisFor(values);
  const W = 560;
  const freq = frequency(values);
  const maxC = Math.max(...freq.map((f) => f.count));
  const gap = Math.min(16, 150 / maxC);
  const r = Math.min(6.5, gap / 2.3);
  const B = 24 + maxC * gap;
  const H = B + 70;
  const X = (v: number) => 30 + ((v - a) / (b - a)) * (W - 60);
  const labelEvery = Math.ceil(ticks.length / 14);
  return (
    <Scroll w={W}>
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={aria}>
        <line x1={18} y1={B} x2={W - 18} y2={B} stroke="var(--ink-2)" strokeWidth="1.5" />
        {ticks.map((v, i) => (
          <g key={v}>
            <line x1={X(v)} y1={B} x2={X(v)} y2={B + 6} stroke="var(--ink-2)" strokeWidth="1.2" />
            {i % labelEvery === 0 && (
              <text x={X(v)} y={B + 19} textAnchor="middle" fontSize="11" fill="var(--ink-2)">
                {num(v)}
              </text>
            )}
          </g>
        ))}
        {freq.map((f) =>
          Array.from({ length: f.count }, (_, j) => <circle key={`${f.value}-${j}`} cx={X(f.value)} cy={B - gap / 2 - j * gap} r={r} fill={modeValues.includes(f.value) ? "var(--good)" : "var(--sky)"} />),
        )}
        {modeValues.length > 0 &&
          modeValues.map((v) => (
            <text key={`m${v}`} x={X(v)} y={B - maxC * gap - 4 + (maxC - (freq.find((f) => f.value === v)?.count ?? 0)) * gap} textAnchor="middle" fontSize="10" fontWeight="700" fill="var(--good)">
              {t("w.data.modeShort")}
            </text>
          ))}
        <Markers t={t} X={X} y={B + 26} mean={mean(values)} median={medianInfo(values).median} showMean={showMean} showMedian={showMedian} />
      </svg>
    </Scroll>
  );
}

function Histogram({ t, values, width, showMean, showMedian }: { t: T; values: number[]; width: number; showMean: boolean; showMedian: boolean }) {
  const bins = histogram(values, width);
  const W = 560;
  const L = 44;
  const top = 18;
  const B = 200;
  const H = B + 70;
  const a = bins[0].lo;
  const b = bins[bins.length - 1].hi;
  const X = (v: number) => L + ((v - a) / (b - a)) * (W - L - 20);
  const ticks = countTicks(Math.max(...bins.map((x) => x.count)));
  const yMax = ticks[ticks.length - 1];
  const Y = (v: number) => B - (v / yMax) * (B - top);
  const labelEvery = Math.ceil((bins.length + 1) / 12);
  return (
    <Scroll w={W}>
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={`${t("w.data.view.histogram")}: ${bins.map((x) => `[${num(x.lo)}, ${num(x.hi)}) ${x.count}`).join(", ")}`}>
        {ticks.map((v) => (
          <g key={v}>
            <line x1={L} y1={Y(v)} x2={W - 20} y2={Y(v)} stroke="var(--line)" />
            <text x={L - 7} y={Y(v) + 4} textAnchor="end" fontSize="11" fill="var(--muted)">
              {v}
            </text>
          </g>
        ))}
        <text x={12} y={(top + B) / 2} fontSize="11" fill="var(--muted)" textAnchor="middle" transform={`rotate(-90 12 ${(top + B) / 2})`}>
          {t("w.data.frequency")}
        </text>
        {bins.map((x, i) => (
          <g key={i}>
            <rect x={X(x.lo)} y={Y(x.count)} width={X(x.hi) - X(x.lo)} height={B - Y(x.count)} fill="var(--sky)" opacity={0.8} stroke="var(--card)" strokeWidth="1.5" />
            {x.count > 0 && (
              <text x={(X(x.lo) + X(x.hi)) / 2} y={Y(x.count) - 5} textAnchor="middle" fontSize="11.5" fontWeight="700" fill="var(--ink)">
                {x.count}
              </text>
            )}
          </g>
        ))}
        <line x1={L} y1={B} x2={W - 20} y2={B} stroke="var(--ink-2)" strokeWidth="1.5" />
        {[...bins.map((x) => x.lo), b].map((v, i) => (
          <g key={i}>
            <line x1={X(v)} y1={B} x2={X(v)} y2={B + 5} stroke="var(--ink-2)" />
            {i % labelEvery === 0 && (
              <text x={X(v)} y={B + 18} textAnchor="middle" fontSize="11" fill="var(--ink-2)">
                {num(v)}
              </text>
            )}
          </g>
        ))}
        <Markers t={t} X={X} y={B + 26} mean={mean(values)} median={medianInfo(values).median} showMean={showMean} showMedian={showMedian} />
      </svg>
    </Scroll>
  );
}

function FairShare({ t, items, levelled }: { t: T; items: Datum[]; levelled: boolean }) {
  const uid = useId().replace(/[^a-zA-Z0-9_-]/g, "");
  const values = items.map((d) => d.value);
  const fs = fairShare(values);
  const max = Math.max(1, ...values);
  const W = Math.max(320, 40 + items.length * 48);
  const unitPx = Math.min(24, 180 / max);
  const B = 26 + max * unitPx;
  const H = B + 30;
  const slot = (W - 30) / items.length;
  const tw = Math.min(32, slot * 0.7);
  const Y = (v: number) => B - v * unitPx;
  return (
    <Scroll w={W}>
      <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={`${t("w.data.view.fair")}: ${items.map((d) => `${d.label} ${num(d.value)}`).join(", ")}`}>
        <defs>
          <pattern id={`dc-hatch-${uid}`} width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
            <rect width="6" height="6" fill="var(--gold-soft)" />
            <line x1="0" y1="0" x2="0" y2="6" stroke="var(--gold)" strokeWidth="2" />
          </pattern>
        </defs>
        <line x1={12} y1={B} x2={W - 12} y2={B} stroke="var(--ink-2)" strokeWidth="1.5" />
        {items.map((d, i) => {
          const x = 15 + slot * (i + 0.5) - tw / 2;
          const own = levelled ? Math.min(d.value, fs.mean) : d.value;
          const whole = Math.floor(own + 1e-9);
          const frac = own - whole;
          return (
            <g key={i}>
              {Array.from({ length: whole }, (_, j) => (
                <rect key={j} x={x} y={Y(j + 1) + 1} width={tw} height={unitPx - 2} rx={2} fill="var(--sky)" opacity={0.85} />
              ))}
              {frac > 1e-9 && <rect x={x} y={Y(own) + 1} width={tw} height={Math.max(0, frac * unitPx - 2)} rx={2} fill="var(--sky)" opacity={0.85} />}
              {levelled && fs.received[i] > 1e-9 && <rect x={x} y={Y(fs.mean)} width={tw} height={fs.received[i] * unitPx} rx={2} fill={`url(#dc-hatch-${uid})`} stroke="var(--gold)" strokeWidth="1.2" />}
              {levelled && fs.given[i] > 1e-9 && <rect x={x} y={Y(d.value)} width={tw} height={fs.given[i] * unitPx} rx={2} fill="none" stroke="var(--muted)" strokeWidth="1.2" strokeDasharray="3 3" />}
              <text x={x + tw / 2} y={B + 17} textAnchor="middle" fontSize="11" fill="var(--ink-2)">
                {short(d.label, 8)}
              </text>
            </g>
          );
        })}
        {levelled && (
          <g>
            <line x1={12} y1={Y(fs.mean)} x2={W - 12} y2={Y(fs.mean)} stroke="var(--formal)" strokeWidth="2" strokeDasharray="7 4" />
            <text x={W - 14} y={Y(fs.mean) - 5} textAnchor="end" fontSize="11" fontWeight="700" fill="var(--formal)" {...HALO}>
              {t("w.data.fairShort")} {stat2(fs.mean)}
            </text>
          </g>
        )}
      </svg>
    </Scroll>
  );
}
