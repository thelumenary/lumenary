"use client";

import { Dices, Minus, Plus, RotateCcw, Shuffle } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { DEFAULT_SECTORS, cumulative, parseSectors, sectorFraction, sectorPath, spinMany, type SectorSpec } from "./lib/shape-spinner";
import { NAMED_COLOURS, seedFrom, toInt } from "./lib/shape-util";

export interface SpinnerProps {
  sectors?: { label: string; weight?: number; color?: string }[];
  spins?: number;
  seed?: number;
  editable?: boolean;
  title?: string;
  subtitle?: string;
}

const C = 120;
const R = 104;

/** Simple chance with a spinner: seeded spins (one or many), a tally, and observed vs. sector fractions. */
export function Spinner({ sectors, spins, seed, editable = true, title, subtitle }: SpinnerProps) {
  const { t, n } = useI18n();
  const initial = useMemo(() => parseSectors(sectors) ?? DEFAULT_SECTORS, [sectors]);
  const batch = toInt(spins, 10, 1, 1000);
  const seed0 = toInt(seed, 1, 0, 1_000_000);
  const [specs, setSpecs] = useState<SectorSpec[]>(initial);
  const [run, setRun] = useState(seed0);
  const [rng, setRng] = useState(() => seedFrom(seed0));
  const [counts, setCounts] = useState<number[]>(() => initial.map(() => 0));
  const [history, setHistory] = useState<number[]>([]);
  const [angle, setAngle] = useState(0);
  const [editing, setEditing] = useState(false);

  const weights = specs.map((s) => s.weight);
  const cum = cumulative(weights);
  const total = counts.reduce((s, c) => s + c, 0);
  const label = (s: SectorSpec) => s.label ?? t(`w.spinner.colour.${s.colour}`);
  const integerWeights = weights.every((w) => Number.isInteger(w));
  const last = history.length ? history[history.length - 1] : null;

  const spin = (k: number) => {
    const res = spinMany(rng, k, weights);
    setRng(res.state);
    setCounts((prev) => {
      const next = [...prev];
      for (const o of res.outcomes) next[o]++;
      return next;
    });
    setHistory((prev) => [...prev, ...res.outcomes.slice(-24)].slice(-24));
    setAngle((a) => {
      const target = res.lastU * 360;
      const turns = k === 1 ? 3 : 1;
      return a + turns * 360 + ((((target - a) % 360) + 360) % 360);
    });
  };
  const restart = (newSeed: number, nextSpecs = specs) => {
    setRun(newSeed);
    setRng(seedFrom(newSeed));
    setCounts(nextSpecs.map(() => 0));
    setHistory([]);
  };
  const resize = (i: number, d: number) => {
    const next = specs.map((s, j) => (j === i ? { ...s, weight: Math.max(1, Math.min(12, s.weight + d)) } : s));
    setSpecs(next);
    restart(run, next);
  };

  return (
    <WidgetFrame title={title ?? t("w.spinner.title")} subtitle={subtitle ?? t("w.spinner.subtitle")}>
      <div className="grid items-start gap-6 md:grid-cols-[auto_1fr]">
        <div className="mx-auto w-full max-w-[16rem]" dir="ltr">
          <svg viewBox="0 0 240 240" className="w-full" role="img" aria-label={t("w.spinner.aria", { parts: specs.map((s, i) => `${label(s)} ${sectorFraction(weights, i) ?? `${Math.round((cum[i + 1] - cum[i]) * 100)}%`}`).join(", ") })}>
            <circle cx={C} cy={C} r={R + 8} fill="var(--paper-2)" stroke="var(--line-2)" strokeWidth="2" />
            {specs.map((s, i) => (
              <path key={i} d={sectorPath(C, C, R, cum[i], cum[i + 1])} fill={NAMED_COLOURS[s.colour]} stroke="var(--card)" strokeWidth="2.5" opacity={0.92} />
            ))}
            {specs.map((s, i) => {
              const span = cum[i + 1] - cum[i];
              if (span < 0.07) return null;
              const mid = 2 * Math.PI * ((cum[i] + cum[i + 1]) / 2);
              const rr = specs.length === 1 ? 0 : R * 0.62;
              const x = C + rr * Math.sin(mid);
              const y = C - rr * Math.cos(mid) + (specs.length === 1 ? 40 : 0);
              const text = label(s).slice(0, 10);
              const w = Math.max(26, text.length * 7 + 12);
              return (
                <g key={`l${i}`}>
                  <rect x={x - w / 2} y={y - 10} width={w} height={20} rx={10} fill="var(--card)" opacity={0.92} />
                  <text x={x} y={y + 4} textAnchor="middle" fontSize="11.5" fontWeight="700" fill="var(--ink)">
                    {text}
                  </text>
                </g>
              );
            })}
            <g style={{ transform: `rotate(${angle}deg)`, transformOrigin: `${C}px ${C}px`, transition: "transform 1.3s cubic-bezier(.15,.8,.25,1)" }}>
              <path d={`M${C} ${C - R + 10} L${C + 9} ${C - 8} L${C} ${C + 16} L${C - 9} ${C - 8} Z`} fill="var(--ink)" stroke="var(--card)" strokeWidth="2" strokeLinejoin="round" />
            </g>
            <circle cx={C} cy={C} r="9" fill="var(--card)" stroke="var(--ink)" strokeWidth="3" />
          </svg>
          <div className="mt-3 flex flex-wrap justify-center gap-2" dir="auto">
            <button type="button" className="btn btn-sm btn-gold" onClick={() => spin(1)}>
              <Dices size={14} aria-hidden="true" /> {t("w.spinner.spinOnce")}
            </button>
            {batch > 1 && (
              <button type="button" className="btn btn-sm btn-primary" onClick={() => spin(batch)}>
                {t("w.spinner.spinMany", { k: n(batch) })}
              </button>
            )}
          </div>
          <div className="mt-2 flex flex-wrap justify-center gap-2" dir="auto">
            <button type="button" className="btn btn-sm btn-ghost" disabled={total === 0} onClick={() => restart(run)}>
              <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => restart(run + 1)}>
              <Shuffle size={14} aria-hidden="true" /> {t("w.spinner.newRun")}
            </button>
          </div>
        </div>

        <div className="min-w-0 space-y-4">
          <div aria-live="polite" className="flex flex-wrap items-baseline justify-between gap-2">
            <p className="text-sm text-ink-2">{total === 0 ? t("w.spinner.none") : t("w.spinner.total", { k: n(total) })}</p>
            {last !== null && <p className="text-sm font-semibold text-ink">{t("w.spinner.landed", { label: label(specs[last]) })}</p>}
          </div>
          <div className="overflow-x-auto">
            <table className="w-full text-sm">
              <thead>
                <tr className="text-xs text-muted">
                  <th className="py-1.5 text-start font-semibold">{t("w.spinner.colSector")}</th>
                  <th className="py-1.5 text-end font-semibold">{t("w.spinner.colCount")}</th>
                  <th className="py-1.5 ps-3 text-start font-semibold">{t("w.spinner.colCompare")}</th>
                </tr>
              </thead>
              <tbody>
                {specs.map((s, i) => {
                  const expected = cum[i + 1] - cum[i];
                  const observed = total ? counts[i] / total : 0;
                  const frac = sectorFraction(weights, i);
                  return (
                    <tr key={i} className="border-t border-line align-middle">
                      <td className="py-2 pe-2">
                        <span className="flex items-center gap-2">
                          <span className="inline-block h-3.5 w-3.5 shrink-0 rounded-full" style={{ background: NAMED_COLOURS[s.colour] }} aria-hidden="true" />
                          <span className="font-semibold text-ink">{label(s)}</span>
                          {editing && integerWeights && (
                            <span className="ms-auto flex items-center gap-1">
                              <button type="button" className="btn btn-sm btn-ghost !p-1" aria-label={t("w.spinner.smaller", { label: label(s) })} disabled={s.weight <= 1} onClick={() => resize(i, -1)}>
                                <Minus size={12} aria-hidden="true" />
                              </button>
                              <button type="button" className="btn btn-sm btn-ghost !p-1" aria-label={t("w.spinner.bigger", { label: label(s) })} disabled={s.weight >= 12} onClick={() => resize(i, 1)}>
                                <Plus size={12} aria-hidden="true" />
                              </button>
                            </span>
                          )}
                        </span>
                      </td>
                      <td className="py-2 text-end font-mono font-bold text-ink">{n(counts[i])}</td>
                      <td className="py-2 ps-3">
                        <div className="space-y-1" dir="ltr">
                          <div className="flex items-center gap-2">
                            <div className="h-2.5 min-w-8 flex-1 overflow-hidden rounded-full bg-paper-2">
                              <div className="h-full rounded-full transition-[width] duration-500" style={{ width: `${observed * 100}%`, background: NAMED_COLOURS[s.colour] }} />
                            </div>
                            <span className="w-[5.6rem] shrink-0 text-end font-mono text-[0.7rem] text-ink">
                              {total ? `${counts[i]}/${total}` : "–"} <span className="text-muted">{total ? `${n(Math.round(observed * 1000) / 10)}%` : ""}</span>
                            </span>
                          </div>
                          <div className="flex items-center gap-2">
                            <div className="relative h-2.5 min-w-8 flex-1 rounded-full border border-dashed border-line-2">
                              <div className="absolute inset-y-0 start-0 rounded-full border-2" style={{ width: `${expected * 100}%`, borderColor: NAMED_COLOURS[s.colour] }} />
                            </div>
                            <span className="w-[5.6rem] shrink-0 text-end font-mono text-[0.7rem] text-ink-2">
                              {frac ?? ""} <span className="text-muted">{n(Math.round(expected * 1000) / 10)}%</span>
                            </span>
                          </div>
                        </div>
                      </td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
          <p className="flex flex-wrap gap-4 text-xs text-muted">
            <span className="flex items-center gap-1.5">
              <span className="inline-block h-2.5 w-6 rounded-full bg-ink-2" aria-hidden="true" /> {t("w.spinner.legendObserved")}
            </span>
            <span className="flex items-center gap-1.5">
              <span className="inline-block h-2.5 w-6 rounded-full border-2 border-ink-2" aria-hidden="true" /> {t("w.spinner.legendExpected")}
            </span>
          </p>
          {history.length > 0 && (
            <div>
              <p className="text-xs font-semibold text-muted">{t("w.spinner.history")}</p>
              <div className="mt-1 flex flex-wrap gap-1">
                {history.map((h, i) => (
                  <span key={i} className="inline-flex items-center gap-1 rounded-md bg-paper-2 px-1.5 py-0.5 text-[0.7rem] text-ink-2">
                    <span className="inline-block h-2 w-2 rounded-full" style={{ background: NAMED_COLOURS[specs[h].colour] }} aria-hidden="true" />
                    {label(specs[h]).slice(0, 8)}
                  </span>
                ))}
              </div>
            </div>
          )}
          <p className="rounded-xl bg-paper-2 px-4 py-3 text-sm text-ink-2">{t("w.spinner.note")}</p>
          <div className="flex flex-wrap items-center gap-2">
            {editable && integerWeights && (
              <button type="button" aria-pressed={editing} className={`btn btn-sm ${editing ? "btn-gold" : "btn-ghost"}`} onClick={() => setEditing((v) => !v)}>
                {t("w.spinner.edit")}
              </button>
            )}
            <span className="text-xs text-muted">{t("w.spinner.replayNote")}</span>
          </div>
        </div>
      </div>
    </WidgetFrame>
  );
}
