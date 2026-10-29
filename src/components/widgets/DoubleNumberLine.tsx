"use client";

import { Minus, Plus, Table2 } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { clampInt, range } from "./lib/number-common";
import { reduce, type Frac } from "./lib/number-fraction";
import { matchBottom, rationalText, simplestRatio, sliderStep } from "./lib/number-ratio";

interface DoubleNumberLineProps {
  /** The base ratio a : b (whole numbers). */
  a?: number;
  b?: number;
  /** Names of the two quantities, top line first, e.g. ["cups of flour", "cookies"]. */
  labels?: string[];
  /** How many multiples of the base ratio the lines show (1–12). */
  max?: number;
  /** Start with the table open. */
  table?: boolean;
  title?: string;
  subtitle?: string;
}

const W = 640;
const X0 = 46;
const X1 = W - 30;
const TOP = 74;
const BOT = 148;
const H = 214;

/** Ratios and rates on two parallel number lines that always stay in proportion. */
export function DoubleNumberLine({ a: a0, b: b0, labels, max: max0, table, title, subtitle }: DoubleNumberLineProps) {
  const { t, n } = useI18n();
  const a = clampInt(a0, 1, 1000, 3);
  const b = clampInt(b0, 1, 1000, 24);
  const max = clampInt(max0, 1, 12, 5);
  const names: [string, string] = [
    Array.isArray(labels) && typeof labels[0] === "string" && labels[0].trim() ? labels[0] : t("w.doubleLine.defaultTop"),
    Array.isArray(labels) && typeof labels[1] === "string" && labels[1].trim() ? labels[1] : t("w.doubleLine.defaultBottom"),
  ];
  const step = sliderStep(a, max);
  const [top, setTop] = useState(a);
  const [showTable, setShowTable] = useState(table === true);
  const topMax = max * a;
  const bottom = matchBottom(top, a, b);
  const mult: Frac = reduce({ n: top, d: a });
  const xOf = (v: number) => X0 + (v / topMax) * (X1 - X0);
  const x = xOf(top);
  const simple = simplestRatio(a, b);
  const unitB = matchBottom(1, a, b); // b/a of the bottom quantity per 1 of the top
  const unitA = reduce({ n: a, d: b }); // a/b of the top quantity per 1 of the bottom
  const isMultiple = mult.d === 1;
  const bw = (s: string) => Math.max(40, s.length * 7.4 + 14);
  const topText = `${top}`;
  const botText = rationalText(bottom);

  const tableRows = [
    ...(a > 1 ? [{ top: 1, key: "unit" }] : []),
    ...range(0, max).map((k) => ({ top: k * a, key: `k${k}` })),
    ...(top % a !== 0 && top !== 1 ? [{ top, key: "here" }] : []),
  ].sort((p, q) => p.top - q.top);

  return (
    <WidgetFrame title={title ?? t("w.doubleLine.title")} subtitle={subtitle ?? t("w.doubleLine.subtitle")}>
      <div dir="ltr" className="overflow-x-auto">
        <svg viewBox={`0 0 ${W} ${H}`} className="block w-full min-w-[30rem]" role="img" aria-label={t("w.doubleLine.aria", { a: n(a), b: n(b), top: names[0], bottom: names[1] })}>
          <text x={X0 - 10} y={18} fontSize="14" fontWeight="700" fill="var(--human)">
            {names[0]}
          </text>
          <text x={X0 - 10} y={H - 6} fontSize="14" fontWeight="700" fill="var(--formal)">
            {names[1]}
          </text>
          {/* connectors between matching multiples */}
          {range(0, max).map((k) => (
            <line key={`c${k}`} x1={xOf(k * a)} x2={xOf(k * a)} y1={TOP} y2={BOT} stroke="var(--line-2)" strokeDasharray="2 4" />
          ))}
          <line x1={X0 - 12} x2={X1 + 14} y1={TOP} y2={TOP} stroke="var(--human)" strokeWidth="2.5" />
          <line x1={X0 - 12} x2={X1 + 14} y1={BOT} y2={BOT} stroke="var(--formal)" strokeWidth="2.5" />
          {range(0, max).map((k) => (
            <g key={k}>
              <line x1={xOf(k * a)} x2={xOf(k * a)} y1={TOP - 9} y2={TOP + 9} stroke="var(--human)" strokeWidth="2" />
              <line x1={xOf(k * a)} x2={xOf(k * a)} y1={BOT - 9} y2={BOT + 9} stroke="var(--formal)" strokeWidth="2" />
              <text x={xOf(k * a)} y={TOP - 15} textAnchor="middle" fontSize="13" fontWeight="600" fill="var(--ink)">
                {k * a}
              </text>
              <text x={xOf(k * a)} y={BOT + 26} textAnchor="middle" fontSize="13" fontWeight="600" fill="var(--ink)">
                {k * b}
              </text>
            </g>
          ))}
          {a > 1 && (
            <g>
              <line x1={xOf(1)} x2={xOf(1)} y1={TOP - 6} y2={BOT + 6} stroke="var(--gold)" strokeWidth="1.5" strokeDasharray="4 3" />
              <text x={xOf(1)} y={TOP - 32} textAnchor="middle" fontSize="12" fontWeight="700" fill="var(--gold-ink)">
                1
              </text>
              <text x={xOf(1)} y={BOT + 42} textAnchor="middle" fontSize="12" fontWeight="700" fill="var(--gold-ink)">
                {rationalText(unitB)}
              </text>
            </g>
          )}
          {/* the moving marker */}
          <g style={{ transform: `translateX(${x}px)`, transition: "transform .25s ease-out" }}>
            <line x1={0} x2={0} y1={TOP} y2={BOT} stroke="var(--gold)" strokeWidth="3" />
            <circle cx={0} cy={TOP} r="7" fill="var(--gold)" stroke="var(--card)" strokeWidth="2.5" />
            <circle cx={0} cy={BOT} r="7" fill="var(--gold)" stroke="var(--card)" strokeWidth="2.5" />
            <rect x={-bw(topText) / 2} y={(TOP + BOT) / 2 - 24} width={bw(topText)} height={20} rx={6} fill="var(--card)" stroke="var(--gold)" />
            <text x={0} y={(TOP + BOT) / 2 - 9.5} textAnchor="middle" fontSize="12" fontWeight="700" fill="var(--human)">
              {topText}
            </text>
            <rect x={-bw(botText) / 2} y={(TOP + BOT) / 2 + 4} width={bw(botText)} height={20} rx={6} fill="var(--card)" stroke="var(--gold)" />
            <text x={0} y={(TOP + BOT) / 2 + 18.5} textAnchor="middle" fontSize="12" fontWeight="700" fill="var(--formal)">
              {botText}
            </text>
          </g>
        </svg>
      </div>

      <div className="mt-3 flex flex-wrap items-end gap-3">
        <button type="button" className="btn btn-ghost h-10 w-10 !p-0" aria-label={t("w.doubleLine.back", { a: n(a) })} disabled={top <= 0} onClick={() => setTop((v) => Math.max(0, Math.ceil(v / a) * a - a))}>
          <Minus size={16} aria-hidden="true" />
        </button>
        <label className="min-w-48 flex-1 text-sm font-semibold text-ink-2">
          {t("w.doubleLine.slide")}
          <input type="range" min={0} max={topMax} step={step} value={top} onChange={(e) => setTop(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--gold)]" dir="ltr" aria-valuetext={`${top} : ${rationalText(bottom)}`} />
        </label>
        <button type="button" className="btn btn-ghost h-10 w-10 !p-0" aria-label={t("w.doubleLine.forward", { a: n(a) })} disabled={top >= topMax} onClick={() => setTop((v) => Math.min(topMax, Math.floor(v / a) * a + a))}>
          <Plus size={16} aria-hidden="true" />
        </button>
      </div>

      <div className="mt-4 grid gap-4 md:grid-cols-2">
        <div className="rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
          <div className="flex items-stretch justify-center gap-3 text-center" dir="ltr">
            <div>
              <p className="font-serif text-4xl text-human">{top}</p>
              <p className="text-xs font-semibold text-ink-2" dir="auto">
                {names[0]}
              </p>
            </div>
            <p className="self-center font-serif text-3xl text-muted">:</p>
            <div>
              <p className="font-serif text-4xl text-formal">{rationalText(bottom)}</p>
              <p className="text-xs font-semibold text-ink-2" dir="auto">
                {names[1]}
              </p>
            </div>
          </div>
          <p className="mt-3 text-center font-serif text-lg text-ink-2" dir="ltr">
            {`${top} : ${rationalText(bottom)} = ${a} : ${b}`} <span className="text-sm">{`(× ${rationalText(mult)})`}</span>
          </p>
          <p className="mt-2 text-[0.95rem] text-ink">
            {top === 0 ? t("w.doubleLine.zero") : top === a ? t("w.doubleLine.base") : isMultiple ? t("w.doubleLine.multiple", { k: n(mult.n) }) : t("w.doubleLine.between")}
          </p>
        </div>
        <div className="space-y-3">
          <div className="rounded-xl border border-line bg-card px-4 py-3">
            <p className="text-sm font-semibold text-ink-2">{t("w.doubleLine.unitRates")}</p>
            <ul className="list-none ps-0 mt-1 space-y-1 text-[0.95rem] text-ink">
              <li>
                <span className="font-serif text-lg" dir="ltr">
                  {`1 : ${rationalText(unitB)}`}
                </span>{" "}
                <span className="text-sm text-ink-2">— {t("w.doubleLine.per", { amount: rationalText(unitB), what: names[1], each: names[0] })}</span>
              </li>
              <li>
                <span className="font-serif text-lg" dir="ltr">
                  {`${rationalText(unitA)} : 1`}
                </span>{" "}
                <span className="text-sm text-ink-2">— {t("w.doubleLine.per", { amount: rationalText(unitA), what: names[0], each: names[1] })}</span>
              </li>
            </ul>
          </div>
          <div className="rounded-xl border border-line bg-card px-4 py-3">
            <p className="text-sm font-semibold text-ink-2">{t("w.doubleLine.equivalent")}</p>
            <p className="mt-1 font-serif text-lg leading-relaxed text-ink" dir="ltr">
              {range(1, Math.min(max, 4))
                .map((k) => `${k * a} : ${k * b}`)
                .join(" = ")}
              {max > 4 ? " = …" : ""}
            </p>
            <p className="mt-1 text-sm text-ink-2">
              {simple.g > 1 ? t("w.doubleLine.simplest", { g: n(simple.g) }) : t("w.doubleLine.alreadySimplest")}{" "}
              <span className="font-serif text-base text-ink" dir="ltr">
                {`${simple.p} : ${simple.q}`}
              </span>
            </p>
          </div>
        </div>
      </div>

      <div className="mt-4">
        <button type="button" aria-pressed={showTable} aria-expanded={showTable} className={`btn btn-sm ${showTable ? "btn-primary" : "btn-ghost"}`} onClick={() => setShowTable((v) => !v)}>
          <Table2 size={14} aria-hidden="true" /> {t("w.doubleLine.table")}
        </button>
        {showTable && (
          <div className="mt-3 overflow-x-auto">
            <table className="w-full min-w-[18rem] border-collapse text-center text-sm [&_td]:text-center [&_th]:text-center">
              <thead>
                <tr className="border-b-2 border-line-2 text-ink-2">
                  <th className="px-3 py-1.5 font-semibold">×</th>
                  <th className="px-3 py-1.5 font-semibold text-human">{names[0]}</th>
                  <th className="px-3 py-1.5 font-semibold text-formal">{names[1]}</th>
                </tr>
              </thead>
              <tbody className="font-serif text-base" dir="ltr">
                {tableRows.map((r) => {
                  const here = r.top === top;
                  return (
                    <tr key={r.key} className={`border-b border-line ${here ? "bg-gold-soft font-semibold" : ""} ${r.key === "unit" ? "text-gold-ink" : "text-ink"}`}>
                      <td className="px-3 py-1">{rationalText(reduce({ n: r.top, d: a }))}</td>
                      <td className="px-3 py-1">{r.top}</td>
                      <td className="px-3 py-1">{rationalText(matchBottom(r.top, a, b))}</td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        )}
      </div>
    </WidgetFrame>
  );
}
