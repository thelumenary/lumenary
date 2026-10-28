"use client";

import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const mod = (a: number, k: number) => ((a % k) + k) % k;
const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b));

/** Clock arithmetic: wrap-around addition on a k-hour clock, and the hunt for multiplicative partners. */
export function ClockLab() {
  const { t } = useI18n();
  const [k, setK] = useState(12);
  const [start, setStart] = useState(9);
  const [step, setStep] = useState(5);
  const [tab, setTab] = useState<"add" | "multiply">("add");
  const [showPattern, setShowPattern] = useState(false);
  const s = mod(start, k);
  const end = mod(s + step, k);
  const R = 92;
  const C = 110;
  const pos = (i: number) => {
    const ang = (i / k) * 2 * Math.PI - Math.PI / 2;
    return { x: C + R * Math.cos(ang), y: C + R * Math.sin(ang) };
  };
  const handAngle = (end / k) * 360;
  const hasPartner = (a: number) => Array.from({ length: k }, (_, b) => b).some((b) => mod(a * b, k) === 1);

  return (
    <WidgetFrame tone="gold" title={t("w.clock.title")} subtitle={t("w.clock.subtitle")}>
      <div className="flex flex-wrap items-end gap-4">
        <div className="flex gap-2">
          {(["add", "multiply"] as const).map((m) => (
            <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
              {t(`w.clock.tab.${m}`)}
            </button>
          ))}
        </div>
        <label className="min-w-44 flex-1 text-sm font-semibold text-ink-2">
          {t("w.clock.hours")} <span className="font-mono text-ink">k = {k}</span>
          <input type="range" min={2} max={tab === "add" ? 24 : 15} value={k} onChange={(e) => setK(Number(e.target.value))} className="mt-2 w-full accent-[var(--gold)]" dir="ltr" />
        </label>
      </div>

      {tab === "add" ? (
        <div className="mt-5 grid items-center gap-6 md:grid-cols-[auto_1fr]" dir="ltr">
          <svg viewBox="0 0 220 220" className="mx-auto w-56" role="img" aria-label={`${s} + ${step} ≡ ${end} (mod ${k})`}>
            <circle cx={C} cy={C} r={R + 16} fill="var(--card)" stroke="var(--line-2)" strokeWidth="2" />
            {Array.from({ length: k }, (_, i) => {
              const p = pos(i);
              const active = i === end;
              const origin = i === s;
              return (
                <g key={i}>
                  <circle cx={p.x} cy={p.y} r={k > 16 ? 8 : 11} fill={active ? "var(--gold)" : origin ? "var(--formal-soft)" : "var(--paper-2)"} stroke={origin ? "var(--formal)" : "none"} strokeWidth="2" />
                  <text x={p.x} y={p.y + 4} textAnchor="middle" fontSize={k > 16 ? 9 : 11} fontWeight="700" fill="var(--ink)">
                    {i}
                  </text>
                </g>
              );
            })}
            <g style={{ transform: `rotate(${handAngle}deg)`, transformOrigin: `${C}px ${C}px`, transition: "transform .6s cubic-bezier(.3,1.3,.6,1)" }}>
              <line x1={C} y1={C} x2={C} y2={C - R + 18} stroke="var(--ink)" strokeWidth="3" strokeLinecap="round" />
            </g>
            <circle cx={C} cy={C} r="5" fill="var(--ink)" />
          </svg>
          <div className="space-y-4">
            <div className="grid gap-3 sm:grid-cols-2">
              <label className="text-sm font-semibold text-ink-2">
                {t("w.clock.start")} <span className="font-mono text-ink">{s}</span>
                <input type="range" min={0} max={k - 1} value={s} onChange={(e) => setStart(Number(e.target.value))} className="mt-2 w-full accent-[var(--formal)]" />
              </label>
              <label className="text-sm font-semibold text-ink-2">
                {t("w.clock.add")} <span className="font-mono text-ink">{step}</span>
                <input type="range" min={0} max={3 * k} value={step} onChange={(e) => setStep(Number(e.target.value))} className="mt-2 w-full accent-[var(--gold)]" />
              </label>
            </div>
            <p className="rounded-xl bg-paper-2 px-4 py-3 font-serif text-2xl text-ink" aria-live="polite">
              {s} + {step} = {s + step} ≡ <strong className="text-gold-ink">{end}</strong> <span className="text-base text-muted">(mod {k})</span>
            </p>
            <p className="text-sm text-ink-2">{t("w.clock.addNote", { k, sum: s + step, end })}</p>
          </div>
        </div>
      ) : (
        <div className="mt-5" dir="ltr">
          <div className="overflow-x-auto">
            <table className="mx-auto border-separate border-spacing-0.5 text-center font-mono text-xs">
              <thead>
                <tr>
                  <th className="h-7 w-7 text-muted">×</th>
                  {Array.from({ length: k }, (_, b) => (
                    <th key={b} className="h-7 w-7 text-muted">
                      {b}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {Array.from({ length: k }, (_, a) => (
                  <tr key={a}>
                    <th className={`h-7 w-7 rounded ${hasPartner(a) ? "bg-gold-soft text-gold-ink" : "text-muted"}`}>{a}</th>
                    {Array.from({ length: k }, (_, b) => {
                      const v = mod(a * b, k);
                      return (
                        <td key={b} className={`h-7 w-7 rounded ${v === 1 ? "bg-gold font-bold text-[#1b1406]" : v === 0 ? "bg-paper-2 text-muted" : "bg-card text-ink-2"}`}>
                          {v}
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <div className="mx-auto mt-4 max-w-2xl space-y-2 text-sm text-ink-2" dir="auto">
            <p>
              {t("w.clock.partners")}{" "}
              <strong className="font-mono text-ink" dir="ltr">
                {"{"}
                {Array.from({ length: k }, (_, a) => a)
                  .filter(hasPartner)
                  .join(", ")}
                {"}"}
              </strong>
            </p>
            {!showPattern ? (
              <button type="button" className="btn btn-sm btn-ghost" onClick={() => setShowPattern(true)}>
                {t("w.clock.revealPattern")}
              </button>
            ) : (
              <p className="rounded-xl bg-gold-soft px-4 py-3 text-ink">
                {t("w.clock.pattern")}{" "}
                <span className="font-mono" dir="ltr">
                  {"{"}
                  {Array.from({ length: k }, (_, a) => a)
                    .filter((a) => gcd(a, k) === 1)
                    .join(", ")}
                  {"}"}
                </span>
              </p>
            )}
          </div>
        </div>
      )}
    </WidgetFrame>
  );
}
