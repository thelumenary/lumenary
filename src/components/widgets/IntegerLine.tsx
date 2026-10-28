"use client";

import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const MIN = -10;
const MAX = 10;
const W = 640;
const X0 = 30;
const STEP = (W - 2 * X0) / (MAX - MIN);
const xOf = (v: number) => X0 + (v - MIN) * STEP;
const clamp = (v: number) => Math.max(MIN, Math.min(MAX, v));
const fmt = (v: number) => (v < 0 ? `−${-v}` : `${v}`);
const paren = (v: number) => (v < 0 ? `(${fmt(v)})` : fmt(v));

/**
 * Integers on a number line. "Add" shows a + b as a jump; "Opposite" shows
 * a + (−a) = 0 and −(−a) = a as reflections through zero.
 */
export function IntegerLine() {
  const { t } = useI18n();
  const [mode, setMode] = useState<"add" | "opposite">("add");
  const [a, setA] = useState(3);
  const [b, setB] = useState(-5);
  const [flips, setFlips] = useState(0);

  const sum = clamp(a + b);
  const flipped = flips % 2 === 0 ? a : -a;

  const arc = (from: number, to: number, color: string, above = true) => {
    const x1 = xOf(from);
    const x2 = xOf(to);
    const h = Math.min(70, 16 + Math.abs(x2 - x1) * 0.35);
    const y = 92;
    const cy = above ? y - h : y + h;
    return (
      <g>
        <path d={`M${x1} ${y} Q${(x1 + x2) / 2} ${cy} ${x2} ${y}`} fill="none" stroke={color} strokeWidth="2.5" strokeLinecap="round" markerEnd={`url(#arrow-${color === "var(--human)" ? "h" : "f"})`} />
      </g>
    );
  };

  return (
    <WidgetFrame title={t("w.int.title")} subtitle={t("w.int.subtitle")}>
      <div className="flex flex-wrap gap-2">
        {(["add", "opposite"] as const).map((m) => (
          <button key={m} type="button" aria-pressed={mode === m} className={`btn btn-sm ${mode === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setMode(m)}>
            {t(`w.int.mode.${m}`)}
          </button>
        ))}
      </div>
      <div dir="ltr" className="mt-4 overflow-x-auto">
        <svg viewBox={`0 0 ${W} 150`} className="min-w-[560px]" role="img" aria-label={mode === "add" ? `${fmt(a)} + ${paren(b)} = ${fmt(a + b)}` : `${fmt(a)}`}>
          <defs>
            <marker id="arrow-h" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
              <path d="M0 0 10 5 0 10z" fill="var(--human)" />
            </marker>
            <marker id="arrow-f" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
              <path d="M0 0 10 5 0 10z" fill="var(--formal)" />
            </marker>
          </defs>
          <line x1={X0 - 14} y1={92} x2={W - X0 + 14} y2={92} stroke="var(--ink-2)" strokeWidth="1.5" />
          {Array.from({ length: MAX - MIN + 1 }, (_, i) => MIN + i).map((v) => (
            <g key={v}>
              <line x1={xOf(v)} y1={v === 0 ? 82 : 86} x2={xOf(v)} y2={v === 0 ? 102 : 98} stroke={v === 0 ? "var(--gold)" : "var(--ink-2)"} strokeWidth={v === 0 ? 3 : 1.2} />
              <text x={xOf(v)} y={120} textAnchor="middle" fontSize="12" fill={v === 0 ? "var(--gold-ink)" : "var(--muted)"} fontWeight={v === 0 ? 700 : 500}>
                {fmt(v)}
              </text>
            </g>
          ))}
          {mode === "add" && (
            <>
              {arc(0, a, "var(--formal)")}
              {a + b >= MIN && a + b <= MAX && arc(a, a + b, "var(--human)", false)}
              <circle cx={xOf(a)} cy={92} r="7" fill="var(--formal)" />
              <circle cx={xOf(sum)} cy={92} r="8" fill="var(--human)" stroke="var(--card)" strokeWidth="2.5" />
            </>
          )}
          {mode === "opposite" && (
            <>
              <path d={`M${xOf(a)} 92 Q${xOf(0)} 20 ${xOf(-a)} 92`} fill="none" stroke="var(--formal)" strokeWidth="2" strokeDasharray="5 5" opacity="0.7" />
              <circle cx={xOf(a)} cy={92} r="7" fill={flips % 2 === 0 ? "var(--formal)" : "var(--line-2)"} />
              <circle cx={xOf(-a)} cy={92} r="7" fill={flips % 2 === 1 ? "var(--human)" : "var(--line-2)"} />
              <circle cx={xOf(flipped)} cy={92} r="11" fill="none" stroke="var(--gold)" strokeWidth="3" style={{ transition: "cx .45s cubic-bezier(.3,1.4,.6,1)" }} />
            </>
          )}
        </svg>
      </div>

      {mode === "add" ? (
        <div className="mt-3 grid gap-4 sm:grid-cols-[1fr_1fr_auto] sm:items-end">
          <Slider label={t("w.int.start")} value={a} onChange={setA} color="var(--formal)" />
          <Slider label={t("w.int.add")} value={b} onChange={setB} color="var(--human)" />
          <p className="rounded-xl bg-paper-2 px-4 py-2.5 text-center font-serif text-2xl text-ink" dir="ltr" aria-live="polite">
            {fmt(a)} + {paren(b)} = <strong>{fmt(a + b)}</strong>
          </p>
          <p className="text-sm text-ink-2 sm:col-span-3">{a + b === 0 ? t("w.int.home") : t("w.int.addHint")}</p>
        </div>
      ) : (
        <div className="mt-3 grid gap-4 sm:grid-cols-[1fr_auto] sm:items-end">
          <Slider label={t("w.int.number")} value={a} onChange={(v) => { setA(v); setFlips(0); }} color="var(--formal)" />
          <button type="button" className="btn btn-gold" onClick={() => setFlips((f) => f + 1)}>
            {t("w.int.flip")}
          </button>
          <p className="rounded-xl bg-paper-2 px-4 py-2.5 font-serif text-xl text-ink sm:col-span-2" dir="ltr" aria-live="polite">
            {flips === 0 ? fmt(a) : `${"−(".repeat(flips)}${fmt(a)}${")".repeat(flips)} = ${fmt(flipped)}`}
          </p>
          <p className="text-sm text-ink-2 sm:col-span-2">{flips >= 2 ? t("w.int.twice") : t("w.int.flipHint")}</p>
        </div>
      )}
    </WidgetFrame>
  );
}

function Slider({ label, value, onChange, color }: { label: string; value: number; onChange: (v: number) => void; color: string }) {
  return (
    <label className="block">
      <span className="flex items-center justify-between text-sm font-semibold text-ink-2">
        {label}
        <span className="font-mono text-ink" dir="ltr">
          {fmt(value)}
        </span>
      </span>
      <input type="range" min={MIN} max={MAX} value={value} onChange={(e) => onChange(Number(e.target.value))} className="mt-1.5 w-full" style={{ accentColor: color }} dir="ltr" />
    </label>
  );
}
