"use client";

import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const fmt = (v: number) => (v < 0 ? `−${-v}` : `${v}`);
const SEARCH = Array.from({ length: 25 }, (_, i) => i - 12);

/** Search for partners: b with a + b = 0, or b with a × b = 1, among integers −12…12 — then allow fractions. */
export function InverseFinder() {
  const { t } = useI18n();
  const [op, setOp] = useState<"+" | "×">("+");
  const [a, setA] = useState(4);
  const [fractions, setFractions] = useState(false);
  const target = op === "+" ? 0 : 1;
  const combine = (x: number, y: number) => (op === "+" ? x + y : x * y);
  const hits = SEARCH.filter((b) => combine(a, b) === target);
  const fractionPartner = op === "×" && fractions && a !== 0 && hits.length === 0 ? (a < 0 ? `−1/${-a}` : `1/${a}`) : null;

  return (
    <WidgetFrame tone="gold" title={t("w.inv.title")} subtitle={t("w.inv.subtitle")}>
      <div className="flex flex-wrap items-end gap-4">
        <div className="flex gap-2">
          {(["+", "×"] as const).map((o) => (
            <button key={o} type="button" aria-pressed={op === o} onClick={() => setOp(o)} className={`btn ${op === o ? "btn-primary" : "btn-ghost"} w-14 font-serif text-lg`}>
              {o}
            </button>
          ))}
        </div>
        <label className="min-w-48 flex-1 text-sm font-semibold text-ink-2">
          {t("w.inv.pick")} <span className="font-mono text-ink">a = {fmt(a)}</span>
          <input type="range" min={-6} max={6} value={a} onChange={(e) => setA(Number(e.target.value))} className="mt-2 w-full accent-[var(--gold)]" dir="ltr" />
        </label>
        {op === "×" && (
          <label className="flex items-center gap-2 text-sm font-semibold text-ink-2">
            <input type="checkbox" checked={fractions} onChange={(e) => setFractions(e.target.checked)} className="accent-[var(--gold)]" />
            {t("w.inv.allowFractions")}
          </label>
        )}
      </div>
      <p className="mt-4 font-serif text-xl text-ink" dir="ltr">
        {t("w.inv.lookingFor")} {fmt(a)} {op} b = {target}
      </p>
      <div className="mt-3 grid grid-cols-5 gap-1.5 sm:grid-cols-[repeat(13,minmax(0,1fr))]" dir="ltr">
        {SEARCH.map((b) => {
          const hit = combine(a, b) === target;
          return (
            <div key={b} className={`rounded-lg border px-1 py-1.5 text-center font-mono text-xs transition-colors ${hit ? "border-gold bg-gold text-[#1b1406] font-bold" : "border-line text-muted line-through decoration-line-2"}`} title={`${fmt(a)} ${op} ${fmt(b)} = ${fmt(combine(a, b))}`}>
              {fmt(b)}
            </div>
          );
        })}
      </div>
      <div className="mt-4 rounded-xl bg-card px-4 py-3 text-sm leading-relaxed text-ink-2" aria-live="polite">
        {hits.length > 0 && <p>{t("w.inv.found", { b: hits.map(fmt).join(", ") })}</p>}
        {hits.length === 0 && !fractionPartner && <p>{op === "×" && a === 0 ? t("w.inv.zero") : t("w.inv.none")}</p>}
        {fractionPartner && <p>{t("w.inv.fraction", { b: fractionPartner })}</p>}
        {op === "×" && <p className="mt-2 text-muted">{t("w.inv.onlyOnes")}</p>}
      </div>
    </WidgetFrame>
  );
}
