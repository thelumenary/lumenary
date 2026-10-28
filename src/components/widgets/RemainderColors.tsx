"use client";

import { Shuffle } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const mod = (a: number, k: number) => ((a % k) + k) % k;
const fmt = (v: number) => (v < 0 ? `−${-v}` : `${v}`);
const PALETTE = ["var(--gold)", "var(--human)", "var(--formal)", "var(--compute)", "var(--sky)", "#c0567f"];
const tint = (c: string) => ({ borderColor: c, background: `color-mix(in oklab, ${c} 24%, var(--card))` });
const NUMS = Array.from({ length: 31 }, (_, i) => i - 15);

/** Partition the integers into remainder families, then test whether "family + family" is well defined. */
export function RemainderColors() {
  const { t } = useI18n();
  const [k, setK] = useState(3);
  const [fx, setFx] = useState(1);
  const [fy, setFy] = useState(2);
  const [samples, setSamples] = useState<[number, number][]>([]);

  const members = (r: number) => NUMS.filter((n) => mod(n, k) === r);
  const draw = () => {
    const xs = members(fx % k);
    const ys = members(fy % k);
    const pick = (arr: number[]) => arr[Math.floor(Math.random() * arr.length)];
    setSamples((prev) => [[pick(xs), pick(ys)] as [number, number], ...prev].slice(0, 6));
  };

  return (
    <WidgetFrame tone="gold" title={t("w.rem.title")} subtitle={t("w.rem.subtitle")}>
      <label className="block max-w-sm text-sm font-semibold text-ink-2">
        {t("w.rem.divideBy")} <span className="font-mono text-ink">k = {k}</span>
        <input
          type="range"
          min={2}
          max={6}
          value={k}
          onChange={(e) => {
            setK(Number(e.target.value));
            setSamples([]);
            setFx(1);
            setFy(Math.min(2, Number(e.target.value) - 1));
          }}
          className="mt-2 w-full accent-[var(--gold)]"
          dir="ltr"
        />
      </label>
      <div className="mt-4 flex flex-wrap gap-1" dir="ltr" role="img" aria-label={t("w.rem.line")}>
        {NUMS.map((n) => (
          <span key={n} className="flex h-9 w-9 items-center justify-center rounded-full border-2 font-mono text-xs font-bold text-ink" style={tint(PALETTE[mod(n, k)])}>
            {fmt(n)}
          </span>
        ))}
      </div>
      <ul className="mt-4 grid gap-1.5 text-sm" dir="ltr">
        {Array.from({ length: k }, (_, r) => (
          <li key={r} className="flex items-center gap-2">
            <span className="h-3 w-3 shrink-0 rounded-full" style={{ background: PALETTE[r] }} />
            <span className="font-semibold text-ink">[{r}]</span>
            <span className="truncate font-mono text-ink-2">
              {"{ …, "}
              {members(r).slice(0, 6).map(fmt).join(", ")}
              {", … }"}
            </span>
          </li>
        ))}
      </ul>
      <div className="mt-5 rounded-xl border border-line bg-card p-4">
        <p className="text-sm font-semibold text-ink">{t("w.rem.addTitle")}</p>
        <div className="mt-2 flex flex-wrap items-center gap-2 text-sm" dir="ltr">
          <select className="input w-auto py-1" value={fx} onChange={(e) => (setFx(Number(e.target.value)), setSamples([]))}>
            {Array.from({ length: k }, (_, r) => (
              <option key={r} value={r}>
                [{r}]
              </option>
            ))}
          </select>
          <span className="font-serif text-lg">+</span>
          <select className="input w-auto py-1" value={fy} onChange={(e) => (setFy(Number(e.target.value)), setSamples([]))}>
            {Array.from({ length: k }, (_, r) => (
              <option key={r} value={r}>
                [{r}]
              </option>
            ))}
          </select>
          <button type="button" className="btn btn-sm btn-gold" onClick={draw}>
            <Shuffle size={14} aria-hidden="true" /> {t("w.rem.pick")}
          </button>
        </div>
        <ul className="mt-3 space-y-1 font-mono text-sm" dir="ltr" aria-live="polite">
          {samples.map(([x, y], i) => (
            <li key={i} className="flex items-center gap-2">
              {fmt(x)} + {fmt(y)} = {fmt(x + y)}
              <span className="rounded-full border-2 px-2 text-xs font-bold text-ink" style={tint(PALETTE[mod(x + y, k)])}>
                [{mod(x + y, k)}]
              </span>
            </li>
          ))}
        </ul>
        {samples.length >= 3 && <p className="mt-3 text-sm text-ink-2">{t("w.rem.always", { r: mod(fx + fy, k) })}</p>}
      </div>
    </WidgetFrame>
  );
}
