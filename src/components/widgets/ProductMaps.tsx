"use client";

import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const Z = ["p", "q", "r"];
const A = ["red", "blue"];
const B = ["1", "2", "3"];
const SWATCH: Record<string, string> = { red: "#d1495b", blue: "#3d7cc9" };

/**
 * The universal property of the product A × B, in finite sets: maps f : Z → A and g : Z → B
 * determine exactly one map h : Z → A × B with π₁ ∘ h = f and π₂ ∘ h = g.
 */
export function ProductMaps() {
  const { t } = useI18n();
  const [f, setF] = useState<string[]>(["red", "blue", "red"]);
  const [g, setG] = useState<string[]>(["2", "2", "3"]);
  const [h, setH] = useState<(string | null)[]>([null, null, null]);
  const [active, setActive] = useState(0);

  const filled = h.every(Boolean);
  const mismatch = Z.map((z, i) => {
    if (!h[i]) return null;
    const [a, b] = h[i]!.split("|");
    if (a !== f[i]) return t("w.prod.badFirst", { z, a, fa: t(`w.prod.c.${f[i]}`) });
    if (b !== g[i]) return t("w.prod.badSecond", { z, b, gb: g[i] });
    return null;
  }).find(Boolean);

  const sel = (vals: string[], set: (v: string[]) => void, opts: string[], name: string, colour = false) => (
    <div className="flex flex-wrap gap-2" dir="ltr">
      {Z.map((z, i) => (
        <label key={z} className="flex items-center gap-1 font-mono text-sm">
          {name}({z}) =
          <select
            className="input w-auto py-1"
            value={vals[i]}
            onChange={(e) => {
              set(vals.map((v, k) => (k === i ? e.target.value : v)));
              setH([null, null, null]);
            }}
          >
            {opts.map((o) => (
              <option key={o} value={o}>
                {colour ? t(`w.prod.c.${o}`) : o}
              </option>
            ))}
          </select>
        </label>
      ))}
    </div>
  );

  return (
    <WidgetFrame tone="gold" title={t("w.prod.title")} subtitle={t("w.prod.subtitle")}>
      <div className="grid gap-5 lg:grid-cols-[1fr_1.1fr]">
        <div className="space-y-3 text-sm">
          <p className="font-semibold text-ink-2">f : Z → A</p>
          {sel(f, setF, A, "f", true)}
          <p className="pt-1 font-semibold text-ink-2">g : Z → B</p>
          {sel(g, setG, B, "g")}
          <div className="rounded-xl bg-paper-2 p-3">
            <p className="text-xs font-semibold uppercase tracking-wide text-muted">⟨f, g⟩ : Z → A × B</p>
            <p className="mt-1 font-mono text-sm text-ink" dir="ltr">
              {Z.map((z, i) => `${z} ↦ (${t(`w.prod.c.${f[i]}`)}, ${g[i]})`).join("   ")}
            </p>
          </div>
        </div>
        <div>
          <p className="text-sm font-semibold text-ink">{t("w.prod.challenge")}</p>
          <div className="mt-2 flex gap-1.5" dir="ltr">
            {Z.map((z, i) => (
              <button key={z} type="button" aria-pressed={active === i} className={`btn btn-sm ${active === i ? "btn-primary" : "btn-ghost"} font-mono`} onClick={() => setActive(i)}>
                h({z}) {h[i] ? "✓" : "?"}
              </button>
            ))}
          </div>
          <div className="mt-3 overflow-x-auto" dir="ltr">
            <table className="border-separate border-spacing-1">
              <thead>
                <tr>
                  <th className="text-xs text-muted">A × B</th>
                  {B.map((b) => (
                    <th key={b} className="font-mono text-sm text-ink-2">
                      {b}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {A.map((a) => (
                  <tr key={a}>
                    <th className="pe-2 text-start text-sm font-semibold" style={{ color: SWATCH[a] }}>
                      {t(`w.prod.c.${a}`)}
                    </th>
                    {B.map((b) => {
                      const key = `${a}|${b}`;
                      const here = Z.filter((_, i) => h[i] === key);
                      return (
                        <td key={b}>
                          <button
                            type="button"
                            className="flex h-14 w-16 flex-wrap items-center justify-center gap-0.5 rounded-lg border-2 border-line bg-card font-mono text-xs hover:border-gold"
                            aria-label={`(${t(`w.prod.c.${a}`)}, ${b})`}
                            onClick={() => {
                              setH(h.map((v, k) => (k === active ? key : v)));
                              setActive((x) => Math.min(Z.length - 1, x + 1));
                            }}
                          >
                            {here.map((z) => (
                              <span key={z} className="rounded bg-gold px-1 font-bold text-[#1b1406]">
                                {z}
                              </span>
                            ))}
                          </button>
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <div className="mt-3 text-sm" aria-live="polite">
            {mismatch && <p className="rounded-lg bg-warn-soft px-3 py-2 text-warn">{mismatch}</p>}
            {filled && !mismatch && <p className="rounded-lg bg-good-soft px-3 py-2 text-good">{t("w.prod.unique")}</p>}
          </div>
        </div>
      </div>
    </WidgetFrame>
  );
}
