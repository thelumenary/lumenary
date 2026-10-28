"use client";

import { Package, PackagePlus, RotateCcw, Wand2 } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

/** A hereditarily finite set: a set whose elements are themselves such sets. */
type HF = HF[];

export function canon(s: HF): string {
  if (s.length === 0) return "∅";
  return `{${[...new Set(s.map(canon))].sort((a, b) => a.length - b.length || a.localeCompare(b)).join(", ")}}`;
}
function normalize(s: HF): HF {
  const seen = new Map<string, HF>();
  for (const x of s) seen.set(canon(x), normalize(x));
  return [...seen.entries()].sort(([a], [b]) => a.length - b.length || a.localeCompare(b)).map(([, v]) => v);
}

const DEPTH_TINT = ["var(--gold)", "var(--human)", "var(--formal)", "var(--compute)", "var(--sky)"];

function BoxView({ s, depth = 0 }: { s: HF; depth?: number }) {
  const color = DEPTH_TINT[depth % DEPTH_TINT.length];
  return (
    <span
      className="inline-flex min-h-7 min-w-7 flex-wrap items-center justify-center gap-1 rounded-lg border-2 p-1"
      style={{ borderColor: color, background: `color-mix(in oklab, ${color} 10%, transparent)` }}
    >
      {s.map((x, i) => (
        <BoxView key={i} s={x} depth={depth + 1} />
      ))}
    </span>
  );
}

export function BoxesNesting() {
  const { t } = useI18n();
  const [shelf, setShelf] = useState<HF[]>([[]]);
  const [picked, setPicked] = useState<number[]>([]);
  const [note, setNote] = useState<string | null>(null);

  const add = (s: HF) => {
    const n = normalize(s);
    const key = canon(n);
    if (shelf.some((x) => canon(x) === key)) setNote(t("w.boxes.already", { set: key }));
    else {
      setShelf((prev) => [...prev, n]);
      setNote(null);
    }
    setPicked([]);
  };
  const combine = () => {
    const chosen = picked.map((i) => shelf[i]);
    add(chosen);
  };
  const successor = () => {
    // The von Neumann successor of n is n ∪ {n}, starting from 0 = ∅.
    let n: HF = [];
    const keys = new Set(shelf.map(canon));
    while (keys.has(canon(n))) n = normalize([...n, n]);
    add(n);
  };

  return (
    <WidgetFrame tone="gold" title={t("w.boxes.title")} subtitle={t("w.boxes.subtitle")}>
      <div className="flex flex-wrap gap-2">
        <button type="button" className="btn btn-sm btn-primary" disabled={picked.length !== 1} onClick={combine}>
          <Package size={14} aria-hidden="true" /> {t("w.boxes.wrap")}
        </button>
        <button type="button" className="btn btn-sm btn-primary" disabled={picked.length < 2} onClick={combine}>
          <PackagePlus size={14} aria-hidden="true" /> {t("w.boxes.together")}
        </button>
        <button type="button" className="btn btn-sm btn-gold" onClick={successor}>
          <Wand2 size={14} aria-hidden="true" /> {t("w.boxes.next")}
        </button>
        <button
          type="button"
          className="btn btn-sm btn-ghost ms-auto"
          onClick={() => {
            setShelf([[]]);
            setPicked([]);
            setNote(null);
          }}
        >
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.boxes.howTo")}</p>
      <ul className="mt-4 grid gap-2 sm:grid-cols-2">
        {shelf.map((s, i) => {
          const on = picked.includes(i);
          return (
            <li key={canon(s)}>
              <button
                type="button"
                aria-pressed={on}
                onClick={() => setPicked((p) => (on ? p.filter((x) => x !== i) : [...p, i]))}
                className={`flex w-full items-center gap-3 rounded-xl border px-3 py-2.5 text-start transition-colors ${on ? "border-gold bg-gold-soft" : "border-line bg-card hover:bg-paper-2/60"}`}
              >
                <BoxView s={s} />
                <span className="min-w-0 flex-1">
                  <span className="block truncate font-serif text-[1.05rem] text-ink" dir="ltr">
                    {canon(s)}
                  </span>
                  <span className="text-xs text-muted">{t("w.boxes.elements", { n: s.length })}</span>
                </span>
              </button>
            </li>
          );
        })}
      </ul>
      <div aria-live="polite">{note && <p className="mt-3 rounded-xl bg-gold-soft px-4 py-2.5 text-sm text-ink">{note}</p>}</div>
      {shelf.length >= 4 && <p className="mt-3 text-sm leading-relaxed text-ink-2">{t("w.boxes.vonNeumann")}</p>}
    </WidgetFrame>
  );
}
