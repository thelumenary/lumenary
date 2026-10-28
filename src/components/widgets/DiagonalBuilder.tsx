"use client";

import { Plus, RotateCcw } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

const COLS = 10;
const START: number[][] = [
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 1, 0, 0, 1, 0, 0, 1],
  [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 0, 1, 1, 0],
];

/** Cantor's diagonal argument, finitely: whatever list you write, the flipped diagonal is missing from it. */
export function DiagonalBuilder() {
  const { t } = useI18n();
  const [rows, setRows] = useState<number[][]>(START);
  const [focus, setFocus] = useState<number | null>(null);
  const n = Math.min(rows.length, COLS);
  const diag = Array.from({ length: COLS }, (_, i) => (i < rows.length ? 1 - rows[i][i] : 0));

  const flip = (r: number, c: number) => setRows(rows.map((row, i) => (i === r ? row.map((b, j) => (j === c ? 1 - b : b)) : row)));

  return (
    <WidgetFrame tone="gold" title={t("w.diag.title")} subtitle={t("w.diag.subtitle")}>
      <div className="overflow-x-auto" dir="ltr">
        <table className="border-separate border-spacing-1 font-mono text-sm">
          <tbody>
            {rows.map((row, i) => (
              <tr key={i} onMouseEnter={() => setFocus(i)} onMouseLeave={() => setFocus(null)}>
                <th className="pe-2 text-end text-xs text-muted">s{i + 1}</th>
                {row.map((b, j) => {
                  const onDiag = i === j;
                  return (
                    <td key={j}>
                      <button
                        type="button"
                        onClick={() => flip(i, j)}
                        onFocus={() => setFocus(i)}
                        aria-label={`s${i + 1}, ${j + 1}: ${b}`}
                        className={`h-8 w-8 rounded-md border text-center font-bold transition-colors ${
                          onDiag ? "border-gold bg-gold-soft text-gold-ink" : "border-line bg-card text-ink-2"
                        } ${focus === i && onDiag ? "ring-2 ring-gold" : ""}`}
                      >
                        {b}
                      </button>
                    </td>
                  );
                })}
                <td className="ps-2 text-xs text-muted">…</td>
              </tr>
            ))}
            <tr>
              <td colSpan={COLS + 2} className="pt-2" />
            </tr>
            <tr>
              <th className="pe-2 text-end text-xs font-bold text-gold-ink">d</th>
              {diag.map((b, j) => (
                <td key={j}>
                  <span
                    className={`flex h-8 w-8 items-center justify-center rounded-md font-bold ${
                      j < n ? (focus === j ? "bg-gold text-[#1b1406] ring-2 ring-gold" : "bg-gold/80 text-[#1b1406]") : "border border-dashed border-line-2 text-muted"
                    }`}
                  >
                    {j < n ? b : "?"}
                  </span>
                </td>
              ))}
              <td className="ps-2 text-xs text-muted">…</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p className="mt-3 min-h-10 text-sm text-ink-2" aria-live="polite">
        {focus !== null && focus < n ? t("w.diag.differs", { i: focus + 1, a: rows[focus][focus], b: diag[focus] }) : t("w.diag.hover")}
      </p>
      <div className="mt-2 flex flex-wrap gap-2">
        <button type="button" className="btn btn-sm btn-gold" disabled={rows.length >= COLS} onClick={() => setRows([...rows, diag.slice()])}>
          <Plus size={14} aria-hidden="true" /> {t("w.diag.addD")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" onClick={() => setRows(START)}>
          <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
        </button>
      </div>
      <p className="mt-3 text-sm leading-relaxed text-ink-2">{t("w.diag.note")}</p>
    </WidgetFrame>
  );
}
