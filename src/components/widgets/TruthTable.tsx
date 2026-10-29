"use client";

import { Columns3, GitCompareArrows } from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import type { TFunction } from "@/i18n/dictionary";
import { WidgetFrame } from "./WidgetFrame";
import { evaluate, parseFormula, show, showFull, truthTable, type LogicError } from "./lib/logic-core";

export interface TruthTableProps {
  formula?: string;
  compare?: string;
  showSubformulas?: boolean;
  title?: string;
  subtitle?: string;
}

const INSERTS: { sym: string; key: string; binary: boolean }[] = [
  { sym: "¬", key: "not", binary: false },
  { sym: "∧", key: "and", binary: true },
  { sym: "∨", key: "or", binary: true },
  { sym: "→", key: "implies", binary: true },
  { sym: "↔", key: "iff", binary: true },
  { sym: "(", key: "open", binary: false },
  { sym: ")", key: "close", binary: false },
];

const EXAMPLES = [
  { id: "contrapositive", f: "p → q", g: "¬q → ¬p" },
  { id: "converse", f: "p → q", g: "q → p" },
  { id: "deMorgan", f: "¬(p ∧ q)", g: "¬p ∨ ¬q" },
  { id: "excludedMiddle", f: "p ∨ ¬p", g: "" },
  { id: "distributive", f: "p ∧ (q ∨ r)", g: "(p ∧ q) ∨ (p ∧ r)" },
];

const asText = (v: unknown, fallback = "") => (typeof v === "string" ? v.slice(0, 200) : fallback);

export function errorText(t: TFunction, e: LogicError): string {
  switch (e.code) {
    case "empty":
      return t("w.truth.err.empty");
    case "tooLong":
      return t("w.truth.err.tooLong", { max: e.max });
    case "unknownSymbol":
      return t("w.truth.err.unknownSymbol", { symbol: e.symbol, pos: e.pos + 1 });
    case "unknownWord":
      return t("w.truth.err.unknownWord", { word: e.word, pos: e.pos + 1 });
    case "unexpected":
      return t("w.truth.err.unexpected", { symbol: e.symbol, pos: e.pos + 1 });
    case "missingOperand":
      return t("w.truth.err.missingOperand", { pos: e.pos + 1 });
    case "missingClose":
      return t("w.truth.err.missingClose", { pos: e.pos + 1 });
    case "tooDeep":
      return t("w.truth.err.tooDeep");
    case "tooManyVars":
      return t("w.truth.err.tooManyVars", { count: e.count, max: e.max });
  }
}

/** Truth tables with sub-formula columns, classification, and an equivalence check against a second formula. */
export function TruthTable({ formula, compare, showSubformulas, title, subtitle }: TruthTableProps) {
  const { t, n } = useI18n();
  const [f1, setF1] = useState(asText(formula, "p → q") || "p → q");
  const [f2, setF2] = useState(asText(compare));
  const [comparing, setComparing] = useState(asText(compare).trim() !== "");
  const [subs, setSubs] = useState(showSubformulas !== false);
  const ref1 = useRef<HTMLInputElement>(null);
  const ref2 = useRef<HTMLInputElement>(null);
  const lastFocus = useRef<1 | 2>(1);
  const pendingCaret = useRef<{ which: 1 | 2; pos: number } | null>(null);

  // Restore focus and caret after inserting a symbol.
  useEffect(() => {
    const pc = pendingCaret.current;
    if (!pc) return;
    pendingCaret.current = null;
    const el = pc.which === 1 ? ref1.current : ref2.current;
    if (el) {
      el.focus();
      el.setSelectionRange(pc.pos, pc.pos);
    }
  });

  const p1 = useMemo(() => parseFormula(f1), [f1]);
  const p2 = useMemo(() => (comparing && f2.trim() ? parseFormula(f2) : null), [comparing, f2]);
  const table = useMemo(() => (p1.ok ? truthTable(p1.formula, p2 && p2.ok ? p2.vars : []) : null), [p1, p2]);
  const second = useMemo(() => (table && p2 && p2.ok ? table.rows.map((env) => evaluate(p2.formula, env)) : null), [table, p2]);
  const diff = useMemo(() => (table && second ? table.main.map((v, i) => (v !== second[i] ? i : -1)).filter((i) => i >= 0) : []), [table, second]);
  const diffSet = new Set(diff);

  const insert = (sym: string, binary: boolean) => {
    const which: 1 | 2 = comparing ? lastFocus.current : 1;
    const el = which === 1 ? ref1.current : ref2.current;
    const val = which === 1 ? f1 : f2;
    const start = el?.selectionStart ?? val.length;
    const end = el?.selectionEnd ?? val.length;
    const before = val.slice(0, start);
    const lead = binary && before.length > 0 && !/[\s(]$/.test(before) ? " " : "";
    const piece = binary ? `${lead}${sym} ` : sym;
    const next = before + piece + val.slice(end);
    if (which === 1) setF1(next);
    else setF2(next);
    pendingCaret.current = { which, pos: start + piece.length };
  };

  const TF = (v: boolean) => (v ? t("w.truth.T") : t("w.truth.F"));
  const rows = table?.rows.length ?? 0;
  const trueCount = table ? table.main.filter(Boolean).length : 0;

  const field = (which: 1 | 2) => {
    const val = which === 1 ? f1 : f2;
    const parsed = which === 1 ? p1 : p2;
    const id = which === 1 ? "formula" : "compare";
    return (
      <div>
        <label className="block text-sm font-semibold text-ink-2">
          {which === 1 ? t("w.truth.formula") : t("w.truth.compareLabel")}
          <input
            ref={which === 1 ? ref1 : ref2}
            type="text"
            dir="ltr"
            value={val}
            spellCheck={false}
            autoCapitalize="off"
            autoComplete="off"
            aria-invalid={parsed !== null && !parsed.ok}
            aria-describedby={`truth-${id}-status`}
            onFocus={() => (lastFocus.current = which)}
            onChange={(e) => (which === 1 ? setF1(e.target.value) : setF2(e.target.value))}
            className={`input mt-1.5 font-serif text-lg ${parsed && !parsed.ok ? "!border-bad" : ""}`}
            placeholder={which === 1 ? "p → q" : "¬q → ¬p"}
          />
        </label>
        <p id={`truth-${id}-status`} className="mt-1 min-h-[1.25rem] text-sm" aria-live="polite">
          {parsed === null ? null : parsed.ok ? (
            <span className="text-muted">
              {t("w.truth.readAs")}{" "}
              <span className="font-serif text-ink" dir="ltr">
                {showFull(parsed.formula)}
              </span>
            </span>
          ) : (
            <span className="text-bad">{errorText(t, parsed.error)}</span>
          )}
        </p>
      </div>
    );
  };

  return (
    <WidgetFrame title={title ?? t("w.truth.title")} subtitle={subtitle ?? t("w.truth.subtitle")}>
      <div className="space-y-3">
        {field(1)}
        <div className="flex flex-wrap items-center gap-1.5">
          {INSERTS.map((b) => (
            <button key={b.key} type="button" className="btn btn-sm btn-ghost min-h-9 min-w-9 px-2.5 font-serif text-base" aria-label={t("w.truth.insert", { symbol: b.sym, name: t(`w.truth.sym.${b.key}`) })} onClick={() => insert(b.sym, b.binary)}>
              {b.sym}
            </button>
          ))}
          <span className="mx-1 hidden h-6 w-px bg-line sm:inline-block" aria-hidden="true" />
          <button type="button" aria-pressed={comparing} className={`btn btn-sm min-h-9 ${comparing ? "btn-primary" : "btn-ghost"}`} onClick={() => setComparing((c) => !c)}>
            <GitCompareArrows size={14} aria-hidden="true" /> {t("w.truth.compare")}
          </button>
          <button type="button" aria-pressed={subs} className={`btn btn-sm min-h-9 ${subs ? "btn-primary" : "btn-ghost"}`} onClick={() => setSubs((s) => !s)}>
            <Columns3 size={14} aria-hidden="true" /> {t("w.truth.subformulas")}
          </button>
        </div>
        {comparing && field(2)}
        <p className="text-xs text-muted">{t("w.truth.syntax")}</p>
        <div className="flex flex-wrap items-center gap-1.5 text-xs">
          <span className="font-semibold text-muted">{t("w.truth.examples")}</span>
          {EXAMPLES.map((ex) => (
            <button
              key={ex.id}
              type="button"
              className="chip min-h-8 cursor-pointer hover:bg-line"
              onClick={() => {
                setF1(ex.f);
                setF2(ex.g);
                setComparing(ex.g !== "");
              }}
            >
              {t(`w.truth.example.${ex.id}`)}
            </button>
          ))}
        </div>
      </div>

      {table && (
        <>
          <div className="mt-4 flex flex-wrap gap-2" aria-live="polite">
            <p className={`rounded-xl px-4 py-2.5 text-sm ${table.classification === "tautology" ? "bg-good-soft" : table.classification === "contradiction" ? "bg-bad-soft" : "bg-paper-2"} text-ink`}>
              <strong>{t(`w.truth.class.${table.classification}`)}</strong> — {t(`w.truth.classWhy.${table.classification}`, { t: n(trueCount), rows: n(rows) })}
            </p>
            {second && (
              <p className={`rounded-xl px-4 py-2.5 text-sm text-ink ${diff.length === 0 ? "bg-good-soft" : "bg-warn-soft"}`}>
                <strong>{diff.length === 0 ? t("w.truth.equivalent") : t("w.truth.notEquivalent")}</strong> — {diff.length === 0 ? t("w.truth.equivalentWhy", { rows: n(rows) }) : t("w.truth.notEquivalentWhy", { count: n(diff.length), rows: n(rows) })}
              </p>
            )}
          </div>
          <div className="mt-3 max-h-[30rem] overflow-auto rounded-xl border border-line" dir="ltr">
            <table className="w-full border-collapse text-center text-sm [&_td]:!text-center [&_th]:!text-center">
              <thead className="sticky top-0 z-10 bg-card shadow-[0_1px_0_var(--line)]">
                <tr>
                  {table.vars.map((v) => (
                    <th key={v} scope="col" className="px-3 py-2 font-serif text-base italic text-ink">
                      {v}
                    </th>
                  ))}
                  {subs &&
                    table.columns.slice(0, -1).map((c) => (
                      <th key={c.label} scope="col" className="whitespace-nowrap border-s border-line px-3 py-2 font-serif text-base font-normal text-ink-2">
                        {c.label}
                      </th>
                    ))}
                  <th scope="col" className="whitespace-nowrap border-s-2 border-gold bg-gold-soft px-3 py-2 font-serif text-base text-ink">
                    {table.columns.length ? table.columns[table.columns.length - 1].label : f1.trim()}
                  </th>
                  {second && p2 && p2.ok && (
                    <th scope="col" className="whitespace-nowrap border-s border-line bg-sky-soft px-3 py-2 font-serif text-base text-ink">
                      {show(p2.formula)}
                    </th>
                  )}
                  {second && (
                    <th scope="col" className="w-10 px-2 py-2 text-xs font-semibold text-muted">
                      <span aria-hidden="true">≠</span>
                      <span className="sr-only">{t("w.truth.differs")}</span>
                    </th>
                  )}
                </tr>
              </thead>
              <tbody>
                {table.rows.map((env, i) => {
                  const differs = diffSet.has(i);
                  return (
                    <tr key={i} className={`border-t border-line/70 ${differs ? "bg-warn-soft" : i % 2 ? "bg-paper-2/40" : ""}`}>
                      {table.vars.map((v) => (
                        <td key={v} className={`px-3 py-1.5 font-mono ${env[v] ? "text-ink" : "text-muted"}`}>
                          {TF(env[v])}
                        </td>
                      ))}
                      {subs &&
                        table.columns.slice(0, -1).map((c) => (
                          <td key={c.label} className={`border-s border-line px-3 py-1.5 font-mono ${c.values[i] ? "text-ink-2" : "text-muted/80"}`}>
                            {TF(c.values[i])}
                          </td>
                        ))}
                      <td className={`border-s-2 border-gold px-3 py-1.5 font-mono font-bold ${table.main[i] ? "text-good" : "text-bad"}`}>{TF(table.main[i])}</td>
                      {second && (
                        <td className={`border-s border-line px-3 py-1.5 font-mono font-bold ${second[i] ? "text-good" : "text-bad"}`}>{TF(second[i])}</td>
                      )}
                      {second && <td className="px-2 py-1.5 font-bold text-warn">{differs ? "≠" : ""}</td>}
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
          <p className="mt-2 text-xs text-muted">{t("w.truth.rowsNote", { rows: n(rows), vars: n(table.vars.length) })}</p>
        </>
      )}
    </WidgetFrame>
  );
}
