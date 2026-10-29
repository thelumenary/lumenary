"use client";

import { useId, useState, useSyncExternalStore, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import type { CompileResult, ExprError } from "./expr";
import { toNumber } from "./expr";

/** Series colours and dash patterns: curves are told apart by both, never by colour alone. */
export const SERIES_COLORS = ["var(--formal)", "var(--human)", "var(--compute)", "var(--sky)", "var(--gold)", "var(--bad)"] as const;
export const SERIES_DASHES = ["", "9 5", "2.5 4", "12 4 2.5 4", "16 6", "5 3"] as const;
export const seriesColor = (i: number) => SERIES_COLORS[((i % SERIES_COLORS.length) + SERIES_COLORS.length) % SERIES_COLORS.length];
export const seriesDash = (i: number) => SERIES_DASHES[((i % SERIES_DASHES.length) + SERIES_DASHES.length) % SERIES_DASHES.length];

/** Row of mutually exclusive buttons (aria-pressed). */
export function ModeTabs<T extends string>({ value, options, onChange, label, render }: { value: T; options: readonly T[]; onChange: (v: T) => void; label: string; render: (v: T) => ReactNode }) {
  return (
    <div role="group" aria-label={label} className="flex flex-wrap gap-2">
      {options.map((m) => (
        <button key={m} type="button" aria-pressed={value === m} className={`btn btn-sm ${value === m ? "btn-primary" : "btn-ghost"}`} onClick={() => onChange(m)}>
          {render(m)}
        </button>
      ))}
    </div>
  );
}

/** Labelled range slider with the current value shown in a monospace read-out. */
export function Slider({
  label,
  value,
  min,
  max,
  step,
  onChange,
  display,
  accent = "var(--gold)",
  disabled,
  className = "",
}: {
  label: ReactNode;
  value: number;
  min: number;
  max: number;
  step: number;
  onChange: (v: number) => void;
  display?: ReactNode;
  accent?: string;
  disabled?: boolean;
  className?: string;
}) {
  return (
    <label className={`block min-w-0 ${className}`}>
      <span className="flex items-baseline justify-between gap-3 text-sm font-semibold text-ink-2">
        <span className="min-w-0">{label}</span>
        <span className="shrink-0 font-mono text-ink" dir="ltr">
          {display ?? value}
        </span>
      </span>
      <input
        type="range"
        min={min}
        max={max}
        step={step}
        value={value}
        disabled={disabled}
        onChange={(e) => onChange(Number(e.target.value))}
        className="mt-1.5 w-full"
        style={{ accentColor: accent }}
        dir="ltr"
      />
    </label>
  );
}

/** Translated, caret-marked message for an expression error. */
export function ExprErrorNote({ error, source, id }: { error: ExprError; source: string; id?: string }) {
  const { t } = useI18n();
  const key = error.code === "arity" ? `w.plot.err.arity${error.params.count === 2 ? 2 : 1}` : `w.plot.err.${error.code}`;
  const msg = t(key, error.params);
  const pos = Math.max(0, Math.min(source.length, error.pos));
  const showCaret = source.length > 0 && source.length <= 120 && error.code !== "empty" && error.code !== "tooLong";
  return (
    <div id={id} role="alert" className="mt-1.5 rounded-lg border border-bad/40 bg-bad-soft px-3 py-2 text-sm text-ink">
      <p>
        <span className="font-semibold text-bad">{t("w.plot.ui.error")}</span> {msg}
      </p>
      {showCaret && (
        <p className="mt-1 overflow-x-auto whitespace-pre font-mono text-xs text-ink-2" dir="ltr" aria-label={t("w.plot.ui.errorAt", { pos: pos + 1 })}>
          {source.slice(0, pos)}
          <mark className="rounded-sm bg-bad px-px text-card">{source[pos] ?? " "}</mark>
          {source.slice(pos + 1)}
        </p>
      )}
    </div>
  );
}

/** Text input for an expression, showing a friendly error under it. */
export function ExprField({
  label,
  value,
  onChange,
  result,
  prefix,
  placeholder,
  className = "",
}: {
  label: ReactNode;
  value: string;
  onChange: (v: string) => void;
  result?: CompileResult;
  prefix?: ReactNode;
  placeholder?: string;
  className?: string;
}) {
  const id = useId();
  const bad = result && !result.ok;
  return (
    <div className={`min-w-0 ${className}`}>
      <label htmlFor={id} className="text-sm font-semibold text-ink-2">
        {label}
      </label>
      <div className="mt-1 flex items-center gap-2" dir="ltr">
        {prefix && <span className="shrink-0 font-serif text-lg italic text-ink">{prefix}</span>}
        <input
          id={id}
          type="text"
          value={value}
          placeholder={placeholder}
          spellCheck={false}
          autoCapitalize="off"
          autoCorrect="off"
          autoComplete="off"
          aria-invalid={bad || undefined}
          aria-describedby={bad ? `${id}-err` : undefined}
          onChange={(e) => onChange(e.target.value)}
          className={`input py-1.5 font-mono text-sm ${bad ? "!border-bad" : ""}`}
        />
      </div>
      {result && !result.ok && <ExprErrorNote id={`${id}-err`} error={result.error} source={result.source} />}
    </div>
  );
}

/** Editable number used for plain values. Also accepts expressions like "pi/2" or "sqrt(2)". */
export function NumberField({ label, value, onChange, digits = 4, className = "", inputClassName = "w-24" }: { label: ReactNode; value: number; onChange: (v: number) => void; digits?: number; className?: string; inputClassName?: string }) {
  const id = useId();
  const [text, setText] = useState<string | null>(null);
  const plain = Number.isFinite(value) ? String(Number(value.toFixed(digits))) : "";
  const shown = text ?? plain;
  const bad = text !== null && !Number.isFinite(toNumber(text, NaN));
  return (
    <span className={`inline-flex items-center gap-2 ${className}`}>
      <label htmlFor={id} className="text-sm font-semibold text-ink-2">
        {label}
      </label>
      <input
        id={id}
        type="text"
        inputMode="decimal"
        value={shown}
        dir="ltr"
        spellCheck={false}
        aria-invalid={bad || undefined}
        onFocus={() => setText(plain)}
        onBlur={() => setText(null)}
        onChange={(e) => {
          setText(e.target.value);
          const v = toNumber(e.target.value, NaN);
          if (Number.isFinite(v)) onChange(v);
        }}
        onKeyDown={(e) => {
          if (e.key === "Enter") (e.target as HTMLInputElement).blur();
        }}
        className={`input px-2 py-1 text-center font-mono text-sm ${bad ? "!border-bad" : ""} ${inputClassName}`}
      />
    </span>
  );
}

/** Result box announced politely to screen readers. */
export function Readout({ children, className = "" }: { children: ReactNode; className?: string }) {
  return (
    <div className={`rounded-xl bg-paper-2 px-4 py-3 text-ink ${className}`} aria-live="polite">
      {children}
    </div>
  );
}

/** Legend entry: a short line sample in the series' colour and dash pattern. */
export function LegendSwatch({ color, dash, width = 3 }: { color: string; dash?: string; width?: number }) {
  return (
    <svg width="28" height="10" viewBox="0 0 28 10" aria-hidden="true" className="shrink-0">
      <line x1="2" y1="5" x2="26" y2="5" stroke={color} strokeWidth={width} strokeDasharray={dash || undefined} strokeLinecap="round" />
    </svg>
  );
}

const motionQuery = "(prefers-reduced-motion: reduce)";
function subscribeMotion(cb: () => void) {
  if (typeof window === "undefined" || !window.matchMedia) return () => {};
  const mq = window.matchMedia(motionQuery);
  mq.addEventListener?.("change", cb);
  return () => mq.removeEventListener?.("change", cb);
}

/** True when the reader asked for reduced motion (false during the server render). */
export function useReducedMotion(): boolean {
  return useSyncExternalStore(
    subscribeMotion,
    () => (typeof window !== "undefined" && window.matchMedia ? window.matchMedia(motionQuery).matches : false),
    () => false,
  );
}
