"use client";

import { Minus, Plus, RotateCcw } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { clampInt, oneOf } from "./lib/number-common";
import { countFacts, makeTenCounters, makeTenPlan } from "./lib/number-tenframe";

interface TenFrameProps {
  /** Dots already in the frame(s) in "count" mode (0–20). */
  count?: number;
  /** One or two ten-frames in "count" mode. */
  frames?: number;
  mode?: "count" | "make-ten";
  /** First addend in "make-ten" mode (0–10). */
  a?: number;
  /** Second addend in "make-ten" mode (0–10). */
  b?: number;
  title?: string;
  subtitle?: string;
}

/** Ten-frames for counting (K–2) and the "make ten" addition strategy. */
export function TenFrame({ count, frames, mode, a, b, title, subtitle }: TenFrameProps) {
  const { t } = useI18n();
  const m = oneOf(mode, ["count", "make-ten"] as const, "count");
  return m === "count" ? (
    <CountFrames count={count} frames={frames} title={title ?? t("w.tenFrame.title")} subtitle={subtitle ?? t("w.tenFrame.subtitleCount")} />
  ) : (
    <MakeTen a={a} b={b} title={title ?? t("w.tenFrame.titleMakeTen")} subtitle={subtitle ?? t("w.tenFrame.subtitleMakeTen")} />
  );
}

/* ------------------------------------------------------------------ count mode */

function CountFrames({ count, frames, title, subtitle }: { count?: number; frames?: number; title: string; subtitle: string }) {
  const { t, n } = useI18n();
  const initial = clampInt(count, 0, 20, 0);
  const nFrames = clampInt(frames, 1, 2, initial > 10 ? 2 : 1);
  const capacity = nFrames * 10;
  const [filled, setFilled] = useState<boolean[]>(() => Array.from({ length: capacity }, (_, i) => i < Math.min(initial, capacity)));
  const total = filled.filter(Boolean).length;
  const facts = countFacts(total, capacity);

  const toggle = (i: number) => setFilled((prev) => prev.map((v, k) => (k === i ? !v : v)));
  const addOne = () =>
    setFilled((prev) => {
      const i = prev.indexOf(false);
      return i < 0 ? prev : prev.map((v, k) => (k === i ? true : v));
    });
  const takeOne = () =>
    setFilled((prev) => {
      const i = prev.lastIndexOf(true);
      return i < 0 ? prev : prev.map((v, k) => (k === i ? false : v));
    });

  let message: string;
  if (total === 0) message = t("w.tenFrame.zero");
  else if (total === 20) message = t("w.tenFrame.twenty");
  else if (total === 10) message = nFrames === 2 ? `${t("w.tenFrame.isTen")} ${t("w.tenFrame.moreToTwenty", { k: n(10) })}` : t("w.tenFrame.isTen");
  else if (total < 10) message = t("w.tenFrame.moreToTen", { k: n(10 - total) });
  else message = `${t("w.tenFrame.tenAnd", { r: n(facts.ones), total: n(total) })} ${t("w.tenFrame.moreToTwenty", { k: n(20 - total) })}`;

  return (
    <WidgetFrame title={title} subtitle={subtitle}>
      <div className="grid items-start gap-6 md:grid-cols-[minmax(0,22rem)_1fr]">
        <div dir="ltr" className="mx-auto w-full max-w-[22rem] space-y-3">
          {Array.from({ length: nFrames }, (_, f) => (
            <div key={f} role="group" aria-label={t("w.tenFrame.frameLabel", { i: n(f + 1) })} className="grid grid-cols-5 gap-0 overflow-hidden rounded-xl border-[3px] border-ink-2 bg-card">
              {Array.from({ length: 10 }, (_, c) => {
                const i = f * 10 + c;
                const on = filled[i];
                return (
                  <button
                    key={c}
                    type="button"
                    aria-pressed={on}
                    aria-label={t("w.tenFrame.cell", { i: n(i + 1), total: n(capacity) })}
                    onClick={() => toggle(i)}
                    className={`relative flex aspect-square items-center justify-center border-line-2 transition-colors hover:bg-paper-2 ${c % 5 !== 4 ? "border-e-2" : ""} ${c < 5 ? "border-b-2" : ""}`}
                  >
                    <span
                      aria-hidden="true"
                      className="block h-[72%] w-[72%] rounded-full shadow-[inset_0_-3px_0_rgb(0_0_0/0.15)]"
                      style={{
                        background: f === 0 ? "var(--human)" : "var(--sky)",
                        transform: on ? "scale(1)" : "scale(0.2)",
                        opacity: on ? 1 : 0,
                        transition: "transform .22s cubic-bezier(.3,1.5,.6,1), opacity .18s ease",
                      }}
                    />
                  </button>
                );
              })}
            </div>
          ))}
        </div>

        <div className="space-y-4">
          <div className="rounded-2xl bg-paper-2 px-5 py-4 text-center" aria-live="polite">
            <p className="text-sm font-semibold text-ink-2">{t("w.tenFrame.howMany")}</p>
            <p className="font-serif text-6xl leading-tight text-ink">{n(total)}</p>
            {total > 10 && (
              <p className="font-serif text-xl text-ink-2" dir="ltr">
                {total} = 10 + {facts.ones}
              </p>
            )}
            <p className="mt-2 text-[0.95rem] text-ink">{message}</p>
          </div>
          <div className="flex flex-wrap gap-2">
            <button type="button" className="btn btn-primary" onClick={addOne} disabled={total >= capacity}>
              <Plus size={16} aria-hidden="true" /> {t("w.tenFrame.addOne")}
            </button>
            <button type="button" className="btn btn-ghost" onClick={takeOne} disabled={total === 0}>
              <Minus size={16} aria-hidden="true" /> {t("w.tenFrame.takeOne")}
            </button>
            <button type="button" className="btn btn-ghost" onClick={() => setFilled((prev) => prev.map(() => false))} disabled={total === 0}>
              <RotateCcw size={15} aria-hidden="true" /> {t("w.tenFrame.clear")}
            </button>
          </div>
        </div>
      </div>
    </WidgetFrame>
  );
}

/* ------------------------------------------------------------------ make-ten mode */

const GAP = 0.4; // gap between the two frames, in cell units
const HEIGHT = 4 + GAP;

function MakeTen({ a: a0, b: b0, title, subtitle }: { a?: number; b?: number; title: string; subtitle: string }) {
  const { t, n } = useI18n();
  const [a, setA] = useState(() => clampInt(a0, 0, 10, 8));
  const [b, setB] = useState(() => clampInt(b0, 0, 10, 5));
  const [moved, setMoved] = useState(false);
  const plan = makeTenPlan(a, b);
  const counters = makeTenCounters(a, b, moved);
  const top = counters.filter((c) => c.frame === 0).length;
  const bottom = counters.length - top;

  const change = (setter: (v: number) => void) => (v: number) => {
    setter(v);
    setMoved(false);
  };

  let equation: string;
  if (!moved) equation = `${a} + ${b} = ?`;
  else if (plan.toTen > 0 && plan.rest > 0) equation = `${a} + ${b} = ${a} + ${plan.toTen} + ${plan.rest} = 10 + ${plan.rest} = ${plan.total}`;
  else equation = `${a} + ${b} = ${plan.total}`;

  let message: string;
  if (!moved) message = t("w.tenFrame.mt.before", { a: n(a), b: n(b) });
  else if (a === 10) message = `${t("w.tenFrame.mt.alreadyTen")} ${t("w.tenFrame.mt.result", { rest: n(b), total: n(plan.total) })}`;
  else if (plan.rest > 0) message = `${t("w.tenFrame.mt.move", { k: n(plan.toTen), rest: n(plan.rest) })} ${t("w.tenFrame.mt.result", { rest: n(plan.rest), total: n(plan.total) })}`;
  else if (plan.total === 10) message = `${t("w.tenFrame.mt.moveAll", { b: n(b), total: n(plan.total) })} ${t("w.tenFrame.isTen")}`;
  else message = `${t("w.tenFrame.mt.moveAll", { b: n(b), total: n(plan.total) })} ${t("w.tenFrame.mt.short", { k: n(10 - plan.total) })}`;

  const pct = (v: number, of: number) => `${(v / of) * 100}%`;

  return (
    <WidgetFrame title={title} subtitle={subtitle}>
      <div className="grid items-start gap-6 md:grid-cols-[minmax(0,22rem)_1fr]">
        <div className="mx-auto w-full max-w-[22rem]">
          <div dir="ltr" className="relative w-full" style={{ aspectRatio: `5 / ${HEIGHT}` }} role="img" aria-label={t("w.tenFrame.mt.diagram", { top: n(top), bottom: n(bottom) })}>
            {[0, 1].map((f) => (
              <div
                key={f}
                className="absolute inset-x-0 grid grid-cols-5 overflow-hidden rounded-xl border-[3px] border-ink-2 bg-card"
                style={{ top: pct(f * (2 + GAP), HEIGHT), height: pct(2, HEIGHT) }}
              >
                {Array.from({ length: 10 }, (_, c) => (
                  <div key={c} className={`border-line-2 ${c % 5 !== 4 ? "border-e-2" : ""} ${c < 5 ? "border-b-2" : ""}`} />
                ))}
              </div>
            ))}
            {counters.map((c) => {
              const row = Math.floor(c.cell / 5);
              const col = c.cell % 5;
              const y = c.frame * (2 + GAP) + row;
              return (
                <span
                  key={c.id}
                  aria-hidden="true"
                  className="absolute flex items-center justify-center rounded-full shadow-[inset_0_-3px_0_rgb(0_0_0/0.15)]"
                  style={{
                    width: pct(0.68, 5),
                    height: pct(0.68, HEIGHT),
                    left: pct(col + 0.16, 5),
                    top: pct(y + 0.16, HEIGHT),
                    background: c.tone === "a" ? "var(--human)" : "var(--sky)",
                    transition: "left .6s cubic-bezier(.4,1.2,.5,1), top .6s cubic-bezier(.4,1.2,.5,1)",
                  }}
                >
                  {c.tone === "b" && <span className="block h-[38%] w-[38%] rounded-full bg-card" />}
                </span>
              );
            })}
          </div>
          <ul className="list-none ps-0 [&>li]:m-0 mt-3 flex flex-wrap justify-center gap-x-4 gap-y-1 text-sm text-ink-2">
            <li className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-block h-3.5 w-3.5 rounded-full bg-human" />
              {t("w.tenFrame.mt.legendA", { a: n(a) })}
            </li>
            <li className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-flex h-3.5 w-3.5 items-center justify-center rounded-full bg-sky">
                <span className="h-1.5 w-1.5 rounded-full bg-card" />
              </span>
              {t("w.tenFrame.mt.legendB", { b: n(b) })}
            </li>
          </ul>
        </div>

        <div className="space-y-4">
          <div className="grid gap-3 sm:grid-cols-2">
            <Stepper label={t("w.tenFrame.first")} value={a} onChange={change(setA)} />
            <Stepper label={t("w.tenFrame.second")} value={b} onChange={change(setB)} />
          </div>
          <div className="rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
            <p className="font-serif text-2xl leading-snug text-ink" dir="ltr">
              {equation}
            </p>
            <p className="mt-2 text-[0.95rem] text-ink">{message}</p>
          </div>
          <div className="flex flex-wrap gap-2">
            {!moved ? (
              <button type="button" className="btn btn-gold" onClick={() => setMoved(true)}>
                {t("w.tenFrame.mt.makeTen")}
              </button>
            ) : (
              <button type="button" className="btn btn-ghost" onClick={() => setMoved(false)}>
                <RotateCcw size={15} aria-hidden="true" /> {t("w.tenFrame.mt.back")}
              </button>
            )}
          </div>
        </div>
      </div>
    </WidgetFrame>
  );
}

function Stepper({ label, value, onChange }: { label: string; value: number; onChange: (v: number) => void }) {
  const { t, n } = useI18n();
  return (
    <div role="group" aria-label={label} className="rounded-xl border border-line bg-card px-3 py-2">
      <p className="text-sm font-semibold text-ink-2">{label}</p>
      <div className="mt-1 flex items-center justify-between gap-2">
        <button type="button" className="btn btn-ghost h-11 w-11 !p-0" aria-label={t("w.tenFrame.less", { label })} disabled={value <= 0} onClick={() => onChange(value - 1)}>
          <Minus size={18} aria-hidden="true" />
        </button>
        <span className="min-w-8 text-center font-serif text-3xl text-ink">{n(value)}</span>
        <button type="button" className="btn btn-ghost h-11 w-11 !p-0" aria-label={t("w.tenFrame.more", { label })} disabled={value >= 10} onClick={() => onChange(value + 1)}>
          <Plus size={18} aria-hidden="true" />
        </button>
      </div>
    </div>
  );
}
