"use client";

import { useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { elapsedJumps, format24, hourHandDelta, minuteFromAngle, minuteHandDelta, normTime, parts12, splitDuration, timeWords, toTime } from "./lib/shape-clock";
import { oneOf, toInt } from "./lib/shape-util";

export interface AnalogClockProps {
  hours?: number;
  minutes?: number;
  mode?: "read" | "elapsed";
  step?: number;
  elapsed?: number;
  digital?: boolean;
  title?: string;
  subtitle?: string;
}

const C = 130;
const R = 104;
const MAX_ELAPSED = 720;

/**
 * Reading an analogue clock: drag the hands (or use buttons/arrow keys) — the hour
 * hand always moves consistently with the minute hand. Shows 12- and 24-hour digital
 * time and the time in words; an elapsed-time mode counts on from a start time.
 */
export function AnalogClock({ hours, minutes, mode, step, elapsed, digital = true, title, subtitle }: AnalogClockProps) {
  const { t, n } = useI18n();
  const st = toInt(step, 5, 1, 60);
  const [tab, setTab] = useState<"read" | "elapsed">(oneOf(mode, ["read", "elapsed"] as const, "read"));
  // `tt` is unbounded (it may pass midnight many times) so the hands always turn the way they were moved.
  const [tt, setTt] = useState(toTime(toInt(hours, 3, 0, 23), toInt(minutes, 0, 0, 59)));
  const [gone, setGone] = useState(toInt(elapsed, 35, 0, MAX_ELAPSED));
  const [showDigital, setShowDigital] = useState(digital !== false);
  const [edgeMinutes, setEdgeMinutes] = useState(true);
  const [dragging, setDragging] = useState<null | "minute" | "hour">(null);
  const svgRef = useRef<SVGSVGElement>(null);
  /** The time under the pointer during a drag (several pointer events can arrive before React re-renders). */
  const live = useRef(0);

  const isElapsed = tab === "elapsed";
  const shown = isElapsed ? tt + gone : tt;
  const now = normTime(shown);

  /** Move the displayed time by d minutes (in elapsed mode the end time moves, so the time passed changes). */
  const shift = (d: number) => {
    if (!isElapsed) setTt((x) => x + d);
    else setGone((g) => Math.max(0, Math.min(MAX_ELAPSED, g + d)));
  };

  const angleAt = (e: React.PointerEvent) => {
    const svg = svgRef.current;
    if (!svg) return null;
    const ctm = svg.getScreenCTM();
    if (!ctm) return null;
    const pt = new DOMPoint(e.clientX, e.clientY).matrixTransform(ctm.inverse());
    const dx = pt.x - C;
    const dy = pt.y - C;
    return { deg: (Math.atan2(dx, -dy) * 180) / Math.PI, r: Math.hypot(dx, dy) };
  };
  const dragTo = (which: "minute" | "hour", deg: number) => {
    const cur = live.current;
    const d = which === "minute" ? minuteHandDelta(cur, minuteFromAngle(deg)) : hourHandDelta(cur, deg);
    if (d === 0) return;
    if (isElapsed) {
      const g = Math.max(0, Math.min(MAX_ELAPSED, cur + d - tt));
      setGone(g);
      live.current = tt + g;
    } else {
      setTt(cur + d);
      live.current = cur + d;
    }
  };

  const handKeys = (which: "minute" | "hour") => (e: React.KeyboardEvent) => {
    // Minute hand: arrows move 1 minute, PageUp/PageDown move one step. Hour hand: arrows move 1 hour, PageUp/PageDown 3 hours.
    const small = which === "minute" ? 1 : 60;
    const big = which === "minute" ? st : 180;
    const map: Record<string, number> = { ArrowUp: small, ArrowRight: small, ArrowDown: -small, ArrowLeft: -small, PageUp: big, PageDown: -big };
    if (e.key in map) {
      e.preventDefault();
      shift(map[e.key]);
    }
  };

  const p12 = parts12(now);
  const words = timeWords(now);
  const wordVars = Object.fromEntries(Object.entries(words.vars).map(([k, v]) => [k, n(v)]));
  const timeText = `${p12.h}:${p12.mm} ${t(`w.clock2.${p12.period}`)}`;
  const minuteDeg = shown * 6;
  const hourDeg = shown * 0.5;
  const startMinuteDeg = tt * 6;
  const startHourDeg = tt * 0.5;
  const transition = dragging ? "none" : "transform .35s cubic-bezier(.3,1.2,.5,1)";

  // Sector swept by the minute hand in elapsed mode (only the part of the last, unfinished turn).
  const turnsDone = Math.floor(gone / 60);
  const partial = gone % 60;
  const sweep = (() => {
    if (!isElapsed || partial === 0) return null;
    const a0 = ((normTime(tt) % 60) * 6 * Math.PI) / 180;
    const a1 = a0 + (partial * 6 * Math.PI) / 180;
    const r = 88;
    const p = (a: number) => `${C + r * Math.sin(a)} ${C - r * Math.cos(a)}`;
    return `M${C} ${C} L${p(a0)} A${r} ${r} 0 ${partial > 30 ? 1 : 0} 1 ${p(a1)} Z`;
  })();

  const btn = "btn btn-sm btn-ghost font-mono";
  const minLabel = (v: number) => t("w.clock2.minShort", { v: n(v) });
  const hourLabel = (v: number) => t("w.clock2.hourShort", { v: n(v) });
  const dur = splitDuration(gone);

  return (
    <WidgetFrame title={title ?? t("w.clock2.title")} subtitle={subtitle ?? t("w.clock2.subtitle")}>
      <div className="flex flex-wrap gap-2">
        {(["read", "elapsed"] as const).map((m) => (
          <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
            {t(`w.clock2.mode.${m}`)}
          </button>
        ))}
      </div>

      <div className="mt-4 grid items-start gap-6 md:grid-cols-[auto_1fr]">
        <div dir="ltr" className="mx-auto w-full max-w-[17rem]">
          <svg
            ref={svgRef}
            viewBox="0 0 260 260"
            className="w-full touch-none select-none"
            role="group"
            aria-label={t("w.clock2.aria", { time: timeText })}
            onPointerDown={(e) => {
              const a = angleAt(e);
              if (!a || a.r > R + 10) return;
              const which = ((e.target as Element).closest("[data-hand]")?.getAttribute("data-hand") as "minute" | "hour" | null) ?? "minute";
              e.currentTarget.setPointerCapture(e.pointerId);
              live.current = shown;
              setDragging(which);
              dragTo(which, a.deg);
            }}
            onPointerMove={(e) => {
              if (!dragging) return;
              const a = angleAt(e);
              if (a) dragTo(dragging, a.deg);
            }}
            onPointerUp={() => setDragging(null)}
            onPointerCancel={() => setDragging(null)}
          >
            <circle cx={C} cy={C} r={R + 22} fill="var(--paper-2)" />
            <circle cx={C} cy={C} r={R} fill="var(--card)" stroke="var(--ink-2)" strokeWidth="3" />
            {sweep && <path d={sweep} fill="var(--gold-soft)" stroke="var(--gold)" strokeWidth="1.5" />}
            {Array.from({ length: 60 }, (_, i) => {
              const a = (i * 6 * Math.PI) / 180;
              const five = i % 5 === 0;
              const r1 = R - (five ? 11 : 6);
              return <line key={i} x1={C + r1 * Math.sin(a)} y1={C - r1 * Math.cos(a)} x2={C + (R - 2) * Math.sin(a)} y2={C - (R - 2) * Math.cos(a)} stroke={five ? "var(--ink)" : "var(--muted)"} strokeWidth={five ? 2.2 : 1} />;
            })}
            {Array.from({ length: 12 }, (_, i) => {
              const h = i + 1;
              const a = (h * 30 * Math.PI) / 180;
              return (
                <text key={h} x={C + 78 * Math.sin(a)} y={C - 78 * Math.cos(a) + 7} textAnchor="middle" fontSize="19" fontWeight="700" fill="var(--sky-ink)">
                  {h}
                </text>
              );
            })}
            {edgeMinutes &&
              Array.from({ length: 12 }, (_, i) => {
                const a = (i * 30 * Math.PI) / 180;
                return (
                  <text key={`m${i}`} x={C + (R + 12) * Math.sin(a)} y={C - (R + 12) * Math.cos(a) + 4} textAnchor="middle" fontSize="10.5" fontWeight="600" fill="var(--human)">
                    {i * 5}
                  </text>
                );
              })}
            {isElapsed && (
              <g opacity="0.45">
                <line x1={C} y1={C} x2={C} y2={C - 52} stroke="var(--sky)" strokeWidth="7" strokeLinecap="round" strokeDasharray="2 5" style={{ transform: `rotate(${startHourDeg}deg)`, transformOrigin: `${C}px ${C}px` }} />
                <line x1={C} y1={C} x2={C} y2={C - 86} stroke="var(--human)" strokeWidth="4" strokeLinecap="round" strokeDasharray="2 5" style={{ transform: `rotate(${startMinuteDeg}deg)`, transformOrigin: `${C}px ${C}px` }} />
              </g>
            )}
            <g
              data-hand="hour"
              role="slider"
              tabIndex={0}
              aria-label={t("w.clock2.hourHand")}
              aria-valuemin={0}
              aria-valuemax={1439}
              aria-valuenow={now}
              aria-valuetext={timeText}
              onKeyDown={handKeys("hour")}
              className="cursor-grab outline-none [&:focus-visible>line:last-child]:stroke-[var(--gold)]"
              style={{ transform: `rotate(${hourDeg}deg)`, transformOrigin: `${C}px ${C}px`, transition }}
            >
              <line x1={C} y1={C + 12} x2={C} y2={C - 56} stroke="transparent" strokeWidth="22" />
              <line x1={C} y1={C + 12} x2={C} y2={C - 52} stroke="var(--sky)" strokeWidth="8" strokeLinecap="round" />
            </g>
            <g
              data-hand="minute"
              role="slider"
              tabIndex={0}
              aria-label={t("w.clock2.minuteHand")}
              aria-valuemin={0}
              aria-valuemax={59}
              aria-valuenow={now % 60}
              aria-valuetext={timeText}
              onKeyDown={handKeys("minute")}
              className="cursor-grab outline-none [&:focus-visible>line:last-child]:stroke-[var(--gold)]"
              style={{ transform: `rotate(${minuteDeg}deg)`, transformOrigin: `${C}px ${C}px`, transition }}
            >
              <line x1={C} y1={C + 16} x2={C} y2={C - 92} stroke="transparent" strokeWidth="20" />
              <line x1={C} y1={C + 16} x2={C} y2={C - 88} stroke="var(--human)" strokeWidth="4.5" strokeLinecap="round" />
            </g>
            <circle cx={C} cy={C} r="6" fill="var(--ink)" />
          </svg>
          <p className="mt-1 text-center text-xs text-muted" dir="auto">
            <span className="font-semibold text-sky-ink">{t("w.clock2.hourHand")}</span> · <span className="font-semibold text-human">{t("w.clock2.minuteHand")}</span>
          </p>
        </div>

        <div className="space-y-4">
          {!isElapsed ? (
            <div className="flex flex-wrap gap-2" dir="ltr">
              <button type="button" className={btn} onClick={() => shift(-60)}>
                −{hourLabel(1)}
              </button>
              <button type="button" className={btn} onClick={() => shift(-st)}>
                −{minLabel(st)}
              </button>
              <button type="button" className={btn} onClick={() => shift(st)}>
                +{minLabel(st)}
              </button>
              <button type="button" className={btn} onClick={() => shift(60)}>
                +{hourLabel(1)}
              </button>
            </div>
          ) : (
            <div className="grid gap-3 sm:grid-cols-2">
              <div>
                <p className="text-sm font-semibold text-ink-2">{t("w.clock2.elapsed.start")}</p>
                <div className="mt-1.5 flex flex-wrap gap-1.5" dir="ltr">
                  <button type="button" className={btn} onClick={() => setTt((x) => x - st)}>
                    −{minLabel(st)}
                  </button>
                  <button type="button" className={btn} onClick={() => setTt((x) => x + st)}>
                    +{minLabel(st)}
                  </button>
                  <button type="button" className={btn} onClick={() => setTt((x) => x + 60)}>
                    +{hourLabel(1)}
                  </button>
                </div>
              </div>
              <div>
                <p className="text-sm font-semibold text-ink-2">{t("w.clock2.elapsed.passed")}</p>
                <div className="mt-1.5 flex flex-wrap gap-1.5" dir="ltr">
                  <button type="button" className={btn} disabled={gone === 0} onClick={() => shift(-st)}>
                    −{minLabel(st)}
                  </button>
                  <button type="button" className={btn} disabled={gone >= MAX_ELAPSED} onClick={() => shift(st)}>
                    +{minLabel(st)}
                  </button>
                  <button type="button" className={btn} disabled={gone >= MAX_ELAPSED} onClick={() => shift(60)}>
                    +{hourLabel(1)}
                  </button>
                </div>
              </div>
            </div>
          )}

          <div aria-live="polite" className="space-y-3">
            {isElapsed && <ElapsedSummary start={tt} gone={gone} turnsDone={turnsDone} dur={dur} />}
            {showDigital ? (
              <div className="grid gap-2 sm:grid-cols-2">
                <div className="rounded-xl bg-paper-2 px-4 py-2.5">
                  <p className="text-xs font-semibold text-muted">{t("w.clock2.h12")}</p>
                  <p className="font-mono text-2xl font-bold text-ink" dir="ltr">
                    {p12.h}:{p12.mm} <span className="text-base font-semibold text-ink-2">{t(`w.clock2.${p12.period}`)}</span>
                  </p>
                </div>
                <div className="rounded-xl bg-paper-2 px-4 py-2.5">
                  <p className="text-xs font-semibold text-muted">{t("w.clock2.h24")}</p>
                  <p className="font-mono text-2xl font-bold text-ink" dir="ltr">
                    {format24(now)}
                  </p>
                </div>
                <p className="text-sm text-ink-2 sm:col-span-2">
                  <span className="font-semibold text-ink">{t(`w.clock2.words.${words.key}`, wordVars)}</span> · {t(p12.period === "am" ? "w.clock2.amNote" : "w.clock2.pmNote")}
                </p>
              </div>
            ) : (
              <p className="rounded-xl bg-paper-2 px-4 py-3 text-sm text-ink-2">{t("w.clock2.hidden")}</p>
            )}
          </div>

          <div className="flex flex-wrap gap-2">
            <button type="button" aria-pressed={showDigital} className={`btn btn-sm ${showDigital ? "btn-gold" : "btn-ghost"}`} onClick={() => setShowDigital((v) => !v)}>
              {t("w.clock2.showDigital")}
            </button>
            <button type="button" aria-pressed={edgeMinutes} className={`btn btn-sm ${edgeMinutes ? "btn-gold" : "btn-ghost"}`} onClick={() => setEdgeMinutes((v) => !v)}>
              {t("w.clock2.edgeMinutes")}
            </button>
          </div>
          <p className="text-xs text-muted">{t("w.clock2.dragHint")}</p>
        </div>
      </div>
    </WidgetFrame>
  );
}

function ElapsedSummary({ start, gone, turnsDone, dur }: { start: number; gone: number; turnsDone: number; dur: { h: number; m: number } }) {
  const { t, n } = useI18n();
  const jumps = elapsedJumps(start, gone);
  const s12 = (x: number) => {
    const p = parts12(x);
    return `${p.h}:${p.mm} ${t(`w.clock2.${p.period}`)}`;
  };
  const end = normTime(start + gone);
  const hm = (x: number) => {
    const p = parts12(x);
    return `${p.h}:${p.mm}`;
  };
  return (
    <div className="rounded-xl border border-line p-3">
      <div className="flex flex-wrap items-baseline justify-between gap-2 text-sm">
        <span>
          <span className="text-muted">{t("w.clock2.elapsed.start")}: </span>
          <strong className="font-mono text-ink" dir="ltr">
            {s12(start)}
          </strong>
        </span>
        <span>
          <span className="text-muted">{t("w.clock2.elapsed.end")}: </span>
          <strong className="font-mono text-ink" dir="ltr">
            {s12(end)}
          </strong>
        </span>
      </div>
      {jumps.length > 0 && (
        <ol className="mt-3 flex flex-wrap items-center gap-x-1.5 gap-y-2 font-mono text-sm" dir="ltr" aria-hidden="true">
          <li className="rounded-md bg-paper-2 px-2 py-0.5 font-bold text-ink">{hm(start)}</li>
          {jumps.map((j, i) => (
            <li key={i} className="flex items-center gap-1.5">
              <span className="flex items-center gap-1 text-xs font-bold text-gold-ink">
                <span aria-hidden="true">→</span>+{j.minutes >= 60 && j.minutes % 60 === 0 ? t("w.clock2.hourShort", { v: n(j.minutes / 60) }) : t("w.clock2.minShort", { v: n(j.minutes) })}
                <span aria-hidden="true">→</span>
              </span>
              <span className={`rounded-md px-2 py-0.5 font-bold ${i === jumps.length - 1 ? "bg-gold-soft text-ink" : "bg-paper-2 text-ink"}`}>{hm(j.to)}</span>
            </li>
          ))}
        </ol>
      )}
      <p className="mt-2 text-sm text-ink-2">
        {t("w.clock2.elapsed.passed")}: <strong className="text-ink">{t("w.clock2.elapsed.duration", { h: n(dur.h), m: n(dur.m) })}</strong> = {t("w.clock2.minShort", { v: n(gone) })}
      </p>
      {jumps.length > 1 && <p className="mt-1 text-xs text-muted">{t("w.clock2.elapsed.countOn")}</p>}
      {turnsDone > 0 && <p className="mt-1 text-xs text-muted">{t("w.clock2.elapsed.turns", { k: n(turnsDone) })}</p>}
    </div>
  );
}
