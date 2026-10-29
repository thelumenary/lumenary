"use client";

import { Minus, Plus, RotateCcw, Undo2 } from "lucide-react";
import { useId, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { range } from "./lib/number-common";
import { applyMove, equationText, isolatedValue, moveText, readSide, sideText, solve, stuckFraction, type Move, type Rejection, type Side } from "./lib/number-balance";

interface BalanceScaleProps {
  /** Left pan: number of x-boxes and unit weights, e.g. { x: 2, units: 3 }. */
  left?: { x: number; units: number };
  /** Right pan, e.g. { x: 0, units: 11 }. */
  right?: { x: number; units: number };
  /** Allow negative amounts, drawn as balloons that pull upwards. */
  allowNegative?: boolean;
  title?: string;
  subtitle?: string;
}

interface Entry {
  left: Side;
  right: Side;
  move?: Move;
}

const W = 640;
const PIVOT_X = 320;
const ARM = 190;
const MIN_HANG = 170;
const PAN_HALF = 105;

/** Linear equations as a balance: do the same thing to both sides until x is alone. */
export function BalanceScale({ left, right, allowNegative, title, subtitle }: BalanceScaleProps) {
  const { t, n } = useI18n();
  const selectId = useId();
  const L0 = readSide(left, { x: 2, units: 3 });
  const R0 = readSide(right, { x: 0, units: 11 });
  const [start, setStart] = useState<Entry>({ left: L0, right: R0 });
  // Balloons (negative amounts) are needed when asked for, when the equation has negative amounts,
  // or when its solution is negative — otherwise x could never be isolated.
  const startSol = solve(start.left, start.right);
  const negative = allowNegative === true || [start.left.x, start.left.units, start.right.x, start.right.units].some((v) => v < 0) || (startSol.kind === "unique" && startSol.n < 0);

  const [history, setHistory] = useState<Entry[]>([{ left: L0, right: R0 }]);
  const [k, setK] = useState(2);
  const [reject, setReject] = useState<Rejection | null>(null);
  const cur = history[history.length - 1];
  const sol = solve(cur.left, cur.right);
  const lone = isolatedValue(cur.left, cur.right);
  const stuck = stuckFraction(cur.left, cur.right);

  const play = (move: Move) => {
    const r = applyMove(cur.left, cur.right, move, negative);
    if (!r.ok) return setReject(r.reason);
    setReject(null);
    setHistory((h) => [...h, { left: r.left, right: r.right, move }]);
  };
  const restartWith = (e: Entry) => {
    setStart(e);
    setHistory([e]);
    setReject(null);
  };

  // Tilt only when no value of x can balance the scale.
  const tilt = sol.kind === "none" ? (cur.left.units > cur.right.units ? -6 : 6) : 0;
  const rad = (tilt * Math.PI) / 180;

  // Balloon band height depends on how many balloons there are.
  const balloonRows = (s: Side) => Math.ceil(Math.max(0, -s.x) / 6) * 34 + Math.ceil(Math.max(0, -s.units) / 8) * 26;
  const band = Math.max(balloonRows(cur.left), balloonRows(cur.right));
  const stack = (s: Side) => 6 + Math.ceil(Math.max(0, s.x) / 6) * 30 + Math.ceil(Math.max(0, s.units) / 8) * 22;
  const hang = Math.max(MIN_HANG, Math.max(stack(cur.left), stack(cur.right)) + 24);
  const PIVOT_Y = 40 + band;
  const H = PIVOT_Y + hang + 70;
  const end = (dir: -1 | 1) => ({ x: PIVOT_X + dir * ARM * Math.cos(rad), y: PIVOT_Y + dir * ARM * Math.sin(rad) });

  let status: React.ReactNode;
  if (sol.kind === "none") status = t("w.balance.none");
  else if (sol.kind === "all") status = t("w.balance.all");
  else if (lone !== null) {
    const v = lone;
    status = (
      <>
        <span className="font-semibold">{t("w.balance.solved", { v: n(v) })}</span>{" "}
        {t("w.balance.check")}{" "}
        <span className="font-serif text-lg" dir="ltr">
          {substitute(start.left, v)} = {substitute(start.right, v)} → {signedText(start.left.x * v + start.left.units)} = {signedText(start.right.x * v + start.right.units)} ✓
        </span>
      </>
    );
  } else if (stuck && sol.kind === "unique") status = t("w.balance.stuck", { frac: `${sol.n < 0 ? "−" : ""}${Math.abs(sol.n)}/${sol.d}` });
  else status = t("w.balance.hint");

  // Compress runs of identical unit / x moves for the written record.
  const rows: { label: string; eq: string; kind?: Move["kind"]; count: number }[] = [];
  for (const h of history) {
    const last = rows[rows.length - 1];
    if (h.move && last && last.kind === h.move.kind && h.move.kind !== "divide") {
      last.count += 1;
      last.label = runLabel(h.move, last.count);
      last.eq = equationText(h.left, h.right);
    } else rows.push({ label: h.move ? moveText(h.move) : "", eq: equationText(h.left, h.right), kind: h.move?.kind, count: 1 });
  }

  return (
    <WidgetFrame title={title ?? t("w.balance.title")} subtitle={subtitle ?? t("w.balance.subtitle")}>
      <div dir="ltr" className="overflow-x-auto">
        <svg viewBox={`0 0 ${W} ${H}`} className="mx-auto block w-full max-w-2xl" role="img" aria-label={t("w.balance.aria", { left: sideText(cur.left), right: sideText(cur.right) })}>
          {/* stand */}
          <path d={`M${PIVOT_X - 70} ${H - 12} L${PIVOT_X + 70} ${H - 12}`} stroke="var(--ink-2)" strokeWidth="6" strokeLinecap="round" />
          <path d={`M${PIVOT_X} ${PIVOT_Y} L${PIVOT_X - 30} ${H - 14} L${PIVOT_X + 30} ${H - 14} Z`} fill="var(--line-2)" stroke="var(--ink-2)" strokeWidth="2" strokeLinejoin="round" />
          {/* beam */}
          <g style={{ transform: `rotate(${tilt}deg)`, transformOrigin: `${PIVOT_X}px ${PIVOT_Y}px`, transition: "transform .6s cubic-bezier(.3,1.3,.6,1)" }}>
            <rect x={PIVOT_X - ARM - 8} y={PIVOT_Y - 5} width={2 * ARM + 16} height={10} rx={5} fill="var(--ink-2)" />
          </g>
          <circle cx={PIVOT_X} cy={PIVOT_Y} r="8" fill="var(--gold)" stroke="var(--card)" strokeWidth="2.5" />
          {([-1, 1] as const).map((dir) => {
            const e = end(dir);
            const s = dir === -1 ? cur.left : cur.right;
            return (
              <g key={dir} style={{ transform: `translate(${e.x}px, ${e.y}px)`, transition: "transform .6s cubic-bezier(.3,1.3,.6,1)" }}>
                <Pan side={s} hang={hang} />
              </g>
            );
          })}
        </svg>
      </div>
      <ul className="mt-2 flex list-none flex-wrap justify-center gap-x-4 gap-y-1 ps-0 text-xs text-ink-2 [&>li]:m-0">
        <LegendItem kind="x" label={t("w.balance.legendX")} />
        <LegendItem kind="unit" label={t("w.balance.legendUnit")} />
        {negative && <LegendItem kind="balloon" label={t("w.balance.legendBalloon")} />}
        {negative && <LegendItem kind="xballoon" label={t("w.balance.legendXBalloon")} />}
      </ul>

      <div className="mt-4 grid gap-4 md:grid-cols-[1fr_auto]">
        <div>
          <p className="rounded-xl bg-paper-2 px-4 py-3 text-center font-serif text-3xl text-ink" dir="ltr">
            {equationText(cur.left, cur.right)}
          </p>
          <div className="mt-3 flex flex-wrap gap-2">
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => play({ kind: "addUnit" })}>
              <Plus size={14} aria-hidden="true" /> {t("w.balance.addUnit")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => play({ kind: "subUnit" })}>
              <Minus size={14} aria-hidden="true" /> {t("w.balance.subUnit")}
            </button>
            {negative && (
              <button type="button" className="btn btn-sm btn-ghost" onClick={() => play({ kind: "addX" })}>
                <Plus size={14} aria-hidden="true" /> {t("w.balance.addX")}
              </button>
            )}
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => play({ kind: "subX" })}>
              <Minus size={14} aria-hidden="true" /> {t("w.balance.subX")}
            </button>
            <span className="inline-flex items-center gap-1.5">
              <button type="button" className="btn btn-sm btn-gold" onClick={() => play({ kind: "divide", k })}>
                {t("w.balance.divide", { k: n(k) })}
              </button>
              <select id={selectId} className="input w-auto py-1" value={k} onChange={(e) => setK(Number(e.target.value))} aria-label={t("w.balance.divisor")}>
                {range(2, 9).map((v) => (
                  <option key={v} value={v}>
                    {v}
                  </option>
                ))}
              </select>
            </span>
          </div>
          <div className="mt-3 space-y-2" aria-live="polite">
            {reject && <p className="rounded-lg bg-warn-soft px-3 py-2 text-sm text-ink">{t(`w.balance.reject.${reject}`, { k: n(k) })}</p>}
            <p className="text-[0.95rem] text-ink">{status}</p>
            {sol.kind === "unique" && lone === null && <p className="text-sm text-muted">{t("w.balance.level")}</p>}
          </div>
          <div className="mt-3 flex flex-wrap gap-2">
            <button type="button" className="btn btn-sm btn-ghost" disabled={history.length < 2} onClick={() => (setHistory((h) => h.slice(0, -1)), setReject(null))}>
              <Undo2 size={14} aria-hidden="true" /> {t("w.balance.undo")}
            </button>
            <button type="button" className="btn btn-sm btn-ghost" disabled={history.length < 2} onClick={() => restartWith(start)}>
              <RotateCcw size={14} aria-hidden="true" /> {t("w.balance.reset")}
            </button>
          </div>
        </div>
        <div className="min-w-[13rem] rounded-xl border border-line bg-card px-4 py-3">
          <p className="text-xs font-semibold text-muted">{t("w.balance.record")}</p>
          <ol className="mt-1 list-none space-y-0.5 ps-0 font-serif text-lg text-ink" dir="ltr">
            {rows.map((r, i) => (
              <li key={i} className="flex items-baseline gap-3">
                <span className="w-12 shrink-0 text-end font-mono text-xs text-muted">{r.label}</span>
                <span className={i === rows.length - 1 ? "font-semibold" : "text-ink-2"}>{r.eq}</span>
              </li>
            ))}
          </ol>
        </div>
      </div>

      <details className="mt-4 rounded-xl border border-line px-4 py-2">
        <summary className="cursor-pointer text-sm font-semibold text-ink-2">{t("w.balance.build")}</summary>
        <div className="mt-3 grid gap-3 pb-2 sm:grid-cols-2">
          {(["left", "right"] as const).map((side) => (
            <div key={side} className="space-y-2">
              <p className="text-sm font-semibold text-ink">{t(`w.balance.${side}`)}</p>
              {(["x", "units"] as const).map((part) => (
                <Stepper
                  key={part}
                  label={t(part === "x" ? "w.balance.xCount" : "w.balance.unitCount")}
                  value={start[side][part]}
                  min={negative ? -12 : 0}
                  max={12}
                  onChange={(v) => restartWith({ ...start, [side]: { ...start[side], [part]: v } })}
                />
              ))}
            </div>
          ))}
        </div>
      </details>
    </WidgetFrame>
  );
}

function runLabel(m: Move, count: number): string {
  switch (m.kind) {
    case "addUnit":
      return `+ ${count}`;
    case "subUnit":
      return `− ${count}`;
    case "addX":
      return `+ ${count}x`;
    case "subX":
      return `− ${count}x`;
    default:
      return moveText(m);
  }
}

const signedText = (v: number) => (v < 0 ? `−${-v}` : `${v}`);

/** "2 × 4 + 3" — a side with x replaced by v. */
function substitute(s: Side, v: number): string {
  const val = v < 0 ? `(−${-v})` : `${v}`;
  const parts: string[] = [];
  if (s.x !== 0) parts.push(s.x === 1 ? val : s.x === -1 ? `−${val}` : `${s.x < 0 ? "−" : ""}${Math.abs(s.x)} × ${val}`);
  if (s.units !== 0) parts.push(parts.length === 0 ? (s.units < 0 ? `−${-s.units}` : `${s.units}`) : s.units < 0 ? `− ${-s.units}` : `+ ${s.units}`);
  return parts.length ? parts.join(" ") : "0";
}

/* ------------------------------------------------------------------ drawing */

function XBox({ x, y }: { x: number; y: number }) {
  return (
    <g transform={`translate(${x} ${y})`}>
      <g className="animate-float-up">
        <rect width={26} height={26} rx={5} fill="var(--formal-soft)" stroke="var(--formal)" strokeWidth={2} />
        <text x={13} y={18.5} textAnchor="middle" fontSize={16} fontStyle="italic" fontWeight={700} fontFamily="var(--font-serif)" fill="var(--formal)">
          x
        </text>
      </g>
    </g>
  );
}

function Unit({ x, y }: { x: number; y: number }) {
  return (
    <g transform={`translate(${x} ${y})`}>
      <g className="animate-float-up">
        <rect width={18} height={18} rx={3} fill="var(--gold-soft)" stroke="var(--gold-ink)" strokeWidth={1.6} />
        <text x={9} y={13.5} textAnchor="middle" fontSize={11} fontWeight={700} fill="var(--gold-ink)">
          1
        </text>
      </g>
    </g>
  );
}

function Balloon({ x, y, big }: { x: number; y: number; big?: boolean }) {
  const r = big ? 14 : 10;
  return (
    <g transform={`translate(${x} ${y})`}>
      <g className="animate-float-up">
      <ellipse cx={0} cy={0} rx={r} ry={r * 1.15} fill={big ? "var(--formal-soft)" : "var(--human-soft)"} stroke={big ? "var(--formal)" : "var(--human)"} strokeWidth={1.6} strokeDasharray={big ? undefined : "3 2"} />
      <text x={0} y={big ? 5 : 4} textAnchor="middle" fontSize={big ? 12 : 10} fontWeight={700} fill={big ? "var(--formal)" : "var(--human)"} fontStyle={big ? "italic" : undefined}>
        {big ? "−x" : "−1"}
      </text>
      </g>
    </g>
  );
}

/** A pan hanging from a beam end at (0, 0): strings, bowl, weights on it, balloons above. */
function Pan({ side, hang }: { side: Side; hang: number }) {
  const panY = hang;
  const xs = Math.max(0, side.x);
  const us = Math.max(0, side.units);
  const items: React.ReactNode[] = [];
  // x-boxes: rows of 6 from the pan upwards.
  let y = panY - 6;
  for (let i = 0; i < xs; i++) {
    const row = Math.floor(i / 6);
    const inRow = Math.min(6, xs - row * 6);
    const col = i % 6;
    items.push(<XBox key={`x${i}`} x={-(inRow * 30) / 2 + col * 30 + 2} y={y - (row + 1) * 30 + 2} />);
  }
  y -= Math.ceil(xs / 6) * 30;
  for (let i = 0; i < us; i++) {
    const row = Math.floor(i / 8);
    const inRow = Math.min(8, us - row * 8);
    const col = i % 8;
    items.push(<Unit key={`u${i}`} x={-(inRow * 22) / 2 + col * 22 + 2} y={y - (row + 1) * 22 + 2} />);
  }
  // balloons above the beam end
  const bx = Math.max(0, -side.x);
  const bu = Math.max(0, -side.units);
  const balloons: React.ReactNode[] = [];
  let by = -24;
  for (let i = 0; i < bx; i++) {
    const row = Math.floor(i / 6);
    const inRow = Math.min(6, bx - row * 6);
    balloons.push(<Balloon key={`bx${i}`} big x={-(inRow * 32) / 2 + (i % 6) * 32 + 16} y={by - row * 34} />);
  }
  by -= Math.ceil(bx / 6) * 34;
  for (let i = 0; i < bu; i++) {
    const row = Math.floor(i / 8);
    const inRow = Math.min(8, bu - row * 8);
    balloons.push(<Balloon key={`bu${i}`} x={-(inRow * 24) / 2 + (i % 8) * 24 + 12} y={by - row * 26} />);
  }
  return (
    <g>
      {balloons.length > 0 && <line x1={0} y1={0} x2={0} y2={-12} stroke="var(--muted)" strokeWidth={1.2} />}
      {balloons}
      <line x1={0} y1={0} x2={-PAN_HALF} y2={panY} stroke="var(--muted)" strokeWidth={1.4} />
      <line x1={0} y1={0} x2={PAN_HALF} y2={panY} stroke="var(--muted)" strokeWidth={1.4} />
      <circle cx={0} cy={0} r={4} fill="var(--ink-2)" />
      {items}
      <path d={`M${-PAN_HALF - 8} ${panY} Q0 ${panY + 34} ${PAN_HALF + 8} ${panY} Z`} fill="var(--paper-2)" stroke="var(--ink-2)" strokeWidth={2.5} strokeLinejoin="round" />
    </g>
  );
}

function LegendItem({ kind, label }: { kind: "x" | "unit" | "balloon" | "xballoon"; label: string }) {
  return (
    <li className="flex items-center gap-1.5">
      <svg viewBox="-16 -18 32 36" className="h-5 w-5" aria-hidden="true">
        {kind === "x" && <XBox x={-13} y={-13} />}
        {kind === "unit" && <Unit x={-9} y={-9} />}
        {kind === "balloon" && <Balloon x={0} y={0} />}
        {kind === "xballoon" && <Balloon x={0} y={0} big />}
      </svg>
      {label}
    </li>
  );
}

function Stepper({ label, value, min, max, onChange }: { label: string; value: number; min: number; max: number; onChange: (v: number) => void }) {
  const { t } = useI18n();
  return (
    <div role="group" aria-label={label} className="flex items-center justify-between gap-2 rounded-lg bg-paper-2 px-3 py-1.5">
      <span className="text-sm text-ink-2">{label}</span>
      <span className="flex items-center gap-1.5">
        <button type="button" className="btn btn-ghost h-8 w-8 !p-0" aria-label={t("w.balance.less", { label })} disabled={value <= min} onClick={() => onChange(value - 1)}>
          <Minus size={14} aria-hidden="true" />
        </button>
        <span className="w-8 text-center font-mono text-ink" dir="ltr">
          {value < 0 ? `−${-value}` : value}
        </span>
        <button type="button" className="btn btn-ghost h-8 w-8 !p-0" aria-label={t("w.balance.more", { label })} disabled={value >= max} onClick={() => onChange(value + 1)}>
          <Plus size={14} aria-hidden="true" />
        </button>
      </span>
    </div>
  );
}
