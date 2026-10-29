"use client";

import { ChevronLeft, ChevronRight, Minus, Plus, RotateCcw } from "lucide-react";
import { useEffect, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { clampInt, oneOf, prefersReducedMotion, range } from "./lib/number-common";
import {
  COLUMN_W,
  additionSteps,
  bundle,
  columnsFor,
  digitsOf,
  isCanonical,
  layoutColumn,
  liveCount,
  nudge,
  subtractionSteps,
  totalOf,
  unbundle,
  type ColumnView,
  type Tone,
  type WrittenView,
} from "./lib/number-place";

interface PlaceValueProps {
  mode?: "build" | "add" | "subtract";
  /** Starting number in "build" mode. */
  start?: number;
  /** First number in "add" / "subtract" mode. */
  a?: number;
  /** Second number in "add" / "subtract" mode. */
  b?: number;
  /** Largest number allowed (≤ 9999). In "build" mode it also decides which columns appear. */
  max?: number;
  title?: string;
  subtitle?: string;
}

const TONE: Record<Tone, { fill: string; stroke: string; dash?: string; opacity?: number }> = {
  plain: { fill: "var(--compute-soft)", stroke: "var(--compute)" },
  a: { fill: "var(--human-soft)", stroke: "var(--human)" },
  b: { fill: "var(--formal-soft)", stroke: "var(--formal)" },
  carry: { fill: "var(--gold-soft)", stroke: "var(--gold)" },
  fresh: { fill: "var(--gold-soft)", stroke: "var(--gold)" },
  traded: { fill: "none", stroke: "var(--muted)", dash: "2.5 2", opacity: 0.75 },
  taken: { fill: "none", stroke: "var(--bad)", dash: "2.5 2", opacity: 0.8 },
};

const MIN_W: Record<number, string> = { 1: "min-w-[8rem]", 2: "min-w-[14rem]", 3: "min-w-[18rem]", 4: "min-w-[26rem]" };

/** Base-ten blocks: build numbers and regroup, or walk through written addition / subtraction. */
export function PlaceValue({ mode, start, a, b, max, title, subtitle }: PlaceValueProps) {
  const { t } = useI18n();
  const m = oneOf(mode, ["build", "add", "subtract"] as const, "build");
  const cap = clampInt(max, 9, 9999, m === "build" ? 999 : 9999);
  if (m === "build") return <BuildMode start={clampInt(start, 0, cap, 0)} max={cap} title={title ?? t("w.placeValue.title")} subtitle={subtitle ?? t("w.placeValue.subtitleBuild")} />;
  return (
    <Walkthrough
      op={m}
      a0={clampInt(a, 0, cap, m === "add" ? 47 : 52)}
      b0={clampInt(b, 0, cap, m === "add" ? 38 : 27)}
      max={cap}
      title={title ?? t(m === "add" ? "w.placeValue.titleAdd" : "w.placeValue.titleSubtract")}
      subtitle={subtitle ?? t(m === "add" ? "w.placeValue.subtitleAdd" : "w.placeValue.subtitleSubtract")}
    />
  );
}

/* ------------------------------------------------------------------ drawing */

function BlockShape({ kind, tone }: { kind: number; tone: Tone }) {
  const s = TONE[tone];
  const common = { fill: s.fill, stroke: s.stroke, strokeWidth: 1.2, strokeDasharray: s.dash, opacity: s.opacity };
  const fine = { stroke: s.stroke, strokeWidth: 0.55, opacity: s.dash ? 0.45 : 0.55 };
  let w = 8;
  let h = 8;
  let shape: React.ReactNode;
  if (kind === 0) shape = <rect width={8} height={8} rx={1.5} {...common} />;
  else if (kind === 1) {
    h = 80;
    shape = (
      <g>
        <rect width={8} height={80} rx={1.5} {...common} />
        {range(1, 9).map((k) => (
          <line key={k} x1={0} x2={8} y1={k * 8} y2={k * 8} {...fine} />
        ))}
      </g>
    );
  } else if (kind === 2) {
    w = h = 80;
    shape = (
      <g>
        <rect width={80} height={80} rx={2} {...common} />
        {range(1, 9).map((k) => (
          <g key={k}>
            <line x1={k * 8} x2={k * 8} y1={0} y2={80} {...fine} />
            <line x1={0} x2={80} y1={k * 8} y2={k * 8} {...fine} />
          </g>
        ))}
      </g>
    );
  } else {
    w = h = 80;
    shape = (
      <g>
        <polygon points="0,16 16,0 80,0 64,16" {...common} fill={s.fill === "none" ? "none" : `color-mix(in oklab, ${s.fill} 70%, var(--card))`} />
        <polygon points="64,16 80,0 80,64 64,80" {...common} fill={s.fill === "none" ? "none" : `color-mix(in oklab, ${s.stroke} 22%, ${s.fill})`} />
        <rect x={0} y={16} width={64} height={64} {...common} />
        {range(1, 9).map((k) => (
          <g key={k}>
            <line x1={k * 6.4} x2={k * 6.4} y1={16} y2={80} {...fine} />
            <line x1={0} x2={64} y1={16 + k * 6.4} y2={16 + k * 6.4} {...fine} />
          </g>
        ))}
      </g>
    );
  }
  return (
    <>
      {shape}
      {tone === "taken" && <line x1={0} y1={h} x2={w} y2={0} stroke="var(--bad)" strokeWidth={1.4} />}
    </>
  );
}

/** One column of blocks. `leaving` blocks (indices) slide out; `entering` blocks fade in. */
function ColumnBlocks({ kind, view, label, leaving = [], leaveDir = -1, plusSeparators = false }: { kind: number; view: ColumnView; label: string; leaving?: number[]; leaveDir?: number; plusSeparators?: boolean }) {
  const { pos, height, separators } = layoutColumn(kind, view);
  const H = Math.max(height, 24) + 8;
  return (
    <svg viewBox={`-2 -4 ${COLUMN_W + 4} ${H}`} className="mx-auto block w-full max-w-[11rem]" role="img" aria-label={label}>
      {separators.map((y, k) =>
        plusSeparators ? (
          <text key={k} x={COLUMN_W / 2} y={y + 5} textAnchor="middle" fontSize="14" fontWeight="700" fill="var(--muted)">
            +
          </text>
        ) : (
          <line key={k} x1={20} x2={COLUMN_W - 20} y1={y} y2={y} stroke="var(--line-2)" strokeDasharray="3 3" />
        ),
      )}
      {view.items.map((tone, i) => {
        const p = pos[i];
        const out = leaving.includes(i);
        return (
          <g key={i} transform={`translate(${p.x} ${p.y})`}>
            <g
              className={tone === "carry" || tone === "fresh" ? "animate-float-up" : undefined}
              style={{ transition: "transform .45s ease-in, opacity .45s ease-in", transform: out ? `translate(${leaveDir * 34}px, 0px) scale(.6)` : undefined, opacity: out ? 0 : 1 }}
            >
              <BlockShape kind={kind} tone={tone} />
            </g>
          </g>
        );
      })}
    </svg>
  );
}

function ColumnCard({ active, children, name, count }: { active?: boolean; children: React.ReactNode; name: string; count: number }) {
  const { n } = useI18n();
  return (
    <div className={`flex flex-col rounded-xl border-2 bg-card px-1.5 pb-2 pt-1.5 transition-colors ${active ? "border-gold bg-gold-soft/40" : "border-line"}`}>
      <p className="text-center text-xs font-bold uppercase tracking-wide text-ink-2">{name}</p>
      <p className="text-center font-serif text-2xl leading-tight text-ink">{n(count)}</p>
      <div className="mt-1 flex flex-1 flex-col justify-start">{children}</div>
    </div>
  );
}

/* ------------------------------------------------------------------ build mode */

function BuildMode({ start, max, title, subtitle }: { start: number; max: number; title: string; subtitle: string }) {
  const { t, n } = useI18n();
  const cols = Math.max(2, Math.min(4, columnsFor(max)));
  const [counts, setCounts] = useState<number[]>(() => digitsOf(start, cols));
  const [pending, setPending] = useState<{ kind: "bundle" | "unbundle"; col: number } | null>(null);
  const [fresh, setFresh] = useState<{ col: number; count: number } | null>(null);
  const timer = useRef<ReturnType<typeof setTimeout> | null>(null);
  useEffect(() => () => {
    if (timer.current) clearTimeout(timer.current);
  }, []);

  const total = totalOf(counts);
  const canonical = isCanonical(counts);

  const act = (next: number[] | null, freshNext: { col: number; count: number } | null = null) => {
    if (!next) return;
    setCounts(next);
    setFresh(freshNext);
  };
  const regroup = (kind: "bundle" | "unbundle", col: number) => {
    const next = kind === "bundle" ? bundle(counts, col) : unbundle(counts, col);
    if (!next || pending) return;
    const target = kind === "bundle" ? { col: col + 1, count: 1 } : { col: col - 1, count: 10 };
    if (prefersReducedMotion()) return act(next, target);
    setPending({ kind, col });
    timer.current = setTimeout(() => {
      setPending(null);
      act(next, target);
    }, 460);
  };

  const viewOf = (i: number): ColumnView => {
    const c = counts[i];
    const f = fresh && fresh.col === i ? Math.min(fresh.count, c) : 0;
    return { items: [...Array<Tone>(c - f).fill("plain"), ...Array<Tone>(f).fill("fresh")], breaks: [] };
  };
  const leavingOf = (i: number): number[] => {
    if (!pending || pending.col !== i) return [];
    const c = counts[i];
    return pending.kind === "bundle" ? range(c - 10, c - 1) : [c - 1];
  };

  const expanded = counts
    .map((c, i) => ({ c, i }))
    .filter(({ c }) => c > 0)
    .reverse();
  const tooMany = counts.findIndex((c) => c > 9);

  return (
    <WidgetFrame title={title} subtitle={subtitle}>
      <div className="overflow-x-auto pb-1">
        <div dir="ltr" className={`grid gap-2 ${MIN_W[cols]}`} style={{ gridTemplateColumns: `repeat(${cols}, minmax(0, 1fr))` }}>
          {range(0, cols - 1)
            .reverse()
            .map((i) => (
              <ColumnCard key={i} name={t(`w.placeValue.colName.${i}`)} count={counts[i]}>
                <ColumnBlocks kind={i} view={viewOf(i)} label={t("w.placeValue.columnAria", { place: t(`w.placeValue.colName.${i}`), count: n(counts[i]) })} leaving={leavingOf(i)} leaveDir={pending?.kind === "bundle" ? -1 : 1} />
                <div className="mt-auto flex justify-center gap-1.5 pt-2">
                  <button type="button" className="btn btn-ghost h-9 w-9 !p-0" aria-label={t(`w.placeValue.remove.${i}`)} disabled={!!pending || !nudge(counts, i, -1, max)} onClick={() => act(nudge(counts, i, -1, max))}>
                    <Minus size={16} aria-hidden="true" />
                  </button>
                  <button type="button" className="btn btn-ghost h-9 w-9 !p-0" aria-label={t(`w.placeValue.add.${i}`)} disabled={!!pending || !nudge(counts, i, 1, max)} onClick={() => act(nudge(counts, i, 1, max))}>
                    <Plus size={16} aria-hidden="true" />
                  </button>
                </div>
              </ColumnCard>
            ))}
        </div>
      </div>

      <div className="mt-3 flex flex-wrap gap-2">
        {range(0, cols - 2)
          .reverse()
          .map((i) => (
            <span key={i} className="flex flex-wrap gap-1.5">
              <button type="button" className="btn btn-sm btn-ghost" disabled={!!pending || !bundle(counts, i)} onClick={() => regroup("bundle", i)}>
                {t(`w.placeValue.trade.${i}`)}
              </button>
              <button type="button" className="btn btn-sm btn-ghost" disabled={!!pending || !unbundle(counts, i + 1)} onClick={() => regroup("unbundle", i + 1)}>
                {t(`w.placeValue.break.${i + 1}`)}
              </button>
            </span>
          ))}
        <button type="button" className="btn btn-sm btn-ghost ms-auto" disabled={!!pending} onClick={() => act(digitsOf(start, cols))}>
          <RotateCcw size={14} aria-hidden="true" /> {t("w.placeValue.reset")}
        </button>
      </div>

      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <div className="flex flex-wrap items-baseline gap-x-4 gap-y-1" dir="ltr">
          <span className="font-serif text-4xl text-ink">{total}</span>
          <span className="font-serif text-xl text-ink-2">
            ={" "}
            {expanded.length === 0
              ? "0"
              : canonical
                ? expanded.map(({ c, i }) => c * 10 ** i).join(" + ")
                : expanded.map(({ c, i }) => `${c} × ${10 ** i}`).join(" + ")}
          </span>
        </div>
        <p className="mt-2 text-[0.95rem] text-ink">
          {tooMany >= 0
            ? t("w.placeValue.tooMany", { count: n(counts[tooMany]), place: t(`w.placeValue.placeName.${tooMany}`) })
            : total === 0
              ? t("w.placeValue.empty")
              : t("w.placeValue.expandedNote")}
        </p>
      </div>
    </WidgetFrame>
  );
}

/* ------------------------------------------------------------------ add / subtract walkthrough */

function Walkthrough({ op, a0, b0, max, title, subtitle }: { op: "add" | "subtract"; a0: number; b0: number; max: number; title: string; subtitle: string }) {
  const { t, n } = useI18n();
  const fitB = (a: number, b: number) => (op === "add" ? Math.min(b, max - a) : b);
  const [a, setA] = useState(a0);
  const [b, setB] = useState(fitB(a0, b0));
  const [step, setStep] = useState(0);
  const walk = useMemo(() => (op === "add" ? additionSteps(a, b) : subtractionSteps(a, b)), [op, a, b]);
  const s = walk.steps[Math.min(step, walk.steps.length - 1)];
  const last = walk.steps.length - 1;
  const place = (i: number) => t(`w.placeValue.placeName.${i}`);
  const sym = op === "add" ? "+" : "−";

  let text = "";
  let expr = "";
  switch (s.kind) {
    case "start":
      text = op === "add" ? t("w.placeValue.walk.startAdd", { a: n(walk.a), b: n(walk.b) }) : t("w.placeValue.walk.startSubtract", { a: n(walk.a), b: n(walk.b) });
      if (walk.swapped) text += ` ${t("w.placeValue.walk.swapped", { a: n(walk.a), b: n(walk.b) })}`;
      expr = `${walk.a} ${sym} ${walk.b}`;
      break;
    case "combine": {
      const { a: x, b: y, carry, total } = s.vars;
      text = `${t("w.placeValue.walk.combine", { place: place(s.col) })} ${total <= 9 ? t("w.placeValue.walk.fits", { digit: n(total) }) : t("w.placeValue.walk.over")}`;
      expr = carry ? `${x} + ${y} + ${carry} = ${total}` : `${x} + ${y} = ${total}`;
      break;
    }
    case "regroup":
      text = `${t(`w.placeValue.tradeLong.${s.col}`)} ${t("w.placeValue.walk.carry", { rest: n(s.vars.rest) })}`;
      expr = `${s.vars.total} = 10 + ${s.vars.rest}`;
      break;
    case "borrow": {
      const from = s.from ?? s.col + 1;
      const first = s.firstBreak ? `${t("w.placeValue.walk.notEnough", { have: n(s.vars.have), need: n(s.vars.need), place: place(s.col) })} ` : "";
      const further = s.firstBreak && from > s.col + 1 ? `${t("w.placeValue.walk.emptyNext")} ` : "";
      text = `${first}${further}${t(`w.placeValue.breakLong.${from}`)} ${t("w.placeValue.walk.borrowWrite")}`;
      expr = `1 × ${10 ** from} = 10 × ${10 ** (from - 1)}`;
      break;
    }
    case "takeaway":
      text = `${s.vars.need > 0 ? t("w.placeValue.walk.takeaway", { need: n(s.vars.need), place: place(s.col) }) : t("w.placeValue.walk.takeNone", { place: place(s.col) })} ${t("w.placeValue.walk.write", { digit: n(s.vars.rest) })}`;
      expr = `${s.vars.have} − ${s.vars.need} = ${s.vars.rest}`;
      break;
    case "done":
      text = t(op === "add" ? "w.placeValue.walk.doneAdd" : "w.placeValue.walk.doneSubtract");
      expr = `${walk.a} ${sym} ${walk.b} = ${walk.result}`;
      break;
  }

  const setNumbers = (na: number, nb: number) => {
    setA(na);
    setB(fitB(na, nb));
    setStep(0);
  };

  return (
    <WidgetFrame title={title} subtitle={subtitle}>
      <div className="flex flex-wrap items-end gap-3">
        <NumberField label={t("w.placeValue.first")} value={a} max={max} onChange={(v) => setNumbers(v, b)} />
        <span className="pb-2 font-serif text-2xl text-ink-2" aria-hidden="true">
          {sym}
        </span>
        <NumberField label={t("w.placeValue.second")} value={b} max={op === "add" ? max - a : max} onChange={(v) => setNumbers(a, v)} />
        <ul className="list-none ps-0 [&>li]:m-0 ms-auto flex flex-wrap gap-1.5 text-xs">
          {(op === "add" ? (["a", "b", "carry"] as const) : (["plain", "fresh", "taken"] as const)).map((tone) => (
            <li key={tone} className="chip">
              <svg viewBox="-1 -1 10 10" className="h-3 w-3" aria-hidden="true">
                <BlockShape kind={0} tone={tone} />
              </svg>
              {t(`w.placeValue.legend.${tone}`, { a: n(walk.a), b: n(walk.b) })}
            </li>
          ))}
        </ul>
      </div>

      <div className="mt-4 grid gap-4 lg:grid-cols-[1fr_auto]">
        <div className="overflow-x-auto pb-1">
          <div dir="ltr" className={`grid gap-2 ${MIN_W[walk.cols]}`} style={{ gridTemplateColumns: `repeat(${walk.cols}, minmax(0, 1fr))` }}>
            {range(0, walk.cols - 1)
              .reverse()
              .map((i) => {
                const view = s.columns[i];
                return (
                  <ColumnCard key={i} name={t(`w.placeValue.colName.${i}`)} count={liveCount(view)} active={s.col === i || s.from === i}>
                    <ColumnBlocks kind={i} view={view} plusSeparators={op === "add"} label={t("w.placeValue.columnAria", { place: t(`w.placeValue.colName.${i}`), count: n(liveCount(view)) })} />
                  </ColumnCard>
                );
              })}
          </div>
        </div>
        <Written written={s.written} cols={walk.cols} sym={sym} active={s.col} from={s.from} resultDigits={columnsFor(walk.result)} done={s.kind === "done"} />
      </div>

      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <p className="text-xs font-semibold text-muted">{t("w.placeValue.stepOf", { i: n(step + 1), total: n(last + 1) })}</p>
        <p className="mt-1 font-serif text-2xl text-ink" dir="ltr">
          {expr}
        </p>
        <p className="mt-1.5 text-[0.95rem] leading-relaxed text-ink">{text}</p>
      </div>
      <div className="mt-3 flex flex-wrap gap-2">
        <button type="button" className="btn btn-ghost" disabled={step === 0} onClick={() => setStep((v) => Math.max(0, v - 1))}>
          <ChevronLeft size={16} aria-hidden="true" className="rtl:rotate-180" /> {t("w.placeValue.back")}
        </button>
        <button type="button" className="btn btn-primary" disabled={step >= last} onClick={() => setStep((v) => Math.min(last, v + 1))}>
          {t("w.placeValue.next")} <ChevronRight size={16} aria-hidden="true" className="rtl:rotate-180" />
        </button>
        <button type="button" className="btn btn-ghost ms-auto" disabled={step === 0} onClick={() => setStep(0)}>
          <RotateCcw size={15} aria-hidden="true" /> {t("w.placeValue.restart")}
        </button>
      </div>
    </WidgetFrame>
  );
}

function NumberField({ label, value, max, onChange }: { label: string; value: number; max: number; onChange: (v: number) => void }) {
  return (
    <label className="text-sm font-semibold text-ink-2">
      {label}
      <input
        type="number"
        inputMode="numeric"
        min={0}
        max={max}
        value={value}
        onChange={(e) => onChange(clampInt(e.target.value === "" ? 0 : Number(e.target.value), 0, Math.max(0, max), 0))}
        className="input mt-1 block w-28 py-1.5 font-mono"
        dir="ltr"
      />
    </label>
  );
}

/** The written column method, in step with the blocks. */
function Written({ written, cols, sym, active, from, resultDigits, done }: { written: WrittenView; cols: number; sym: string; active: number; from?: number; resultDigits: number; done: boolean }) {
  const { t } = useI18n();
  const order = range(0, cols - 1).reverse();
  const cell = (i: number) => `flex w-9 flex-col items-center justify-end rounded-md ${active === i || from === i ? "bg-gold-soft" : ""}`;
  return (
    <figure className="mx-auto self-start rounded-xl border border-line bg-card px-4 py-3" aria-label={t("w.placeValue.writtenAria")}>
      <figcaption className="mb-1 text-center text-xs font-semibold text-muted">{t("w.placeValue.written")}</figcaption>
      <div dir="ltr" className="font-serif text-2xl leading-none text-ink">
        {/* carries / borrow notes */}
        <div className="flex">
          <span className="w-7" />
          {order.map((i) => {
            const w = written.top[i];
            const c = written.carries[i];
            return (
              <span key={i} className={`${cell(i)} min-h-6 pb-0.5 text-sm`}>
                {c !== null && <span className="font-bold text-gold-ink">{c}</span>}
                {w.crossed.length > 0 && (
                  <span className="flex gap-0.5">
                    {w.crossed.slice(1).map((v, k) => (
                      <s key={k} className="text-muted">
                        {v}
                      </s>
                    ))}
                    <span className="font-bold text-gold-ink">{w.value}</span>
                  </span>
                )}
              </span>
            );
          })}
        </div>
        <div className="flex">
          <span className="w-7" />
          {order.map((i) => {
            const w = written.top[i];
            return (
              <span key={i} className={`${cell(i)} h-9`}>
                {w.crossed.length > 0 ? <s className="text-muted">{w.crossed[0]}</s> : topDigit(written, i, cols)}
              </span>
            );
          })}
        </div>
        <div className="flex border-b-2 border-ink pb-1">
          <span className="flex w-7 items-center justify-center text-ink-2">{sym}</span>
          {order.map((i) => (
            <span key={i} className={`${cell(i)} h-9`}>
              {bottomDigit(written, i)}
            </span>
          ))}
        </div>
        <div className="flex pt-1">
          <span className="w-7" />
          {order.map((i) => {
            const d = written.answer[i];
            const lead = i >= resultDigits;
            return (
              <span key={i} className={`${cell(i)} h-9 font-semibold ${lead ? "text-muted/60" : "text-ink"}`}>
                {d === null || (lead && done) ? "" : d}
              </span>
            );
          })}
        </div>
      </div>
    </figure>
  );
}

/** Top-line digit, blank for leading zeros. */
function topDigit(w: WrittenView, i: number, cols: number): string {
  const higherAllZero = range(i, cols - 1).every((j) => w.top[j].value === 0 && w.top[j].crossed.length === 0);
  return i > 0 && higherAllZero ? "" : String(w.top[i].value);
}

/** Bottom-line digit, blank for leading zeros. */
function bottomDigit(w: WrittenView, i: number): string {
  const higherAllZero = w.bottom.slice(i).every((d) => d === 0);
  return i > 0 && higherAllZero ? "" : String(w.bottom[i]);
}

