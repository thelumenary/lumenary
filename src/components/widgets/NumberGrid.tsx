"use client";

import { ChevronLeft, ChevronRight, FastForward, RotateCcw } from "lucide-react";
import { useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { clampInt, lcm, oneOf, range } from "./lib/number-common";
import { euclidSquares, euclidSteps, factorPairs, factorsOf, gcd, multiplesOf, sieveSteps } from "./lib/number-grid";

type Mode = "multiples" | "sieve" | "factors" | "gcd";

interface NumberGridProps {
  mode?: Mode;
  /** Largest number on the grid (default 100). */
  size?: number;
  /** Numbers per row (default 10). */
  columns?: number;
  /** "multiples": the number whose multiples are marked. */
  k?: number;
  /** "multiples": an optional second number, to find common multiples. */
  k2?: number;
  /** "factors": the number to factor. */
  n?: number;
  /** "gcd": the two numbers. */
  a?: number;
  b?: number;
  title?: string;
  subtitle?: string;
}

const PRIME_COLORS = ["var(--human)", "var(--formal)", "var(--compute)", "var(--sky)", "var(--warn)", "var(--gold)"];
const STEP_COLORS = ["var(--human)", "var(--formal)", "var(--compute)", "var(--sky)", "var(--gold)", "var(--warn)"];

/** A hundred grid for multiples and primes, factor-pair arrays, and Euclid's algorithm as cutting squares. */
export function NumberGrid({ mode, size, columns, k, k2, n, a, b, title, subtitle }: NumberGridProps) {
  const { t } = useI18n();
  const m = oneOf(mode, ["multiples", "sieve", "factors", "gcd"] as const, "multiples");
  const sz = clampInt(size, 10, 400, 100);
  const cols = clampInt(columns, 2, 20, 10);
  const head = { title: title ?? t(`w.numberGrid.title.${m}`), subtitle: subtitle ?? t(`w.numberGrid.subtitle.${m}`) };
  return (
    <WidgetFrame title={head.title} subtitle={head.subtitle}>
      {m === "multiples" && <Multiples size={sz} cols={cols} k0={clampInt(k, 1, 50, 3)} k20={k2 === undefined ? 0 : clampInt(k2, 0, 50, 0)} />}
      {m === "sieve" && <Sieve size={sz} cols={cols} />}
      {m === "factors" && <Factors n0={clampInt(n, 1, 200, 24)} />}
      {m === "gcd" && <Euclid a0={clampInt(a, 1, 300, 36)} b0={clampInt(b, 1, 300, 15)} />}
    </WidgetFrame>
  );
}

/* ------------------------------------------------------------------ grid with roving focus */

function NumberCells({ size, cols, picked, onPick, label, cell }: { size: number; cols: number; picked: number | null; onPick: (v: number) => void; label: string; cell: (v: number) => { className: string; aria: string; content?: React.ReactNode } }) {
  const refs = useRef<(HTMLButtonElement | null)[]>([]);
  const [focus, setFocus] = useState(1);
  const go = (v: number) => {
    const to = Math.max(1, Math.min(size, v));
    setFocus(to);
    refs.current[to]?.focus();
  };
  const onKey = (e: React.KeyboardEvent, v: number) => {
    const map: Record<string, number> = { ArrowRight: v + 1, ArrowLeft: v - 1, ArrowDown: v + cols, ArrowUp: v - cols, Home: v - ((v - 1) % cols), End: Math.min(size, v - ((v - 1) % cols) + cols - 1) };
    if (e.key in map) {
      e.preventDefault();
      go(map[e.key]);
    }
  };
  return (
    <div dir="ltr" className="overflow-x-auto pb-1">
      <div role="group" aria-label={label} className="mx-auto grid max-w-xl gap-1" style={{ gridTemplateColumns: `repeat(${cols}, minmax(1.85rem, 1fr))`, minWidth: `${cols * 1.95}rem` }}>
        {range(1, size).map((v) => {
          const c = cell(v);
          return (
            <button
              key={v}
              ref={(el) => {
                refs.current[v] = el;
              }}
              type="button"
              tabIndex={v === focus ? 0 : -1}
              aria-label={c.aria}
              aria-pressed={picked === v}
              onClick={() => {
                setFocus(v);
                onPick(v);
              }}
              onKeyDown={(e) => onKey(e, v)}
              className={`relative flex aspect-square items-center justify-center font-mono text-[0.8rem] leading-none transition-colors duration-300 ${picked === v ? "outline outline-2 outline-offset-1 outline-sky" : ""} ${c.className}`}
            >
              {c.content}
              <span className="relative">{v}</span>
            </button>
          );
        })}
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ multiples */

function Multiples({ size, cols, k0, k20 }: { size: number; cols: number; k0: number; k20: number }) {
  const { t, n } = useI18n();
  const [k, setK] = useState(k0);
  const [k2, setK2] = useState(k20 || Math.min(50, k0 + 1));
  const [second, setSecond] = useState(k20 > 0);
  const [picked, setPicked] = useState<number | null>(null);
  const maxK = Math.min(50, size);
  const mk = multiplesOf(k, size);
  const common = second ? multiplesOf(lcm(k, k2), size) : [];
  const l = lcm(k, k2);

  const info = (v: number, d: number) => {
    const q = Math.floor(v / d);
    const r = v % d;
    return (
      <p className="flex flex-wrap items-baseline gap-x-3">
        <span>{r === 0 ? t("w.numberGrid.isMultiple", { m: n(v), k: n(d) }) : t("w.numberGrid.notMultiple", { m: n(v), k: n(d) })}</span>
        <span className="font-serif text-lg text-ink-2" dir="ltr">
          {v} = {d} × {q}
          {r ? ` + ${r}` : ""}
        </span>
      </p>
    );
  };

  return (
    <div>
      <div className="mb-4 grid gap-4 sm:grid-cols-2">
        <Slider label={t("w.numberGrid.multiplesOf")} value={k} min={1} max={maxK} onChange={setK} accent="var(--formal)" />
        <div>
          <button type="button" aria-pressed={second} className={`btn btn-sm ${second ? "btn-primary" : "btn-ghost"}`} onClick={() => setSecond((s) => !s)}>
            {t("w.numberGrid.secondToggle")}
          </button>
          {second && (
            <div className="mt-2">
              <Slider label={t("w.numberGrid.andMultiplesOf")} value={k2} min={1} max={maxK} onChange={setK2} accent="var(--human)" />
            </div>
          )}
        </div>
      </div>
      <NumberCells
        size={size}
        cols={cols}
        picked={picked}
        onPick={setPicked}
        label={t("w.numberGrid.gridAria", { size: n(size) })}
        cell={(v) => {
          const a = v % k === 0;
          const b2 = second && v % k2 === 0;
          const tags = [a ? t("w.numberGrid.tagMultiple", { k: n(k) }) : "", b2 ? t("w.numberGrid.tagMultiple", { k: n(k2) }) : ""].filter(Boolean).join(", ");
          return {
            className: `rounded-md ${a && b2 ? "font-bold text-gold-ink" : a ? "font-bold text-ink" : "text-ink-2"} ${b2 ? "border-2 border-human" : "border border-line"} bg-card`,
            aria: tags ? `${v}: ${tags}` : `${v}`,
            content: a ? <span aria-hidden="true" className={`absolute inset-[12%] rounded-full ${b2 ? "bg-gold-soft ring-2 ring-gold" : "bg-formal-soft ring-1 ring-formal/60"}`} /> : undefined,
          };
        }}
      />
      <ul className="list-none ps-0 [&>li]:m-0 mt-2 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-2">
        <li className="flex items-center gap-1.5">
          <span aria-hidden="true" className="inline-block h-3.5 w-3.5 rounded-full bg-formal-soft ring-1 ring-formal/60" /> {t("w.numberGrid.legendK", { k: n(k) })}
        </li>
        {second && (
          <>
            <li className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-block h-3.5 w-3.5 rounded-sm border-2 border-human" /> {t("w.numberGrid.legendK2", { k: n(k2) })}
            </li>
            <li className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-flex h-4 w-4 items-center justify-center rounded-sm border-2 border-human">
                <span className="h-2.5 w-2.5 rounded-full bg-gold-soft ring-2 ring-gold" />
              </span>
              {t("w.numberGrid.legendBoth")}
            </li>
          </>
        )}
      </ul>
      <div className="mt-4 space-y-1.5 rounded-2xl bg-paper-2 px-5 py-4 text-[0.95rem] text-ink" aria-live="polite">
        <p>{t("w.numberGrid.countMultiples", { count: n(mk.length), k: n(k), size: n(size) })}</p>
        {second && (
          <p>
            {common.length > 0
              ? t("w.numberGrid.common", { k: n(k), k2: n(k2), list: common.slice(0, 8).map(n).join(", ") + (common.length > 8 ? ", …" : ""), lcm: n(l) })
              : t("w.numberGrid.noCommon", { k: n(k), k2: n(k2), size: n(size), lcm: n(l) })}
          </p>
        )}
        {picked !== null && picked <= size && (
          <div className="border-t border-line pt-2">
            {info(picked, k)}
            {second && info(picked, k2)}
          </div>
        )}
        {picked === null && <p className="text-sm text-muted">{t("w.numberGrid.tapHint")}</p>}
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ sieve */

function Sieve({ size, cols }: { size: number; cols: number }) {
  const { t, n } = useI18n();
  const { steps, primes } = useMemo(() => sieveSteps(size), [size]);
  const [step, setStep] = useState(0);
  const [picked, setPicked] = useState<number | null>(null);
  const last = steps.length - 1;
  const cur = steps[step];
  // When was each number crossed, and by which prime?
  const { crossedAt, crossedBy, primeAt } = useMemo(() => {
    const at = new Map<number, number>();
    const by = new Map<number, number>();
    const pAt = new Map<number, number>();
    steps.forEach((s, i) => {
      s.crossed.forEach((m) => {
        at.set(m, i);
        by.set(m, s.p ?? 1);
      });
      if (s.p) pAt.set(s.p, i);
    });
    return { crossedAt: at, crossedBy: by, primeAt: pAt };
  }, [steps]);
  const done = cur.kind === "done";
  const sievePrimes = steps.filter((s) => s.p).map((s) => s.p!);
  const colorOf = (p: number) => PRIME_COLORS[Math.max(0, sievePrimes.indexOf(p)) % PRIME_COLORS.length];
  const isCrossed = (v: number) => (crossedAt.get(v) ?? Infinity) <= step;
  const isCircled = (v: number) => (done && !isCrossed(v) && v > 1) || (primeAt.get(v) ?? Infinity) <= step;
  const root = Math.floor(Math.sqrt(size));

  let text: string;
  switch (cur.kind) {
    case "start":
      text = t("w.numberGrid.sieve.start", { size: n(size) });
      break;
    case "one":
      text = t("w.numberGrid.sieve.one");
      break;
    case "prime":
      text = `${t("w.numberGrid.sieve.prime", { p: n(cur.p!), count: n(cur.crossed.length) })} ${t("w.numberGrid.sieve.skip", { p: n(cur.p!), sq: n(cur.p! * cur.p!) })}`;
      break;
    default:
      text = `${t("w.numberGrid.sieve.done", { count: n(primes.length), size: n(size) })} ${t("w.numberGrid.sieve.why", { root: n(root), size: n(size) })}`;
  }

  const pickInfo = (v: number) => {
    if (v === 1) return t("w.numberGrid.sieve.oneInfo");
    if (isCrossed(v)) {
      const p = crossedBy.get(v)!;
      return (
        <>
          {t("w.numberGrid.sieve.crossedBy", { m: n(v), p: n(p) })}{" "}
          <span className="font-serif text-lg text-ink-2" dir="ltr">
            {v} = {p} × {v / p}
          </span>
        </>
      );
    }
    if (isCircled(v)) return t("w.numberGrid.sieve.isPrime", { m: n(v) });
    return t("w.numberGrid.sieve.undecided", { m: n(v) });
  };

  return (
    <div>
      <NumberCells
        size={size}
        cols={cols}
        picked={picked}
        onPick={setPicked}
        label={t("w.numberGrid.gridAria", { size: n(size) })}
        cell={(v) => {
          const crossed = isCrossed(v);
          const fresh = crossed && crossedAt.get(v) === step;
          const circled = isCircled(v);
          const current = cur.p === v;
          const by = crossedBy.get(v) ?? 1;
          return {
            className: `${current ? "bg-gold font-bold text-[#1b1406]" : circled ? "bg-gold-soft font-bold text-gold-ink ring-2 ring-gold" : fresh ? "bg-warn-soft text-muted" : crossed ? "bg-paper-2 text-muted" : "bg-card text-ink"} ${circled || current ? "rounded-full" : "rounded-md border border-line"}`,
            aria: `${v}: ${circled ? t("w.numberGrid.sieve.tagPrime") : crossed ? t("w.numberGrid.sieve.tagCrossed") : t("w.numberGrid.sieve.tagOpen")}`,
            content: crossed ? <span aria-hidden="true" className="absolute left-[12%] right-[12%] top-1/2 h-[2px] -rotate-45 rounded" style={{ background: by === 1 ? "var(--muted)" : colorOf(by) }} /> : undefined,
          };
        }}
      />
      <ul className="list-none ps-0 [&>li]:m-0 mt-2 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-2">
        <li className="flex items-center gap-1.5">
          <span aria-hidden="true" className="inline-block h-3.5 w-3.5 rounded-full bg-gold-soft ring-2 ring-gold" /> {t("w.numberGrid.sieve.legendPrime")}
        </li>
        <li className="flex items-center gap-1.5">
          <span aria-hidden="true" className="relative inline-block h-3.5 w-3.5 rounded-sm border border-line bg-paper-2">
            <span className="absolute left-0 right-0 top-1/2 h-[2px] -rotate-45 bg-muted" />
          </span>
          {t("w.numberGrid.sieve.legendCrossed")}
        </li>
        {sievePrimes
          .filter((p) => (primeAt.get(p) ?? Infinity) <= step)
          .map((p) => (
            <li key={p} className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-block h-[3px] w-4 rounded" style={{ background: colorOf(p) }} /> {t("w.numberGrid.sieve.legendBy", { p: n(p) })}
            </li>
          ))}
      </ul>
      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4 text-[0.95rem] text-ink" aria-live="polite">
        <p className="text-xs font-semibold text-muted">{t("w.numberGrid.stepOf", { i: n(step + 1), total: n(last + 1) })}</p>
        <p className="mt-1">{text}</p>
        {done && (
          <p className="mt-2 font-mono text-sm leading-relaxed text-ink-2" dir="ltr">
            {primes.join(", ")}
          </p>
        )}
        {picked !== null && picked <= size && <p className="mt-2 border-t border-line pt-2">{pickInfo(picked)}</p>}
      </div>
      <StepButtons step={step} last={last} setStep={setStep} finish />
    </div>
  );
}

function StepButtons({ step, last, setStep, finish = false }: { step: number; last: number; setStep: (f: (s: number) => number) => void; finish?: boolean }) {
  const { t } = useI18n();
  return (
    <div className="mt-3 flex flex-wrap gap-2">
      <button type="button" className="btn btn-ghost" disabled={step === 0} onClick={() => setStep((s) => Math.max(0, s - 1))}>
        <ChevronLeft size={16} aria-hidden="true" className="rtl:rotate-180" /> {t("w.numberGrid.back")}
      </button>
      <button type="button" className="btn btn-primary" disabled={step >= last} onClick={() => setStep((s) => Math.min(last, s + 1))}>
        {t("w.numberGrid.next")} <ChevronRight size={16} aria-hidden="true" className="rtl:rotate-180" />
      </button>
      {finish && (
        <button type="button" className="btn btn-ghost" disabled={step >= last} onClick={() => setStep(() => last)}>
          <FastForward size={15} aria-hidden="true" className="rtl:rotate-180" /> {t("w.numberGrid.finish")}
        </button>
      )}
      <button type="button" className="btn btn-ghost ms-auto" disabled={step === 0} onClick={() => setStep(() => 0)}>
        <RotateCcw size={15} aria-hidden="true" /> {t("w.numberGrid.restart")}
      </button>
    </div>
  );
}

function Slider({ label, value, min, max, onChange, accent }: { label: string; value: number; min: number; max: number; onChange: (v: number) => void; accent: string }) {
  const { n } = useI18n();
  return (
    <label className="block text-sm font-semibold text-ink-2">
      <span className="flex items-center justify-between gap-2">
        {label}
        <span className="font-mono text-base text-ink">{n(value)}</span>
      </span>
      <input type="range" min={min} max={max} value={value} onChange={(e) => onChange(Number(e.target.value))} className="mt-1.5 w-full" style={{ accentColor: accent }} dir="ltr" />
    </label>
  );
}

/* ------------------------------------------------------------------ factors */

function DotArray({ total, perRow, maxW = 360, maxH = 220, label }: { total: number; perRow: number; maxW?: number; maxH?: number; label: string }) {
  const rows = Math.ceil(total / perRow);
  const full = Math.floor(total / perRow);
  const P = 14;
  const w = perRow * P;
  const h = rows * P;
  return (
    <svg viewBox={`0 0 ${w} ${h}`} className="mx-auto block" style={{ width: "100%", maxWidth: Math.min(maxW, (w / h) * maxH), maxHeight: maxH }} role="img" aria-label={label}>
      {range(0, total - 1).map((i) => {
        const r = Math.floor(i / perRow);
        const c = i % perRow;
        const extra = r >= full;
        return <circle key={i} cx={c * P + P / 2} cy={r * P + P / 2} r={P * 0.36} fill={extra ? "var(--card)" : "var(--compute)"} stroke={extra ? "var(--warn)" : "none"} strokeWidth={extra ? 2 : 0} strokeDasharray={extra ? "2.5 2" : undefined} style={{ transition: "cx .3s ease, cy .3s ease" }} />;
      })}
    </svg>
  );
}

function Factors({ n0 }: { n0: number }) {
  const { t, n } = useI18n();
  const top = Math.max(100, n0);
  const [num, setNum] = useState(n0);
  const pairs = factorPairs(num);
  const [perRow, setPerRow] = useState(() => pairs[Math.floor((pairs.length - 1) / 2)]?.[1] ?? 1);
  const r = Math.min(perRow, num);
  const q = Math.floor(num / r);
  const left = num % r;
  const factors = factorsOf(num);
  const sq = Math.round(Math.sqrt(num));

  return (
    <div>
      <div className="mb-4 grid gap-4 sm:grid-cols-2">
        <Slider
          label={t("w.numberGrid.factors.dots")}
          value={num}
          min={1}
          max={top}
          onChange={(v) => {
            setNum(v);
            setPerRow((p) => Math.min(p, v));
          }}
          accent="var(--compute)"
        />
        <Slider label={t("w.numberGrid.factors.perRow")} value={r} min={1} max={num} onChange={setPerRow} accent="var(--warn)" />
      </div>
      <div className="grid items-start gap-5 md:grid-cols-[1fr_1fr]">
        <div dir="ltr" className="rounded-xl border border-line bg-card p-3">
          <DotArray total={num} perRow={r} label={left === 0 ? `${num} = ${q} × ${r}` : `${num} = ${q} × ${r} + ${left}`} />
        </div>
        <div className="rounded-2xl bg-paper-2 px-5 py-4 text-[0.95rem] text-ink" aria-live="polite">
          <p className="font-serif text-2xl" dir="ltr">
            {num} = {q} × {r}
            {left ? <span className="text-warn"> + {left}</span> : ""}
          </p>
          <p className="mt-2">{left === 0 ? t("w.numberGrid.factors.fits", { n: n(num), r: n(r), q: n(q) }) : t("w.numberGrid.factors.left", { n: n(num), r: n(r), q: n(q), left: n(left) })}</p>
        </div>
      </div>
      <div className="mt-5">
        <p className="text-sm font-semibold text-ink-2">{t("w.numberGrid.factors.pairs", { n: n(num) })}</p>
        <div className="mt-2 flex flex-wrap items-end gap-2" dir="ltr">
          {pairs.map(([x, y]) => (
            <button key={x} type="button" aria-pressed={r === y && left === 0} onClick={() => setPerRow(y)} className={`flex flex-col items-center gap-1 rounded-xl border px-2 py-2 transition-colors ${r === y ? "border-compute bg-compute-soft" : "border-line bg-card hover:bg-paper-2"}`}>
              <DotArray total={num} perRow={y} maxW={110} maxH={70} label={`${x} × ${y}`} />
              <span className="font-serif text-sm text-ink">
                {x} × {y}
              </span>
            </button>
          ))}
        </div>
        <p className="mt-3 text-[0.95rem] text-ink">
          {t("w.numberGrid.factors.list", { n: n(num), count: n(factors.length) })}{" "}
          <span className="font-mono" dir="ltr">
            {factors.join(", ")}
          </span>
        </p>
        <p className="mt-1 text-sm text-ink-2">
          {num === 1 ? t("w.numberGrid.factors.one") : factors.length === 2 ? t("w.numberGrid.factors.prime", { n: n(num) }) : t("w.numberGrid.factors.composite", { n: n(num) })}
          {num > 1 && sq * sq === num && ` ${t("w.numberGrid.factors.square", { n: n(num), r: n(sq) })}`}
        </p>
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ Euclid */

function Euclid({ a0, b0 }: { a0: number; b0: number }) {
  const { t, n } = useI18n();
  const [a, setA] = useState(a0);
  const [b, setB] = useState(b0);
  const [step, setStep] = useState(0);
  const [tiling, setTiling] = useState(false);
  const steps = useMemo(() => euclidSteps(a, b), [a, b]);
  const squares = useMemo(() => euclidSquares(a, b), [a, b]);
  const g = gcd(a, b);
  const last = steps.length;
  const done = step >= last;
  const top = Math.max(100, a0, b0);
  const S = Math.min(600 / a, 300 / b);
  const W = a * S;
  const H = b * S;
  const reset = (na: number, nb: number) => {
    setA(na);
    setB(nb);
    setStep(0);
    setTiling(false);
  };

  let text: string;
  if (step === 0) text = t("w.numberGrid.gcd.start", { a: n(a), b: n(b) });
  else {
    const s = steps[step - 1];
    text = s.r === 0 ? t("w.numberGrid.gcd.exact", { q: n(s.q), s: n(s.small) }) : t("w.numberGrid.gcd.cut", { q: n(s.q), s: n(s.small), r: n(s.r) });
    if (done) text += ` ${t("w.numberGrid.gcd.done", { a: n(a), b: n(b), g: n(g) })}`;
  }

  return (
    <div>
      <div className="mb-4 grid gap-4 sm:grid-cols-2">
        <Slider label={t("w.numberGrid.gcd.width")} value={a} min={1} max={top} onChange={(v) => reset(v, b)} accent="var(--human)" />
        <Slider label={t("w.numberGrid.gcd.height")} value={b} min={1} max={top} onChange={(v) => reset(a, v)} accent="var(--formal)" />
      </div>
      <div dir="ltr" className="flex justify-center">
        <svg viewBox={`-4 -4 ${W + 8} ${H + 8}`} className="block w-full" style={{ maxWidth: W + 8, maxHeight: 320 }} role="img" aria-label={t("w.numberGrid.gcd.aria", { a: n(a), b: n(b) })}>
          <rect x={0} y={0} width={W} height={H} fill="var(--paper-2)" stroke="var(--ink-2)" strokeWidth={2} />
          {squares
            .filter((sq) => sq.step < step)
            .map((sq, i) => {
              const current = sq.step === step - 1;
              const color = STEP_COLORS[sq.step % STEP_COLORS.length];
              const px = sq.size * S;
              return (
                <g key={i} className={current ? "animate-float-up" : undefined}>
                  <rect x={sq.x * S} y={sq.y * S} width={px} height={px} fill={`color-mix(in oklab, ${color} ${current ? 45 : 25}%, var(--card))`} stroke={color} strokeWidth={current ? 2.5 : 1.5} />
                  {px >= 24 && (
                    <text x={sq.x * S + px / 2} y={sq.y * S + px / 2 + 5} textAnchor="middle" fontSize={Math.min(16, px / 3)} fontWeight="700" fill="var(--ink)">
                      {sq.size}
                    </text>
                  )}
                </g>
              );
            })}
          {done && tiling && g * S >= 3 && (
            <g aria-hidden="true">
              {range(1, a / g - 1).map((i) => (
                <line key={`v${i}`} x1={i * g * S} x2={i * g * S} y1={0} y2={H} stroke="var(--ink)" strokeOpacity={0.45} strokeDasharray="3 3" />
              ))}
              {range(1, b / g - 1).map((i) => (
                <line key={`h${i}`} x1={0} x2={W} y1={i * g * S} y2={i * g * S} stroke="var(--ink)" strokeOpacity={0.45} strokeDasharray="3 3" />
              ))}
            </g>
          )}
          <rect x={0} y={0} width={W} height={H} fill="none" stroke="var(--ink-2)" strokeWidth={2} />
        </svg>
      </div>
      <p className="mt-1 text-center font-mono text-xs text-muted" dir="ltr">
        {a} × {b}
      </p>
      <div className="mt-3 grid gap-4 md:grid-cols-[1fr_auto]">
        <div className="rounded-2xl bg-paper-2 px-5 py-4 text-[0.95rem] text-ink" aria-live="polite">
          <p className="text-xs font-semibold text-muted">{t("w.numberGrid.stepOf", { i: n(step + 1), total: n(last + 1) })}</p>
          <p className="mt-1">{text}</p>
          {done && g * S >= 3 && (
            <button type="button" aria-pressed={tiling} className={`btn btn-sm mt-3 ${tiling ? "btn-primary" : "btn-ghost"}`} onClick={() => setTiling((v) => !v)}>
              {t("w.numberGrid.gcd.tiling", { g: n(g) })}
            </button>
          )}
        </div>
        <ol className="list-none ps-0 space-y-1 rounded-xl border border-line bg-card px-4 py-3 font-serif text-lg text-ink" dir="ltr" aria-label={t("w.numberGrid.gcd.equations")}>
          {steps.slice(0, step).map((s, i) => (
            <li key={i} className={`flex items-center gap-2 ${i === step - 1 ? "font-semibold" : "text-ink-2"}`}>
              <span aria-hidden="true" className="inline-block h-3 w-3 rounded-sm" style={{ background: STEP_COLORS[i % STEP_COLORS.length] }} />
              {s.big} = {s.q} × {s.small} + {s.r}
            </li>
          ))}
          {done && <li className="border-t border-line pt-1 font-semibold text-gold-ink">gcd({a}, {b}) = {g}</li>}
          {step === 0 && <li className="text-muted">…</li>}
        </ol>
      </div>
      <StepButtons step={step} last={last} setStep={setStep} />
    </div>
  );
}
