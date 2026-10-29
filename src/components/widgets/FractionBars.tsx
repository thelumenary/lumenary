"use client";

import { ChevronLeft, ChevronRight, Minus, Plus, RotateCcw, X } from "lucide-react";
import { useId, useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { clampInt, lcm, oneOf, range } from "./lib/number-common";
import { compare, decimalText, fracText, mixedText, parseList, parseValue, reduce, valueOf, withDenominator, type Frac, type ParsedValue } from "./lib/number-fraction";

type Mode = "compare" | "equivalent" | "add" | "line";

interface FractionBarsProps {
  mode?: Mode;
  /** Fractions as strings: "3/4", "1 1/2", "2"; decimals such as "0.75" are also accepted. */
  fractions?: string[];
  /** Largest denominator offered by the controls (default 12). */
  maxDenominator?: number;
  /** "add" mode only: "+" (default) or "-". */
  op?: string;
  title?: string;
  subtitle?: string;
}

const COLORS = ["var(--human)", "var(--formal)", "var(--compute)", "var(--sky)", "var(--gold)", "var(--warn)"];
const DEFAULTS: Record<Mode, string[]> = { compare: ["3/4", "2/3"], equivalent: ["2/3"], add: ["1/2", "1/3"], line: ["1/4", "0.5", "2/3", "0.75"] };

/** Fraction strips and a fraction number line: compare, find equivalents, add/subtract, and place values. */
export function FractionBars({ mode, fractions, maxDenominator, op, title, subtitle }: FractionBarsProps) {
  const { t } = useI18n();
  const m = oneOf(mode, ["compare", "equivalent", "add", "line"] as const, "compare");
  const maxDen = clampInt(maxDenominator, 2, 24, 12);
  const parsed = useMemo(() => parseList(fractions === undefined ? DEFAULTS[m] : fractions), [fractions, m]);
  const props = { values: parsed.values, bad: parsed.bad, maxDen };
  const head = { title: title ?? t(`w.fractions.title.${m}`), subtitle: subtitle ?? t(`w.fractions.subtitle.${m}`) };
  return (
    <WidgetFrame title={head.title} subtitle={head.subtitle}>
      {m === "compare" && <CompareMode {...props} />}
      {m === "equivalent" && <EquivalentMode {...props} />}
      {m === "add" && <AddMode {...props} op={op === "-" || op === "−" || op === "subtract" ? "-" : "+"} />}
      {m === "line" && <LineMode {...props} />}
    </WidgetFrame>
  );
}

interface ModeProps {
  values: ParsedValue[];
  bad: string[];
  maxDen: number;
}

/* ------------------------------------------------------------------ shared pieces */

function BadInput({ items, why }: { items: string[]; why?: string }) {
  const { t } = useI18n();
  if (items.length === 0) return null;
  return (
    <p className="mb-3 rounded-lg bg-warn-soft px-3 py-2 text-sm text-ink">
      {t("w.fractions.bad", { list: items.map((s) => `“${s}”`).join(", ") })} {why}
    </p>
  );
}

/** A fraction written the school way: numerator over a bar over denominator. */
function FracView({ f, className = "" }: { f: Frac; className?: string }) {
  if (f.d === 1) return <span className={className}>{f.n}</span>;
  return (
    <span className={`inline-flex items-center ${className}`}>
      <span className="sr-only">
        {f.n}/{f.d}
      </span>
      <span aria-hidden="true" className="mx-0.5 inline-flex flex-col items-center align-middle leading-none">
        <span className="px-0.5 pb-0.5">{f.n}</span>
        <span className="border-t-2 border-current px-0.5 pt-0.5">{f.d}</span>
      </span>
    </span>
  );
}

const BW = 560;
const BH = 40;

interface Segment {
  from: number;
  to: number;
  color: string;
  hatch?: boolean;
}

/** One strip: `wholes` wholes, each cut into `den` equal parts; segments are measured in parts. */
function BarSvg({ wholes, den, segments, markers = [], majorEvery, label }: { wholes: number; den: number; segments: Segment[]; markers?: number[]; majorEvery?: number; label: string }) {
  const id = useId().replace(/:/g, "");
  const total = wholes * den;
  const px = (parts: number) => (parts / total) * BW;
  return (
    <svg viewBox={`-2 -2 ${BW + 4} ${BH + 4}`} className="block w-full" role="img" aria-label={label}>
      <defs>
        <pattern id={`h${id}`} width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
          <line x1="0" y1="0" x2="0" y2="7" stroke="var(--ink-2)" strokeWidth="2" />
        </pattern>
      </defs>
      {range(0, wholes - 1).map((w) => (
        <rect key={w} x={px(w * den)} y={0} width={px(den)} height={BH} fill="var(--card)" />
      ))}
      {segments.map((s, k) => (
        <g key={k}>
          <rect x={px(s.from)} y={0} width={px(s.to - s.from)} height={BH} fill={s.hatch ? "var(--paper-2)" : `color-mix(in oklab, ${s.color} 62%, var(--card))`} style={{ transition: "width .35s ease, x .35s ease" }} />
          {s.hatch && <rect x={px(s.from)} y={0} width={px(s.to - s.from)} height={BH} fill={`url(#h${id})`} opacity={0.55} />}
        </g>
      ))}
      {range(1, total - 1).map((k) => {
        const whole = k % den === 0;
        const major = !whole && majorEvery !== undefined && k % majorEvery === 0;
        return <line key={k} x1={px(k)} x2={px(k)} y1={0} y2={BH} stroke="var(--ink-2)" strokeOpacity={whole || major ? 1 : 0.45} strokeWidth={whole ? 3 : major ? 2.2 : total > 60 ? 0.5 : 1} />;
      })}
      {range(0, wholes - 1).map((w) => (
        <rect key={w} x={px(w * den)} y={0} width={px(den)} height={BH} fill="none" stroke="var(--ink-2)" strokeWidth={2} rx={2} />
      ))}
      {markers.map((v, k) => (
        <line key={k} x1={(v / wholes) * BW} x2={(v / wholes) * BW} y1={-2} y2={BH + 2} stroke="var(--ink)" strokeWidth={1.5} strokeDasharray="4 3" />
      ))}
    </svg>
  );
}

function BarRow({ f, color, wholes, markers, labelFrac, children }: { f: Frac; color: string; wholes: number; markers?: number[]; labelFrac?: Frac; children?: React.ReactNode }) {
  const { t, n } = useI18n();
  return (
    <div className="flex items-center gap-3">
      <span className="w-12 shrink-0 text-center font-serif text-xl text-ink" style={{ color }}>
        <FracView f={labelFrac ?? f} />
      </span>
      <div className="min-w-0 flex-1">
        {children ?? <BarSvg wholes={wholes} den={f.d} segments={[{ from: 0, to: f.n, color }]} markers={markers} label={t("w.fractions.barAria", { n: n(f.n), d: n(f.d) })} />}
      </div>
    </div>
  );
}

function FracStepper({ f, onChange, maxDen, maxValue, color, index }: { f: Frac; onChange: (f: Frac) => void; maxDen: number; maxValue: number; color: string; index: number }) {
  const { t, n } = useI18n();
  const row = (part: "n" | "d") => {
    const v = part === "n" ? f.n : f.d;
    const lo = part === "n" ? 0 : 1;
    const hi = part === "n" ? Math.floor(maxValue * f.d) : maxDen;
    const set = (nv: number) => {
      if (part === "n") onChange({ n: nv, d: f.d });
      else onChange({ n: Math.min(f.n, Math.floor(maxValue * nv)), d: nv });
    };
    const name = t(part === "n" ? "w.fractions.numerator" : "w.fractions.denominator");
    return (
      <div className="flex items-center gap-1.5">
        <button type="button" className="btn btn-ghost h-8 w-8 !p-0" aria-label={t("w.fractions.less", { part: name, i: n(index + 1) })} disabled={v <= lo} onClick={() => set(v - 1)}>
          <Minus size={14} aria-hidden="true" />
        </button>
        <span className="w-7 text-center font-mono text-sm text-ink">{v}</span>
        <button type="button" className="btn btn-ghost h-8 w-8 !p-0" aria-label={t("w.fractions.more", { part: name, i: n(index + 1) })} disabled={v >= hi} onClick={() => set(v + 1)}>
          <Plus size={14} aria-hidden="true" />
        </button>
      </div>
    );
  };
  return (
    <div className="flex items-center gap-2 rounded-xl border border-line bg-card px-2.5 py-1.5" role="group" aria-label={t("w.fractions.editAria", { i: n(index + 1) })}>
      <span className="h-8 w-1.5 rounded-full" style={{ background: color }} aria-hidden="true" />
      <div className="space-y-1" dir="ltr">
        {row("n")}
        <div className="mx-1 border-t border-ink-2" />
        {row("d")}
      </div>
    </div>
  );
}

const relSymbol = (c: -1 | 0 | 1) => (c < 0 ? "<" : c > 0 ? ">" : "=");

/* ------------------------------------------------------------------ compare */

function CompareMode({ values, bad, maxDen }: ModeProps) {
  const { t, n } = useI18n();
  const fits = values.filter((v) => valueOf(v.frac) <= 2 && v.frac.d <= 100).slice(0, 6);
  const tooBig = values.filter((v) => !fits.includes(v)).map((v) => v.label);
  const start = fits.length ? fits.map((v) => v.frac) : [{ n: 1, d: 2 }];
  const [list, setList] = useState<Frac[]>(start);
  const wholes = list.some((f) => valueOf(f) > 1) ? 2 : 1;
  const common = list.reduce((l, f) => lcm(l, f.d), 1);
  const order = list.map((f, i) => ({ f, i })).sort((x, y) => compare(x.f, y.f));
  const markers = list.map(valueOf);

  let verdict: React.ReactNode;
  if (list.length === 2) {
    const c = compare(list[0], list[1]);
    verdict = (
      <>
        <FracView f={list[0]} /> <span className="mx-1.5">{relSymbol(c)}</span> <FracView f={list[1]} />
      </>
    );
  } else {
    verdict = order.map(({ f, i }, k) => (
      <span key={i}>
        {k > 0 && <span className="mx-1.5">{relSymbol(compare(order[k - 1].f, f))}</span>}
        <FracView f={f} />
      </span>
    ));
  }
  const allEqual = order.every(({ f }) => compare(f, order[0].f) === 0);

  return (
    <div>
      <BadInput items={[...bad, ...tooBig]} why={tooBig.length ? t("w.fractions.upToTwo") : undefined} />
      <div dir="ltr" className="space-y-2.5">
        {list.map((f, i) => (
          <BarRow key={i} f={f} color={COLORS[i % COLORS.length]} wholes={wholes} markers={markers} />
        ))}
      </div>
      <div className="mt-4 flex flex-wrap gap-2">
        {list.map((f, i) => (
          <FracStepper key={i} f={f} index={i} color={COLORS[i % COLORS.length]} maxDen={maxDen} maxValue={2} onChange={(nf) => setList((prev) => prev.map((g, k) => (k === i ? nf : g)))} />
        ))}
      </div>
      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <p className="font-serif text-3xl text-ink" dir="ltr">
          {verdict}
        </p>
        {list.length > 1 && (
          <>
            <p className="mt-2 text-[0.95rem] text-ink">{allEqual ? t("w.fractions.compare.equal") : t("w.fractions.compare.why", { d: n(common) })}</p>
            {common <= 999 && list.some((f) => f.d !== common) && (
              <p className="mt-1 flex flex-wrap items-center gap-x-4 gap-y-1 font-serif text-xl text-ink-2" dir="ltr">
                {list.map((f, i) => (
                  <span key={i} className="inline-flex items-center">
                    <FracView f={f} /> <span className="mx-1">=</span> <FracView f={withDenominator(f, common)} />
                  </span>
                ))}
              </p>
            )}
          </>
        )}
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ equivalent */

function EquivalentMode({ values, bad, maxDen }: ModeProps) {
  const { t, n } = useI18n();
  const given = values.find((v) => valueOf(v.frac) <= 2 && v.frac.d <= 100)?.frac ?? { n: 2, d: 3 };
  const base = reduce(given);
  const kGiven = given.d / base.d;
  const maxK = Math.max(1, Math.floor(maxDen / base.d), kGiven);
  const [k, setK] = useState(kGiven);
  const wholes = valueOf(base) > 1 ? 2 : 1;
  const cur = { n: base.n * k, d: base.d * k };
  const ignored = values.length > 1 ? values.slice(1).map((v) => v.label) : [];

  return (
    <div>
      <BadInput items={bad} />
      {ignored.length > 0 && <p className="mb-3 text-sm text-muted">{t("w.fractions.equiv.onlyFirst")}</p>}
      <div dir="ltr" className="space-y-2.5">
        <BarRow f={base} color={COLORS[0]} wholes={wholes} />
        <BarRow f={cur} color={COLORS[1]} wholes={wholes}>
          <BarSvg wholes={wholes} den={cur.d} segments={[{ from: 0, to: cur.n, color: COLORS[1] }]} majorEvery={k > 1 ? k : undefined} label={t("w.fractions.barAria", { n: n(cur.n), d: n(cur.d) })} />
        </BarRow>
      </div>
      <label className="mt-4 block max-w-md text-sm font-semibold text-ink-2">
        <span className="flex items-center justify-between">
          {t("w.fractions.equiv.split")}
          <span className="font-mono text-ink" dir="ltr">
            × {k}
          </span>
        </span>
        <input type="range" min={1} max={maxK} value={k} onChange={(e) => setK(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--formal)]" dir="ltr" />
      </label>
      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <p className="flex flex-wrap items-center font-serif text-2xl text-ink" dir="ltr">
          <FracView f={base} />
          <span className="mx-2">=</span>
          <span className="inline-flex flex-col items-center leading-none" aria-hidden="true">
            <span className="px-0.5 pb-0.5">
              {base.n} × {k}
            </span>
            <span className="border-t-2 border-current px-0.5 pt-0.5">
              {base.d} × {k}
            </span>
          </span>
          <span className="sr-only">
            ({base.n} × {k}) / ({base.d} × {k})
          </span>
          <span className="mx-2">=</span>
          <FracView f={cur} />
        </p>
        <p className="mt-2 text-[0.95rem] text-ink">{k === 1 ? t("w.fractions.equiv.simplest") : t("w.fractions.equiv.explain", { k: n(k), shaded: n(cur.n), parts: n(cur.d) })}</p>
      </div>
      <div className="mt-3">
        <p className="text-sm font-semibold text-ink-2">{t("w.fractions.equiv.family")}</p>
        <div className="mt-1.5 flex flex-wrap items-center gap-1 font-serif text-lg" dir="ltr">
          {range(1, maxK).map((j) => (
            <span key={j} className="inline-flex items-center">
              {j > 1 && <span className="mx-0.5 text-muted">=</span>}
              <button type="button" aria-pressed={j === k} onClick={() => setK(j)} className={`rounded-lg px-1.5 py-0.5 transition-colors ${j === k ? "bg-formal-soft text-ink ring-2 ring-formal" : "text-ink-2 hover:bg-paper-2"}`}>
                <FracView f={{ n: base.n * j, d: base.d * j }} />
              </button>
            </span>
          ))}
        </div>
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ add / subtract */

function AddMode({ values, bad, maxDen, op: op0 }: ModeProps & { op: "+" | "-" }) {
  const { t, n } = useI18n();
  const proper = values.filter((v) => valueOf(v.frac) <= 1 && v.frac.d <= maxDen * 2);
  const tooBig = values.filter((v) => !proper.includes(v)).map((v) => v.label);
  const [fs, setFs] = useState<[Frac, Frac]>([proper[0]?.frac ?? { n: 1, d: 2 }, proper[1]?.frac ?? { n: 1, d: 3 }]);
  const [op, setOp] = useState<"+" | "-">(op0);
  const [step, setStep] = useState(0);
  const swapped = op === "-" && compare(fs[0], fs[1]) < 0;
  const [x, y] = swapped ? [fs[1], fs[0]] : fs;
  const L = lcm(x.d, y.d);
  const X = withDenominator(x, L);
  const Y = withDenominator(y, L);
  const resultN = op === "+" ? X.n + Y.n : X.n - Y.n;
  const result = { n: resultN, d: L };
  const simple = reduce(result);
  const wholes = resultN > L ? 2 : 1;
  const sym = op === "+" ? "+" : "−";
  const same = x.d === y.d;
  const setF = (i: number, f: Frac) => {
    setFs((prev) => (i === 0 ? [f, prev[1]] : [prev[0], f]));
    setStep(0);
  };

  let text: string;
  let formula: React.ReactNode;
  if (step === 0) {
    text = same ? t("w.fractions.add.sameSize") : t("w.fractions.add.different", { a: n(x.d), b: n(y.d) });
    formula = (
      <>
        <FracView f={x} /> <span className="mx-1.5">{sym}</span> <FracView f={y} /> <span className="mx-1.5">=</span> ?
      </>
    );
  } else if (step === 1) {
    text = same ? t("w.fractions.add.sameSize") : t("w.fractions.add.common", { d: n(L) });
    formula = (
      <>
        <FracView f={x} /> <span className="mx-1">=</span> <FracView f={X} />
        <span className="mx-3 text-muted">·</span>
        <FracView f={y} /> <span className="mx-1">=</span> <FracView f={Y} />
      </>
    );
  } else {
    text = op === "+" ? t("w.fractions.add.combine", { a: n(X.n), b: n(Y.n), total: n(resultN) }) : t("w.fractions.add.takeAway", { a: n(X.n), b: n(Y.n), total: n(resultN) });
    const extra = simple.d !== L || simple.n > simple.d;
    formula = (
      <>
        <FracView f={X} /> <span className="mx-1.5">{sym}</span> <FracView f={Y} /> <span className="mx-1.5">=</span> <FracView f={result} />
        {extra && simple.d !== L && (
          <>
            <span className="mx-1.5">=</span> <FracView f={simple} />
          </>
        )}
        {simple.n > simple.d && simple.d !== 1 && <span className="ms-2 text-lg text-ink-2">({mixedText(simple)})</span>}
      </>
    );
  }

  const den1 = step === 0 ? x.d : L;
  const den2 = step === 0 ? y.d : L;
  const n1 = step === 0 ? x.n : X.n;
  const n2 = step === 0 ? y.n : Y.n;

  return (
    <div>
      <BadInput items={[...bad, ...tooBig]} why={tooBig.length ? t("w.fractions.upToOne") : undefined} />
      <div className="mb-3 flex flex-wrap items-center gap-2">
        {(["+", "-"] as const).map((o) => (
          <button key={o} type="button" aria-pressed={op === o} className={`btn btn-sm ${op === o ? "btn-primary" : "btn-ghost"}`} onClick={() => (setOp(o), setStep(0))}>
            {t(o === "+" ? "w.fractions.add.opAdd" : "w.fractions.add.opSubtract")}
          </button>
        ))}
      </div>
      <div dir="ltr" className="space-y-2.5">
        <BarRow f={x} color={COLORS[0]} wholes={wholes} labelFrac={step === 0 ? x : X}>
          <BarSvg wholes={wholes} den={den1} segments={[{ from: 0, to: n1, color: COLORS[0] }]} label={t("w.fractions.barAria", { n: n(n1), d: n(den1) })} />
        </BarRow>
        <BarRow f={y} color={COLORS[1]} wholes={wholes} labelFrac={step === 0 ? y : Y}>
          <BarSvg wholes={wholes} den={den2} segments={[{ from: 0, to: n2, color: COLORS[1] }]} label={t("w.fractions.barAria", { n: n(n2), d: n(den2) })} />
        </BarRow>
        {step === 2 && (
          <div className="animate-float-up border-t border-dashed border-line-2 pt-2.5">
            <BarRow f={result} color="var(--gold-ink)" wholes={wholes}>
              <BarSvg
                wholes={wholes}
                den={L}
                segments={op === "+" ? [{ from: 0, to: X.n, color: COLORS[0] }, { from: X.n, to: X.n + Y.n, color: COLORS[1] }] : [{ from: 0, to: resultN, color: COLORS[0] }, { from: resultN, to: X.n, color: COLORS[1], hatch: true }]}
                label={t("w.fractions.barAria", { n: n(resultN), d: n(L) })}
              />
            </BarRow>
          </div>
        )}
      </div>
      <div className="mt-4 flex flex-wrap gap-2">
        {fs.map((f, i) => (
          <FracStepper key={i} f={f} index={i} color={COLORS[(swapped ? 1 - i : i) % COLORS.length]} maxDen={maxDen} maxValue={1} onChange={(nf) => setF(i, nf)} />
        ))}
      </div>
      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <p className="text-xs font-semibold text-muted">{t("w.fractions.stepOf", { i: n(step + 1), total: n(3) })}</p>
        <p className="mt-1 flex flex-wrap items-center font-serif text-2xl text-ink" dir="ltr">
          {formula}
        </p>
        <p className="mt-2 text-[0.95rem] text-ink">
          {text}
          {swapped && ` ${t("w.fractions.add.swapped")}`}
        </p>
      </div>
      <div className="mt-3 flex flex-wrap gap-2">
        <button type="button" className="btn btn-ghost" disabled={step === 0} onClick={() => setStep((s) => s - 1)}>
          <ChevronLeft size={16} aria-hidden="true" className="rtl:rotate-180" /> {t("w.fractions.back")}
        </button>
        <button type="button" className="btn btn-primary" disabled={step === 2} onClick={() => setStep((s) => s + 1)}>
          {t("w.fractions.next")} <ChevronRight size={16} aria-hidden="true" className="rtl:rotate-180" />
        </button>
        <button type="button" className="btn btn-ghost ms-auto" disabled={step === 0} onClick={() => setStep(0)}>
          <RotateCcw size={15} aria-hidden="true" /> {t("w.fractions.restart")}
        </button>
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ number line */

const LW = 640;
const LX0 = 28;
const LX1 = LW - 28;

function LineMode({ values, bad, maxDen }: ModeProps) {
  const { t, n } = useI18n();
  const [points, setPoints] = useState<ParsedValue[]>(values.slice(0, 12));
  const firstDen = values.length ? reduce(values[0].frac).d : 4;
  const [d, setD] = useState(firstDen <= maxDen ? firstDen : Math.min(10, maxDen));
  const [draft, setDraft] = useState("");
  const [error, setError] = useState<string | null>(null);
  const span = points.some((p) => valueOf(p.frac) > 1) ? 2 : 1;
  const onLine = points.filter((p) => valueOf(p.frac) <= span);
  const off = points.filter((p) => valueOf(p.frac) > 2).map((p) => p.label);
  const xOf = (v: number) => LX0 + (v / span) * (LX1 - LX0);

  // Group equal values; assign label rows so labels don't collide.
  const groups: { v: Frac; labels: string[]; colorIdx: number }[] = [];
  onLine
    .map((p, i) => ({ p, i }))
    .sort((a, b) => compare(a.p.frac, b.p.frac))
    .forEach(({ p, i }) => {
      const g = groups.find((x) => compare(x.v, p.frac) === 0);
      if (g) {
        if (!g.labels.includes(p.label)) g.labels.push(p.label);
      } else groups.push({ v: p.frac, labels: [p.label], colorIdx: i });
    });
  const lastX: number[] = [];
  const rows = groups.map((g) => {
    const x = xOf(valueOf(g.v));
    const w = g.labels.join(" = ").length * 7.5 + 10;
    let r = 0;
    while (lastX[r] !== undefined && x - w / 2 < lastX[r]) r++;
    lastX[r] = x + w / 2;
    return r;
  });
  const maxRow = Math.max(0, ...rows);
  const lineY = 40 + maxRow * 22 + 24;
  const H = lineY + 54;
  const ticks = span * d;
  const labelTicks = ticks <= 16;

  const place = () => {
    const p = parseValue(draft);
    if (!p) return setError(t("w.fractions.line.cantRead", { s: draft.trim() }));
    if (valueOf(p.frac) > 2) return setError(t("w.fractions.line.tooBig", { s: p.label }));
    setPoints((prev) => [...prev, p].slice(-12));
    setDraft("");
    setError(null);
  };

  const chain = groups.map((g) => g.labels.join(" = ")).join(" < ");

  return (
    <div>
      <BadInput items={bad} />
      {off.length > 0 && <p className="mb-3 text-sm text-muted">{t("w.fractions.line.offLine", { list: off.join(", ") })}</p>}
      <div dir="ltr" className="overflow-x-auto">
        <svg viewBox={`0 0 ${LW} ${H}`} className="block w-full min-w-[30rem]" role="img" aria-label={t("w.fractions.line.aria", { list: chain || "—" })}>
          <line x1={LX0 - 10} x2={LX1 + 10} y1={lineY} y2={lineY} stroke="var(--ink-2)" strokeWidth="2" />
          {range(0, ticks).map((k) => {
            const whole = k % d === 0;
            const x = xOf(k / d);
            return (
              <g key={`${d}-${k}`}>
                <line x1={x} x2={x} y1={lineY - (whole ? 12 : 7)} y2={lineY + (whole ? 12 : 7)} stroke="var(--ink-2)" strokeWidth={whole ? 2.5 : 1.3} />
                {whole ? (
                  <text x={x} y={lineY + 32} textAnchor="middle" fontSize="16" fontWeight="700" fill="var(--ink)">
                    {k / d}
                  </text>
                ) : (
                  labelTicks && (
                    <text x={x} y={lineY + 28} textAnchor="middle" fontSize="12" fill="var(--muted)">
                      {k}/{d}
                    </text>
                  )
                )}
              </g>
            );
          })}
          {groups.map((g, gi) => {
            const x = xOf(valueOf(g.v));
            const y = 40 + rows[gi] * 22;
            const color = COLORS[g.colorIdx % COLORS.length];
            return (
              <g key={gi} className="animate-float-up">
                <line x1={x} x2={x} y1={y + 4} y2={lineY - 6} stroke={color} strokeWidth="1.5" strokeDasharray="3 3" />
                <circle cx={x} cy={lineY} r="7" fill={color} stroke="var(--card)" strokeWidth="2" />
                <text x={x} y={y} textAnchor="middle" fontSize="14" fontWeight="700" fill="var(--ink)">
                  {g.labels.join(" = ")}
                </text>
              </g>
            );
          })}
        </svg>
      </div>

      <div className="mt-3 grid gap-4 md:grid-cols-2">
        <label className="block text-sm font-semibold text-ink-2">
          <span className="flex items-center justify-between">
            {t("w.fractions.line.ticks")}
            <span className="font-mono text-ink">{n(d)}</span>
          </span>
          <input type="range" min={1} max={maxDen} value={d} onChange={(e) => setD(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--sky)]" dir="ltr" />
        </label>
        <form
          className="flex flex-wrap items-end gap-2"
          onSubmit={(e) => {
            e.preventDefault();
            place();
          }}
        >
          <label className="min-w-0 flex-1 text-sm font-semibold text-ink-2">
            {t("w.fractions.line.addLabel")}
            <input value={draft} onChange={(e) => setDraft(e.target.value)} placeholder={t("w.fractions.line.placeholder")} className="input mt-1 py-1.5 font-mono" dir="ltr" aria-invalid={error ? true : undefined} />
          </label>
          <button type="submit" className="btn btn-primary btn-sm h-9" disabled={draft.trim() === ""}>
            {t("w.fractions.line.place")}
          </button>
        </form>
      </div>
      {error && (
        <p className="mt-2 text-sm text-bad" role="alert">
          {error}
        </p>
      )}
      {points.length > 0 && (
        <ul className="list-none ps-0 [&>li]:m-0 mt-3 flex flex-wrap gap-1.5">
          {points.map((p, i) => (
            <li key={`${p.label}-${i}`} className="chip">
              <span className="h-2.5 w-2.5 rounded-full" style={{ background: COLORS[i % COLORS.length] }} aria-hidden="true" />
              <span dir="ltr" className="font-mono">
                {p.label}
              </span>
              <button type="button" className="-me-1 rounded-full p-0.5 hover:bg-line" aria-label={t("w.fractions.line.remove", { s: p.label })} onClick={() => setPoints((prev) => prev.filter((_, k) => k !== i))}>
                <X size={12} aria-hidden="true" />
              </button>
            </li>
          ))}
        </ul>
      )}
      <div className="mt-4 rounded-2xl bg-paper-2 px-5 py-4" aria-live="polite">
        <p className="text-sm font-semibold text-ink-2">{t("w.fractions.line.order")}</p>
        <p className="mt-1 font-serif text-xl text-ink" dir="ltr">
          {chain || "—"}
        </p>
        <p className="mt-2 text-[0.95rem] text-ink">{t("w.fractions.line.hint", { d: n(d) })}</p>
        {groups.length > 0 && (
          <p className="mt-1 font-mono text-sm text-ink-2" dir="ltr">
            {groups.map((g) => [...new Set([...g.labels, fracText(reduce(g.v)), decimalText(g.v) ?? ""].filter(Boolean))].join(" = ")).join("   ·   ")}
          </p>
        )}
      </div>
    </div>
  );
}

