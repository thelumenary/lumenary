"use client";

import { Check, Delete, Eye, Plus } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { MAX_CORE, PALETTE, clampCoefficients, differences, formatRule, formatTerm, growLayout, growTerm, parseCore, repeatPosition, type PatternSymbol, type ShapeName } from "./lib/shape-pattern";
import { NAMED_COLOURS, asNumber, oneOf, toInt } from "./lib/shape-util";

export interface PatternMakerProps {
  mode?: "repeat" | "grow";
  core?: string[];
  a?: number;
  b?: number;
  c?: number;
  steps?: number;
  title?: string;
  subtitle?: string;
}

type T = (k: string, v?: Record<string, string | number>) => string;

const LETTERS = "ABCDEF";

/** One pattern symbol in a 24 × 24 box. */
function SymbolShape({ shape, colour }: { shape: ShapeName; colour: string }) {
  switch (shape) {
    case "circle":
      return <circle cx={12} cy={12} r={9} fill={colour} />;
    case "triangle":
      return <path d="M12 2.5 L21.5 20 H2.5 Z" fill={colour} strokeLinejoin="round" />;
    case "square":
      return <rect x={3.5} y={3.5} width={17} height={17} rx={2} fill={colour} />;
    case "star":
      return <path d="M12 1.8l2.9 6.6 7.1.6-5.4 4.7 1.6 7-6.2-3.7-6.2 3.7 1.6-7L2 9l7.1-.6z" fill={colour} />;
    case "heart":
      return <path d="M12 21s-8.5-5.3-8.5-11.2A4.7 4.7 0 0 1 12 6.6a4.7 4.7 0 0 1 8.5 3.2C20.5 15.7 12 21 12 21z" fill={colour} />;
    case "diamond":
    default:
      return <path d="M12 2 L21 12 L12 22 L3 12 Z" fill={colour} />;
  }
}

function Sym({ s, size = 28, label }: { s: PatternSymbol; size?: number; label?: string }) {
  return (
    <svg viewBox="0 0 24 24" width={size} height={size} role={label ? "img" : undefined} aria-label={label} aria-hidden={label ? undefined : true} className="shrink-0">
      <SymbolShape shape={s.shape} colour={NAMED_COLOURS[s.colour]} />
    </svg>
  );
}

const symName = (t: T, s: PatternSymbol) => t("w.pattern.symbolName", { shape: t(`w.pattern.shape.${s.shape}`), colour: t(`w.pattern.colour.${s.colour}`) });

/** Repeating patterns (predict item k with a remainder) and growing tile patterns a·n² + b·n + c. */
export function PatternMaker({ mode, core, a, b, c, steps, title, subtitle }: PatternMakerProps) {
  const { t } = useI18n();
  const [tab, setTab] = useState<"repeat" | "grow">(oneOf(mode, ["repeat", "grow"] as const, "repeat"));
  return (
    <WidgetFrame title={title ?? t("w.pattern.title")} subtitle={subtitle ?? t("w.pattern.subtitle")}>
      <div className="flex flex-wrap gap-2">
        {(["repeat", "grow"] as const).map((m) => (
          <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
            {t(`w.pattern.mode.${m}`)}
          </button>
        ))}
      </div>
      {tab === "repeat" ? (
        <Repeat core0={parseCore(core)} count={toInt(steps, 0, 0, 24)} />
      ) : (
        <Grow {...clampCoefficients(Number.isFinite(asNumber(a)) ? Math.round(asNumber(a)) : 0, Number.isFinite(asNumber(b)) ? Math.round(asNumber(b)) : 2, Number.isFinite(asNumber(c)) ? Math.round(asNumber(c)) : 1)} steps0={toInt(steps, 3, 1, 6)} />
      )}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------- repeat */

function Repeat({ core0, count }: { core0: PatternSymbol[]; count: number }) {
  const { t, n } = useI18n();
  const [core, setCore] = useState(core0);
  const [letters, setLetters] = useState(true);
  const [k, setK] = useState(20);
  const [guess, setGuess] = useState<string | null>(null);
  const [checked, setChecked] = useState<"right" | "wrong" | "pick" | null>(null);
  const [how, setHow] = useState(false);
  const len = core.length;
  const shownCount = count >= 4 ? count : Math.max(12, Math.min(18, len * 4));
  const choices = core.filter((s, i) => core.findIndex((x) => x.id === s.id) === i);
  const { q, r, pos } = repeatPosition(k, len);
  const answer = core[pos - 1];
  // Letters name distinct symbols (ABB means: first symbol, then the second symbol twice).
  const letterOf = (s: PatternSymbol) => LETTERS[choices.findIndex((x) => x.id === s.id)];

  const edit = (next: PatternSymbol[]) => {
    setCore(next);
    setGuess(null);
    setChecked(null);
    setHow(false);
  };
  const setItem = (v: number) => {
    setK(Math.max(1, Math.min(100, Math.round(v) || 1)));
    setChecked(null);
    setHow(false);
  };

  return (
    <div className="mt-4 space-y-5">
      <div>
        <p className="text-sm font-semibold text-ink-2">{t("w.pattern.core")}</p>
        <div className="mt-2 flex flex-wrap items-center gap-3">
          <div className="flex items-center gap-1.5 rounded-xl border-2 border-dashed border-gold bg-gold-soft/60 px-3 py-2" dir="ltr">
            {core.map((s, i) => (
              <div key={i} className="flex flex-col items-center">
                <Sym s={s} label={symName(t, s)} />
                {letters && <span className="font-mono text-xs font-bold text-gold-ink">{letterOf(s)}</span>}
              </div>
            ))}
          </div>
          <button type="button" className="btn btn-sm btn-ghost" disabled={len <= 1} onClick={() => edit(core.slice(0, -1))}>
            <Delete size={14} aria-hidden="true" className="rtl:-scale-x-100" /> {t("w.pattern.removeLast")}
          </button>
          <button type="button" aria-pressed={letters} className={`btn btn-sm ${letters ? "btn-gold" : "btn-ghost"}`} onClick={() => setLetters((v) => !v)}>
            {t("w.pattern.letters")}
          </button>
        </div>
        <div className="mt-3">
          <p className="text-xs text-muted">{len >= MAX_CORE ? t("w.pattern.coreFull", { max: n(MAX_CORE) }) : t("w.pattern.addHint")}</p>
          <div className="mt-1.5 flex flex-wrap gap-1.5">
            {PALETTE.map((s) => (
              <button key={s.id} type="button" disabled={len >= MAX_CORE} className="btn btn-sm btn-ghost !px-2" aria-label={`${t("w.pattern.add")}: ${symName(t, s)}`} onClick={() => edit([...core, s])}>
                <Plus size={12} aria-hidden="true" className="text-muted" />
                <Sym s={s} size={20} />
              </button>
            ))}
          </div>
        </div>
      </div>

      <div>
        <p className="text-sm font-semibold text-ink-2">{t("w.pattern.sequence")}</p>
        <div className="mt-2 overflow-x-auto pb-1">
          <ol className="flex min-w-max gap-1" dir="ltr" aria-label={t("w.pattern.sequence")}>
            {Array.from({ length: shownCount }, (_, i) => {
              const s = core[i % len];
              const unit = Math.floor(i / len);
              return (
                <li key={i} className={`flex flex-col items-center rounded-lg px-1 py-1.5 ${unit % 2 ? "bg-paper-2" : "bg-sky-soft/60"}`} aria-label={t("w.pattern.itemAria", { k: i + 1, name: symName(t, s) })}>
                  <Sym s={s} size={26} />
                  {letters && <span className="font-mono text-[0.65rem] font-bold text-ink-2">{letterOf(s)}</span>}
                  <span className="font-mono text-[0.65rem] text-muted">{i + 1}</span>
                </li>
              );
            })}
            <li className="flex items-center px-2 font-bold text-muted" aria-hidden="true">
              …
            </li>
          </ol>
        </div>
      </div>

      <div className="rounded-xl border border-line p-4">
        <label className="flex flex-wrap items-center gap-3 text-sm font-semibold text-ink-2">
          {t("w.pattern.whichItem")}
          <input type="number" min={1} max={100} value={k} onChange={(e) => setItem(Number(e.target.value))} className="input w-24 py-1.5" dir="ltr" />
        </label>
        <p className="mt-3 text-sm font-semibold text-ink">{t("w.pattern.predict", { k: n(k) })}</p>
        <div role="group" aria-label={t("w.pattern.predict", { k: n(k) })} className="mt-2 flex flex-wrap gap-2">
          {choices.map((s) => (
            <button
              key={s.id}
              type="button"
              aria-pressed={guess === s.id}
              aria-label={symName(t, s)}
              className={`flex h-12 w-12 items-center justify-center rounded-xl border-2 transition-colors ${guess === s.id ? "border-ink bg-paper-2" : "border-line bg-card hover:bg-paper-2"}`}
              onClick={() => {
                setGuess(s.id);
                setChecked(null);
              }}
            >
              <Sym s={s} size={30} />
            </button>
          ))}
        </div>
        <div className="mt-3 flex flex-wrap gap-2">
          <button type="button" className="btn btn-sm btn-primary" onClick={() => setChecked(guess === null ? "pick" : guess === answer.id ? "right" : "wrong")}>
            <Check size={14} aria-hidden="true" /> {t("w.pattern.check")}
          </button>
          <button type="button" aria-pressed={how} className={`btn btn-sm ${how ? "btn-gold" : "btn-ghost"}`} onClick={() => setHow((v) => !v)}>
            <Eye size={14} aria-hidden="true" /> {t("w.pattern.showHow")}
          </button>
        </div>
        <div aria-live="polite" className="mt-3 space-y-2 text-sm">
          {checked && <p className={`rounded-lg px-3 py-2 ${checked === "right" ? "bg-good-soft text-ink" : checked === "pick" ? "bg-paper-2 text-ink-2" : "bg-warn-soft text-ink"}`}>{checked === "right" ? t("w.pattern.fb.right", { k: n(k), name: symName(t, answer) }) : checked === "pick" ? t("w.pattern.fb.pick") : t("w.pattern.fb.wrong")}</p>}
          {how && (
            <div className="rounded-lg bg-gold-soft px-3 py-2 text-ink">
              <p>{t("w.pattern.how", { len: n(len) })}</p>
              <p className="my-1 font-serif text-lg" dir="ltr">
                {k} ÷ {len} = {q} r {r}
              </p>
              <p className="flex flex-wrap items-center gap-2">
                {r === 0 ? t("w.pattern.howZero", { k: n(k) }) : t("w.pattern.howPos", { k: n(k), pos: n(pos) })} <Sym s={answer} size={22} label={symName(t, answer)} />
              </p>
            </div>
          )}
        </div>
      </div>
    </div>
  );
}

/* ---------------------------------------------------------------- grow */

const PART_FILL = { square: "var(--gold)", column: "var(--sky)", single: "var(--human)" } as const;

function Figure({ a, b, c, step, tile }: { a: number; b: number; c: number; step: number; tile: number }) {
  const { t } = useI18n();
  const lay = growLayout(a, b, c, step);
  if (!lay) return null;
  const w = lay.width * tile;
  const h = lay.height * tile;
  return (
    <figure className="flex shrink-0 flex-col items-center justify-end gap-1.5">
      <svg viewBox={`-2 -2 ${w + 4} ${h + 4}`} width={w + 4} height={h + 4} role="img" aria-label={t("w.pattern.figureAria", { n: step, v: growTerm(a, b, c, step) })}>
        {lay.tiles.map((tl, i) => (
          <rect
            key={i}
            x={tl.x * tile + 1}
            y={(lay.height - 1 - tl.y) * tile + 1}
            width={tile - 2}
            height={tile - 2}
            rx={2}
            fill={tl.removed ? "none" : PART_FILL[tl.part]}
            stroke={tl.removed ? "var(--muted)" : "none"}
            strokeDasharray={tl.removed ? "3 2" : undefined}
            strokeWidth="1.2"
          />
        ))}
      </svg>
      <figcaption className="text-xs font-semibold text-ink-2">{t("w.pattern.step", { n: step })}</figcaption>
    </figure>
  );
}

function Grow({ a, b, c, steps0 }: { a: number; b: number; c: number; steps0: number }) {
  const { t, n } = useI18n();
  const [shown, setShown] = useState(steps0);
  const [askStep, setAskStep] = useState(10);
  const [answer, setAnswer] = useState("");
  const [fb, setFb] = useState<"right" | "wrong" | "negative" | null>(null);
  const [rule, setRule] = useState(false);

  const LIMIT = 160;
  const negativeAt = useMemo(() => Array.from({ length: 8 }, (_, i) => i + 1).find((k) => growTerm(a, b, c, k) < 0), [a, b, c]);
  let maxDrawable = 6;
  while (maxDrawable > 1 && growTerm(a, b, c, maxDrawable) + Math.max(0, -a) * maxDrawable ** 2 + Math.max(0, -b) * maxDrawable + Math.max(0, -c) > LIMIT) maxDrawable--;
  const visible = Math.min(shown, maxDrawable);
  const seq = Array.from({ length: visible }, (_, i) => growTerm(a, b, c, i + 1));
  const d1 = differences(seq);
  const d2 = differences(d1);
  const widest = Math.max(...Array.from({ length: visible }, (_, i) => growLayout(a, b, c, i + 1)?.width ?? 1));
  const totalWidth = Array.from({ length: visible }, (_, i) => growLayout(a, b, c, i + 1)?.width ?? 1).reduce((s, w) => s + w, 0);
  const tile = Math.max(9, Math.min(22, Math.floor(560 / Math.max(totalWidth + visible * 2, widest))));

  if (negativeAt !== undefined && negativeAt <= Math.max(shown, 1)) {
    return <p className="mt-4 rounded-xl bg-bad-soft px-4 py-3 text-sm text-ink">{t("w.pattern.error.negative", { n: n(negativeAt) })}</p>;
  }

  const legend = [
    { part: "square" as const, coef: a, label: t("w.pattern.part.square"), term: formatTerm(a, "n²") },
    { part: "column" as const, coef: b, label: t("w.pattern.part.column"), term: formatTerm(b, "n") },
    { part: "single" as const, coef: c, label: t("w.pattern.part.single"), term: formatTerm(c, "") },
  ].filter((x) => x.coef !== 0);
  const target = growTerm(a, b, c, askStep);

  return (
    <div className="mt-4 space-y-5">
      <div className="overflow-x-auto rounded-xl bg-paper-2/60 px-3 py-4">
        <div className="flex min-w-max items-end gap-6" dir="ltr">
          {Array.from({ length: visible }, (_, i) => (
            <Figure key={i} a={a} b={b} c={c} step={i + 1} tile={tile} />
          ))}
          <div className="flex h-16 w-14 shrink-0 flex-col items-center justify-center rounded-xl border-2 border-dashed border-line-2 text-xl font-bold text-muted" aria-hidden="true">
            ?
          </div>
        </div>
      </div>
      <div className="flex flex-wrap items-center gap-2">
        <button type="button" className="btn btn-sm btn-ghost" disabled={visible >= maxDrawable || (negativeAt !== undefined && negativeAt <= shown + 1)} onClick={() => setShown((s) => s + 1)}>
          <Plus size={14} aria-hidden="true" /> {t("w.pattern.showNext")}
        </button>
        {shown > maxDrawable && <span className="text-xs text-muted">{t("w.pattern.error.tooMany", { k: n(maxDrawable) })}</span>}
      </div>

      <div className="overflow-x-auto">
        <table className="text-center text-sm" dir="ltr">
          <tbody>
            <tr>
              <th scope="row" className="pe-3 text-start text-xs font-semibold text-muted">
                {t("w.pattern.stepRow")}
              </th>
              {seq.map((_, i) => (
                <td key={i} className="w-12 border-b border-line py-1.5 font-mono text-ink-2">
                  {i + 1}
                </td>
              ))}
              <td className="w-14 border-b border-line py-1.5 font-mono text-muted">{askStep}</td>
            </tr>
            <tr>
              <th scope="row" className="pe-3 text-start text-xs font-semibold text-muted">
                {t("w.pattern.tilesRow")}
              </th>
              {seq.map((v, i) => (
                <td key={i} className="py-1.5 font-mono text-base font-bold text-ink">
                  {v}
                </td>
              ))}
              <td className="py-1.5 font-mono text-base font-bold text-muted">{(fb === "right" || rule) && target >= 0 ? target : "?"}</td>
            </tr>
            {d1.length > 0 && (
              <tr>
                <th scope="row" className="pe-3 text-start text-xs font-semibold text-muted">
                  {t("w.pattern.changeRow")}
                </th>
                <td />
                {d1.map((v, i) => (
                  <td key={i} className="py-1 font-mono text-xs text-gold-ink">
                    {v >= 0 ? `+${v}` : `−${-v}`}
                  </td>
                ))}
              </tr>
            )}
          </tbody>
        </table>
      </div>

      <form
        className="flex flex-wrap items-end gap-3 rounded-xl border border-line p-4"
        onSubmit={(e) => {
          e.preventDefault();
          if (answer.trim() === "") return;
          setFb(target < 0 ? "negative" : Number(answer) === target ? "right" : "wrong");
        }}
      >
        <label className="text-sm font-semibold text-ink-2">
          {t("w.pattern.stepNumber")}
          <input
            type="number"
            min={1}
            max={50}
            value={askStep}
            onChange={(e) => {
              setAskStep(Math.max(1, Math.min(50, Math.round(Number(e.target.value)) || 1)));
              setFb(null);
            }}
            className="input mt-1.5 block w-20 py-1.5"
            dir="ltr"
          />
        </label>
        <label className="text-sm font-semibold text-ink-2">
          {t("w.pattern.predictGrow", { k: n(askStep) })}
          <input type="number" value={answer} onChange={(e) => setAnswer(e.target.value)} className="input mt-1.5 block w-28 py-1.5" dir="ltr" />
        </label>
        <button type="submit" className="btn btn-sm btn-primary">
          <Check size={14} aria-hidden="true" /> {t("w.pattern.check")}
        </button>
        <button type="button" aria-pressed={rule} className={`btn btn-sm ${rule ? "btn-gold" : "btn-ghost"}`} onClick={() => setRule((v) => !v)}>
          <Eye size={14} aria-hidden="true" /> {t("w.pattern.revealRule")}
        </button>
      </form>

      <div aria-live="polite" className="space-y-3 text-sm">
        {fb && (
          <p className={`rounded-lg px-3 py-2 ${fb === "right" ? "bg-good-soft" : "bg-warn-soft"} text-ink`}>
            {fb === "right" ? t("w.pattern.fbGrow.right", { k: n(askStep), v: n(target) }) : fb === "negative" ? t("w.pattern.error.negative", { n: n(askStep) }) : t("w.pattern.fbGrow.wrong")}
          </p>
        )}
        {rule && (
          <div className="rounded-xl bg-gold-soft px-4 py-3 text-ink">
            <p>{t("w.pattern.rule")}</p>
            <p className="my-1 font-serif text-2xl" dir="ltr">
              {formatRule(a, b, c)}
            </p>
            <ul className="mt-2 space-y-1">
              {legend.map((x) => (
                <li key={x.part} className="flex items-center gap-2">
                  {x.coef > 0 ? (
                    <span className="inline-block h-3.5 w-3.5 rounded-sm" style={{ background: PART_FILL[x.part] }} aria-hidden="true" />
                  ) : (
                    <span className="inline-block h-3.5 w-3.5 rounded-sm border border-dashed border-muted" aria-hidden="true" />
                  )}
                  <span>{x.coef > 0 ? x.label : t("w.pattern.part.takenAway", { part: x.label })}</span>
                  <span className="font-serif font-semibold" dir="ltr">
                    {x.term}
                  </span>
                </li>
              ))}
            </ul>
            {d1.length >= 2 && <p className="mt-2 text-ink-2">{a !== 0 && d2.length > 0 ? t("w.pattern.secondDiff", { d: n(d2[0]) }) : t("w.pattern.firstDiff", { d: n(d1[0]) })}</p>}
          </div>
        )}
      </div>
    </div>
  );
}
