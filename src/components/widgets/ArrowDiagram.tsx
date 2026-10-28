"use client";

import { Check, RotateCcw, X } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";

type Arrow = [number, number];

const DOMAIN_LABELS = ["1", "2", "3", "4"];
const CODOMAIN_LABELS = ["a", "b", "c", "d"];

const PRESETS: { id: string; m: number; n: number; arrows: Arrow[] }[] = [
  { id: "bijection", m: 3, n: 3, arrows: [[0, 1], [1, 2], [2, 0]] },
  { id: "notInjective", m: 3, n: 3, arrows: [[0, 0], [1, 0], [2, 2]] },
  { id: "notFunction", m: 3, n: 3, arrows: [[0, 0], [0, 1], [2, 2]] },
  { id: "pigeonhole", m: 4, n: 3, arrows: [[0, 0], [1, 1], [2, 2], [3, 0]] },
];

/** Analyse a relation between {0..m-1} and {0..n-1} given as arrows. */
export function analyse(m: number, n: number, arrows: Arrow[]) {
  const outs = Array.from({ length: m }, (_, i) => arrows.filter(([a]) => a === i).map(([, b]) => b));
  const ins = Array.from({ length: n }, (_, j) => arrows.filter(([, b]) => b === j).map(([a]) => a));
  const missing = outs.map((o, i) => (o.length === 0 ? i : -1)).filter((i) => i >= 0);
  const multiple = outs.map((o, i) => (o.length > 1 ? i : -1)).filter((i) => i >= 0);
  const isFunction = missing.length === 0 && multiple.length === 0;
  const collisions = ins.map((s, j) => (s.length > 1 ? j : -1)).filter((j) => j >= 0);
  const unreached = ins.map((s, j) => (s.length === 0 ? j : -1)).filter((j) => j >= 0);
  return { isFunction, missing, multiple, injective: isFunction && collisions.length === 0, surjective: isFunction && unreached.length === 0, collisions, unreached };
}

export function ArrowDiagram() {
  const { t } = useI18n();
  const [m, setM] = useState(3);
  const [n, setN] = useState(3);
  const [arrows, setArrows] = useState<Arrow[]>([[0, 1], [1, 2], [2, 0]]);
  const [from, setFrom] = useState<number | null>(null);
  const info = useMemo(() => analyse(m, n, arrows), [m, n, arrows]);

  const spread = (k: number, count: number) => (count === 1 ? 172 : 62 + (k * 220) / (count - 1));
  const yA = (i: number) => spread(i, m);
  const yB = (j: number) => spread(j, n);
  const XA = 90;
  const XB = 330;

  const clickA = (i: number) => setFrom(from === i ? null : i);
  const clickB = (j: number) => {
    if (from === null) return;
    setArrows((prev) => (prev.some(([a, b]) => a === from && b === j) ? prev.filter(([a, b]) => !(a === from && b === j)) : [...prev, [from, j]]));
    setFrom(null);
  };
  const resize = (nm: number, nn: number) => {
    setM(nm);
    setN(nn);
    setArrows((prev) => prev.filter(([a, b]) => a < nm && b < nn));
    setFrom(null);
  };

  const Verdict = ({ ok, label, why }: { ok: boolean; label: string; why?: string }) => (
    <li className="flex items-start gap-2.5">
      <span className={`mt-0.5 flex h-5 w-5 shrink-0 items-center justify-center rounded-full ${ok ? "bg-good-soft text-good" : "bg-paper-2 text-muted"}`}>{ok ? <Check size={13} /> : <X size={13} />}</span>
      <span>
        <span className={`font-semibold ${ok ? "text-ink" : "text-ink-2"}`}>{label}</span>
        {why && <span className="block text-sm text-muted">{why}</span>}
      </span>
    </li>
  );

  const A = (i: number) => DOMAIN_LABELS[i];
  const B = (j: number) => CODOMAIN_LABELS[j];

  return (
    <WidgetFrame title={t("w.arrow.title")} subtitle={t("w.arrow.subtitle")}>
      <div className="flex flex-wrap items-center gap-2">
        {PRESETS.map((p) => (
          <button
            key={p.id}
            type="button"
            className="btn btn-sm btn-ghost"
            onClick={() => {
              setM(p.m);
              setN(p.n);
              setArrows(p.arrows);
              setFrom(null);
            }}
          >
            {t(`w.arrow.preset.${p.id}`)}
          </button>
        ))}
        <button type="button" className="btn btn-sm btn-ghost ms-auto" onClick={() => setArrows([])}>
          <RotateCcw size={14} aria-hidden="true" /> {t("w.arrow.clear")}
        </button>
      </div>
      <div className="mt-4 grid gap-5 md:grid-cols-[1.2fr_1fr]">
        <div dir="ltr">
          <svg viewBox="0 0 420 324" className="w-full select-none" role="group" aria-label={t("w.arrow.diagram")}>
            <defs>
              <marker id="ad-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
                <path d="M0 0 10 5 0 10z" fill="var(--ink-2)" />
              </marker>
            </defs>
            <ellipse cx={XA} cy={172} rx={62} ry={142} fill="var(--human-soft)" stroke="var(--human)" strokeWidth="1.5" />
            <ellipse cx={XB} cy={172} rx={62} ry={142} fill="var(--formal-soft)" stroke="var(--formal)" strokeWidth="1.5" />
            <text x={XA} y={14} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--human)">
              A · {t("w.arrow.domain")}
            </text>
            <text x={XB} y={14} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--formal)">
              B · {t("w.arrow.codomain")}
            </text>
            {arrows.map(([a, b], k) => {
              const bad = info.multiple.includes(a);
              const collide = info.isFunction && info.collisions.includes(b);
              return (
                <line
                  key={k}
                  x1={XA + 16}
                  y1={yA(a)}
                  x2={XB - 18}
                  y2={yB(b)}
                  stroke={bad ? "var(--bad)" : collide ? "var(--warn)" : "var(--ink-2)"}
                  strokeWidth="2.2"
                  markerEnd="url(#ad-arrow)"
                />
              );
            })}
            {Array.from({ length: m }, (_, i) => (
              <g key={i} role="button" tabIndex={0} aria-label={`${t("w.arrow.element")} ${A(i)}`} aria-pressed={from === i} onClick={() => clickA(i)} onKeyDown={(e) => (e.key === "Enter" || e.key === " ") && (e.preventDefault(), clickA(i))} className="cursor-pointer outline-none [&:focus-visible>circle]:stroke-[var(--sky)]">
                <circle cx={XA} cy={yA(i)} r={15} fill={from === i ? "var(--gold)" : "var(--card)"} stroke={info.missing.includes(i) ? "var(--bad)" : "var(--human)"} strokeWidth={from === i ? 3 : 2} strokeDasharray={info.missing.includes(i) ? "4 3" : undefined} />
                <text x={XA} y={yA(i) + 5} textAnchor="middle" fontSize="15" fontWeight="700" fill="var(--ink)">
                  {A(i)}
                </text>
              </g>
            ))}
            {Array.from({ length: n }, (_, j) => (
              <g key={j} role="button" tabIndex={0} aria-label={`${t("w.arrow.element")} ${B(j)}`} onClick={() => clickB(j)} onKeyDown={(e) => (e.key === "Enter" || e.key === " ") && (e.preventDefault(), clickB(j))} className={`outline-none [&:focus-visible>circle]:stroke-[var(--sky)] ${from !== null ? "cursor-pointer" : ""}`}>
                <circle cx={XB} cy={yB(j)} r={15} fill={from !== null ? "var(--gold-soft)" : "var(--card)"} stroke="var(--formal)" strokeWidth="2" />
                <text x={XB} y={yB(j) + 5} textAnchor="middle" fontSize="15" fontWeight="700" fill="var(--ink)">
                  {B(j)}
                </text>
              </g>
            ))}
          </svg>
          <p className="mt-1 text-center text-xs text-muted">{from === null ? t("w.arrow.howTo") : t("w.arrow.nowPick", { x: A(from) })}</p>
          <div className="mt-3 flex flex-wrap justify-center gap-4 text-sm">
            <label className="flex items-center gap-2">
              |A|
              <select className="input w-auto py-1" value={m} onChange={(e) => resize(Number(e.target.value), n)}>
                {[1, 2, 3, 4].map((v) => (
                  <option key={v}>{v}</option>
                ))}
              </select>
            </label>
            <label className="flex items-center gap-2">
              |B|
              <select className="input w-auto py-1" value={n} onChange={(e) => resize(m, Number(e.target.value))}>
                {[1, 2, 3, 4].map((v) => (
                  <option key={v}>{v}</option>
                ))}
              </select>
            </label>
          </div>
        </div>
        <div aria-live="polite">
          <ul className="space-y-3">
            <Verdict
              ok={info.isFunction}
              label={t("w.arrow.isFunction")}
              why={
                info.isFunction
                  ? t("w.arrow.isFunctionYes")
                  : info.multiple.length
                    ? t("w.arrow.tooMany", { x: A(info.multiple[0]) })
                    : t("w.arrow.noArrow", { x: A(info.missing[0]) })
              }
            />
            <Verdict
              ok={info.injective}
              label={t("w.arrow.injective")}
              why={!info.isFunction ? t("w.arrow.needFunction") : info.injective ? t("w.arrow.injectiveYes") : t("w.arrow.injectiveNo", { y: B(info.collisions[0]) })}
            />
            <Verdict
              ok={info.surjective}
              label={t("w.arrow.surjective")}
              why={!info.isFunction ? t("w.arrow.needFunction") : info.surjective ? t("w.arrow.surjectiveYes") : t("w.arrow.surjectiveNo", { y: B(info.unreached[0]) })}
            />
            <Verdict ok={info.injective && info.surjective} label={t("w.arrow.bijective")} why={info.injective && info.surjective ? t("w.arrow.bijectiveYes") : undefined} />
          </ul>
          {m > n && <p className="mt-4 rounded-xl bg-gold-soft px-4 py-3 text-sm text-ink">{t("w.arrow.pigeonhole", { m, n })}</p>}
        </div>
      </div>
    </WidgetFrame>
  );
}
