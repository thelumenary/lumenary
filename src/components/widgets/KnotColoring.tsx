"use client";

import { Check, Lightbulb, RotateCcw, X } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { KNOT_IDS, KNOT_INFO, allColourings, checkColouring, getDiagram, isKnotId, linkingNumber, type Colour, type KnotId } from "./lib/topo-knots";
import { r2, type V2 } from "./lib/topo-vec";

const COLOURS: Record<1 | 2 | 3, string> = { 1: "var(--human)", 2: "var(--formal)", 3: "var(--compute)" };
const next = (c: Colour): Colour => (c === 0 || c === 3 ? 1 : ((c + 1) as Colour));

/** A shape for each colour, so the colouring never relies on colour alone. */
function Glyph({ c, x, y, r }: { c: Colour; x: number; y: number; r: number }) {
  if (c === 0)
    return (
      <text x={x} y={y + 4} textAnchor="middle" fontSize={r * 1.2} fontWeight={800} fill="var(--muted)">
        ?
      </text>
    );
  const k = r * 0.5;
  if (c === 1) return <circle cx={x} cy={y} r={k} fill="var(--card)" />;
  if (c === 2) return <path d={`M${r2(x)} ${r2(y - k * 1.1)}L${r2(x + k)} ${r2(y + k * 0.75)}L${r2(x - k)} ${r2(y + k * 0.75)}Z`} fill="var(--card)" />;
  return <rect x={x - k * 0.85} y={y - k * 0.85} width={k * 1.7} height={k * 1.7} fill="var(--card)" />;
}

export interface KnotColoringProps {
  knot?: KnotId;
  knots?: KnotId[];
  title?: string;
  subtitle?: string;
}

/**
 * Tricolouring knot diagrams: click arcs to colour them; at every crossing the
 * three arcs must be all the same colour or all different. Tricolourability is
 * a knot invariant — it shows the trefoil is knotted, but cannot see that the
 * figure-eight knot is.
 */
export function KnotColoring({ knot, knots, title, subtitle }: KnotColoringProps) {
  const { t, n } = useI18n();
  const allowed = useMemo<KnotId[]>(() => {
    const list = Array.isArray(knots) ? KNOT_IDS.filter((k) => knots.includes(k)) : [];
    return list.length ? list : [...KNOT_IDS];
  }, [knots]);
  const [id, setId] = useState<KnotId>(isKnotId(knot) && allowed.includes(knot) ? knot : allowed.includes("trefoil") ? "trefoil" : allowed[0]);
  const [colours, setColours] = useState<Colour[]>([]);
  const [searched, setSearched] = useState(false);
  const d = getDiagram(id);
  const info = KNOT_INFO[id];
  const cols = d.arcs.map((_, i) => colours[i] ?? 0);
  const check = checkColouring(d, cols);
  const all = useMemo(() => allColourings(getDiagram(id)), [id]);
  const nontrivial = all.filter((c) => new Set(c).size >= 2);
  const lk = info.components > 1 ? Math.abs(linkingNumber(d)) : null;
  const centre: V2 = [d.size / 2, d.size / 2];

  const choose = (k: KnotId) => {
    setId(k);
    setColours([]);
    setSearched(false);
  };
  const setArc = (i: number, c: Colour) => setColours(() => d.arcs.map((_, j) => (j === i ? c : (cols[j] ?? 0))));

  let status: string;
  if (check.valid) status = check.nontrivial ? t("w.knot.status.valid", { k: n(check.used) }) : t("w.knot.status.trivial");
  else if (check.bad > 0) status = t("w.knot.status.bad", { k: n(check.bad) });
  else status = t("w.knot.status.incomplete", { k: n(cols.filter((c) => c > 0).length), total: n(d.arcs.length) });

  return (
    <WidgetFrame title={title ?? t("w.knot.title")} subtitle={subtitle ?? t("w.knot.subtitle")}>
      {allowed.length > 1 && (
        <div className="flex flex-wrap gap-1.5" role="group" aria-label={t("w.knot.choose")}>
          {allowed.map((k) => (
            <button key={k} type="button" aria-pressed={id === k} className={`btn btn-sm ${id === k ? "btn-primary" : "btn-ghost"}`} onClick={() => choose(k)}>
              {t(`w.knot.name.${k}`)}
            </button>
          ))}
        </div>
      )}
      <div className="mt-4 grid gap-5 md:grid-cols-[1.1fr_1fr]">
        <div>
          <div dir="ltr" className="mx-auto max-w-[400px] rounded-2xl border border-line bg-paper-2/60">
            <svg viewBox={`0 0 ${d.size} ${d.size}`} className="w-full select-none" role="group" aria-label={t("w.knot.diagram", { name: t(`w.knot.name.${id}`), arcs: n(d.arcs.length), crossings: n(d.crossings.length) })}>
              {d.arcs.map((arc, i) => {
                const c = cols[i];
                const pathD = arc.points.map((p, j) => `${j ? "L" : "M"}${r2(p[0])} ${r2(p[1])}`).join("");
                return (
                  <g
                    key={i}
                    role="button"
                    tabIndex={0}
                    aria-label={t("w.knot.arc", { k: n(i + 1), colour: c ? t(`w.knot.colour.${c}`) : t("w.knot.colour.none") })}
                    className="group cursor-pointer outline-none"
                    onClick={() => setArc(i, next(c))}
                    onKeyDown={(e) => {
                      if (e.key === "Enter" || e.key === " ") {
                        e.preventDefault();
                        setArc(i, next(c));
                      } else if (e.key === "1" || e.key === "2" || e.key === "3") {
                        e.preventDefault();
                        setArc(i, Number(e.key) as Colour);
                      } else if (e.key === "0" || e.key === "Backspace" || e.key === "Delete") {
                        e.preventDefault();
                        setArc(i, 0);
                      }
                    }}
                  >
                    <path d={pathD} fill="none" stroke="var(--sky)" strokeWidth={16} strokeLinecap="round" strokeLinejoin="round" className="opacity-0 transition-opacity group-hover:opacity-20 group-focus-visible:opacity-45" />
                    <path d={pathD} fill="none" stroke="transparent" strokeWidth={22} strokeLinecap="round" />
                    <path d={pathD} fill="none" stroke={c ? COLOURS[c] : "var(--ink-2)"} strokeWidth={7} strokeLinecap="round" strokeLinejoin="round" style={{ transition: "stroke .2s" }} />
                    <circle cx={r2(arc.label[0])} cy={r2(arc.label[1])} r={10.5} fill={c ? COLOURS[c] : "var(--card)"} stroke={c ? "var(--card)" : "var(--ink-2)"} strokeWidth={2} />
                    <Glyph c={c} x={r2(arc.label[0])} y={r2(arc.label[1])} r={10.5} />
                  </g>
                );
              })}
              {d.crossings.map((cr, i) => {
                const st = check.states[i];
                if (st === "pending") return null;
                const dir: V2 = [cr.p[0] - centre[0], cr.p[1] - centre[1]];
                const L = Math.hypot(dir[0], dir[1]) || 1;
                const off = 21;
                const x = r2(cr.p[0] + (dir[0] / L) * off);
                const y = r2(cr.p[1] + (dir[1] / L) * off);
                return (
                  <g key={`c${i}`} aria-hidden="true">
                    <circle cx={x} cy={y} r={8.5} fill={st === "ok" ? "var(--good)" : "var(--bad)"} stroke="var(--card)" strokeWidth={2} />
                    {st === "ok" ? (
                      <path d={`M${x - 4} ${y}l3 3l5 -6`} fill="none" stroke="var(--card)" strokeWidth={2.2} strokeLinecap="round" strokeLinejoin="round" />
                    ) : (
                      <path d={`M${x - 3.5} ${y - 3.5}l7 7M${x + 3.5} ${y - 3.5}l-7 7`} stroke="var(--card)" strokeWidth={2.2} strokeLinecap="round" />
                    )}
                  </g>
                );
              })}
            </svg>
          </div>
          <p className="mt-2 text-xs text-muted">{t("w.knot.howTo")}</p>
          <div className="mt-2 flex flex-wrap items-center gap-3 text-xs text-ink-2">
            {([1, 2, 3] as const).map((c) => (
              <span key={c} className="flex items-center gap-1.5">
                <svg viewBox="0 0 24 24" className="h-5 w-5" aria-hidden="true">
                  <circle cx={12} cy={12} r={10} fill={COLOURS[c]} />
                  <Glyph c={c} x={12} y={12} r={10} />
                </svg>
                {t(`w.knot.colour.${c}`)}
              </span>
            ))}
          </div>
          <div className="mt-3 flex flex-wrap gap-2">
            <button
              type="button"
              className="btn btn-sm btn-ghost"
              onClick={() => {
                setSearched(true);
                if (nontrivial.length) setColours(nontrivial[0]);
              }}
            >
              <Lightbulb size={14} aria-hidden="true" /> {t("w.knot.search")}
            </button>
            <button
              type="button"
              className="btn btn-sm btn-ghost"
              disabled={cols.every((c) => c === 0)}
              onClick={() => {
                setColours([]);
                setSearched(false);
              }}
            >
              <RotateCcw size={14} aria-hidden="true" /> {t("w.common.reset")}
            </button>
          </div>
        </div>

        <div className="space-y-3">
          <div className="flex flex-wrap items-center gap-2">
            <span className="font-semibold text-ink">{t(`w.knot.name.${id}`)}</span>
            <span className="chip font-serif">{info.notation}</span>
          </div>
          <dl className="grid grid-cols-2 gap-2 text-center">
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.knot.inDiagram")}</dt>
              <dd className="font-mono text-lg text-ink">{n(d.crossings.length)}</dd>
            </div>
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.knot.crossingNumber")}</dt>
              <dd className="font-mono text-lg text-ink">{n(info.crossingNumber)}</dd>
            </div>
            {lk !== null && (
              <div className="col-span-2 rounded-xl bg-paper-2 px-2 py-2">
                <dt className="text-xs font-semibold text-ink-2">{t("w.knot.linking")}</dt>
                <dd className="font-mono text-lg text-ink" dir="ltr">
                  ±{lk}
                </dd>
              </div>
            )}
          </dl>
          <div aria-live="polite" className={`flex items-start gap-2 rounded-xl px-4 py-3 text-sm ${check.nontrivial ? "bg-good-soft" : check.bad ? "bg-bad-soft" : "bg-paper-2"}`}>
            {check.nontrivial ? <Check size={16} className="mt-0.5 shrink-0 text-good" aria-hidden="true" /> : check.bad ? <X size={16} className="mt-0.5 shrink-0 text-bad" aria-hidden="true" /> : null}
            <div>
              <p className="font-semibold text-ink">{status}</p>
              {searched && (
                <p className="mt-1 text-ink-2">
                  {t("w.knot.searchResult", { total: n(3 ** d.arcs.length), valid: n(all.length), trivial: n(all.length - nontrivial.length) })}{" "}
                  {nontrivial.length ? t("w.knot.searchYes") : t("w.knot.searchNo")}
                </p>
              )}
            </div>
          </div>
          <p className="text-sm text-ink-2">{t("w.knot.rule")}</p>
          <p className="text-sm text-ink-2">{t(`w.knot.about.${id}`)}</p>
          <p className="rounded-xl bg-gold-soft px-4 py-3 text-sm text-ink">{t("w.knot.invariant")}</p>
        </div>
      </div>
    </WidgetFrame>
  );
}
