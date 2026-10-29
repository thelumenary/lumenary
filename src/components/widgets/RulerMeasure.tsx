"use client";

import { ArrowLeft, ArrowRight, Check, ChevronsRight, Eye, Hand, Paperclip } from "lucide-react";
import { useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { OBJECT_IDS, OBJECTS, RULER_CM, UNIT_IDS, UNITS, clampStart, fitWords, judge, type ObjectId, type UnitId, type Verdict } from "./lib/shape-ruler";
import { oneOf, toInt } from "./lib/shape-util";

export interface RulerMeasureProps {
  units?: "cm" | "clips" | "both";
  object?: ObjectId;
  objects?: ObjectId[];
  start?: number;
  title?: string;
  subtitle?: string;
}

const PX = 24;
const RX0 = 16;
const X0 = RX0 + 0.75 * PX;
const OBJ_Y = 50;

/** A simple drawing of an object exactly `len` px long, from x = 0 to x = len, centred on y = 0. */
function ObjectShape({ id, len }: { id: ObjectId; len: number }) {
  switch (id) {
    case "pencil": {
      const body = len * 0.8;
      return (
        <g strokeLinejoin="round">
          <rect x={0} y={-8} width={len * 0.07} height={16} rx={3} fill="var(--human)" />
          <rect x={len * 0.07} y={-8} width={len * 0.06} height={16} fill="var(--line-2)" stroke="var(--muted)" strokeWidth="1" />
          <rect x={len * 0.13} y={-8} width={body - len * 0.13} height={16} fill="var(--gold)" stroke="var(--gold-ink)" strokeWidth="1.2" />
          <line x1={len * 0.13} y1={0} x2={body} y2={0} stroke="var(--gold-ink)" strokeWidth="0.8" opacity="0.6" />
          <path d={`M${body} -8 L${len} 0 L${body} 8 Z`} fill="var(--gold-soft)" stroke="var(--gold-ink)" strokeWidth="1.2" />
          <path d={`M${len - (len - body) * 0.32} -2.6 L${len} 0 L${len - (len - body) * 0.32} 2.6 Z`} fill="var(--ink)" />
        </g>
      );
    }
    case "crayon":
      return (
        <g strokeLinejoin="round">
          <rect x={0} y={-9} width={len * 0.82} height={18} rx={3} fill="var(--formal)" />
          <rect x={len * 0.18} y={-9} width={len * 0.46} height={18} fill="var(--formal-soft)" stroke="var(--formal)" strokeWidth="1.2" />
          <path d={`M${len * 0.82} -7 L${len} -2.5 L${len} 2.5 L${len * 0.82} 7 Z`} fill="var(--formal)" />
        </g>
      );
    case "key": {
      const bow = Math.min(15, len * 0.2);
      return (
        <g fill="var(--gold-ink)">
          <circle cx={bow} cy={0} r={bow} />
          <circle cx={bow * 0.85} cy={0} r={bow * 0.42} fill="var(--card)" />
          <rect x={bow * 1.8} y={-3.5} width={len - bow * 1.8} height={7} rx={1.5} />
          <path d={`M${len - len * 0.28} 3 h${len * 0.07} v7 h${len * 0.06} v-4 h${len * 0.06} v6 h${len * 0.09} V3 Z`} />
        </g>
      );
    }
    case "leaf": {
      const stem = len * 0.16;
      return (
        <g>
          <line x1={0} y1={0} x2={stem + 4} y2={0} stroke="var(--good)" strokeWidth="2.4" strokeLinecap="round" />
          <path d={`M${stem} 0 C${stem + (len - stem) * 0.3} -20 ${stem + (len - stem) * 0.75} -16 ${len} 0 C${stem + (len - stem) * 0.75} 16 ${stem + (len - stem) * 0.3} 20 ${stem} 0 Z`} fill="var(--good-soft)" stroke="var(--good)" strokeWidth="1.8" />
          <path d={`M${stem} 0 L${len - 3} 0`} stroke="var(--good)" strokeWidth="1.2" />
          {[0.35, 0.55, 0.75].map((f) => (
            <path key={f} d={`M${stem + (len - stem) * f} 0 l${len * 0.07} -7 M${stem + (len - stem) * f} 0 l${len * 0.07} 7`} stroke="var(--good)" strokeWidth="1" fill="none" />
          ))}
        </g>
      );
    }
    case "spoon": {
      const bowl = len * 0.3;
      return (
        <g fill="var(--line-2)" stroke="var(--muted)" strokeWidth="1.2">
          <path d={`M0 -3.5 Q${len * 0.35} -2.5 ${len - bowl} -2 L${len - bowl} 2 Q${len * 0.35} 2.5 0 3.5 Q-1 0 0 -3.5 Z`} />
          <ellipse cx={len - bowl / 2} cy={0} rx={bowl / 2} ry={Math.min(11, bowl * 0.38)} />
        </g>
      );
    }
    case "feather":
    default:
      return (
        <g>
          <path d={`M${len * 0.12} 0 C${len * 0.3} -18 ${len * 0.75} -16 ${len} -1 C${len * 0.72} 12 ${len * 0.32} 15 ${len * 0.12} 0 Z`} fill="var(--sky-soft)" stroke="var(--sky)" strokeWidth="1.5" />
          <path d={`M0 1.5 Q${len * 0.5} 0 ${len} -1`} stroke="var(--sky-ink)" strokeWidth="1.8" fill="none" strokeLinecap="round" />
          {[0.3, 0.45, 0.6, 0.75].map((f) => (
            <path key={f} d={`M${len * f} 0.5 l${len * 0.08} -9 M${len * f} 0.5 l${len * 0.08} 8`} stroke="var(--sky)" strokeWidth="0.9" fill="none" />
          ))}
        </g>
      );
  }
}

/** A non-standard unit drawn `len` px long. */
function UnitShape({ id, len }: { id: UnitId; len: number }) {
  if (id === "smallClip" || id === "bigClip") {
    return (
      <g fill="none" stroke="var(--compute)" strokeWidth="2">
        <rect x={1.5} y={-6} width={len - 3} height={12} rx={6} />
        <path d={`M${len * 0.82} -3 H${len * 0.2} a3 3 0 0 0 0 6 H${len * 0.7}`} strokeWidth="1.6" />
      </g>
    );
  }
  return (
    <g>
      <rect x={1.5} y={-10} width={len - 3} height={20} rx={10} fill="var(--human-soft)" stroke="var(--human)" strokeWidth="1.8" />
      <circle cx={10} cy={0} r={4.5} fill="var(--human)" />
      <circle cx={len - 10} cy={0} r={4.5} fill="var(--human)" />
      <line x1={18} y1={0} x2={len - 18} y2={0} stroke="var(--human)" strokeWidth="1.2" strokeDasharray="4 4" />
    </g>
  );
}

/**
 * Measuring length with a centimetre ruler (and the "start at zero" misconception)
 * or with non-standard units, to see why standard units matter.
 */
export function RulerMeasure({ units, object, objects, start, title, subtitle }: RulerMeasureProps) {
  const { t } = useI18n();
  const which = oneOf(units, ["cm", "clips", "both"] as const, "cm");
  const list = Array.isArray(objects) ? OBJECT_IDS.filter((o) => objects.includes(o)) : OBJECT_IDS;
  const offered = list.length ? list : OBJECT_IDS;
  const [obj, setObj] = useState<ObjectId>(oneOf(object, offered, offered.includes("pencil") ? "pencil" : offered[0]));
  const [view, setView] = useState<"cm" | "clips">(which === "clips" ? "clips" : "cm");

  return (
    <WidgetFrame title={title ?? t("w.ruler.title")} subtitle={subtitle ?? t(which === "clips" ? "w.ruler.subtitleClips" : "w.ruler.subtitle")}>
      <div role="group" aria-label={t("w.ruler.objects")} className="flex flex-wrap gap-2">
        {offered.map((o) => (
          <button key={o} type="button" aria-pressed={obj === o} className={`btn btn-sm ${obj === o ? "btn-primary" : "btn-ghost"}`} onClick={() => setObj(o)}>
            {t(`w.ruler.object.${o}`)}
          </button>
        ))}
      </div>
      {which === "both" && (
        <div className="mt-3 flex flex-wrap gap-2">
          {(["cm", "clips"] as const).map((v) => (
            <button key={v} type="button" aria-pressed={view === v} className={`btn btn-sm ${view === v ? "btn-gold" : "btn-ghost"}`} onClick={() => setView(v)}>
              {t(`w.ruler.view.${v}`)}
            </button>
          ))}
        </div>
      )}
      {view === "cm" ? <CmView obj={obj} offered={offered} setObj={setObj} start0={toInt(start, 2, 0, RULER_CM)} /> : <UnitsView obj={obj} showCm={which === "both"} />}
    </WidgetFrame>
  );
}

function CmView({ obj, offered, setObj, start0 }: { obj: ObjectId; offered: ObjectId[]; setObj: (o: ObjectId) => void; start0: number }) {
  const { t, n } = useI18n();
  const L = OBJECTS[obj];
  const [rawStart, setStart] = useState(start0);
  const [answer, setAnswer] = useState("");
  const [verdict, setVerdict] = useState<Verdict | "empty" | null>(null);
  const [reveal, setReveal] = useState(false);
  const [drag, setDrag] = useState<number | null>(null);
  const [seen, setSeen] = useState(obj);
  const svgRef = useRef<SVGSVGElement>(null);
  if (seen !== obj) {
    // A different object was picked: clear the previous answer (adjusting state during render is React's recommended pattern).
    setSeen(obj);
    setAnswer("");
    setVerdict(null);
    setReveal(false);
  }
  const s = clampStart(rawStart, L);
  const e = s + L;
  const W = X0 + RULER_CM * PX + 0.75 * PX + RX0;

  const move = (to: number) => {
    setStart(clampStart(to, L));
    setVerdict(null);
  };
  const cmAt = (ev: React.PointerEvent) => {
    const ctm = svgRef.current?.getScreenCTM();
    if (!ctm) return null;
    const p = new DOMPoint(ev.clientX, ev.clientY).matrixTransform(ctm.inverse());
    return (p.x - X0) / PX;
  };
  const check = (ev: React.FormEvent) => {
    ev.preventDefault();
    if (answer.trim() === "") return setVerdict("empty");
    setVerdict(judge(Number(answer.replace(",", ".")), s, L));
  };
  const next = () => {
    const i = offered.indexOf(obj);
    const o = offered[(i + 1) % offered.length];
    setObj(o);
    setStart(clampStart((s * 7 + 3) % (RULER_CM - OBJECTS[o] + 1), OBJECTS[o]));
    setAnswer("");
    setVerdict(null);
    setReveal(false);
  };
  const showReadings = reveal || verdict === "correct" || verdict === "endReading";
  const name = t(`w.ruler.object.${obj}`);

  return (
    <div className="mt-4">
      <div dir="ltr" className="overflow-x-auto">
        <svg
          ref={svgRef}
          viewBox={`0 0 ${W} 150`}
          className="w-full min-w-[360px] select-none"
          role="group"
          aria-label={t("w.ruler.aria", { object: name })}
          onPointerMove={(ev) => {
            if (drag === null) return;
            const x = cmAt(ev);
            if (x !== null) move(x - drag);
          }}
          onPointerUp={() => setDrag(null)}
          onPointerCancel={() => setDrag(null)}
        >
          {/* ruler */}
          <rect x={RX0} y={92} width={W - 2 * RX0} height={48} rx={6} fill="var(--gold-soft)" stroke="var(--gold)" strokeWidth="1.5" />
          {Array.from({ length: RULER_CM * 10 + 1 }, (_, i) => {
            const len = i % 10 === 0 ? 17 : i % 5 === 0 ? 11 : 6;
            return <line key={i} x1={X0 + (i * PX) / 10} y1={92} x2={X0 + (i * PX) / 10} y2={92 + len} stroke="var(--ink-2)" strokeWidth={i % 10 === 0 ? 1.6 : 0.8} />;
          })}
          {Array.from({ length: RULER_CM + 1 }, (_, i) => (
            <text key={i} x={X0 + i * PX} y={128} textAnchor="middle" fontSize="14" fontWeight={i === 0 ? 800 : 600} fill={i === 0 ? "var(--gold-ink)" : "var(--ink-2)"}>
              {i}
            </text>
          ))}
          <text x={W - RX0 - 6} y={136} textAnchor="end" fontSize="9" fill="var(--muted)">
            cm
          </text>
          {/* guides from the object's ends down to the ruler */}
          <line x1={X0 + s * PX} y1={OBJ_Y + 16} x2={X0 + s * PX} y2={92} stroke="var(--sky)" strokeWidth="1.5" strokeDasharray="3 3" style={{ transition: drag === null ? "all .3s" : "none" }} />
          <line x1={X0 + e * PX} y1={OBJ_Y + 16} x2={X0 + e * PX} y2={92} stroke="var(--human)" strokeWidth="1.5" strokeDasharray="3 3" style={{ transition: drag === null ? "all .3s" : "none" }} />
          {showReadings && (
            <g fontSize="15" fontWeight="700">
              <text x={X0 + s * PX} y={16} textAnchor="middle" fill="var(--sky-ink)">
                {s}
              </text>
              <text x={X0 + e * PX} y={16} textAnchor="middle" fill="var(--human)">
                {e}
              </text>
            </g>
          )}
          {/* the object (draggable) */}
          <g
            role="slider"
            tabIndex={0}
            aria-label={name}
            aria-valuemin={0}
            aria-valuemax={RULER_CM - L}
            aria-valuenow={s}
            aria-valuetext={t("w.ruler.position", { s })}
            className="cursor-grab touch-none outline-none [&:focus-visible>rect]:stroke-[var(--sky)]"
            style={{ transform: `translate(${X0 + s * PX}px, ${OBJ_Y}px)`, transition: drag === null ? "transform .3s cubic-bezier(.3,1.2,.5,1)" : "none" }}
            onPointerDown={(ev) => {
              const x = cmAt(ev);
              if (x === null) return;
              svgRef.current?.setPointerCapture(ev.pointerId);
              setDrag(x - s);
            }}
            onKeyDown={(ev) => {
              const d = ev.key === "ArrowRight" || ev.key === "ArrowUp" ? 1 : ev.key === "ArrowLeft" || ev.key === "ArrowDown" ? -1 : ev.key === "Home" ? -s : ev.key === "End" ? RULER_CM : 0;
              if (d) {
                ev.preventDefault();
                move(s + d);
              }
            }}
          >
            <rect x={-6} y={-24} width={L * PX + 12} height={48} rx={8} fill="transparent" stroke="transparent" strokeWidth="2" strokeDasharray="4 3" />
            <ObjectShape id={obj} len={L * PX} />
          </g>
        </svg>
      </div>

      <div className="mt-2 flex flex-wrap items-center gap-2">
        <button type="button" className="btn btn-sm btn-ghost" onClick={() => move(s - 1)} disabled={s === 0}>
          <ArrowLeft size={14} aria-hidden="true" /> {t("w.ruler.left")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" onClick={() => move(s + 1)} disabled={s >= RULER_CM - L}>
          {t("w.ruler.right")} <ArrowRight size={14} aria-hidden="true" />
        </button>
        <button type="button" className="btn btn-sm btn-gold" onClick={() => move(0)} disabled={s === 0}>
          {t("w.ruler.zero")}
        </button>
        <span className="text-xs text-muted">{t("w.ruler.dragHint")}</span>
      </div>

      <form onSubmit={check} className="mt-4 flex flex-wrap items-end gap-3">
        <label className="text-sm font-semibold text-ink-2">
          {t("w.ruler.question")}
          <span className="mt-1.5 flex items-center gap-2">
            <input type="number" inputMode="numeric" min={0} max={40} className="input w-24 py-1.5" value={answer} onChange={(ev) => setAnswer(ev.target.value)} dir="ltr" />
            <span className="text-ink">cm</span>
          </span>
        </label>
        <button type="submit" className="btn btn-sm btn-primary">
          <Check size={14} aria-hidden="true" /> {t("w.ruler.check")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" aria-pressed={reveal} onClick={() => setReveal((v) => !v)}>
          <Eye size={14} aria-hidden="true" /> {t("w.ruler.showReadings")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" onClick={next}>
          {t("w.ruler.next")} <ChevronsRight size={14} aria-hidden="true" className="rtl:rotate-180" />
        </button>
      </form>

      <div aria-live="polite" className="mt-3 min-h-6">
        {verdict && (
          <p className={`rounded-xl px-4 py-3 text-sm ${verdict === "correct" ? "bg-good-soft text-ink" : verdict === "empty" ? "bg-paper-2 text-ink-2" : "bg-warn-soft text-ink"}`}>
            {verdict === "correct"
              ? s === 0
                ? t("w.ruler.fb.correctZero", { e: n(e), l: n(L) })
                : t("w.ruler.fb.correct", { s: n(s), e: n(e), l: n(L) })
              : verdict === "endReading"
                ? t("w.ruler.fb.endReading", { s: n(s), e: n(e), l: n(L) })
                : verdict === "countedMarks"
                  ? t("w.ruler.fb.marks")
                  : verdict === "empty"
                    ? t("w.ruler.fb.empty")
                    : t("w.ruler.fb.wrong")}
          </p>
        )}
        {showReadings && verdict !== "correct" && verdict !== "endReading" && (
          <p className="mt-2 font-serif text-lg text-ink" dir="ltr">
            {e} − {s} = {L} cm
          </p>
        )}
      </div>
      <p className="mt-2 text-xs text-muted">{t("w.ruler.edgeNote")}</p>
    </div>
  );
}

function UnitsView({ obj, showCm }: { obj: ObjectId; showCm: boolean }) {
  const { t, n } = useI18n();
  const [unit, setUnit] = useState<UnitId>("smallClip");
  const L = OBJECTS[obj];
  const u = UNITS[unit];
  const P2 = 20;
  const count = Math.ceil(L / u - 1e-9);
  const boardCm = Math.max(16, count * u);
  const XS = 16;
  const W = XS * 2 + boardCm * P2;
  const name = t(`w.ruler.object.${obj}`);
  const fw = fitWords(L, u);

  return (
    <div className="mt-4">
      <div role="group" aria-label={t("w.ruler.unitsLabel")} className="flex flex-wrap gap-2">
        {UNIT_IDS.map((id) => (
          <button key={id} type="button" aria-pressed={unit === id} className={`btn btn-sm ${unit === id ? "btn-primary" : "btn-ghost"}`} onClick={() => setUnit(id)}>
            {id.endsWith("Clip") ? <Paperclip size={14} aria-hidden="true" /> : <Hand size={14} aria-hidden="true" />} {t(`w.ruler.unit.${id}`)}
          </button>
        ))}
      </div>
      <div dir="ltr" className="mt-3 overflow-x-auto">
        <svg viewBox={`0 0 ${W} 112`} className="w-full min-w-[340px]" role="img" aria-label={`${name}: ${t(`w.ruler.unit.${unit}`)}, ${t(`w.ruler.fit.${fw.key}`, { k: n(fw.k) })}`}>
          <g transform={`translate(${XS} 34)`}>
            <ObjectShape id={obj} len={L * P2} />
          </g>
          <line x1={XS} y1={10} x2={XS} y2={104} stroke="var(--ink-2)" strokeWidth="1.2" strokeDasharray="3 3" />
          <line x1={XS + L * P2} y1={10} x2={XS + L * P2} y2={104} stroke="var(--ink-2)" strokeWidth="1.2" strokeDasharray="3 3" />
          {Array.from({ length: count }, (_, i) => {
            const x = XS + i * u * P2;
            const beyond = (i + 1) * u > L + 1e-9;
            return (
              <g key={i}>
                <g transform={`translate(${x} 80)`} opacity={beyond ? 0.4 : 1}>
                  <UnitShape id={unit} len={u * P2} />
                </g>
                <text x={x + (u * P2) / 2} y={104} textAnchor="middle" fontSize="11" fontWeight="700" fill={beyond ? "var(--muted)" : "var(--ink-2)"}>
                  {i + 1}
                </text>
              </g>
            );
          })}
        </svg>
      </div>
      <div aria-live="polite" className="mt-3 rounded-xl bg-paper-2 px-4 py-3">
        <p className="text-sm text-ink-2">
          {name} · {t(`w.ruler.unit.${unit}`)}
        </p>
        <p className="mt-0.5 text-lg font-semibold text-ink">{t(`w.ruler.fit.${fw.key}`, { k: n(fw.k) })}</p>
      </div>
      <table className="mt-4 w-full text-sm">
        <tbody>
          {UNIT_IDS.map((id) => {
            const f = fitWords(L, UNITS[id]);
            return (
              <tr key={id} className={`border-t border-line ${id === unit ? "bg-gold-soft/50" : ""}`}>
                <td className="py-1.5 pe-2 text-ink-2">
                  {t(`w.ruler.unit.${id}`)}
                  {showCm && <span className="ms-1 text-xs text-muted">({t("w.ruler.eachCm", { v: n(UNITS[id]) })})</span>}
                </td>
                <td className="py-1.5 text-end font-semibold text-ink">{t(`w.ruler.fit.${f.key}`, { k: n(f.k) })}</td>
              </tr>
            );
          })}
          {showCm && (
            <tr className="border-t border-line">
              <td className="py-1.5 pe-2 text-ink-2">{t("w.ruler.view.cm")}</td>
              <td className="py-1.5 text-end font-semibold text-ink">{t("w.ruler.fit.exactly", { k: `${n(L)} cm` })}</td>
            </tr>
          )}
        </tbody>
      </table>
      <p className="mt-3 text-sm text-ink-2">{t("w.ruler.why")}</p>
    </div>
  );
}
