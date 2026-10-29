"use client";

import { Eraser, ListPlus, Shapes } from "lucide-react";
import { useId, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { AREA_12_PRESETS, DRAW_H, DRAW_W, area, boundaryEdges, cellsFromRows, emptyCells, perimeter, pieces, rectArea, rectPerimeter, triangleArea, type Cells } from "./lib/shape-grid";
import { listOf, oneOf, toInt } from "./lib/shape-util";

const MODES = ["rectangle", "draw", "split", "triangle"] as const;
type Mode = (typeof MODES)[number];

export interface AreaGridProps {
  mode?: Mode;
  modes?: Mode[];
  width?: number;
  height?: number;
  split?: number;
  unit?: string;
  title?: string;
  subtitle?: string;
}

type T = (k: string, v?: Record<string, string | number>) => string;

/** Area and perimeter on a square grid: rectangles as arrays, free drawing, the distributive law, and the triangle as half a rectangle. */
export function AreaGrid({ mode, modes, width, height, split, unit, title, subtitle }: AreaGridProps) {
  const { t, n } = useI18n();
  const offered = listOf(modes, MODES);
  const available = offered.length ? offered : [...MODES];
  const [tab, setTab] = useState<Mode>(oneOf(mode, available, available[0]));
  const u = typeof unit === "string" && unit.trim() ? unit.trim().slice(0, 12) : "";
  const fmtArea = (v: number) => (u ? `${n(v)} ${u}²` : t("w.area.sqUnits", { v: n(v) }));
  const fmtLen = (v: number) => (u ? `${n(v)} ${u}` : t("w.area.units", { v: n(v) }));

  return (
    <WidgetFrame title={title ?? t("w.area.title")} subtitle={subtitle ?? t("w.area.subtitle")}>
      {available.length > 1 && (
        <div className="mb-4 flex flex-wrap gap-2">
          {available.map((m) => (
            <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
              {t(`w.area.mode.${m}`)}
            </button>
          ))}
        </div>
      )}
      {tab === "rectangle" && <RectangleMode w0={toInt(width, 5, 1, 12)} h0={toInt(height, 3, 1, 10)} fmtArea={fmtArea} fmtLen={fmtLen} />}
      {tab === "draw" && <DrawMode fmtArea={fmtArea} fmtLen={fmtLen} />}
      {tab === "split" && <SplitMode a0={toInt(height, 3, 1, 8)} b0={toInt(split, Math.max(1, Math.min(8, toInt(width, 6, 2, 16) - 2)), 1, 8)} width={toInt(width, 6, 2, 16)} fmtArea={fmtArea} />}
      {tab === "triangle" && <TriangleMode b0={toInt(width, 6, 2, 10)} h0={toInt(height, 4, 1, 8)} fmtArea={fmtArea} />}
    </WidgetFrame>
  );
}

function Slider({ label, value, min, max, onChange, color = "var(--gold)" }: { label: string; value: number; min: number; max: number; onChange: (v: number) => void; color?: string }) {
  return (
    <label className="block">
      <span className="flex items-center justify-between gap-2 text-sm font-semibold text-ink-2">
        {label}
        <span className="font-mono text-ink" dir="ltr">
          {value}
        </span>
      </span>
      <input type="range" min={min} max={max} value={value} onChange={(e) => onChange(Number(e.target.value))} className="mt-1.5 w-full" style={{ accentColor: color }} dir="ltr" />
    </label>
  );
}

function Stat({ label, value, formula, tone }: { label: string; value: string; formula?: string; tone: "area" | "perimeter" }) {
  return (
    <div className={`rounded-xl px-4 py-3 ${tone === "area" ? "bg-sky-soft" : "bg-human-soft"}`}>
      <p className={`text-xs font-bold uppercase tracking-wide ${tone === "area" ? "text-sky-ink" : "text-human"}`}>{label}</p>
      {formula && (
        <p className="mt-1 font-serif text-lg text-ink" dir="ltr">
          {formula}
        </p>
      )}
      <p className="text-sm font-semibold text-ink">{value}</p>
    </div>
  );
}

/* ---------------------------------------------------------------- rectangle */

function RectangleMode({ w0, h0, fmtArea, fmtLen }: { w0: number; h0: number; fmtArea: (v: number) => string; fmtLen: (v: number) => string }) {
  const { t, n } = useI18n();
  const [w, setW] = useState(w0);
  const [h, setH] = useState(h0);
  const [count, setCount] = useState(false);
  const [trace, setTrace] = useState(0);
  const S = 26;
  const X0 = 34;
  const Y0 = 28;
  const BW = 12;
  const BH = 10;
  const A = rectArea(w, h);
  const P = rectPerimeter(w, h);
  const len = 2 * (w + h) * S;

  return (
    <div className="grid items-start gap-5 md:grid-cols-[1.3fr_1fr]">
      <div>
        <div className="grid gap-3 sm:grid-cols-2">
          <Slider label={t("w.area.width")} value={w} min={1} max={BW} onChange={setW} color="var(--sky)" />
          <Slider label={t("w.area.height")} value={h} min={1} max={BH} onChange={setH} color="var(--sky)" />
        </div>
        <div dir="ltr" className="mt-3">
          <svg viewBox={`0 0 ${X0 + BW * S + 26} ${Y0 + BH * S + 26}`} className="w-full" role="img" aria-label={t("w.area.rect.aria", { w, h, a: A, p: P })}>
            {Array.from({ length: BH }, (_, r) =>
              Array.from({ length: BW }, (_, c) => {
                const on = r < h && c < w;
                return <rect key={`${r}-${c}`} x={X0 + c * S} y={Y0 + r * S} width={S} height={S} fill={on ? (r % 2 ? "var(--gold-soft)" : "var(--sky-soft)") : "transparent"} stroke={on ? "var(--sky)" : "var(--line)"} strokeWidth={on ? 1.2 : 0.8} style={{ transition: "fill .2s" }} />;
              }),
            )}
            {count &&
              Array.from({ length: A }, (_, i) => (
                <text key={i} x={X0 + (i % w) * S + S / 2} y={Y0 + Math.floor(i / w) * S + S / 2 + 4} textAnchor="middle" fontSize="10" fontWeight="600" fill="var(--ink-2)">
                  {i + 1}
                </text>
              ))}
            <rect x={X0} y={Y0} width={w * S} height={h * S} fill="none" stroke="var(--ink-2)" strokeWidth="2" />
            {trace > 0 && (
              <>
                <path key={trace} d={`M${X0} ${Y0} h${w * S} v${h * S} h${-w * S} z`} fill="none" stroke="var(--human)" strokeWidth="4.5" strokeLinejoin="round" style={{ strokeDasharray: len, strokeDashoffset: len, animation: "draw 2s ease-in-out forwards" }} />
                {Array.from({ length: w + 1 }, (_, i) => (
                  <g key={`tb${i}`} fill="var(--human)">
                    <circle cx={X0 + i * S} cy={Y0} r="2.6" />
                    <circle cx={X0 + i * S} cy={Y0 + h * S} r="2.6" />
                  </g>
                ))}
                {Array.from({ length: h + 1 }, (_, i) => (
                  <g key={`lr${i}`} fill="var(--human)">
                    <circle cx={X0} cy={Y0 + i * S} r="2.6" />
                    <circle cx={X0 + w * S} cy={Y0 + i * S} r="2.6" />
                  </g>
                ))}
                <text x={X0 + (w * S) / 2} y={Y0 + h * S + 18} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--human)">
                  {w}
                </text>
                <text x={X0 + w * S + 8} y={Y0 + (h * S) / 2 + 5} fontSize="13" fontWeight="700" fill="var(--human)">
                  {h}
                </text>
              </>
            )}
            <text x={X0 + (w * S) / 2} y={Y0 - 9} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--ink-2)">
              {w}
            </text>
            <text x={X0 - 9} y={Y0 + (h * S) / 2 + 5} textAnchor="end" fontSize="13" fontWeight="700" fill="var(--ink-2)">
              {h}
            </text>
          </svg>
        </div>
      </div>
      <div className="space-y-3">
        <div className="flex flex-wrap gap-2">
          <button type="button" aria-pressed={count} className={`btn btn-sm ${count ? "btn-gold" : "btn-ghost"}`} onClick={() => setCount((v) => !v)}>
            {t("w.area.count")}
          </button>
          <button type="button" aria-pressed={trace > 0} className={`btn btn-sm ${trace > 0 ? "btn-gold" : "btn-ghost"}`} onClick={() => setTrace((k) => (k > 0 ? 0 : 1))}>
            {t("w.area.trace")}
          </button>
        </div>
        <div aria-live="polite" className="space-y-3">
          <p className="text-sm text-ink-2">{t("w.area.rows", { h: n(h), w: n(w) })}</p>
          <Stat tone="area" label={t("w.area.areaLabel")} formula={`${w} × ${h} = ${A}`} value={fmtArea(A)} />
          {trace > 0 && <Stat tone="perimeter" label={t("w.area.perimeterLabel")} formula={`${w} + ${h} + ${w} + ${h} = 2 × (${w} + ${h}) = ${P}`} value={fmtLen(P)} />}
        </div>
        <p className="text-xs text-muted">{t("w.area.rectNote")}</p>
      </div>
    </div>
  );
}

/* ---------------------------------------------------------------- draw */

function DrawMode({ fmtArea, fmtLen }: { fmtArea: (v: number) => string; fmtLen: (v: number) => string }) {
  const { t, n } = useI18n();
  const [cells, setCells] = useState<Cells>(() => emptyCells(DRAW_W, DRAW_H));
  const [focus, setFocus] = useState(0);
  const [example, setExample] = useState(0);
  const [records, setRecords] = useState<{ a: number; p: number }[]>([]);
  const paint = useRef<boolean | null>(null);
  const skipClick = useRef(false);
  const refs = useRef<(HTMLButtonElement | null)[]>([]);

  const A = area(cells);
  const P = perimeter(cells);
  const k = pieces(cells);
  const edges = useMemo(() => boundaryEdges(cells), [cells]);
  const sameArea = records.some((r, i) => records.some((s, j) => j > i && s.a === r.a && s.p !== r.p));

  const set = (r: number, c: number, v: boolean) => setCells((prev) => (prev[r][c] === v ? prev : prev.map((row, y) => (y === r ? row.map((x, xi) => (xi === c ? v : x)) : row))));
  const cellAt = (x: number, y: number) => {
    const el = typeof document !== "undefined" ? (document.elementFromPoint(x, y) as HTMLElement | null)?.closest<HTMLElement>("[data-cell]") : null;
    if (!el) return null;
    const i = Number(el.dataset.cell);
    return Number.isInteger(i) ? i : null;
  };
  const move = (i: number) => {
    const j = Math.max(0, Math.min(DRAW_W * DRAW_H - 1, i));
    setFocus(j);
    refs.current[j]?.focus();
  };
  const onKey = (e: React.KeyboardEvent, i: number) => {
    const r = Math.floor(i / DRAW_W);
    const c = i % DRAW_W;
    const map: Record<string, number | null> = {
      ArrowRight: c < DRAW_W - 1 ? i + 1 : null,
      ArrowLeft: c > 0 ? i - 1 : null,
      ArrowDown: r < DRAW_H - 1 ? i + DRAW_W : null,
      ArrowUp: r > 0 ? i - DRAW_W : null,
      Home: r * DRAW_W,
      End: r * DRAW_W + DRAW_W - 1,
    };
    if (e.key in map) {
      e.preventDefault();
      const j = map[e.key];
      if (j !== null && j !== undefined) move(j);
    }
  };

  return (
    <div className="grid items-start gap-5 md:grid-cols-[1.3fr_1fr]">
      <div>
        <p className="mb-2 text-sm text-ink-2">{t("w.area.draw.hint")}</p>
        <div
          dir="ltr"
          className="relative mx-auto max-w-md select-none"
          onPointerMove={(e) => {
            if (paint.current === null || e.pointerType === "touch") return;
            const i = cellAt(e.clientX, e.clientY);
            if (i !== null) set(Math.floor(i / DRAW_W), i % DRAW_W, paint.current);
          }}
          onPointerUp={() => (paint.current = null)}
          onPointerLeave={() => (paint.current = null)}
        >
          <div role="group" aria-label={t("w.area.draw.grid")} className="grid gap-0 overflow-hidden rounded-lg border border-line-2" style={{ gridTemplateColumns: `repeat(${DRAW_W}, minmax(0, 1fr))` }}>
            {cells.map((row, r) =>
              row.map((on, c) => {
                  const i = r * DRAW_W + c;
                  return (
                      <button
                        key={i}
                        ref={(el) => {
                          refs.current[i] = el;
                        }}
                        type="button"
                        data-cell={i}
                        tabIndex={i === focus ? 0 : -1}
                        aria-pressed={on}
                        aria-label={t("w.area.draw.cell", { r: r + 1, c: c + 1 })}
                        className={`aspect-square border-[0.5px] border-line transition-colors focus-visible:relative focus-visible:z-10 ${on ? "bg-sky-soft" : "bg-card hover:bg-paper-2"}`}
                        onFocus={() => setFocus(i)}
                        onKeyDown={(e) => onKey(e, i)}
                        onPointerDown={(e) => {
                          if (e.pointerType === "touch") return;
                          paint.current = !on;
                          skipClick.current = true;
                          set(r, c, !on);
                        }}
                        onClick={() => {
                          if (skipClick.current) {
                            skipClick.current = false;
                            return;
                          }
                          set(r, c, !on);
                        }}
                      >
                        {on && <span className="mx-auto block h-1.5 w-1.5 rounded-full bg-sky/50" aria-hidden="true" />}
                      </button>
                  );
                }),
            )}
          </div>
          <svg viewBox={`0 0 ${DRAW_W} ${DRAW_H}`} preserveAspectRatio="none" className="pointer-events-none absolute inset-0 h-full w-full" aria-hidden="true">
            {edges.map((e, i) => (
              <line key={i} x1={e.x1} y1={e.y1} x2={e.x2} y2={e.y2} stroke="var(--human)" strokeWidth="3.5" strokeLinecap="round" vectorEffect="non-scaling-stroke" />
            ))}
          </svg>
        </div>
        <div className="mt-3 flex flex-wrap justify-center gap-2">
          <button type="button" className="btn btn-sm btn-ghost" onClick={() => setCells(emptyCells(DRAW_W, DRAW_H))}>
            <Eraser size={14} aria-hidden="true" /> {t("w.area.draw.clear")}
          </button>
          <button
            type="button"
            className="btn btn-sm btn-ghost"
            onClick={() => {
              setCells(cellsFromRows(AREA_12_PRESETS[example % AREA_12_PRESETS.length], DRAW_W, DRAW_H));
              setExample((x) => x + 1);
            }}
          >
            <Shapes size={14} aria-hidden="true" /> {t("w.area.draw.example")}
          </button>
          <button type="button" className="btn btn-sm btn-gold" disabled={A === 0} onClick={() => setRecords((prev) => [...prev, { a: A, p: P }].slice(-6))}>
            <ListPlus size={14} aria-hidden="true" /> {t("w.area.draw.record")}
          </button>
        </div>
      </div>
      <div className="space-y-3">
        <div aria-live="polite" className="space-y-3">
          {A === 0 ? (
            <p className="rounded-xl bg-paper-2 px-4 py-3 text-sm text-ink-2">{t("w.area.draw.empty")}</p>
          ) : (
            <>
              <Stat tone="area" label={t("w.area.areaLabel")} value={fmtArea(A)} />
              <Stat tone="perimeter" label={t("w.area.perimeterLabel")} value={fmtLen(P)} />
              {k > 1 && <p className="text-sm text-ink-2">{t("w.area.draw.pieces", { k: n(k) })}</p>}
            </>
          )}
        </div>
        {records.length > 0 && (
          <div>
            <p className="text-sm font-semibold text-ink-2">{t("w.area.draw.recorded")}</p>
            <table className="mt-1.5 w-full text-sm">
              <thead>
                <tr className="text-start text-xs text-muted">
                  <th className="py-1 text-start font-semibold">#</th>
                  <th className="py-1 text-start font-semibold">{t("w.area.areaLabel")}</th>
                  <th className="py-1 text-start font-semibold">{t("w.area.perimeterLabel")}</th>
                </tr>
              </thead>
              <tbody>
                {records.map((r, i) => (
                  <tr key={i} className="border-t border-line">
                    <td className="py-1 text-muted">{n(i + 1)}</td>
                    <td className="py-1 font-semibold text-ink">{fmtArea(r.a)}</td>
                    <td className="py-1 font-semibold text-ink">{fmtLen(r.p)}</td>
                  </tr>
                ))}
              </tbody>
            </table>
            {sameArea && <p className="mt-2 rounded-lg bg-gold-soft px-3 py-2 text-sm text-ink">{t("w.area.draw.sameArea")}</p>}
          </div>
        )}
      </div>
    </div>
  );
}

/* ---------------------------------------------------------------- split */

function SplitMode({ a0, b0, width, fmtArea }: { a0: number; b0: number; width: number; fmtArea: (v: number) => string }) {
  const { t } = useI18n();
  const [a, setA] = useState(a0);
  const [b, setB] = useState(b0);
  const [c, setC] = useState(Math.max(1, Math.min(8, width - b0)));
  const [apart, setApart] = useState(false);
  const S = 24;
  const X0 = 28;
  const Y0 = 34;
  const gap = apart ? 1.4 * S : 0;
  const total = a * (b + c);

  const block = (cols: number, x0: number, fill: string, stroke: string) =>
    Array.from({ length: a }, (_, r) =>
      Array.from({ length: cols }, (_, k) => <rect key={`${r}-${k}`} x={x0 + k * S} y={Y0 + r * S} width={S} height={S} fill={fill} stroke={stroke} strokeWidth="1" />),
    );

  return (
    <div className="grid items-start gap-5 md:grid-cols-[1.3fr_1fr]">
      <div>
        <div className="grid gap-3 sm:grid-cols-3">
          <Slider label={t("w.area.split.a")} value={a} min={1} max={8} onChange={setA} color="var(--ink-2)" />
          <Slider label={t("w.area.split.b")} value={b} min={1} max={8} onChange={setB} color="var(--sky)" />
          <Slider label={t("w.area.split.c")} value={c} min={1} max={8} onChange={setC} color="var(--gold)" />
        </div>
        <div dir="ltr" className="mt-3 overflow-x-auto">
          <svg viewBox={`0 0 ${X0 + (Math.max(10, b + c) + 1.4) * S + 10} ${Y0 + Math.max(4, a) * S + 34}`} className="w-full min-w-[300px]" role="img" aria-label={`${a} × (${b} + ${c}) = ${a} × ${b} + ${a} × ${c} = ${total}`}>
            <g>{block(b, X0, "var(--sky-soft)", "var(--sky)")}</g>
            <g style={{ transform: `translateX(${gap}px)`, transition: "transform .45s cubic-bezier(.3,1.2,.5,1)" }}>
              {block(c, X0 + b * S, "var(--gold-soft)", "var(--gold)")}
              <rect x={X0 + b * S} y={Y0} width={c * S} height={a * S} fill="none" stroke="var(--gold-ink)" strokeWidth="2" />
              <text x={X0 + b * S + (c * S) / 2} y={Y0 - 10} textAnchor="middle" fontSize="14" fontWeight="700" fill="var(--gold-ink)">
                c = {c}
              </text>
              <text x={X0 + b * S + (c * S) / 2} y={Y0 + a * S + 20} textAnchor="middle" fontSize="13" fontWeight="600" fill="var(--gold-ink)">
                {a} × {c} = {a * c}
              </text>
            </g>
            <rect x={X0} y={Y0} width={b * S} height={a * S} fill="none" stroke="var(--sky)" strokeWidth="2" />
            {!apart && <rect x={X0} y={Y0} width={(b + c) * S} height={a * S} fill="none" stroke="var(--ink-2)" strokeWidth="2.5" />}
            <text x={X0 + (b * S) / 2} y={Y0 - 10} textAnchor="middle" fontSize="14" fontWeight="700" fill="var(--sky)">
              b = {b}
            </text>
            <text x={X0 + (b * S) / 2} y={Y0 + a * S + 20} textAnchor="middle" fontSize="13" fontWeight="600" fill="var(--sky)">
              {a} × {b} = {a * b}
            </text>
            <text x={X0 - 8} y={Y0 + (a * S) / 2 + 5} textAnchor="end" fontSize="14" fontWeight="700" fill="var(--ink-2)">
              {a}
            </text>
          </svg>
        </div>
      </div>
      <div className="space-y-3">
        <button type="button" aria-pressed={apart} className={`btn btn-sm ${apart ? "btn-gold" : "btn-ghost"}`} onClick={() => setApart((v) => !v)}>
          {t("w.area.split.apart")}
        </button>
        <div aria-live="polite" className="rounded-xl bg-paper-2 px-4 py-3 font-serif text-lg leading-relaxed text-ink" dir="ltr">
          <p>
            {a} × ({b} + {c}) = {a} × {b} + {a} × {c}
          </p>
          <p>
            = {a * b} + {a * c} = <strong>{total}</strong>
          </p>
        </div>
        <p className="text-sm font-semibold text-ink">{fmtArea(total)}</p>
        <p className="text-sm text-ink-2">{t("w.area.split.note")}</p>
        <p className="font-serif text-base text-muted" dir="ltr">
          a × (b + c) = a × b + a × c
        </p>
      </div>
    </div>
  );
}

/* ---------------------------------------------------------------- triangle */

function TriangleMode({ b0, h0, fmtArea }: { b0: number; h0: number; fmtArea: (v: number) => string }) {
  const { t, n } = useI18n();
  const [b, setB] = useState(b0);
  const [h, setH] = useState(h0);
  const [s, setS] = useState(Math.floor(b0 / 3));
  const [turned, setTurned] = useState(false);
  const uid = useId().replace(/[^a-zA-Z0-9_-]/g, "");
  const S = 30;
  const X0 = 30;
  const Y0 = 16;
  const apex = Math.min(s, b);
  const X = (x: number) => X0 + x * S;
  // The rectangle sits on the bottom of the 10 × 8 board: y = 0 is its top edge.
  const Y = (y: number) => Y0 + (y + 8 - h) * S;
  const pts = (p: [number, number][]) => p.map(([x, y]) => `${X(x)},${Y(y)}`).join(" ");
  const R = rectArea(b, h);
  const A = triangleArea(b, h);
  const half = (v: number) => (Number.isInteger(v) ? `${v}` : `${Math.floor(v)}½`);
  const turnStyle = (cx: number) => ({ transform: `rotate(${turned ? 180 : 0}deg)`, transformOrigin: `${X(cx)}px ${Y(h / 2)}px`, transition: "transform .9s cubic-bezier(.4,0,.2,1)" });
  const changeBase = (v: number) => {
    setB(v);
    setS((x) => Math.min(x, v));
  };

  return (
    <div className="grid items-start gap-5 md:grid-cols-[1.3fr_1fr]">
      <div>
        <div className="grid gap-3 sm:grid-cols-3">
          <Slider label={t("w.area.tri.base")} value={b} min={2} max={10} onChange={changeBase} color="var(--sky)" />
          <Slider label={t("w.area.tri.height")} value={h} min={1} max={8} onChange={setH} color="var(--sky)" />
          <Slider label={t("w.area.tri.apex")} value={apex} min={0} max={b} onChange={setS} color="var(--gold)" />
        </div>
        <div dir="ltr" className="mt-3">
          <svg viewBox={`0 0 ${X0 + 10 * S + 20} ${Y0 + 8 * S + 30}`} className="w-full" role="img" aria-label={t("w.area.tri.aria", { b, h, r: R, a: n(A) })}>
            <defs>
              <pattern id={`ag-hatch-l-${uid}`} width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
                <rect width="6" height="6" fill="var(--sky-soft)" />
                <line x1="0" y1="0" x2="0" y2="6" stroke="var(--sky)" strokeWidth="1.6" />
              </pattern>
              <pattern id={`ag-hatch-r-${uid}`} width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(-45)">
                <rect width="6" height="6" fill="var(--gold-soft)" />
                <line x1="0" y1="0" x2="0" y2="6" stroke="var(--gold)" strokeWidth="1.6" />
              </pattern>
            </defs>
            {Array.from({ length: 9 }, (_, i) => (
              <line key={`h${i}`} x1={X(0)} y1={Y0 + i * S} x2={X(10)} y2={Y0 + i * S} stroke="var(--line)" strokeWidth="0.8" />
            ))}
            {Array.from({ length: 11 }, (_, i) => (
              <line key={`v${i}`} x1={X(i)} y1={Y0} x2={X(i)} y2={Y0 + 8 * S} stroke="var(--line)" strokeWidth="0.8" />
            ))}
            <g>
              {/* inside pieces */}
              <polygon points={pts([[0, h], [apex, h], [apex, 0]])} fill="var(--sky-soft)" />
              <polygon points={pts([[apex, h], [b, h], [apex, 0]])} fill="var(--gold-soft)" />
              {/* outside pieces: each turns half a turn about the midpoint of a triangle side and lands on an inside piece */}
              {apex > 0 && (
                <g style={turnStyle(apex / 2)}>
                  <polygon points={pts([[0, h], [0, 0], [apex, 0]])} fill={`url(#ag-hatch-l-${uid})`} stroke="var(--sky)" strokeWidth="1.5" opacity={turned ? 0.75 : 1} />
                </g>
              )}
              {apex < b && (
                <g style={turnStyle((apex + b) / 2)}>
                  <polygon points={pts([[b, h], [b, 0], [apex, 0]])} fill={`url(#ag-hatch-r-${uid})`} stroke="var(--gold)" strokeWidth="1.5" opacity={turned ? 0.75 : 1} />
                </g>
              )}
              <rect x={X(0)} y={Y(0)} width={b * S} height={h * S} fill="none" stroke="var(--ink-2)" strokeWidth="1.8" strokeDasharray="6 4" />
              <line x1={X(apex)} y1={Y(0)} x2={X(apex)} y2={Y(h)} stroke="var(--ink-2)" strokeWidth="1.4" strokeDasharray="3 3" />
              <polygon points={pts([[0, h], [b, h], [apex, 0]])} fill="none" stroke="var(--ink)" strokeWidth="3" strokeLinejoin="round" />
              <text x={X(b / 2)} y={Y(h) + 20} textAnchor="middle" fontSize="13" fontWeight="700" fill="var(--ink-2)">
                {b}
              </text>
              <text x={X(b) + 8} y={Y(h / 2) + 5} fontSize="13" fontWeight="700" fill="var(--ink-2)">
                {h}
              </text>
            </g>
          </svg>
        </div>
      </div>
      <div className="space-y-3">
        <button type="button" aria-pressed={turned} className={`btn btn-sm ${turned ? "btn-gold" : "btn-ghost"}`} onClick={() => setTurned((v) => !v)}>
          {t("w.area.tri.rearrange")}
        </button>
        <div aria-live="polite" className="space-y-3">
          <Stat tone="perimeter" label={t("w.area.tri.rect")} formula={`${b} × ${h} = ${R}`} value={fmtArea(R)} />
          <Stat tone="area" label={t("w.area.tri.tri")} formula={`½ × ${b} × ${h} = ${half(A)}`} value={fmtArea(A)} />
          {turned && <p className="rounded-lg bg-gold-soft px-3 py-2 text-sm text-ink">{t("w.area.tri.note1")}</p>}
        </div>
        <p className="text-sm text-ink-2">{t("w.area.tri.note2")}</p>
      </div>
    </div>
  );
}
