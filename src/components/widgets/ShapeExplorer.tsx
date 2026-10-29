"use client";

import { RotateCw, Shuffle } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  angleSum,
  centroid,
  diagonalCount,
  diagonals,
  equalMarks,
  fanTriangles,
  fitToBox,
  formatAngle,
  interiorAngles,
  irregularPolygon,
  isRight,
  parallelMarks,
  parallelPairCount,
  regularPolygon,
  resolveGallery,
  rotationOrder,
  roundPreservingSum,
  sideLengths,
  symmetryAxes,
  type Pt,
  type ShapeDef,
} from "./lib/shape-geometry";
import { listOf, oneOf, toInt } from "./lib/shape-util";

const FEATURES = ["sides", "vertices", "angles", "symmetry", "rotation", "diagonals"] as const;
type Feature = (typeof FEATURES)[number];

const W = 360;
const H = 290;
const LETTERS = "ABCDEFGHIJKL";

export interface ShapeExplorerProps {
  shapes?: string[];
  show?: string[];
  mode?: "gallery" | "polygon";
  n?: number;
  title?: string;
  subtitle?: string;
}

/**
 * 2D shapes: a gallery of named shapes with switchable features (sides, vertices,
 * angles, symmetry lines, rotational symmetry, diagonals), and a polygon mode
 * that triangulates an n-gon from one vertex to find the angle sum (n − 2) × 180°.
 */
export function ShapeExplorer({ shapes, show, mode, n, title, subtitle }: ShapeExplorerProps) {
  const { t } = useI18n();
  const gallery = useMemo(() => resolveGallery(shapes), [shapes]);
  const [tab, setTab] = useState<"gallery" | "polygon">(oneOf(mode, ["gallery", "polygon"] as const, "gallery"));
  const [selected, setSelected] = useState(0);
  const initial = listOf(show, FEATURES);
  const [on, setOn] = useState<Feature[]>(Array.isArray(show) ? initial : ["sides", "vertices"]);
  const toggle = (f: Feature) => setOn((prev) => (prev.includes(f) ? prev.filter((x) => x !== f) : [...prev, f]));

  const shape = gallery[Math.min(selected, gallery.length - 1)];

  return (
    <WidgetFrame title={title ?? t("w.shapes.title")} subtitle={subtitle ?? t("w.shapes.subtitle")}>
      <div className="flex flex-wrap gap-2">
        {(["gallery", "polygon"] as const).map((m) => (
          <button key={m} type="button" aria-pressed={tab === m} className={`btn btn-sm ${tab === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setTab(m)}>
            {t(`w.shapes.mode.${m}`)}
          </button>
        ))}
      </div>
      {tab === "gallery" ? (
        <Gallery gallery={gallery} selected={Math.min(selected, gallery.length - 1)} onSelect={setSelected} shape={shape} on={on} toggle={toggle} />
      ) : (
        <PolygonAngles initialN={toInt(n, 6, 3, 12)} showAnglesDefault={Array.isArray(show) ? initial.includes("angles") : true} />
      )}
    </WidgetFrame>
  );
}

/* ---------------------------------------------------------------- gallery */

function shapeName(t: (k: string, v?: Record<string, string | number>) => string, s: ShapeDef) {
  return s.key === "regularN" ? t("w.shapes.name.regularN", { n: s.regularN ?? 0 }) : t(`w.shapes.name.${s.key}`);
}

function Thumb({ s }: { s: ShapeDef }) {
  if (s.family === "circle") return <circle cx={22} cy={18} r={14} fill="var(--sky-soft)" stroke="var(--sky)" strokeWidth="2" />;
  const { points } = fitToBox(s.vertices, 44, 36, 4);
  return <polygon points={points.map((p) => `${p.x},${p.y}`).join(" ")} fill="var(--sky-soft)" stroke="var(--sky)" strokeWidth="2" strokeLinejoin="round" />;
}

function Gallery({ gallery, selected, onSelect, shape, on, toggle }: { gallery: ShapeDef[]; selected: number; onSelect: (i: number) => void; shape: ShapeDef; on: Feature[]; toggle: (f: Feature) => void }) {
  const { t, n } = useI18n();
  const [turns, setTurns] = useState(0);
  const isCircle = shape.family === "circle";
  const nV = shape.vertices.length;

  const geo = useMemo(() => {
    if (isCircle) return null;
    const { points } = fitToBox(shape.vertices, W, H, 50);
    const c = centroid(points);
    return {
      points,
      c,
      angles: interiorAngles(shape.vertices),
      sideMarks: equalMarks(sideLengths(points)),
      parMarks: parallelMarks(points),
      axes: symmetryAxes(points),
      order: rotationOrder(points),
      pairs: parallelPairCount(points),
      reach: Math.max(...points.map((p) => Math.hypot(p.x - c.x, p.y - c.y))),
    };
  }, [shape, isCircle]);

  const order = geo?.order ?? 1;
  const step = isCircle ? 45 : 360 / order;
  const has = (f: Feature) => on.includes(f);
  const name = shapeName(t, shape);
  const select = (i: number) => {
    onSelect(i);
    setTurns(0);
  };

  /* --- facts (shown for the switched-on features) --- */
  const facts: { label: string; value: string }[] = [];
  if (has("sides")) {
    facts.push({ label: t("w.shapes.fact.sides"), value: isCircle ? t("w.shapes.circle.sides") : n(nV) });
    if (!isCircle && nV >= 4) facts.push({ label: t("w.shapes.fact.parallel"), value: n(geo!.pairs) });
  }
  if (has("vertices")) facts.push({ label: t("w.shapes.fact.vertices"), value: isCircle ? t("w.shapes.circle.none") : n(nV) });
  if (has("angles")) {
    if (isCircle) facts.push({ label: t("w.shapes.fact.angles"), value: t("w.shapes.circle.angles") });
    else {
      facts.push({ label: t("w.shapes.fact.angles"), value: geo!.angles.map(formatAngle).join(", ") });
      facts.push({ label: t("w.shapes.fact.angleSum"), value: `${angleSum(nV)}°` });
    }
  }
  if (has("symmetry")) facts.push({ label: t("w.shapes.fact.symmetry"), value: isCircle ? t("w.shapes.circle.symmetry") : n(geo!.axes.length) });
  if (has("rotation")) facts.push({ label: t("w.shapes.fact.rotation"), value: isCircle ? t("w.shapes.circle.rotation") : order === 1 ? t("w.shapes.rotationNone") : t("w.shapes.rotationOrder", { k: n(order) }) });
  if (has("diagonals")) facts.push({ label: t("w.shapes.fact.diagonals"), value: isCircle ? t("w.shapes.circle.none") : n(diagonalCount(nV)) });

  const ariaLabel = [name, ...facts.map((f) => `${f.label}: ${f.value}`)].join(". ");

  return (
    <div className="mt-4">
      <div role="group" aria-label={t("w.shapes.gallery")} className="-mx-1 flex gap-1.5 overflow-x-auto px-1 pb-2">
        {gallery.map((s, i) => (
          <button
            key={`${s.key}-${s.regularN ?? ""}`}
            type="button"
            aria-pressed={i === selected}
            onClick={() => select(i)}
            className={`flex w-[5.4rem] shrink-0 flex-col items-center gap-1 rounded-xl border px-1.5 py-2 text-center text-[0.7rem] leading-tight transition-colors ${i === selected ? "border-sky bg-sky-soft font-semibold text-ink" : "border-line bg-card text-ink-2 hover:bg-paper-2"}`}
          >
            <svg viewBox="0 0 44 36" className="h-9 w-11" aria-hidden="true">
              <Thumb s={s} />
            </svg>
            <span>{shapeName(t, s)}</span>
          </button>
        ))}
      </div>

      <div role="group" aria-label={t("w.shapes.features")} className="mt-3 flex flex-wrap gap-2">
        {FEATURES.map((f) => (
          <button key={f} type="button" aria-pressed={has(f)} className={`btn btn-sm ${has(f) ? "btn-gold" : "btn-ghost"}`} onClick={() => toggle(f)}>
            {t(`w.shapes.feature.${f}`)}
          </button>
        ))}
      </div>

      <div className="mt-4 grid items-start gap-5 md:grid-cols-[1.25fr_1fr]">
        <div dir="ltr">
          <svg viewBox={`0 0 ${W} ${H}`} className="w-full rounded-xl bg-paper-2/60" role="img" aria-label={ariaLabel}>
            {isCircle ? <CircleDrawing has={has} turns={turns} t={t} /> : <PolygonDrawing geo={geo!} has={has} turns={turns} step={step} nV={nV} />}
          </svg>
          {has("rotation") && (
            <div className="mt-2 flex flex-wrap items-center justify-center gap-2" dir="auto">
              <button type="button" className="btn btn-sm btn-ghost" onClick={() => setTurns((k) => k + 1)}>
                <RotateCw size={14} aria-hidden="true" /> {t("w.shapes.turn", { deg: n(Math.round(step * 100) / 100) })}
              </button>
              {turns > 0 && (
                <button type="button" className="btn btn-sm btn-ghost" onClick={() => setTurns(0)}>
                  {t("w.common.reset")}
                </button>
              )}
            </div>
          )}
        </div>

        <div aria-live="polite">
          <p className="flex flex-wrap items-center gap-2">
            <span className="font-serif text-xl font-semibold text-ink">{name}</span>
            <span className="chip">{t(`w.shapes.family.${shape.family}`)}</span>
          </p>
          {facts.length > 0 ? (
            <dl className="mt-3 divide-y divide-line rounded-xl border border-line text-sm">
              {facts.map((f) => (
                <div key={f.label} className="flex items-baseline justify-between gap-3 px-3 py-2">
                  <dt className="text-ink-2">{f.label}</dt>
                  <dd className="text-end font-semibold text-ink" dir="auto">
                    {f.value}
                  </dd>
                </div>
              ))}
            </dl>
          ) : (
            <p className="mt-3 text-sm text-muted">{t("w.shapes.hint")}</p>
          )}
          <p className="mt-3 text-sm leading-relaxed text-ink-2">{t(`w.shapes.note.${shape.family === "polygon" ? "regular" : shape.key}`)}</p>
          {has("sides") && !isCircle && (
            <p className="mt-2 text-xs text-muted">
              {t("w.shapes.legend.sides")}
              {nV <= 4 && geo!.pairs > 0 && ` ${t("w.shapes.legend.parallel")}`}
            </p>
          )}
          {has("symmetry") && <p className="mt-2 text-xs text-muted">{t("w.shapes.legend.symmetry")}</p>}
          {has("rotation") && turns > 0 && (
            <p className="mt-2 rounded-lg bg-gold-soft px-3 py-2 text-sm text-ink">
              {t("w.shapes.turned", { total: n(Math.round(turns * step * 100) / 100) })}{" "}
              {isCircle ? t("w.shapes.circle.fits") : order === 1 ? t("w.shapes.fitsOnlyFull") : t("w.shapes.fitsAfter", { deg: n(Math.round(step * 100) / 100), k: n(order) })}
            </p>
          )}
        </div>
      </div>
    </div>
  );
}

/** A soft outline behind SVG labels so they stay readable over lines. */
const HALO = { stroke: "var(--paper-2)", strokeWidth: 4, strokeLinejoin: "round" as const, paintOrder: "stroke" };

const unit = (a: Pt, b: Pt) => {
  const d = Math.hypot(b.x - a.x, b.y - a.y) || 1;
  return { x: (b.x - a.x) / d, y: (b.y - a.y) / d };
};

/** Angle arc (or right-angle box) at vertex p between neighbours a and b, with an optional label. */
function AngleMark({ p, a, b, value, label = true, color = "var(--human)" }: { p: Pt; a: Pt; b: Pt; value: number; label?: boolean; color?: string }) {
  const u1 = unit(p, a);
  const u2 = unit(p, b);
  const bis = unit({ x: 0, y: 0 }, { x: u1.x + u2.x, y: u1.y + u2.y });
  const half = (value * Math.PI) / 360;
  const lr = Math.min(58, Math.max(30, 15 / Math.max(0.2, Math.sin(half))));
  if (isRight(value)) {
    const s = 13;
    return (
      <g>
        <path d={`M${p.x + s * u1.x} ${p.y + s * u1.y} L${p.x + s * (u1.x + u2.x)} ${p.y + s * (u1.y + u2.y)} L${p.x + s * u2.x} ${p.y + s * u2.y}`} fill="none" stroke={color} strokeWidth="1.8" />
        {label && (
          <text x={p.x + lr * bis.x} y={p.y + lr * bis.y + 4} textAnchor="middle" fontSize="12" fontWeight="600" fill={color} {...HALO}>
            90°
          </text>
        )}
      </g>
    );
  }
  const r = 19;
  const cross = u1.x * u2.y - u1.y * u2.x;
  return (
    <g>
      <path d={`M${p.x + r * u1.x} ${p.y + r * u1.y} A${r} ${r} 0 0 ${cross > 0 ? 1 : 0} ${p.x + r * u2.x} ${p.y + r * u2.y}`} fill="none" stroke={color} strokeWidth="1.8" />
      {label && (
        <text x={p.x + lr * bis.x} y={p.y + lr * bis.y + 4} textAnchor="middle" fontSize="12" fontWeight="600" fill={color} {...HALO}>
          {formatAngle(value)}
        </text>
      )}
    </g>
  );
}

interface Geo {
  points: Pt[];
  c: Pt;
  angles: number[];
  sideMarks: number[];
  parMarks: number[];
  axes: number[];
  order: number;
  reach: number;
}

function PolygonDrawing({ geo, has, turns, step, nV }: { geo: Geo; has: (f: Feature) => boolean; turns: number; step: number; nV: number }) {
  const { points: P, c } = geo;
  const poly = P.map((p) => `${p.x},${p.y}`).join(" ");
  const L = geo.reach * 1.22;
  return (
    <g>
      {has("rotation") && <polygon points={poly} fill="none" stroke="var(--line-2)" strokeWidth="2" strokeDasharray="5 5" />}
      <g style={{ transform: `rotate(${has("rotation") ? turns * step : 0}deg)`, transformOrigin: `${c.x}px ${c.y}px`, transition: "transform .7s cubic-bezier(.3,1.2,.5,1)" }}>
        <polygon points={poly} fill="var(--sky-soft)" stroke={has("sides") ? "var(--sky)" : "var(--ink-2)"} strokeWidth={has("sides") ? 3.5 : 2} strokeLinejoin="round" opacity={has("rotation") ? 0.9 : 1} />
        {has("rotation") && <circle cx={P[0].x} cy={P[0].y} r="7" fill="var(--gold)" stroke="var(--card)" strokeWidth="2" />}
      </g>
      {has("diagonals") && diagonals(nV).map(([i, j]) => <line key={`d${i}-${j}`} x1={P[i].x} y1={P[i].y} x2={P[j].x} y2={P[j].y} stroke="var(--compute)" strokeWidth="1.8" strokeDasharray="6 4" />)}
      {has("symmetry") &&
        geo.axes.map((d) => {
          // Axes were computed from the SVG-space points, so the direction applies directly.
          const dx = Math.cos((d * Math.PI) / 180);
          const dy = Math.sin((d * Math.PI) / 180);
          return <line key={`s${d}`} x1={c.x - L * dx} y1={c.y - L * dy} x2={c.x + L * dx} y2={c.y + L * dy} stroke="var(--formal)" strokeWidth="2" strokeDasharray="8 5" strokeLinecap="round" />;
        })}
      {has("rotation") && (
        <g stroke="var(--ink-2)" strokeWidth="1.5">
          <line x1={c.x - 5} y1={c.y} x2={c.x + 5} y2={c.y} />
          <line x1={c.x} y1={c.y - 5} x2={c.x} y2={c.y + 5} />
        </g>
      )}
      {has("sides") &&
        P.map((p, i) => {
          const q = P[(i + 1) % nV];
          const d = unit(p, q);
          const nrm = { x: -d.y, y: d.x };
          const m = { x: (p.x + q.x) / 2, y: (p.y + q.y) / 2 };
          const k = geo.sideMarks[i];
          const par = nV <= 4 ? geo.parMarks[i] : 0;
          const dd = d.x > 1e-9 || (Math.abs(d.x) <= 1e-9 && d.y > 0) ? d : { x: -d.x, y: -d.y };
          const at = { x: p.x + 0.27 * (q.x - p.x), y: p.y + 0.27 * (q.y - p.y) };
          return (
            <g key={`m${i}`} stroke="var(--ink)" strokeWidth="1.8" fill="none" strokeLinecap="round">
              {Array.from({ length: k }, (_, j) => {
                const o = (j - (k - 1) / 2) * 5;
                return <line key={j} x1={m.x + o * d.x - 6 * nrm.x} y1={m.y + o * d.y - 6 * nrm.y} x2={m.x + o * d.x + 6 * nrm.x} y2={m.y + o * d.y + 6 * nrm.y} />;
              })}
              {Array.from({ length: par }, (_, j) => {
                const cpt = { x: at.x + j * 6 * dd.x, y: at.y + j * 6 * dd.y };
                return <path key={`p${j}`} d={`M${cpt.x - 5 * dd.x + 4.5 * nrm.x} ${cpt.y - 5 * dd.y + 4.5 * nrm.y} L${cpt.x} ${cpt.y} L${cpt.x - 5 * dd.x - 4.5 * nrm.x} ${cpt.y - 5 * dd.y - 4.5 * nrm.y}`} />;
              })}
            </g>
          );
        })}
      {has("angles") && P.map((p, i) => <AngleMark key={`a${i}`} p={p} a={P[(i - 1 + nV) % nV]} b={P[(i + 1) % nV]} value={geo.angles[i]} label={nV <= 10} />)}
      {has("vertices") &&
        P.map((p, i) => {
          const u = unit(c, p);
          return (
            <g key={`v${i}`}>
              <circle cx={p.x} cy={p.y} r="4.5" fill="var(--ink)" />
              <text x={p.x + 17 * u.x} y={p.y + 17 * u.y + 5} textAnchor="middle" fontSize="14" fontWeight="700" fill="var(--ink)" fontStyle="italic" className="font-serif" {...HALO}>
                {LETTERS[i]}
              </text>
            </g>
          );
        })}
    </g>
  );
}

function CircleDrawing({ has, turns, t }: { has: (f: Feature) => boolean; turns: number; t: (k: string) => string }) {
  const cx = W / 2;
  const cy = H / 2;
  const r = 108;
  return (
    <g>
      {has("rotation") && <circle cx={cx} cy={cy} r={r} fill="none" stroke="var(--line-2)" strokeWidth="2" strokeDasharray="5 5" />}
      <circle cx={cx} cy={cy} r={r} fill="var(--sky-soft)" stroke={has("sides") ? "var(--sky)" : "var(--ink-2)"} strokeWidth={has("sides") ? 3.5 : 2} />
      {has("symmetry") &&
        Array.from({ length: 8 }, (_, i) => {
          const a = (i * Math.PI) / 8;
          return <line key={i} x1={cx - (r + 18) * Math.cos(a)} y1={cy - (r + 18) * Math.sin(a)} x2={cx + (r + 18) * Math.cos(a)} y2={cy + (r + 18) * Math.sin(a)} stroke="var(--formal)" strokeWidth="1.6" strokeDasharray="8 5" opacity="0.8" />;
        })}
      {has("symmetry") && (
        <text x={cx + r + 8} y={28} fontSize="22" fontWeight="700" fill="var(--formal)" textAnchor="middle">
          ∞
        </text>
      )}
      <line x1={cx} y1={cy} x2={cx + r} y2={cy} stroke="var(--ink-2)" strokeWidth="1.8" />
      <text x={cx + r / 2} y={cy - 7} textAnchor="middle" fontSize="12" fill="var(--ink-2)" {...HALO}>
        {t("w.shapes.radius")}
      </text>
      <circle cx={cx} cy={cy} r="4" fill="var(--ink)" />
      <text x={cx} y={cy + 20} textAnchor="middle" fontSize="12" fill="var(--ink-2)" {...HALO}>
        {t("w.shapes.centre")}
      </text>
      {has("rotation") && (
        <g style={{ transform: `rotate(${turns * 45}deg)`, transformOrigin: `${cx}px ${cy}px`, transition: "transform .7s cubic-bezier(.3,1.2,.5,1)" }}>
          <circle cx={cx} cy={cy - r} r="7" fill="var(--gold)" stroke="var(--card)" strokeWidth="2" />
        </g>
      )}
    </g>
  );
}

/* ---------------------------------------------------------------- polygon mode */

function PolygonAngles({ initialN, showAnglesDefault }: { initialN: number; showAnglesDefault: boolean }) {
  const { t, n: fmt } = useI18n();
  const [n, setN] = useState(initialN);
  const [irregular, setIrregular] = useState(false);
  const [seed, setSeed] = useState(1);
  const [showAngles, setShowAngles] = useState(showAnglesDefault);

  const raw = useMemo(() => (irregular ? irregularPolygon(n, seed) : regularPolygon(n)), [n, irregular, seed]);
  const { points: P } = useMemo(() => fitToBox(raw, W, 270, 40), [raw]);
  const angles = useMemo(() => interiorAngles(raw), [raw]);
  const tris = fanTriangles(n);
  const sum = angleSum(n);
  const polyName = t(`w.shapes.polyName.${n}`);
  const fullName = t(irregular ? "w.shapes.poly.irregularName" : "w.shapes.poly.regularName", { name: polyName });
  const each = sum / n;
  const c = centroid(P);

  return (
    <div className="mt-4">
      <div className="grid gap-4 sm:grid-cols-[1fr_auto] sm:items-end">
        <label className="block">
          <span className="flex items-center justify-between text-sm font-semibold text-ink-2">
            {t("w.shapes.poly.n")}
            <span className="font-mono text-ink" dir="ltr">
              n = {n}
            </span>
          </span>
          <input type="range" min={3} max={12} value={n} onChange={(e) => setN(Number(e.target.value))} className="mt-1.5 w-full accent-[var(--gold)]" dir="ltr" />
        </label>
        <div className="flex flex-wrap gap-2">
          {([false, true] as const).map((irr) => (
            <button key={String(irr)} type="button" aria-pressed={irregular === irr} className={`btn btn-sm ${irregular === irr ? "btn-primary" : "btn-ghost"}`} onClick={() => setIrregular(irr)}>
              {t(irr ? "w.shapes.poly.irregular" : "w.shapes.poly.regular")}
            </button>
          ))}
          {irregular && (
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => setSeed((s) => s + 1)}>
              <Shuffle size={14} aria-hidden="true" /> {t("w.shapes.poly.reshape")}
            </button>
          )}
          <button type="button" aria-pressed={showAngles} className={`btn btn-sm ${showAngles ? "btn-gold" : "btn-ghost"}`} onClick={() => setShowAngles((v) => !v)}>
            {t("w.shapes.feature.angles")}
          </button>
        </div>
      </div>

      <div className="mt-4 grid items-start gap-5 md:grid-cols-[1.25fr_1fr]">
        <div dir="ltr">
          <svg viewBox={`0 0 ${W} 270`} className="w-full rounded-xl bg-paper-2/60" role="img" aria-label={`${fullName}: ${t("w.shapes.poly.aria", { t: n - 2 })}`}>
            {tris.map(([a, b, d], i) => (
              <polygon key={i} points={[P[a], P[b], P[d]].map((p) => `${p.x},${p.y}`).join(" ")} fill={i % 2 ? "var(--sky-soft)" : "var(--gold-soft)"} stroke="none" />
            ))}
            {tris.slice(0, -1).map(([a, , d]) => (
              <line key={`dg${d}`} x1={P[a].x} y1={P[a].y} x2={P[d].x} y2={P[d].y} stroke="var(--gold-ink)" strokeWidth="1.8" strokeDasharray="6 4" />
            ))}
            <polygon points={P.map((p) => `${p.x},${p.y}`).join(" ")} fill="none" stroke="var(--ink-2)" strokeWidth="2.5" strokeLinejoin="round" />
            {tris.map(([a, b, d], i) => {
              const g = centroid([P[a], P[b], P[d]]);
              return (
                <text key={`tn${i}`} x={g.x} y={g.y + 5} textAnchor="middle" fontSize={n > 9 ? 11 : 14} fontWeight="700" fill="var(--ink-2)">
                  {i + 1}
                </text>
              );
            })}
            {showAngles && P.map((p, i) => <AngleMark key={`pa${i}`} p={p} a={P[(i - 1 + n) % n]} b={P[(i + 1) % n]} value={angles[i]} label={n <= 5} color="var(--human)" />)}
            <circle cx={P[0].x} cy={P[0].y} r="6" fill="var(--gold)" stroke="var(--card)" strokeWidth="2" />
            {(() => {
              const u = unit(c, P[0]);
              return (
                <text x={P[0].x + 18 * u.x} y={P[0].y + 18 * u.y + 5} textAnchor="middle" fontSize="15" fontWeight="700" fontStyle="italic" fill="var(--ink)" className="font-serif">
                  A
                </text>
              );
            })()}
          </svg>
        </div>
        <div className="space-y-3 text-sm text-ink-2" aria-live="polite">
          <p className="font-serif text-xl font-semibold text-ink">{fullName}</p>
          <p>{n === 3 ? t("w.shapes.poly.triangle") : t("w.shapes.poly.cut", { d: fmt(n - 3), name: polyName, t: fmt(n - 2) })}</p>
          <p>{t("w.shapes.poly.sum")}</p>
          <p className="rounded-xl bg-paper-2 px-4 py-2.5 text-center font-serif text-xl text-ink" dir="ltr">
            ({n} − 2) × 180° = <strong>{sum}°</strong>
          </p>
          {!irregular ? (
            <p>
              {t("w.shapes.poly.each", { name: polyName })}{" "}
              <span className="whitespace-nowrap font-serif text-base text-ink" dir="ltr">
                {sum}° ÷ {n} {Number.isInteger(each) ? "=" : "≈"} {Number.isInteger(each) ? each : (Math.round(each * 10) / 10).toFixed(1)}°
              </span>
            </p>
          ) : (
            <p>
              {t("w.shapes.poly.measured")}{" "}
              <span className="font-serif text-ink" dir="ltr">
                {roundPreservingSum(angles, 1, sum)
                  .map((a) => `${a.toFixed(1)}°`)
                  .join(" + ")}{" "}
                = {sum}°
              </span>
            </p>
          )}
          <p className="text-xs text-muted">{t("w.shapes.poly.anyConvex")}</p>
        </div>
      </div>
    </div>
  );
}
