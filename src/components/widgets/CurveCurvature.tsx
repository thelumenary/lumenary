"use client";

import { Pause, Play } from "lucide-react";
import { useId, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { CURVES, CURVE_IDS, PARAM_RANGES, frameAt, isCurveId, sampleCurve, sanitizeParams, type CurveId, type CurveParams, type NumericParam } from "./lib/topo-curves";
import { TAU, clamp, r2, type V2 } from "./lib/topo-vec";
import { svgPoint, useAnimationLoop } from "./lib/topo-dom";

const W = 480;
const H = 360;
const XR = 3.6;
const YR = 2.7;
const KX = W / (2 * XR);
/** World → screen, rounded so server and browser render identical markup. */
const S = (p: V2): V2 => [r2(W / 2 + p[0] * KX), r2(H / 2 - p[1] * KX)];
const toWorld = (q: V2): V2 => [(q[0] - W / 2) / KX, (H / 2 - q[1]) / KX];

const SLIDER: Partial<Record<CurveId, NumericParam>> = { circle: "R", ellipse: "b", parabola: "k", limacon: "c" };

const sgn = (x: number, d = 3) => (Number.isFinite(x) ? (x < 0 ? `−${(-x).toFixed(d)}` : x.toFixed(d)) : "—");

export interface CurveCurvatureProps {
  curve?: CurveId;
  curves?: CurveId[];
  showOsculating?: boolean;
  params?: Partial<CurveParams>;
  title?: string;
  subtitle?: string;
}

/**
 * Curvature of plane curves: a point travels along the curve with its unit
 * tangent, normal and osculating circle; the signed curvature κ(s) is graphed
 * against arc length, and for closed curves ∫ κ ds = 2π × turning number.
 */
export function CurveCurvature({ curve, curves, showOsculating = true, params, title, subtitle }: CurveCurvatureProps) {
  const { t, n } = useI18n();
  const allowed = useMemo<CurveId[]>(() => {
    const list = Array.isArray(curves) ? CURVE_IDS.filter((c) => curves.includes(c)) : [];
    return list.length ? list : [...CURVE_IDS];
  }, [curves]);
  const [id, setId] = useState<CurveId>(isCurveId(curve) && allowed.includes(curve) ? curve : allowed[0]);
  const [prm, setPrm] = useState<CurveParams>(() => sanitizeParams(params && typeof params === "object" ? params : {}));
  const [u, setU] = useState(0.12);
  const [playing, setPlaying] = useState(false);
  const [osc, setOsc] = useState(showOsculating !== false);
  const svgRef = useRef<SVGSVGElement>(null);
  const drag = useRef<{ i: number; pid: number } | null>(null);
  const clipId = useId().replace(/:/g, "");

  const def = CURVES[id];
  const smp = useMemo(() => sampleCurve(def, prm), [def, prm]);
  const fr = frameAt(def, prm, smp, u);
  const kappa = fr.kappa;
  const radius = Number.isFinite(kappa) && Math.abs(kappa) > 1e-9 ? 1 / Math.abs(kappa) : Infinity;
  const turns = smp.totalCurvature / TAU;
  const sliderKey = SLIDER[id];

  useAnimationLoop(playing, (dt) => setU((x) => (x + dt / 9) % 1));

  // curve and κ(s) graph paths (every 4th sample is plenty for drawing)
  const step = 4;
  const curveD = smp.r.filter((_, i) => i % step === 0 || i === smp.r.length - 1).map((p, i) => `${i ? "L" : "M"}${r2(S(p)[0])} ${r2(S(p)[1])}`).join("");
  const sorted = smp.kappa.map(Math.abs).sort((a, b) => a - b);
  // scale the graph to the whole curve, except that the spike at a cusp (κ → ∞) is cut off
  const kmax = Math.max(0.6, smp.singular ? 1.3 * sorted[Math.floor(sorted.length * 0.9)] : 1.1 * sorted[sorted.length - 1]);
  const G = { x0: 46, x1: 468, y0: 14, y1: 146 };
  const gx = (s: number) => G.x0 + (smp.length > 0 ? (s / smp.length) * (G.x1 - G.x0) : 0);
  const gy = (k: number) => (G.y0 + G.y1) / 2 - (clamp(k, -kmax * 1.05, kmax * 1.05) / kmax) * ((G.y1 - G.y0) / 2);
  const idx = smp.s.map((_, i) => i).filter((i) => i % step === 0 || i === smp.s.length - 1);
  const graphD = idx.map((i, j) => `${j ? "L" : "M"}${r2(gx(smp.s[i]))} ${r2(gy(smp.kappa[i]))}`).join("");
  const area = (sign: 1 | -1) =>
    `M${r2(gx(0))} ${r2(gy(0))}` + idx.map((i) => `L${r2(gx(smp.s[i]))} ${r2(gy(sign > 0 ? Math.max(0, smp.kappa[i]) : Math.min(0, smp.kappa[i])))}`).join("") + `L${r2(gx(smp.length))} ${r2(gy(0))}Z`;

  // osculating circle (or tangent line when the curvature is ~0)
  const centre: V2 | null = Number.isFinite(radius) && radius < 40 ? [fr.r[0] + fr.N[0] / kappa, fr.r[1] + fr.N[1] / kappa] : null;
  const P = S(fr.r);
  const arrow = (v: V2, len: number): V2 => S([fr.r[0] + v[0] * len, fr.r[1] + v[1] * len]);

  let total: string;
  if (!def.closed) total = t("w.curvature.openTotal", { deg: n(Math.round((smp.totalCurvature * 180) / Math.PI)) });
  else if (smp.singular) total = t("w.curvature.cusp");
  else total = t("w.curvature.closedTotal", { k: n(Math.round(turns)) });

  return (
    <WidgetFrame title={title ?? t("w.curvature.title")} subtitle={subtitle ?? t("w.curvature.subtitle")}>
      {allowed.length > 1 && (
        <div className="flex flex-wrap gap-1.5" role="group" aria-label={t("w.curvature.choose")}>
          {allowed.map((c) => (
            <button
              key={c}
              type="button"
              aria-pressed={id === c}
              className={`btn btn-sm ${id === c ? "btn-primary" : "btn-ghost"}`}
              onClick={() => {
                setId(c);
              }}
            >
              {t(`w.curvature.curve.${c}`)}
            </button>
          ))}
        </div>
      )}
      <div className="mt-4 grid gap-5 md:grid-cols-[1.25fr_1fr]">
        <div>
          <div dir="ltr">
            <svg
              ref={svgRef}
              viewBox={`0 0 ${W} ${H}`}
              className="w-full touch-none select-none rounded-2xl border border-line bg-paper-2/60"
              role="group"
              aria-label={t("w.curvature.diagram", { name: t(`w.curvature.curve.${id}`) })}
              onPointerMove={(e) => {
                const d = drag.current;
                if (!d || d.pid !== e.pointerId) return;
                const q = svgPoint(svgRef.current, e.clientX, e.clientY);
                if (!q) return;
                const w = toWorld(q);
                setPrm((p) => sanitizeParams({ ...p, ctrl: p.ctrl.map((c, j) => (j === d.i ? [w[0], w[1]] : c)) as CurveParams["ctrl"] }));
              }}
              onPointerUp={() => (drag.current = null)}
              onPointerCancel={() => (drag.current = null)}
            >
              <defs>
                <clipPath id={clipId}>
                  <rect x={0} y={0} width={W} height={H} rx={16} />
                </clipPath>
              </defs>
              <g clipPath={`url(#${clipId})`}>
                {Array.from({ length: 7 }, (_, i) => i - 3).map((x) => (
                  <line key={`x${x}`} x1={S([x, 0])[0]} y1={0} x2={S([x, 0])[0]} y2={H} stroke="var(--line)" strokeWidth={x === 0 ? 1.1 : 0.6} />
                ))}
                {Array.from({ length: 5 }, (_, i) => i - 2).map((y) => (
                  <line key={`y${y}`} x1={0} y1={S([0, y])[1]} x2={W} y2={S([0, y])[1]} stroke="var(--line)" strokeWidth={y === 0 ? 1.1 : 0.6} />
                ))}
                {id === "bezier" && (
                  <path d={prm.ctrl.map((c, i) => `${i ? "L" : "M"}${r2(S(c)[0])} ${r2(S(c)[1])}`).join("")} fill="none" stroke="var(--muted)" strokeWidth={1.2} strokeDasharray="4 4" />
                )}
                <path d={curveD} fill="none" stroke="var(--ink)" strokeWidth={2.6} strokeLinejoin="round" strokeLinecap="round" />
                {osc &&
                  (centre ? (
                    <g>
                      <circle cx={r2(S(centre)[0])} cy={r2(S(centre)[1])} r={r2(radius * KX)} fill="var(--gold)" fillOpacity={0.06} stroke="var(--gold)" strokeWidth={1.8} strokeDasharray="6 4" />
                      <line x1={r2(P[0])} y1={r2(P[1])} x2={r2(S(centre)[0])} y2={r2(S(centre)[1])} stroke="var(--gold-ink)" strokeWidth={1.2} />
                      <circle cx={r2(S(centre)[0])} cy={r2(S(centre)[1])} r={3.5} fill="var(--gold-ink)" />
                    </g>
                  ) : (
                    <line x1={r2(arrow(fr.T, -40)[0])} y1={r2(arrow(fr.T, -40)[1])} x2={r2(arrow(fr.T, 40)[0])} y2={r2(arrow(fr.T, 40)[1])} stroke="var(--gold)" strokeWidth={1.8} strokeDasharray="6 4" />
                  ))}
                <Arrow from={P} to={arrow(fr.T, 0.9)} colour="var(--human)" label="T" />
                <Arrow from={P} to={arrow(fr.N, 0.9)} colour="var(--compute)" label="N" />
                <circle cx={r2(P[0])} cy={r2(P[1])} r={6} fill="var(--ink)" stroke="var(--card)" strokeWidth={2} />
              </g>
              {id === "bezier" &&
                prm.ctrl.map((c, i) => (
                  <g
                    key={i}
                    role="button"
                    tabIndex={0}
                    aria-label={t("w.curvature.handle", { k: n(i + 1) })}
                    className="cursor-grab outline-none active:cursor-grabbing [&:focus-visible>rect:first-of-type]:stroke-[var(--sky)]"
                    onPointerDown={(e) => {
                      drag.current = { i, pid: e.pointerId };
                      svgRef.current?.setPointerCapture(e.pointerId);
                    }}
                    onKeyDown={(e) => {
                      const st = e.shiftKey ? 0.4 : 0.1;
                      const m: Record<string, V2> = { ArrowLeft: [-st, 0], ArrowRight: [st, 0], ArrowUp: [0, st], ArrowDown: [0, -st] };
                      const d = m[e.key];
                      if (!d) return;
                      e.preventDefault();
                      setPrm((p) => sanitizeParams({ ...p, ctrl: p.ctrl.map((q, j) => (j === i ? [q[0] + d[0], q[1] + d[1]] : q)) as CurveParams["ctrl"] }));
                    }}
                  >
                    <rect x={r2(S(c)[0] - 7)} y={r2(S(c)[1] - 7)} width={14} height={14} rx={3} fill="var(--card)" stroke="var(--formal)" strokeWidth={2.4} />
                    <circle cx={r2(S(c)[0])} cy={r2(S(c)[1])} r={20} fill="transparent" />
                  </g>
                ))}
            </svg>
          </div>
          <div className="mt-3 flex flex-wrap items-center gap-2">
            <button type="button" className="btn btn-sm btn-gold" aria-pressed={playing} onClick={() => setPlaying((v) => !v)}>
              {playing ? <Pause size={14} aria-hidden="true" /> : <Play size={14} aria-hidden="true" />} {playing ? t("w.curvature.pause") : t("w.curvature.play")}
            </button>
            <label className="flex min-w-40 flex-1 items-center gap-2 text-xs font-semibold text-ink-2">
              {t("w.curvature.along")}
              <input
                type="range"
                min={0}
                max={1000}
                value={Math.round(u * 1000)}
                onChange={(e) => {
                  setPlaying(false);
                  setU(Number(e.target.value) / 1000);
                }}
                className="w-full accent-[var(--gold)]"
                dir="ltr"
              />
            </label>
            <button type="button" className={`btn btn-sm ${osc ? "btn-primary" : "btn-ghost"}`} aria-pressed={osc} onClick={() => setOsc((v) => !v)}>
              {t("w.curvature.osculating")}
            </button>
          </div>
          {sliderKey && (
            <label className="mt-3 block text-sm font-semibold text-ink-2">
              <span className="flex items-center justify-between">
                {t(`w.curvature.param.${sliderKey}`)}
                <span className="font-mono text-ink" dir="ltr">
                  {prm[sliderKey].toFixed(2)}
                </span>
              </span>
              <input
                type="range"
                min={PARAM_RANGES[sliderKey][0]}
                max={PARAM_RANGES[sliderKey][1]}
                step={PARAM_RANGES[sliderKey][2]}
                value={prm[sliderKey]}
                onChange={(e) => setPrm((p) => sanitizeParams({ ...p, [sliderKey]: Number(e.target.value) }))}
                className="mt-1.5 w-full accent-[var(--formal)]"
                dir="ltr"
              />
            </label>
          )}
          {id === "bezier" && <p className="mt-2 text-xs text-muted">{t("w.curvature.bezierHint")}</p>}
        </div>

        <div className="space-y-3">
          <dl className="grid grid-cols-2 gap-2 text-center" aria-live="polite">
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.curvature.kappa")}</dt>
              <dd className="font-mono text-lg text-ink" dir="ltr">
                κ = {Number.isFinite(kappa) ? sgn(kappa, 3) : "—"}
              </dd>
            </div>
            <div className="rounded-xl bg-paper-2 px-2 py-2">
              <dt className="text-xs font-semibold text-ink-2">{t("w.curvature.radius")}</dt>
              <dd className="font-mono text-lg text-ink" dir="ltr">
                1/|κ| = {Number.isFinite(radius) ? (radius > 999 ? "∞" : radius.toFixed(3)) : Number.isFinite(kappa) ? "∞" : "—"}
              </dd>
            </div>
          </dl>
          <p className="text-sm text-ink-2">{t("w.curvature.signNote")}</p>
          <div className="rounded-xl bg-gold-soft px-4 py-3">
            <p className="font-serif text-lg text-ink" dir="ltr">
              ∫ κ ds = {sgn(smp.totalCurvature, 3)} = {sgn(turns, 3)} × 2π
            </p>
            <p className="mt-1 text-sm text-ink">{total}</p>
          </div>
          {def.closed && !smp.singular && <p className="text-xs text-muted">{t("w.curvature.umlaufsatz")}</p>}
          {smp.singular && id === "bezier" && <p className="text-xs text-muted">{t("w.curvature.bezierCusp")}</p>}
          <p className="text-xs text-muted">{t("w.curvature.numeric")}</p>
        </div>
      </div>

      <div className="mt-5" dir="ltr">
        <p className="mb-1 text-sm font-semibold text-ink-2" dir="auto">
          {t("w.curvature.graph")}
        </p>
        <svg viewBox="0 0 480 160" className="w-full rounded-xl border border-line bg-card" role="img" aria-label={t("w.curvature.graphLabel", { name: t(`w.curvature.curve.${id}`) })}>
          <defs>
            <clipPath id={`${clipId}-g`}>
              <rect x={G.x0} y={G.y0 - 2} width={G.x1 - G.x0} height={G.y1 - G.y0 + 4} />
            </clipPath>
          </defs>
          <line x1={G.x0} y1={gy(0)} x2={G.x1} y2={gy(0)} stroke="var(--line-2)" strokeWidth={1} />
          <line x1={G.x0} y1={G.y0} x2={G.x0} y2={G.y1} stroke="var(--line-2)" strokeWidth={1} />
          <g clipPath={`url(#${clipId}-g)`}>
            <path d={area(1)} fill="var(--compute)" fillOpacity={0.16} />
            <path d={area(-1)} fill="var(--human)" fillOpacity={0.16} />
            <path d={graphD} fill="none" stroke="var(--ink)" strokeWidth={1.8} strokeLinejoin="round" />
          </g>
          <line x1={r2(gx(fr.s))} y1={G.y0} x2={r2(gx(fr.s))} y2={G.y1} stroke="var(--gold)" strokeWidth={1.4} />
          <circle cx={r2(gx(fr.s))} cy={r2(gy(Number.isFinite(kappa) ? kappa : 0))} r={4.5} fill="var(--gold)" stroke="var(--card)" strokeWidth={1.5} />
          <text x={G.x0 - 6} y={G.y0 + 8} textAnchor="end" fontSize="10" fill="var(--muted)">
            {kmax.toFixed(1)}
          </text>
          <text x={G.x0 - 6} y={gy(0) + 4} textAnchor="end" fontSize="10" fill="var(--muted)">
            0
          </text>
          <text x={G.x0 - 6} y={G.y1} textAnchor="end" fontSize="10" fill="var(--muted)">
            −{kmax.toFixed(1)}
          </text>
          <text x={14} y={(G.y0 + G.y1) / 2 - 14} fontSize="13" fontStyle="italic" fill="var(--ink-2)" style={{ fontFamily: "var(--font-serif)" }}>
            κ
          </text>
          <text x={G.x1} y={158} textAnchor="end" fontSize="10" fill="var(--muted)">
            s = {smp.length.toFixed(2)}
          </text>
          <text x={G.x0} y={158} fontSize="10" fill="var(--muted)">
            s = 0
          </text>
        </svg>
        <p className="mt-1 text-xs text-muted" dir="auto">
          {t("w.curvature.graphNote")}
        </p>
      </div>
    </WidgetFrame>
  );
}

function Arrow({ from, to, colour, label }: { from: V2; to: V2; colour: string; label: string }) {
  const dx = to[0] - from[0];
  const dy = to[1] - from[1];
  const L = Math.hypot(dx, dy) || 1;
  const ux = dx / L;
  const uy = dy / L;
  const h1: V2 = [to[0] - ux * 10 - uy * 5.5, to[1] - uy * 10 + ux * 5.5];
  const h2: V2 = [to[0] - ux * 10 + uy * 5.5, to[1] - uy * 10 - ux * 5.5];
  return (
    <g>
      <line x1={r2(from[0])} y1={r2(from[1])} x2={r2(to[0] - ux * 4)} y2={r2(to[1] - uy * 4)} stroke={colour} strokeWidth={2.6} strokeLinecap="round" />
      <path d={`M${r2(h1[0])} ${r2(h1[1])}L${r2(to[0])} ${r2(to[1])}L${r2(h2[0])} ${r2(h2[1])}Z`} fill={colour} />
      <text x={r2(to[0] + ux * 11)} y={r2(to[1] + uy * 11 + 5)} textAnchor="middle" fontSize="14" fontWeight={700} fontStyle="italic" fill={colour} stroke="var(--card)" strokeWidth={3} paintOrder="stroke" style={{ fontFamily: "var(--font-serif)" }}>
        {label}
      </text>
    </g>
  );
}
