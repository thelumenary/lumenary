"use client";

import { Minus, Pause, PenLine, Play, Plus } from "lucide-react";
import { useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import { BOX, DEFAULT_PUNCTURES, LOOP_IDS, contourIntegral, cumulativeAngles, isLoopId, parsePunctures, presetLoop, resampleClosed, windingNumber, type LoopId } from "./lib/topo-winding";
import { TAU, clamp, len2, r2, sub2, type V2 } from "./lib/topo-vec";
import { svgPoint, useAnimationLoop } from "./lib/topo-dom";

const W = 400;
const K = W / (2 * BOX); // px per unit
/** World → screen, rounded so server and browser render identical markup. */
const S = (p: V2): V2 => [r2(W / 2 + p[0] * K), r2(W / 2 - p[1] * K)];
const toWorld = (q: V2): V2 => [(q[0] - W / 2) / K, (W / 2 - q[1]) / K];
const PCOL = ["var(--human)", "var(--compute)"];
const N = 360;
const SUB = ["₁", "₂"];

const fmtSigned = (x: number, d = 3) => (x < 0 ? `−${(-x).toFixed(d)}` : x.toFixed(d));
const fmtInt = (x: number) => (x < 0 ? `−${-x}` : `${x}`);

export interface WindingNumberProps {
  punctures?: [number, number][];
  loop?: LoopId;
  loops?: LoopId[];
  title?: string;
  subtitle?: string;
}

/**
 * Winding numbers in the punctured plane: preset or hand-drawn loops, one or
 * two draggable punctures, a radius vector that sweeps out the angle, and the
 * link to π₁ and to the contour integral ∮ dz/(z − a).
 */
export function WindingNumber({ punctures, loop, loops, title, subtitle }: WindingNumberProps) {
  const { t, n } = useI18n();
  const presets = useMemo<LoopId[]>(() => {
    const list = Array.isArray(loops) ? LOOP_IDS.filter((l) => loops.includes(l)) : [];
    return list.length ? list : [...LOOP_IDS];
  }, [loops]);
  const [pts, setPts] = useState<V2[]>(() => parsePunctures(punctures) ?? [DEFAULT_PUNCTURES[0]]);
  const [which, setWhich] = useState<LoopId | "custom">(isLoopId(loop) && presets.includes(loop) ? loop : presets[0]);
  const [custom, setCustom] = useState<V2[] | null>(null);
  const [drawing, setDrawing] = useState(false);
  const [stroke, setStroke] = useState<V2[] | null>(null);
  const [u, setU] = useState(0);
  const [playing, setPlaying] = useState(false);
  const svgRef = useRef<SVGSVGElement>(null);
  const drag = useRef<{ kind: "puncture"; i: number; pid: number } | { kind: "draw"; pid: number } | null>(null);

  const curve = useMemo(() => (which === "custom" && custom ? custom : presetLoop(which === "custom" ? presets[0] : which, N)), [which, custom, presets]);
  const results = pts.map((p) => ({
    w: windingNumber(curve, p),
    integral: contourIntegral(curve, p),
    cum: cumulativeAngles(curve, p),
  }));

  // one trip around the loop takes 6 seconds; stop at the end so the final total is the winding number
  useAnimationLoop(playing, (dt) => {
    const nx = u + dt / 6;
    if (nx >= 1) {
      setU(1);
      setPlaying(false);
    } else setU(nx);
  });

  // moving point and the angle swept so far
  const pos = u * curve.length;
  const i0 = Math.min(curve.length - 1, Math.floor(pos));
  const f = pos - i0;
  const a = curve[i0];
  const b = curve[(i0 + 1) % curve.length];
  const mover: V2 = [a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f];

  const setPreset = (id: LoopId) => {
    setWhich(id);
    setDrawing(false);
    setU(0);
    setPlaying(false);
  };

  const onDown = (e: React.PointerEvent<SVGSVGElement>) => {
    if (!drawing) return;
    const q = svgPoint(svgRef.current, e.clientX, e.clientY);
    if (!q) return;
    drag.current = { kind: "draw", pid: e.pointerId };
    svgRef.current?.setPointerCapture(e.pointerId);
    setStroke([toWorld(q)]);
    setPlaying(false);
  };
  const onMove = (e: React.PointerEvent<SVGSVGElement>) => {
    const d = drag.current;
    if (!d || d.pid !== e.pointerId) return;
    const q = svgPoint(svgRef.current, e.clientX, e.clientY);
    if (!q) return;
    const w: V2 = [clamp(toWorld(q)[0], -BOX + 0.1, BOX - 0.1), clamp(toWorld(q)[1], -BOX + 0.1, BOX - 0.1)];
    if (d.kind === "puncture") setPts((ps) => ps.map((p, j) => (j === d.i ? [clamp(w[0], -BOX + 0.3, BOX - 0.3), clamp(w[1], -BOX + 0.3, BOX - 0.3)] : p)));
    else setStroke((s) => (s && len2(sub2(w, s[s.length - 1])) > 0.06 ? [...s, w] : s));
  };
  const onUp = () => {
    const d = drag.current;
    drag.current = null;
    if (d?.kind === "draw") {
      if (stroke && stroke.length >= 6) {
        setCustom(resampleClosed(stroke, N));
        setWhich("custom");
        setDrawing(false);
        setU(0);
      }
      setStroke(null);
    }
  };

  // direction arrows along the loop
  const arrows = [0.125, 0.375, 0.625, 0.875].map((fr) => {
    const k = Math.floor(fr * curve.length);
    const p = S(curve[k]);
    const q = S(curve[(k + 2) % curve.length]);
    return { p, ang: (Math.atan2(q[1] - p[1], q[0] - p[0]) * 180) / Math.PI };
  });
  const loopD = curve.map((p, k) => `${k ? "L" : "M"}${r2(S(p)[0])} ${r2(S(p)[1])}`).join("") + "Z";

  return (
    <WidgetFrame title={title ?? t("w.winding.title")} subtitle={subtitle ?? t("w.winding.subtitle")}>
      <div className="flex flex-wrap gap-1.5" role="group" aria-label={t("w.winding.chooseLoop")}>
        {presets.map((id) => (
          <button key={id} type="button" aria-pressed={which === id && !drawing} className={`btn btn-sm ${which === id && !drawing ? "btn-primary" : "btn-ghost"}`} onClick={() => setPreset(id)}>
            {t(`w.winding.loop.${id}`)}
          </button>
        ))}
        <button type="button" aria-pressed={drawing || which === "custom"} className={`btn btn-sm ${drawing || which === "custom" ? "btn-primary" : "btn-ghost"}`} onClick={() => setDrawing((v) => !v)}>
          <PenLine size={14} aria-hidden="true" /> {t("w.winding.draw")}
        </button>
      </div>
      <div className="mt-4 grid gap-5 md:grid-cols-[1.1fr_1fr]">
        <div>
          <div dir="ltr" className="mx-auto max-w-[420px]">
            <svg
              ref={svgRef}
              viewBox={`0 0 ${W} ${W}`}
              className={`w-full touch-none select-none rounded-2xl border bg-paper-2/60 ${drawing ? "cursor-crosshair border-gold" : "border-line"}`}
              role="group"
              aria-label={t("w.winding.diagram")}
              onPointerDown={onDown}
              onPointerMove={onMove}
              onPointerUp={onUp}
              onPointerCancel={onUp}
            >
              {Array.from({ length: 2 * BOX + 1 }, (_, k) => k - BOX).map((v) => (
                <g key={v}>
                  <line x1={S([v, 0])[0]} y1={0} x2={S([v, 0])[0]} y2={W} stroke="var(--line)" strokeWidth={v === 0 ? 1.2 : 0.6} />
                  <line x1={0} y1={S([0, v])[1]} x2={W} y2={S([0, v])[1]} stroke="var(--line)" strokeWidth={v === 0 ? 1.2 : 0.6} />
                </g>
              ))}
              {!stroke && (
                <>
                  <path d={loopD} fill="var(--formal)" fillOpacity={0.05} stroke="var(--formal)" strokeWidth={2.6} strokeLinejoin="round" />
                  {arrows.map((ar, k) => (
                    <path key={k} d="M-6 -5 L4 0 L-6 5" transform={`translate(${r2(ar.p[0])} ${r2(ar.p[1])}) rotate(${r2(ar.ang)})`} fill="none" stroke="var(--formal)" strokeWidth={2.4} strokeLinecap="round" strokeLinejoin="round" />
                  ))}
                  <rect x={S(curve[0])[0] - 4} y={S(curve[0])[1] - 4} width={8} height={8} fill="var(--card)" stroke="var(--formal)" strokeWidth={2} />
                </>
              )}
              {stroke && stroke.length > 1 && (
                <>
                  <path d={stroke.map((p, k) => `${k ? "L" : "M"}${r2(S(p)[0])} ${r2(S(p)[1])}`).join("")} fill="none" stroke="var(--gold)" strokeWidth={2.6} strokeLinecap="round" strokeLinejoin="round" />
                  <line x1={S(stroke[stroke.length - 1])[0]} y1={S(stroke[stroke.length - 1])[1]} x2={S(stroke[0])[0]} y2={S(stroke[0])[1]} stroke="var(--gold)" strokeWidth={1.5} strokeDasharray="4 4" />
                </>
              )}
              {/* radius vectors and swept-angle spirals */}
              {!stroke &&
                pts.map((p, k) => {
                  const cum = results[k].cum;
                  const swept = cum[i0] + (cum[Math.min(cum.length - 1, i0 + 1)] - cum[i0]) * f;
                  const a0 = Math.atan2(curve[0][1] - p[1], curve[0][0] - p[0]);
                  const steps = Math.max(2, Math.ceil(Math.abs(swept) / 0.08));
                  const spiral: string[] = [];
                  for (let s = 0; s <= steps; s++) {
                    const phi = (swept * s) / steps;
                    const r = 0.55 + (0.22 * Math.abs(phi)) / TAU;
                    const q = S([p[0] + r * Math.cos(a0 + phi), p[1] + r * Math.sin(a0 + phi)]);
                    spiral.push(`${s ? "L" : "M"}${r2(q[0])} ${r2(q[1])}`);
                  }
                  return (
                    <g key={k}>
                      <line x1={S(p)[0]} y1={S(p)[1]} x2={S(mover)[0]} y2={S(mover)[1]} stroke={PCOL[k]} strokeWidth={1.8} strokeDasharray="5 3" />
                      {u > 0 && <path d={spiral.join("")} fill="none" stroke={PCOL[k]} strokeWidth={2.2} strokeLinecap="round" />}
                    </g>
                  );
                })}
              {!stroke && <circle cx={S(mover)[0]} cy={S(mover)[1]} r={6} fill="var(--gold)" stroke="var(--card)" strokeWidth={2} />}
              {pts.map((p, k) => (
                <g
                  key={k}
                  role="button"
                  tabIndex={0}
                  aria-label={t("w.winding.puncture", { k: n(k + 1) })}
                  className="cursor-grab outline-none active:cursor-grabbing [&:focus-visible>circle:first-of-type]:stroke-[var(--sky)]"
                  onPointerDown={(e) => {
                    e.stopPropagation();
                    drag.current = { kind: "puncture", i: k, pid: e.pointerId };
                    svgRef.current?.setPointerCapture(e.pointerId);
                  }}
                  onKeyDown={(e) => {
                    const st = e.shiftKey ? 0.5 : 0.1;
                    const m: Record<string, V2> = { ArrowLeft: [-st, 0], ArrowRight: [st, 0], ArrowUp: [0, st], ArrowDown: [0, -st] };
                    const d = m[e.key];
                    if (!d) return;
                    e.preventDefault();
                    setPts((ps) => ps.map((q, j) => (j === k ? [clamp(q[0] + d[0], -BOX + 0.3, BOX - 0.3), clamp(q[1] + d[1], -BOX + 0.3, BOX - 0.3)] : q)));
                  }}
                >
                  <circle cx={S(p)[0]} cy={S(p)[1]} r={9} fill="var(--card)" stroke={PCOL[k]} strokeWidth={3} />
                  <circle cx={S(p)[0]} cy={S(p)[1]} r={20} fill="transparent" />
                  <text x={S(p)[0] + 12} y={S(p)[1] - 11} fontSize="15" fontStyle="italic" fontWeight={700} fill={PCOL[k]} stroke="var(--card)" strokeWidth={3} paintOrder="stroke" style={{ fontFamily: "var(--font-serif)" }}>
                    p{SUB[k]}
                  </text>
                </g>
              ))}
            </svg>
          </div>
          <p className="mt-2 text-xs text-muted">{drawing ? t("w.winding.drawHint") : t("w.winding.hint")}</p>
          <div className="mt-2 flex flex-wrap items-center gap-2">
            <button
              type="button"
              className="btn btn-sm btn-gold"
              aria-pressed={playing}
              onClick={() => {
                if (!playing && u >= 1) setU(0);
                setPlaying((v) => !v);
              }}
            >
              {playing ? <Pause size={14} aria-hidden="true" /> : <Play size={14} aria-hidden="true" />} {playing ? t("w.winding.pause") : t("w.winding.play")}
            </button>
            <label className="flex min-w-40 flex-1 items-center gap-2 text-xs font-semibold text-ink-2">
              {t("w.winding.along")}
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
          </div>
          <div className="mt-2">
            {pts.length < 2 ? (
              <button type="button" className="btn btn-sm btn-ghost" onClick={() => setPts((ps) => [...ps, ps[0][0] > 0 ? DEFAULT_PUNCTURES[0] : DEFAULT_PUNCTURES[1]])}>
                <Plus size={14} aria-hidden="true" /> {t("w.winding.addHole")}
              </button>
            ) : (
              <button type="button" className="btn btn-sm btn-ghost" onClick={() => setPts((ps) => ps.slice(0, 1))}>
                <Minus size={14} aria-hidden="true" /> {t("w.winding.removeHole")}
              </button>
            )}
          </div>
        </div>

        <div className="space-y-3">
          <div aria-live="polite" className="space-y-2">
            {pts.map((p, k) => {
              const r = results[k];
              return (
                <div key={k} className="rounded-xl bg-paper-2 px-4 py-3">
                  <p className="flex flex-wrap items-baseline justify-between gap-x-3">
                    <span className="text-sm font-semibold text-ink-2">
                      <span className="me-1.5 inline-block h-2.5 w-2.5 rounded-full align-middle" style={{ background: PCOL[k] }} aria-hidden="true" />
                      {t("w.winding.around", { p: `p${SUB[k]}` })}
                    </span>
                    <span className="font-serif text-3xl text-ink" dir="ltr">
                      {r.w === null ? "—" : fmtInt(r.w)}
                    </span>
                  </p>
                  {r.w === null ? (
                    <p className="mt-1 text-sm text-bad">{t("w.winding.through", { p: `p${SUB[k]}` })}</p>
                  ) : (
                    <p className="mt-1 font-mono text-xs text-ink-2" dir="ltr">
                      (1/2πi)∮ dz/(z − p{SUB[k]}) ≈ {fmtSigned(Math.abs(r.integral[0]) < 5e-4 ? 0 : r.integral[0])} {r.integral[1] < -5e-4 ? "−" : "+"} {Math.abs(r.integral[1]).toFixed(3)}i
                    </p>
                  )}
                </div>
              );
            })}
          </div>
          <div className="text-sm text-ink-2">
            <p>{t("w.winding.swept")}</p>
            <p className="mt-1 flex flex-wrap gap-x-5 font-mono text-ink" dir="ltr">
              {pts.map((p, k) => {
                const cum = results[k].cum;
                const swept = cum[i0] + (cum[Math.min(cum.length - 1, i0 + 1)] - cum[i0]) * f;
                return (
                  <span key={k}>
                    <span style={{ color: PCOL[k] }}>p{SUB[k]}</span>: {fmtSigned(swept / TAU, 2)}
                  </span>
                );
              })}
            </p>
          </div>
          <p className="text-sm text-ink-2">{t("w.winding.howComputed")}</p>
          <p className="rounded-xl bg-gold-soft px-4 py-3 text-sm text-ink">{pts.length > 1 ? t("w.winding.twoHoles") : t("w.winding.homotopy")}</p>
          <p className="text-sm text-ink-2">{t("w.winding.complex")}</p>
        </div>
      </div>
    </WidgetFrame>
  );
}
