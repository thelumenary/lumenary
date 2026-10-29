"use client";

import { ArrowDown, ArrowLeft, ArrowRight, ArrowUp, Check, RotateCcw } from "lucide-react";
import { useId, useMemo, useRef, useState } from "react";
import { useI18n } from "@/i18n/client";
import { WidgetFrame } from "./WidgetFrame";
import {
  clampDisk,
  fromLatLon,
  greatArc,
  hypAngles,
  hypAreaNumeric,
  hypEndpoints,
  geodesic,
  hypTangent,
  planeAngles,
  sphereAngles,
  sphereAreaNumeric,
  sphereMesh,
  sphereTangent,
  toLatLon,
} from "./lib/topo-curvedtri";
import { add3, apply3, clamp, DEG, dot3, dragRotate, isNum, len2, mul3, norm2, norm3, r2, rotX, rotY, scale3, sub2, sub3, transpose3, type M3, type V2, type V3 } from "./lib/topo-vec";
import { svgPoint } from "./lib/topo-dom";

type Mode = "plane" | "sphere" | "hyperbolic";
const MODES: Mode[] = ["plane", "sphere", "hyperbolic"];
const NAMES = ["A", "B", "C"] as const;
const PI = Math.PI;

const DEFAULTS: { plane: V2[]; sphere: [number, number][]; hyperbolic: V2[] } = {
  plane: [[-3.1, -2], [3.3, -1.5], [0.2, 2.7]],
  sphere: [[52, -14], [-2, -36], [6, 30]],
  hyperbolic: [[-0.58, -0.36], [0.62, -0.3], [0.04, 0.64]],
};
const PRESETS = {
  plane: { equilateral: [[-2.6, -2], [2.6, -2], [0, 2.5]] as V2[], right: [[-3, -2.2], [3, -2.2], [-3, 2.4]] as V2[], obtuse: [[-4.3, -1.6], [4.3, -1.2], [-2.2, 1.1]] as V2[] },
  sphere: { small: [[24, -6], [15, 5], [28, 8]] as [number, number][], octant: [[90, 0], [0, 0], [0, 90]] as [number, number][], big: [[58, -62], [-38, -18], [8, 72]] as [number, number][] },
  hyperbolic: { small: [[-0.09, -0.06], [0.1, -0.05], [0.0, 0.1]] as V2[], medium: DEFAULTS.hyperbolic, large: [[0.9, 0], [-0.45, 0.78], [-0.45, -0.78]] as V2[] },
};

const PLANE_BOX = { x: 5.4, y: 3.9 };
const clampPlane = (p: V2): V2 => [clamp(p[0], -PLANE_BOX.x + 0.25, PLANE_BOX.x - 0.25), clamp(p[1], -PLANE_BOX.y + 0.25, PLANE_BOX.y - 0.25)];

/** World (x toward lon 0, z north) → view basis: east to the right, north up, lon 0 toward the viewer. */
const BASE: M3 = [0, 1, 0, 0, 0, 1, 1, 0, 0];
function viewCentredOn(v: V3): M3 {
  const [lat, lon] = toLatLon(v);
  return mul3(mul3(rotX((lat * PI) / 180), rotY((-lon * PI) / 180)), BASE);
}

const isPair = (p: unknown): p is [number, number] => Array.isArray(p) && p.length >= 2 && isNum(p[0]) && isNum(p[1]);
function parseTriple(v: unknown): [number, number][] | null {
  return Array.isArray(v) && v.length >= 3 && v.slice(0, 3).every(isPair) ? (v.slice(0, 3).map((p) => [p[0], p[1]]) as [number, number][]) : null;
}

function initialVertices(vertices: unknown, mode: Mode) {
  const out = { plane: DEFAULTS.plane, sphere: DEFAULTS.sphere, hyperbolic: DEFAULTS.hyperbolic };
  const set = (m: Mode, raw: unknown) => {
    const tri = parseTriple(raw);
    if (!tri) return;
    if (m === "plane") out.plane = tri.map(clampPlane);
    if (m === "sphere") out.sphere = tri.map(([la, lo]) => [clamp(la, -90, 90), clamp(lo, -360, 360)]);
    if (m === "hyperbolic") out.hyperbolic = tri.map((p) => clampDisk(p));
  };
  if (Array.isArray(vertices)) set(mode, vertices);
  else if (vertices && typeof vertices === "object") for (const m of MODES) set(m, (vertices as Record<string, unknown>)[m]);
  return { plane: out.plane, sphere: out.sphere.map(([la, lo]) => fromLatLon(la, lo)), hyperbolic: out.hyperbolic };
}

const f1 = (x: number) => (Number.isFinite(x) ? (x < 0 ? `−${(-x).toFixed(1)}` : x.toFixed(1)) : "—");
const f3 = (x: number) => (Number.isFinite(x) ? (x < 0 ? `−${(-x).toFixed(3)}` : x.toFixed(3)) : "—");

export interface CurvedTrianglesProps {
  mode?: Mode;
  modes?: Mode[];
  vertices?: unknown;
  title?: string;
  subtitle?: string;
}

/**
 * Geodesic triangles in flat, spherical and hyperbolic geometry: drag the
 * vertices, compare the angle sum with 180°, and check numerically that the
 * excess (sphere) or defect (hyperbolic plane) equals the area — Gauss–Bonnet.
 */
export function CurvedTriangles({ mode: initialMode, modes, vertices, title, subtitle }: CurvedTrianglesProps) {
  const { t } = useI18n();
  const allowed = useMemo<Mode[]>(() => {
    const list = Array.isArray(modes) ? MODES.filter((m) => modes.includes(m)) : [];
    return list.length ? list : MODES;
  }, [modes]);
  const start: Mode = initialMode && allowed.includes(initialMode) ? initialMode : allowed[0];
  const [mode, setMode] = useState<Mode>(start);
  const [init] = useState(() => initialVertices(vertices, start));
  const [plane, setPlane] = useState<V2[]>(init.plane);
  const [sphere, setSphere] = useState<V3[]>(init.sphere);
  const [hyp, setHyp] = useState<V2[]>(init.hyperbolic);
  const [rot, setRot] = useState<M3>(() => viewCentredOn(add3(add3(init.sphere[0], init.sphere[1]), init.sphere[2])));

  const angles = mode === "plane" ? planeAngles(plane[0], plane[1], plane[2]) : mode === "sphere" ? sphereAngles(sphere[0], sphere[1], sphere[2]) : hypAngles(hyp[0], hyp[1], hyp[2]);
  const sum = angles[0] + angles[1] + angles[2];
  const area = useMemo(
    () => (mode === "sphere" ? sphereAreaNumeric(sphere[0], sphere[1], sphere[2]) : mode === "hyperbolic" ? hypAreaNumeric(hyp[0], hyp[1], hyp[2]) : NaN),
    [mode, sphere, hyp],
  );

  const preset = (key: string) => {
    if (mode === "plane") setPlane(PRESETS.plane[key as keyof typeof PRESETS.plane]);
    if (mode === "sphere") {
      const tri = PRESETS.sphere[key as keyof typeof PRESETS.sphere].map(([la, lo]) => fromLatLon(la, lo));
      setSphere(tri);
      setRot(viewCentredOn(add3(add3(tri[0], tri[1]), tri[2])));
    }
    if (mode === "hyperbolic") setHyp(PRESETS.hyperbolic[key as keyof typeof PRESETS.hyperbolic]);
  };

  return (
    <WidgetFrame title={title ?? t("w.curved.title")} subtitle={subtitle ?? t("w.curved.subtitle")}>
      {allowed.length > 1 && (
        <div className="flex flex-wrap gap-2" role="group" aria-label={t("w.curved.chooseMode")}>
          {allowed.map((m) => (
            <button key={m} type="button" aria-pressed={mode === m} className={`btn btn-sm ${mode === m ? "btn-primary" : "btn-ghost"}`} onClick={() => setMode(m)}>
              {t(`w.curved.mode.${m}`)}
            </button>
          ))}
        </div>
      )}
      <div className="mt-4 grid gap-5 md:grid-cols-[1.1fr_1fr]">
        <div>
          <div dir="ltr" className="mx-auto max-w-[420px]">
            {mode === "plane" && <PlaneCanvas pts={plane} setPts={setPlane} angles={angles} />}
            {mode === "sphere" && <SphereCanvas pts={sphere} setPts={setSphere} rot={rot} setRot={setRot} angles={angles} />}
            {mode === "hyperbolic" && <HypCanvas pts={hyp} setPts={setHyp} angles={angles} />}
          </div>
          <p className="mt-2 text-xs text-muted">{t(`w.curved.hint.${mode}`)}</p>
          <div className="mt-2 flex flex-wrap gap-1.5">
            {Object.keys(PRESETS[mode]).map((k) => (
              <button key={k} type="button" className="btn btn-sm btn-ghost" onClick={() => preset(k)}>
                {t(`w.curved.preset.${k}`)}
              </button>
            ))}
          </div>
        </div>
        <Readout mode={mode} angles={angles} sum={sum} area={area} />
      </div>
      <GaussBonnet mode={mode} />
    </WidgetFrame>
  );
}

// ------------------------------------------------------------------ readout

function Readout({ mode, angles, sum, area }: { mode: Mode; angles: [number, number, number]; sum: number; area: number }) {
  const { t } = useI18n();
  const sumDeg = sum * DEG;
  const excess = sum - PI;
  const match = Number.isFinite(area) && Math.abs(Math.abs(excess) - area) < 0.005;
  return (
    <div aria-live="polite" className="space-y-3">
      <ul className="grid grid-cols-3 gap-2 text-center" dir="ltr">
        {angles.map((a, i) => (
          <li key={i} className="rounded-xl bg-paper-2 px-2 py-2">
            <span className="block font-serif text-sm italic text-ink-2">∠{NAMES[i]}</span>
            <span className="font-mono text-lg text-ink">{f1(a * DEG)}°</span>
          </li>
        ))}
      </ul>
      <p className="rounded-xl bg-gold-soft px-4 py-2.5 font-serif text-xl text-ink" dir="ltr">
        ∠A + ∠B + ∠C = <strong className="text-gold-ink">{f1(sumDeg)}°</strong>
      </p>
      {mode === "plane" && <p className="text-sm text-ink-2">{t("w.curved.planeNote")}</p>}
      {mode !== "plane" && (
        <>
          <dl className="space-y-1.5 text-sm">
            <div className="flex flex-wrap items-baseline justify-between gap-x-3">
              <dt className="text-ink-2">{mode === "sphere" ? t("w.curved.excess") : t("w.curved.defect")}</dt>
              <dd className="ms-auto font-mono text-ink" dir="ltr">
                {mode === "sphere" ? `${f1(sumDeg - 180)}° = ${f3(excess)} rad` : `${f1(180 - sumDeg)}° = ${f3(-excess)} rad`}
              </dd>
            </div>
            <div className="flex flex-wrap items-baseline justify-between gap-x-3">
              <dt className="text-ink-2">{mode === "sphere" ? t("w.curved.areaSphere") : t("w.curved.areaHyp")}</dt>
              <dd className="ms-auto font-mono text-ink" dir="ltr">
                {mode === "sphere" ? `${f3(area)} R²` : f3(area)}
              </dd>
            </div>
            {mode === "sphere" && (
              <div className="flex flex-wrap items-baseline justify-between gap-x-3">
                <dt className="text-ink-2">{t("w.curved.fraction")}</dt>
                <dd className="ms-auto font-mono text-ink" dir="ltr">
                  {Number.isFinite(area) ? `${((100 * area) / (4 * PI)).toFixed(2)} %` : "—"}
                </dd>
              </div>
            )}
          </dl>
          <p className={`flex items-start gap-2 rounded-xl px-3 py-2 text-sm ${match ? "bg-good-soft text-ink" : "bg-paper-2 text-ink-2"}`}>
            {match && <Check size={16} className="mt-0.5 shrink-0 text-good" aria-hidden="true" />}
            <span>
              <span className="font-serif" dir="ltr">
                {mode === "sphere" ? `∠A + ∠B + ∠C − π = ${t("w.curved.areaWord")} / R²` : `π − (∠A + ∠B + ∠C) = ${t("w.curved.areaWord")}`}
              </span>
              <span className="block text-xs text-muted">{mode === "sphere" ? t("w.curved.sphereNote") : t("w.curved.hypNote")}</span>
            </span>
          </p>
        </>
      )}
    </div>
  );
}

function GaussBonnet({ mode }: { mode: Mode }) {
  const { t } = useI18n();
  const rows: [Mode, string, string][] = [
    ["plane", "K = 0", "= 180°"],
    ["sphere", "K = 1/R²", "> 180°"],
    ["hyperbolic", "K = −1", "< 180°"],
  ];
  return (
    <div className="mt-5 rounded-2xl border border-line p-4">
      <p className="font-serif text-lg text-ink" dir="ltr">
        ∠A + ∠B + ∠C − π = K · {t("w.curved.areaWord")}
      </p>
      <div className="mt-2 overflow-x-auto">
        <table className="w-full min-w-[280px] text-sm">
          <tbody>
            {rows.map(([m, k, s]) => (
              <tr key={m} className={`border-b border-line/60 last:border-0 ${m === mode ? "font-semibold text-ink" : "text-ink-2"}`}>
                <th scope="row" className="py-1.5 pe-3 text-start font-medium">
                  {m === mode && <span className="me-1.5 inline-block h-2 w-2 rounded-full bg-gold align-middle" aria-hidden="true" />}
                  {t(`w.curved.mode.${m}`)}
                </th>
                <td className="whitespace-nowrap px-2 py-1.5 font-mono text-xs sm:text-sm" dir="ltr">
                  {k}
                </td>
                <td className="whitespace-nowrap ps-2 py-1.5 font-mono text-xs sm:text-sm" dir="ltr">
                  ∠A+∠B+∠C {s}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p className="mt-2 text-sm text-ink-2">{t("w.curved.gaussBonnet")}</p>
    </div>
  );
}

// ------------------------------------------------------------------ shared drawing helpers

/** Interior-angle arc at screen point p between screen directions d1, d2 (radians < π). */
function arcPath(p: V2, d1: V2, d2: V2, r: number): string {
  const a1 = Math.atan2(d1[1], d1[0]);
  let da = Math.atan2(d2[1], d2[0]) - a1;
  while (da > PI) da -= 2 * PI;
  while (da < -PI) da += 2 * PI;
  const s: V2 = [p[0] + r * Math.cos(a1), p[1] + r * Math.sin(a1)];
  const e: V2 = [p[0] + r * Math.cos(a1 + da), p[1] + r * Math.sin(a1 + da)];
  return `M${r2(p[0])} ${r2(p[1])}L${r2(s[0])} ${r2(s[1])}A${r} ${r} 0 0 ${da > 0 ? 1 : 0} ${r2(e[0])} ${r2(e[1])}Z`;
}
function squarePath(p: V2, d1: V2, d2: V2, r: number): string {
  const u = norm2(d1);
  const v = norm2(d2);
  const k = r * 0.62;
  return `M${r2(p[0] + u[0] * k)} ${r2(p[1] + u[1] * k)}L${r2(p[0] + (u[0] + v[0]) * k)} ${r2(p[1] + (u[1] + v[1]) * k)}L${r2(p[0] + v[0] * k)} ${r2(p[1] + v[1] * k)}`;
}
function bisector(d1: V2, d2: V2): V2 {
  const b = norm2([norm2(d1)[0] + norm2(d2)[0], norm2(d1)[1] + norm2(d2)[1]]);
  return len2(b) > 0 ? b : norm2([-d1[1], d1[0]]);
}

/** Angle marker (arc, or a square for a right angle) with its degree label. */
function AngleMark({ p, d1, d2, angle, colour, r = 20 }: { p: V2; d1: V2; d2: V2; angle: number; colour: string; r?: number }) {
  const right = Math.abs(angle * DEG - 90) < 0.25;
  const b = bisector(d1, d2);
  const lr = r + 17;
  return (
    <g>
      {right ? (
        <path d={squarePath(p, d1, d2, r)} fill="none" stroke={colour} strokeWidth={1.6} />
      ) : (
        <path d={arcPath(p, d1, d2, r)} fill={colour} fillOpacity={0.16} stroke={colour} strokeWidth={1.4} />
      )}
      <text x={r2(p[0] + b[0] * lr)} y={r2(p[1] + b[1] * lr + 4)} textAnchor="middle" fontSize="11.5" fontWeight={700} fill="var(--ink)" stroke="var(--card)" strokeWidth={3} paintOrder="stroke">
        {(angle * DEG).toFixed(1)}°
      </text>
    </g>
  );
}

function VertexHandle({
  p,
  name,
  label,
  outward,
  onPointerDown,
  onKey,
  disabled = false,
}: {
  p: V2;
  name: string;
  label: string;
  outward: V2;
  onPointerDown?: (e: React.PointerEvent<SVGGElement>) => void;
  onKey: (dx: number, dy: number) => void;
  disabled?: boolean;
}) {
  return (
    <g
      role="button"
      tabIndex={0}
      aria-label={label}
      className={`outline-none [&:focus-visible>circle:first-of-type]:stroke-[var(--sky)] [&:focus-visible>circle:first-of-type]:stroke-[4px] ${disabled ? "" : "cursor-grab active:cursor-grabbing"}`}
      onPointerDown={disabled ? undefined : onPointerDown}
      onKeyDown={(e) => {
        const step = e.shiftKey ? 4 : 1;
        const map: Record<string, V2> = { ArrowLeft: [-step, 0], ArrowRight: [step, 0], ArrowUp: [0, step], ArrowDown: [0, -step] };
        const d = map[e.key];
        if (d) {
          e.preventDefault();
          onKey(d[0], d[1]);
        }
      }}
    >
      <circle cx={r2(p[0])} cy={r2(p[1])} r={disabled ? 6 : 9} fill="var(--card)" stroke="var(--ink)" strokeWidth={2.2} opacity={disabled ? 0.55 : 1} />
      <circle cx={r2(p[0])} cy={r2(p[1])} r={22} fill="transparent" />
      <text x={r2(p[0] + outward[0] * 21)} y={r2(p[1] + outward[1] * 21 + 5)} textAnchor="middle" fontSize="15" fontWeight={800} fontStyle="italic" fill="var(--ink)" opacity={disabled ? 0.5 : 1} stroke="var(--card)" strokeWidth={3} paintOrder="stroke" style={{ fontFamily: "var(--font-serif)" }}>
        {name}
      </text>
    </g>
  );
}

const outwardFrom = (p: V2, centroid: V2): V2 => {
  const d = norm2(sub2(p, centroid));
  return len2(d) > 0 ? d : [0, -1];
};

/** Pointer-drag plumbing shared by the canvases. */
function useDrag<T>(onMove: (target: T, pt: V2, e: React.PointerEvent) => void) {
  const svgRef = useRef<SVGSVGElement>(null);
  const drag = useRef<{ target: T; pid: number } | null>(null);
  const begin = (target: T) => (e: React.PointerEvent) => {
    e.stopPropagation();
    drag.current = { target, pid: e.pointerId };
    svgRef.current?.setPointerCapture(e.pointerId);
  };
  const svgProps = {
    ref: svgRef,
    onPointerMove: (e: React.PointerEvent<SVGSVGElement>) => {
      const d = drag.current;
      if (!d || d.pid !== e.pointerId) return;
      const pt = svgPoint(svgRef.current, e.clientX, e.clientY);
      if (pt) onMove(d.target, pt, e);
    },
    onPointerUp: () => (drag.current = null),
    onPointerCancel: () => (drag.current = null),
  };
  return { begin, svgProps, drag, svgRef };
}

// ------------------------------------------------------------------ plane

function PlaneCanvas({ pts, setPts, angles }: { pts: V2[]; setPts: (f: (p: V2[]) => V2[]) => void; angles: number[] }) {
  const { t } = useI18n();
  const W = 360;
  const H = 260;
  const k = W / (2 * PLANE_BOX.x);
  const S = (p: V2): V2 => [r2(W / 2 + p[0] * k), r2(H / 2 - p[1] * k)];
  const toWorld = (q: V2): V2 => [(q[0] - W / 2) / k, (H / 2 - q[1]) / k];
  const { begin, svgProps } = useDrag<number>((i, q) => setPts((p) => p.map((v, j) => (j === i ? clampPlane(toWorld(q)) : v))));
  const sp = pts.map(S);
  const c: V2 = [(sp[0][0] + sp[1][0] + sp[2][0]) / 3, (sp[0][1] + sp[1][1] + sp[2][1]) / 3];
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="w-full touch-none select-none rounded-2xl border border-line bg-paper-2/60" role="group" aria-label={t("w.curved.diagram.plane")} {...svgProps}>
      {Array.from({ length: 11 }, (_, i) => i - 5).map((x) => (
        <line key={`x${x}`} x1={S([x, 0])[0]} y1={0} x2={S([x, 0])[0]} y2={H} stroke="var(--line)" strokeWidth={x === 0 ? 1.2 : 0.7} />
      ))}
      {Array.from({ length: 7 }, (_, i) => i - 3).map((y) => (
        <line key={`y${y}`} x1={0} y1={S([0, y])[1]} x2={W} y2={S([0, y])[1]} stroke="var(--line)" strokeWidth={y === 0 ? 1.2 : 0.7} />
      ))}
      <polygon points={sp.map((p) => p.map(r2).join(",")).join(" ")} fill="var(--human)" fillOpacity={0.14} stroke="var(--human)" strokeWidth={2.5} strokeLinejoin="round" />
      {sp.map((p, i) => (
        <AngleMark key={i} p={p} d1={sub2(sp[(i + 1) % 3], p)} d2={sub2(sp[(i + 2) % 3], p)} angle={angles[i]} colour="var(--human)" />
      ))}
      {sp.map((p, i) => (
        <VertexHandle
          key={i}
          p={p}
          name={NAMES[i]}
          outward={outwardFrom(p, c)}
          label={t("w.curved.vertex", { name: NAMES[i] })}
          onPointerDown={begin(i)}
          onKey={(dx, dy) => setPts((q) => q.map((v, j) => (j === i ? clampPlane([v[0] + dx * 0.15, v[1] + dy * 0.15]) : v)))}
        />
      ))}
    </svg>
  );
}

// ------------------------------------------------------------------ sphere

const SR = 150;
const SC = 180;

function SphereCanvas({ pts, setPts, rot, setRot, angles }: { pts: V3[]; setPts: (f: (p: V3[]) => V3[]) => void; rot: M3; setRot: (f: (m: M3) => M3) => void; angles: number[] }) {
  const { t } = useI18n();
  const gid = useId().replace(/:/g, "");
  const last = useRef<V2 | null>(null);
  const toView = (v: V3) => apply3(rot, v);
  const S = (v: V3): V2 => [r2(SC + SR * v[0]), r2(SC - SR * v[1])];
  const { begin, svgProps, drag, svgRef } = useDrag<number | "rotate">((target, q, e) => {
    if (target === "rotate") {
      const prev = last.current;
      last.current = [e.clientX, e.clientY];
      if (prev) setRot((m) => dragRotate(m, (e.clientX - prev[0]) * 0.009, (e.clientY - prev[1]) * 0.009));
      return;
    }
    let x = (q[0] - SC) / SR;
    let y = (SC - q[1]) / SR;
    const r = Math.hypot(x, y);
    if (r > 0.999) {
      x = (x / r) * 0.999;
      y = (y / r) * 0.999;
    }
    const v: V3 = [x, y, Math.sqrt(Math.max(0, 1 - x * x - y * y))];
    setPts((p) => p.map((w, j) => (j === target ? norm3(apply3(transpose3(rot), v)) : w)));
  });

  const view = pts.map(toView);
  const front = view.map((v) => v[2] > 0.02);
  const sp = view.map(S);

  // graticule
  const grat: { d: string; eq: boolean }[] = [];
  const runs = (pts3: V3[]) => {
    const out: { front: V2[][]; back: V2[][] } = { front: [], back: [] };
    let cur: V2[] = [];
    let curFront: boolean | null = null;
    for (const w of pts3) {
      const v = toView(w);
      // points on the horizon have z ≈ ±1e-17; round so server and browser classify them identically
      const f = Math.round(v[2] * 1e9) >= 0;
      if (curFront !== null && f !== curFront) {
        (curFront ? out.front : out.back).push(cur);
        cur = [cur[cur.length - 1]];
      }
      curFront = f;
      cur.push(S(v));
    }
    if (cur.length > 1 && curFront !== null) (curFront ? out.front : out.back).push(cur);
    return out;
  };
  const toD = (line: V2[]) => line.map((p, i) => `${i ? "L" : "M"}${r2(p[0])} ${r2(p[1])}`).join("");
  for (let lon = 0; lon < 180; lon += 30) {
    const circle = Array.from({ length: 97 }, (_, i) => fromLatLon(-90 + (i * 360) / 96, lon));
    for (const line of runs(circle).front) grat.push({ d: toD(line), eq: false });
  }
  for (let lat = -60; lat <= 60; lat += 30) {
    const circle = Array.from({ length: 97 }, (_, i) => fromLatLon(lat, (i * 360) / 96));
    for (const line of runs(circle).front) grat.push({ d: toD(line), eq: lat === 0 });
  }

  // triangle pieces
  const mesh = sphereMesh(pts[0], pts[1], pts[2], 14);
  let frontFill = "";
  let backFill = "";
  for (const tri of mesh) {
    const v = tri.map(toView);
    const d = `M${v.map((w) => S(w).map(r2).join(" ")).join("L")}Z`;
    if (Math.round(((v[0][2] + v[1][2] + v[2][2]) / 3) * 1e9) >= 0) frontFill += d;
    else backFill += d;
  }
  const sides = [0, 1, 2].map((i) => runs(greatArc(pts[i], pts[(i + 1) % 3], 72)));
  const centroid: V2 = [(sp[0][0] + sp[1][0] + sp[2][0]) / 3, (sp[0][1] + sp[1][1] + sp[2][1]) / 3];

  // angle marks drawn on the sphere: small arcs in the tangent plane, projected
  const marks = [0, 1, 2].map((i) => {
    const A = pts[i];
    const t1 = sphereTangent(A, pts[(i + 1) % 3]);
    const t2 = sphereTangent(A, pts[(i + 2) % 3]);
    const w = norm3(sub3(t2, scale3(t1, dot3(t2, t1))));
    const at = (phi: number, eps: number): V2 => S(toView(norm3(add3(scale3(A, Math.cos(eps)), scale3(add3(scale3(t1, Math.cos(phi)), scale3(w, Math.sin(phi))), Math.sin(eps))))));
    const a = angles[i];
    const right = Math.abs(a * DEG - 90) < 0.25;
    const eps = 0.13;
    let d: string;
    if (right) {
      const p1 = at(0, eps * 0.75);
      const p2 = S(toView(norm3(add3(A, scale3(add3(t1, w), Math.tan(eps * 0.75))))));
      const p3 = at(PI / 2, eps * 0.75);
      d = `M${r2(p1[0])} ${r2(p1[1])}L${r2(p2[0])} ${r2(p2[1])}L${r2(p3[0])} ${r2(p3[1])}`;
    } else {
      const arc = Array.from({ length: 13 }, (_, j) => at((a * j) / 12, eps));
      d = `M${r2(sp[i][0])} ${r2(sp[i][1])}` + arc.map((p) => `L${r2(p[0])} ${r2(p[1])}`).join("") + "Z";
    }
    return { d, right, label: at(a / 2, 0.27) };
  });

  const nudge = (i: number, dx: number, dy: number) => {
    const v = toView(pts[i]);
    const moved = norm3([v[0] + dx * 0.035, v[1] + dy * 0.035, v[2]]);
    setPts((p) => p.map((w, j) => (j === i ? norm3(apply3(transpose3(rot), moved)) : w)));
  };

  return (
    <div>
      <svg
        viewBox="0 0 360 360"
        className="w-full cursor-grab touch-none select-none active:cursor-grabbing"
        role="group"
        aria-label={t("w.curved.diagram.sphere")}
        {...svgProps}
        ref={svgRef}
        onPointerDown={(e) => {
          drag.current = { target: "rotate", pid: e.pointerId };
          last.current = [e.clientX, e.clientY];
          svgRef.current?.setPointerCapture(e.pointerId);
        }}
        onPointerUp={() => {
          drag.current = null;
          last.current = null;
        }}
      >
        <defs>
          <radialGradient id={`${gid}-ball`} cx="38%" cy="32%" r="75%">
            <stop offset="0%" stopColor="var(--card)" />
            <stop offset="70%" stopColor="var(--sky-soft)" />
            <stop offset="100%" stopColor="var(--line-2)" />
          </radialGradient>
        </defs>
        {/* the far side, seen faintly through the sphere */}
        <path d={backFill} fill="var(--human)" fillOpacity={0.1} />
        {sides.map((s, i) => s.back.map((line, j) => <path key={`b${i}-${j}`} d={toD(line)} fill="none" stroke="var(--human)" strokeWidth={1.4} strokeDasharray="4 4" opacity={0.5} />))}
        <circle cx={SC} cy={SC} r={SR} fill={`url(#${gid}-ball)`} fillOpacity={0.82} stroke="var(--ink-2)" strokeWidth={1.5} />
        {grat.map((g, i) => (
          <path key={i} d={g.d} fill="none" stroke={g.eq ? "var(--muted)" : "var(--line-2)"} strokeWidth={g.eq ? 1.1 : 0.8} />
        ))}
        <path d={frontFill} fill="var(--human)" fillOpacity={0.2} />
        {sides.map((s, i) => s.front.map((line, j) => <path key={`f${i}-${j}`} d={toD(line)} fill="none" stroke="var(--human)" strokeWidth={2.6} strokeLinecap="round" />))}
        {marks.map((m, i) =>
          front[i] ? (
            <g key={i}>
              <path d={m.d} fill={m.right ? "none" : "var(--human)"} fillOpacity={0.16} stroke="var(--human)" strokeWidth={1.4} />
              <text x={r2(m.label[0])} y={r2(m.label[1] + 4)} textAnchor="middle" fontSize="11.5" fontWeight={700} fill="var(--ink)" stroke="var(--card)" strokeWidth={3} paintOrder="stroke">
                {(angles[i] * DEG).toFixed(1)}°
              </text>
            </g>
          ) : null,
        )}
        {sp.map((p, i) => (
          <VertexHandle
            key={i}
            p={p}
            name={NAMES[i]}
            outward={outwardFrom(p, centroid)}
            disabled={!front[i]}
            label={front[i] ? t("w.curved.vertex", { name: NAMES[i] }) : t("w.curved.vertexBehind", { name: NAMES[i] })}
            onPointerDown={begin(i)}
            onKey={(dx, dy) => nudge(i, dx, dy)}
          />
        ))}
      </svg>
      <div className="mt-1 flex justify-end gap-1" dir="ltr">
        {(
          [
            ["left", ArrowLeft, -0.26, 0],
            ["up", ArrowUp, 0, -0.26],
            ["down", ArrowDown, 0, 0.26],
            ["right", ArrowRight, 0.26, 0],
          ] as const
        ).map(([k, Icon, dx, dy]) => (
          <button key={k} type="button" className="btn btn-sm btn-ghost px-2" aria-label={t(`w.curved.rotate.${k}`)} title={t(`w.curved.rotate.${k}`)} onClick={() => setRot((m) => dragRotate(m, dx, dy))}>
            <Icon size={15} aria-hidden="true" />
          </button>
        ))}
        <button
          type="button"
          className="btn btn-sm btn-ghost px-2"
          aria-label={t("w.curved.rotate.reset")}
          title={t("w.curved.rotate.reset")}
          onClick={() => setRot(() => viewCentredOn(add3(add3(pts[0], pts[1]), pts[2])))}
        >
          <RotateCcw size={15} aria-hidden="true" />
        </button>
      </div>
    </div>
  );
}

// ------------------------------------------------------------------ hyperbolic

const HR = 165;
const HC = 180;

function HypCanvas({ pts, setPts, angles }: { pts: V2[]; setPts: (f: (p: V2[]) => V2[]) => void; angles: number[] }) {
  const { t } = useI18n();
  const S = (p: V2): V2 => [r2(HC + HR * p[0]), r2(HC - HR * p[1])];
  const toDisk = (q: V2): V2 => [(q[0] - HC) / HR, (HC - q[1]) / HR];
  const { begin, svgProps } = useDrag<number>((i, q) => setPts((p) => p.map((v, j) => (j === i ? clampDisk(toDisk(q)) : v))));
  const sp = pts.map(S);
  const centroid: V2 = [(sp[0][0] + sp[1][0] + sp[2][0]) / 3, (sp[0][1] + sp[1][1] + sp[2][1]) / 3];

  /** SVG path command from p to q along the geodesic. */
  const seg = (p: V2, q: V2) => {
    const g = geodesic(p, q);
    const Q = S(q);
    if (g.kind === "line") return `L${r2(Q[0])} ${r2(Q[1])}`;
    const P = S(p);
    const C = S(g.c);
    const cross = (P[0] - C[0]) * (Q[1] - C[1]) - (P[1] - C[1]) * (Q[0] - C[0]);
    return `A${r2(g.r * HR)} ${r2(g.r * HR)} 0 0 ${cross > 0 ? 1 : 0} ${r2(Q[0])} ${r2(Q[1])}`;
  };
  const tri = `M${r2(sp[0][0])} ${r2(sp[0][1])}${seg(pts[0], pts[1])}${seg(pts[1], pts[2])}${seg(pts[2], pts[0])}Z`;
  // each side extended to a complete geodesic, from one ideal point on the boundary to the other
  const full = [0, 1, 2].map((i) => {
    const [e1, e2] = hypEndpoints(pts[i], pts[(i + 1) % 3]);
    return `M${r2(S(e1)[0])} ${r2(S(e1)[1])}${seg(e1, e2)}`;
  });

  return (
    <svg viewBox="0 0 360 360" className="w-full touch-none select-none" role="group" aria-label={t("w.curved.diagram.hyperbolic")} {...svgProps}>
      <circle cx={HC} cy={HC} r={HR} fill="var(--formal-soft)" fillOpacity={0.45} stroke="var(--ink-2)" strokeWidth={1.6} />
      {full.map((d, i) => (
        <path key={i} d={d} fill="none" stroke="var(--formal)" strokeWidth={1.1} strokeDasharray="3 4" opacity={0.7} />
      ))}
      <path d={tri} fill="var(--formal)" fillOpacity={0.18} stroke="var(--formal)" strokeWidth={2.6} strokeLinejoin="round" />
      {sp.map((p, i) => {
        const t1 = hypTangent(pts[i], pts[(i + 1) % 3]);
        const t2 = hypTangent(pts[i], pts[(i + 2) % 3]);
        return <AngleMark key={i} p={p} d1={[t1[0], -t1[1]]} d2={[t2[0], -t2[1]]} angle={angles[i]} colour="var(--formal)" />;
      })}
      {sp.map((p, i) => (
        <VertexHandle
          key={i}
          p={p}
          name={NAMES[i]}
          outward={outwardFrom(p, centroid)}
          label={t("w.curved.vertex", { name: NAMES[i] })}
          onPointerDown={begin(i)}
          onKey={(dx, dy) => setPts((q) => q.map((v, j) => (j === i ? clampDisk([v[0] + dx * 0.02, v[1] + dy * 0.02]) : v)))}
        />
      ))}
    </svg>
  );
}
