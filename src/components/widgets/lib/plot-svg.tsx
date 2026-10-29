"use client";

import { createContext, useContext, useEffect, useId, useMemo, useRef, useState, type ReactNode } from "react";
import { useI18n } from "@/i18n/client";
import { clamp, fitEqualAspect, fmt, linearScale, looksLikePiRange, niceStep, niceTicks, piTicks, type Pt, type Range, type Scale, type Ticks } from "./plot-core";

/**
 * <Plot> — the shared coordinate plane of the analysis widgets.
 *
 * Renders a responsive SVG whose viewBox matches its real pixel width (so
 * text stays legible from phones to desktops), with grid, axes and nice tick
 * labels (multiples of π when the window is given in π). Content is supplied
 * by render props that receive the scales. Always rendered left-to-right.
 */

export interface PlotView {
  W: number;
  H: number;
  /** The visible windows (may be widened for equal aspect). */
  x: Range;
  y: Range;
  sx: Scale;
  sy: Scale;
  clipId: string;
  /** Convert a pointer position to data coordinates. */
  toData: (clientX: number, clientY: number) => Pt | null;
}

const PlotContext = createContext<PlotView | null>(null);
export const usePlotView = () => useContext(PlotContext);

export type TickMode = "auto" | "pi" | "decimal" | "none";

export interface PlotProps {
  x: Range;
  y: Range;
  /** Height as a fraction of the width (default 0.62), or "equal" for equal units on both axes. */
  aspect?: number | "equal";
  minHeight?: number;
  maxHeight?: number;
  /** Width used for the server render, before the real width is measured. */
  defaultWidth?: number;
  grid?: boolean;
  axes?: boolean;
  xTicks?: TickMode;
  yTicks?: TickMode;
  xLabel?: string;
  yLabel?: string;
  ariaLabel: string;
  onHover?: (p: Pt | null) => void;
  onPress?: (p: Pt) => void;
  /** Clipped content layer. */
  children?: (v: PlotView) => ReactNode;
  /** Unclipped layer (handles, labels near the edge). */
  above?: (v: PlotView) => ReactNode;
  /** Small HTML read-out shown in the top corner. */
  readout?: ReactNode;
  className?: string;
}

function useMeasuredWidth(initial: number) {
  const ref = useRef<HTMLDivElement>(null);
  const [w, setW] = useState(initial);
  useEffect(() => {
    const el = ref.current;
    if (!el) return;
    const update = () => {
      const cw = Math.round(el.clientWidth);
      if (cw > 0) setW((old) => (Math.abs(old - cw) >= 1 ? cw : old));
    };
    update();
    if (typeof ResizeObserver === "undefined") return;
    const ro = new ResizeObserver(update);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);
  return [ref, w] as const;
}

function ticksFor(mode: TickMode, lo: number, hi: number, target: number): Ticks {
  if (mode === "none") return { step: 1, values: [], labels: [] };
  if (mode === "pi" || (mode === "auto" && looksLikePiRange(lo, hi))) return piTicks(lo, hi, target);
  return niceTicks(lo, hi, target);
}

export function Plot({
  x,
  y,
  aspect = 0.62,
  minHeight = 220,
  maxHeight = 480,
  defaultWidth = 640,
  grid = true,
  axes = true,
  xTicks = "auto",
  yTicks = "auto",
  xLabel,
  yLabel,
  ariaLabel,
  onHover,
  onPress,
  children,
  above,
  readout,
  className = "",
}: PlotProps) {
  const [wrapRef, measured] = useMeasuredWidth(defaultWidth);
  const svgRef = useRef<SVGSVGElement>(null);
  const clipId = useId().replace(/[^a-zA-Z0-9_-]/g, "");
  const W = Math.max(200, measured);

  const view = useMemo<PlotView>(() => {
    let H: number;
    let vx: Range = x;
    let vy: Range = y;
    if (aspect === "equal") {
      H = clamp(Math.round((W * (y[1] - y[0])) / (x[1] - x[0])), minHeight, maxHeight);
      const fit = fitEqualAspect(x, y, W, H);
      vx = fit.x;
      vy = fit.y;
    } else {
      H = clamp(Math.round(W * aspect), minHeight, maxHeight);
    }
    const sx = linearScale(vx, [0, W]);
    const sy = linearScale(vy, [H, 0]);
    const toData = (cx: number, cy: number): Pt | null => {
      const svg = svgRef.current;
      if (!svg) return null;
      const r = svg.getBoundingClientRect();
      if (r.width === 0 || r.height === 0) return null;
      return [sx.invert(((cx - r.left) / r.width) * W), sy.invert(((cy - r.top) / r.height) * H)];
    };
    return { W, H, x: vx, y: vy, sx, sy, clipId: `plot-${clipId}`, toData };
  }, [W, x, y, aspect, minHeight, maxHeight, clipId]);

  const { H, sx, sy } = view;
  const xt = ticksFor(xTicks, view.x[0], view.x[1], Math.max(3, Math.round(W / 75)));
  const yt = ticksFor(yTicks, view.y[0], view.y[1], Math.max(3, Math.round(H / 48)));
  const minor = (t: Ticks, lo: number, hi: number, px: number) => {
    if (t.values.length === 0) return [];
    const mant = t.step / Math.pow(10, Math.floor(Math.log10(t.step) + 1e-9));
    const div = Math.abs(mant - 2) < 1e-6 ? 4 : 5;
    const st = t.step / div;
    if ((st / (hi - lo)) * px < 9) return [];
    const out: number[] = [];
    for (let k = Math.ceil(lo / st - 1e-9); k <= Math.floor(hi / st + 1e-9) && out.length < 400; k++) out.push(k * st);
    return out;
  };
  const xMinor = looksLikePiRange(view.x[0], view.x[1]) || xTicks === "pi" ? [] : minor(xt, view.x[0], view.x[1], W);
  const yMinor = looksLikePiRange(view.y[0], view.y[1]) || yTicks === "pi" ? [] : minor(yt, view.y[0], view.y[1], H);

  const X0 = sx(0);
  const Y0 = sy(0);
  const xAxisVisible = Y0 >= 0 && Y0 <= H;
  const yAxisVisible = X0 >= 0 && X0 <= W;
  // Tick labels sit next to the axes, and stay inside the plot when an axis is off-screen.
  const xLabelY = !xAxisVisible ? (Y0 < 0 ? 14 : H - 6) : Y0 + 16 > H - 4 ? Y0 - 6 : Y0 + 15;
  let yLabelX = yAxisVisible ? X0 - 6 : X0 < 0 ? 6 : W - 6;
  let yAnchor: "start" | "end" = yAxisVisible ? "end" : X0 < 0 ? "start" : "end";
  if (yAxisVisible && X0 < 30) {
    yLabelX = X0 + 6;
    yAnchor = "start";
  }

  const halo = { stroke: "var(--paper)", strokeWidth: 3, paintOrder: "stroke" as const, strokeLinejoin: "round" as const };

  return (
    <div ref={wrapRef} className={`relative w-full ${className}`} dir="ltr">
      <svg
        ref={svgRef}
        viewBox={`0 0 ${W} ${H}`}
        className={`block h-auto w-full select-none ${onPress ? "cursor-crosshair" : ""}`}
        role="img"
        aria-label={ariaLabel}
        onPointerMove={onHover ? (e) => onHover(view.toData(e.clientX, e.clientY)) : undefined}
        onPointerLeave={onHover ? () => onHover(null) : undefined}
        onClick={
          onPress
            ? (e) => {
                const p = view.toData(e.clientX, e.clientY);
                if (p) onPress(p);
              }
            : undefined
        }
      >
        <defs>
          <clipPath id={view.clipId}>
            <rect x={0} y={0} width={W} height={H} rx={10} />
          </clipPath>
        </defs>
        <rect x={0.5} y={0.5} width={W - 1} height={H - 1} rx={10} fill="var(--paper)" stroke="var(--line)" />
        {grid && (
          <g aria-hidden="true">
            {xMinor.map((v) => (
              <line key={`xm${v}`} x1={sx(v)} x2={sx(v)} y1={0} y2={H} stroke="var(--line)" strokeOpacity={0.45} strokeWidth={0.75} />
            ))}
            {yMinor.map((v) => (
              <line key={`ym${v}`} x1={0} x2={W} y1={sy(v)} y2={sy(v)} stroke="var(--line)" strokeOpacity={0.45} strokeWidth={0.75} />
            ))}
            {xt.values.map((v) => (
              <line key={`x${v}`} x1={sx(v)} x2={sx(v)} y1={0} y2={H} stroke="var(--line)" strokeWidth={1} />
            ))}
            {yt.values.map((v) => (
              <line key={`y${v}`} x1={0} x2={W} y1={sy(v)} y2={sy(v)} stroke="var(--line)" strokeWidth={1} />
            ))}
          </g>
        )}
        {axes && (
          <g aria-hidden="true">
            {xAxisVisible && <line x1={0} x2={W} y1={Y0} y2={Y0} stroke="var(--ink-2)" strokeOpacity={0.75} strokeWidth={1.25} />}
            {yAxisVisible && <line x1={X0} x2={X0} y1={0} y2={H} stroke="var(--ink-2)" strokeOpacity={0.75} strokeWidth={1.25} />}
            <g fontSize={11} fill="var(--muted)" style={{ fontVariantNumeric: "tabular-nums" }}>
              {xt.values.map((v, i) => {
                const px = sx(v);
                if (px < 10 || px > W - 10) return null;
                if (Math.abs(v) < 1e-12 && yAxisVisible) return null;
                return (
                  <text key={`xl${v}`} x={px} y={xLabelY} textAnchor="middle" {...halo}>
                    {xt.labels[i]}
                  </text>
                );
              })}
              {yt.values.map((v, i) => {
                const py = sy(v);
                if (py < 10 || py > H - 10) return null;
                if (Math.abs(v) < 1e-12 && xAxisVisible) return null;
                return (
                  <text key={`yl${v}`} x={yLabelX} y={py + 4} textAnchor={yAnchor} {...halo}>
                    {yt.labels[i]}
                  </text>
                );
              })}
              {xAxisVisible && yAxisVisible && X0 > 12 && Y0 < H - 12 && (
                <text x={X0 - 5} y={Y0 + 14} textAnchor="end" {...halo}>
                  0
                </text>
              )}
            </g>
            {xLabel && (
              <text x={W - 8} y={clamp(xAxisVisible ? Y0 - 7 : H - 20, 14, H - 6)} textAnchor="end" fontSize={14} fontStyle="italic" fill="var(--ink-2)" className="font-serif" {...halo}>
                {xLabel}
              </text>
            )}
            {yLabel && (
              <text x={clamp(yAxisVisible ? X0 + 7 : 8, 8, W - 30)} y={16} fontSize={14} fontStyle="italic" fill="var(--ink-2)" className="font-serif" {...halo}>
                {yLabel}
              </text>
            )}
          </g>
        )}
        <PlotContext.Provider value={view}>
          <g clipPath={`url(#${view.clipId})`}>{children?.(view)}</g>
          {above?.(view)}
        </PlotContext.Provider>
      </svg>
      {readout && (
        <div className="pointer-events-none absolute end-2 top-2 max-w-[70%] rounded-lg border border-line bg-card/90 px-2.5 py-1 font-mono text-xs text-ink-2 shadow-sm" aria-hidden="true">
          {readout}
        </div>
      )}
    </div>
  );
}

/* ---------------------------------------------------------------------------
 * Draggable point (pointer and keyboard)
 * ------------------------------------------------------------------------- */

export interface PlotHandleProps {
  x: number;
  y: number;
  onMove: (p: Pt) => void;
  /** Accessible name, e.g. "z". The current coordinates are appended. */
  label: string;
  /** Text describing the value for screen readers (defaults to "(x, y)"). */
  valueText?: string;
  color?: string;
  /** Keyboard step in data units (default: a nice fraction of the window). */
  step?: number;
  /** Map a proposed position to an allowed one (snapping, constraints). */
  constrain?: (p: Pt) => Pt;
  r?: number;
  /** Optional text drawn next to the point. */
  tag?: string;
}

export function PlotHandle({ x, y, onMove, label, valueText, color = "var(--gold)", step, constrain, r = 7, tag }: PlotHandleProps) {
  const view = usePlotView();
  const { t } = useI18n();
  const [focused, setFocused] = useState(false);
  const [dragging, setDragging] = useState(false);
  if (!view) return null;
  const { sx, sy } = view;
  const keyStep = step ?? niceStep(view.x[1] - view.x[0], 40);
  const fix = (p: Pt): Pt => {
    const q: Pt = [clamp(p[0], view.x[0], view.x[1]), clamp(p[1], view.y[0], view.y[1])];
    return constrain ? constrain(q) : q;
  };
  const X = sx(x);
  const Y = sy(y);
  if (!Number.isFinite(X) || !Number.isFinite(Y)) return null;
  return (
    <g
      role="button"
      tabIndex={0}
      aria-roledescription={t("w.plot.ui.dragPoint")}
      aria-label={`${label}: ${valueText ?? `(${fmt(x, 2)}, ${fmt(y, 2)})`}`}
      aria-keyshortcuts="ArrowUp ArrowDown ArrowLeft ArrowRight"
      className="outline-none"
      style={{ cursor: dragging ? "grabbing" : "grab", touchAction: "none" }}
      onFocus={() => setFocused(true)}
      onBlur={() => setFocused(false)}
      onClick={(e) => e.stopPropagation()}
      onPointerDown={(e) => {
        e.stopPropagation();
        e.preventDefault();
        (e.currentTarget as Element).setPointerCapture?.(e.pointerId);
        (e.currentTarget as SVGGElement).focus({ preventScroll: true });
        setDragging(true);
      }}
      onPointerMove={(e) => {
        if (!dragging) return;
        e.stopPropagation();
        const p = view.toData(e.clientX, e.clientY);
        if (p) onMove(fix(p));
      }}
      onPointerUp={(e) => {
        (e.currentTarget as Element).releasePointerCapture?.(e.pointerId);
        setDragging(false);
      }}
      onPointerCancel={() => setDragging(false)}
      onKeyDown={(e) => {
        const s = e.shiftKey ? keyStep / 10 : keyStep;
        const d: Record<string, Pt> = { ArrowLeft: [-s, 0], ArrowRight: [s, 0], ArrowUp: [0, s], ArrowDown: [0, -s] };
        const v = d[e.key];
        if (!v) return;
        e.preventDefault();
        const snap = (u: number) => Math.round(u / s) * s;
        onMove(fix([snap(x + v[0]), snap(y + v[1])]));
      }}
    >
      <circle cx={X} cy={Y} r={18} fill="transparent" />
      {(focused || dragging) && <circle cx={X} cy={Y} r={r + 5} fill="none" stroke="var(--sky)" strokeWidth={2.5} />}
      <circle cx={X} cy={Y} r={r} fill={color} stroke="var(--card)" strokeWidth={2.5} />
      {tag && (
        <text x={X + r + 5} y={Y - r - 2} fontSize={14} fontStyle="italic" fontWeight={600} fill={color} className="font-serif" stroke="var(--paper)" strokeWidth={3} paintOrder="stroke" style={{ pointerEvents: "none" }}>
          {tag}
        </text>
      )}
    </g>
  );
}

/* ---------------------------------------------------------------------------
 * Arrows in pixel space (no SVG markers, so any colour token works)
 * ------------------------------------------------------------------------- */

/** Path data for a line from (x1,y1) to (x2,y2) with a filled arrowhead of the given size (pixels). */
export function arrowPath(x1: number, y1: number, x2: number, y2: number, head = 8): { line: string; head: string } {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const len = Math.hypot(dx, dy);
  if (!(len > 0.01)) return { line: "", head: "" };
  const ux = dx / len;
  const uy = dy / len;
  const h = Math.min(head, len * 0.6);
  const bx = x2 - ux * h;
  const by = y2 - uy * h;
  const w = h * 0.5;
  const f = (v: number) => v.toFixed(2);
  return {
    line: `M${f(x1)} ${f(y1)}L${f(bx + ux * 0.5)} ${f(by + uy * 0.5)}`,
    head: `M${f(x2)} ${f(y2)}L${f(bx - uy * w)} ${f(by + ux * w)}L${f(bx + uy * w)} ${f(by - ux * w)}Z`,
  };
}

/** A single arrow between two data points. */
export function DataArrow({ from, to, color = "var(--ink-2)", width = 2.25, head = 9, dash, opacity }: { from: Pt; to: Pt; color?: string; width?: number; head?: number; dash?: string; opacity?: number }) {
  const view = usePlotView();
  if (!view) return null;
  const a = arrowPath(view.sx(from[0]), view.sy(from[1]), view.sx(to[0]), view.sy(to[1]), head);
  if (!a.line) return null;
  return (
    <g opacity={opacity}>
      <path d={a.line} stroke={color} strokeWidth={width} strokeLinecap="round" strokeDasharray={dash} fill="none" />
      <path d={a.head} fill={color} />
    </g>
  );
}
