/**
 * Winding numbers of closed loops in the punctured plane.
 * The winding number is computed by adding up the signed change of argument
 * (angle) of the vector from the puncture to the moving point; independently,
 * the contour integral (1/2πi)∮ dz/(z − a) is computed by the midpoint rule.
 */
import { cross2, dot2, len2, sub2, TAU, type V2 } from "./topo-vec";

export const LOOP_IDS = ["circle", "figureEight", "twice", "miss"] as const;
export type LoopId = (typeof LOOP_IDS)[number];
export const isLoopId = (v: unknown): v is LoopId => typeof v === "string" && (LOOP_IDS as readonly string[]).includes(v);

/** Default puncture positions (math coordinates, y up). The presets are designed around them. */
export const DEFAULT_PUNCTURES: V2[] = [[-1.6, 0], [1.6, 0]];
export const BOX = 5;

/** Preset loops as closed polylines (first point not repeated at the end). */
export function presetLoop(id: LoopId, n = 360): V2[] {
  const pts: V2[] = [];
  for (let i = 0; i < n; i++) {
    const t = (i / n) * TAU;
    switch (id) {
      case "circle":
        pts.push([3.3 * Math.cos(t), 3.3 * Math.sin(t)]);
        break;
      case "figureEight":
        // lemniscate of Gerono: lobes around (−1.6, 0) and (1.6, 0), crossing at the origin
        pts.push([3.3 * Math.cos(t), 2.2 * Math.sin(2 * t)]);
        break;
      case "twice": {
        // goes twice around (−1.6, 0), never closer than 1.0 to it, never reaching (1.6, 0)
        const r = 1.6 + 0.6 * Math.cos(t);
        pts.push([-1.6 + r * Math.cos(2 * t), r * Math.sin(2 * t)]);
        break;
      }
      case "miss": {
        // a crescent that curls around (−1.6, 0) without enclosing it
        const c: V2 = [-1.6, 0];
        const s = i / n;
        const span = 0.82 * Math.PI;
        let a: number;
        let r: number;
        if (s < 0.4) {
          a = -span + (2 * span * s) / 0.4;
          r = 2.5;
        } else if (s < 0.5) {
          const u = (s - 0.4) / 0.1;
          const cx = c[0] + 1.85 * Math.cos(span);
          const cy = c[1] + 1.85 * Math.sin(span);
          const ang = span + Math.PI * u;
          pts.push([cx + 0.65 * Math.cos(ang), cy + 0.65 * Math.sin(ang)]);
          continue;
        } else if (s < 0.9) {
          a = span - (2 * span * (s - 0.5)) / 0.4;
          r = 1.2;
        } else {
          const u = (s - 0.9) / 0.1;
          const cx = c[0] + 1.85 * Math.cos(-span);
          const cy = c[1] + 1.85 * Math.sin(-span);
          const ang = -span + Math.PI + Math.PI * u;
          pts.push([cx + 0.65 * Math.cos(ang), cy + 0.65 * Math.sin(ang)]);
          continue;
        }
        pts.push([c[0] + r * Math.cos(a), c[1] + r * Math.sin(a)]);
        break;
      }
    }
  }
  return pts;
}

/** Signed change of argument along the closed loop around `a`, in turns (≈ an integer). */
export function windingTurns(loop: readonly V2[], a: V2): number {
  let total = 0;
  for (let i = 0; i < loop.length; i++) {
    const u = sub2(loop[i], a);
    const v = sub2(loop[(i + 1) % loop.length], a);
    total += Math.atan2(cross2(u, v), dot2(u, v));
  }
  return total / TAU;
}

/** Distance from a point to the closed polyline. */
export function distanceToLoop(loop: readonly V2[], a: V2): number {
  let best = Infinity;
  for (let i = 0; i < loop.length; i++) {
    const p = loop[i];
    const q = loop[(i + 1) % loop.length];
    const d = sub2(q, p);
    const L2 = dot2(d, d);
    const t = L2 > 0 ? Math.max(0, Math.min(1, dot2(sub2(a, p), d) / L2)) : 0;
    best = Math.min(best, len2(sub2(a, [p[0] + d[0] * t, p[1] + d[1] * t])));
  }
  return best;
}

/** The winding number, or null when the loop (nearly) passes through the puncture. */
export function windingNumber(loop: readonly V2[], a: V2, tol = 0.08): number | null {
  if (loop.length < 3 || distanceToLoop(loop, a) < tol) return null;
  const w = Math.round(windingTurns(loop, a));
  return w === 0 ? 0 : w; // never −0
}

/** (1/2πi) ∮ dz/(z − a) by the midpoint rule; returns [real, imaginary]. Should be ≈ [winding number, 0]. */
export function contourIntegral(loop: readonly V2[], a: V2): [number, number] {
  let re = 0;
  let im = 0;
  for (let i = 0; i < loop.length; i++) {
    const p = loop[i];
    const q = loop[(i + 1) % loop.length];
    const dz: V2 = [q[0] - p[0], q[1] - p[1]];
    const w: V2 = [(p[0] + q[0]) / 2 - a[0], (p[1] + q[1]) / 2 - a[1]];
    const den = w[0] * w[0] + w[1] * w[1];
    // dz / w  =  dz · conj(w) / |w|²
    re += (dz[0] * w[0] + dz[1] * w[1]) / den;
    im += (dz[1] * w[0] - dz[0] * w[1]) / den;
  }
  // divide by 2πi:  (re + i im) / (2π i) = im/2π − i re/2π
  return [im / TAU, -re / TAU];
}

/** Resample a closed loop to n points equally spaced by arc length. */
export function resampleClosed(loop: readonly V2[], n: number): V2[] {
  if (loop.length < 2) return [...loop];
  const pts = [...loop, loop[0]];
  const cum = [0];
  for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + len2(sub2(pts[i], pts[i - 1])));
  const total = cum[cum.length - 1];
  if (total < 1e-9) return [...loop];
  const out: V2[] = [];
  let j = 0;
  for (let k = 0; k < n; k++) {
    const target = (k / n) * total;
    while (j < cum.length - 2 && cum[j + 1] < target) j++;
    const seg = cum[j + 1] - cum[j];
    const t = seg > 0 ? (target - cum[j]) / seg : 0;
    out.push([pts[j][0] + (pts[j + 1][0] - pts[j][0]) * t, pts[j][1] + (pts[j + 1][1] - pts[j][1]) * t]);
  }
  return out;
}

/** Cumulative change of argument (radians) from loop[0] up to each point, for animating the radius vector. */
export function cumulativeAngles(loop: readonly V2[], a: V2): number[] {
  const out = [0];
  for (let i = 1; i <= loop.length; i++) {
    const u = sub2(loop[i - 1], a);
    const v = sub2(loop[i % loop.length], a);
    out.push(out[i - 1] + Math.atan2(cross2(u, v), dot2(u, v)));
  }
  return out;
}

/** Sanitize user-supplied punctures: up to two finite points inside the box. */
export function parsePunctures(v: unknown): V2[] | null {
  if (!Array.isArray(v)) return null;
  const out: V2[] = [];
  for (const p of v) {
    if (Array.isArray(p) && p.length >= 2 && typeof p[0] === "number" && typeof p[1] === "number" && Number.isFinite(p[0]) && Number.isFinite(p[1])) {
      out.push([Math.max(-BOX + 0.3, Math.min(BOX - 0.3, p[0])), Math.max(-BOX + 0.3, Math.min(BOX - 0.3, p[1]))]);
    }
    if (out.length === 2) break;
  }
  return out.length ? out : null;
}
