/**
 * Geodesic triangles in the three constant-curvature geometries:
 *  - the Euclidean plane (K = 0),
 *  - the unit sphere (K = 1; for radius R, K = 1/R² and areas scale by R²),
 *  - the hyperbolic plane in the Poincaré disk model (K = −1).
 * Angles are computed from tangent vectors; areas are computed *independently*
 * by numerical boundary integrals (Stokes/Green), so the widget can show that
 * angle sum − π = K · area as a measurement rather than by assuming it.
 */
import { angle2, angle3, cross2, cross3, dot2, dot3, len2, len3, norm2, norm3, perp2, scale3, sub2, sub3, add3, TAU, type V2, type V3 } from "./topo-vec";

// ---------------------------------------------------------------- plane

/** Interior angles of a Euclidean triangle (radians); NaN-free for degenerate input (returns zeros). */
export function planeAngles(a: V2, b: V2, c: V2): [number, number, number] {
  const at = (p: V2, q: V2, r: V2) => {
    const u = sub2(q, p);
    const v = sub2(r, p);
    return len2(u) < 1e-12 || len2(v) < 1e-12 ? 0 : angle2(u, v);
  };
  return [at(a, b, c), at(b, c, a), at(c, a, b)];
}

// ---------------------------------------------------------------- sphere

/** Latitude/longitude in degrees → unit vector (x toward lon 0, z toward the north pole). */
export function fromLatLon(lat: number, lon: number): V3 {
  const φ = (lat * Math.PI) / 180;
  const λ = (lon * Math.PI) / 180;
  return [Math.cos(φ) * Math.cos(λ), Math.cos(φ) * Math.sin(λ), Math.sin(φ)];
}

export function toLatLon(v: V3): [number, number] {
  const u = norm3(v);
  return [(Math.asin(Math.max(-1, Math.min(1, u[2]))) * 180) / Math.PI, (Math.atan2(u[1], u[0]) * 180) / Math.PI];
}

/** Unit tangent at `p` of the great-circle arc from p toward q. */
export function sphereTangent(p: V3, q: V3): V3 {
  return norm3(sub3(q, scale3(p, dot3(p, q))));
}

/** Interior angles of the spherical triangle with minor-arc sides (radians). */
export function sphereAngles(a: V3, b: V3, c: V3): [number, number, number] {
  const at = (p: V3, q: V3, r: V3) => {
    const t1 = sphereTangent(p, q);
    const t2 = sphereTangent(p, r);
    return len3(t1) < 0.5 || len3(t2) < 0.5 ? 0 : angle3(t1, t2);
  };
  return [at(a, b, c), at(b, c, a), at(c, a, b)];
}

/** Closed-form area on the unit sphere (Van Oosterom–Strackee), used only to cross-check in tests. */
export function sphereAreaFormula(a: V3, b: V3, c: V3): number {
  const num = Math.abs(dot3(a, cross3(b, c)));
  const den = 1 + dot3(a, b) + dot3(b, c) + dot3(c, a);
  return 2 * Math.atan2(num, den);
}

/** Points along the minor great-circle arc from a to b (inclusive), by spherical interpolation. */
export function greatArc(a: V3, b: V3, n = 48): V3[] {
  const ω = angle3(a, b);
  if (ω < 1e-9) return [a, b];
  const s = Math.sin(ω);
  const out: V3[] = [];
  for (let i = 0; i <= n; i++) {
    const t = i / n;
    out.push(add3(scale3(a, Math.sin((1 - t) * ω) / s), scale3(b, Math.sin(t * ω) / s)));
  }
  return out;
}

/**
 * Area of a spherical triangle on the unit sphere by a numerical boundary
 * integral: with polar angle φ measured from the triangle's centroid m (which
 * lies inside the triangle), dA = d(1 − cos φ) ∧ dθ, so A = ∮ (1 − cos φ) dθ.
 */
export function sphereAreaNumeric(a: V3, b: V3, c: V3, perSide = 240): number {
  const m = norm3(add3(add3(a, b), c));
  if (len3(m) < 0.5) return NaN;
  const helper: V3 = Math.abs(m[0]) < 0.9 ? [1, 0, 0] : [0, 1, 0];
  const e1 = norm3(sub3(helper, scale3(m, dot3(helper, m))));
  const e2 = cross3(m, e1);
  const pts = [...greatArc(a, b, perSide).slice(0, -1), ...greatArc(b, c, perSide).slice(0, -1), ...greatArc(c, a, perSide).slice(0, -1)];
  let area = 0;
  for (let i = 0; i < pts.length; i++) {
    const p = pts[i];
    const q = pts[(i + 1) % pts.length];
    const θp = Math.atan2(dot3(p, e2), dot3(p, e1));
    const θq = Math.atan2(dot3(q, e2), dot3(q, e1));
    let dθ = θq - θp;
    if (dθ > Math.PI) dθ -= TAU;
    if (dθ < -Math.PI) dθ += TAU;
    const zMid = (dot3(p, m) + dot3(q, m)) / 2;
    area += (1 - zMid) * dθ;
  }
  return Math.abs(area);
}

/** Small triangles covering a spherical triangle (for shading it). */
export function sphereMesh(a: V3, b: V3, c: V3, n = 14): V3[][] {
  const P = (i: number, j: number): V3 => {
    const k = n - i - j;
    return norm3(add3(add3(scale3(a, k / n), scale3(b, i / n)), scale3(c, j / n)));
  };
  const tris: V3[][] = [];
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n - i; j++) {
      tris.push([P(i, j), P(i + 1, j), P(i, j + 1)]);
      if (i + j < n - 1) tris.push([P(i + 1, j), P(i + 1, j + 1), P(i, j + 1)]);
    }
  return tris;
}

// ---------------------------------------------------------------- hyperbolic (Poincaré disk)

export type Geodesic = { kind: "line" } | { kind: "arc"; c: V2; r: number };

/** The hyperbolic geodesic through p and q: a diameter-line or a circle orthogonal to the unit circle. */
export function geodesic(p: V2, q: V2): Geodesic {
  const det = cross2(p, q);
  if (Math.abs(det) < 1e-9) return { kind: "line" };
  // c·p = (|p|² + 1)/2 and c·q = (|q|² + 1)/2  (orthogonality to the unit circle)
  const bp = (dot2(p, p) + 1) / 2;
  const bq = (dot2(q, q) + 1) / 2;
  const c: V2 = [(bp * q[1] - bq * p[1]) / det, (p[0] * bq - q[0] * bp) / det];
  const r = Math.sqrt(Math.max(0, dot2(c, c) - 1));
  return { kind: "arc", c, r };
}

/** Unit tangent at p of the geodesic segment from p to q. */
export function hypTangent(p: V2, q: V2): V2 {
  const g = geodesic(p, q);
  if (g.kind === "line") return norm2(sub2(q, p));
  const t = norm2(perp2(sub2(p, g.c)));
  return dot2(t, sub2(q, p)) >= 0 ? t : [-t[0], -t[1]];
}

/** Interior angles of a hyperbolic triangle: the model is conformal, so these are Euclidean angles between tangents. */
export function hypAngles(a: V2, b: V2, c: V2): [number, number, number] {
  const at = (p: V2, q: V2, r: V2) => {
    if (len2(sub2(q, p)) < 1e-9 || len2(sub2(r, p)) < 1e-9) return 0;
    return angle2(hypTangent(p, q), hypTangent(p, r));
  };
  return [at(a, b, c), at(b, c, a), at(c, a, b)];
}

/** Points along the geodesic segment from p to q (inclusive). */
export function hypSegment(p: V2, q: V2, n = 64): V2[] {
  const g = geodesic(p, q);
  const out: V2[] = [];
  if (g.kind === "line") {
    for (let i = 0; i <= n; i++) out.push([p[0] + ((q[0] - p[0]) * i) / n, p[1] + ((q[1] - p[1]) * i) / n]);
    return out;
  }
  const a0 = Math.atan2(p[1] - g.c[1], p[0] - g.c[0]);
  let da = Math.atan2(q[1] - g.c[1], q[0] - g.c[0]) - a0;
  if (da > Math.PI) da -= TAU;
  if (da < -Math.PI) da += TAU;
  for (let i = 0; i <= n; i++) {
    const a = a0 + (da * i) / n;
    out.push([g.c[0] + g.r * Math.cos(a), g.c[1] + g.r * Math.sin(a)]);
  }
  return out;
}

/** The two ideal endpoints (on the unit circle) of the full geodesic through p and q. */
export function hypEndpoints(p: V2, q: V2): [V2, V2] {
  const g = geodesic(p, q);
  if (g.kind === "line") {
    const d = norm2(sub2(q, p));
    const u = len2(d) > 0 ? d : ([1, 0] as V2);
    // the line through p in direction u meets the unit circle where |p + t u| = 1
    const b = dot2(p, u);
    const disc = Math.sqrt(Math.max(0, b * b - (dot2(p, p) - 1)));
    return [[p[0] + (-b - disc) * u[0], p[1] + (-b - disc) * u[1]], [p[0] + (-b + disc) * u[0], p[1] + (-b + disc) * u[1]]];
  }
  const L = len2(g.c);
  const e: V2 = [g.c[0] / L, g.c[1] / L];
  const δ = Math.acos(Math.min(1, 1 / L));
  const rot = (v: V2, a: number): V2 => [v[0] * Math.cos(a) - v[1] * Math.sin(a), v[0] * Math.sin(a) + v[1] * Math.cos(a)];
  return [rot(e, -δ), rot(e, δ)];
}

/**
 * Hyperbolic area (curvature −1) by a numerical boundary integral.
 * The area form 4 dx∧dy / (1 − r²)² equals d( 2(x dy − y dx) / (1 − r²) ), so
 * by Green's theorem the area is ∮ 2(x dy − y dx) / (1 − r²) around the triangle.
 */
export function hypAreaNumeric(a: V2, b: V2, c: V2, perSide = 400): number {
  const pts = [...hypSegment(a, b, perSide).slice(0, -1), ...hypSegment(b, c, perSide).slice(0, -1), ...hypSegment(c, a, perSide).slice(0, -1)];
  let s = 0;
  for (let i = 0; i < pts.length; i++) {
    const p = pts[i];
    const q = pts[(i + 1) % pts.length];
    const mx = (p[0] + q[0]) / 2;
    const my = (p[1] + q[1]) / 2;
    const r2 = mx * mx + my * my;
    s += (2 * (mx * (q[1] - p[1]) - my * (q[0] - p[0]))) / (1 - r2);
  }
  return Math.abs(s);
}

/** Keep a point strictly inside the disk (|z| ≤ max). */
export function clampDisk(p: V2, max = 0.93): V2 {
  const l = len2(p);
  return l > max ? [(p[0] / l) * max, (p[1] / l) * max] : p;
}
