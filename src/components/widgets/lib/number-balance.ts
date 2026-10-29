/** Linear equations as a balance scale: sides, "same move on both sides", and solving. */
import { gcd } from "./number-common";

export interface Side {
  /** Number of x-boxes (negative = x-balloons). */
  x: number;
  /** Unit weights (negative = balloons). */
  units: number;
}

export type Move = { kind: "addUnit" } | { kind: "subUnit" } | { kind: "addX" } | { kind: "subX" } | { kind: "divide"; k: number };

export type Rejection = "noUnits" | "noX" | "notDivisible" | "badDivisor" | "limit";

export type MoveResult = { ok: true; left: Side; right: Side } | { ok: false; reason: Rejection };

/** Largest count of any one kind of object allowed on a pan. */
export const PAN_LIMIT = 20;

/** Read a side from MDX props; malformed values become 0 and counts are clamped to ±PAN_LIMIT. */
export function readSide(raw: unknown, fallback: Side): Side {
  if (!raw || typeof raw !== "object") return fallback;
  const r = raw as Record<string, unknown>;
  const num = (v: unknown) => (typeof v === "number" && Number.isFinite(v) ? Math.max(-PAN_LIMIT, Math.min(PAN_LIMIT, Math.round(v))) : 0);
  return { x: num(r.x), units: num(r.units) };
}

/** Apply the same move to both sides, or explain why it is not allowed. */
export function applyMove(left: Side, right: Side, move: Move, allowNegative: boolean): MoveResult {
  const both = (f: (s: Side) => Side): MoveResult => {
    const l = f(left);
    const r = f(right);
    const all = [l.x, l.units, r.x, r.units];
    if (all.some((v) => Math.abs(v) > PAN_LIMIT)) return { ok: false, reason: "limit" };
    return { ok: true, left: l, right: r };
  };
  switch (move.kind) {
    case "addUnit":
      return both((s) => ({ ...s, units: s.units + 1 }));
    case "subUnit":
      if (!allowNegative && (left.units < 1 || right.units < 1)) return { ok: false, reason: "noUnits" };
      return both((s) => ({ ...s, units: s.units - 1 }));
    case "addX":
      return both((s) => ({ ...s, x: s.x + 1 }));
    case "subX":
      if (!allowNegative && (left.x < 1 || right.x < 1)) return { ok: false, reason: "noX" };
      return both((s) => ({ ...s, x: s.x - 1 }));
    case "divide": {
      const k = move.k;
      if (!Number.isInteger(k) || k < 2) return { ok: false, reason: "badDivisor" };
      if ([left.x, left.units, right.x, right.units].some((v) => v % k !== 0)) return { ok: false, reason: "notDivisible" };
      return { ok: true, left: { x: left.x / k, units: left.units / k }, right: { x: right.x / k, units: right.units / k } };
    }
  }
}

export type Solution = { kind: "unique"; n: number; d: number } | { kind: "none" } | { kind: "all" };

/** Solve left = right for x. A unique solution is returned as a reduced fraction n/d with d > 0. */
export function solve(left: Side, right: Side): Solution {
  const a = left.x - right.x;
  const c = right.units - left.units;
  if (a === 0) return c === 0 ? { kind: "all" } : { kind: "none" };
  const sign = a < 0 ? -1 : 1;
  const g = gcd(c, a) || 1;
  return { kind: "unique", n: (sign * c) / g, d: (sign * a) / g };
}

/** Value of a side when x = n/d, as a fraction with denominator d. */
export const sideValueNumerator = (s: Side, n: number, d: number) => s.x * n + s.units * d;

/** If one side is a lone x and the other has no x, the value of x. */
export function isolatedValue(left: Side, right: Side): number | null {
  if (left.x === 1 && left.units === 0 && right.x === 0) return right.units;
  if (right.x === 1 && right.units === 0 && left.x === 0) return left.units;
  return null;
}

/** If one side is kx (|k| ≥ 2) and the other is c units with k ∤ c, report k and c (x is then c/k). */
export function stuckFraction(left: Side, right: Side): { k: number; c: number } | null {
  const check = (s: Side, o: Side) => (s.units === 0 && Math.abs(s.x) >= 2 && o.x === 0 && o.units % s.x !== 0 ? { k: s.x, c: o.units } : null);
  return check(left, right) ?? check(right, left);
}

/** "2x + 3", "x", "−x − 4", "0". */
export function sideText(s: Side): string {
  const parts: string[] = [];
  if (s.x !== 0) parts.push(s.x === 1 ? "x" : s.x === -1 ? "−x" : `${s.x < 0 ? "−" : ""}${Math.abs(s.x)}x`);
  if (s.units !== 0) {
    if (parts.length === 0) parts.push(s.units < 0 ? `−${-s.units}` : `${s.units}`);
    else parts.push(s.units < 0 ? `− ${-s.units}` : `+ ${s.units}`);
  }
  return parts.length ? parts.join(" ") : "0";
}

export const equationText = (l: Side, r: Side) => `${sideText(l)} = ${sideText(r)}`;

/** Short, language-neutral label for a move ("+1", "−x", "÷3"). */
export function moveText(m: Move): string {
  switch (m.kind) {
    case "addUnit":
      return "+ 1";
    case "subUnit":
      return "− 1";
    case "addX":
      return "+ x";
    case "subX":
      return "− x";
    case "divide":
      return `÷ ${m.k}`;
  }
}
