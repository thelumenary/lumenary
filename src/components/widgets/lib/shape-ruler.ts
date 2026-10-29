/**
 * Measuring helpers for RulerMeasure. Objects have whole-centimetre lengths so
 * every reading on the ruler is exact; non-standard units (paper clips, hand
 * spans) usually do not fit a whole number of times, and the wording says so.
 */
import { clamp } from "./shape-util";

/** Centimetres shown on the ruler. */
export const RULER_CM = 20;

export const OBJECTS = { key: 5, leaf: 7, crayon: 9, feather: 11, spoon: 13, pencil: 15 } as const;
export type ObjectId = keyof typeof OBJECTS;
export const OBJECT_IDS = Object.keys(OBJECTS) as ObjectId[];

/** Non-standard units and their (illustrative) size in centimetres. */
export const UNITS = { smallClip: 3, bigClip: 5, childSpan: 12, adultSpan: 18 } as const;
export type UnitId = keyof typeof UNITS;
export const UNIT_IDS = Object.keys(UNITS) as UnitId[];

/** Keep an object fully on the ruler, starting at a whole centimetre. */
export const clampStart = (start: number, length: number) => clamp(Math.round(start), 0, RULER_CM - length);

export type Verdict = "correct" | "endReading" | "countedMarks" | "wrong";

/**
 * Judge a learner's answer for an object of `length` cm whose left end is at
 * `start` on the ruler. Recognises the two classic mistakes: reading the end
 * mark when the object does not start at 0, and counting marks instead of spaces.
 */
export function judge(answer: number, start: number, length: number): Verdict {
  if (!Number.isFinite(answer)) return "wrong";
  if (answer === length) return "correct";
  if (start > 0 && answer === start + length) return "endReading";
  if (answer === length + 1) return "countedMarks";
  return "wrong";
}

/**
 * How many units fit along a length: the whole number that fit, whether that
 * is exact, and whether the length is nearer the count below or above.
 */
export function unitFit(lengthCm: number, unitCm: number): { whole: number; exact: boolean; nearer: "below" | "above"; ratio: number } {
  const ratio = lengthCm / unitCm;
  const whole = Math.floor(ratio + 1e-9);
  const exact = Math.abs(ratio - Math.round(ratio)) < 1e-9;
  return { whole: exact ? Math.round(ratio) : whole, exact, nearer: ratio - whole < 0.5 ? "below" : "above", ratio };
}

/** A message key and count describing a fit: "exactly 5", "a bit more than 1", "a bit less than 3", "less than 1". */
export function fitWords(lengthCm: number, unitCm: number): { key: "exactly" | "moreThan" | "lessThan" | "lessThanOne"; k: number } {
  const f = unitFit(lengthCm, unitCm);
  if (f.exact) return { key: "exactly", k: f.whole };
  if (f.whole === 0) return { key: "lessThanOne", k: 1 };
  if (f.nearer === "below") return { key: "moreThan", k: f.whole };
  return { key: "lessThan", k: f.whole + 1 };
}
