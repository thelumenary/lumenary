/**
 * Time-telling helpers for AnalogClock. A time is a whole number of minutes
 * after midnight (0–1439). The hands are always consistent: the minute hand
 * turns 6° per minute and the hour hand 0.5° per minute.
 */

export const DAY = 24 * 60;

export const normTime = (t: number) => ((Math.round(t) % DAY) + DAY) % DAY;

export const toTime = (hours: number, minutes: number) => normTime(hours * 60 + minutes);

/** Hand angles in degrees, clockwise from 12. */
export function handAngles(t: number): { minute: number; hour: number } {
  const x = normTime(t);
  return { minute: (x % 60) * 6, hour: (x % 720) * 0.5 };
}

const pad2 = (v: number) => String(v).padStart(2, "0");

/** "15:05" */
export function format24(t: number): string {
  const x = normTime(t);
  return `${pad2(Math.floor(x / 60))}:${pad2(x % 60)}`;
}

/** 12-hour parts: { h: 3, mm: "05", period: "pm" }. Midnight is 12 a.m., noon is 12 p.m. */
export function parts12(t: number): { h: number; mm: string; period: "am" | "pm" } {
  const x = normTime(t);
  const h24 = Math.floor(x / 60);
  return { h: ((h24 + 11) % 12) + 1, mm: pad2(x % 60), period: h24 < 12 ? "am" : "pm" };
}

/** Whole minute (0–59) pointed at by a hand at `deg` degrees clockwise from 12. */
export const minuteFromAngle = (deg: number) => ((Math.round((((deg % 360) + 360) % 360) / 6) % 60) + 60) % 60;

/**
 * Minutes to add so the minute hand points at minute m (0–59), taking the
 * shorter way round. Passing 12 carries the hour, so dragging round and round
 * moves the hour hand on (or back).
 */
export function minuteHandDelta(t: number, m: number): number {
  const x = normTime(t);
  let delta = (((Math.round(m) - (x % 60)) % 60) + 60) % 60;
  if (delta > 30) delta -= 60;
  return delta;
}

export const setMinuteHand = (t: number, m: number) => normTime(t + minuteHandDelta(t, m));

/** Minutes to add so the hour hand points at `deg` degrees (the minutes follow: the hour hand points between the numbers). */
export function hourHandDelta(t: number, deg: number): number {
  const x = normTime(t);
  const target = Math.round((((deg % 360) + 360) % 360) * 2) % 720;
  let delta = (((target - (x % 720)) % 720) + 720) % 720;
  if (delta > 360) delta -= 720;
  return delta;
}

export const setHourHand = (t: number, deg: number) => normTime(t + hourHandDelta(t, deg));

/** Hours and minutes in a duration. */
export const splitDuration = (mins: number) => ({ h: Math.floor(Math.max(0, mins) / 60), m: Math.max(0, mins) % 60 });

/**
 * Words for a time on the 12-hour clock, as a message key and its variables:
 * o'clock, quarter/half past, quarter to, "m past h" (m ≤ 30) and "m to h+1".
 */
export function timeWords(t: number): { key: string; vars: Record<string, number> } {
  const x = normTime(t);
  const m = x % 60;
  const h = ((Math.floor(x / 60) + 11) % 12) + 1;
  const next = (h % 12) + 1;
  if (m === 0) return { key: "oclock", vars: { h } };
  if (m === 15) return { key: "quarterPast", vars: { h } };
  if (m === 30) return { key: "halfPast", vars: { h } };
  if (m === 45) return { key: "quarterTo", vars: { h: next } };
  if (m < 30) return { key: m === 1 ? "minutePast" : "past", vars: { m, h } };
  return { key: 60 - m === 1 ? "minuteTo" : "to", vars: { m: 60 - m, h: next } };
}

/**
 * The "count on" strategy for elapsed time: from the start, jump to the next
 * o'clock, then whole hours, then the remaining minutes. Each jump has a start,
 * an end and a length in minutes; together they add up to `mins`.
 */
export function elapsedJumps(start: number, mins: number): { from: number; to: number; minutes: number }[] {
  const total = Math.max(0, Math.round(mins));
  const jumps: { from: number; to: number; minutes: number }[] = [];
  let at = normTime(start);
  let left = total;
  const toHour = (60 - (at % 60)) % 60;
  if (toHour > 0 && left >= toHour) {
    jumps.push({ from: at, to: normTime(at + toHour), minutes: toHour });
    at = normTime(at + toHour);
    left -= toHour;
  }
  const hours = Math.floor(left / 60);
  if (hours > 0) {
    jumps.push({ from: at, to: normTime(at + hours * 60), minutes: hours * 60 });
    at = normTime(at + hours * 60);
    left -= hours * 60;
  }
  if (left > 0) jumps.push({ from: at, to: normTime(at + left), minutes: left });
  return jumps;
}
