/** Answer parsing shared by the browser and the test-suite. */

const DIGIT_SETS = ["٠١٢٣٤٥٦٧٨٩", "۰۱۲۳۴۵۶۷۸۹", "०१२३४५६७८९", "০১২৩৪৫৬৭৮৯", "０１２３４５６７８９"];

/** Convert regional digits (Arabic-Indic, Persian, Devanagari, Bengali, full-width) to ASCII. */
export function normalizeDigits(text: string): string {
  let out = text;
  for (const set of DIGIT_SETS) {
    for (let d = 0; d < 10; d++) out = out.replaceAll(set[d], String(d));
  }
  return out;
}

/** Parse an integer answer; accepts −, ‒, – and regional numerals. Returns null if unreadable. */
export function parseInteger(input: string): number | null {
  const s = normalizeDigits(input).replace(/[−‒–—﹣－]/g, "-").replace(/\s+/g, "");
  if (!/^[+-]?\d+$/.test(s)) return null;
  const n = Number(s);
  return Number.isSafeInteger(n) ? n : null;
}

/** Canonical form of one set element as typed by a learner. */
export function normalizeElement(el: string): string {
  return normalizeDigits(el)
    .trim()
    .replace(/^["'“”‘’]+|["'“”‘’]+$/g, "")
    .replace(/[−‒–—]/g, "-")
    .replace(/\s+/g, " ")
    .toLowerCase();
}

/**
 * Parse a set like "{1, 2, 3}", "1,2,3", "{}", "∅". Order and repetition are
 * ignored — exactly as for sets. Returns null if braces are unbalanced.
 */
export function parseSet(input: string): Set<string> | null {
  let s = input.trim();
  if (s === "∅" || s === "{}" || s === "｛｝") return new Set();
  s = s.replace(/[｛]/g, "{").replace(/[｝]/g, "}").replace(/[،、，;]/g, ",");
  const open = s.startsWith("{");
  const close = s.endsWith("}");
  if (open !== close) return null;
  if (open) s = s.slice(1, -1);
  if (s.includes("{") || s.includes("}")) return null;
  const parts = s
    .split(",")
    .map(normalizeElement)
    .filter((p) => p.length > 0);
  return new Set(parts);
}

export function setsEqual(a: Set<string>, b: Set<string>): boolean {
  if (a.size !== b.size) return false;
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

/** Stable printable key for a set answer (sorted), used to match feedback rules. */
export function setKey(s: Set<string>): string {
  return [...s].sort().join(",");
}
