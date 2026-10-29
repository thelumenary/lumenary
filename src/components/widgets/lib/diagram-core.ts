/**
 * Geometry for CommutativeDiagram: objects on a grid, arrows clipped to the
 * object boxes, parallel pairs, bent arrows, tikz-cd-style label placement,
 * and a plain-text reading of each arrow for screen readers.
 */

export type Pt = { x: number; y: number };
export const ARROW_STYLES = ["solid", "dashed", "hook", "epi", "double", "iso"] as const;
export type ArrowStyle = (typeof ARROW_STYLES)[number];
export type DiagramSize = "sm" | "md" | "lg";

export interface DObject {
  id: string;
  tex: string;
  row: number;
  col: number;
}
export interface DArrow {
  from: string;
  to: string;
  tex: string;
  style: ArrowStyle;
  bend: number;
  labelSide: "left" | "right";
}

export const SIZES: Record<DiagramSize, { colGap: number; rowGap: number; font: number; labelFont: number }> = {
  sm: { colGap: 92, rowGap: 74, font: 15, labelFont: 12.5 },
  md: { colGap: 124, rowGap: 96, font: 17, labelFont: 14 },
  lg: { colGap: 160, rowGap: 124, font: 20, labelFont: 16 },
};

/** KaTeX scales its own text by 1.21. */
export const KATEX_SCALE = 1.21;

/* ------------------------------------------------------------------------ */
/* Input normalisation                                                       */
/* ------------------------------------------------------------------------ */

/**
 * Undo JavaScript string escapes that authors trigger by writing single
 * backslashes inside MDX {…} expressions: "\to" arrives as TAB + "o",
 * "\frac" as FORMFEED + "rac", "\beta" as BACKSPACE + "eta", and so on.
 */
export function repairTex(s: string): string {
  return s.replace(/[\t\f\b\v\r\n]/g, (c) => ({ "\t": "\\t", "\f": "\\f", "\b": "\\b", "\v": "\\v", "\r": "\\r", "\n": "\\n" })[c] ?? c);
}

const str = (v: unknown): string => (typeof v === "string" ? v : typeof v === "number" && Number.isFinite(v) ? String(v) : "");
const num = (v: unknown): number | null => {
  const x = typeof v === "number" ? v : typeof v === "string" && v.trim() !== "" ? Number(v) : NaN;
  return Number.isFinite(x) ? x : null;
};

export function normaliseDiagram(objectsIn: unknown, arrowsIn: unknown): { objects: DObject[]; arrows: DArrow[]; ignored: number } {
  let ignored = 0;
  const objects: DObject[] = [];
  const ids = new Set<string>();
  for (const o of Array.isArray(objectsIn) ? objectsIn.slice(0, 40) : []) {
    if (!o || typeof o !== "object") {
      ignored++;
      continue;
    }
    const rec = o as Record<string, unknown>;
    const id = str(rec.id).trim();
    const row = num(rec.row);
    const col = num(rec.col);
    if (!id || ids.has(id) || row === null || col === null) {
      ignored++;
      continue;
    }
    ids.add(id);
    const tex = repairTex(str(rec.tex)) || id;
    objects.push({ id, tex: tex.slice(0, 200), row: clamp(row, -20, 20), col: clamp(col, -20, 20) });
  }
  const arrows: DArrow[] = [];
  for (const a of Array.isArray(arrowsIn) ? arrowsIn.slice(0, 60) : []) {
    if (!a || typeof a !== "object") {
      ignored++;
      continue;
    }
    const rec = a as Record<string, unknown>;
    const from = str(rec.from).trim();
    const to = str(rec.to).trim();
    if (!ids.has(from) || !ids.has(to) || from === to) {
      ignored++;
      continue;
    }
    const style = (ARROW_STYLES as readonly string[]).includes(str(rec.style)) ? (str(rec.style) as ArrowStyle) : "solid";
    const bend = clamp(num(rec.bend) ?? 0, -75, 75);
    const labelSide = rec.labelSide === "right" ? "right" : "left";
    arrows.push({ from, to, tex: repairTex(str(rec.tex)).slice(0, 200), style, bend, labelSide });
  }
  return { objects, arrows, ignored };
}

const clamp = (v: number, lo: number, hi: number) => Math.max(lo, Math.min(hi, v));

/* ------------------------------------------------------------------------ */
/* TeX size estimates (we cannot measure on the server)                      */
/* ------------------------------------------------------------------------ */

const BIN = new Set(["times", "otimes", "oplus", "circ", "cdot", "cup", "cap", "wedge", "vee", "setminus", "ast", "star", "sqcup", "amalg", "pm", "mp", "bullet", "boxtimes", "odot", "sqcap"]);
const REL = new Set(["to", "rightarrow", "leftarrow", "gets", "cong", "simeq", "sim", "approx", "equiv", "le", "ge", "leq", "geq", "subset", "subseteq", "supset", "supseteq", "in", "ni", "mapsto", "hookrightarrow", "twoheadrightarrow", "Rightarrow", "Leftarrow", "neq", "ne", "iff", "implies", "longrightarrow", "rightleftarrows", "leftrightarrow", "trianglelefteq", "lhd", "triangleleft"]);
const ZERO = new Set(["left", "right", "big", "Big", "bigg", "Bigg", "bigl", "bigr", "Bigl", "Bigr", "displaystyle", "textstyle", "scriptstyle", "limits", "nolimits", "middle"]);
const FONT = new Set(["mathbf", "mathrm", "mathbb", "mathcal", "mathfrak", "mathsf", "mathit", "mathscr", "boldsymbol", "bm", "mathtt", "mathnormal", "cat", "operatorname", "text", "textrm", "textbf", "textit", "textsf", "mbox"]);
const ACCENT = new Set(["overline", "underline", "hat", "widehat", "bar", "tilde", "widetilde", "vec", "dot", "ddot", "check", "breve", "acute", "grave"]);
const OPNAMES = new Set(["ker", "coker", "im", "Im", "Hom", "End", "Aut", "id", "sin", "cos", "tan", "log", "ln", "exp", "lim", "det", "dim", "max", "min", "sup", "inf", "deg", "gcd", "Spec", "Tor", "Ext", "colim", "rank", "Mor", "Ob", "op"]);
const SPACES: Record<string, number> = { ",": 0.17, ":": 0.22, ">": 0.22, ";": 0.28, "!": -0.17, " ": 0.33, quad: 1, qquad: 2, enspace: 0.5, thinspace: 0.17 };

interface Measure {
  w: number;
  /** extra height above/below one line, in em */
  tall: number;
}

/** Rough width (in em of the KaTeX font) and extra height of a TeX string. */
export function measureTex(tex: string): Measure {
  let i = 0;
  const s = tex;
  const readGroup = (): Measure => {
    // Called with s[i] === "{"
    i++;
    const m = seq("}");
    i++;
    return m;
  };
  const readArg = (): Measure => {
    while (s[i] === " ") i++;
    if (s[i] === "{") return readGroup();
    if (s[i] === "\\") return atom();
    const ch = s[i++] ?? "";
    return { w: charWidth(ch, false), tall: 0 };
  };
  const readRawArg = (): string => {
    while (s[i] === " ") i++;
    if (s[i] !== "{") return s[i++] ?? "";
    let depth = 0;
    const start = i;
    for (; i < s.length; i++) {
      if (s[i] === "{") depth++;
      else if (s[i] === "}" && --depth === 0) break;
    }
    i++;
    return s.slice(start + 1, i - 1);
  };
  const atom = (): Measure => {
    const ch = s[i];
    if (ch === "\\") {
      i++;
      let name = "";
      if (/[A-Za-z]/.test(s[i] ?? "")) while (/[A-Za-z]/.test(s[i] ?? "")) name += s[i++];
      else name = s[i++] ?? "";
      if (name in SPACES) return { w: SPACES[name], tall: 0 };
      if (ZERO.has(name)) return { w: 0, tall: 0 };
      if (BIN.has(name)) return { w: 1.22, tall: 0 };
      if (REL.has(name)) return { w: name.startsWith("long") ? 2.1 : 1.55, tall: 0 };
      if (name === "frac" || name === "dfrac" || name === "tfrac" || name === "binom") {
        const a = readArg();
        const b = readArg();
        return { w: Math.max(a.w, b.w) * 0.85 + 0.25, tall: 0.9 + Math.max(a.tall, b.tall) };
      }
      if (name === "sqrt") return { w: readArg().w + 0.85, tall: 0.15 };
      if (ACCENT.has(name)) {
        const a = readArg();
        return { w: a.w, tall: a.tall + 0.15 };
      }
      if (FONT.has(name)) {
        const raw = readRawArg();
        const roman = name !== "mathit" && name !== "mathnormal" && name !== "boldsymbol" && name !== "bm";
        const inner = /[\\{^_]/.test(raw) ? measureTex(raw) : { w: [...raw].reduce((w, c) => w + charWidth(c, roman), 0), tall: 0 };
        return { w: inner.w * (name === "mathbb" || name === "mathcal" || name === "mathscr" ? 1.05 : name === "mathbf" ? 1.1 : 1), tall: inner.tall };
      }
      if (OPNAMES.has(name)) return { w: name.length * 0.5 + 0.17, tall: 0 };
      if (name === "{" || name === "}" || name === "|") return { w: 0.5, tall: 0 };
      if (name === "ldots" || name === "cdots" || name === "dots") return { w: 1.2, tall: 0 };
      return { w: 0.68, tall: 0 }; // Greek letters and other symbols
    }
    if (ch === "{") return readGroup();
    i++;
    return { w: charWidth(ch, false), tall: 0 };
  };
  const seq = (stop?: string): Measure => {
    let w = 0;
    let tall = 0;
    let lastScript = -1;
    while (i < s.length && s[i] !== stop) {
      const ch = s[i];
      if (ch === "^" || ch === "_") {
        i++;
        const a = readArg();
        const sw = a.w * 0.72;
        if (lastScript >= 0) w += Math.max(0, sw - lastScript);
        else w += sw + 0.05;
        lastScript = sw;
        tall = Math.max(tall, 0.25 + a.tall * 0.7);
        continue;
      }
      lastScript = -1;
      const m = atom();
      w += m.w;
      tall = Math.max(tall, m.tall);
    }
    return { w, tall };
  };
  try {
    const m = seq();
    return { w: Math.max(0.5, m.w), tall: m.tall };
  } catch {
    return { w: Math.max(0.6, tex.length * 0.55), tall: 0 };
  }
}

function charWidth(ch: string, roman: boolean): number {
  if (/[A-Z]/.test(ch)) return roman ? 0.72 : 0.76;
  if (/[a-z]/.test(ch)) return roman ? 0.5 : "ijlt".includes(ch) ? 0.36 : "mw".includes(ch) ? 0.85 : 0.55;
  if (/[0-9]/.test(ch)) return 0.5;
  if ("+-*".includes(ch)) return 1.22;
  if ("=<>".includes(ch)) return 1.33;
  if ("()[]|".includes(ch)) return 0.39;
  if (ch === "/") return 0.5;
  if (ch === ",") return 0.45;
  if (ch === ";" || ch === ":") return 0.5;
  if (ch === "." || ch === "'") return 0.3;
  if (ch === " " || ch === "~") return roman ? 0.33 : ch === "~" ? 0.33 : 0;
  if (ch === "&" || ch === "\\") return 0;
  return 0.7;
}

/* ------------------------------------------------------------------------ */
/* Plain text for screen readers                                             */
/* ------------------------------------------------------------------------ */

const TEXT_CMDS: Record<string, string> = {
  to: "→", rightarrow: "→", leftarrow: "←", gets: "←", mapsto: "↦", hookrightarrow: "↪", twoheadrightarrow: "↠", Rightarrow: "⇒", times: "×", otimes: "⊗", oplus: "⊕", circ: "∘", cdot: "·", cong: "≅", simeq: "≃", sim: "∼", cup: "∪", cap: "∩", setminus: "∖", ast: "∗", star: "⋆", prime: "′", infty: "∞", emptyset: "∅", varnothing: "∅", colon: ":", in: "∈", subseteq: "⊆", subset: "⊂", le: "≤", leq: "≤", ge: "≥", geq: "≥", neq: "≠", ldots: "…", cdots: "⋯", dots: "…", lhd: "◁", trianglelefteq: "⊴", sqcup: "⊔", amalg: "⨿", wedge: "∧", vee: "∨", pm: "±",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", iota: "ι", kappa: "κ", lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", pi: "π", rho: "ρ", sigma: "σ", tau: "τ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π", Sigma: "Σ", Phi: "Φ", Psi: "Ψ", Omega: "Ω",
  N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", "{": "{", "}": "}", "|": "‖",
};
const BB: Record<string, string> = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽", A: "𝔸" };
const SUP: Record<string, string> = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "-": "⁻", "+": "⁺", "*": "*", "′": "′" };
const SUB: Record<string, string> = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉" };

/** A readable plain-text rendering of simple TeX ("A \times B" → "A × B"). */
export function texToText(tex: string): string {
  let i = 0;
  const s = tex;
  const group = (): string => {
    while (s[i] === " ") i++;
    if (s[i] === "{") {
      i++;
      const out = seq("}");
      i++;
      return out;
    }
    if (s[i] === "\\") return cmd();
    return s[i++] ?? "";
  };
  const cmd = (): string => {
    i++;
    let name = "";
    if (/[A-Za-z]/.test(s[i] ?? "")) while (/[A-Za-z]/.test(s[i] ?? "")) name += s[i++];
    else name = s[i++] ?? "";
    if (name in SPACES) return " ";
    if (ZERO.has(name)) return "";
    if (name === "mathbb") {
      const g = group();
      return BB[g] ?? g;
    }
    if (FONT.has(name) || ACCENT.has(name)) return group();
    if (name === "frac" || name === "dfrac" || name === "tfrac") {
      const a = group();
      const b = group();
      return `${a}/${b}`;
    }
    if (name === "sqrt") return `√(${group()})`;
    if (name in TEXT_CMDS) return TEXT_CMDS[name];
    if (name === "\\") return " ";
    return name;
  };
  const seq = (stop?: string): string => {
    let out = "";
    while (i < s.length && s[i] !== stop) {
      const ch = s[i];
      if (ch === "^" || ch === "_") {
        i++;
        const g = group().trim();
        const map = ch === "^" ? SUP : SUB;
        if (g === "\\prime" || g === "′") out += "′";
        else if ([...g].every((c) => c in map)) out += [...g].map((c) => map[c]).join("");
        else out += ch === "^" ? `^${g.length > 1 ? `(${g})` : g}` : ` ${g}`;
        continue;
      }
      if (ch === "\\") out += cmd();
      else if (ch === "{") {
        i++;
        out += seq("}");
        i++;
      } else if (ch === "'") {
        out += "′";
        i++;
      } else if (ch === "~") {
        out += " ";
        i++;
      } else {
        out += ch;
        i++;
      }
    }
    return out;
  };
  try {
    return seq()
      .replace(/\s+/g, " ")
      .replace(/\s*([×⊗⊕∘·→←↦⇒≅≃∪∩])\s*/g, " $1 ")
      .replace(/\s+/g, " ")
      .trim();
  } catch {
    return tex;
  }
}

const STYLE_WORD: Record<ArrowStyle, string> = { solid: "", dashed: "dashed", hook: "hooked, injective", epi: "two-headed, surjective", double: "double", iso: "isomorphism" };

/** "f from A to B" style descriptions, joined for an aria-label. */
export function describeDiagram(objects: DObject[], arrows: DArrow[]): string {
  const name = new Map(objects.map((o) => [o.id, texToText(o.tex) || o.id]));
  const parts = arrows.map((a) => {
    const label = a.tex ? texToText(a.tex) : "";
    const extra = STYLE_WORD[a.style];
    const head = label ? (extra ? `${label} (${extra})` : label) : extra ? `${extra} arrow` : "arrow";
    return `${head} from ${name.get(a.from)} to ${name.get(a.to)}`;
  });
  const objs = objects.map((o) => name.get(o.id)).join(", ");
  return parts.length ? `Diagram with objects ${objs}. Arrows: ${parts.join("; ")}.` : `Diagram with objects ${objs}.`;
}

/* ------------------------------------------------------------------------ */
/* Layout                                                                    */
/* ------------------------------------------------------------------------ */

export interface NodeBox {
  id: string;
  tex: string;
  cx: number;
  cy: number;
  /** half extents of the (estimated) typeset box */
  hw: number;
  hh: number;
}

export interface LabelBox {
  tex: string;
  cx: number;
  cy: number;
  hw: number;
  hh: number;
}

export interface ArrowShape {
  arrow: DArrow;
  /** Shaft path(s): one for most styles, two for "double". */
  shafts: string[];
  /** Arrowhead strokes (two for "epi"). */
  heads: string[];
  /** Hook at the tail ("hook" style). */
  hook?: string;
  label?: LabelBox;
  /** Position for the ≅ mark ("iso" style). */
  iso?: Pt;
  start: Pt;
  end: Pt;
  control: Pt;
}

export interface DiagramLayout {
  viewBox: { x: number; y: number; w: number; h: number };
  nodes: NodeBox[];
  arrows: ArrowShape[];
  font: number;
  labelFont: number;
}

const add = (a: Pt, b: Pt): Pt => ({ x: a.x + b.x, y: a.y + b.y });
const sub = (a: Pt, b: Pt): Pt => ({ x: a.x - b.x, y: a.y - b.y });
const mul = (a: Pt, k: number): Pt => ({ x: a.x * k, y: a.y * k });
const unit = (a: Pt): Pt => {
  const l = Math.hypot(a.x, a.y);
  return l > 1e-9 ? { x: a.x / l, y: a.y / l } : { x: 1, y: 0 };
};
/** Left of the direction of travel, in screen coordinates (y down). */
const leftOf = (u: Pt): Pt => ({ x: u.y, y: -u.x });
const f = (v: number) => (Math.round(v * 100) / 100).toString();
const P = (p: Pt) => `${f(p.x)} ${f(p.y)}`;

export function bezier(p0: Pt, c: Pt, p2: Pt, t: number): Pt {
  const s = 1 - t;
  return { x: s * s * p0.x + 2 * s * t * c.x + t * t * p2.x, y: s * s * p0.y + 2 * s * t * c.y + t * t * p2.y };
}

const insideBox = (p: Pt, n: NodeBox, m: number) => Math.abs(p.x - n.cx) <= n.hw + m && Math.abs(p.y - n.cy) <= n.hh + m;

/** Parameter where the curve leaves the box around `n` (searching from `fromStart` end). */
function exitParam(p0: Pt, c: Pt, p2: Pt, n: NodeBox, m: number, fromStart: boolean): number {
  const at = (t: number) => bezier(p0, c, p2, fromStart ? t : 1 - t);
  if (!insideBox(at(0), n, m)) return fromStart ? 0 : 1;
  let lo = 0;
  let hi = 0.5;
  if (insideBox(at(hi), n, m)) hi = 0.49; // objects overlap: give up gracefully
  for (let k = 0; k < 30; k++) {
    const mid = (lo + hi) / 2;
    if (insideBox(at(mid), n, m)) lo = mid;
    else hi = mid;
  }
  return fromStart ? hi : 1 - hi;
}

/** Control point of the sub-curve on [a, b] (blossom of the quadratic). */
function subControl(p0: Pt, c: Pt, p2: Pt, a: number, b: number): Pt {
  const w0 = (1 - a) * (1 - b);
  const w1 = (1 - a) * b + a * (1 - b);
  const w2 = a * b;
  return { x: w0 * p0.x + w1 * c.x + w2 * p2.x, y: w0 * p0.y + w1 * c.y + w2 * p2.y };
}

function arrowhead(tip: Pt, u: Pt, L: number, W: number): string {
  const n = leftOf(u);
  const w1 = add(sub(tip, mul(u, L)), mul(n, W));
  const w2 = sub(sub(tip, mul(u, L)), mul(n, W));
  const c1 = add(sub(tip, mul(u, L * 0.42)), mul(n, W * 0.22));
  const c2 = sub(sub(tip, mul(u, L * 0.42)), mul(n, W * 0.22));
  return `M${P(w1)}Q${P(c1)} ${P(tip)}Q${P(c2)} ${P(w2)}`;
}

export function layoutDiagram(objects: DObject[], arrows: DArrow[], size: DiagramSize = "md"): DiagramLayout {
  const spec = SIZES[size] ?? SIZES.md;
  const em = spec.font * KATEX_SCALE;
  const lem = spec.labelFont * KATEX_SCALE;
  const k = spec.font / 17; // stroke geometry scale
  const nodes: NodeBox[] = objects.map((o) => {
    const m = measureTex(o.tex);
    return { id: o.id, tex: o.tex, cx: o.col * spec.colGap, cy: o.row * spec.rowGap, hw: (m.w * em) / 2 + 3, hh: ((1 + m.tall) * em) / 2 };
  });
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const order = new Map(objects.map((o, i) => [o.id, i]));

  // Parallel straight arrows between the same two objects fan out sideways.
  const groups = new Map<string, number[]>();
  arrows.forEach((a, i) => {
    if (a.bend !== 0) return;
    const key = [a.from, a.to].sort((x, y) => order.get(x)! - order.get(y)!).join("\u0000");
    groups.set(key, [...(groups.get(key) ?? []), i]);
  });
  const offsetOf = new Map<number, number>();
  const gap = 11 * k;
  // The first-listed arrow goes on the left of the canonical direction (on top for a rightward pair).
  for (const idxs of groups.values()) idxs.forEach((ai, j) => offsetOf.set(ai, ((idxs.length - 1) / 2 - j) * gap));

  const margin = 5.5 * k;
  const L = 7 * k;
  const W = 4.3 * k;
  const shapes: ArrowShape[] = arrows.map((a, ai) => {
    const A = byId.get(a.from)!;
    const B = byId.get(a.to)!;
    let p0: Pt = { x: A.cx, y: A.cy };
    let p2: Pt = { x: B.cx, y: B.cy };
    const off = offsetOf.get(ai) ?? 0;
    let outward: Pt | null = null;
    if (off !== 0) {
      // Canonical normal (from the earlier-listed object to the later one) so opposite arrows separate too.
      const [lo, hi] = order.get(a.from)! < order.get(a.to)! ? [p0, p2] : [p2, p0];
      const nrm = leftOf(unit(sub(hi, lo)));
      p0 = add(p0, mul(nrm, off));
      p2 = add(p2, mul(nrm, off));
      outward = mul(nrm, Math.sign(off));
    }
    const chord = sub(p2, p0);
    const len = Math.hypot(chord.x, chord.y);
    const u = unit(chord);
    const mid = mul(add(p0, p2), 0.5);
    const c = a.bend ? add(mid, mul(leftOf(u), (len / 2) * Math.tan((a.bend * Math.PI) / 180))) : mid;

    const t0 = exitParam(p0, c, p2, A, margin, true);
    const t1 = exitParam(p0, c, p2, B, margin, false);
    const s0 = bezier(p0, c, p2, t0);
    const s2 = bezier(p0, c, p2, t1);
    const sc = subControl(p0, c, p2, t0, t1);
    const uEnd = unit(Math.hypot(s2.x - sc.x, s2.y - sc.y) > 1e-6 ? sub(s2, sc) : sub(s2, s0));
    const uStart = unit(Math.hypot(sc.x - s0.x, sc.y - s0.y) > 1e-6 ? sub(sc, s0) : sub(s2, s0));
    const straight = !a.bend;

    const shafts: string[] = [];
    const heads: string[] = [];
    let hook: string | undefined;
    if (a.style === "double") {
      const d = 1.7 * k;
      const back = 3.2 * k;
      const nStart = leftOf(uStart);
      const nEnd = leftOf(uEnd);
      const nMid = leftOf(unit(sub(s2, s0)));
      for (const sgn of [1, -1]) {
        const q0 = add(s0, mul(nStart, d * sgn));
        const q2 = add(sub(s2, mul(uEnd, back)), mul(nEnd, d * sgn));
        const qc = add(sc, mul(nMid, d * sgn));
        shafts.push(straight ? `M${P(q0)}L${P(q2)}` : `M${P(q0)}Q${P(qc)} ${P(q2)}`);
      }
      heads.push(arrowhead(s2, uEnd, L * 1.25, W * 1.5));
    } else {
      shafts.push(straight ? `M${P(s0)}L${P(s2)}` : `M${P(s0)}Q${P(sc)} ${P(s2)}`);
      heads.push(arrowhead(s2, uEnd, L, W));
      if (a.style === "epi") heads.push(arrowhead(sub(s2, mul(uEnd, 4.6 * k)), uEnd, L, W));
      if (a.style === "hook") {
        const r = 3.9 * k;
        const n = leftOf(uStart);
        const top = add(s0, mul(n, 2 * r));
        const kk = 1.33 * r;
        hook = `M${P(top)}C${P(sub(top, mul(uStart, kk)))} ${P(sub(s0, mul(uStart, kk)))} ${P(s0)}`;
      }
    }

    // Labels sit beside the middle of the visible curve, on the requested side (tikz-cd: left = "auto", right = "swap").
    const m = bezier(s0, sc, s2, 0.5);
    const dirMid = unit(sub(s2, s0));
    // In a parallel pair the label always goes on the outer side, away from its partner.
    const side = outward ? (leftOf(dirMid).x * outward.x + leftOf(dirMid).y * outward.y >= 0 ? 1 : -1) : a.labelSide === "right" ? -1 : 1;
    const nSide = mul(leftOf(dirMid), side);
    let label: LabelBox | undefined;
    if (a.tex) {
      const ms = measureTex(a.tex);
      const hw = (ms.w * lem) / 2 + 1;
      const hh = ((0.9 + ms.tall) * lem) / 2;
      const dist = 3.5 * k + Math.abs(nSide.x) * hw + Math.abs(nSide.y) * hh + (a.style === "double" ? 2 * k : 0);
      const at = add(m, mul(nSide, dist));
      label = { tex: a.tex, cx: at.x, cy: at.y, hw, hh };
    }
    let iso: Pt | undefined;
    if (a.style === "iso") iso = add(m, mul(nSide, -(9 * k)));
    return { arrow: a, shafts, heads, hook, label, iso, start: s0, end: s2, control: sc };
  });

  // Bounding box of everything drawn.
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  const grow = (x0: number, y0: number, x1: number, y1: number) => {
    minX = Math.min(minX, x0);
    minY = Math.min(minY, y0);
    maxX = Math.max(maxX, x1);
    maxY = Math.max(maxY, y1);
  };
  for (const n of nodes) grow(n.cx - n.hw, n.cy - n.hh, n.cx + n.hw, n.cy + n.hh);
  for (const s of shapes) {
    for (let t = 0; t <= 1; t += 0.0625) {
      const p = bezier(s.start, s.control, s.end, t);
      grow(p.x - 6, p.y - 6, p.x + 6, p.y + 6);
    }
    if (s.label) grow(s.label.cx - s.label.hw, s.label.cy - s.label.hh, s.label.cx + s.label.hw, s.label.cy + s.label.hh);
    if (s.iso) grow(s.iso.x - 8, s.iso.y - 8, s.iso.x + 8, s.iso.y + 8);
  }
  if (!Number.isFinite(minX)) grow(0, 0, 40, 40);
  const pad = 8;
  return {
    viewBox: { x: minX - pad, y: minY - pad, w: maxX - minX + 2 * pad, h: maxY - minY + 2 * pad },
    nodes,
    arrows: shapes,
    font: spec.font,
    labelFont: spec.labelFont,
  };
}
