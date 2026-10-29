/**
 * Propositional logic for the TruthTable widget: a small tokenizer and
 * precedence-climbing parser, printing, sub-formulas and truth tables.
 *
 * Syntax: variables are single lowercase letters; constants T/F, true/false,
 * ⊤/⊥, 1/0; operators (tightest first)
 *   ¬  not ~ !
 *   ∧  and & && /\
 *   ∨  or | || \/      ⊕ xor  (same level as ∨)
 *   →  implies -> =>   (right-associative)
 *   ↔  iff <-> <=> ≡
 */

export type BinOp = "and" | "or" | "xor" | "implies" | "iff";
export type Formula = { type: "var"; name: string } | { type: "const"; value: boolean } | { type: "not"; arg: Formula } | { type: "bin"; op: BinOp; left: Formula; right: Formula };

export type LogicError =
  | { code: "empty" }
  | { code: "tooLong"; max: number }
  | { code: "unknownSymbol"; symbol: string; pos: number }
  | { code: "unknownWord"; word: string; pos: number }
  | { code: "unexpected"; symbol: string; pos: number }
  | { code: "missingOperand"; pos: number }
  | { code: "missingClose"; pos: number }
  | { code: "tooDeep" }
  | { code: "tooManyVars"; count: number; max: number };

export type ParseResult = { ok: true; formula: Formula; vars: string[] } | { ok: false; error: LogicError };

type Tok = { kind: "var"; name: string; pos: number } | { kind: "const"; value: boolean; pos: number } | { kind: "not"; pos: number } | { kind: "op"; op: BinOp; pos: number } | { kind: "lparen"; pos: number } | { kind: "rparen"; pos: number };

export const MAX_LENGTH = 200;
export const MAX_VARS = 6;
const MAX_DEPTH = 60;

export const SYMBOL: Record<BinOp, string> = { and: "∧", or: "∨", xor: "⊕", implies: "→", iff: "↔" };
const PREC: Record<BinOp, number> = { iff: 1, implies: 2, or: 3, xor: 3, and: 4 };

const WORDS: Record<string, Tok["kind"] | BinOp | "true" | "false"> = {
  not: "not",
  and: "and",
  or: "or",
  xor: "xor",
  implies: "implies",
  iff: "iff",
  true: "true",
  false: "false",
};

/** Multi-character and single-character symbol spellings, longest first. */
const SYMBOLS: [string, Tok["kind"] | BinOp | "true" | "false"][] = [
  ["<->", "iff"],
  ["<=>", "iff"],
  ["->", "implies"],
  ["=>", "implies"],
  ["&&", "and"],
  ["||", "or"],
  ["/\\", "and"],
  ["\\/", "or"],
  ["¬", "not"],
  ["~", "not"],
  ["!", "not"],
  ["∧", "and"],
  ["&", "and"],
  ["∨", "or"],
  ["|", "or"],
  ["⊕", "xor"],
  ["→", "implies"],
  ["⇒", "implies"],
  ["↔", "iff"],
  ["⇔", "iff"],
  ["≡", "iff"],
  ["⊤", "true"],
  ["⊥", "false"],
  ["1", "true"],
  ["0", "false"],
  ["(", "lparen"],
  [")", "rparen"],
];

function makeTok(kind: Tok["kind"] | BinOp | "true" | "false", pos: number): Tok {
  if (kind === "true" || kind === "false") return { kind: "const", value: kind === "true", pos };
  if (kind === "not" || kind === "lparen" || kind === "rparen") return { kind, pos };
  return { kind: "op", op: kind as BinOp, pos };
}

function tokenize(src: string): { ok: true; toks: Tok[] } | { ok: false; error: LogicError } {
  const toks: Tok[] = [];
  let i = 0;
  outer: while (i < src.length) {
    const ch = src[i];
    if (/\s/.test(ch)) {
      i++;
      continue;
    }
    for (const [s, kind] of SYMBOLS) {
      if (src.startsWith(s, i)) {
        toks.push(makeTok(kind, i));
        i += s.length;
        continue outer;
      }
    }
    if (/[A-Za-z]/.test(ch)) {
      let j = i;
      while (j < src.length && /[A-Za-z]/.test(src[j])) j++;
      const word = src.slice(i, j);
      const lower = word.toLowerCase();
      if (word.length === 1 && /[a-z]/.test(word)) toks.push({ kind: "var", name: word, pos: i });
      else if (word === "T" || word === "F") toks.push({ kind: "const", value: word === "T", pos: i });
      else if (lower in WORDS) toks.push(makeTok(WORDS[lower], i));
      else return { ok: false, error: { code: "unknownWord", word, pos: i } };
      i = j;
      continue;
    }
    return { ok: false, error: { code: "unknownSymbol", symbol: String.fromCodePoint(src.codePointAt(i) ?? 63), pos: i } };
  }
  return { ok: true, toks };
}

const tokText = (t: Tok): string => (t.kind === "var" ? t.name : t.kind === "const" ? (t.value ? "⊤" : "⊥") : t.kind === "not" ? "¬" : t.kind === "op" ? SYMBOL[t.op] : t.kind === "lparen" ? "(" : ")");

class ParseFail extends Error {
  constructor(public err: LogicError) {
    super(err.code);
  }
}

export function parseFormula(src: string): ParseResult {
  const text = typeof src === "string" ? src : "";
  if (!text.trim()) return { ok: false, error: { code: "empty" } };
  if (text.length > MAX_LENGTH) return { ok: false, error: { code: "tooLong", max: MAX_LENGTH } };
  const tk = tokenize(text);
  if (!tk.ok) return tk;
  const toks = tk.toks;
  let p = 0;
  const end = text.length;

  const primary = (depth: number): Formula => {
    if (depth > MAX_DEPTH) throw new ParseFail({ code: "tooDeep" });
    const t = toks[p];
    if (!t) throw new ParseFail({ code: "missingOperand", pos: end });
    if (t.kind === "not") {
      p++;
      return { type: "not", arg: primary(depth + 1) };
    }
    if (t.kind === "var") {
      p++;
      return { type: "var", name: t.name };
    }
    if (t.kind === "const") {
      p++;
      return { type: "const", value: t.value };
    }
    if (t.kind === "lparen") {
      p++;
      const inner = expr(1, depth + 1);
      const close = toks[p];
      if (!close || close.kind !== "rparen") {
        if (close) throw new ParseFail({ code: "unexpected", symbol: tokText(close), pos: close.pos });
        throw new ParseFail({ code: "missingClose", pos: t.pos });
      }
      p++;
      return inner;
    }
    // An operator or ')' where a formula should start.
    throw new ParseFail({ code: "missingOperand", pos: t.pos });
  };

  const expr = (minPrec: number, depth: number): Formula => {
    if (depth > MAX_DEPTH) throw new ParseFail({ code: "tooDeep" });
    let left = primary(depth + 1);
    for (;;) {
      const t = toks[p];
      if (!t || t.kind !== "op" || PREC[t.op] < minPrec) break;
      const op = t.op;
      p++;
      // → is right-associative; the others associate to the left.
      const right = expr(op === "implies" ? PREC[op] : PREC[op] + 1, depth + 1);
      left = { type: "bin", op, left, right };
    }
    return left;
  };

  try {
    const formula = expr(1, 0);
    if (p < toks.length) {
      const t = toks[p];
      throw new ParseFail({ code: "unexpected", symbol: tokText(t), pos: t.pos });
    }
    const vars = variables(formula);
    if (vars.length > MAX_VARS) return { ok: false, error: { code: "tooManyVars", count: vars.length, max: MAX_VARS } };
    return { ok: true, formula, vars };
  } catch (e) {
    if (e instanceof ParseFail) return { ok: false, error: e.err };
    return { ok: false, error: { code: "tooDeep" } };
  }
}

export function variables(f: Formula): string[] {
  const out = new Set<string>();
  const walk = (g: Formula) => {
    if (g.type === "var") out.add(g.name);
    else if (g.type === "not") walk(g.arg);
    else if (g.type === "bin") {
      walk(g.left);
      walk(g.right);
    }
  };
  walk(f);
  return [...out].sort();
}

export function evaluate(f: Formula, env: Record<string, boolean>): boolean {
  switch (f.type) {
    case "var":
      return !!env[f.name];
    case "const":
      return f.value;
    case "not":
      return !evaluate(f.arg, env);
    case "bin": {
      const a = evaluate(f.left, env);
      const b = evaluate(f.right, env);
      switch (f.op) {
        case "and":
          return a && b;
        case "or":
          return a || b;
        case "xor":
          return a !== b;
        case "implies":
          return !a || b;
        case "iff":
          return a === b;
      }
    }
  }
}

/** Print with the fewest parentheses that keep the same reading (chains of → keep the grouping explicit when it is not the default). */
export function show(f: Formula): string {
  const go = (g: Formula, parentPrec: number, side: "l" | "r" | "u"): string => {
    if (g.type === "var") return g.name;
    if (g.type === "const") return g.value ? "⊤" : "⊥";
    if (g.type === "not") return `¬${go(g.arg, 5, "u")}`;
    const prec = PREC[g.op];
    const body = `${go(g.left, prec, "l")} ${SYMBOL[g.op]} ${go(g.right, prec, "r")}`;
    let needs = prec < parentPrec;
    if (prec === parentPrec) needs = true; // mixing or repeating operators at one level: be explicit
    if (side === "u") needs = true;
    return needs ? `(${body})` : body;
  };
  return go(f, 0, "l");
}

/** Fully parenthesised form — shows exactly how the formula was grouped. */
export function showFull(f: Formula, top = true): string {
  if (f.type === "var") return f.name;
  if (f.type === "const") return f.value ? "⊤" : "⊥";
  if (f.type === "not") return `¬${showFull(f.arg, false)}`;
  const body = `${showFull(f.left, false)} ${SYMBOL[f.op]} ${showFull(f.right, false)}`;
  return top ? body : `(${body})`;
}

/** Compound sub-formulas, smallest first, without duplicates; the last one is the formula itself. */
export function subformulas(f: Formula): Formula[] {
  const out: Formula[] = [];
  const seen = new Set<string>();
  const walk = (g: Formula) => {
    if (g.type === "not") walk(g.arg);
    if (g.type === "bin") {
      walk(g.left);
      walk(g.right);
    }
    if (g.type === "var" || g.type === "const") return;
    const key = show(g);
    if (!seen.has(key)) {
      seen.add(key);
      out.push(g);
    }
  };
  walk(f);
  return out;
}

/** All assignments, in the textbook order starting with every variable true. */
export function assignments(vars: string[]): Record<string, boolean>[] {
  const n = vars.length;
  return Array.from({ length: 2 ** n }, (_, row) => Object.fromEntries(vars.map((v, i) => [v, ((row >> (n - 1 - i)) & 1) === 0])));
}

export type Classification = "tautology" | "contradiction" | "contingent";

export function classify(values: boolean[]): Classification {
  if (values.every(Boolean)) return "tautology";
  if (values.every((v) => !v)) return "contradiction";
  return "contingent";
}

export interface TruthTableData {
  vars: string[];
  rows: Record<string, boolean>[];
  columns: { formula: Formula; label: string; values: boolean[] }[];
  main: boolean[];
  classification: Classification;
}

export function truthTable(f: Formula, extraVars: string[] = []): TruthTableData {
  const vars = [...new Set([...variables(f), ...extraVars])].sort();
  const rows = assignments(vars);
  const columns = subformulas(f).map((g) => ({ formula: g, label: show(g), values: rows.map((env) => evaluate(g, env)) }));
  const main = rows.map((env) => evaluate(f, env));
  return { vars, rows, columns, main, classification: classify(main) };
}

/** Rows (indices into the shared assignment list) where two formulas differ. */
export function differences(f: Formula, g: Formula): { vars: string[]; rows: number[] } {
  const vars = [...new Set([...variables(f), ...variables(g)])].sort();
  const rows = assignments(vars)
    .map((env, i) => (evaluate(f, env) !== evaluate(g, env) ? i : -1))
    .filter((i) => i >= 0);
  return { vars, rows };
}
