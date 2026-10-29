/**
 * A small, safe expression language for the analysis widgets.
 *
 * Recursive-descent parser that compiles to plain closures — no `eval`, no
 * `new Function`. Supported syntax:
 *
 *   numbers      2, 0.5, .5, 1e-3, 6.02E23
 *   variables    any name the caller allows (x, y, t, n, parameter names …)
 *   constants    pi (π), tau, e
 *   operators    + - * / ^ (right-associative), unary minus/plus, postfix ! (factorial)
 *   functions    sin cos tan sec csc cot asin acos atan atan2 sinh cosh tanh
 *                asinh acosh atanh exp ln log (= ln) log10 log2 sqrt cbrt abs
 *                floor ceil round sign min max mod
 *
 * Precedence, loosest first: + -, then * /, then unary minus, then ^, then !.
 * So -x^2 = -(x^2), 2^-1 = 0.5, 2^3^2 = 2^9 and -3! = -(3!).
 * Multiplication must be written explicitly (2*x, not 2x); the parser says so.
 *
 * Errors carry a machine-readable `code`, a `pos` (0-based character offset)
 * and `params`, so widgets can translate them with t(`w.plot.err.${code}`, params).
 */

export type Vars = Readonly<Record<string, number>>;
export type CompiledExpr = (vars?: Vars) => number;

export type ExprErrorCode =
  | "empty"
  | "tooLong"
  | "tooDeep"
  | "badChar"
  | "badNumber"
  | "unknownName"
  | "implicitMul"
  | "needParen"
  | "notFunction"
  | "arity"
  | "missingClose"
  | "unexpectedEnd"
  | "unexpected";

export interface ExprError {
  code: ExprErrorCode;
  pos: number;
  params: Record<string, string | number>;
}

export type CompileResult =
  | { ok: true; fn: CompiledExpr; vars: string[]; source: string }
  | { ok: false; error: ExprError; source: string };

const MAX_LENGTH = 600;
const MAX_DEPTH = 64;

/* ---------------------------------------------------------------------------
 * Built-ins
 * ------------------------------------------------------------------------- */

const factorial = (v: number): number => {
  if (!Number.isFinite(v) || v < 0 || Math.abs(v - Math.round(v)) > 1e-9) return NaN;
  const k = Math.round(v);
  if (k > 170) return Infinity;
  let r = 1;
  for (let i = 2; i <= k; i++) r *= i;
  return r;
};

/** Real-valued power. Negative bases need integer exponents (use cbrt for real cube roots). */
const pow = (a: number, b: number) => Math.pow(a, b);

type Fn1 = (a: number) => number;
type Fn2 = (a: number, b: number) => number;

export const FUNCTIONS1: Readonly<Record<string, Fn1>> = {
  sin: Math.sin,
  cos: Math.cos,
  tan: Math.tan,
  sec: (a) => 1 / Math.cos(a),
  csc: (a) => 1 / Math.sin(a),
  cot: (a) => Math.cos(a) / Math.sin(a),
  asin: Math.asin,
  acos: Math.acos,
  atan: Math.atan,
  arcsin: Math.asin,
  arccos: Math.acos,
  arctan: Math.atan,
  sinh: Math.sinh,
  cosh: Math.cosh,
  tanh: Math.tanh,
  asinh: Math.asinh,
  acosh: Math.acosh,
  atanh: Math.atanh,
  exp: Math.exp,
  ln: Math.log,
  log: Math.log,
  log10: Math.log10,
  log2: Math.log2,
  sqrt: Math.sqrt,
  cbrt: Math.cbrt,
  abs: Math.abs,
  floor: Math.floor,
  ceil: Math.ceil,
  round: Math.round,
  sign: (a) => (Number.isNaN(a) ? NaN : a > 0 ? 1 : a < 0 ? -1 : 0),
};

export const FUNCTIONS2: Readonly<Record<string, Fn2>> = {
  atan2: Math.atan2,
  min: Math.min,
  max: Math.max,
  /** Mathematical remainder: mod(a, b) has the sign of b (mod(-1, 3) = 2). */
  mod: (a, b) => (b === 0 ? NaN : a - b * Math.floor(a / b)),
};

export const CONSTANTS: Readonly<Record<string, number>> = { pi: Math.PI, "π": Math.PI, tau: 2 * Math.PI, e: Math.E };

export const FUNCTION_NAMES = [...Object.keys(FUNCTIONS1), ...Object.keys(FUNCTIONS2)];
/** Names that cannot be used for parameters or variables. */
export const RESERVED_NAMES = new Set([...FUNCTION_NAMES, ...Object.keys(CONSTANTS)]);

/** True when `name` is a legal parameter/variable name that does not clash with a built-in. */
export function isValidName(name: unknown): name is string {
  return typeof name === "string" && /^[A-Za-z_\u0370-\u03ff][A-Za-z0-9_\u0370-\u03ff]*$/.test(name) && !RESERVED_NAMES.has(name) && name.length <= 24;
}

/* ---------------------------------------------------------------------------
 * Lexer
 * ------------------------------------------------------------------------- */

type OpV = "+" | "-" | "*" | "/" | "^" | "!" | "(" | ")" | ",";
type Tok =
  | { k: "num"; v: number; pos: number; text: string }
  | { k: "name"; v: string; pos: number; text: string }
  | { k: "op"; v: OpV; pos: number; text: string }
  | { k: "end"; pos: number; text: string };

class ParseError extends Error {
  constructor(public err: ExprError) {
    super(err.code);
  }
}
const fail = (code: ExprErrorCode, pos: number, params: Record<string, string | number> = {}): never => {
  throw new ParseError({ code, pos, params });
};

const OP_ALIASES: Record<string, OpV> = {
  "+": "+",
  "-": "-",
  "−": "-",
  "–": "-",
  "*": "*",
  "×": "*",
  "·": "*",
  "⋅": "*",
  "/": "/",
  "÷": "/",
  "^": "^",
  "!": "!",
  "(": "(",
  ")": ")",
  ",": ",",
};

const isDigit = (c: string) => c >= "0" && c <= "9";
const isNameStart = (c: string) => /[A-Za-z_\u0370-\u03ff]/.test(c);
const isNameChar = (c: string) => /[A-Za-z0-9_\u0370-\u03ff]/.test(c);

function lex(src: string): Tok[] {
  const toks: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) {
      i++;
      continue;
    }
    if (isDigit(c) || (c === "." && isDigit(src[i + 1] ?? ""))) {
      const start = i;
      while (isDigit(src[i] ?? "")) i++;
      if (src[i] === ".") {
        i++;
        while (isDigit(src[i] ?? "")) i++;
      }
      // Scientific notation only when an exponent really follows (so "2e" is 2 then e).
      if ((src[i] === "e" || src[i] === "E") && (isDigit(src[i + 1] ?? "") || ((src[i + 1] === "+" || src[i + 1] === "-") && isDigit(src[i + 2] ?? "")))) {
        i += 2;
        while (isDigit(src[i] ?? "")) i++;
      }
      if (src[i] === ".") fail("badNumber", start, { token: src.slice(start, i + 1) });
      const text = src.slice(start, i);
      const v = Number(text);
      if (!Number.isFinite(v)) fail("badNumber", start, { token: text });
      toks.push({ k: "num", v, pos: start, text });
      continue;
    }
    if (isNameStart(c)) {
      const start = i;
      while (i < src.length && isNameChar(src[i])) i++;
      const text = src.slice(start, i);
      toks.push({ k: "name", v: text, pos: start, text });
      continue;
    }
    if (c === "*" && src[i + 1] === "*") {
      toks.push({ k: "op", v: "^", pos: i, text: "**" });
      i += 2;
      continue;
    }
    const op = Object.prototype.hasOwnProperty.call(OP_ALIASES, c) ? OP_ALIASES[c] : undefined;
    if (op) {
      toks.push({ k: "op", v: op, pos: i, text: c });
      i++;
      continue;
    }
    fail("badChar", i, { char: c });
  }
  toks.push({ k: "end", pos: src.length, text: "" });
  return toks;
}

/* ---------------------------------------------------------------------------
 * Parser → closures
 * ------------------------------------------------------------------------- */

type Node = (v: Vars) => number;

class Parser {
  private i = 0;
  private depth = 0;
  readonly used = new Set<string>();

  constructor(
    private toks: Tok[],
    private allowed: ReadonlySet<string>,
  ) {}

  private peek(): Tok {
    return this.toks[this.i];
  }
  private next(): Tok {
    return this.toks[this.i++];
  }
  private isOp(t: Tok, v: string) {
    return t.k === "op" && t.v === v;
  }

  parse(): Node {
    const node = this.expr();
    const t = this.peek();
    if (t.k !== "end") this.unexpected(t);
    return node;
  }

  private enter(pos: number) {
    if (++this.depth > MAX_DEPTH) fail("tooDeep", pos);
  }
  private leave() {
    this.depth--;
  }

  /** Report a token that cannot appear here, recognising the common "implicit multiplication" mistake. */
  private unexpected(t: Tok): never {
    if (t.k === "end") return fail("unexpectedEnd", t.pos);
    const prev = this.toks[this.i - 1];
    const prevEndsValue = prev && (prev.k === "num" || prev.k === "name" || this.isOp(prev, ")") || this.isOp(prev, "!"));
    const startsValue = t.k === "num" || t.k === "name" || this.isOp(t, "(");
    if (prevEndsValue && startsValue) return fail("implicitMul", t.pos, { left: prev.text, right: t.text });
    if (this.isOp(t, ")")) return fail("unexpected", t.pos, { token: ")" });
    return fail("unexpected", t.pos, { token: t.text });
  }

  private expr(): Node {
    this.enter(this.peek().pos);
    let left = this.term();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "+") || this.isOp(t, "-")) {
        this.next();
        const a = left;
        const b = this.term();
        left = t.k === "op" && t.v === "+" ? (v) => a(v) + b(v) : (v) => a(v) - b(v);
      } else break;
    }
    this.leave();
    return left;
  }

  private term(): Node {
    let left = this.unary();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "*") || this.isOp(t, "/")) {
        this.next();
        const a = left;
        const b = this.unary();
        left = t.k === "op" && t.v === "*" ? (v) => a(v) * b(v) : (v) => a(v) / b(v);
      } else break;
    }
    return left;
  }

  private unary(): Node {
    const t = this.peek();
    if (this.isOp(t, "-") || this.isOp(t, "+")) {
      this.next();
      this.enter(t.pos);
      const a = this.unary();
      this.leave();
      return t.k === "op" && t.v === "-" ? (v) => -a(v) : a;
    }
    return this.power();
  }

  private power(): Node {
    const base = this.postfix();
    const t = this.peek();
    if (this.isOp(t, "^")) {
      this.next();
      this.enter(t.pos);
      const exp = this.unary(); // right-associative, and allows 2^-x
      this.leave();
      return (v) => pow(base(v), exp(v));
    }
    return base;
  }

  private postfix(): Node {
    let node = this.primary();
    while (this.isOp(this.peek(), "!")) {
      this.next();
      const a = node;
      node = (v) => factorial(a(v));
    }
    return node;
  }

  private primary(): Node {
    const t = this.next();
    if (t.k === "num") {
      const value = t.v;
      return () => value;
    }
    if (t.k === "op" && t.v === "(") {
      if (this.isOp(this.peek(), ")")) fail("unexpected", this.peek().pos, { token: ")" });
      const inner = this.expr();
      const close = this.peek();
      if (!this.isOp(close, ")")) {
        if (close.k === "end") fail("missingClose", t.pos);
        this.unexpected(close);
      }
      this.next();
      return inner;
    }
    if (t.k === "name") return this.name(t);
    this.i--;
    return this.unexpected(t);
  }

  private name(t: Extract<Tok, { k: "name" }>): Node {
    const name = t.v;
    const callFollows = this.isOp(this.peek(), "(");
    const f1 = Object.prototype.hasOwnProperty.call(FUNCTIONS1, name) ? FUNCTIONS1[name] : undefined;
    const f2 = Object.prototype.hasOwnProperty.call(FUNCTIONS2, name) ? FUNCTIONS2[name] : undefined;
    if (f1 || f2) {
      if (!callFollows) fail("needParen", t.pos, { name });
      const open = this.next();
      const args: Node[] = [];
      if (this.isOp(this.peek(), ")")) fail("arity", t.pos, { name, count: f1 ? 1 : 2 });
      for (;;) {
        args.push(this.expr());
        const s = this.peek();
        if (this.isOp(s, ",")) {
          this.next();
          continue;
        }
        if (this.isOp(s, ")")) {
          this.next();
          break;
        }
        if (s.k === "end") fail("missingClose", open.pos);
        this.unexpected(s);
      }
      const want = f1 ? 1 : 2;
      if (args.length !== want) fail("arity", t.pos, { name, count: want });
      if (f1) {
        const [a] = args;
        return (v) => f1(a(v));
      }
      const [a, b] = args;
      return (v) => f2!(a(v), b(v));
    }
    if (this.allowed.has(name)) {
      if (callFollows) fail("implicitMul", this.peek().pos, { left: name, right: "(" });
      this.used.add(name);
      return (v) => {
        const x = v[name];
        return typeof x === "number" ? x : NaN;
      };
    }
    if (Object.prototype.hasOwnProperty.call(CONSTANTS, name)) {
      const c = CONSTANTS[name];
      if (callFollows) fail("notFunction", t.pos, { name });
      return () => c;
    }
    // "xy" when x and y are allowed, or "2pi"-style runs: suggest explicit multiplication.
    const split = splitIntoKnown(name, this.allowed);
    if (split) fail("implicitMul", t.pos + split[0].length, { left: split[0], right: split.slice(1).join("") });
    fail("unknownName", t.pos, { name, allowed: [...this.allowed, "pi", "e"].join(", ") });
    return () => NaN;
  }
}

/** If `name` is a concatenation of known names (variables, constants), return the pieces. */
function splitIntoKnown(name: string, allowed: ReadonlySet<string>): string[] | null {
  const known = [...allowed, ...Object.keys(CONSTANTS)].sort((a, b) => b.length - a.length);
  const go = (rest: string): string[] | null => {
    if (rest === "") return [];
    for (const k of known) {
      if (rest.startsWith(k)) {
        const tail = go(rest.slice(k.length));
        if (tail) return [k, ...tail];
      }
    }
    return null;
  };
  const parts = go(name);
  return parts && parts.length > 1 ? parts : null;
}

/** Strip a leading "y =", "f(x) =", "r =", "dy/dx =", "x' =" … so authors can write equations naturally. */
export function stripLhs(src: string): string {
  return src.replace(/^\s*(?:d[A-Za-z]\s*\/\s*d[A-Za-z]|[A-Za-z_\u0370-\u03ff][A-Za-z0-9_\u0370-\u03ff]*'*(?:\s*\([^()=]*\))?)\s*=(?!=)/, "");
}

const SUP_DIGITS: Record<string, string> = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" };

/**
 * Display form of an expression for legends and labels (not for parsing):
 * x^2 → x², a*x → a·x, pi → π, theta → θ, - → −.
 */
export function prettyExpr(src: string): string {
  return src
    .replace(/\*\*/g, "^")
    .replace(/\^(\d{1,3})(?![\d.(!])/g, (_, d: string) => d.replace(/\d/g, (c) => SUP_DIGITS[c]))
    .replace(/\*/g, "·")
    .replace(/\bpi\b/g, "π")
    .replace(/\btheta\b/g, "θ")
    .replace(/-/g, "−")
    .replace(/\s+/g, " ")
    .trim();
}

/**
 * Compile `src` into a function of the allowed variables.
 * `allowed` lists the variable names the expression may use (e.g. ["x"], ["x", "a", "b"]).
 */
export function compileExpr(src: unknown, allowed: readonly string[] = ["x"]): CompileResult {
  const source = typeof src === "number" ? String(src) : typeof src === "string" ? src : "";
  try {
    if (source.trim() === "") fail("empty", 0);
    if (source.length > MAX_LENGTH) fail("tooLong", MAX_LENGTH, { max: MAX_LENGTH });
    const toks = lex(source);
    const parser = new Parser(toks, new Set(allowed));
    const node = parser.parse();
    const fn: CompiledExpr = (vars = {}) => {
      const y = node(vars);
      return typeof y === "number" ? y : NaN;
    };
    return { ok: true, fn, vars: [...parser.used], source };
  } catch (e) {
    if (e instanceof ParseError) return { ok: false, error: e.err, source };
    return { ok: false, error: { code: "unexpected", pos: 0, params: { token: "?" } }, source };
  }
}

/** Evaluate an expression once; NaN on any error. */
export function evalExpr(src: unknown, vars: Vars = {}, allowed: readonly string[] = Object.keys(vars)): number {
  const r = compileExpr(src, allowed);
  return r.ok ? r.fn(vars) : NaN;
}

/**
 * Read a numeric prop that may be a number or a constant expression string
 * ("pi/2", "-1.5", "sqrt(2)"). Returns `fallback` for anything unusable.
 */
export function toNumber(value: unknown, fallback: number, vars: Vars = {}): number {
  if (typeof value === "number") return Number.isFinite(value) ? value : fallback;
  if (typeof value === "string") {
    const v = evalExpr(value, vars);
    return Number.isFinite(v) ? v : fallback;
  }
  return fallback;
}

/** Read a [min, max] window prop; falls back when malformed, and swaps reversed bounds. */
export function toRange(value: unknown, fallback: readonly [number, number], vars: Vars = {}): [number, number] {
  if (!Array.isArray(value) || value.length < 2) return [fallback[0], fallback[1]];
  let a = toNumber(value[0], NaN, vars);
  let b = toNumber(value[1], NaN, vars);
  if (!Number.isFinite(a) || !Number.isFinite(b)) return [fallback[0], fallback[1]];
  if (a > b) [a, b] = [b, a];
  if (b - a < 1e-9) {
    const pad = Math.max(1, Math.abs(a)) * 0.5;
    a -= pad;
    b += pad;
  }
  // Keep windows sane: enormous spans make every widget useless.
  const LIM = 1e6;
  return [Math.max(-LIM, a), Math.min(LIM, b)];
}

export interface ParamSpec {
  name: string;
  min: number;
  max: number;
  step: number;
  value: number;
  label?: string;
}

/**
 * Validate a `params` prop: [{ name, min, max, step, value, label? }, …].
 * Malformed entries are dropped; numbers are clamped into a consistent state.
 */
export function toParams(value: unknown, taken: readonly string[] = []): ParamSpec[] {
  if (!Array.isArray(value)) return [];
  const out: ParamSpec[] = [];
  const seen = new Set(taken);
  for (const raw of value.slice(0, 8)) {
    if (!raw || typeof raw !== "object") continue;
    const r = raw as Record<string, unknown>;
    if (!isValidName(r.name) || seen.has(r.name)) continue;
    let min = toNumber(r.min, -5);
    let max = toNumber(r.max, 5);
    if (min > max) [min, max] = [max, min];
    if (min === max) max = min + 1;
    let step = toNumber(r.step, (max - min) / 100);
    if (!(step > 0)) step = (max - min) / 100;
    step = Math.min(step, max - min);
    const v = Math.min(max, Math.max(min, toNumber(r.value, (min + max) / 2)));
    seen.add(r.name);
    out.push({ name: r.name, min, max, step, value: v, label: typeof r.label === "string" ? r.label.slice(0, 60) : undefined });
  }
  return out;
}
