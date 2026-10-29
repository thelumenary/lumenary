/**
 * Structural rules every lesson must satisfy, shared by `tests/lesson-check.test.ts` (which
 * also renders each lesson) and usable on a single lesson while it is being written:
 *
 *   LESSONS=sets,integers npx vitest run tests/lesson-check.test.ts
 *
 * These checks read only source files, never the generated verification reports, so they can
 * run before `npm run verify`. `tests/content.test.ts` separately checks citations against the
 * reports (compiled Lean, passing experiments).
 */
import fs from "node:fs";
import path from "node:path";
import { ExercisesFile, GraphFile, LEVEL_IDS, LessonFrontmatter, type LevelId } from "@/lib/schema";
import { LENSES, SECTION_KINDS } from "@/components/lesson/kinds";
import { ROOT, dirs, exists, fm, json, read } from "./helpers";

export const graph = GraphFile.parse(json("content/math/graph/graph.json"));
export const topicsById = new Map(graph.topics.map((t) => [t.id, t]));
export const lessonDirs = () => dirs("content/math/lessons").filter((d) => exists(`content/math/lessons/${d}/en.mdx`));
export const trailDirs = () => dirs("content/math/trails");
const lvl = (l: string) => LEVEL_IDS.indexOf(l as LevelId);

/** Lenses that are foundational languages rather than other mathematicians' viewpoints. */
export const FOUNDATIONAL_LENSES = new Set(["sets", "categories", "logic"]);

/**
 * How many viewpoints a lesson must offer, by level. From early undergraduate onwards a lesson
 * must show its subject through other mathematicians' eyes — topologist, geometer, analyst,
 * algebraist, number theorist, probabilist, physicist… — and not only through set theory and
 * category theory.
 */
export function viewpointRequirement(level: LevelId): { lenses: number; nonFoundational: number } | null {
  if (lvl(level) >= lvl("ug2")) return { lenses: 3, nonFoundational: 2 };
  if (level === "ug1") return { lenses: 2, nonFoundational: 1 };
  return null;
}

/**
 * How many `<Narrator>` asides a lesson must have. The three cat guides appear at every level
 * (readers can hide them); from early undergraduate onwards they are brief, substantive asides.
 */
export function narratorRequirement(level: LevelId): number {
  return lvl(level) >= lvl("ug1") ? 2 : 1;
}

/**
 * Phrases that describe, and so may implicitly encourage, actions that could hurt people or
 * damage property. Falling-object examples use natural events (an apple from a tree), safe
 * sport, or a supervised laboratory demonstration instead. See docs/authoring-guide.md §9.
 */
export const SAFETY_PATTERNS: { re: RegExp; why: string }[] = [
  {
    re: /\b(?:drop|dropp|throw|threw|thrown|toss|fling|flung|hurl|push|roll|lob|launch|fir(?:e|es|ed|ing))\w*\b[^.!?\n]{0,80}?\b(?:from|off|over)\s+(?:the\s+|a\s+|an\s+|your\s+|their\s+)?(?:[\w-]+\s+){0,2}?(?:bridge|balcony|window|roof|rooftop|cliff|tower|overpass|ledge|parapet|stairwell)s?\b/gi,
    why: "dropping or throwing something from a height where it could hurt someone",
  },
  {
    re: /\b(?:stone|rock|brick|object|ball|coin|egg)s?\b[^.!?\n]{0,40}?\b(?:dropped|thrown|tossed|falls?|falling|fell)\b[^.!?\n]{0,40}?\b(?:from|off)\s+(?:the\s+|a\s+|an\s+)?(?:[\w-]+\s+){0,2}?(?:bridge|balcony|window|roof|rooftop|cliff|tower|overpass|ledge|parapet|building)s?\b/gi,
    why: "an object falling from a height where it could hurt someone",
  },
  { re: /\b(?:look|looking|stare|staring|gaze|gazing|peek|peeking)\s+(?:directly\s+|straight\s+)?(?:at|into)\s+the\s+sun\b/gi, why: "looking at the Sun" },
  { re: /\b(?:play|playing|walk|walking|stand|standing|count|counting)\b[^.!?\n]{0,30}?\b(?:on|along|across)\s+(?:the\s+|a\s+)?(?:railway|railroad|train)\s+tracks?\b/gi, why: "being on railway tracks" },
];

/** Safety problems in a piece of learner-facing text (empty = fine). Warnings against a danger are allowed. */
export function safetyProblems(text: string): string[] {
  const out: string[] = [];
  for (const { re, why } of SAFETY_PATTERNS)
    for (const m of text.matchAll(re)) {
      const before = text.slice(Math.max(0, (m.index ?? 0) - 30), m.index);
      if (/\b(?:never|not|n't|no one|nobody|avoid)\b[^.!?]*$/i.test(before)) continue;
      out.push(`unsafe example (${why}): "${m[0].slice(0, 100)}"`);
    }
  return out;
}

const attrs = (s: string) => Object.fromEntries([...s.matchAll(/(\w+)="([^"]*)"/g)].map((a) => [a[1], a[2]]));

export function sectionsOf(body: string) {
  return [...body.matchAll(/<Section\b([^>]*)>/g)].map((m) => attrs(m[1]));
}

export function lensesOf(body: string): string[] {
  return [...body.matchAll(/<Viewpoint\b([^>]*)>/g)].map((m) => attrs(m[1]).lens ?? "");
}

/* ------------------------------------------------------------------ */
/* Lean declarations, read from source (not from the build report)    */
/* ------------------------------------------------------------------ */

let leanDeclCache: Set<string> | null = null;

/** Fully qualified names of declarations in formal/Lumenary/**.lean, from a light parse of the source. */
export function leanDeclarationsInSource(): Set<string> {
  if (leanDeclCache) return leanDeclCache;
  const out = new Set<string>();
  const walk = (dir: string) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith(".lean")) parseLean(fs.readFileSync(p, "utf8"), out);
    }
  };
  const lib = path.join(ROOT, "formal/Lumenary");
  if (fs.existsSync(lib)) walk(lib);
  leanDeclCache = out;
  return out;
}

function parseLean(text: string, out: Set<string>) {
  // Drop block comments (which nest in Lean) and line comments, keeping line structure.
  let code = "";
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    const two = text.slice(i, i + 2);
    if (two === "/-") {
      depth++;
      i++;
    } else if (depth > 0 && two === "-/") {
      depth--;
      i++;
    } else if (depth === 0) code += text[i];
    else if (text[i] === "\n") code += "\n";
  }
  const scopes: { kind: "namespace" | "section"; name: string | null }[] = [];
  for (const raw of code.split("\n")) {
    const line = raw.replace(/--.*$/, "");
    const ns = line.match(/^\s*namespace\s+(\S+)/);
    if (ns) {
      for (const part of ns[1].split(".")) scopes.push({ kind: "namespace", name: part });
      continue;
    }
    const sec = line.match(/^\s*(?:noncomputable\s+)?section\b\s*(\S+)?/);
    if (sec) {
      scopes.push({ kind: "section", name: sec[1] ?? null });
      continue;
    }
    const end = line.match(/^\s*end\b\s*(\S+)?\s*$/);
    if (end) {
      const parts = end[1] ? end[1].split(".") : [null];
      for (let k = 0; k < parts.length; k++) scopes.pop();
      continue;
    }
    const d = line.match(
      /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([^\s(\[{:⦃]+)/,
    );
    if (d) {
      const local = d[1].replace(/\.$/, "");
      const prefix = scopes.filter((s) => s.kind === "namespace").map((s) => s.name);
      out.add(local.startsWith("_root_.") ? local.slice(7) : [...prefix, local].join("."));
    }
  }
}

/* ------------------------------------------------------------------ */
/* Rules                                                               */
/* ------------------------------------------------------------------ */

export interface LessonProblemOptions {
  /** Component names MDX may use (blocks, widgets, Lean, Python, …). */
  components: Set<string>;
}

/** Everything structurally wrong with one lesson, as human-readable messages (empty = fine). */
export function lessonProblems(slug: string, { components }: LessonProblemOptions): string[] {
  const problems: string[] = [];
  const say = (m: string) => problems.push(`${slug}: ${m}`);
  const dir = `content/math/lessons/${slug}`;
  if (!exists(`${dir}/en.mdx`)) return [`${slug}: missing ${dir}/en.mdx`];
  const doc = fm(`${dir}/en.mdx`);
  const parsed = LessonFrontmatter.safeParse(doc.data);
  if (!parsed.success) return [`${slug}: invalid frontmatter: ${parsed.error.message}`];
  const f = parsed.data;
  const body = doc.content;

  // Frontmatter and graph
  if (f.slug !== slug) say(`frontmatter slug "${f.slug}" does not match the folder name`);
  const topic = topicsById.get(f.topic);
  if (!topic) say(`topic ${f.topic} is not in the knowledge graph`);
  else if (topic.level !== f.level) say(`level ${f.level} differs from the topic's level ${topic.level}`);
  if (f.translation.status !== "canonical") say("en.mdx must be canonical");
  if (!f.labels.includes("ai-drafted")) say('labels must include "ai-drafted" until a named human has reviewed the lesson');
  for (const bad of ["formally-verified", "computationally-tested", "mathematically-reviewed", "pedagogically-reviewed"] as const)
    if (f.labels.includes(bad)) say(`label "${bad}" cannot be hand-asserted`);
  if (f.objectives.length < 2 || f.objectives.length > 7) say(`has ${f.objectives.length} objectives (expected 2–7)`);
  if (f.minutes < 10 || f.minutes > 240) say(`minutes ${f.minutes} looks wrong`);

  // Sections
  const sections = sectionsOf(body);
  if (sections.length < 6) say(`only ${sections.length} sections`);
  const ids = sections.map((s) => s.id);
  if (new Set(ids).size !== ids.length) say("duplicate section ids");
  for (const s of sections) {
    if (!s.id || !s.title) say(`section without id or title: ${JSON.stringify(s)}`);
    if (!(s.kind in SECTION_KINDS)) say(`unknown section kind "${s.kind}"`);
  }
  for (const kind of ["exercises", "reading"]) if (!sections.some((s) => s.kind === kind)) say(`no "${kind}" section`);
  if (!sections.some((s) => s.kind === "formal")) say('no "formal" section');
  if (!sections.some((s) => s.kind === "computation")) say('no "computation" section');

  // Viewpoints
  const lenses = lensesOf(body);
  for (const l of lenses) if (!(l in LENSES)) say(`unknown viewpoint lens "${l}" (known: ${Object.keys(LENSES).join(", ")})`);
  const req = viewpointRequirement(f.level);
  if (req) {
    const distinct = new Set(lenses.filter((l) => l in LENSES));
    const other = [...distinct].filter((l) => !FOUNDATIONAL_LENSES.has(l));
    if (!sections.some((s) => s.kind === "viewpoints")) say('needs a "viewpoints" section at this level');
    if (distinct.size < req.lenses) say(`offers ${distinct.size} viewpoint lenses; needs at least ${req.lenses}`);
    if (other.length < req.nonFoundational)
      say(`needs at least ${req.nonFoundational} viewpoint(s) beyond set theory, category theory and logic (e.g. topology, geometry, analysis, algebra)`);
  }

  // Narrators (the cat guides)
  const narratorTags = [...body.matchAll(/<Narrator\b([^>]*)>/g)].map((m) => attrs(m[1]).who);
  const minNarrators = narratorRequirement(f.level);
  if (narratorTags.length < minNarrators) say(`has ${narratorTags.length} <Narrator> aside(s); needs at least ${minNarrators} (the cat guides appear at every level)`);
  for (const n of new Set(narratorTags)) if (!(f.narrators as string[]).includes(n)) say(`<Narrator who="${n}"> is not listed in the frontmatter "narrators"`);
  for (const n of f.narrators) if (!narratorTags.includes(n)) say(`frontmatter narrator "${n}" never speaks in the lesson`);

  // Safety: nothing that could hurt people or damage property, even as a problem's setting
  for (const p of safetyProblems(body)) say(p);
  if (exists(`${dir}/exercises.json`)) for (const p of safetyProblems(read(`${dir}/exercises.json`))) say(`exercises.json: ${p}`);

  // Components used in MDX
  for (const m of body.matchAll(/<([A-Z][A-Za-z0-9]*)\b/g)) if (!components.has(m[1])) say(`unknown MDX component <${m[1]}>`);
  for (const m of body.matchAll(/<TopicLink\b([^>]*)>/g)) {
    const id = attrs(m[1]).id;
    if (!id || !topicsById.has(id)) say(`<TopicLink id="${id}"> is not a topic`);
  }
  const trails = new Set(trailDirs());
  for (const m of body.matchAll(/<Trail slug="([^"]+)"/g)) if (!trails.has(m[1])) say(`<Trail slug="${m[1]}"> does not exist`);
  for (const s of f.trails) if (!trails.has(s)) say(`frontmatter trail ${s} does not exist`);

  // Lean
  const decls = leanDeclarationsInSource();
  const cited = new Set([...f.lean, ...[...body.matchAll(/<Lean decl="([^"]+)"/g)].map((m) => m[1])]);
  for (const d of cited) if (!decls.has(d)) say(`Lean declaration ${d} not found in formal/Lumenary`);
  for (const m of body.matchAll(/<Lean decl="([^"]+)"/g)) if (!f.lean.includes(m[1])) say(`<Lean decl="${m[1]}"> is not listed in the frontmatter "lean"`);
  if (f.lean.length === 0) say('frontmatter "lean" is empty: every lesson cites at least one compiled declaration');

  // Python experiments
  const used = new Set([...f.compute, ...[...body.matchAll(/<Python id="([^"]+)"/g)].map((m) => m[1])]);
  for (const id of used) {
    const file = `compute/experiments/${id}.py`;
    if (!exists(file)) {
      say(`experiment ${id} has no file ${file}`);
      continue;
    }
    const lessonsList = read(file).match(/"lessons"\s*:\s*\[([^\]]*)\]/);
    if (!lessonsList || !lessonsList[1].includes(`"${slug}"`)) say(`experiment ${id} does not list "${slug}" in EXPERIMENT["lessons"]`);
    if (!exists(`compute/tests/test_${id}.py`)) say(`experiment ${id} has no tests (compute/tests/test_${id}.py)`);
  }
  for (const m of body.matchAll(/<Python id="([^"]+)"/g)) if (!f.compute.includes(m[1])) say(`<Python id="${m[1]}"> is not listed in the frontmatter "compute"`);
  if (f.compute.length === 0) say('frontmatter "compute" is empty: every lesson uses at least one tested experiment');

  // Exercises
  if (!exists(`${dir}/exercises.json`)) say("missing exercises.json");
  else {
    const ex = ExercisesFile.safeParse(json(`${dir}/exercises.json`));
    if (!ex.success) say(`invalid exercises.json: ${ex.error.message}`);
    else {
      if (ex.data.lesson !== slug) say(`exercises.json "lesson" is "${ex.data.lesson}"`);
      if (ex.data.exercises.length < 5) say(`only ${ex.data.exercises.length} exercises (expected at least 5)`);
      const seen = new Set<string>();
      for (const e of ex.data.exercises) {
        if (seen.has(e.id)) say(`duplicate exercise id ${e.id}`);
        seen.add(e.id);
        if (e.type === "choice" && !e.options.some((o) => o.correct)) say(`${e.id}: no correct option`);
        if (e.type === "choice" && !e.multiple && e.options.filter((o) => o.correct).length !== 1) say(`${e.id}: single-answer question needs exactly one correct option`);
        if (e.type === "integer") for (const fb of e.feedback) if (Number(fb.match) === e.answer) say(`${e.id}: feedback targets the right answer`);
        if (e.type === "python" && !/```python\n/.test(e.solution)) say(`${e.id}: python solution needs a \`\`\`python block`);
      }
    }
  }
  return problems;
}
