import "server-only";
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import matter from "gray-matter";
import { z } from "zod";
import {
  ComputeReport,
  CountriesFile,
  ExercisesFile,
  GraphFile,
  LanguagesFile,
  LeanReport,
  LessonFrontmatter,
  PathwaysFile,
  TrailFrontmatter,
  Translation,
  type Exercise,
  type LevelId,
  type Topic,
  LEVEL_IDS,
} from "./schema";
import type { Locale } from "@/i18n/config";

export const ROOT = process.cwd();
const CONTENT = path.join(ROOT, "content");
const read = (p: string) => fs.readFileSync(p, "utf8");
const exists = (p: string) => fs.existsSync(p);

export function shortHash(text: string): string {
  return crypto.createHash("sha256").update(text).digest("hex").slice(0, 12);
}

const memo = new Map<string, unknown>();
function cached<T>(key: string, load: () => T): T {
  if (!memo.has(key)) memo.set(key, load());
  return memo.get(key) as T;
}

/* ------------------------------------------------------------------ */
/* Knowledge graph                                                     */
/* ------------------------------------------------------------------ */

export function getGraph() {
  return cached("graph", () => GraphFile.parse(JSON.parse(read(path.join(CONTENT, "math/graph/graph.json")))));
}

export function getPathways() {
  return cached("pathways", () => PathwaysFile.parse(JSON.parse(read(path.join(CONTENT, "math/graph/pathways.json")))).pathways);
}

export function getTopic(id: string): Topic | undefined {
  return getGraph().topics.find((t) => t.id === id);
}

export function levelIndex(level: LevelId): number {
  return LEVEL_IDS.indexOf(level);
}

/** All transitive required prerequisites of a topic. */
export function prerequisiteClosure(id: string): Set<string> {
  const byId = new Map(getGraph().topics.map((t) => [t.id, t]));
  const seen = new Set<string>();
  const stack = [...(byId.get(id)?.prerequisites ?? [])];
  while (stack.length) {
    const next = stack.pop()!;
    if (seen.has(next)) continue;
    seen.add(next);
    stack.push(...(byId.get(next)?.prerequisites ?? []));
  }
  return seen;
}

/* ------------------------------------------------------------------ */
/* Lessons                                                             */
/* ------------------------------------------------------------------ */

const LESSONS = path.join(CONTENT, "math/lessons");

export interface LoadedDoc<F> {
  frontmatter: F;
  body: string;
  /** Locale actually rendered (may differ from requested on fallback). */
  locale: Locale;
  requested: Locale;
  fallback: boolean;
  /** True when a translation's sourceHash no longer matches the canonical file. */
  stale: boolean;
}

function loadLocalized<F>(dir: string, locale: Locale, parse: (data: unknown) => F, sourceHashOf: (f: F) => string | undefined): LoadedDoc<F> {
  const canonicalPath = path.join(dir, "en.mdx");
  const localPath = path.join(dir, `${locale}.mdx`);
  const useLocal = locale !== "en" && exists(localPath);
  const raw = read(useLocal ? localPath : canonicalPath);
  const { data, content } = matter(raw);
  const frontmatter = parse(data);
  let stale = false;
  if (useLocal) {
    const canonicalBody = matter(read(canonicalPath)).content;
    const recorded = sourceHashOf(frontmatter);
    stale = recorded !== undefined && recorded !== shortHash(canonicalBody);
  }
  return { frontmatter, body: content, locale: useLocal ? locale : "en", requested: locale, fallback: locale !== "en" && !useLocal, stale };
}

export function lessonSlugs(): string[] {
  return cached("lessonSlugs", () =>
    fs
      .readdirSync(LESSONS)
      .filter((d) => exists(path.join(LESSONS, d, "en.mdx")))
      .map((slug) => ({ slug, order: LessonFrontmatter.parse(matter(read(path.join(LESSONS, slug, "en.mdx"))).data).order }))
      .sort((a, b) => a.order - b.order)
      .map((l) => l.slug),
  );
}

export function getLesson(slug: string, locale: Locale) {
  return loadLocalized(path.join(LESSONS, slug), locale, (d) => LessonFrontmatter.parse(d), (f) => f.translation.sourceHash);
}

export function getLessonList(locale: Locale) {
  return lessonSlugs().map((slug) => getLesson(slug, locale));
}

export function lessonLocales(slug: string): Locale[] {
  const dir = path.join(LESSONS, slug);
  return fs
    .readdirSync(dir)
    .filter((f) => f.endsWith(".mdx"))
    .map((f) => f.replace(/\.mdx$/, "") as Locale);
}

/** Exercises with optional per-locale string overrides (exercises.<locale>.json). */
export function getExercises(slug: string, locale: Locale): { exercises: Exercise[]; translated: boolean } {
  const base = path.join(LESSONS, slug, "exercises.json");
  if (!exists(base)) return { exercises: [], translated: false };
  const file = ExercisesFile.parse(JSON.parse(read(base)));
  const overridePath = path.join(LESSONS, slug, `exercises.${locale}.json`);
  if (locale === "en" || !exists(overridePath)) return { exercises: file.exercises, translated: locale === "en" };
  const overrides = JSON.parse(read(overridePath)) as Record<string, Record<string, unknown>>;
  const exercises = file.exercises.map((ex) => {
    const o = overrides[ex.id];
    if (!o) return ex;
    const merged = { ...ex, ...o } as Record<string, unknown>;
    if (ex.type === "choice" && Array.isArray(o.options)) {
      merged.options = ex.options.map((opt) => {
        const tr = (o.options as { id: string; label?: string; feedback?: string }[]).find((x) => x.id === opt.id);
        return { ...opt, ...(tr ? { label: tr.label ?? opt.label, feedback: tr.feedback ?? opt.feedback } : {}) };
      });
    }
    // Answers, tests and ids are never translated.
    for (const k of ["id", "type", "answer", "tests", "mode", "difficulty"]) merged[k] = (ex as Record<string, unknown>)[k];
    return merged as Exercise;
  });
  return { exercises, translated: true };
}

/* ------------------------------------------------------------------ */
/* Wonder Trails                                                       */
/* ------------------------------------------------------------------ */

const TRAILS = path.join(CONTENT, "math/trails");

export function trailSlugs(): string[] {
  return cached("trailSlugs", () =>
    fs
      .readdirSync(TRAILS)
      .filter((d) => exists(path.join(TRAILS, d, "en.mdx")))
      .sort(),
  );
}

export function getTrail(slug: string, locale: Locale) {
  return loadLocalized(path.join(TRAILS, slug), locale, (d) => TrailFrontmatter.parse(d), (f) => f.translation.sourceHash);
}

export function getTrailList(locale: Locale) {
  const order = lessonSlugs();
  return trailSlugs()
    .map((s) => getTrail(s, locale))
    .sort((a, b) => order.indexOf(a.frontmatter.from.lesson) - order.indexOf(b.frontmatter.from.lesson));
}

/* ------------------------------------------------------------------ */
/* Verification reports                                                */
/* ------------------------------------------------------------------ */

export function getLeanReport() {
  return cached("lean", () => {
    const p = path.join(CONTENT, "verification/lean-report.json");
    return exists(p) ? LeanReport.parse(JSON.parse(read(p))) : null;
  });
}

export function getComputeReport() {
  return cached("compute", () => {
    const p = path.join(CONTENT, "verification/compute-report.json");
    return exists(p) ? ComputeReport.parse(JSON.parse(read(p))) : null;
  });
}

export interface DeclarationStatus {
  name: string;
  verified: boolean;
  found: boolean;
  usesSorry: boolean;
  axioms: string[];
  provenance?: "library" | "independent" | "definition";
  region?: string | null;
}

export function leanStatus(name: string): DeclarationStatus {
  const report = getLeanReport();
  const decl = report?.declarations.find((d) => d.name === name);
  if (!report || !decl) return { name, verified: false, found: false, usesSorry: false, axioms: [] };
  return {
    name,
    found: true,
    verified: report.build.success && !decl.usesSorry,
    usesSorry: decl.usesSorry,
    axioms: decl.axioms,
    provenance: decl.provenance,
    region: decl.region,
  };
}

export function experimentStatus(id: string) {
  const exp = getComputeReport()?.experiments.find((e) => e.id === id);
  return exp ? { ...exp, verified: exp.ran && exp.testsPassed } : null;
}

/** Derived verification summary for a lesson or trail — never hand-asserted. */
export function deriveVerification(lean: string[], compute: string[]) {
  const leanStatuses = lean.map(leanStatus);
  const computeStatuses = compute.map((id) => ({ id, status: experimentStatus(id) }));
  return {
    lean: leanStatuses,
    compute: computeStatuses,
    formallyVerified: lean.length > 0 && leanStatuses.every((s) => s.verified),
    computationallyTested: compute.length > 0 && computeStatuses.every((c) => c.status?.verified),
    leanVerifiedCount: leanStatuses.filter((s) => s.verified).length,
    computeVerifiedCount: computeStatuses.filter((c) => c.status?.verified).length,
  };
}

/* ------------------------------------------------------------------ */
/* Source extraction                                                   */
/* ------------------------------------------------------------------ */

const FORMAL = path.join(ROOT, "formal");

function leanFiles(): string[] {
  return cached("leanFiles", () => {
    if (!exists(FORMAL)) return [];
    const out: string[] = [];
    const walk = (dir: string) => {
      for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
        if (entry.name.startsWith(".")) continue;
        const full = path.join(dir, entry.name);
        if (entry.isDirectory()) walk(full);
        else if (entry.name.endsWith(".lean")) out.push(full);
      }
    };
    walk(FORMAL);
    return out;
  });
}

export interface LeanRegion {
  id: string;
  file: string;
  code: string;
  provenance: string | null;
  solution: string | null;
}

export function leanRegions(): Map<string, LeanRegion> {
  return cached("leanRegions", () => {
    const map = new Map<string, LeanRegion>();
    for (const file of leanFiles()) {
      const lines = read(file).split("\n");
      let current: { id: string; start: number; provenance: string | null; solution: string | null } | null = null;
      lines.forEach((line, i) => {
        const open = line.match(/^\s*--\s*@region\s+(\S+)/);
        if (open) {
          current = { id: open[1], start: i + 1, provenance: null, solution: null };
          return;
        }
        if (!current) return;
        const prov = line.match(/^\s*--\s*@provenance\s+(\S+)/);
        if (prov) current.provenance = prov[1];
        const sol = line.match(/^\s*--\s*@solution\s+(\S+)/);
        if (sol) current.solution = sol[1];
        if (/^\s*--\s*@endregion/.test(line)) {
          const body = lines
            .slice(current.start, i)
            .filter((l) => !/^\s*--\s*@(provenance|solution)\b/.test(l))
            .join("\n")
            .replace(/^\n+|\n+$/g, "");
          map.set(current.id, { id: current.id, file: path.relative(FORMAL, file), code: body, provenance: current.provenance, solution: current.solution });
          current = null;
        }
      });
    }
    return map;
  });
}

export function leanRegionForDeclaration(name: string): LeanRegion | undefined {
  const region = getLeanReport()?.declarations.find((d) => d.name === name)?.region;
  return region ? leanRegions().get(region) : undefined;
}

export function getExperimentSource(id: string): string | null {
  const p = path.join(ROOT, "compute/experiments", `${id}.py`);
  return exists(p) ? read(p) : null;
}

/* ------------------------------------------------------------------ */
/* Registries                                                          */
/* ------------------------------------------------------------------ */

export function getLanguages() {
  return cached("languages", () => {
    const p = path.join(CONTENT, "registry/languages.json");
    return exists(p) ? LanguagesFile.parse(JSON.parse(read(p))) : null;
  });
}

export function getCountries() {
  return cached("countries", () => {
    const p = path.join(CONTENT, "registry/countries.json");
    return exists(p) ? CountriesFile.parse(JSON.parse(read(p))) : null;
  });
}

/* ------------------------------------------------------------------ */
/* Prose pages (about, contribute, educators)                          */
/* ------------------------------------------------------------------ */

export const PageFrontmatter = z.object({
  title: z.string(),
  lead: z.string(),
  translation: Translation.default({ status: "canonical", source: "en", reviewers: [] }),
});

export function getPage(slug: string, locale: Locale) {
  return loadLocalized(path.join(CONTENT, "pages", slug), locale, (d) => PageFrontmatter.parse(d), (f) => f.translation.sourceHash);
}
