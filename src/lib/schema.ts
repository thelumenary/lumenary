/**
 * Canonical schemas for all machine-readable Lumenary content.
 *
 * Every JSON/MDX-frontmatter file under `content/` is validated against these
 * schemas by `tests/content.test.ts`. Keep identifiers stable: they are the
 * join keys for translations, progress records and the knowledge graph.
 */
import { z } from "zod";

/* ------------------------------------------------------------------ */
/* Shared vocabulary                                                   */
/* ------------------------------------------------------------------ */

export const LEVEL_IDS = ["k2", "g3-5", "g6-8", "g9-12", "ug1", "ug2", "grad", "research"] as const;
export const LevelId = z.enum(LEVEL_IDS);
export type LevelId = z.infer<typeof LevelId>;

export const SUBJECT_IDS = [
  "foundations", // collections, sets, logic, proof, set theory, model theory
  "number", // counting, arithmetic, integers, rationals, number theory
  "algebra", // algebra, linear algebra, abstract algebra, representation theory
  "geometry", // geometry, trigonometry, topology, differential geometry
  "analysis", // functions of a real variable, calculus, analysis, measure theory
  "discrete", // combinatorics, graph theory, discrete mathematics
  "probability", // probability, statistics, stochastic processes
  "category", // category theory and its precursors
  "computation", // algorithms, numerical methods, computability, formal methods, Lean
  "applied", // mathematical physics, cryptography, information theory, biology, optimisation
] as const;
export const SubjectId = z.enum(SUBJECT_IDS);
export type SubjectId = z.infer<typeof SubjectId>;

/** Stable topic identifier, e.g. `math.found.sets` or `math.cat.yoneda`. */
export const TopicId = z.string().regex(/^math\.[a-z]+(\.[a-z0-9]+(-[a-z0-9]+)*)+$/, "topic ids look like math.<area>.<kebab-name>");

export const VERIFICATION_LABELS = [
  "formally-verified", // only derived from a successful Lean build report
  "computationally-tested", // only derived from a successful compute report
  "mathematically-reviewed", // requires a named human reviewer record
  "pedagogically-reviewed", // requires a named human reviewer record
  "machine-translated",
  "translation-reviewed",
  "experimental",
  "incomplete",
  "ai-drafted", // written with AI assistance, awaiting human review
] as const;
export const VerificationLabel = z.enum(VERIFICATION_LABELS);
export type VerificationLabel = z.infer<typeof VerificationLabel>;

export const Reference = z.object({
  title: z.string(),
  author: z.string().optional(),
  year: z.number().int().optional(),
  url: z.string().url().optional(),
  note: z.string().optional(),
});

/* ------------------------------------------------------------------ */
/* Knowledge graph                                                     */
/* ------------------------------------------------------------------ */

export const Level = z.object({
  id: LevelId,
  title: z.string(),
  short: z.string(),
  ages: z.string(),
  description: z.string(),
});

export const Subject = z.object({
  id: SubjectId,
  title: z.string(),
  short: z.string().optional(),
  description: z.string(),
});

export const DiscoveryEdge = z.object({
  to: TopicId,
  /** Wonder Trail slug that walks this optional edge, if any. */
  trail: z.string().optional(),
  note: z.string().optional(),
});

export const Topic = z.object({
  id: TopicId,
  title: z.string(),
  subject: SubjectId,
  level: LevelId,
  summary: z.string(),
  /** Required prerequisite edges. Must form a DAG across the whole graph. */
  prerequisites: z.array(TopicId),
  /** Optional discovery edges. Never affect progression or mastery. */
  discoveries: z.array(DiscoveryEdge).default([]),
  objectives: z.array(z.string()).min(1),
  definitions: z.array(z.string()).default([]),
  keyResults: z.array(z.string()).default([]),
  misconceptions: z.array(z.string()).default([]),
  /** Lesson slug under content/math/lessons when the topic has a lesson. */
  lesson: z.string().optional(),
  /** Wonder Trail slugs that start from or pass through this topic. */
  trails: z.array(z.string()).default([]),
  references: z.array(Reference).default([]),
  status: z.enum(["implemented", "draft", "planned"]),
  tags: z.array(z.string()).default([]),
});
export type Topic = z.infer<typeof Topic>;

export const Pathway = z.object({
  id: z.string().regex(/^[a-z0-9-]+$/),
  title: z.string(),
  audience: z.string(),
  description: z.string(),
  /** Ordered milestones; each must be a topic id. */
  milestones: z.array(TopicId).min(3),
});
export type Pathway = z.infer<typeof Pathway>;

export const GraphFile = z.object({
  version: z.literal(1),
  levels: z.array(Level),
  subjects: z.array(Subject),
  topics: z.array(Topic),
});

export const PathwaysFile = z.object({
  version: z.literal(1),
  pathways: z.array(Pathway),
});

/* ------------------------------------------------------------------ */
/* Lessons, trails and exercises                                       */
/* ------------------------------------------------------------------ */

export const TranslationStatus = z.enum([
  "canonical", // the source text
  "machine-draft", // AI/machine generated, not reviewed by a human
  "human-reviewed", // reviewed for language by a named human
  "math-reviewed", // reviewed for mathematical accuracy in this language by a named human
  "incomplete",
]);
export type TranslationStatus = z.infer<typeof TranslationStatus>;

export const Translation = z.object({
  status: TranslationStatus,
  source: z.string().default("en"),
  /** sha256 (first 12 hex chars) of the canonical file this was translated from. */
  sourceHash: z.string().optional(),
  translatedAt: z.string().optional(),
  reviewers: z.array(z.string()).default([]),
});

export const LessonFrontmatter = z.object({
  slug: z.string(),
  topic: TopicId,
  title: z.string(),
  subtitle: z.string(),
  level: LevelId,
  ages: z.string(),
  minutes: z.number().int().positive(),
  order: z.number().int(),
  objectives: z.array(z.string()).min(1),
  narrators: z.array(z.enum(["chloe", "margaret", "gideon"])).default([]),
  /** Fully-qualified Lean declarations this lesson relies on. Verification is read from the Lean report. */
  lean: z.array(z.string()).default([]),
  /** Compute experiment ids this lesson relies on. Verification is read from the compute report. */
  compute: z.array(z.string()).default([]),
  trails: z.array(z.string()).default([]),
  /** Hand-asserted labels. formally-verified / computationally-tested are NOT allowed here: they are derived. */
  labels: z.array(VerificationLabel).default([]),
  translation: Translation.default({ status: "canonical", source: "en", reviewers: [] }),
});
export type LessonFrontmatter = z.infer<typeof LessonFrontmatter>;

export const TrailFrontmatter = z.object({
  slug: z.string(),
  title: z.string(),
  question: z.string(),
  kind: z.enum(["algebraic", "modular", "quotient", "category", "set-theory", "logic", "analysis", "history", "topology", "geometry", "number-theory", "probability", "computability", "physics"]),
  from: z.object({ lesson: z.string(), label: z.string() }),
  level: LevelId,
  hints: z.array(z.string()).min(1),
  experiment: z.string(),
  deeper: z.array(TopicId).min(1),
  /** Honest note when the trail uses an intuitive analogy rather than a formal construction. */
  analogyNote: z.string().optional(),
  lean: z.array(z.string()).default([]),
  compute: z.array(z.string()).default([]),
  translation: Translation.default({ status: "canonical", source: "en", reviewers: [] }),
});
export type TrailFrontmatter = z.infer<typeof TrailFrontmatter>;

const Feedback = z.object({ match: z.string(), message: z.string() });

const ExerciseBase = z.object({
  id: z.string().regex(/^[a-z0-9-]+$/),
  prompt: z.string(),
  difficulty: z.enum(["warm-up", "core", "stretch"]),
  mode: z.enum(["H", "F", "C"]),
  hints: z.array(z.string()).min(1),
  solution: z.string(),
});

export const Exercise = z.discriminatedUnion("type", [
  ExerciseBase.extend({
    type: z.literal("choice"),
    options: z.array(z.object({ id: z.string(), label: z.string(), correct: z.boolean(), feedback: z.string() })).min(2),
    multiple: z.boolean().default(false),
  }),
  ExerciseBase.extend({
    type: z.literal("integer"),
    answer: z.number().int(),
    /** Targeted, non-shaming feedback for predictable wrong answers. `match` is the wrong answer as a string. */
    feedback: z.array(Feedback).default([]),
  }),
  ExerciseBase.extend({
    type: z.literal("set"),
    /** Elements as strings; order and repetition never matter. */
    answer: z.array(z.string()),
    feedback: z.array(Feedback).default([]),
  }),
  ExerciseBase.extend({
    type: z.literal("python"),
    starter: z.string(),
    /** Python source that raises AssertionError on failure; runs after the learner's code. */
    tests: z.string(),
  }),
]);
export type Exercise = z.infer<typeof Exercise>;

export const ExercisesFile = z.object({
  lesson: z.string(),
  exercises: z.array(Exercise).min(1),
});

/* ------------------------------------------------------------------ */
/* Registries                                                          */
/* ------------------------------------------------------------------ */

export const LanguageEntry = z.object({
  /** BCP 47 tag, e.g. "sw", "zh-Hans", "ar", "arz". */
  tag: z.string().regex(/^[a-z]{2,3}(-[A-Z][a-z]{3})?(-([A-Z]{2}|[0-9]{3}))?$/),
  name: z.string(),
  nativeName: z.string(),
  /** ISO 15924 script code. */
  script: z.string().regex(/^[A-Z][a-z]{3}$/),
  direction: z.enum(["ltr", "rtl"]),
  family: z.string(),
  /** ISO 3166-1 alpha-2 codes where the language is widely used or official. */
  regions: z.array(z.string().regex(/^[A-Z]{2}$/)),
  /** Arabic varieties etc. point at their macrolanguage/standard. */
  variantOf: z.string().optional(),
  /** Why the language is in the registry. */
  inclusion: z.array(z.enum(["top-100-seed", "un-official", "national-official", "regional-indigenous", "variety", "demo"])),
  ui: z.enum(["available", "machine-draft", "not-started"]),
  translationStatus: z.enum(["canonical", "none", "machine-draft", "partial", "human-reviewed", "math-reviewed"]),
  reviewStatus: z.enum(["unreviewed", "language-reviewed", "math-reviewed"]),
  glossary: z.string().nullable(),
  lastReviewed: z.string().nullable(),
  notes: z.string().optional(),
});
export type LanguageEntry = z.infer<typeof LanguageEntry>;

export const LanguagesFile = z.object({
  version: z.literal(1),
  methodology: z.string(),
  languages: z.array(LanguageEntry),
});

/** Mathematical terminology glossary for one language (content/registry/glossaries/<tag>.json). */
export const GlossaryFile = z.object({
  version: z.literal(1),
  language: z.string(),
  status: z.enum(["machine-draft", "human-reviewed", "math-reviewed"]),
  notes: z.string().optional(),
  /** Keyed by stable English term id (e.g. "set", "empty-set", "injective"). */
  terms: z.record(z.string(), z.object({ term: z.string(), alternatives: z.array(z.string()).default([]), note: z.string().optional() })),
});

export const CountryEntry = z.object({
  iso2: z.string().regex(/^[A-Z]{2}$/),
  iso3: z.string().regex(/^[A-Z]{3}$/),
  m49: z.string().regex(/^[0-9]{3}$/),
  name: z.string(),
  status: z.enum(["un-member", "un-observer", "territory", "other"]),
  region: z.enum(["Africa", "Americas", "Asia", "Europe", "Oceania"]),
  subregion: z.string(),
  /** BCP 47 tags of de jure official languages (empty when none is legally designated). */
  officialLanguages: z.array(z.string()),
  /** Languages used nationally/administratively when there is no de jure official language. */
  deFactoLanguages: z.array(z.string()).default([]),
  /** The language the Lumenary will use for this country first. */
  primaryLumenaryLanguage: z.string(),
  notes: z.string().optional(),
  needsReview: z.boolean().default(false),
});
export type CountryEntry = z.infer<typeof CountryEntry>;

export const CountriesFile = z.object({
  version: z.literal(1),
  sources: z.array(z.string()),
  countries: z.array(CountryEntry),
});

/* ------------------------------------------------------------------ */
/* Verification reports (generated — never edit by hand)               */
/* ------------------------------------------------------------------ */

export const LeanReport = z.object({
  generatedAt: z.string(),
  toolchain: z.string(),
  leanVersion: z.string(),
  mathlib: z.string().nullable(),
  build: z.object({ command: z.string(), success: z.boolean(), durationMs: z.number() }),
  files: z.array(z.object({ path: z.string(), sha256: z.string(), success: z.boolean() })),
  declarations: z.array(
    z.object({
      name: z.string(),
      kind: z.enum(["theorem", "def", "instance", "structure", "example"]),
      file: z.string(),
      region: z.string().nullable(),
      usesSorry: z.boolean(),
      axioms: z.array(z.string()),
      /** "library" = proof applies an existing library theorem (core Lean or Mathlib); "independent" = proved here from more basic facts. */
      provenance: z.enum(["library", "independent", "definition"]),
      /** "core" = core Lean only; "mathlib" = the declaration's file builds on Mathlib. */
      foundation: z.enum(["core", "mathlib"]).default("core"),
    }),
  ),
  exercises: z.array(
    z.object({
      file: z.string(),
      name: z.string(),
      region: z.string().nullable(),
      elaborates: z.boolean(),
      sorryCount: z.number().int(),
      solution: z.string().nullable(),
    }),
  ),
});
export type LeanReport = z.infer<typeof LeanReport>;

export const EVIDENCE_TYPES = ["exact", "symbolic", "numerical", "experimental", "exhaustive-finite", "statistical", "counterexample"] as const;
export const EvidenceType = z.enum(EVIDENCE_TYPES);
export type EvidenceType = z.infer<typeof EvidenceType>;

export const ComputeReport = z.object({
  generatedAt: z.string(),
  python: z.string(),
  packages: z.record(z.string(), z.string()),
  pytest: z.object({ passed: z.number().int(), failed: z.number().int(), skipped: z.number().int(), durationMs: z.number() }),
  experiments: z.array(
    z.object({
      id: z.string(),
      title: z.string(),
      file: z.string(),
      evidence: z.array(EvidenceType).min(1),
      lessons: z.array(z.string()),
      summary: z.string(),
      packages: z.array(z.string()),
      ran: z.boolean(),
      testsPassed: z.boolean(),
      durationMs: z.number(),
      sha256: z.string(),
    }),
  ),
});
export type ComputeReport = z.infer<typeof ComputeReport>;
