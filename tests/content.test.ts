import { describe, expect, it } from "vitest";
import crypto from "node:crypto";
import { compile } from "@mdx-js/mdx";
import remarkMath from "remark-math";
import remarkGfm from "remark-gfm";
import { ExercisesFile, GraphFile, LEVEL_IDS, LessonFrontmatter, PathwaysFile, TrailFrontmatter, LeanReport, ComputeReport } from "@/lib/schema";
import { findCycle, ancestors } from "@/lib/graph-layout";
import { EXPERIMENT_IDS } from "@/lib/experiments";
import { SECTION_KINDS } from "@/components/lesson/kinds";
import { dirs, exists, files, fm, json, read } from "./helpers";

const graph = GraphFile.parse(json("content/math/graph/graph.json"));
const pathways = PathwaysFile.parse(json("content/math/graph/pathways.json")).pathways;
const byId = new Map(graph.topics.map((t) => [t.id, t]));
const lean = LeanReport.parse(json("content/verification/lean-report.json"));
const compute = ComputeReport.parse(json("content/verification/compute-report.json"));
const lessons = dirs("content/math/lessons");
const trails = dirs("content/math/trails");
const lvl = (l: string) => LEVEL_IDS.indexOf(l as (typeof LEVEL_IDS)[number]);
const hash = (s: string) => crypto.createHash("sha256").update(s).digest("hex").slice(0, 12);

describe("knowledge graph", () => {
  it("has unique topic ids", () => {
    expect(new Set(graph.topics.map((t) => t.id)).size).toBe(graph.topics.length);
  });

  it("references only existing topics, with no self-loops", () => {
    for (const t of graph.topics) {
      for (const p of t.prerequisites) {
        expect(byId.has(p), `${t.id} → missing prerequisite ${p}`).toBe(true);
        expect(p, `${t.id} lists itself`).not.toBe(t.id);
      }
      for (const d of t.discoveries) expect(byId.has(d.to), `${t.id} → missing discovery ${d.to}`).toBe(true);
    }
  });

  it("has acyclic required prerequisites", () => {
    expect(findCycle(graph.topics)).toBeNull();
  });

  it("never requires a topic from a later level", () => {
    for (const t of graph.topics) for (const p of t.prerequisites) expect(lvl(byId.get(p)!.level), `${p} is above ${t.id}`).toBeLessThanOrEqual(lvl(t.level));
  });

  it("keeps optional discovery edges distinct from required edges", () => {
    for (const t of graph.topics) for (const d of t.discoveries) expect(t.prerequisites.includes(d.to), `${t.id} → ${d.to} is both`).toBe(false);
  });

  it("covers every level and subject", () => {
    for (const l of LEVEL_IDS) expect(graph.topics.some((t) => t.level === l), l).toBe(true);
    for (const s of graph.subjects) expect(graph.topics.some((t) => t.subject === s.id), s.id).toBe(true);
  });

  it("links implemented topics to real lessons and vice versa", () => {
    for (const t of graph.topics.filter((x) => x.status === "implemented")) {
      expect(t.lesson, t.id).toBeDefined();
      expect(lessons).toContain(t.lesson);
    }
    for (const slug of lessons) {
      const f = LessonFrontmatter.parse(fm(`content/math/lessons/${slug}/en.mdx`).data);
      expect(byId.get(f.topic)?.lesson, `${slug} ↔ ${f.topic}`).toBe(slug);
    }
  });

  it("references only existing Wonder Trails", () => {
    for (const t of graph.topics) {
      for (const s of t.trails) expect(trails, `${t.id} → ${s}`).toContain(s);
      for (const d of t.discoveries) if (d.trail) expect(trails, `${t.id} → ${d.trail}`).toContain(d.trail);
    }
  });
});

describe("pathways", () => {
  it("has the eight required pathways", () => {
    expect(pathways.map((p) => p.id).sort()).toEqual(["accelerated-secondary", "adult-beginner", "applied-math", "cs-formal-methods", "graduate-prep", "k12-conventional", "math-major", "research-prep"]);
  });

  it("orders milestones consistently with prerequisites", () => {
    const pre = new Map(graph.topics.map((t) => [t.id, t.prerequisites]));
    for (const p of pathways) {
      p.milestones.forEach((m, i) => {
        expect(byId.has(m), `${p.id}: ${m}`).toBe(true);
        const need = ancestors(m, pre);
        for (const later of p.milestones.slice(i + 1)) expect(need.has(later), `${p.id}: ${later} must come before ${m}`).toBe(false);
      });
    }
  });
});

describe("lessons", () => {
  const leanNames = new Set(lean.declarations.map((d) => d.name));
  const exerciseIds = new Set<string>();

  for (const slug of lessons) {
    describe(slug, () => {
      const doc = fm(`content/math/lessons/${slug}/en.mdx`);
      const f = LessonFrontmatter.parse(doc.data);

      it("has valid canonical frontmatter", () => {
        expect(f.slug).toBe(slug);
        expect(f.translation.status).toBe("canonical");
        expect(f.labels).not.toContain("formally-verified");
        expect(f.labels).not.toContain("computationally-tested");
        expect(f.labels).not.toContain("mathematically-reviewed");
      });

      it("cites only compiled, sorry-free Lean declarations", () => {
        expect(lean.build.success).toBe(true);
        for (const d of f.lean) {
          expect(leanNames.has(d), d).toBe(true);
          expect(lean.declarations.find((x) => x.name === d)!.usesSorry, d).toBe(false);
        }
        for (const m of doc.content.matchAll(/<Lean decl="([^"]+)"/g)) expect(leanNames.has(m[1]), m[1]).toBe(true);
      });

      it("cites only tested experiments", () => {
        for (const id of [...f.compute, ...[...doc.content.matchAll(/<Python id="([^"]+)"/g)].map((m) => m[1])]) {
          const e = compute.experiments.find((x) => x.id === id);
          expect(e, id).toBeDefined();
          expect(e!.ran && e!.testsPassed, id).toBe(true);
        }
      });

      it("uses known section kinds with ids and titles", () => {
        const sections = [...doc.content.matchAll(/<Section\b([^>]*)>/g)].map((m) => Object.fromEntries([...m[1].matchAll(/(\w+)="([^"]*)"/g)].map((a) => [a[1], a[2]])));
        expect(sections.length).toBeGreaterThan(5);
        const ids = sections.map((s) => s.id);
        expect(new Set(ids).size, "duplicate section ids").toBe(ids.length);
        for (const s of sections) {
          expect(s.title, JSON.stringify(s)).toBeTruthy();
          expect(Object.keys(SECTION_KINDS), s.kind).toContain(s.kind);
        }
        expect(sections.some((s) => s.kind === "exercises")).toBe(true);
      });

      it("compiles as MDX", async () => {
        await expect(compile(doc.content, { remarkPlugins: [remarkGfm, remarkMath] })).resolves.toBeTruthy();
      });

      it("embeds only existing trails", () => {
        for (const m of doc.content.matchAll(/<Trail slug="([^"]+)"/g)) expect(trails).toContain(m[1]);
        for (const s of f.trails) expect(trails).toContain(s);
      });

      it("has well-formed exercises", () => {
        const ex = ExercisesFile.parse(json(`content/math/lessons/${slug}/exercises.json`));
        expect(ex.lesson).toBe(slug);
        for (const e of ex.exercises) {
          expect(exerciseIds.has(e.id), `duplicate exercise id ${e.id}`).toBe(false);
          exerciseIds.add(e.id);
          if (e.type === "choice") expect(e.options.some((o) => o.correct), e.id).toBe(true);
          if (e.type === "choice" && !e.multiple) expect(e.options.filter((o) => o.correct).length, e.id).toBe(1);
          if (e.type === "integer") for (const fb of e.feedback) expect(Number(fb.match), e.id).not.toBe(e.answer);
          if (e.type === "python") expect(e.solution, e.id).toMatch(/```python\n/);
        }
      });

      it("keeps translations linked to their source", () => {
        const canonical = hash(doc.content);
        for (const file of files(`content/math/lessons/${slug}`).filter((x) => /^[a-zA-Z-]+\.mdx$/.test(x) && x !== "en.mdx")) {
          const tr = LessonFrontmatter.parse(fm(`content/math/lessons/${slug}/${file}`).data);
          expect(tr.translation.status, file).not.toBe("canonical");
          expect(tr.translation.sourceHash, `${file} needs a sourceHash`).toMatch(/^[0-9a-f]{12}$/);
          if (tr.translation.sourceHash !== canonical) console.warn(`[stale translation] ${slug}/${file}`);
          // Identifiers that join content together must never be translated.
          expect(tr.slug).toBe(f.slug);
          expect(tr.topic).toBe(f.topic);
          expect(tr.lean).toEqual(f.lean);
          expect(tr.compute).toEqual(f.compute);
        }
      });
    });
  }
});

describe("Wonder Trails", () => {
  for (const slug of trails) {
    it(`${slug} is complete and connected`, async () => {
      const doc = fm(`content/math/trails/${slug}/en.mdx`);
      const f = TrailFrontmatter.parse(doc.data);
      expect(f.slug).toBe(slug);
      expect(lessons).toContain(f.from.lesson);
      const lessonBody = read(`content/math/lessons/${f.from.lesson}/en.mdx`);
      expect(lessonBody, `return anchor #${f.from.label}`).toContain(`id="${f.from.label}"`);
      expect(lessonBody, `${f.from.lesson} should link to ${slug}`).toContain(`<Trail slug="${slug}"`);
      expect(EXPERIMENT_IDS as readonly string[]).toContain(f.experiment);
      for (const id of f.deeper) expect(byId.has(id), id).toBe(true);
      for (const d of f.lean) expect(lean.declarations.some((x) => x.name === d && !x.usesSorry), d).toBe(true);
      for (const id of f.compute) expect(compute.experiments.some((x) => x.id === id && x.testsPassed), id).toBe(true);
      expect(doc.content.trim().length).toBeGreaterThan(200);
      await expect(compile(doc.content, { remarkPlugins: [remarkGfm, remarkMath] })).resolves.toBeTruthy();
    });
  }
});

describe("prose pages", () => {
  for (const slug of dirs("content/pages")) {
    it(`${slug} compiles`, async () => {
      expect(exists(`content/pages/${slug}/en.mdx`)).toBe(true);
      await expect(compile(fm(`content/pages/${slug}/en.mdx`).content, { remarkPlugins: [remarkGfm, remarkMath] })).resolves.toBeTruthy();
    });
  }
});
