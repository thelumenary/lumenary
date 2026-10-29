/**
 * Per-lesson checks that need no verification report: structure (tests/lesson-rules.ts) and a
 * full server render of the MDX with the real lesson blocks and widgets, which catches unknown
 * components, widgets that crash on their props, and LaTeX that KaTeX cannot typeset.
 *
 *   npx vitest run tests/lesson-check.test.ts                      # every lesson
 *   LESSONS=sets,integers npx vitest run tests/lesson-check.test.ts  # just these
 */
import { describe, expect, it } from "vitest";
import { createElement, type ComponentType, type ReactNode } from "react";
import { renderToString } from "react-dom/server";
import { evaluate } from "@mdx-js/mdx";
import * as runtime from "react/jsx-runtime";
import remarkGfm from "remark-gfm";
import remarkMath from "remark-math";
import rehypeKatex from "rehype-katex";
import { ExercisesFile, LessonFrontmatter } from "@/lib/schema";
import { katexOptions, mdToHtml } from "@/lib/markdown";
import { rehypeKatexHtml } from "@/lib/rehype-katex-html";
import { CORE_NAMESPACES, makeT, pickMessages, type Messages } from "@/i18n/dictionary";
import { widgetMessageNamespaces } from "@/lib/widget-messages";
import { I18nProvider } from "@/i18n/client";
import en from "@/i18n/messages/en.json";
import { makeBlocks } from "@/components/lesson/blocks";
import { WIDGETS } from "@/components/lesson/widget-map";
import { exists, fm, json } from "./helpers";
import { lessonDirs, lessonProblems } from "./lesson-rules";
// @ts-expect-error -- plain ESM script without type declarations
import { contentLocales } from "../scripts/gen-content-locales.mjs";
import generatedLocales from "@/lib/generated/content-locales.json";

const t = makeT(en);
const stub = (name: string) => (p: { children?: ReactNode }) => createElement("div", { "data-stub": name }, p.children);
// Server-only pieces (Lean source, Python source, trail cards, exercises) are stubbed: their own
// tests cover them, and the citations they render are checked by lesson-rules and content.test.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const components: Record<string, ComponentType<any>> = {
  ...makeBlocks(t),
  Lean: stub("Lean"),
  Python: stub("Python"),
  Trail: stub("Trail"),
  Exercises: stub("Exercises"),
  TopicLink: ({ id, children }: { id: string; children?: ReactNode }) => createElement("a", { href: `#${id}` }, children ?? id),
  ...WIDGETS,
};
const names = new Set(Object.keys(components));

const requested = process.env.LESSONS?.split(",").map((s) => s.trim()).filter(Boolean);
const all = lessonDirs();
const slugs = requested ?? all;

describe("lesson checks", () => {
  if (requested) it("requested lessons exist", () => expect(requested.filter((s) => !all.includes(s))).toEqual([]));

  for (const slug of slugs.filter((s) => all.includes(s))) {
    describe(slug, () => {
      it("follows the lesson rules", () => {
        expect(lessonProblems(slug, { components: names })).toEqual([]);
      });

      it("renders, with every formula typeset", async () => {
        const doc = fm(`content/math/lessons/${slug}/en.mdx`);
        const { default: Content } = await evaluate(doc.content, {
          ...runtime,
          remarkPlugins: [remarkGfm, remarkMath],
          rehypePlugins: [[rehypeKatex, katexOptions], rehypeKatexHtml],
          development: false,
        });
        // The page ships only the widget strings it needs; render with exactly that subset so a
        // widget whose strings were left out shows up here as a raw "w.…" key.
        const messages = pickMessages(en as Messages, [...CORE_NAMESPACES, "exercise", "python", "lesson", ...widgetMessageNamespaces(doc.content)]);
        const html = renderToString(createElement(I18nProvider, { locale: "en", messages, children: createElement(Content, { components }) }));
        expect(html.length).toBeGreaterThan(2000);
        // Only real widget namespaces count, so prose like "w.h.p." is not mistaken for a key.
        const widgetNs = new Set(Object.keys((en as { w: Record<string, unknown> }).w));
        const rawKeys = [...new Set([...html.replace(/<[^>]*>/g, " ").matchAll(/\bw\.([a-zA-Z0-9]+)\.[a-zA-Z0-9.]+/g)].filter((m) => widgetNs.has(m[1])).map((m) => m[0]))];
        expect(rawKeys, "widget message keys missing from the page's message subset").toEqual([]);
        const errors = [...html.matchAll(/class="katex-error"[^>]*title="([^"]*)"/g)].map((m) => m[1]);
        expect(errors, "KaTeX errors in the lesson body").toEqual([]);
        const rawCaptions = [...html.matchAll(/<figcaption[^>]*>([\s\S]*?)<\/figcaption>/g)].map((m) => m[1].replace(/<[^>]*>/g, "")).filter((c) => /\$[^$\s][^$]*\$/.test(c));
        expect(rawCaptions, "figure captions with untypeset $…$").toEqual([]);
        // Frontmatter strings are rendered as inline Markdown on the page.
        const f = LessonFrontmatter.parse(doc.data);
        for (const s of [f.subtitle, ...f.objectives]) expect(mdToHtml(s), s).not.toContain("katex-error");
      });

      it("has exercises whose Markdown typesets", () => {
        const ex = ExercisesFile.parse(json(`content/math/lessons/${slug}/exercises.json`));
        for (const e of ex.exercises) {
          const texts = [e.prompt, e.solution, ...e.hints];
          if (e.type === "choice") for (const o of e.options) texts.push(o.label, o.feedback);
          if (e.type === "integer" || e.type === "set") for (const f of e.feedback) texts.push(f.message);
          for (const s of texts) expect(mdToHtml(s), `${e.id}: ${s.slice(0, 80)}`).not.toContain("katex-error");
        }
      });
    });
  }
});

describe("curriculum-wide lesson invariants", () => {
  it("has an up-to-date index of translated lessons (node scripts/gen-content-locales.mjs)", () => {
    expect(generatedLocales).toEqual(contentLocales());
  });

  it("gives every lesson a distinct order and globally unique exercise ids", () => {
    const orders = new Map<number, string>();
    const exerciseIds = new Map<string, string>();
    for (const slug of all) {
      // Lessons that are still being written (invalid frontmatter, no exercises yet) are
      // reported by their own per-lesson checks; skip them here so they cannot break others'.
      let data: unknown;
      try {
        data = fm(`content/math/lessons/${slug}/en.mdx`).data;
      } catch {
        continue; // unparsable YAML: reported by that lesson's own checks
      }
      const f = LessonFrontmatter.safeParse(data);
      if (!f.success) continue;
      expect(orders.get(f.data.order), `order ${f.data.order} used by ${orders.get(f.data.order)} and ${slug}`).toBeUndefined();
      orders.set(f.data.order, slug);
      if (!exists(`content/math/lessons/${slug}/exercises.json`)) continue;
      let raw: unknown;
      try {
        raw = json(`content/math/lessons/${slug}/exercises.json`);
      } catch {
        continue; // half-written JSON
      }
      const ex = ExercisesFile.safeParse(raw);
      if (!ex.success) continue;
      for (const e of ex.data.exercises) {
        expect(exerciseIds.get(e.id), `exercise id ${e.id} in ${exerciseIds.get(e.id)} and ${slug}`).toBeUndefined();
        exerciseIds.set(e.id, slug);
      }
    }
  });
});
