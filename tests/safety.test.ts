/**
 * No learner-facing text may describe, or implicitly encourage, actions that could hurt people
 * or damage property (docs/authoring-guide.md §9). Lessons are also checked one by one in
 * tests/lesson-check.test.ts; this test covers every other learner-facing source.
 */
import { describe, expect, it } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./helpers";
import { safetyProblems } from "./lesson-rules";

function files(dir: string, ext: RegExp): string[] {
  const abs = path.join(ROOT, dir);
  if (!fs.existsSync(abs)) return [];
  return fs.readdirSync(abs, { recursive: true, encoding: "utf8" }).filter((f) => ext.test(f)).map((f) => path.join(dir, f));
}

const SOURCES = [
  ...files("content/math/lessons", /\.(mdx|json)$/),
  ...files("content/math/trails", /\.mdx$/),
  ...files("content/pages", /\.mdx$/),
  ...files("compute/experiments", /\.py$/),
  ...files("src/i18n/messages", /\.json$/),
  "content/math/graph/graph.json",
];

describe("safety of examples", () => {
  it("finds the sources", () => expect(SOURCES.length).toBeGreaterThan(400));
  it("detects an unsafe example and allows a warning", () => {
    expect(safetyProblems("A stone is dropped from a bridge.")).not.toEqual([]);
    expect(safetyProblems("Do not look directly at the Sun.")).toEqual([]);
    expect(safetyProblems("Look at the sun through the clouds.")).not.toEqual([]);
    expect(safetyProblems("Never drop anything from a bridge.")).toEqual([]);
    expect(safetyProblems("An apple falls from a tree.")).toEqual([]);
  });
  for (const file of SOURCES)
    it(file, () => {
      expect(safetyProblems(fs.readFileSync(path.join(ROOT, file), "utf8"))).toEqual([]);
    });
});
