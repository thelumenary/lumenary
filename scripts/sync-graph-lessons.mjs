#!/usr/bin/env node
/**
 * sync-graph-lessons.mjs — link lessons into the knowledge graph.
 *
 * For every content/math/lessons/<slug>/en.mdx, set the `lesson` field and `status:
 * "implemented"` on the topic named in its frontmatter. Topics without a lesson keep their
 * status. Run after adding a lesson (`npm run sync:graph`); `npm test` checks the result.
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import matter from "gray-matter";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const GRAPH = path.join(ROOT, "content/math/graph/graph.json");
const LESSONS = path.join(ROOT, "content/math/lessons");

const graph = JSON.parse(fs.readFileSync(GRAPH, "utf8"));
const byId = new Map(graph.topics.map((t) => [t.id, t]));
let linked = 0;
for (const slug of fs.readdirSync(LESSONS).sort()) {
  const file = path.join(LESSONS, slug, "en.mdx");
  if (!fs.existsSync(file)) continue;
  const { topic } = matter(fs.readFileSync(file, "utf8")).data;
  const t = byId.get(topic);
  if (!t) {
    console.error(`sync-graph-lessons: ${slug} names unknown topic ${topic}`);
    process.exitCode = 1;
    continue;
  }
  if (t.lesson !== slug || t.status !== "implemented") linked++;
  t.lesson = slug;
  t.status = "implemented";
}
fs.writeFileSync(GRAPH, `${JSON.stringify(graph, null, 2)}\n`);
const implemented = graph.topics.filter((t) => t.status === "implemented").length;
console.log(`sync-graph-lessons: ${linked} topic(s) newly linked; ${implemented} of ${graph.topics.length} topics implemented`);
