#!/usr/bin/env node
/**
 * gen-curriculum-docs.mjs — regenerate the marked tables in docs/curriculum/taxonomy.md and
 * docs/curriculum/pathways.md from content/math/graph/{graph,pathways}.json
 * (`npm run docs:curriculum`). Only text between `<!-- generated:NAME -->` and
 * `<!-- /generated:NAME -->` is replaced; the surrounding prose is left alone.
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import matter from "gray-matter";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const graph = JSON.parse(fs.readFileSync(path.join(ROOT, "content/math/graph/graph.json"), "utf8"));
const pathways = JSON.parse(fs.readFileSync(path.join(ROOT, "content/math/graph/pathways.json"), "utf8")).pathways;
const byId = new Map(graph.topics.map((t) => [t.id, t]));
const level = new Map(graph.levels.map((l) => [l.id, l]));
const subject = new Map(graph.subjects.map((s) => [s.id, s]));
const trails = fs.readdirSync(path.join(ROOT, "content/math/trails")).filter((d) => fs.existsSync(path.join(ROOT, "content/math/trails", d, "en.mdx")));

function fill(file, sections) {
  const p = path.join(ROOT, file);
  let text = fs.readFileSync(p, "utf8");
  for (const [name, body] of Object.entries(sections)) {
    const re = new RegExp(`(<!-- generated:${name} -->\\n)[\\s\\S]*?(<!-- /generated:${name} -->)`);
    if (!re.test(text)) throw new Error(`${file}: no generated:${name} markers`);
    text = text.replace(re, `$1${body.trimEnd()}\n$2`);
  }
  fs.writeFileSync(p, text);
}

const table = (head, rows) => [`| ${head.join(" | ")} |`, `|${head.map(() => "---").join("|")}|`, ...rows.map((r) => `| ${r.join(" | ")} |`)].join("\n");

/* taxonomy.md */
const required = graph.topics.reduce((n, t) => n + t.prerequisites.length, 0);
const discoveries = graph.topics.reduce((n, t) => n + t.discoveries.length, 0);
const walked = graph.topics.reduce((n, t) => n + t.discoveries.filter((d) => d.trail).length, 0);
const implemented = graph.topics.filter((t) => t.status === "implemented").length;
const summary = `The graph has **${graph.topics.length} topics**, **${required} required prerequisite edges** and **${discoveries} optional discovery edges** (${walked} of them walked by a named Wonder Trail). ${implemented} topics are implemented as lessons${implemented === graph.topics.length ? " — every topic in the graph" : ""}; there are ${trails.length} Wonder Trails.`;

const counts = table(
  ["Subject", ...graph.levels.map((l) => l.short), "Total"],
  [
    ...graph.subjects.map((s) => {
      const cells = graph.levels.map((l) => graph.topics.filter((t) => t.subject === s.id && t.level === l.id).length);
      return [s.title, ...cells.map((n) => (n ? String(n) : "·")), String(cells.reduce((a, b) => a + b, 0))];
    }),
    ["**Total**", ...graph.levels.map((l) => String(graph.topics.filter((t) => t.level === l.id).length)), String(graph.topics.length)],
  ],
);

const tagCounts = new Map();
for (const t of graph.topics) for (const tag of t.tags) tagCounts.set(tag, (tagCounts.get(tag) ?? 0) + 1);
const tags = table(["Tag", "Topics"], [...tagCounts.entries()].sort((a, b) => a[0].localeCompare(b[0])).map(([k, n]) => [`\`${k}\``, String(n)]));

const index = graph.levels
  .map((l) => {
    const rows = graph.topics
      .filter((t) => t.level === l.id)
      .sort((a, b) => a.id.localeCompare(b.id))
      .map((t) => [`\`${t.id}\``, t.title, subject.get(t.subject).title, t.lesson ? `implemented (\`${t.lesson}\`)` : t.status]);
    return `### ${l.title} (${l.short})\n\n${table(["Id", "Title", "Subject", "Status"], rows)}`;
  })
  .join("\n\n");

fill("docs/curriculum/taxonomy.md", { summary, counts, tags, index });

/* pathways.md */
const summaryTable = table(["Id", "Title", "Milestones"], pathways.map((p) => [`\`${p.id}\``, p.title, String(p.milestones.length)]));
const sections = pathways
  .map((p) => {
    const rows = p.milestones.map((m, i) => {
      const t = byId.get(m);
      return [String(i + 1), level.get(t.level).short, `\`${m}\``, t.title, subject.get(t.subject).title];
    });
    return `## ${p.title} (\`${p.id}\`)\n\n**Audience:** ${p.audience}\n\n${p.description}\n\n${table(["#", "Level", "Milestone", "Title", "Subject"], rows)}`;
  })
  .join("\n\n");
fill("docs/curriculum/pathways.md", { table: summaryTable, pathways: sections });

/* wonder-trails.md */
const short = (id) => id.replace(/^math\./, "");
const trailSections = trails
  .sort()
  .map((slug) => {
    const fm = matter(fs.readFileSync(path.join(ROOT, "content/math/trails", slug, "en.mdx"), "utf8")).data;
    const lesson = graph.topics.find((t) => t.lesson === fm.from.lesson);
    const edges = graph.topics.flatMap((t) => t.discoveries.filter((d) => d.trail === slug).map((d) => ({ from: t, to: byId.get(d.to), note: d.note ?? "" })));
    const rows = edges.map((e) => [short(e.from.id), level.get(e.from.level).short, short(e.to.id), level.get(e.to.level).short, e.note.replace(/\|/g, "\\|")]);
    return [
      `### \`${slug}\` — ${fm.title}`,
      "",
      `- **Kind:** ${fm.kind}`,
      `- **Inviting question:** ${fm.question}`,
      `- **Starts from:** ${lesson ? `\`${lesson.id}\` (${lesson.title})` : `lesson \`${fm.from.lesson}\``}`,
      `- **Leads to:** ${fm.deeper.map((id) => `${byId.get(id)?.title ?? id} (\`${short(id)}\`)`).join(", ")}`,
      ...(fm.analogyNote ? [`- **Analogy note:** ${fm.analogyNote}`] : []),
      ...(rows.length ? ["", table(["From", "Level", "To", "Level", "Connection"], rows)] : []),
    ].join("\n");
  })
  .join("\n\n");
fill("docs/curriculum/wonder-trails.md", { trails: trailSections });

console.log(`gen-curriculum-docs: ${graph.topics.length} topics, ${pathways.length} pathways, ${trails.length} trails`);
