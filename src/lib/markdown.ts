import "server-only";
import { unified } from "unified";
import remarkParse from "remark-parse";
import remarkGfm from "remark-gfm";
import remarkMath from "remark-math";
import remarkRehype from "remark-rehype";
import rehypeKatex from "rehype-katex";
import rehypeStringify from "rehype-stringify";

export const KATEX_MACROS = {
  "\\N": "\\mathbb{N}",
  "\\Z": "\\mathbb{Z}",
  "\\Q": "\\mathbb{Q}",
  "\\R": "\\mathbb{R}",
  "\\C": "\\mathbb{C}",
  "\\cat": "\\mathbf{#1}",
  "\\id": "\\mathrm{id}",
  "\\Hom": "\\mathrm{Hom}",
};

export const katexOptions = { macros: KATEX_MACROS, strict: "ignore" as const, output: "htmlAndMathml" as const, throwOnError: false };

const processor = unified()
  .use(remarkParse)
  .use(remarkGfm)
  .use(remarkMath)
  .use(remarkRehype)
  .use(rehypeKatex, katexOptions)
  .use(rehypeStringify);

/** Markdown + $math$ → HTML string (server-side; no client JS needed for maths). */
export function mdToHtml(markdown: string): string {
  return String(processor.processSync(markdown));
}

/** Like mdToHtml but unwraps a single top-level paragraph, for inline labels. */
export function mdInline(markdown: string): string {
  const html = mdToHtml(markdown).trim();
  const m = html.match(/^<p>([\s\S]*)<\/p>$/);
  return m && !m[1].includes("<p>") ? m[1] : html;
}
