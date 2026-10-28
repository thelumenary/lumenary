import "server-only";
import { evaluate } from "@mdx-js/mdx";
import * as runtime from "react/jsx-runtime";
import remarkGfm from "remark-gfm";
import remarkMath from "remark-math";
import rehypeKatex from "rehype-katex";
import type { ComponentType } from "react";
import { katexOptions } from "./markdown";

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type MdxComponents = Record<string, ComponentType<any>>;

/** Compile and render an MDX document on the server (at build time for the static export). */
export async function renderMdx(source: string, components: MdxComponents) {
  const { default: Content } = await evaluate(source, {
    ...runtime,
    remarkPlugins: [remarkGfm, remarkMath],
    rehypePlugins: [[rehypeKatex, katexOptions]],
    development: false,
  });
  return <Content components={components} />;
}

export interface TocEntry {
  id: string;
  title: string;
  kind: string;
}

/** Table of contents from <Section id="…" kind="…" title="…"> tags in an MDX body. */
export function extractToc(source: string): TocEntry[] {
  const out: TocEntry[] = [];
  for (const m of source.matchAll(/<Section\b([^>]*)>/g)) {
    const attrs = Object.fromEntries([...m[1].matchAll(/(\w+)="([^"]*)"/g)].map((a) => [a[1], a[2]]));
    if (attrs.id && attrs.title) out.push({ id: attrs.id, title: attrs.title, kind: attrs.kind ?? "" });
  }
  return out;
}
