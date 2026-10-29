import { describe, expect, it } from "vitest";
import { compile } from "@mdx-js/mdx";
import remarkMath from "remark-math";
import rehypeKatex from "rehype-katex";
import { katexOptions } from "@/lib/markdown";
import { rehypeKatexHtml } from "@/lib/rehype-katex-html";

describe("MDX pipeline", () => {
  it("collapses every typeset formula, including those inside JSX blocks, into one HTML string", async () => {
    const source = '<Section id="a" kind="human" title="t">\n\nLet $x^2$ be given.\n\n<Theorem name="T">\n\n$$\n\\frac{1}{2}\n$$\n\n</Theorem>\n\n</Section>';
    const out = String(await compile(source, { remarkPlugins: [remarkMath], rehypePlugins: [[rehypeKatex, katexOptions], rehypeKatexHtml] }));
    expect((out.match(/KatexHtml/g) ?? []).length).toBeGreaterThanOrEqual(2);
    // No KaTeX span tree survives as JSX: the formula markup lives only inside the html strings.
    expect(out).not.toMatch(/className: "mord/);
  });
});
