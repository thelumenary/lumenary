import { toHtml } from "hast-util-to-html";
import type { Element, Root, RootContent } from "hast";

/**
 * After rehype-katex, replace each typeset formula's element tree with a single `<KatexHtml>`
 * MDX element carrying the formula's HTML as a string.
 *
 * KaTeX emits dozens of nested spans per formula. Rendered as React elements, every one of them
 * is serialised again in the page's React Server Components payload (and in each prefetch file),
 * which made formula-heavy lessons several megabytes larger. As one string, a formula costs about
 * what its HTML costs. The HTML is produced by KaTeX itself (with `trust` off), never by authors.
 */
export function rehypeKatexHtml() {
  return (tree: Root) => {
    const walk = (parent: { children: RootContent[] }) => {
      parent.children.forEach((node, i) => {
        // Descend through MDX JSX elements (<Section>, <Theorem>, …) as well as HTML elements.
        const cls = node.type === "element" ? (node as Element).properties?.className : undefined;
        const classes = Array.isArray(cls) ? cls.map(String) : [];
        if (classes.includes("katex") || classes.includes("katex-display")) {
          parent.children[i] = {
            type: "mdxJsxTextElement",
            name: "KatexHtml",
            attributes: [
              { type: "mdxJsxAttribute", name: "className", value: classes.join(" ") },
              { type: "mdxJsxAttribute", name: "html", value: toHtml((node as Element).children) },
            ],
            children: [],
          } as unknown as RootContent;
          return;
        }
        if ("children" in node && Array.isArray(node.children)) walk(node as { children: RootContent[] });
      });
    };
    walk(tree);
  };
}
