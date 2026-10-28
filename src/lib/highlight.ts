import "server-only";
import { createHighlighter, type Highlighter } from "shiki";

let highlighter: Promise<Highlighter> | null = null;

function getHighlighter() {
  highlighter ??= createHighlighter({ themes: ["github-light", "github-dark-dimmed"], langs: ["lean4", "python", "json", "bash"] });
  return highlighter;
}

/** Server-side syntax highlighting with light/dark themes switched by CSS variables. */
export async function highlight(code: string, lang: "lean4" | "python" | "json" | "bash"): Promise<string> {
  const hl = await getHighlighter();
  return hl.codeToHtml(code, {
    lang,
    themes: { light: "github-light", dark: "github-dark-dimmed" },
    defaultColor: "light",
  });
}
