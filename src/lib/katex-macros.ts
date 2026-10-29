/** KaTeX macros shared by lesson prose (src/lib/markdown.ts) and server-rendered diagrams. */
export const KATEX_MACROS: Record<string, string> = {
  "\\N": "\\mathbb{N}",
  "\\Z": "\\mathbb{Z}",
  "\\Q": "\\mathbb{Q}",
  "\\R": "\\mathbb{R}",
  "\\C": "\\mathbb{C}",
  "\\cat": "\\mathbf{#1}",
  "\\id": "\\mathrm{id}",
  "\\Hom": "\\mathrm{Hom}",
};
