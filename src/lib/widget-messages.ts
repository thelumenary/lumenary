import "server-only";
import fs from "node:fs";
import path from "node:path";

const WIDGETS = path.join(process.cwd(), "src/components/widgets");
const memo = new Map<string, Set<string>>();

/** The `w.<namespace>` message namespaces a source file refers to (over-approximated; unknown ones are ignored). */
function namespacesIn(file: string): Set<string> {
  if (!memo.has(file)) {
    const text = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
    memo.set(file, new Set([...text.matchAll(/\bw\.([A-Za-z][A-Za-z0-9]*)\b/g)].map((m) => m[1])));
  }
  return memo.get(file)!;
}

/**
 * Message namespaces (`w.<ns>`) needed by the widgets an MDX body uses, so a lesson page ships
 * only those strings to the browser instead of every widget's strings (about 90 KB per page).
 */
export function widgetMessageNamespaces(body: string): string[] {
  const out = new Set<string>(["common"]);
  const lib = path.join(WIDGETS, "lib");
  if (fs.existsSync(lib)) for (const f of fs.readdirSync(lib)) for (const n of namespacesIn(path.join(lib, f))) out.add(n);
  for (const m of body.matchAll(/<([A-Z][A-Za-z0-9]*)\b/g)) for (const n of namespacesIn(path.join(WIDGETS, `${m[1]}.tsx`))) out.add(n);
  return [...out].sort().map((n) => `w.${n}`);
}
