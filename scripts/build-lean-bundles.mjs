#!/usr/bin/env node
// For every Lean source file, write a tiny static page under public/lean-open/
// that opens a self-contained copy of the file in the official Lean web editor
// (live.lean-lang.org). `import Lumenary.X` lines are inlined recursively, which
// works because the library uses core Lean only. Runs before `next build`/`dev`.
import fs from "node:fs";
import path from "node:path";

const ROOT = path.resolve(import.meta.dirname, "..");
const FORMAL = path.join(ROOT, "formal");
const OUT = path.join(ROOT, "public/lean-open");

function bundle(file, seen = new Set()) {
  if (seen.has(file)) return "";
  seen.add(file);
  const full = path.join(FORMAL, file);
  if (!fs.existsSync(full)) return "";
  const out = [];
  for (const line of fs.readFileSync(full, "utf8").split("\n")) {
    const m = line.match(/^import\s+(Lumenary\S*)/);
    if (m) {
      out.push(bundle(`${m[1].replaceAll(".", "/")}.lean`, seen));
      continue;
    }
    if (/^\s*--\s*@(region|endregion|provenance|solution)\b/.test(line)) continue;
    out.push(line);
  }
  return out.join("\n").replace(/\n{3,}/g, "\n\n");
}

export function bundleSlug(file) {
  return file.replace(/\.lean$/, "").replaceAll("/", "--");
}

const files = [];
const walk = (dir) => {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    if (e.name.startsWith(".")) continue;
    const full = path.join(dir, e.name);
    if (e.isDirectory()) walk(full);
    else if (e.name.endsWith(".lean")) files.push(path.relative(FORMAL, full));
  }
};
if (fs.existsSync(FORMAL)) walk(FORMAL);

fs.rmSync(OUT, { recursive: true, force: true });
fs.mkdirSync(OUT, { recursive: true });
for (const file of files) {
  const code = bundle(file).trim() + "\n";
  const esc = code.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[c]);
  const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Opening ${file} in the Lean web editor…</title>
<style>body{font-family:system-ui,sans-serif;max-width:52rem;margin:2rem auto;padding:0 1rem;color:#172033;background:#faf7f0}pre{background:#fff;border:1px solid #e5ddcc;padding:1rem;overflow:auto;font-size:.8rem}</style>
<script>var code=${JSON.stringify(code).replace(/</g, "\\u003c")};location.replace("https://live.lean-lang.org/#code="+encodeURIComponent(code));</script>
</head><body><p>Opening <code>formal/${file}</code> in the Lean web editor… If nothing happens, copy the code below into <a href="https://live.lean-lang.org/">live.lean-lang.org</a>.</p><pre>${esc}</pre></body></html>
`;
  fs.writeFileSync(path.join(OUT, `${bundleSlug(file)}.html`), html);
}
console.log(`lean bundles: ${files.length} files → public/lean-open/`);
