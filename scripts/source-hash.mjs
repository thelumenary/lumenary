#!/usr/bin/env node
// Print the sourceHash of a canonical content file: the first 12 hex digits of
// sha256 over its body (frontmatter excluded). Translations record this value
// so the site can detect when the original has changed.
// Usage: node scripts/source-hash.mjs content/math/lessons/collections/en.mdx
import fs from "node:fs";
import crypto from "node:crypto";
import matter from "gray-matter";

const file = process.argv[2];
if (!file) {
  console.error("usage: node scripts/source-hash.mjs <file.mdx>");
  process.exit(2);
}
const { content } = matter(fs.readFileSync(file, "utf8"));
console.log(crypto.createHash("sha256").update(content).digest("hex").slice(0, 12));
