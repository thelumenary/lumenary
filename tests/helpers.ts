import fs from "node:fs";
import path from "node:path";
import matter from "gray-matter";

export const ROOT = path.resolve(import.meta.dirname, "..");
export const read = (p: string) => fs.readFileSync(path.join(ROOT, p), "utf8");
export const json = <T = unknown>(p: string): T => JSON.parse(read(p)) as T;
export const exists = (p: string) => fs.existsSync(path.join(ROOT, p));
export const dirs = (p: string) =>
  fs
    .readdirSync(path.join(ROOT, p), { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name);
export const files = (p: string) => fs.readdirSync(path.join(ROOT, p));
export const fm = (p: string) => matter(read(p));
