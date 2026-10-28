// Capture screenshots of the exported site for the educator evaluation package,
// and report any console errors encountered on each page.
// Usage: npm run build && npm run screenshots   (then rebuild to include them)
import fs from "node:fs";
import path from "node:path";
import { chromium } from "playwright";
import { serve } from "./serve-static.mjs";

const ROOT = path.resolve(import.meta.dirname, "..");
const OUT = path.join(ROOT, "public/educators/screenshots");
const PAGES = [
  ["01-home", "/en/", "light"],
  ["02-lesson-sets", "/en/math/lessons/sets/", "light"],
  ["03-lesson-composition-dark", "/en/math/lessons/composition/#categories", "dark"],
  ["04-knowledge-graph", "/en/math/graph/", "light"],
  ["05-wonder-trail-clock", "/en/math/trails/clock-arithmetic/", "light"],
  ["06-formal-lab", "/en/formal/", "dark"],
  ["07-arabic-rtl-home", "/ar/", "light"],
  ["08-practice", "/en/practice/", "light"],
];

const server = await serve(path.join(ROOT, "out"), 4173);
const browser = await chromium.launch({ channel: process.env.PW_CHANNEL ?? "chrome" });
fs.mkdirSync(OUT, { recursive: true });
let failures = 0;
for (const [name, url, theme] of PAGES) {
  const context = await browser.newContext({ viewport: { width: 1440, height: 900 }, colorScheme: theme, deviceScaleFactor: 1 });
  const page = await context.newPage();
  const errors = [];
  page.on("pageerror", (e) => errors.push(String(e)));
  page.on("console", (m) => m.type() === "error" && errors.push(m.text()));
  await page.goto(`http://localhost:4173${url}`, { waitUntil: "networkidle" });
  await page.waitForTimeout(1200);
  await page.screenshot({ path: path.join(OUT, `${name}.png`) });
  if (errors.length) {
    failures++;
    console.log(`✗ ${name}: ${errors.join(" | ")}`);
  } else console.log(`✓ ${name}`);
  await context.close();
}
await browser.close();
server.close();
process.exit(failures ? 1 : 0);
