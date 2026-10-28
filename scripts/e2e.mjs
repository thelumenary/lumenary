// End-to-end checks against the exported site (out/), in a real browser.
// Usage: npm run build && npm run test:e2e
// Set PW_CHANNEL=chromium to use Playwright's bundled Chromium instead of Chrome.
// Set E2E_SKIP_PYODIDE=1 to skip the checks that download Pyodide from the CDN.
import path from "node:path";
import fs from "node:fs";
import { chromium } from "playwright";
import { serve } from "./serve-static.mjs";

const ROOT = path.resolve(import.meta.dirname, "..");
const PORT = 4190;
const BASE = `http://localhost:${PORT}`;
const results = [];
const check = async (name, fn) => {
  const started = Date.now();
  try {
    await fn();
    results.push({ name, ok: true, ms: Date.now() - started });
    console.log(`  ✓ ${name}`);
  } catch (err) {
    results.push({ name, ok: false, error: String(err).split("\n")[0] });
    console.log(`  ✗ ${name}\n      ${String(err).split("\n")[0]}`);
  }
};

const server = await serve(path.join(ROOT, "out"), PORT);
const browser = await chromium.launch({ channel: process.env.PW_CHANNEL ?? "chrome" });

async function withPage(fn, opts = {}) {
  const ctx = await browser.newContext({ viewport: { width: 1280, height: 900 }, ...opts });
  const page = await ctx.newPage();
  const errors = [];
  page.on("pageerror", (e) => errors.push(String(e)));
  page.on("console", (m) => m.type() === "error" && errors.push(m.text()));
  try {
    await fn(page);
  } finally {
    await ctx.close();
  }
  if (errors.length) throw new Error(`console errors: ${errors.join(" | ")}`);
}

const locales = ["en", "es", "ar", "hi", "zh-Hans", "sw"];
const pages = ["", "math/", "math/graph/", "math/lessons/collections/", "math/lessons/composition/", "math/trails/clock-arithmetic/", "lab/", "formal/", "practice/", "progress/", "educators/", "educators/overview/", "languages/", "verification/", "about/", "contribute/"];

console.log("Pages render without errors:");
for (const locale of locales) {
  await check(`${locale}: ${pages.length} pages`, () =>
    withPage(async (page) => {
      for (const p of pages) {
        const res = await page.goto(`${BASE}/${locale}/${p}`, { waitUntil: "load" });
        if (!res || res.status() !== 200) throw new Error(`${p} → HTTP ${res?.status()}`);
        const lang = await page.getAttribute("html", "lang");
        if (lang !== locale) throw new Error(`${p}: <html lang="${lang}">`);
      }
      if (locale === "ar" && (await page.getAttribute("html", "dir")) !== "rtl") throw new Error("Arabic page is not rtl");
    }),
  );
}

console.log("Interactions:");
await check("set exercise gives targeted feedback, then accepts any order", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/en/math/lessons/sets/`, { waitUntil: "networkidle" });
    const ex = page.locator("#ex-sets-union");
    await ex.locator("input").fill("{3, 4}");
    await ex.getByRole("button", { name: "Check" }).click();
    await ex.getByText("intersection").first().waitFor({ timeout: 5000 });
    await ex.locator("input").fill("{6, 5, 4, 3, 2, 1, 1}");
    await ex.getByRole("button", { name: "Check" }).click();
    await ex.getByText("Yes — that’s right.").waitFor({ timeout: 5000 });
  }),
);
await check("integer exercise accepts Eastern Arabic numerals", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/ar/math/lessons/integers/`, { waitUntil: "networkidle" });
    const ex = page.locator("#ex-integers-add");
    await ex.locator("input").fill("−٣");
    await ex.locator("button[type=submit]").click();
    await ex.locator("[aria-live=polite] .bg-good-soft").waitFor({ timeout: 5000 });
  }),
);
await check("hints reveal one at a time", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/en/math/lessons/functions/`, { waitUntil: "networkidle" });
    const ex = page.locator("#ex-functions-count");
    await ex.getByRole("button", { name: "Show a hint" }).click();
    await ex.getByText("Hint 1 of 2").waitFor({ timeout: 5000 });
    if (await ex.getByText("Hint 2 of 2").count()) throw new Error("second hint shown too early");
  }),
);
await check("arrow diagram detects a non-function", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/en/math/lessons/functions/`, { waitUntil: "networkidle" });
    await page.getByRole("button", { name: "Not a function" }).click();
    await page.getByText("has more than one arrow").first().waitFor({ timeout: 5000 });
  }),
);
await check("knowledge graph highlights a topic's prerequisites", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/en/math/graph/?topic=math.cat.composition`, { waitUntil: "networkidle" });
    await page.getByText("required prerequisites", { exact: false }).first().waitFor({ timeout: 5000 });
  }),
);
await check("progress tracking is off by default and stores nothing", () =>
  withPage(async (page) => {
    await page.goto(`${BASE}/en/math/lessons/sets/`, { waitUntil: "networkidle" });
    const stored = await page.evaluate(() => localStorage.getItem("lumenary:progress:v1"));
    if (stored !== null) throw new Error("progress was stored without consent");
  }),
);

if (!process.env.E2E_SKIP_PYODIDE) {
  console.log("Python in the browser (downloads Pyodide):");
  await check("lesson experiment runs and prints its epistemic status", () =>
    withPage(async (page) => {
      await page.goto(`${BASE}/en/math/lessons/sets/#computation`, { waitUntil: "networkidle" });
      await page.locator("#computation").getByRole("button", { name: "Run in browser" }).first().click();
      await page.waitForFunction(() => [...document.querySelectorAll("#computation [aria-live=polite] pre")].some((p) => /Epistemic status/.test(p.textContent ?? "")), null, { timeout: 120000 });
    }),
  );
  await check("Python exercise: correct solution passes the tests", () =>
    withPage(async (page) => {
      await page.goto(`${BASE}/en/math/lessons/composition/`, { waitUntil: "networkidle" });
      const ex = page.locator("#ex-composition-python");
      await ex.locator("textarea").fill("def compose(g, f):\n    return {x: g[f[x]] for x in f}\n");
      await ex.getByRole("button", { name: "Run tests" }).click();
      await ex.getByText("Yes — that’s right.").waitFor({ timeout: 120000 });
    }),
  );
  await check("an infinite loop is stopped by the time limit", () =>
    withPage(async (page) => {
      await page.goto(`${BASE}/en/lab/`, { waitUntil: "networkidle" });
      await page.getByRole("button", { name: "Edit and experiment" }).last().click();
      await page.locator("textarea").last().fill("while True:\n    pass\n");
      await page.getByRole("button", { name: "Run in browser" }).last().click();
      await page.getByText("Stopped: the program ran longer than").waitFor({ timeout: 120000 });
    }),
  );
}

await browser.close();
server.close();
const failed = results.filter((r) => !r.ok);
fs.mkdirSync(path.join(ROOT, "content/verification"), { recursive: true });
fs.writeFileSync(path.join(ROOT, "content/verification/e2e-report.json"), JSON.stringify({ generatedAt: new Date().toISOString(), passed: results.length - failed.length, failed: failed.length, results }, null, 2) + "\n");
console.log(`\n${results.length - failed.length} passed, ${failed.length} failed`);
process.exit(failed.length ? 1 : 0);
