#!/usr/bin/env node
/**
 * check-lesson.mjs — everything an author needs to know about one or more lessons, without
 * regenerating the shared verification reports:
 *
 *   npm run check:lesson -- sets integers
 *
 * For each lesson it:
 *   1. runs the source-only lesson checks and a full render (tests/lesson-check.test.ts);
 *   2. builds the Lean modules that hold the lesson's declarations (and their exercise files)
 *      with `lake build <Module>`, then runs `#print axioms` on every cited declaration and
 *      fails if any depends on `sorryAx`;
 *   3. runs pytest for the lesson's experiments (their own tests plus the browser-safety and
 *      output checks) and for the lesson's Python exercises.
 *
 * It never writes content/verification/*.json; `npm run verify` does that for the whole site.
 */
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import matter from "gray-matter";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const FORMAL = path.join(ROOT, "formal");
const slugs = process.argv.slice(2).filter((a) => !a.startsWith("-"));
if (slugs.length === 0) {
  console.error("usage: npm run check:lesson -- <slug> [<slug> …]");
  process.exit(2);
}

let failed = false;
const fail = (msg) => {
  failed = true;
  console.error(`✖ ${msg}`);
};
const ok = (msg) => console.log(`✔ ${msg}`);
const run = (cmd, args, opts = {}) => spawnSync(cmd, args, { cwd: ROOT, encoding: "utf8", maxBuffer: 256 * 1024 * 1024, ...opts });

/* ---------------------------------------------------------------- 1. lesson checks */
{
  const res = run("npx", ["vitest", "run", "tests/lesson-check.test.ts", "--reporter=dot"], { env: { ...process.env, LESSONS: slugs.join(",") } });
  const out = `${res.stdout}${res.stderr}`;
  if (res.status === 0) ok(`lesson checks and render: ${slugs.join(", ")}`);
  else {
    fail("lesson checks (tests/lesson-check.test.ts):");
    console.error(out.split("\n").filter((l) => !/^\s*$/.test(l)).slice(-80).join("\n"));
  }
}

/* ---------------------------------------------------------------- 2. Lean */
function leanEnv() {
  const env = { ...process.env };
  const candidates = [];
  if (process.env.LEAN_BIN) candidates.push(process.env.LEAN_BIN);
  const tc = path.join(ROOT, ".toolchain");
  if (fs.existsSync(tc)) for (const d of fs.readdirSync(tc).filter((d) => d.startsWith("lean-")).sort().reverse()) candidates.push(path.join(tc, d, "bin"));
  candidates.push(path.join(os.homedir(), ".elan", "bin"));
  const bin = candidates.find((d) => fs.existsSync(path.join(d, "lake")));
  if (bin) env.PATH = `${bin}${path.delimiter}${env.PATH ?? ""}`;
  return env;
}

/** Map "Lumenary.Foo.bar" to the module whose source declares it (by namespace + name). */
function moduleDeclaring(decl) {
  const parts = decl.split(".");
  for (let k = parts.length - 1; k >= 2; k--) {
    const mod = parts.slice(0, k).join(".");
    const file = path.join(FORMAL, `${mod.replaceAll(".", "/")}.lean`);
    if (fs.existsSync(file)) return mod;
  }
  // Fall back to a search for the short name.
  const short = parts.at(-1);
  const dir = path.join(FORMAL, "Lumenary");
  for (const f of fs.readdirSync(dir, { recursive: true })) {
    if (!String(f).endsWith(".lean")) continue;
    const text = fs.readFileSync(path.join(dir, String(f)), "utf8");
    if (new RegExp(`\\b(theorem|lemma|def|abbrev|instance|structure|class|inductive)\\s+${short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`).test(text))
      return `Lumenary.${String(f).replace(/\.lean$/, "").split(path.sep).join(".")}`;
  }
  return null;
}

/**
 * The conventions scripts/verify-lean.mjs enforces at verification time, checked early: region
 * ids, one declaration per region, provenance (library) or solution (exercises), unique ids,
 * and no axioms / native_decide in the library.
 */
const REGION_ID = /^(ex\.)?[a-z][a-z0-9_]*(\.[a-z0-9_]+)+$/;
const DECL = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque|axiom)\b/;
function allRegionIds(exceptFile) {
  const ids = new Map();
  const walk = (dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith(".lean") && p !== exceptFile)
        for (const m of fs.readFileSync(p, "utf8").matchAll(/^\s*--\s*@region\s+(\S+)/gm)) ids.set(m[1], path.relative(FORMAL, p));
    }
  };
  for (const lib of ["Lumenary", "LumenaryExercises"]) if (fs.existsSync(path.join(FORMAL, lib))) walk(path.join(FORMAL, lib));
  return ids;
}
function lintLeanFile(file, isExercise) {
  const problems = [];
  const rel = path.relative(ROOT, file);
  const others = allRegionIds(file);
  let open = null;
  let depth = 0;
  fs.readFileSync(file, "utf8").split("\n").forEach((raw, i) => {
    // track block comments so commented-out code is ignored
    let line = raw;
    if (depth > 0 || line.includes("/-")) {
      let out = "";
      for (let k = 0; k < line.length; k++) {
        const two = line.slice(k, k + 2);
        if (two === "/-") { depth++; k++; continue; }
        if (two === "-/" && depth > 0) { depth--; k++; continue; }
        if (depth === 0) out += line[k];
      }
      line = out;
    }
    const where = `${rel}:${i + 1}`;
    const marker = line.match(/^\s*--\s*@(region|endregion|provenance|solution)\b\s*(.*?)\s*$/);
    if (marker) {
      const [, tag, arg] = marker;
      if (tag === "region") {
        if (open) problems.push(`${where}: region ${arg} opened inside ${open.id}`);
        if (!REGION_ID.test(arg)) problems.push(`${where}: region id "${arg}" must be lowercase dotted <module_snake>.<name> (a-z, 0-9, _)`);
        if (isExercise && !arg.startsWith("ex.")) problems.push(`${where}: exercise region ids start with "ex."`);
        if (others.has(arg)) problems.push(`${where}: region id ${arg} is already used in ${others.get(arg)}`);
        open = { id: arg, decls: 0, provenance: null, solution: null, line: i + 1 };
      } else if (tag === "endregion") {
        if (!open) problems.push(`${where}: @endregion without @region`);
        else {
          if (open.decls !== 1) problems.push(`${rel}:${open.line}: region ${open.id} has ${open.decls} declarations (exactly 1 required)`);
          if (!isExercise && !["library", "independent", "definition"].includes(open.provenance ?? "")) problems.push(`${rel}:${open.line}: region ${open.id} needs "-- @provenance library|independent|definition"`);
          if (isExercise && !open.solution) problems.push(`${rel}:${open.line}: exercise region ${open.id} needs "-- @solution Lumenary.<Module>.<name>"`);
        }
        open = null;
      } else if (open && tag === "provenance") open.provenance = arg;
      else if (open && tag === "solution") open.solution = arg;
      return;
    }
    const code = line.replace(/--.*$/, "");
    const d = code.match(DECL);
    if (d) {
      if (d[1] === "axiom") problems.push(`${where}: axiom declarations are not allowed`);
      if (!open) problems.push(`${where}: declaration outside a @region`);
      else open.decls++;
    }
    if (!isExercise && /\b(sorry|admit|native_decide)\b/.test(code)) problems.push(`${where}: sorry/admit/native_decide is not allowed in the library`);
  });
  if (open) problems.push(`${rel}: region ${open.id} is never closed`);
  return problems;
}

const env = leanEnv();
for (const slug of slugs) {
  const mdx = path.join(ROOT, "content/math/lessons", slug, "en.mdx");
  if (!fs.existsSync(mdx)) continue;
  const f = matter(fs.readFileSync(mdx, "utf8")).data;
  const decls = Array.isArray(f.lean) ? f.lean : [];
  const modules = new Map();
  for (const d of decls) {
    const mod = moduleDeclaring(d);
    if (!mod) fail(`${slug}: cannot find the Lean module declaring ${d}`);
    else modules.set(mod, [...(modules.get(mod) ?? []), d]);
  }
  for (const [mod, names] of modules) {
    // Only lint the lesson's own module (the original seven core modules predate these checks).
    const mainFile = path.join(FORMAL, `${mod.replaceAll(".", "/")}.lean`);
    const exFile = path.join(FORMAL, `${mod.replace(/^Lumenary\./, "LumenaryExercises.").replaceAll(".", "/")}.lean`);
    const lint = [...lintLeanFile(mainFile, false), ...(fs.existsSync(exFile) ? lintLeanFile(exFile, true) : [])];
    if (lint.length) fail(`${slug}: Lean conventions (checked by verify-lean):\n  ${lint.join("\n  ")}`);
    const targets = [mod];
    const ex = mod.replace(/^Lumenary\./, "LumenaryExercises.");
    if (fs.existsSync(path.join(FORMAL, `${ex.replaceAll(".", "/")}.lean`))) targets.push(ex);
    const build = run("lake", ["build", ...targets], { cwd: FORMAL, env });
    const out = `${build.stdout}${build.stderr}`;
    const errors = out.split("\n").filter((l) => /^error:/.test(l));
    const exerciseWarnings = out
      .split("\n")
      .filter((l) => /^warning: LumenaryExercises\/\S+\.lean:\d+:\d+:/.test(l) && !/declaration uses [`']sorry[`']/.test(l));
    if (build.status !== 0) {
      fail(`${slug}: lake build ${targets.join(" ")} failed`);
      console.error(out.split("\n").filter((l) => !l.startsWith("trace:")).slice(-60).join("\n"));
      continue;
    }
    if (errors.length) fail(`${slug}: Lean errors:\n${errors.join("\n")}`);
    if (exerciseWarnings.length) fail(`${slug}: exercise files may only warn about sorry:\n${exerciseWarnings.join("\n")}`);
    const mainWarnings = out.split("\n").filter((l) => /^warning: Lumenary\/\S+\.lean:\d+:\d+:/.test(l));
    if (mainWarnings.length) console.log(`  note: warnings in ${mod} (please fix linter warnings such as unused variables):\n  ${mainWarnings.join("\n  ")}`);
    // #print axioms on each cited declaration
    const dir = path.join(FORMAL, ".lake", "check");
    fs.mkdirSync(dir, { recursive: true });
    const tmp = path.join(dir, `Axioms_${slug.replace(/[^a-z0-9]/g, "_")}_${process.pid}.lean`);
    fs.writeFileSync(tmp, [`import ${mod}`, "", ...names.map((n) => `#print axioms ${n}`), ""].join("\n"));
    const ax = run("lake", ["env", "lean", path.relative(FORMAL, tmp)], { cwd: FORMAL, env });
    fs.rmSync(tmp, { force: true });
    const axOut = `${ax.stdout}${ax.stderr}`;
    if (ax.status !== 0) {
      fail(`${slug}: #print axioms failed for ${mod}:\n${axOut}`);
      continue;
    }
    for (const n of names) {
      const m = axOut.match(new RegExp(`'${n.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}' (depends on axioms: \\[([^\\]]*)\\]|does not depend on any axioms)`));
      if (!m) fail(`${slug}: no axioms output for ${n} (is the name right?)`);
      else if ((m[2] ?? "").includes("sorryAx")) fail(`${slug}: ${n} depends on sorry`);
    }
    ok(`${slug}: Lean ${targets.join(", ")} built; ${names.length} declaration(s) sorry-free`);
  }
}

/* ---------------------------------------------------------------- 3. Python */
const python = [path.join(ROOT, "compute/.venv/bin/python"), "python3"].find((p) => p === "python3" || fs.existsSync(p));
for (const slug of slugs) {
  const mdx = path.join(ROOT, "content/math/lessons", slug, "en.mdx");
  if (!fs.existsSync(mdx)) continue;
  const f = matter(fs.readFileSync(mdx, "utf8")).data;
  const ids = Array.isArray(f.compute) ? f.compute : [];
  const tests = ids.map((id) => `compute/tests/test_${id}.py`).filter((p) => fs.existsSync(path.join(ROOT, p)));
  if (ids.length) {
    const k = ids.join(" or ");
    const res = run(python, ["-m", "pytest", "-q", "-p", "no:cacheprovider", ...tests, "compute/tests/test_experiments_meta.py", "-k", k, "-c", "compute/pytest.ini", "--rootdir", "compute"]);
    if (res.status === 0) ok(`${slug}: experiments ${ids.join(", ")} pass their tests and the browser-safety checks`);
    else {
      fail(`${slug}: pytest failed for ${ids.join(", ")}`);
      console.error(`${res.stdout}${res.stderr}`.split("\n").slice(-60).join("\n"));
    }
    for (const id of ids) {
      const r = run(python, ["-I", "-X", "utf8", path.join(ROOT, "compute/experiments", `${id}.py`)], { cwd: path.join(ROOT, "compute") });
      if (r.status !== 0) fail(`${slug}: ${id}.py does not run as a script:\n${r.stderr}`);
    }
  }
  // Python exercises: point the exercise checker at a folder containing only this lesson.
  const exFile = path.join(ROOT, "content/math/lessons", slug, "exercises.json");
  if (fs.existsSync(exFile) && JSON.parse(fs.readFileSync(exFile, "utf8")).exercises?.some((e) => e.type === "python")) {
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "lumenary-ex-"));
    fs.mkdirSync(path.join(tmpDir, slug));
    fs.copyFileSync(exFile, path.join(tmpDir, slug, "exercises.json"));
    const res = run(python, ["-m", "pytest", "-q", "-p", "no:cacheprovider", "compute/tests/test_lesson_exercises.py", "-c", "compute/pytest.ini", "--rootdir", "compute"], {
      env: { ...process.env, LUMENARY_LESSONS_DIR: tmpDir },
    });
    fs.rmSync(tmpDir, { recursive: true, force: true });
    if (res.status === 0) ok(`${slug}: Python exercises — solutions pass, starters fail`);
    else {
      fail(`${slug}: Python exercise checks failed`);
      console.error(`${res.stdout}${res.stderr}`.split("\n").slice(-40).join("\n"));
    }
  }
}

console.log(failed ? "\ncheck-lesson: problems found (see ✖ above)" : "\ncheck-lesson: all checks passed");
process.exit(failed ? 1 : 0);
