#!/usr/bin/env node
/**
 * verify-lean.mjs — build the Lean project in formal/ and write
 * content/verification/lean-report.json (schema: `LeanReport` in src/lib/schema.ts).
 *
 *   node scripts/verify-lean.mjs            # incremental build (Lake re-checks changed files)
 *   node scripts/verify-lean.mjs --clean    # `lake clean` first, then a full rebuild
 *
 * What it does:
 *   1. Locates `lean`/`lake`: $LEAN_BIN (a directory), then <repo>/.toolchain/lean-<ver>/bin,
 *      then ~/.elan/bin, then $PATH.
 *   2. Runs `lake build Lumenary LumenaryExercises` in formal/ and times it.
 *   3. Parses the `-- @region` / `-- @provenance` / `-- @solution` / `-- @endregion` markers
 *      and the declarations inside them from formal/**.lean.
 *   4. Runs `#print axioms` for every main-library declaration (temp file in formal/.lake/)
 *      and marks `usesSorry` when `sorryAx` appears.
 *   5. Writes the report. The report is written even when the build fails; the script then
 *      exits 1. It also exits 1 on convention violations (see `problems` below).
 *
 * Honesty rules encoded here: a file only counts as `success` if Lake built it in this run
 * (or confirmed it up to date) with no errors; a declaration in a file that did not build is
 * reported with `usesSorry: true` (Lean's error recovery elaborates failed proofs to
 * `sorryAx`) and empty `axioms`, so nothing downstream can label it "formally verified".
 *
 * Node 22+, no npm dependencies.
 */
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const FORMAL = path.join(ROOT, "formal");
const REPORT_PATH = path.join(ROOT, "content", "verification", "lean-report.json");
const LIBS = ["Lumenary", "LumenaryExercises"];
const MAIN_LIB = "Lumenary";
const EXERCISE_LIB = "LumenaryExercises";
const BUILD_ARGS = ["build", ...LIBS];
const BUILD_COMMAND = `lake ${BUILD_ARGS.join(" ")}`;

const PROVENANCES = new Set(["library", "independent", "definition"]);
const REGION_ID = /^(ex\.)?[a-z][a-z0-9_]*(\.[a-z0-9_]+)+$/;

/** Convention / policy violations. Any entry makes the script exit 1 (after writing the report). */
const problems = [];

const rel = (p) => path.relative(ROOT, p).split(path.sep).join("/");
const log = (...a) => console.log("[verify-lean]", ...a);

/* ------------------------------------------------------------------ */
/* 1. Toolchain discovery                                             */
/* ------------------------------------------------------------------ */

function isExecutable(p) {
  try {
    fs.accessSync(p, fs.constants.X_OK);
    return fs.statSync(p).isFile();
  } catch {
    return false;
  }
}

function hasLeanAndLake(dir) {
  return isExecutable(path.join(dir, "lean")) && isExecutable(path.join(dir, "lake"));
}

function readToolchainFile() {
  try {
    return fs.readFileSync(path.join(FORMAL, "lean-toolchain"), "utf8").trim();
  } catch {
    return "unknown";
  }
}

/** Returns { binDir, source } where binDir may be null (meaning: rely on $PATH). */
function findToolchain(toolchain) {
  if (process.env.LEAN_BIN) {
    const dir = path.resolve(process.env.LEAN_BIN);
    if (hasLeanAndLake(dir)) return { binDir: dir, source: "LEAN_BIN" };
    log(`LEAN_BIN=${dir} does not contain both lean and lake; ignoring it`);
  }

  const tcDir = path.join(ROOT, ".toolchain");
  if (fs.existsSync(tcDir)) {
    const wanted = (toolchain.match(/v?(\d+\.\d+\.\d+[^\s]*)$/) || [])[1];
    const dirs = fs
      .readdirSync(tcDir)
      .filter((d) => d.startsWith("lean-") && hasLeanAndLake(path.join(tcDir, d, "bin")))
      // Prefer the release named in lean-toolchain, then the newest-looking name.
      .sort((a, b) => {
        const am = wanted && a.startsWith(`lean-${wanted}`) ? 0 : 1;
        const bm = wanted && b.startsWith(`lean-${wanted}`) ? 0 : 1;
        return am - bm || b.localeCompare(a, undefined, { numeric: true });
      });
    if (dirs.length > 0) return { binDir: path.join(tcDir, dirs[0], "bin"), source: `.toolchain/${dirs[0]}` };
  }

  const elan = path.join(os.homedir(), ".elan", "bin");
  if (hasLeanAndLake(elan)) return { binDir: elan, source: "~/.elan/bin" };

  for (const dir of (process.env.PATH || "").split(path.delimiter).filter(Boolean)) {
    if (hasLeanAndLake(dir)) return { binDir: dir, source: "PATH" };
  }
  return { binDir: null, source: "not found" };
}

function run(cmd, args, env, opts = {}) {
  const res = spawnSync(cmd, args, {
    cwd: FORMAL,
    env,
    encoding: "utf8",
    maxBuffer: 256 * 1024 * 1024,
    ...opts,
  });
  return {
    status: res.status,
    error: res.error,
    out: `${res.stdout ?? ""}${res.stderr ?? ""}`,
  };
}

/* ------------------------------------------------------------------ */
/* 2. Source parsing                                                  */
/* ------------------------------------------------------------------ */

function listLeanFiles() {
  const files = [];
  const walk = (dir) => {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      else if (entry.name.endsWith(".lean")) files.push(p);
    }
  };
  for (const lib of LIBS) {
    const rootFile = path.join(FORMAL, `${lib}.lean`);
    if (fs.existsSync(rootFile)) files.push(rootFile);
    const dir = path.join(FORMAL, lib);
    if (fs.existsSync(dir)) walk(dir);
  }
  return files;
}

/** formal/Lumenary/Sets.lean -> Lumenary.Sets */
function moduleOf(file) {
  return path.relative(FORMAL, file).replace(/\.lean$/, "").split(path.sep).join(".");
}

/**
 * Strip comments and string literals, keeping line structure. Returns, per line,
 * { code, comment } where `comment` is the text of a `--` line comment (if any).
 */
function lexLines(text) {
  const lines = text.split(/\r?\n/);
  let depth = 0; // block comment nesting depth (Lean block comments nest)
  return lines.map((line) => {
    let code = "";
    let comment = null;
    let i = 0;
    while (i < line.length) {
      const two = line.slice(i, i + 2);
      if (depth > 0) {
        if (two === "/-") {
          depth++;
          i += 2;
        } else if (two === "-/") {
          depth--;
          i += 2;
        } else i++;
        continue;
      }
      if (two === "/-") {
        depth = 1;
        i += 2;
        code += " ";
        continue;
      }
      if (two === "--") {
        comment = line.slice(i + 2);
        break;
      }
      const ch = line[i];
      if (ch === '"') {
        // string literal (single-line is enough for this project)
        i++;
        while (i < line.length && line[i] !== '"') i += line[i] === "\\" ? 2 : 1;
        i++;
        code += '""';
        continue;
      }
      if (ch === "'" && !/[\p{L}\p{N}_'!?.₀-₉]/u.test(line[i - 1] ?? " ")) {
        // char literal like 'a' or '\n'
        const m = line.slice(i).match(/^'(\\.|[^\\'])'/u);
        if (m) {
          code += "' '";
          i += m[0].length;
          continue;
        }
      }
      code += ch;
      i++;
    }
    return { code, comment };
  });
}

const DECL_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque|axiom)\b(.*)$/;
const KIND = {
  theorem: "theorem",
  lemma: "theorem",
  def: "def",
  abbrev: "def",
  opaque: "def",
  instance: "instance",
  structure: "structure",
  class: "structure",
  inductive: "structure",
  example: "example",
};

/** Parse regions, declarations and namespaces of one file. */
function parseFile(file) {
  const text = fs.readFileSync(file, "utf8");
  const lexed = lexLines(text);
  const where = (n) => `${rel(file)}:${n + 1}`;
  const scopes = []; // { kind: 'namespace' | 'section', name }
  const regions = [];
  const decls = [];
  const imports = [];
  let open = null;

  lexed.forEach(({ code, comment }, n) => {
    // --- markers (only in `--` comments that start the line) ---
    if (comment !== null && code.trim() === "") {
      const m = comment.match(/^\s*@(region|endregion|provenance|solution)\b\s*(.*?)\s*$/);
      if (m) {
        const [, tag, arg] = m;
        if (tag === "region") {
          if (open) problems.push(`${where(n)}: @region ${arg} opened inside region ${open.id}`);
          if (!REGION_ID.test(arg)) problems.push(`${where(n)}: region id "${arg}" is not lowercase dotted <module>.<name>`);
          open = { id: arg, provenance: null, solution: null, start: n, end: null, decls: [] };
          regions.push(open);
        } else if (tag === "endregion") {
          if (!open) problems.push(`${where(n)}: @endregion without @region`);
          else open.end = n;
          open = null;
        } else if (!open) {
          problems.push(`${where(n)}: @${tag} outside a region`);
        } else if (tag === "provenance") {
          if (!PROVENANCES.has(arg)) problems.push(`${where(n)}: unknown provenance "${arg}"`);
          open.provenance = arg;
        } else if (tag === "solution") {
          open.solution = arg;
        }
        return;
      }
    }

    // --- imports / namespaces / sections ---
    const im = code.match(/^\s*import\s+(.+)$/);
    if (im) {
      imports.push(...im[1].trim().split(/\s+/));
      return;
    }
    const ns = code.match(/^\s*namespace\s+(\S+)/);
    if (ns) {
      for (const part of ns[1].split(".")) scopes.push({ kind: "namespace", name: part });
      return;
    }
    const sec = code.match(/^\s*(?:noncomputable\s+)?section\b\s*(\S+)?/);
    if (sec) {
      scopes.push({ kind: "section", name: sec[1] ?? null });
      return;
    }
    const end = code.match(/^\s*end\b\s*(\S+)?\s*$/);
    if (end) {
      const parts = end[1] ? end[1].split(".") : [null];
      for (let k = parts.length - 1; k >= 0; k--) {
        const top = scopes.pop();
        if (!top || (top.name ?? null) !== parts[k]) {
          problems.push(`${where(n)}: unmatched 'end ${end[1] ?? ""}'`);
          break;
        }
      }
      return;
    }

    // --- declarations ---
    const d = code.match(DECL_RE);
    if (!d) return;
    const [, keyword, restRaw] = d;
    let rest = restRaw.trim();
    if (keyword === "axiom") {
      problems.push(`${where(n)}: 'axiom' declarations are not allowed in this project`);
      return;
    }
    if (keyword === "instance") rest = rest.replace(/^\(priority\s*:=\s*[^)]*\)\s*/, "");
    let local = null;
    if (keyword !== "example") {
      const tok = rest.match(/^([^\s(\[{:⦃]+)/);
      if (tok && tok[1] !== "where") local = tok[1].replace(/\.$/, ""); // `Category.{v, u}` -> `Category`
      if (!local) {
        problems.push(`${where(n)}: anonymous ${keyword} — give it an explicit name so it can be reported`);
        return;
      }
    }
    const nsPrefix = scopes.filter((s) => s.kind === "namespace").map((s) => s.name);
    let name;
    if (local === null) name = `${moduleOf(file)}.example_line${n + 1}`;
    else if (local.startsWith("_root_.")) name = local.slice("_root_.".length);
    else name = [...nsPrefix, local].join(".");
    const decl = { name, kind: KIND[keyword], line: n, region: open };
    decls.push(decl);
    if (open) open.decls.push(decl);
  });

  if (open) problems.push(`${rel(file)}: region ${open.id} is never closed`);

  // sorry count per region / per declaration span (comments and strings excluded)
  const countSorry = (from, to) =>
    lexed.slice(from, to + 1).reduce((acc, l) => acc + (l.code.match(/\bsorry\b/g) || []).length, 0);
  for (const r of regions) {
    r.sorryCount = countSorry(r.start, r.end ?? lexed.length - 1);
    if (r.decls.length !== 1) problems.push(`${rel(file)}: region ${r.id} contains ${r.decls.length} declarations (expected exactly 1)`);
  }
  decls.forEach((dcl, k) => {
    const next = k + 1 < decls.length ? decls[k + 1].line - 1 : lexed.length - 1;
    dcl.sorryCount = dcl.region ? dcl.region.sorryCount : countSorry(dcl.line, next);
  });

  return { file, module: moduleOf(file), text, regions, decls, imports };
}

/* ------------------------------------------------------------------ */
/* 3. Build-output analysis                                           */
/* ------------------------------------------------------------------ */

/** Modules Lake reported as failed, and files with error/warning messages. */
function analyseBuildOutput(out) {
  const failedModules = new Set();
  const errorFiles = new Set();
  const warnings = []; // { file, line, text }
  const lines = out.split(/\r?\n/);
  let inFailList = false;
  lines.forEach((line, i) => {
    const f = line.match(/^✖ \[\d+\/\d+\] (?:Building|Running|Compiling)\s+(\S+)/);
    if (f) failedModules.add(f[1].replace(/:.*$/, ""));
    if (/^Some required targets logged failures:/.test(line)) {
      inFailList = true;
      return;
    }
    if (inFailList) {
      const m = line.match(/^- (\S+)/);
      if (m) failedModules.add(m[1].replace(/:.*$/, ""));
      else inFailList = false;
    }
    const e = line.match(/^error: (\S+?\.lean):(\d+):(\d+):/);
    if (e) errorFiles.add(path.normalize(path.join(FORMAL, e[1])));
    const w = line.match(/^warning: (\S+?\.lean):(\d+):(\d+): (.*)$/);
    if (w) warnings.push({ file: path.normalize(path.join(FORMAL, w[1])), line: Number(w[2]), text: w[4] });
  });
  return { failedModules, errorFiles, warnings };
}

/* ------------------------------------------------------------------ */
/* 4. Axioms                                                          */
/* ------------------------------------------------------------------ */

function collectAxioms(modules, names, env) {
  const result = new Map();
  if (names.length === 0) return result;
  const dir = path.join(FORMAL, ".lake", "verify");
  fs.mkdirSync(dir, { recursive: true });
  const tmp = path.join(dir, "PrintAxioms.lean");
  const src = [
    "-- Generated by scripts/verify-lean.mjs; safe to delete.",
    ...modules.map((m) => `import ${m}`),
    "",
    ...names.map((n) => `#print axioms ${n}`),
    "",
  ].join("\n");
  fs.writeFileSync(tmp, src);
  const res = run("lake", ["env", "lean", path.relative(FORMAL, tmp)], env);
  try {
    fs.rmSync(tmp);
  } catch {}
  if (res.status !== 0) {
    problems.push(`#print axioms run failed (exit ${res.status}):\n${res.out}`);
    return result;
  }
  const re = /'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)/gs;
  for (const m of res.out.matchAll(re)) {
    const axioms = m[2] === undefined ? [] : m[2].split(",").map((s) => s.trim()).filter(Boolean);
    result.set(m[1], axioms);
  }
  for (const n of names) if (!result.has(n)) problems.push(`no #print axioms output for ${n} (does the name exist?)`);
  return result;
}

/* ------------------------------------------------------------------ */
/* main                                                               */
/* ------------------------------------------------------------------ */

function main() {
  const toolchain = readToolchainFile();
  const { binDir, source } = findToolchain(toolchain);
  const env = { ...process.env };
  if (binDir) env.PATH = `${binDir}${path.delimiter}${process.env.PATH ?? ""}`;
  log(`toolchain file: ${toolchain}; using lean/lake from ${source}${binDir ? ` (${binDir})` : ""}`);

  const ver = run("lean", ["--version"], env);
  const leanVersion = ver.status === 0 ? ver.out.trim() : "unavailable";
  if (ver.status !== 0) problems.push(`could not run 'lean --version': ${ver.error?.message ?? ver.out}`);
  log(leanVersion);

  if (process.argv.includes("--clean")) {
    log("lake clean");
    run("lake", ["clean"], env, { stdio: "inherit" });
  }

  // ---- build ----
  log(`$ (cd formal && ${BUILD_COMMAND})`);
  const t0 = performance.now();
  const build = ver.status === 0 ? run("lake", BUILD_ARGS, env) : { status: 1, out: "lean not available\n" };
  const durationMs = Math.round(performance.now() - t0);
  process.stdout.write(build.out);
  const buildSuccess = build.status === 0;
  log(`build ${buildSuccess ? "succeeded" : "FAILED"} in ${durationMs} ms`);
  if (!buildSuccess) problems.push("lake build failed");

  // ---- parse sources ----
  const parsed = listLeanFiles().map(parseFile);
  const byModule = new Map(parsed.map((p) => [p.module, p]));
  const { failedModules, errorFiles, warnings } = analyseBuildOutput(build.out);

  // A file succeeded iff the build attempted it without errors and all project imports succeeded.
  const okMemo = new Map();
  const fileOk = (p, seen = new Set()) => {
    if (okMemo.has(p.module)) return okMemo.get(p.module);
    if (seen.has(p.module)) return false;
    seen.add(p.module);
    let ok = buildSuccess || (!failedModules.has(p.module) && !errorFiles.has(path.normalize(p.file)));
    if (ok && !buildSuccess && (failedModules.size === 0 || ver.status !== 0)) ok = false; // failed before any module ran
    if (ok) for (const imp of p.imports) if (byModule.has(imp) && !fileOk(byModule.get(imp), seen)) ok = false;
    okMemo.set(p.module, ok);
    return ok;
  };

  const isMain = (p) => p.module === MAIN_LIB || p.module.startsWith(`${MAIN_LIB}.`);
  const isExercise = (p) => p.module === EXERCISE_LIB || p.module.startsWith(`${EXERCISE_LIB}.`);

  // Exercises may only produce "declaration uses `sorry`" warnings.
  for (const w of warnings) {
    const p = parsed.find((q) => path.normalize(q.file) === w.file);
    if (p && isExercise(p) && !/declaration uses [`']sorry[`']/.test(w.text))
      problems.push(`exercise warning other than sorry at ${rel(w.file)}:${w.line}: ${w.text}`);
    else if (p && isMain(p)) log(`note: warning in main library at ${rel(w.file)}:${w.line}: ${w.text}`);
  }

  // ---- axioms for main-library declarations ----
  const mainFiles = parsed.filter(isMain);
  const okMain = mainFiles.filter((p) => fileOk(p));
  const namesToCheck = okMain.flatMap((p) => p.decls.filter((d) => d.kind !== "example").map((d) => d.name));
  const axiomsByName = collectAxioms(
    okMain.map((p) => p.module),
    namesToCheck,
    env,
  );

  // ---- assemble report ----
  const files = parsed.map((p) => ({
    path: rel(p.file),
    sha256: createHash("sha256").update(p.text).digest("hex"),
    success: fileOk(p),
  }));

  const declarations = [];
  for (const p of mainFiles) {
    for (const d of p.decls) {
      if (!d.region) problems.push(`${rel(p.file)}:${d.line + 1}: ${d.name} is not inside a @region`);
      else if (!d.region.provenance) problems.push(`${rel(p.file)}: region ${d.region.id} has no @provenance`);
      const ok = fileOk(p);
      const axioms = ok && axiomsByName.has(d.name) ? axiomsByName.get(d.name) : [];
      let usesSorry;
      if (!ok) usesSorry = true; // not built: Lean's error recovery would have used sorryAx
      else if (d.kind === "example") usesSorry = d.sorryCount > 0; // examples have no name to #print
      else if (!axiomsByName.has(d.name)) usesSorry = true; // unknown, so be conservative
      else usesSorry = axioms.includes("sorryAx");
      if (ok && usesSorry) problems.push(`main-library declaration ${d.name} uses sorry`);
      declarations.push({
        name: d.name,
        kind: d.kind,
        file: rel(p.file),
        region: d.region ? d.region.id : null,
        usesSorry,
        axioms,
        // A missing @provenance is already reported as a problem; fall back to the weaker claim.
        provenance: d.region?.provenance ?? (d.kind === "theorem" ? "library" : "definition"),
      });
    }
  }

  const mainNames = new Set(declarations.map((d) => d.name));
  const exercises = [];
  for (const p of parsed.filter(isExercise)) {
    for (const d of p.decls) {
      const solution = d.region?.solution ?? null;
      if (d.region && !d.region.id.startsWith("ex.")) problems.push(`exercise region ${d.region.id} should start with "ex."`);
      if (solution === null) problems.push(`${rel(p.file)}:${d.line + 1}: exercise ${d.name} has no @solution`);
      else if (!mainNames.has(solution)) problems.push(`exercise ${d.name}: @solution ${solution} is not a main-library declaration`);
      exercises.push({
        file: rel(p.file),
        name: d.name,
        region: d.region ? d.region.id : null,
        elaborates: fileOk(p),
        sorryCount: d.sorryCount,
        solution,
      });
    }
  }

  // duplicate region ids across the project
  const seenRegions = new Map();
  for (const p of parsed)
    for (const r of p.regions) {
      if (seenRegions.has(r.id)) problems.push(`duplicate region id ${r.id} (${seenRegions.get(r.id)} and ${rel(p.file)})`);
      seenRegions.set(r.id, rel(p.file));
    }

  const report = {
    generatedAt: new Date().toISOString(),
    toolchain,
    leanVersion,
    mathlib: null,
    build: { command: BUILD_COMMAND, success: buildSuccess, durationMs },
    files,
    declarations,
    exercises,
  };

  fs.mkdirSync(path.dirname(REPORT_PATH), { recursive: true });
  fs.writeFileSync(REPORT_PATH, `${JSON.stringify(report, null, 2)}\n`);
  log(
    `wrote ${rel(REPORT_PATH)}: ${files.length} files, ${declarations.length} declarations, ` +
      `${exercises.length} exercises (${exercises.reduce((a, e) => a + e.sorryCount, 0)} sorry placeholders)`,
  );

  if (problems.length > 0) {
    console.error(`[verify-lean] ${problems.length} problem(s):`);
    for (const pr of problems) console.error(`  - ${pr}`);
    process.exit(1);
  }
  log("OK: build succeeded, no sorry in the main library, all regions well-formed.");
}

main();
