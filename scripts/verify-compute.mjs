#!/usr/bin/env node
/**
 * Thin wrapper around compute/verify.py (run by `npm run verify:compute`).
 *
 * Uses the project virtualenv at compute/.venv when it exists, otherwise falls
 * back to `python3` (or `python` on Windows) on PATH. All work - running the
 * experiments, running pytest and writing content/verification/compute-report.json
 * - happens in verify.py; this script only forwards arguments and the exit code.
 *
 * Set LUMENARY_PYTHON to force a specific interpreter.
 */
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const computeDir = path.join(repoRoot, "compute");
const verifyScript = path.join(computeDir, "verify.py");

function findPython() {
  if (process.env.LUMENARY_PYTHON) return { python: process.env.LUMENARY_PYTHON, fromVenv: false };
  const candidates =
    process.platform === "win32"
      ? [path.join(computeDir, ".venv", "Scripts", "python.exe")]
      : [path.join(computeDir, ".venv", "bin", "python"), path.join(computeDir, ".venv", "bin", "python3")];
  for (const candidate of candidates) {
    if (existsSync(candidate)) return { python: candidate, fromVenv: true };
  }
  return { python: process.platform === "win32" ? "python" : "python3", fromVenv: false };
}

const { python, fromVenv } = findPython();
if (!fromVenv && !process.env.LUMENARY_PYTHON) {
  console.warn(
    `verify-compute: compute/.venv not found; falling back to "${python}" on PATH.\n` +
      "  Versions may not match the pinned ones. To create the venv:\n" +
      "    python3 -m venv compute/.venv && compute/.venv/bin/python -m pip install -r compute/requirements.txt",
  );
}

const result = spawnSync(python, [verifyScript, ...process.argv.slice(2)], {
  cwd: repoRoot,
  stdio: "inherit",
});

if (result.error) {
  console.error(`verify-compute: could not start ${python}: ${result.error.message}`);
  process.exit(1);
}
if (result.signal) {
  console.error(`verify-compute: verify.py was terminated by ${result.signal}`);
  process.exit(1);
}
process.exit(result.status ?? 1);
