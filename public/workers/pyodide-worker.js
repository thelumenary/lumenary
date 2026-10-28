/* The Lumenary — Python sandbox worker.
 * Loads Pyodide (CPython compiled to WebAssembly) from a pinned CDN version and
 * executes code in an isolated namespace. The main thread enforces time limits
 * by terminating this worker. No network access is used by learner code paths
 * beyond fetching Pyodide packages (sympy, numpy) on demand. */
const VERSION = "0.29.3";
const INDEX = `https://cdn.jsdelivr.net/pyodide/v${VERSION}/full/`;

let pyodide = null;

async function init() {
  try {
    importScripts(INDEX + "pyodide.js");
    pyodide = await loadPyodide({ indexURL: INDEX });
    self.postMessage({ type: "ready" });
  } catch (err) {
    self.postMessage({ type: "init-error", error: String((err && err.message) || err) });
  }
}

function cleanError(err) {
  const text = String((err && err.message) || err);
  // Keep the learner-relevant tail of the traceback, drop Pyodide internals.
  const lines = text.split("\n");
  const start = lines.findIndex((l) => l.includes('File "<exec>"'));
  const kept = start >= 0 ? lines.slice(start) : lines.slice(-6);
  return kept.join("\n").trim();
}

const initPromise = init();

self.onmessage = async (event) => {
  const { id, code, tests } = event.data || {};
  await initPromise;
  if (!pyodide) {
    self.postMessage({ id, type: "done", ok: false, error: "Python failed to load." });
    return;
  }
  pyodide.setStdout({ batched: (text) => self.postMessage({ id, type: "stdout", text }) });
  pyodide.setStderr({ batched: (text) => self.postMessage({ id, type: "stderr", text }) });
  let ns = null;
  try {
    await pyodide.loadPackagesFromImports(code + "\n" + (tests || ""));
    ns = pyodide.globals.get("dict")();
    ns.set("__name__", "__main__");
    await pyodide.runPythonAsync(code, { globals: ns });
    if (tests) await pyodide.runPythonAsync(tests, { globals: ns });
    self.postMessage({ id, type: "done", ok: true });
  } catch (err) {
    self.postMessage({ id, type: "done", ok: false, error: cleanError(err) });
  } finally {
    if (ns) ns.destroy();
  }
};
