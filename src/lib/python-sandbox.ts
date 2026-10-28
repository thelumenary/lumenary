"use client";

/**
 * Runs learner Python in a dedicated Web Worker (Pyodide/WebAssembly).
 * Code never reaches a server. A run that exceeds its time limit is stopped
 * by terminating the worker, and a fresh worker is created for the next run.
 */
export const PYODIDE_VERSION = "0.29.3";

export interface RunResult {
  ok: boolean;
  stdout: string;
  stderr: string;
  error?: string;
  timedOut?: boolean;
  durationMs: number;
}

type Listener = (chunk: { stream: "stdout" | "stderr"; text: string }) => void;

let worker: Worker | null = null;
let ready: Promise<void> | null = null;
let seq = 0;

function spawn(): Promise<void> {
  worker = new Worker(`/workers/pyodide-worker.js?v=${PYODIDE_VERSION}`);
  ready = new Promise((resolve, reject) => {
    const w = worker!;
    const onMsg = (e: MessageEvent) => {
      if (e.data?.type === "ready") {
        w.removeEventListener("message", onMsg);
        resolve();
      } else if (e.data?.type === "init-error") {
        w.removeEventListener("message", onMsg);
        reject(new Error(e.data.error));
      }
    };
    w.addEventListener("message", onMsg);
    w.addEventListener("error", (err) => reject(new Error(err.message || "worker failed to start")));
  });
  return ready;
}

export function warmUp(): Promise<void> {
  if (!worker || !ready) return spawn();
  return ready;
}

export function stop() {
  worker?.terminate();
  worker = null;
  ready = null;
}

export async function runPython(code: string, opts: { tests?: string; timeoutMs?: number; onChunk?: Listener } = {}): Promise<RunResult> {
  const started = performance.now();
  await warmUp();
  const w = worker!;
  const id = ++seq;
  let stdout = "";
  let stderr = "";
  return new Promise<RunResult>((resolve) => {
    const timer = setTimeout(() => {
      w.removeEventListener("message", onMsg);
      stop();
      resolve({ ok: false, stdout, stderr, timedOut: true, durationMs: performance.now() - started });
    }, opts.timeoutMs ?? 15000);
    const onMsg = (e: MessageEvent) => {
      const msg = e.data;
      if (msg?.id !== id) return;
      if (msg.type === "stdout" || msg.type === "stderr") {
        if (msg.type === "stdout") stdout += msg.text + "\n";
        else stderr += msg.text + "\n";
        opts.onChunk?.({ stream: msg.type, text: msg.text });
      } else if (msg.type === "done") {
        clearTimeout(timer);
        w.removeEventListener("message", onMsg);
        resolve({ ok: msg.ok, stdout, stderr, error: msg.error, durationMs: performance.now() - started });
      }
    };
    w.addEventListener("message", onMsg);
    w.postMessage({ id, code, tests: opts.tests ?? null });
  });
}
