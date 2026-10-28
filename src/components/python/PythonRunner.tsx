"use client";

import { Loader2, Pencil, Play, RotateCcw, Square } from "lucide-react";
import { useState } from "react";
import { useI18n } from "@/i18n/client";
import { runPython, stop, type RunResult } from "@/lib/python-sandbox";
import { CodeEditor } from "./CodeEditor";

type Phase = "idle" | "loading" | "running" | "done";

/**
 * Shows server-highlighted source; "Edit" swaps in an editable textarea.
 * "Run" executes the current code in the sandboxed Pyodide worker.
 */
export function PythonRunner({ code, highlighted, timeoutSeconds = 20 }: { code: string; highlighted: React.ReactNode; timeoutSeconds?: number }) {
  const { t } = useI18n();
  const [editing, setEditing] = useState(false);
  const [source, setSource] = useState(code);
  const [phase, setPhase] = useState<Phase>("idle");
  const [result, setResult] = useState<RunResult | null>(null);
  const [live, setLive] = useState("");
  const [loadFailed, setLoadFailed] = useState(false);

  const run = async () => {
    setResult(null);
    setLive("");
    setLoadFailed(false);
    setPhase("loading");
    try {
      const res = await runPython(source, {
        timeoutMs: timeoutSeconds * 1000,
        onChunk: (c) => {
          setPhase("running");
          setLive((prev) => prev + c.text + "\n");
        },
      });
      setResult(res);
    } catch {
      setLoadFailed(true);
    }
    setPhase("done");
  };

  const busy = phase === "loading" || phase === "running";
  return (
    <div>
      <div className="code-frame max-h-[32rem] overflow-auto">{editing ? <CodeEditor value={source} onChange={setSource} label={t("python.edit")} /> : highlighted}</div>
      <div className="flex flex-wrap items-center gap-2 border-t border-line bg-paper-2/60 px-3 py-2.5">
        {!busy ? (
          <button type="button" className="btn btn-sm bg-compute text-white hover:opacity-90" onClick={run}>
            <Play size={14} aria-hidden="true" /> {result ? t("python.rerun") : t("python.run")}
          </button>
        ) : (
          <button
            type="button"
            className="btn btn-sm btn-ghost"
            onClick={() => {
              stop();
              setPhase("done");
            }}
          >
            <Square size={13} aria-hidden="true" /> {t("python.stop")}
          </button>
        )}
        {!editing ? (
          <button type="button" className="btn btn-sm btn-ghost" onClick={() => setEditing(true)}>
            <Pencil size={13} aria-hidden="true" /> {t("python.edit")}
          </button>
        ) : (
          <button
            type="button"
            className="btn btn-sm btn-ghost"
            onClick={() => {
              setSource(code);
              setEditing(false);
            }}
          >
            <RotateCcw size={13} aria-hidden="true" /> {t("exercise.reset")}
          </button>
        )}
        <span className="ms-auto text-xs text-muted">{t("python.sandbox")}</span>
      </div>
      {(phase !== "idle" || result) && (
        <div className="border-t border-line bg-ink/[0.03] px-4 py-3" aria-live="polite">
          <div className="mb-1.5 flex items-center gap-2 text-xs font-semibold uppercase tracking-wider text-muted">
            {busy && <Loader2 size={13} className="animate-spin" aria-hidden="true" />}
            {phase === "loading" ? t("python.loading") : phase === "running" ? t("python.running") : t("python.output")}
          </div>
          {loadFailed && <p className="text-sm text-bad">{t("python.offline")}</p>}
          <pre dir="ltr" className="max-h-96 overflow-auto whitespace-pre-wrap font-mono text-[0.8rem] leading-relaxed text-ink">
            {result ? result.stdout || (result.ok ? t("python.noOutput") : "") : live}
          </pre>
          {result?.stderr && <pre dir="ltr" className="mt-2 whitespace-pre-wrap font-mono text-[0.78rem] text-warn">{result.stderr}</pre>}
          {result && !result.ok && !result.timedOut && result.error && (
            <div className="mt-2 rounded-lg bg-bad-soft px-3 py-2">
              <p className="text-xs font-semibold text-bad">{t("python.error")}</p>
              <pre dir="ltr" className="mt-1 whitespace-pre-wrap font-mono text-[0.78rem] text-bad">{result.error}</pre>
            </div>
          )}
          {result?.timedOut && <p className="mt-2 text-sm text-warn">{t("python.timeout", { seconds: timeoutSeconds })}</p>}
        </div>
      )}
    </div>
  );
}
