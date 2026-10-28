"use client";

import { Check, ChevronDown, Lightbulb, Loader2, Play, RotateCcw, Sparkles } from "lucide-react";
import { useId, useState } from "react";
import { useI18n } from "@/i18n/client";
import { recordAttempt } from "@/lib/progress";
import { runPython } from "@/lib/python-sandbox";
import { CodeEditor } from "@/components/python/CodeEditor";
import { parseInteger, parseSet, setKey, setsEqual, normalizeElement } from "./parse";
import type { RenderedExercise } from "./types";

type Verdict = { ok: boolean; html?: string; text?: string } | null;

const Html = ({ html, className = "" }: { html: string; className?: string }) => <div className={className} dangerouslySetInnerHTML={{ __html: html }} />;

const DIFF_STYLE = {
  "warm-up": "bg-good-soft text-good",
  core: "bg-sky-soft text-sky-ink",
  stretch: "bg-formal-soft text-formal",
} as const;

export function ExerciseCard({ exercise, index }: { exercise: RenderedExercise; index?: number }) {
  const { t } = useI18n();
  const uid = useId();
  const [hintsShown, setHintsShown] = useState(0);
  const [showSolution, setShowSolution] = useState(false);
  const [verdict, setVerdict] = useState<Verdict>(null);

  const report = (ok: boolean, detail?: { html?: string; text?: string }) => {
    setVerdict({ ok, ...detail });
    recordAttempt(exercise.id, ok);
  };

  return (
    <article id={`ex-${exercise.id}`} className="card overflow-hidden" data-mode={exercise.mode} aria-labelledby={`${uid}-title`}>
      <header className="flex flex-wrap items-center gap-2 border-b border-line bg-paper-2/50 px-5 py-3">
        <h3 id={`${uid}-title`} className="font-sans text-sm font-bold text-ink">
          {index !== undefined ? `${index + 1}. ` : ""}
          <span className="text-muted">{exercise.lessonTitle}</span>
        </h3>
        <span className={`rounded-full px-2 py-0.5 text-[0.7rem] font-bold uppercase tracking-wide ${DIFF_STYLE[exercise.difficulty]}`}>
          {t(`exercise.difficulty.${exercise.difficulty}`)}
        </span>
        <span className="ms-auto text-xs font-semibold text-muted">{t(`modes.${exercise.mode}`)}</span>
      </header>
      <div className="space-y-4 px-5 py-5">
        <Html html={exercise.promptHtml} className="prose-lumen text-[1.02rem]" />

        {exercise.type === "choice" && <ChoiceBody exercise={exercise} onResult={report} />}
        {exercise.type === "integer" && <IntegerBody exercise={exercise} onResult={report} />}
        {exercise.type === "set" && <SetBody exercise={exercise} onResult={report} />}
        {exercise.type === "python" && <PythonBody exercise={exercise} onResult={report} />}

        <div aria-live="polite">
          {verdict && (
            <div className={`flex gap-3 rounded-xl px-4 py-3 text-sm ${verdict.ok ? "bg-good-soft text-good" : "bg-warn-soft text-warn"}`}>
              {verdict.ok ? <Check size={18} className="mt-0.5 shrink-0" aria-hidden="true" /> : <Sparkles size={18} className="mt-0.5 shrink-0" aria-hidden="true" />}
              <div className="space-y-1">
                <p className="font-semibold">{verdict.ok ? t("exercise.correct") : t("exercise.notYet")}</p>
                {verdict.html && <Html html={verdict.html} className="text-ink-2 [&_p]:m-0" />}
                {verdict.text && (
                  <pre dir="ltr" className="whitespace-pre-wrap font-mono text-xs text-ink-2">
                    {verdict.text}
                  </pre>
                )}
              </div>
            </div>
          )}
        </div>

        {hintsShown > 0 && (
          <ol className="space-y-2">
            {exercise.hintsHtml.slice(0, hintsShown).map((h, i) => (
              <li key={i} className="flex gap-3 rounded-xl border border-gold/30 bg-gold-soft/60 px-4 py-3 text-sm animate-float-up">
                <Lightbulb size={16} className="mt-0.5 shrink-0 text-gold-ink" aria-hidden="true" />
                <div>
                  <p className="text-xs font-semibold text-gold-ink">{t("exercise.hintN", { n: i + 1, total: exercise.hintsHtml.length })}</p>
                  <Html html={h} className="text-ink [&_p]:m-0" />
                </div>
              </li>
            ))}
          </ol>
        )}

        <div className="flex flex-wrap gap-2">
          {hintsShown < exercise.hintsHtml.length && (
            <button type="button" className="btn btn-sm btn-ghost" onClick={() => setHintsShown((n) => n + 1)}>
              <Lightbulb size={14} aria-hidden="true" /> {hintsShown === 0 ? t("exercise.hint") : t("exercise.nextHint")}
            </button>
          )}
          <button type="button" className="btn btn-sm btn-ghost" aria-expanded={showSolution} onClick={() => setShowSolution((s) => !s)}>
            <ChevronDown size={14} className={`transition-transform ${showSolution ? "rotate-180" : ""}`} aria-hidden="true" />
            {showSolution ? t("exercise.hideSolution") : t("exercise.solution")}
          </button>
        </div>
        {showSolution && <Html html={exercise.solutionHtml} className="prose-lumen rounded-xl border border-line bg-paper-2/50 px-5 py-4 text-[1rem] animate-float-up" />}
      </div>
    </article>
  );
}

type OnResult = (ok: boolean, detail?: { html?: string; text?: string }) => void;

function ChoiceBody({ exercise, onResult }: { exercise: Extract<RenderedExercise, { type: "choice" }>; onResult: OnResult }) {
  const { t } = useI18n();
  const [picked, setPicked] = useState<string[]>([]);
  const name = useId();
  const toggle = (id: string) => setPicked((p) => (exercise.multiple ? (p.includes(id) ? p.filter((x) => x !== id) : [...p, id]) : [id]));
  const check = () => {
    const correct = exercise.options.filter((o) => o.correct).map((o) => o.id);
    const ok = correct.length === picked.length && correct.every((c) => picked.includes(c));
    const wrong = exercise.options.find((o) => picked.includes(o.id) && !o.correct);
    const chosen = exercise.options.find((o) => o.id === picked[0]);
    onResult(ok, { html: ok ? chosen?.feedbackHtml : (wrong ?? chosen)?.feedbackHtml });
  };
  return (
    <fieldset>
      <legend className="mb-2 text-xs font-semibold uppercase tracking-wide text-muted">{exercise.multiple ? t("exercise.chooseAll") : t("exercise.chooseOne")}</legend>
      <div className="grid gap-2">
        {exercise.options.map((o) => (
          <label
            key={o.id}
            className={`flex cursor-pointer items-start gap-3 rounded-xl border px-4 py-3 transition-colors ${
              picked.includes(o.id) ? "border-sky bg-sky-soft" : "border-line hover:border-line-2 hover:bg-paper-2/60"
            }`}
          >
            <input
              type={exercise.multiple ? "checkbox" : "radio"}
              name={name}
              className="mt-1 accent-[var(--sky)]"
              checked={picked.includes(o.id)}
              onChange={() => toggle(o.id)}
            />
            <span className="text-[0.98rem] text-ink" dangerouslySetInnerHTML={{ __html: o.labelHtml }} />
          </label>
        ))}
      </div>
      <button type="button" className="btn btn-primary btn-sm mt-3" disabled={picked.length === 0} onClick={check}>
        {t("exercise.check")}
      </button>
    </fieldset>
  );
}

function IntegerBody({ exercise, onResult }: { exercise: Extract<RenderedExercise, { type: "integer" }>; onResult: OnResult }) {
  const { t } = useI18n();
  const [value, setValue] = useState("");
  const id = useId();
  const check = () => {
    const n = parseInteger(value);
    if (n === null) return onResult(false, { text: t("exercise.parseError") });
    if (n === exercise.answer) return onResult(true);
    const fb = exercise.feedback.find((f) => parseInteger(f.match) === n);
    onResult(false, fb ? { html: fb.html } : undefined);
  };
  return (
    <form
      className="flex flex-wrap items-end gap-2"
      onSubmit={(e) => {
        e.preventDefault();
        check();
      }}
    >
      <label htmlFor={id} className="sr-only">
        {t("exercise.answerPlaceholder")}
      </label>
      <input id={id} className="input max-w-[14rem] font-mono" inputMode="numeric" dir="ltr" placeholder={t("exercise.integerPlaceholder")} value={value} onChange={(e) => setValue(e.target.value)} />
      <button type="submit" className="btn btn-primary btn-sm" disabled={!value.trim()}>
        {t("exercise.check")}
      </button>
    </form>
  );
}

function SetBody({ exercise, onResult }: { exercise: Extract<RenderedExercise, { type: "set" }>; onResult: OnResult }) {
  const { t } = useI18n();
  const [value, setValue] = useState("");
  const id = useId();
  const check = () => {
    const s = parseSet(value);
    if (!s) return onResult(false, { text: t("exercise.parseError") });
    const target = new Set(exercise.answer.map(normalizeElement));
    if (setsEqual(s, target)) return onResult(true);
    const fb = exercise.feedback.find((f) => {
      const m = parseSet(f.match);
      return m && setKey(m) === setKey(s);
    });
    onResult(false, fb ? { html: fb.html } : undefined);
  };
  return (
    <form
      className="space-y-1.5"
      onSubmit={(e) => {
        e.preventDefault();
        check();
      }}
    >
      <label htmlFor={id} className="sr-only">
        {t("exercise.answerPlaceholder")}
      </label>
      <div className="flex flex-wrap gap-2">
        <input id={id} className="input max-w-sm font-mono" dir="ltr" placeholder={t("exercise.setPlaceholder")} value={value} onChange={(e) => setValue(e.target.value)} />
        <button type="submit" className="btn btn-primary btn-sm" disabled={!value.trim()}>
          {t("exercise.check")}
        </button>
      </div>
      <p className="text-xs text-muted">{t("exercise.setHelp")}</p>
    </form>
  );
}

function PythonBody({ exercise, onResult }: { exercise: Extract<RenderedExercise, { type: "python" }>; onResult: OnResult }) {
  const { t } = useI18n();
  const [code, setCode] = useState(exercise.starter);
  const [busy, setBusy] = useState(false);
  const [out, setOut] = useState("");
  const run = async () => {
    setBusy(true);
    setOut("");
    try {
      const res = await runPython(code, { tests: exercise.tests, timeoutMs: 15000 });
      setOut(res.stdout.trim());
      if (res.ok) onResult(true, { text: t("exercise.allPassed") });
      else onResult(false, { text: res.timedOut ? t("python.timeout", { seconds: 15 }) : `${t("exercise.someFailed")}\n\n${res.error ?? ""}` });
    } catch {
      onResult(false, { text: t("python.offline") });
    }
    setBusy(false);
  };
  return (
    <div className="overflow-hidden rounded-xl border border-line bg-card">
      <CodeEditor value={code} onChange={setCode} label={t("python.edit")} minRows={8} />
      <div className="flex flex-wrap items-center gap-2 border-t border-line bg-paper-2/60 px-3 py-2.5">
        <button type="button" className="btn btn-sm bg-compute text-white" onClick={run} disabled={busy}>
          {busy ? <Loader2 size={14} className="animate-spin" aria-hidden="true" /> : <Play size={14} aria-hidden="true" />}
          {busy ? t("exercise.running") : t("exercise.runTests")}
        </button>
        <button type="button" className="btn btn-sm btn-ghost" onClick={() => setCode(exercise.starter)}>
          <RotateCcw size={13} aria-hidden="true" /> {t("exercise.reset")}
        </button>
        <span className="ms-auto text-xs text-muted">{t("python.sandbox")}</span>
      </div>
      {out && (
        <pre dir="ltr" className="whitespace-pre-wrap border-t border-line px-4 py-3 font-mono text-xs text-ink-2">
          {out}
        </pre>
      )}
    </div>
  );
}
