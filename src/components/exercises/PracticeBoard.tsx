"use client";

import { CheckCircle2, Circle, CircleDot } from "lucide-react";
import { useMemo, useState } from "react";
import { useI18n } from "@/i18n/client";
import { useProgress } from "@/lib/progress";
import { ExerciseCard } from "./ExerciseCard";
import type { RenderedExercise } from "./types";

export function PracticeBoard({ exercises, lessons }: { exercises: RenderedExercise[]; lessons: { slug: string; title: string }[] }) {
  const { t } = useI18n();
  const { enabled, store } = useProgress();
  const [lesson, setLesson] = useState("");
  const [mode, setMode] = useState("");
  const [difficulty, setDifficulty] = useState("");
  const list = useMemo(
    () => exercises.filter((e) => (!lesson || e.lesson === lesson) && (!mode || e.mode === mode) && (!difficulty || e.difficulty === difficulty)),
    [exercises, lesson, mode, difficulty],
  );
  const pill = (active: boolean) => `rounded-full px-3 py-1.5 text-sm font-semibold ${active ? "bg-ink text-paper" : "bg-card text-ink-2 border border-line hover:bg-paper-2"}`;

  return (
    <div className="grid gap-8 lg:grid-cols-[16rem_1fr]">
      <aside className="space-y-6 lg:sticky lg:top-24 lg:self-start">
        <div>
          <p className="eyebrow mb-2">{t("practice.byLesson")}</p>
          <div className="flex flex-wrap gap-1.5 lg:flex-col lg:items-stretch">
            <button type="button" className={pill(lesson === "")} onClick={() => setLesson("")}>
              {t("practice.all")}
            </button>
            {lessons.map((l) => {
              const ids = exercises.filter((e) => e.lesson === l.slug).map((e) => e.id);
              const solved = ids.filter((id) => store.exercises[id]?.solved).length;
              return (
                <button key={l.slug} type="button" className={`${pill(lesson === l.slug)} flex items-center justify-between gap-2 text-start`} onClick={() => setLesson(l.slug)}>
                  {l.title}
                  {enabled && (
                    <span className="text-xs opacity-75">
                      {solved}/{ids.length}
                    </span>
                  )}
                </button>
              );
            })}
          </div>
        </div>
        <div>
          <p className="eyebrow mb-2">{t("practice.filter")}</p>
          <div className="flex flex-wrap gap-1.5">
            {["", "H", "F", "C"].map((m) => (
              <button key={m || "all"} type="button" className={pill(mode === m)} onClick={() => setMode(m)}>
                {m ? t(`modes.${m}`) : t("modes.all")}
              </button>
            ))}
          </div>
          <div className="mt-2 flex flex-wrap gap-1.5">
            {["", "warm-up", "core", "stretch"].map((d) => (
              <button key={d || "all"} type="button" className={pill(difficulty === d)} onClick={() => setDifficulty(d)}>
                {d ? t(`exercise.difficulty.${d}`) : t("practice.all")}
              </button>
            ))}
          </div>
        </div>
        <p className="text-xs leading-relaxed text-muted">{t("progress.noRankings")}</p>
      </aside>
      <div className="space-y-5">
        {list.map((ex) => {
          const rec = store.exercises[ex.id];
          return (
            <div key={ex.id} className="relative">
              {enabled && (
                <span className="absolute -start-7 top-4 hidden text-muted lg:block" title={rec?.solved ? t("practice.solved") : rec ? t("practice.attempted") : ""}>
                  {rec?.solved ? <CheckCircle2 size={18} className="text-good" /> : rec ? <CircleDot size={18} /> : <Circle size={18} className="opacity-40" />}
                </span>
              )}
              <ExerciseCard exercise={ex} />
            </div>
          );
        })}
      </div>
    </div>
  );
}
