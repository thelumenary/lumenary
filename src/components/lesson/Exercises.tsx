import { ExerciseCard } from "@/components/exercises/ExerciseCard";
import type { RenderedExercise } from "@/components/exercises/types";

export function ExerciseList({ exercises }: { exercises: RenderedExercise[] }) {
  return (
    <div className="not-prose !mt-6 space-y-5 font-sans">
      {exercises.map((ex, i) => (
        <ExerciseCard key={ex.id} exercise={ex} index={i} />
      ))}
    </div>
  );
}
