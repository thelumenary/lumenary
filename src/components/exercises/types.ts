/** Exercise data after server-side rendering of markdown/maths to HTML. */
export interface RenderedFeedback {
  match: string;
  html: string;
}
interface Base {
  id: string;
  lesson: string;
  lessonTitle: string;
  difficulty: "warm-up" | "core" | "stretch";
  mode: "H" | "F" | "C";
  promptHtml: string;
  hintsHtml: string[];
  solutionHtml: string;
}
export type RenderedExercise =
  | (Base & { type: "choice"; multiple: boolean; options: { id: string; labelHtml: string; correct: boolean; feedbackHtml: string }[] })
  | (Base & { type: "integer"; answer: number; feedback: RenderedFeedback[] })
  | (Base & { type: "set"; answer: string[]; feedback: RenderedFeedback[] })
  | (Base & { type: "python"; starter: string; tests: string });
