/-
The Lumenary — Lean exercises: AI-assisted mathematical research.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/AiAssistedMathematics.lean`.
-/
import Lumenary.AiAssistedMathematics

namespace LumenaryExercises.AiAssistedMathematics

open Lumenary.AiAssistedMathematics

-- @region ex.ai_assisted_mathematics.pentagon_colouring_valid
-- @solution Lumenary.AiAssistedMathematics.pentagonColouring_valid
/-- Check the certificate: the 2-colouring with classes `{1, 4}` and `{2, 3}` is a Schur
colouring of `{1, 2, 3, 4}`.
Hint: the property is a bounded check of finitely many cases. Which tactic asks the kernel to
evaluate it? -/
theorem pentagonColouring_valid : IsSchurColouring 4 pentagonColouring := by
  sorry
-- @endregion

-- @region ex.ai_assisted_mathematics.has_triangle_free_colouring_of_schur
-- @solution Lumenary.AiAssistedMathematics.hasTriangleFreeColouring_of_schur
/-- Turn a Schur colouring of `{1, …, n}` with `k` colours into a `k`-colouring of the edges of
the complete graph on `0, …, n` with no monochromatic triangle.
Hint: colour the edge `{i, j}` by `c (j - i)`, apply `hc` to `x = j - i` and `y = l - j`, and
use `omega` to show `(j - i) + (l - j) = l - i`. -/
theorem hasTriangleFreeColouring_of_schur {k n : ℕ} {c : ℕ → Fin k}
    (hc : IsSchurColouring n c) : HasTriangleFreeColouring k (n + 1) := by
  sorry
-- @endregion

end LumenaryExercises.AiAssistedMathematics
