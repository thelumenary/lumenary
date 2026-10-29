/-
The Lumenary — formal mathematics
AI-assisted mathematical research: checking machine-found certificates.

What is proved here. A search program (see the lesson's Python experiment) proposed a colouring
of `{1, …, 13}` with three colours in which no colour class contains `x`, `y` and `x + y`; the
search is untrusted, and Lean's kernel checks the certificate by evaluation (`decide`). The
optimality claim for two colours (no such colouring of `{1, …, 5}`) is proved by a finite case
analysis. A Schur colouring of `{1, …, n}` is turned into an edge colouring of the complete graph
on `n + 1` vertices with no monochromatic triangle (proved here, `independent`), giving a 3-colouring
of the edges of `K₁₄` with no monochromatic triangle. Schur's theorem — every finite colouring of
the positive integers has a monochromatic solution of `x + y = z` — is deduced from Mathlib's
Hindman theorem (`library`). Not formalised: the exact Schur numbers `S(3) = 13`, `S(4) = 44` and
`S(5) = 160` (the last has a SAT certificate far too large for `decide`), the growth of
multicolour Ramsey numbers, and anything about the AI systems themselves.
-/
import Mathlib.Combinatorics.Hindman
import Mathlib.Data.PNat.Basic

namespace Lumenary.AiAssistedMathematics

/-! ### Schur colourings and a machine-found certificate -/

-- @region ai_assisted_mathematics.is_schur_colouring
-- @provenance definition
/-- A colouring `c` of `{1, …, n}` with `k` colours is a **Schur colouring** if no colour class
contains `x`, `y` and `x + y` (with `x = y` allowed). The quantifiers are bounded (`x < n + 1`)
so that, for a concrete `c`, Lean can decide the property by evaluation. It is an `abbrev` so
that `decide` can see through it. -/
abbrev IsSchurColouring {k : ℕ} (n : ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ x < n + 1, ∀ y < n + 1, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ n → ¬ (c x = c y ∧ c y = c (x + y))
-- @endregion

-- @region ai_assisted_mathematics.search_certificate
-- @provenance definition
/-- The certificate printed by the lesson's search experiment: the colour of `x` is entry `x` of
the list (entry `0` is unused). Colour classes: `{5, 6, 7, 8, 9}`, `{2, 3, 11, 12}` and
`{1, 4, 10, 13}`. -/
def searchCertificate (x : ℕ) : Fin 3 :=
  ([0, 2, 1, 1, 2, 0, 0, 0, 0, 0, 2, 1, 1, 2] : List (Fin 3)).getD x 0
-- @endregion

-- @region ai_assisted_mathematics.search_certificate_valid
-- @provenance independent
/-- **The kernel checks the certificate.** `decide` evaluates all `13 × 13` pairs `(x, y)`. The
search that produced the colouring is not trusted at all: only this check is. It proves the
lower bound `S(3) ≥ 13` for the Schur number. -/
theorem searchCertificate_valid : IsSchurColouring 13 searchCertificate := by
  decide
-- @endregion

-- @region ai_assisted_mathematics.pentagon_colouring
-- @provenance definition
/-- The Schur 2-colouring of `{1, 2, 3, 4}` with classes `{1, 4}` and `{2, 3}`. -/
def pentagonColouring (x : ℕ) : Fin 2 :=
  ([0, 0, 1, 1, 0] : List (Fin 2)).getD x 0
-- @endregion

-- @region ai_assisted_mathematics.pentagon_colouring_valid
-- @provenance independent
/-- The 2-colouring `{1, 4}`, `{2, 3}` is a Schur colouring, checked by `decide`: `S(2) ≥ 4`. -/
theorem pentagonColouring_valid : IsSchurColouring 4 pentagonColouring := by
  decide
-- @endregion

/-! ### Optimality is a different kind of claim -/

-- @region ai_assisted_mathematics.schur_two_optimal
-- @provenance independent
/-- **No Schur 2-colouring of `{1, …, 5}` exists**, so `S(2) = 4`. A construction is checked by
looking at one object; this claim is about *every* colouring. Only the colours of `1, …, 5`
matter, so it reduces to a statement about the `2⁵ = 32` colour patterns, which `decide`
checks. The five equations used are `1 + 1 = 2`, `2 + 2 = 4`, `1 + 3 = 4`, `1 + 4 = 5`,
`2 + 3 = 5`. -/
theorem schur_two_optimal (c : ℕ → Fin 2) : ¬ IsSchurColouring 5 c := by
  intro h
  have key : ∀ a b d e f : Fin 2,
      (a = a ∧ a = b) ∨ (b = b ∧ b = e) ∨ (a = d ∧ d = e) ∨ (a = e ∧ e = f) ∨
        (b = d ∧ d = f) := by
    decide
  rcases key (c 1) (c 2) (c 3) (c 4) (c 5) with h1 | h2 | h3 | h4 | h5
  · exact h 1 (by decide) 1 (by decide) (by decide) h1
  · exact h 2 (by decide) 2 (by decide) (by decide) h2
  · exact h 1 (by decide) 3 (by decide) (by decide) h3
  · exact h 1 (by decide) 4 (by decide) (by decide) h4
  · exact h 2 (by decide) 3 (by decide) (by decide) h5
-- @endregion

/-! ### From Schur colourings to Ramsey colourings -/

-- @region ai_assisted_mathematics.has_triangle_free_colouring
-- @provenance definition
/-- `HasTriangleFreeColouring k m`: the edges of the complete graph on the vertices
`0, 1, …, m − 1` can be coloured with `k` colours so that no triangle has all three edges the
same colour. The edge `{i, j}` with `i < j` gets colour `c i j`. The multicolour Ramsey number
`R(3; k)` is the least `m` for which this fails; Erdős problem #183 asks how fast it grows. -/
def HasTriangleFreeColouring (k m : ℕ) : Prop :=
  ∃ c : ℕ → ℕ → Fin k, ∀ i j l : ℕ, i < j → j < l → l < m →
    ¬ (c i j = c j l ∧ c j l = c i l)
-- @endregion

-- @region ai_assisted_mathematics.has_triangle_free_colouring_of_schur
-- @provenance independent
/-- **Schur colourings give Ramsey colourings.** Colour the edge `{i, j}` (`i < j`) by the colour
of `j − i`. A triangle `i < j < l` has edge colours `c (j − i)`, `c (l − j)` and `c (l − i)`, and
`(j − i) + (l − j) = l − i`; so a monochromatic triangle would be a monochromatic solution of
`x + y = z`. Hence `R(3; k) ≥ S(k) + 2`. -/
theorem hasTriangleFreeColouring_of_schur {k n : ℕ} {c : ℕ → Fin k}
    (hc : IsSchurColouring n c) : HasTriangleFreeColouring k (n + 1) := by
  refine ⟨fun i j => c (j - i), fun i j l hij hjl hl => ?_⟩
  have hsum : j - i + (l - j) = l - i := by omega
  have := hc (j - i) (by omega) (l - j) (by omega) ⟨by omega, by omega, by omega⟩
  rw [hsum] at this
  exact this
-- @endregion

-- @region ai_assisted_mathematics.three_colours_fourteen_vertices
-- @provenance independent
/-- **A certified Ramsey lower bound**: the edges of `K₁₄` can be 3-coloured with no
monochromatic triangle, so `R(3; 3) ≥ 15`. (The true value is `17`, by Greenwood and Gleason,
1955: this certificate proves a true but non-optimal bound.) -/
theorem three_colours_fourteen_vertices : HasTriangleFreeColouring 3 14 :=
  hasTriangleFreeColouring_of_schur searchCertificate_valid
-- @endregion

/-! ### Schur's theorem, from Mathlib -/

-- @region ai_assisted_mathematics.schur_theorem
-- @provenance library
/-- **Schur's theorem** (1916): however the positive integers are coloured with finitely many
colours, some colour class contains `x`, `y` and `x + y`. So Schur numbers are finite, and every
search for colourings must eventually fail. Deduced from Mathlib's much stronger **Hindman
theorem** (`Hindman.exists_FS_of_finite_cover`: one colour class contains all finite sums of
some sequence), applied to the cover of `ℕ+` by the colour classes, with `FS.singleton` and
`FS.add_two`. -/
theorem schur_theorem (k : ℕ) (c : ℕ+ → Fin k) : ∃ x y : ℕ+, c x = c y ∧ c y = c (x + y) := by
  obtain ⟨C, ⟨i, rfl⟩, a, ha⟩ := Hindman.exists_FS_of_finite_cover
    (Set.range fun i : Fin k => c ⁻¹' {i}) (Set.finite_range _)
    (fun m _ => Set.mem_sUnion.2 ⟨c ⁻¹' {c m}, ⟨c m, rfl⟩, rfl⟩)
  have h0 := ha _ (Hindman.FS.singleton a 0)
  have h1 := ha _ (Hindman.FS.singleton a 1)
  have h01 := ha _ (Hindman.FS.add_two a 0 1 Nat.zero_lt_one)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h0 h1 h01
  exact ⟨a.get 0, a.get 1, h0.trans h1.symm, h1.trans h01.symm⟩
-- @endregion

end Lumenary.AiAssistedMathematics
