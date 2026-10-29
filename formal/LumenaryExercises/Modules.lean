/-
The Lumenary — Lean exercises: Modules (free modules and lifting).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Modules.lean`.
-/
import Lumenary.Modules

namespace LumenaryExercises.Modules

-- @region ex.modules.free_lifting
-- @solution Lumenary.Modules.free_lifting
/-- Maps out of a free module lift along surjections.
Hint: `choose m hm using fun i : ι => hg (f (Finsupp.single i 1))` picks preimages of the images
of the basis vectors; then use `Finsupp.linearCombination R m`, and check equality on basis
vectors with `ext i` followed by `simp [hm]`. -/
theorem free_lifting {R : Type*} [Ring R] {ι M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (f : (ι →₀ R) →ₗ[R] N) : ∃ h : (ι →₀ R) →ₗ[R] M, g ∘ₗ h = f := by
  sorry
-- @endregion

-- @region ex.modules.int_two_exact
-- @solution Lumenary.Modules.int_two_exact
/-- The sequence `ℤ --2·--> ℤ → ℤ/2` is exact in the middle.
Hint: `ZMod.intCast_zmod_eq_zero_iff_dvd` turns `(n : ZMod 2) = 0` into `2 ∣ n`. -/
theorem int_two_exact :
    Function.Exact (fun n : ℤ => 2 * n) (fun n : ℤ => (n : ZMod 2)) := by
  sorry
-- @endregion

end LumenaryExercises.Modules
