/-
The Lumenary — formal mathematics
Metric spaces and point-set topology: open balls, ε–δ continuity versus open-set continuity,
compactness and connectedness under continuous maps, Heine–Borel, Tychonoff, clopen sets in `ℚ`,
and why a continuous bijection need not be a homeomorphism.

What is proved here and what Mathlib provides. Mathlib defines topology through open sets
(`TopologicalSpace`, `IsOpen`), compactness through filters (`IsCompact`), and connectedness
through open covers (`IsPreconnected`); every metric space carries the topology of its open
balls. The *independent* declarations below re-prove lesson results from the definitions,
mirroring the human proofs: open balls are open (the triangle inequality), ε–δ continuity is
equivalent to "preimages of open sets are open", continuous images of compact and of connected
sets are compact and connected (by pulling covers back), the set `{x ∈ ℚ | x² < 2}` is open and
closed in `ℚ` (so `ℚ` is not connected), and `[0, 1)` is not homeomorphic to the circle. The
*library* declarations cite Mathlib's ε–δ characterisation, Heine–Borel, the extreme value
theorem, the connectedness of `[0, 1]`, Tychonoff's theorem, the universal property of quotient
topologies and the compactness of the circle `ℝ/ℤ`.
-/
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Lumenary.PointSetTopology

open Set

/-! ### Metric spaces: open balls and continuity -/

-- @region point_set_topology.ball_is_open
-- @provenance independent
/-- **Open balls are open.** If `y` lies in the ball `B(x, r)`, then the smaller ball of radius
`r - d(y, x)` around `y` stays inside `B(x, r)`: for `z` in it, the triangle inequality gives
`d(z, x) ≤ d(z, y) + d(y, x) < (r - d(y, x)) + d(y, x) = r`. -/
theorem ball_isOpen {X : Type*} [MetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  rw [Metric.isOpen_iff]
  intro y hy
  have hy' : dist y x < r := hy
  refine ⟨r - dist y x, sub_pos.mpr hy', fun z hz => ?_⟩
  have hz' : dist z y < r - dist y x := hz
  show dist z x < r
  calc dist z x ≤ dist z y + dist y x := dist_triangle z y x
    _ < (r - dist y x) + dist y x := by linarith
    _ = r := by ring
-- @endregion

-- @region point_set_topology.continuous_iff_eps_delta
-- @provenance library
/-- Mathlib's notion of continuity (preimages of open sets are open) agrees with the ε–δ
definition between metric spaces. This applies Mathlib's `Metric.continuous_iff`; compare
`eps_delta_iff_isOpen_preimage`, which proves the same equivalence from the definitions. -/
theorem continuous_iff_eps_delta {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε :=
  Metric.continuous_iff
-- @endregion

-- @region point_set_topology.eps_delta_iff_is_open_preimage
-- @provenance independent
/-- **ε–δ continuity is open-set continuity.** For a map between metric spaces, the ε–δ condition
at every point holds exactly when the preimage of every open set is open.

(⇒) If `U` is open and `f x ∈ U`, some ball `B(f x, ε)` lies in `U`; the δ for this ε gives a
ball `B(x, δ)` inside `f⁻¹(U)`. (⇐) The ball `B(f x, ε)` is open (`ball_isOpen`), so its preimage
is an open set containing `x`, hence contains some ball `B(x, δ)` — which is the ε–δ condition. -/
theorem eps_delta_iff_isOpen_preimage {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    (∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε) ↔
      ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  constructor
  · intro h U hU
    rw [Metric.isOpen_iff] at hU ⊢
    intro x hx
    obtain ⟨ε, hε, hball⟩ := hU (f x) hx
    obtain ⟨δ, hδ, hfx⟩ := h x ε hε
    exact ⟨δ, hδ, fun y hy => hball (hfx y hy)⟩
  · intro h x ε hε
    have hopen : IsOpen (f ⁻¹' Metric.ball (f x) ε) := h _ (ball_isOpen (f x) ε)
    rw [Metric.isOpen_iff] at hopen
    have hx : x ∈ f ⁻¹' Metric.ball (f x) ε := by
      show dist (f x) (f x) < ε
      rw [dist_self]
      exact hε
    obtain ⟨δ, hδ, hsub⟩ := hopen x hx
    exact ⟨δ, hδ, fun y hy => hsub hy⟩
-- @endregion

/-! ### Compactness and connectedness are preserved by continuous maps -/

-- @region point_set_topology.is_compact_image
-- @provenance independent
/-- **The continuous image of a compact set is compact.** Given an open cover `(Uᵢ)` of `f(K)`,
the preimages `f⁻¹(Uᵢ)` are open (continuity) and cover `K`; compactness of `K` picks finitely
many of them, and the corresponding `Uᵢ` cover `f(K)`. Compactness is used in the open-cover form
(`IsCompact.elim_finite_subcover`, `isCompact_of_finite_subcover`). -/
theorem isCompact_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) : IsCompact (f '' K) := by
  apply isCompact_of_finite_subcover
  intro ι U hUo hcover
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i => f ⁻¹' U i)
    (fun i => (hUo i).preimage hf)
    (fun x hx => by simpa using hcover ⟨x, hx, rfl⟩)
  refine ⟨t, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa using ht hx
-- @endregion

-- @region point_set_topology.is_preconnected_image
-- @provenance independent
/-- **The continuous image of a connected set is connected.** Mathlib's `IsPreconnected s` says:
whenever two open sets `u`, `v` together cover `s` and each meets `s`, they meet each other inside
`s`. If `u`, `v` split `f(s)` like this, then `f⁻¹(u)` and `f⁻¹(v)` are open, cover `s` and each
meets `s`; so some `z ∈ s` lies in both, and `f z` lies in `f(s) ∩ u ∩ v`. -/
theorem isPreconnected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsPreconnected s) {f : X → Y} (hf : Continuous f) :
    IsPreconnected (f '' s) := by
  intro u v hu hv hcover ⟨_, ⟨x, hx, rfl⟩, hxu⟩ ⟨_, ⟨y, hy, rfl⟩, hyv⟩
  obtain ⟨z, hzs, hzu, hzv⟩ := hs (f ⁻¹' u) (f ⁻¹' v) (hu.preimage hf) (hv.preimage hf)
    (fun z hz => hcover ⟨z, hz, rfl⟩) ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
  exact ⟨f z, ⟨z, hzs, rfl⟩, hzu, hzv⟩
-- @endregion

-- @region point_set_topology.unit_interval_is_connected
-- @provenance library
/-- **The interval `[0, 1]` is connected.** This applies Mathlib's `isConnected_Icc`, whose proof
uses the completeness of `ℝ` (a least upper bound argument), as in the lesson. -/
theorem unitInterval_isConnected : IsConnected (Icc (0 : ℝ) 1) :=
  isConnected_Icc zero_le_one
-- @endregion

-- @region point_set_topology.heine_borel
-- @provenance library
/-- **Heine–Borel.** A subset of Euclidean space `ℝⁿ` is compact if and only if it is closed and
bounded. This applies Mathlib's `Metric.isCompact_iff_isClosed_bounded`, which holds in every
*proper* metric space (closed balls compact); `ℝⁿ` is proper because it is finite-dimensional. -/
theorem heine_borel {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K :=
  Metric.isCompact_iff_isClosed_bounded
-- @endregion

-- @region point_set_topology.exists_max_on_compact
-- @provenance library
/-- **Extreme value theorem.** A continuous real-valued function on a non-empty compact set attains
a maximum. This applies Mathlib's `IsCompact.exists_isMaxOn`. -/
theorem exists_max_on_compact {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hf
  exact ⟨x, hx, fun y hy => isMaxOn_iff.mp hmax y hy⟩
-- @endregion

-- @region point_set_topology.tychonoff
-- @provenance library
/-- **Tychonoff's theorem.** A product of compact sets — any number of them — is compact in the
product topology. This applies Mathlib's `isCompact_univ_pi`, which is proved with ultrafilters
(and so uses the axiom of choice, as it must). -/
theorem tychonoff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {K : ∀ i, Set (X i)} (hK : ∀ i, IsCompact (K i)) : IsCompact (Set.pi univ K) :=
  isCompact_univ_pi hK
-- @endregion

/-! ### Clopen sets: `ℚ` falls apart -/

-- @region point_set_topology.no_rat_sq_eq_two
-- @provenance independent
/-- No rational number squares to `2`. If `x * x = 2` with `x ∈ ℚ`, then `√2 = |x|` would be
rational, contradicting Mathlib's `irrational_sqrt_two`. -/
theorem no_rat_sq_eq_two (x : ℚ) : x * x ≠ 2 := by
  intro h
  apply irrational_sqrt_two
  refine ⟨|x|, ?_⟩
  have hx : ((x : ℝ)) ^ 2 = 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at this
    nlinarith [this]
  rw [Rat.cast_abs, ← hx, Real.sqrt_sq_eq_abs]
-- @endregion

-- @region point_set_topology.rat_clopen
-- @provenance independent
/-- **A set that is both open and closed.** In `ℚ`, the set `S = {x | x² < 2}` is open (the
preimage of `(-∞, 2)` under the continuous map `x ↦ x²`) and also closed: since no rational
squares to `2`, `S = {x | x² ≤ 2}`, the preimage of the closed set `(-∞, 2]`. -/
theorem rat_clopen : IsClopen {x : ℚ | x * x < 2} := by
  have hcont : Continuous fun x : ℚ => x * x := continuous_id.mul continuous_id
  have hS : {x : ℚ | x * x < 2} = {x : ℚ | x * x ≤ 2} := by
    ext x
    show x * x < 2 ↔ x * x ≤ 2
    exact ⟨le_of_lt, fun hle => lt_of_le_of_ne hle (no_rat_sq_eq_two x)⟩
  refine ⟨?_, isOpen_lt hcont continuous_const⟩
  rw [hS]
  exact isClosed_le hcont continuous_const
-- @endregion

-- @region point_set_topology.rat_not_preconnected
-- @provenance independent
/-- **`ℚ` is not connected.** In a connected space the only clopen sets are `∅` and the whole
space (Mathlib's `isClopen_iff`). The clopen set `{x | x² < 2}` contains `0` but not `2`, so it is
neither. -/
theorem rat_not_preconnected : ¬ PreconnectedSpace ℚ := by
  intro h
  rcases isClopen_iff.mp rat_clopen with hempty | huniv
  · have h0 : (0 : ℚ) ∈ {x : ℚ | x * x < 2} := by norm_num
    rw [hempty] at h0
    exact h0
  · have h2 : (2 : ℚ) ∈ {x : ℚ | x * x < 2} := by rw [huniv]; trivial
    norm_num at h2
-- @endregion

/-! ### Homeomorphisms -/

-- @region point_set_topology.ico_not_homeomorphic_circle
-- @provenance independent
/-- **`[0, 1)` is not homeomorphic to the circle.** The circle (the unit sphere in `ℝ²`) is
compact (Heine–Borel), and a homeomorphism carries compact spaces to compact spaces; but `[0, 1)`
is not compact, because it is not closed in `ℝ` (Mathlib's `isCompact_Ico_iff`). In particular the
continuous bijection `t ↦ (cos 2πt, sin 2πt)` from `[0, 1)` onto the circle is not a
homeomorphism: its inverse is not continuous. -/
theorem ico_not_homeomorphic_circle :
    IsEmpty (Ico (0 : ℝ) 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  refine ⟨fun h => ?_⟩
  have : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have : CompactSpace (Ico (0 : ℝ) 1) := h.symm.compactSpace
  have hK : IsCompact (Ico (0 : ℝ) 1) := isCompact_iff_compactSpace.mpr inferInstance
  have := isCompact_Ico_iff.mp hK
  norm_num at this
-- @endregion

/-! ### Quotients: gluing the ends of an interval -/

-- @region point_set_topology.quotient_lift_continuous
-- @provenance library
/-- **The universal property of the quotient topology.** If `f : X → Y` is continuous and takes
equal values on equivalent points, the induced map on the quotient `X/∼` is continuous. (The
quotient topology is the finest topology making the projection `X → X/∼` continuous.) This
applies Mathlib's `Continuous.quotient_lift`. -/
theorem quotient_lift_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Setoid X) {f : X → Y} (hf : Continuous f) (h : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f h : Quotient s → Y) :=
  hf.quotient_lift h
-- @endregion

-- @region point_set_topology.add_circle_compact
-- @provenance library
/-- **The circle `ℝ/ℤ` is compact.** Mathlib's `AddCircle 1` is the quotient of `ℝ` by the
subgroup `ℤ`, with the quotient topology. It is compact because it is the image of the compact
interval `[0, 1]` under the continuous projection — the lesson's argument. This applies Mathlib's
instance `AddCircle.compactSpace`. -/
theorem addCircle_compact : CompactSpace (AddCircle (1 : ℝ)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  infer_instance
-- @endregion

end Lumenary.PointSetTopology
