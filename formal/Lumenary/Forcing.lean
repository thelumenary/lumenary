/-
The Lumenary — formal mathematics
Forcing: the combinatorial heart of Cohen's method. Conditions are finite binary strings,
dense sets are the "requirements" a generic object must meet, and a filter meeting countably many
of them exists (the Rasiowa–Sikorski lemma) and produces a *new* real.

What is formalised. We work in the extension order, where `p ≤ q` means "`q` extends `p`" (`q` is
the stronger condition). In this order Mathlib's `Order.Cofinal` sets are exactly the **dense**
sets of forcing, and Mathlib's `Order.Ideal`s are exactly the **filters** of forcing (closed
under weakening, and any two members have a common extension inside). Proved here: the
"domain" and "avoid x" sets are dense; a filter meeting every domain set determines a real; a
filter meeting the "avoid x" sets differs from every such `x` — so for any countable list of
reals (a stand-in for the reals of a countable model `M`) there is a Cohen real not on the list;
and no filter meets *every* dense set, which is why forcing starts from a countable model.
The Rasiowa–Sikorski lemma itself is Mathlib's `Order.idealOfCofinals`. Not formalised: the
forcing relation, the truth and definability lemmas, `M[G] ⊨ ZFC`, the countable chain condition
and the independence of CH. (A full formalisation of the independence of CH exists in Lean 3 —
the Flypitch project of Han and van Doorn — and in Isabelle/ZF; it is not in Mathlib.)
-/
import Mathlib.Order.Ideal

namespace Lumenary.Forcing

-- @region forcing.cohen
-- @provenance definition
/-- **Cohen forcing**: a condition is a finite binary string `p = (p₀, …, p_{k-1})`, a finite
approximation to an infinite binary sequence ("a real"). -/
structure Cohen where
  /-- The finite binary string. -/
  bits : List Bool
-- @endregion

namespace Cohen

-- @region forcing.inst_preorder
-- @provenance definition
/-- The extension order: `p ≤ q` iff `p` is an initial segment (prefix) of `q`, i.e. `q` carries
at least as much information as `p`. -/
instance instPreorder : Preorder Cohen where
  le p q := p.bits <+: q.bits
  le_refl p := List.prefix_refl p.bits
  le_trans _ _ _ := List.IsPrefix.trans
-- @endregion

-- @region forcing.bit
-- @provenance definition
/-- The `i`-th bit decided by the condition `p`, if `p` is long enough. -/
def bit (p : Cohen) (i : ℕ) : Option Bool := p.bits[i]?
-- @endregion

-- @region forcing.bit_mono
-- @provenance independent
/-- Stronger conditions keep the decisions of weaker ones: if `p ≤ q` and `p` says bit `i` is
`b`, so does `q`. -/
theorem bit_mono {p q : Cohen} (h : p ≤ q) {i : ℕ} {b : Bool} (hb : bit p i = some b) :
    bit q i = some b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  exact List.prefix_iff_getElem?.mp h i hi
-- @endregion

-- @region forcing.decides_dense
-- @provenance independent
/-- For each `n`, the set of conditions that decide bit `n` is **dense**: any condition can be
extended (by padding with zeros) to one of length greater than `n`. -/
theorem decides_dense (n : ℕ) : IsCofinal {p : Cohen | (bit p n).isSome} := by
  intro p
  refine ⟨⟨p.bits ++ List.replicate (n + 1) false⟩, ?_, List.prefix_append _ _⟩
  show (p.bits ++ List.replicate (n + 1) false)[n]?.isSome
  rw [Option.isSome_iff_ne_none, Ne, List.getElem?_eq_none_iff, not_le,
    List.length_append, List.length_replicate]
  omega
-- @endregion

-- @region forcing.avoids_dense
-- @provenance independent
/-- For each real `x : ℕ → Bool`, the set of conditions that **disagree with `x` somewhere** is
dense: extend `p` by one bit, the opposite of `x` at position `length p`. Meeting this set is
how a generic real escapes `x` — a diagonal argument, one step at a time. -/
theorem avoids_dense (x : ℕ → Bool) : IsCofinal {p : Cohen | ∃ i, bit p i = some (!x i)} := by
  intro p
  refine ⟨⟨p.bits ++ [!x p.bits.length]⟩, ⟨p.bits.length, ?_⟩, List.prefix_append _ _⟩
  show (p.bits ++ [!x p.bits.length])[p.bits.length]? = _
  simp
-- @endregion

-- @region forcing.decides
-- @provenance definition
/-- The dense set "bit `n` is decided", bundled as a Mathlib `Order.Cofinal`. -/
def decides (n : ℕ) : Order.Cofinal Cohen := ⟨{p | (bit p n).isSome}, decides_dense n⟩
-- @endregion

-- @region forcing.avoids
-- @provenance definition
/-- The dense set "disagrees with `x` somewhere", bundled as a Mathlib `Order.Cofinal`. -/
def avoids (x : ℕ → Bool) : Order.Cofinal Cohen :=
  ⟨{p | ∃ i, bit p i = some (!x i)}, avoids_dense x⟩
-- @endregion

end Cohen

open Cohen

-- @region forcing.rasiowa_sikorski
-- @provenance library
/-- **The Rasiowa–Sikorski lemma**: for any *countable* family of dense sets in a preorder there
is a filter (here: an `Order.Ideal` of the extension order) meeting all of them. Its proof
builds a sequence `p₀ ≤ p₁ ≤ ⋯` with `p_{n+1}` in the `n`-th dense set. This applies Mathlib's
`Order.idealOfCofinals` and `Order.cofinal_meets_idealOfCofinals`. -/
theorem rasiowa_sikorski {P : Type*} [Preorder P] (p : P) {ι : Type*} [Encodable ι]
    (D : ι → Order.Cofinal P) : ∃ G : Order.Ideal P, p ∈ G ∧ ∀ i, ∃ q ∈ D i, q ∈ G :=
  ⟨Order.idealOfCofinals p D, Order.mem_idealOfCofinals p D,
    Order.cofinal_meets_idealOfCofinals p D⟩
-- @endregion

-- @region forcing.generic_real
-- @provenance independent
/-- **A generic filter determines a real.** If a filter `G` meets every dense set `decides n`,
the conditions in `G` are compatible finite approximations of a single real `g`: every bit
decided by a member of `G` is the corresponding bit of `g`.
Proof: choose `pₙ ∈ G` deciding bit `n` and let `g n` be that bit. If `p ∈ G` decides bit `n`
as `b`, then `p` and `pₙ` have a common extension `r ∈ G` (directedness), which decides bit `n`
both as `b` and as `g n`. -/
theorem generic_real (G : Order.Ideal Cohen) (hG : ∀ n, ∃ p ∈ decides n, p ∈ G) :
    ∃ g : ℕ → Bool, ∀ p ∈ G, ∀ i b, bit p i = some b → g i = b := by
  choose q hqD hqG using hG
  -- `q n ∈ G` decides bit `n`; read that bit off.
  have hsome : ∀ n, ∃ b, bit (q n) n = some b := fun n => Option.isSome_iff_exists.mp (hqD n)
  choose g hg using hsome
  refine ⟨g, fun p hp i b hb => ?_⟩
  obtain ⟨r, -, hpr, hqr⟩ := G.directed p hp (q i) (hqG i)
  have h1 : bit r i = some b := bit_mono hpr hb
  have h2 : bit r i = some (g i) := bit_mono hqr (hg i)
  exact Option.some.inj (h2.symm.trans h1)
-- @endregion

-- @region forcing.cohen_real_not_in_list
-- @provenance independent
/-- **Cohen reals are new.** For every countable list `x₀, x₁, …` of reals there is a real `g`
different from all of them — obtained, as in forcing, from a filter meeting the countably many
dense sets `decides n` and `avoids xₖ`. With the list taken to be the reals of a countable
transitive model `M`, this is the statement that the Cohen real of `M[G]` is not in `M`.
(Cantor's diagonal argument, rebuilt from genericity.) -/
theorem cohen_real_not_in_list (xs : ℕ → ℕ → Bool) : ∃ g : ℕ → Bool, ∀ k, g ≠ xs k := by
  obtain ⟨G, -, hG⟩ := rasiowa_sikorski (⟨[]⟩ : Cohen)
    (fun j : ℕ ⊕ ℕ => Sum.elim decides (fun k => avoids (xs k)) j)
  obtain ⟨g, hg⟩ := generic_real G (fun n => hG (Sum.inl n))
  refine ⟨g, fun k hk => ?_⟩
  obtain ⟨p, ⟨i, hi⟩, hpG⟩ := hG (Sum.inr k)
  have := hg p hpG i _ hi
  rw [hk] at this
  exact Bool.not_ne_self (xs k i) this.symm
-- @endregion

-- @region forcing.no_filter_meets_every_dense
-- @provenance independent
/-- **No filter meets every dense set.** For any filter `G`, the complement of `G` is dense, and
`G` does not meet it. Proof: any `p` has the two incompatible extensions `p⌢0` and `p⌢1`; a
filter cannot contain both (they have no common extension), so one lies outside `G`. This is why
forcing begins with a *countable* model `M`: we only ask `G` to meet the dense sets that belong
to `M`, and then `G ∉ M`. -/
theorem no_filter_meets_every_dense (G : Order.Ideal Cohen) :
    ∃ D : Set Cohen, IsCofinal D ∧ ∀ p ∈ D, p ∉ G := by
  refine ⟨(G : Set Cohen)ᶜ, ?_, fun p hp => hp⟩
  intro p
  by_contra h
  push Not at h
  -- Both one-bit extensions of `p` would lie in `G` ...
  have hin : ∀ b : Bool, (⟨p.bits ++ [b]⟩ : Cohen) ∈ (G : Set Cohen) := by
    intro b
    by_contra hb
    exact h _ hb (List.prefix_append _ _)
  -- ... so they would have a common extension `r`, forcing `p⌢1 = p⌢0`.
  obtain ⟨r, -, h1, h2⟩ := G.directed _ (hin true) _ (hin false)
  have hpre := List.prefix_of_prefix_length_le h1 h2 (by simp)
  have heq := hpre.eq_of_length (by simp)
  simp at heq
-- @endregion

end Lumenary.Forcing
