import Suppression.SizeBias

/-!
# Finite probability weights and the laws of `ℕ`-valued variables

A probability weight `P` on a finite set `Ω` (`IsProb P`) gives the law `U(S) = prob P S`. The
chain-rule reductions (`ChainRule.lean`) work with `U` itself, while the size-bias and tilted-law
reductions (`SizeBias.lean`, `Tilt.lean`) work with a law `p` on `ℕ` (`SizeBias.IsLaw`). This file
holds the facts about `U` that the chain rule uses and passes from `U` to a law on `ℕ` by pushing
forward along a variable `X : Ω → ℕ`.

* `prob_nonneg`, `prob_mono`, `prob_univ`, `prob_le_one`, `prob_eq_inter_add_diff`,
  `prob_eq_zero_of_subset` : `U` is a finitely additive probability.
* `lawOf P X`, the law `k ↦ U(X = k)` of `X`. `sum_mul_lawOf` :
  `∑_ω P ω g(X ω) = ∑_{k ≤ N} U(X = k) g(k)` when `X ≤ N`, and `isLaw_lawOf` : the law of
  `X ≤ N` is a law on `[0, N]`.

The round-robin law `hamLaw m` is `lawOf` of the uniform weight along `hamCount m`
(`RoundRobin.Canonical.hamLaw_eq_lawOf`). The declarations sit in the namespace `ChainRule`, where
`IsProb` and `prob` were first introduced.
-/

namespace Pairing

namespace ChainRule

open Finset

variable {Ω : Type*}

/-- `P` is a probability weight on the finite set `Ω`. -/
structure IsProb [Fintype Ω] (P : Ω → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ P ω
  sum_eq_one : ∑ ω, P ω = 1

/-- `U(S) = ∑_{ω ∈ S} P ω`. -/
noncomputable def prob [Fintype Ω] (P : Ω → ℝ) (S : Set Ω) : ℝ :=
  ∑ ω, S.indicator P ω

variable [Fintype Ω] {P : Ω → ℝ}

/-- `U(S) ≥ 0`. -/
theorem prob_nonneg (hP : IsProb P) (S : Set Ω) : 0 ≤ prob P S :=
  sum_nonneg fun ω _ ↦ Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω

/-- `U` is monotone. -/
theorem prob_mono (hP : IsProb P) {S S' : Set Ω} (h : S ⊆ S') : prob P S ≤ prob P S' :=
  sum_le_sum fun ω _ ↦ Set.indicator_le_indicator_of_subset h (fun ω ↦ hP.nonneg ω) ω

/-- `U(Ω) = 1`. -/
theorem prob_univ (hP : IsProb P) : prob P Set.univ = 1 := by
  simp [prob, hP.sum_eq_one]

/-- `U(S) ≤ 1`. -/
theorem prob_le_one (hP : IsProb P) (S : Set Ω) : prob P S ≤ 1 :=
  (prob_mono hP (Set.subset_univ S)).trans_eq (prob_univ hP)

/-- `U(S) = U(B ∩ S) + U(S ∖ B)`. -/
theorem prob_eq_inter_add_diff (P : Ω → ℝ) (S B : Set Ω) :
    prob P S = prob P (B ∩ S) + prob P (S \ B) := by
  rw [prob, prob, prob, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ ↦ ?_
  by_cases hS : ω ∈ S <;> by_cases hB : ω ∈ B <;> simp [Set.indicator, hS, hB]

/-- A subset of a null event is null. -/
theorem prob_eq_zero_of_subset (hP : IsProb P) {S S' : Set Ω} (h : S ⊆ S')
    (h' : prob P S' = 0) : prob P S = 0 :=
  le_antisymm (h' ▸ prob_mono hP h) (prob_nonneg hP S)

/-- The law `k ↦ U(X = k)` of `X : Ω → ℕ` under the weight `P`. -/
noncomputable def lawOf (P : Ω → ℝ) (X : Ω → ℕ) (k : ℕ) : ℝ :=
  prob P {ω | X ω = k}

/-- `U(X = k) = ∑_{ω | X ω = k} P ω`. -/
theorem lawOf_eq_sum (P : Ω → ℝ) (X : Ω → ℕ) (k : ℕ) :
    lawOf P X k = ∑ ω ∈ univ.filter fun ω ↦ X ω = k, P ω := by
  rw [lawOf, prob, sum_filter]
  exact sum_congr rfl fun ω _ ↦ Set.indicator_apply _ _ _

/-- Change of variables. If `X ≤ N`, then `∑_ω P ω g(X ω) = ∑_{k ≤ N} U(X = k) g(k)`. -/
theorem sum_mul_lawOf (P : Ω → ℝ) {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) (g : ℕ → ℝ) :
    ∑ ω, P ω * g (X ω) = ∑ k ∈ range (N + 1), lawOf P X k * g k := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (N + 1)) (g := X)
    fun ω _ ↦ mem_range.mpr (Nat.lt_succ_of_le (hX ω))]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [lawOf_eq_sum, sum_mul]
  exact sum_congr rfl fun ω hω ↦ by rw [(mem_filter.mp hω).2]

/-- The law of a variable `X ≤ N` under a probability weight is a law on `[0, N]`. -/
theorem isLaw_lawOf (hP : IsProb P) {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) :
    SizeBias.IsLaw (lawOf P X) N where
  nonneg _ := prob_nonneg hP _
  eq_zero k hk := by
    rw [lawOf_eq_sum]
    exact sum_eq_zero fun ω hω ↦ absurd (mem_filter.mp hω).2 (by have := hX ω; omega)
  sum_eq_one := by
    simpa [hP.sum_eq_one] using (sum_mul_lawOf P hX fun _ ↦ 1).symm

end ChainRule

end Pairing
