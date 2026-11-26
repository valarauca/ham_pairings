import Repair.Barrier.Contamination

/-!
# Transfer of barriers to the polynomial-rarity rungs (vplusb-poly-contra Theorem 1)

Source: `results/vplusb-poly-contra.md` (1b201a5) §2, Theorem 1 and the B22 instance of
Corollary 1.1. Notation is that of `Reweighted.lean`: `P` is a probability weight on a finite set
`Ω`, `A : ι → Set Ω` are events, `Z_T = avoid A T`, `V_T = condVar`, `B_T = bernVarSum`,
`N_T = |Tᶜ|`, `μ = ∑_t U(A_t)` and `q = U(Z_ι) = U(X = 0)`. The source states Theorem 1 for laws
on perfect matchings. The proof uses only the law-agnostic chain rule, so it is stated here for
every law.

* `exists_lt_condVar` (Theorem 1) : if `q > e^(-ℓ)`, `μ > 1` and `κ < (μ - 1) / ℓ`, then some `T`
  with `N_T ≥ 2` has `V_T > κ B_T`, and that `T` has `U(Z_T) > e^(-ℓ)`.
* `prob_avoid_univ_le_exp_of_condVar_le` (Corollary 1.1(2), "R_K ⟹ Q_K") : (V+_B) with
  `κ < (μ - 1) / ℓ` at every `T` with `N_T ≥ 2` and `U(Z_T) > e^(-ℓ)` gives `q ≤ e^(-ℓ)`.
* `exists_boost_lt_condVar` (the B22 instance) : for `0 < q < 1` and `e^(-ℓ) < τ < 1` the
  level-weight law `ν_c` of `LevelWeight.lean` with `c = (τ - q) / (q (1 - τ))` has `c > -1`,
  `ν_c(Z_ι) = τ`, `μ(ν_c) = μ (1 - τ) / (1 - q)`, and violates (V+_B) at a rung set for every
  `κ < (μ (1 - τ) / (1 - q) - 1) / ℓ`. Since `ν_c` keeps everything listed in Theorem 1 of
  `results/fbr-contra.md` (b2ea07c), that input class proves no rung.

Corrections to the source. Theorem 1 assumes `max_t ν(A_t) < 1` and implicitly `κ > 0`. Neither
is needed: `q > 0` forces `U(A_t) ≤ 1 - q`, and a `κ ≤ 0` can be raised to a positive value below
`(μ - 1) / ℓ`, since `B_T ≥ 0`.
-/

namespace Pairing

namespace Barrier

open Finset ChainRule

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

omit [DecidableEq ι] in
/-- `U(A_t) ≤ 1 - q`, since no `A_t` occurs on `Z_ι` (`results/vplusb-poly-contra.md` (1b201a5),
proof of Theorem 1). -/
theorem prob_le_one_sub_prob_avoid_univ (hP : IsProb P) (t : ι) :
    prob P (A t) ≤ 1 - prob P (avoid A univ) := by
  have h := prob_eq_inter_add_diff P Set.univ (A t)
  rw [prob_univ hP, Set.inter_univ] at h
  have hsub : avoid A univ ⊆ Set.univ \ A t := fun ω hω ↦ ⟨trivial, hω t (mem_univ t)⟩
  linarith [prob_mono hP hsub]

/-- Theorem 1 of `results/vplusb-poly-contra.md` (1b201a5), transfer of barriers. Every law with
`q > e^(-ℓ)`, `μ > 1` and `κ < (μ - 1) / ℓ` violates (V+_B), `V_T > κ B_T`, at some `T` with
`N_T ≥ 2`, and that `T` has `U(Z_T) > e^(-ℓ)`. The source's hypotheses `max_t U(A_t) < 1` and
`κ > 0` are not needed. -/
theorem exists_lt_condVar (hP : IsProb P) {ℓ κ : ℝ}
    (hq : Real.exp (-ℓ) < prob P (avoid A univ)) (hμ : 1 < ∑ t, prob P (A t))
    (hκ : κ < (∑ t, prob P (A t) - 1) / ℓ) :
    ∃ T : Finset ι, 2 ≤ Tᶜ.card ∧ Real.exp (-ℓ) < prob P (avoid A T) ∧
      κ * bernVarSum P A T < condVar P A T := by
  set q := prob P (avoid A univ)
  set μ := ∑ t, prob P (A t)
  have hq0 : 0 < q := (Real.exp_pos _).trans hq
  have hq1 : q ≤ 1 := prob_le_one hP _
  have hℓ : 0 < ℓ := by
    by_contra h
    push Not at h
    have : 1 ≤ Real.exp (-ℓ) := Real.one_le_exp (by linarith)
    linarith
  have hwin : ∀ T : Finset ι, Real.exp (-ℓ) < prob P (avoid A T) := fun T ↦
    hq.trans_le (prob_mono hP (avoid_anti (subset_univ T)))
  by_contra hne
  push Not at hne
  set κ' := max κ ((μ - 1) / (2 * ℓ))
  have hκ'0 : 0 < κ' := lt_of_lt_of_le (div_pos (by linarith) (by linarith)) (le_max_right _ _)
  have hκ'1 : κ' < (μ - 1) / ℓ :=
    max_lt hκ (div_lt_div_of_pos_left (by linarith) hℓ (by linarith))
  have hp : ∀ t, prob P (A t) ≤ 1 - q / 2 := fun t ↦
    (prob_le_one_sub_prob_avoid_univ hP t).trans (by linarith)
  have key := div_le_neg_log_of_condVar_le_bernVarSum hP hq0 (p := 1 - q / 2) (δ := 0)
    (κ := κ') (K := 1) hp (by linarith) le_rfl (by linarith) (by linarith) hκ'0
    (fun T _ hT ↦ (hne T hT (hwin T)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (bernVarSum_nonneg hP T)))
  norm_num at key
  have hlog : -Real.log q < ℓ := by
    rw [neg_lt]
    exact (Real.lt_log_iff_exp_lt hq0).mpr hq
  have hlt : ℓ < (μ - 1) / κ' := by
    rw [lt_div_iff₀ hκ'0]
    rwa [lt_div_iff₀ hℓ, mul_comm] at hκ'1
  linarith

/-- Corollary 1.1(2) of `results/vplusb-poly-contra.md` (1b201a5), the law-agnostic form of
"`R_K ⟹ Q_K`": if `μ > 1`, `κ < (μ - 1) / ℓ` and `V_T ≤ κ B_T` at every `T` with `N_T ≥ 2` and
`U(Z_T) > e^(-ℓ)`, then `q ≤ e^(-ℓ)`. -/
theorem prob_avoid_univ_le_exp_of_condVar_le (hP : IsProb P) {ℓ κ : ℝ}
    (hμ : 1 < ∑ t, prob P (A t)) (hκ : κ < (∑ t, prob P (A t) - 1) / ℓ)
    (hV : ∀ T : Finset ι, 2 ≤ Tᶜ.card → Real.exp (-ℓ) < prob P (avoid A T) →
      condVar P A T ≤ κ * bernVarSum P A T) :
    prob P (avoid A univ) ≤ Real.exp (-ℓ) := by
  by_contra h
  push Not at h
  obtain ⟨T, hT, hw, hlt⟩ := exists_lt_condVar hP h hμ hκ
  exact absurd (hV T hT hw) (not_le.mpr hlt)

/-- The B22 instance of Corollary 1.1 of `results/vplusb-poly-contra.md` (1b201a5). Let
`0 < q < 1` and `e^(-ℓ) < τ < 1`. The level-weight law `ν_c = (1 + c 1_{Z_ι}) U / (1 + c q)` of
`results/fbr-contra.md` (b2ea07c) Theorem 1 with `c = (τ - q) / (q (1 - τ))` has `c > -1`,
`ν_c(Z_ι) = τ` and `μ(ν_c) = μ (1 - τ) / (1 - q)`. If `μ(ν_c) > 1` and
`κ < (μ(ν_c) - 1) / ℓ`, it violates (V+_B) at some `T` with `N_T ≥ 2` and `ν_c(Z_T) > e^(-ℓ)`. -/
theorem exists_boost_lt_condVar (hP : IsProb P) (hq0 : 0 < prob P (avoid A univ))
    (hq1 : prob P (avoid A univ) < 1) {ℓ τ κ : ℝ} (hτ0 : Real.exp (-ℓ) < τ) (hτ1 : τ < 1)
    (hμ : 1 < (∑ t, prob P (A t)) * (1 - τ) / (1 - prob P (avoid A univ)))
    (hκ : κ < ((∑ t, prob P (A t)) * (1 - τ) / (1 - prob P (avoid A univ)) - 1) / ℓ) :
    ∃ c : ℝ, -1 < c ∧ prob (boost P (avoid A univ) c) (avoid A univ) = τ ∧
      ∑ t, prob (boost P (avoid A univ) c) (A t) =
        (∑ t, prob P (A t)) * (1 - τ) / (1 - prob P (avoid A univ)) ∧
      ∃ T : Finset ι, 2 ≤ Tᶜ.card ∧
        Real.exp (-ℓ) < prob (boost P (avoid A univ) c) (avoid A T) ∧
        κ * bernVarSum (boost P (avoid A univ) c) A T < condVar (boost P (avoid A univ) c) A T := by
  set q := prob P (avoid A univ)
  have hτ : 0 < τ := (Real.exp_pos _).trans hτ0
  have h1q : 0 < 1 - q := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  set c := (τ - q) / (q * (1 - τ))
  have hc1 : 1 + c = τ * (1 - q) / (q * (1 - τ)) := by
    rw [show c = (τ - q) / (q * (1 - τ)) from rfl]
    field_simp
    ring
  have hc : -1 < c := by
    have : 0 < 1 + c := by rw [hc1]; positivity
    linarith
  have hD : 1 + c * q = (1 - q) / (1 - τ) := by
    rw [show c = (τ - q) / (q * (1 - τ)) from rfl]
    field_simp
    ring
  have hZ : prob (boost P (avoid A univ) c) (avoid A univ) = τ := by
    rw [prob_boost, Set.inter_self, show q + c * q = (1 + c) * q by ring, hD, hc1]
    field_simp
  have hμν : ∑ t, prob (boost P (avoid A univ) c) (A t) =
      (∑ t, prob P (A t)) * (1 - τ) / (1 - q) := by
    rw [sum_prob_boost subset_rfl, hD]
    field_simp
  refine ⟨c, hc, hZ, hμν, ?_⟩
  refine exists_lt_condVar (isProb_boost hP hc _) (hZ ▸ hτ0) (hμν ▸ hμ) ?_
  rwa [hμν]

end Barrier

end Pairing
