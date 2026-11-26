import Repair.Barrier.Transfer

/-!
# The mean-stopped chain rule (vplusb-poly-extend Proposition A, Corollary A)

Source: `results/vplusb-poly-extend.md` (7d73148) §2, Proposition A and Corollary A. Notation is
that of `Reweighted.lean`: `P` is a probability weight on a finite set `Ω`, `A : ι → Set Ω` are
events, `Z_T = avoid A T`, `ℓ_T = -log U(Z_T)`, `M_T = condMean`, `V_T = condVar`,
`L_T = entSum`, `B_T = bernVarSum`, `μ = ∑_t U(A_t)`, `q = U(Z_ι)`, and the chain is the
`(1 - f)`-weighted ordering `reweight` of COD-198 (Theorem 3, `kerExp_reweight_condVar`,
`kerExp_reweight_entSum`).

* `mul_le_mul_neg_log_of_lt_condMean` (Proposition A, `ℓ_0 = ∞`) : if `q > 0`, `0 ≤ θ ≤ 1`,
  `κ ≥ 0` and `V_T ≤ κ L_T` at every `T` with `M_T > θ μ`, then `(1 - θ) μ ≤ κ (-log q)`.
* `min_le_neg_log_of_lt_condMean` (Proposition A) : if `V_T ≤ κ L_T` at every `T` with
  `M_T > θ μ` and `ℓ_T < ℓ_0`, and `κ > 0`, then `-log q ≥ min{ℓ_0, (1 - θ) μ / κ}`.
* `prob_avoid_univ_le_exp_of_lt_condMean` (Corollary A, any law) : `V_T ≤ κ B_T` at every `T`
  with `M_T > θ μ` and `U(Z_T) > e^(-ℓ)`, with `0 < κ < (1 - θ) μ / ℓ`, gives `q ≤ e^(-ℓ)`.
* `RoundRobin.Canonical.not_repairBound_of_lt_condMean` (Corollary A) : for the round-robin
  events at `m ≥ 6`, the same hypothesis with `ℓ = ℓ_K = (K + 3) log(2m) + log(K + 1) + 1`
  (`levelRarity m K`) and `κ < (1 - θ)(√π / 2) √m / ℓ_K` gives `N_m(G) ≥ K + 1` for every
  gadget, in the form `¬RepairBound m G K` for every six-vertex `G`.

The source proves Proposition A by optional stopping at the first exit from `{M_T > θ μ}`. The
proof here needs no stopping time. With `h(x) = max(x - θ μ, 0)`, every step of the chain has
`h(M_T) - h(M_{T ∪ s}) ≤ 1_{M_T > θ μ} (M_T - M_{T ∪ s})`, and the left side telescopes to
`h(μ) - h(0) = (1 - θ) μ`. So the indicator of the current set may be used in place of the
stopped indicator, and the hypothesis is needed only where `M_T > θ μ`. The source requires
`θ < 1`; `θ = 1` is allowed here, where the statement is trivial.
-/

namespace Pairing

namespace Barrier

open Finset ChainRule

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

/-- Proposition A of `results/vplusb-poly-extend.md` (7d73148) with `ℓ_0 = ∞`: if `q > 0`,
`0 ≤ θ ≤ 1`, `κ ≥ 0` and `V_T ≤ κ L_T` at every `T` with `M_T > θ μ`, then
`(1 - θ) μ ≤ κ (-log q)`. -/
theorem mul_le_mul_neg_log_of_lt_condMean (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {θ κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hV : ∀ T : Finset ι, θ * ∑ t, prob P (A t) < condMean P A T →
      condVar P A T ≤ κ * entSum P A T) :
    (1 - θ) * ∑ t, prob P (A t) ≤ κ * -Real.log (prob P (avoid A univ)) := by
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  set μ := ∑ t, prob P (A t)
  have hμ0 : 0 ≤ μ := sum_nonneg fun t _ ↦ prob_nonneg hP _
  have hH : kerExp (reweight P A)
      (fun T s ↦ max (condMean P A T - θ * μ) 0 - max (condMean P A (insert s T) - θ * μ) 0)
      (Fintype.card ι) ∅ = max (μ - θ * μ) 0 - max (0 - θ * μ) 0 := by
    rw [kerExp_sub hw (fun T ↦ max (condMean P A T - θ * μ) 0) _ ∅
      (by rw [compl_empty, card_univ]), condMean_empty hP, condMean_univ]
  rw [max_eq_left (by nlinarith), max_eq_right (by nlinarith)] at hH
  have h1 := kerExp_mono (w := reweight P A)
    (G := fun T s ↦ max (condMean P A T - θ * μ) 0 - max (condMean P A (insert s T) - θ * μ) 0)
    (H := fun T s ↦ if θ * μ < condMean P A T then
      condMean P A T - condMean P A (insert s T) else 0)
    (fun T s _ ↦ reweight_nonneg hP T s) (fun T s _ ↦ by
      by_cases hT : θ * μ < condMean P A T
      · simp only [hT, ↓reduceIte]
        rw [max_eq_left (by linarith)]
        linarith [le_max_left (condMean P A (insert s T) - θ * μ) 0]
      · simp only [hT, ↓reduceIte]
        rw [max_eq_right (by linarith)]
        linarith [le_max_right (condMean P A (insert s T) - θ * μ) 0])
    (Fintype.card ι) ∅
  have h2 := kerExp_eq_of_sum hw
    (G := fun T s ↦ if θ * μ < condMean P A T then
      condMean P A T - condMean P A (insert s T) else 0)
    (c := fun T ↦ if θ * μ < condMean P A T then condVar P A T / condSlack P A T else 0)
    (fun T _ ↦ by
      by_cases hT : θ * μ < condMean P A T
      · simp only [hT, ↓reduceIte]
        exact sum_reweight_mul_condMean_sub hP T
      · simp only [hT, ↓reduceIte, mul_zero, sum_const_zero]) (Fintype.card ι) ∅
  have h3 := kerExp_mono (w := reweight P A)
    (G := fun T _ ↦ if θ * μ < condMean P A T then condVar P A T / condSlack P A T else 0)
    (H := fun T _ ↦ κ * (entSum P A T / condSlack P A T))
    (fun T s _ ↦ reweight_nonneg hP T s) (fun T s _ ↦ by
      have hD := condSlack_nonneg hP (A := A) T
      have hL := entSum_nonneg hP (A := A) T
      by_cases hT : θ * μ < condMean P A T
      · simp only [hT, ↓reduceIte]
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hV T hT) hD
      · simp only [hT, ↓reduceIte]
        exact mul_nonneg hκ (div_nonneg hL hD)) (Fintype.card ι) ∅
  rw [kerExp_const_mul, kerExp_reweight_entSum hP hq] at h3
  have e : μ - θ * μ - 0 = (1 - θ) * μ := by ring
  linarith

/-- Proposition A of `results/vplusb-poly-extend.md` (7d73148), the mean-stopped chain rule. If
`q > 0`, `0 ≤ θ ≤ 1`, `κ > 0` and `V_T ≤ κ L_T` at every `T` with `M_T > θ μ` and `ℓ_T < ℓ_0`,
then `-log q ≥ min{ℓ_0, (1 - θ) μ / κ}`. -/
theorem min_le_neg_log_of_lt_condMean (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {θ κ ℓ₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ : 0 < κ)
    (hV : ∀ T : Finset ι, θ * ∑ t, prob P (A t) < condMean P A T →
      -Real.log (prob P (avoid A T)) < ℓ₀ → condVar P A T ≤ κ * entSum P A T) :
    min ℓ₀ ((1 - θ) * (∑ t, prob P (A t)) / κ) ≤ -Real.log (prob P (avoid A univ)) := by
  by_cases hℓ : ℓ₀ ≤ -Real.log (prob P (avoid A univ))
  · exact (min_le_left _ _).trans hℓ
  push Not at hℓ
  have hall : ∀ T : Finset ι, -Real.log (prob P (avoid A T)) < ℓ₀ := fun T ↦ by
    have := Real.log_le_log hq (prob_mono hP (avoid_anti (subset_univ T)))
    linarith
  have h := mul_le_mul_neg_log_of_lt_condMean hP hq hθ0 hθ1 hκ.le fun T hT ↦ hV T hT (hall T)
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ hκ]
  linarith

/-- Corollary A of `results/vplusb-poly-extend.md` (7d73148) for any law: if `q > 0`,
`0 ≤ θ ≤ 1`, `0 < κ < (1 - θ) μ / ℓ` and `V_T ≤ κ B_T` at every `T` with `M_T > θ μ` and
`U(Z_T) > e^(-ℓ)`, then `q ≤ e^(-ℓ)`. The hypothesis may be put on `L_T` in place of `B_T`, since
`B_T ≤ L_T`. -/
theorem prob_avoid_univ_le_exp_of_lt_condMean (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {θ κ ℓ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ : 0 < κ)
    (hκℓ : κ < (1 - θ) * (∑ t, prob P (A t)) / ℓ)
    (hV : ∀ T : Finset ι, θ * ∑ t, prob P (A t) < condMean P A T →
      Real.exp (-ℓ) < prob P (avoid A T) → condVar P A T ≤ κ * bernVarSum P A T) :
    prob P (avoid A univ) ≤ Real.exp (-ℓ) := by
  have hmin := min_le_neg_log_of_lt_condMean hP hq hθ0 hθ1 hκ (ℓ₀ := ℓ) fun T hT hℓT ↦ by
    have hu : 0 < prob P (avoid A T) := hq.trans_le (prob_mono hP (avoid_anti (subset_univ T)))
    have hw : Real.exp (-ℓ) < prob P (avoid A T) := by
      rw [← Real.lt_log_iff_exp_lt hu]
      linarith
    exact (hV T hT hw).trans (mul_le_mul_of_nonneg_left (bernVarSum_le_entSum hP T) hκ.le)
  have hℓ : ℓ ≤ -Real.log (prob P (avoid A univ)) := by
    by_cases hℓ0 : ℓ ≤ 0
    · have : Real.log (prob P (avoid A univ)) ≤ 0 :=
        Real.log_nonpos hq.le (prob_le_one hP _)
      linarith
    push Not at hℓ0
    have h1 : ℓ ≤ (1 - θ) * (∑ t, prob P (A t)) / κ := by
      rw [le_div_iff₀ hκ]
      rw [lt_div_iff₀ hℓ0] at hκℓ
      linarith
    rwa [min_eq_left h1] at hmin
  rw [← Real.log_le_iff_le_exp hq]
  linarith

end Barrier

namespace RoundRobin.Canonical

open Finset ChainRule Barrier

/-- The rarity level `ℓ_K = (K + 3) log(2m) + log(K + 1) + 1` of `results/vplusb-poly-extend.md`
(7d73148), with `e^(-ℓ_K) = 1 / (e (K + 1) (2m)^(K + 3))`. -/
noncomputable def levelRarity (m K : ℕ) : ℝ :=
  (K + 3) * Real.log (2 * m) + Real.log (K + 1) + 1

/-- `e^(ℓ_K) = (2m)^(K + 3) (K + 1) e` (`results/vplusb-poly-extend.md` (7d73148) §1). -/
theorem exp_levelRarity {m : ℕ} [NeZero m] (K : ℕ) :
    Real.exp (levelRarity m K) = (2 * m) ^ (K + 3) * (K + 1) * Real.exp 1 := by
  have hm : (0 : ℝ) < 2 * m := by
    have := NeZero.pos m
    positivity
  rw [levelRarity, Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
    show ((K : ℝ) + 3) * Real.log (2 * m) = Real.log ((2 * m) ^ (K + 3)) by
      rw [Real.log_pow]
      push_cast
      ring, Real.exp_log (by positivity)]

/-- `ℓ_K > 0` (`results/vplusb-poly-extend.md` (7d73148) §1). -/
theorem levelRarity_pos {m : ℕ} [NeZero m] (K : ℕ) : 0 < levelRarity m K := by
  have hm : (1 : ℝ) ≤ 2 * m := by
    have : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
    linarith
  have h1 := Real.log_nonneg hm
  have h2 := Real.log_nonneg (by linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)] : (1 : ℝ) ≤ K + 1)
  rw [levelRarity]
  positivity

/-- The counting lemma P5 in the form used by `results/vplusb-poly-extend.md` (7d73148):
`q_m ≤ e^(-ℓ_K)` excludes `RepairBound m G K` for every six-vertex gadget `G`. -/
theorem not_repairBound_of_hamLaw_zero_le {m : ℕ} [NeZero m] {K : ℕ}
    (hq : hamLaw m 0 ≤ Real.exp (-levelRarity m K)) {G : Finset (Vertex m)} (hG : G.card = 6) :
    ¬RepairBound m G K := by
  intro hK
  have h1 := one_le_hamLaw_zero_mul hG hK
  have hE := exp_levelRarity (m := m) K
  have hq' : hamLaw m 0 * Real.exp (levelRarity m K) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hq (Real.exp_pos (levelRarity m K)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  rw [hE] at hq'
  have hmK : (K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) = (2 * m) ^ (K + 3) * (K + 1) := by ring
  rw [hmK] at h1
  have he : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  nlinarith

/-- Corollary A of `results/vplusb-poly-extend.md` (7d73148) for the round-robin events. Let
`m ≥ 6`, `0 ≤ θ ≤ 1` and `0 < κ < (1 - θ)(√π / 2) √m / ℓ_K`. If `V_T ≤ κ B_T` at every `T` with
`M_T > θ μ_m` and `U(Z_T) > e^(-ℓ_K)`, then `RepairBound m G K` fails for every six-vertex
gadget `G`, that is `N_m(G) ≥ K + 1`. -/
theorem not_repairBound_of_lt_condMean {m : ℕ} [NeZero m] (hm : 6 ≤ m) {K : ℕ} {θ κ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ : 0 < κ)
    (hκK : κ < (1 - θ) * (Real.sqrt Real.pi / 2 * Real.sqrt m) / levelRarity m K)
    (hV : ∀ T : Finset (ZMod (2 * m - 1)),
      θ * ∑ t, prob (unifWeight m) (hamEvent m t) < condMean (unifWeight m) (hamEvent m) T →
      Real.exp (-levelRarity m K) < prob (unifWeight m) (avoid (hamEvent m) T) →
      condVar (unifWeight m) (hamEvent m) T ≤ κ * bernVarSum (unifWeight m) (hamEvent m) T)
    {G : Finset (Vertex m)} (hG : G.card = 6) : ¬RepairBound m G K := by
  have hμ := (sqrt_mul_sqrt_le_sum_prob_hamEvent m).1
  have hℓ := levelRarity_pos (m := m) K
  have hκ' : κ < (1 - θ) * (∑ t, prob (unifWeight m) (hamEvent m t)) / levelRarity m K :=
    hκK.trans_le (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hμ (by linarith)) hℓ.le)
  have h := prob_avoid_univ_le_exp_of_lt_condMean (isProb_unifWeight m)
    (prob_avoid_hamEvent_pos hm) hθ0 hθ1 hκ hκ' hV
  rw [prob_avoid_hamEvent] at h
  exact not_repairBound_of_hamLaw_zero_le h hG

end RoundRobin.Canonical

end Pairing
