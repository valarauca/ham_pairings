import Suppression.VMinus
import Repair.Barrier.Contamination

/-!
# Capped variance (vplusb-poly-contra Theorem 4)

Source: `results/vplusb-poly-contra.md` (1b201a5) §4.1, Theorem 4. Notation is that of
`Reweighted.lean`: `P` is a probability weight on a finite set `Ω`, `A : ι → Set Ω` are events,
`Z_T = avoid A T`, `ℓ_T = -log U(Z_T)`, `M_T = condMean`, `V_T = condVar`, `B_T = bernVarSum`,
`X = eventNum A` (`eventCount A` as a natural number) and `n = |ι|`. For a law `p` on `[0, N]`, a
centre `c` and `ℓ`, put

  `Φ(ℓ) = sup{∑_x w_x (x - c)² : 0 ≤ w_x ≤ e^ℓ p(x), ∑_x w_x = 1}` (`capVar p N c ℓ`).

The source takes `c = μ = E X`. The statements below hold for every centre.

* `capVar_le` : `Φ(ℓ) ≤ s + e^ℓ E[(X - c)²; (X - c)² > s]` for every `s ≥ 0`.
* `condLaw_le` (item 1) : `ν_T(X = x) ≤ e^(ℓ_T) U(X = x)`.
* `condVar_add_sq_le_capVar` (item 2) : `V_T + (M_T - c)² = E_T(X - c)² ≤ Φ(ℓ_T)`, so
  `condVar_le_capVar` : `V_T ≤ Φ(ℓ_T)` and `abs_condMean_sub_le` : `|M_T - c| ≤ √Φ(ℓ_T)`.
* `condVar_div_bernVarSum_le` (item 3) : if `f_s(T) ≤ φ < 1` for `s ∉ T` and `Φ(ℓ_T) < c²` with
  `c > 0`, then `V_T / B_T ≤ Φ(ℓ_T) / ((1 - φ)(c - √Φ(ℓ_T)))`.

Item 3 is stated with the cap `f_s(T) ≤ φ` at the one set `T`, as in the source, not at every set.
-/

namespace Pairing

namespace Barrier

open Finset ChainRule

/-- `Φ(ℓ)`, the largest second moment about `c` of a law on `[0, N]` with density at most `e^ℓ`
against `p` (`results/vplusb-poly-contra.md` (1b201a5), Theorem 4). -/
noncomputable def capVar (p : ℕ → ℝ) (N : ℕ) (c ℓ : ℝ) : ℝ :=
  sSup {v | ∃ w : ℕ → ℝ, (∀ x, 0 ≤ w x) ∧ (∀ x, w x ≤ Real.exp ℓ * p x) ∧
    ∑ x ∈ range (N + 1), w x = 1 ∧ v = ∑ x ∈ range (N + 1), w x * ((x : ℝ) - c) ^ 2}

/-- Theorem 4 of `results/vplusb-poly-contra.md` (1b201a5), the split bound:
`Φ(ℓ) ≤ s + e^ℓ E[(X - c)²; (X - c)² > s]` for every `s ≥ 0`. -/
theorem capVar_le {p : ℕ → ℝ} (hp : ∀ x, 0 ≤ p x) (N : ℕ) (c ℓ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    capVar p N c ℓ ≤ s + Real.exp ℓ *
      ∑ x ∈ (range (N + 1)).filter (fun x : ℕ ↦ s < ((x : ℝ) - c) ^ 2),
        p x * ((x : ℝ) - c) ^ 2 := by
  have hR : 0 ≤ s + Real.exp ℓ *
      ∑ x ∈ (range (N + 1)).filter (fun x : ℕ ↦ s < ((x : ℝ) - c) ^ 2),
        p x * ((x : ℝ) - c) ^ 2 :=
    add_nonneg hs (mul_nonneg (Real.exp_pos ℓ).le
      (sum_nonneg fun x _ ↦ mul_nonneg (hp x) (sq_nonneg _)))
  refine Real.sSup_le ?_ hR
  rintro v ⟨w, hw0, hwp, hw1, rfl⟩
  have key : ∀ x ∈ range (N + 1), w x * ((x : ℝ) - c) ^ 2 ≤ s * w x +
      if s < ((x : ℝ) - c) ^ 2 then Real.exp ℓ * (p x * ((x : ℝ) - c) ^ 2) else 0 := by
    intro x _
    by_cases h : s < ((x : ℝ) - c) ^ 2
    · rw [ite_eq_left h]
      have := mul_le_mul_of_nonneg_right (hwp x) (sq_nonneg ((x : ℝ) - c))
      nlinarith [hw0 x]
    · rw [ite_eq_right h]
      push Not at h
      nlinarith [hw0 x]
  refine (sum_le_sum key).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← mul_sum, hw1, mul_one, sum_ite, sum_const_zero, add_zero, mul_sum]

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

omit [DecidableEq ι] in
/-- Theorem 4 item 1 of `results/vplusb-poly-contra.md` (1b201a5):
`ν_T(X = x) ≤ e^(ℓ_T) U(X = x)` with `ℓ_T = -log U(Z_T)`. -/
theorem condLaw_le (hP : IsProb P) {T : Finset ι} (hu : 0 < prob P (avoid A T)) (x : ℕ) :
    prob P ({ω | eventNum A ω = x} ∩ avoid A T) / prob P (avoid A T) ≤
      Real.exp (-Real.log (prob P (avoid A T))) * lawOf P (eventNum A) x := by
  rw [Real.exp_neg, Real.exp_log hu, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (prob_mono hP Set.inter_subset_left) hu.le

omit [DecidableEq ι] in
/-- `∑_{x ≤ n} U({X = x} ∩ Z_T) g(x) = E[g(X) 1_{Z_T}]` (`results/vplusb-poly-contra.md`
(1b201a5), proof of Theorem 4 item 2). -/
theorem sum_prob_inter_avoid_mul (T : Finset ι) (g : ℕ → ℝ) :
    ∑ x ∈ range (Fintype.card ι + 1), prob P ({ω | eventNum A ω = x} ∩ avoid A T) * g x =
      ∑ ω, (avoid A T).indicator P ω * g (eventNum A ω) := by
  rw [sum_mul_lawOf ((avoid A T).indicator P) (eventNum_le A) g]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [lawOf, prob, prob]
  congr 1
  exact sum_congr rfl fun ω _ ↦ by rw [Set.indicator_indicator]

/-- Theorem 4 item 2 of `results/vplusb-poly-contra.md` (1b201a5), joint form:
`V_T + (M_T - c)² = E_T(X - c)² ≤ Φ(ℓ_T)`, with `Φ` taken for the law of `X` and
`ℓ_T = -log U(Z_T)`. -/
theorem condVar_add_sq_le_capVar (hP : IsProb P) {T : Finset ι} (hu : 0 < prob P (avoid A T))
    (c : ℝ) :
    condVar P A T + (condMean P A T - c) ^ 2 ≤
      capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T))) := by
  set u := prob P (avoid A T)
  set w : ℕ → ℝ := fun x ↦ prob P ({ω | eventNum A ω = x} ∩ avoid A T) / u
  have hE : Real.exp (-Real.log u) = 1 / u := by rw [Real.exp_neg, Real.exp_log hu, one_div]
  have hval : ∑ x ∈ range (Fintype.card ι + 1), w x * ((x : ℝ) - c) ^ 2 =
      condVar P A T + (condMean P A T - c) ^ 2 := by
    have h1 := sum_prob_inter_avoid_mul (P := P) (A := A) T (fun x ↦ ((x : ℝ) - c) ^ 2)
    have h2 := sum_avoid_mul_sq_sub hP (A := A) T hu.ne' c
    simp only [← eventCount_eq_eventNum] at h1
    simp only [w, div_mul_eq_mul_div, ← sum_div, h1, h2]
    field_simp
    rfl
  rw [← hval]
  refine le_csSup ⟨∑ x ∈ range (Fintype.card ι + 1),
    Real.exp (-Real.log u) * lawOf P (eventNum A) x * ((x : ℝ) - c) ^ 2, ?_⟩ ⟨w, ?_, ?_, ?_, rfl⟩
  · rintro v ⟨w', hw0, hwp, -, rfl⟩
    exact sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hwp x) (sq_nonneg _)
  · exact fun x ↦ div_nonneg (prob_nonneg hP _) hu.le
  · intro x
    rw [hE, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (prob_mono hP Set.inter_subset_left) hu.le
  · have h1 := sum_prob_inter_avoid_mul (P := P) (A := A) T (fun _ ↦ (1 : ℝ))
    simp only [mul_one] at h1
    simp only [w, ← sum_div, h1]
    exact div_self hu.ne'

/-- Theorem 4 item 2 of `results/vplusb-poly-contra.md` (1b201a5): `V_T ≤ Φ(ℓ_T)`. -/
theorem condVar_le_capVar (hP : IsProb P) {T : Finset ι} (hu : 0 < prob P (avoid A T)) (c : ℝ) :
    condVar P A T ≤
      capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T))) :=
  le_trans (le_add_of_nonneg_right (sq_nonneg _)) (condVar_add_sq_le_capVar hP hu c)

/-- Theorem 4 item 2 of `results/vplusb-poly-contra.md` (1b201a5): `|M_T - c| ≤ √Φ(ℓ_T)`. -/
theorem abs_condMean_sub_le (hP : IsProb P) {T : Finset ι} (hu : 0 < prob P (avoid A T))
    (c : ℝ) :
    |condMean P A T - c| ≤ Real.sqrt
      (capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T)))) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (le_trans (le_add_of_nonneg_left (condVar_nonneg hP T))
    (condVar_add_sq_le_capVar hP hu c))

/-- Theorem 4 item 3 of `results/vplusb-poly-contra.md` (1b201a5): if `f_s(T) ≤ φ < 1` for every
`s ∉ T`, `c > 0` and `Φ(ℓ_T) < c²`, then `V_T / B_T ≤ Φ(ℓ_T) / ((1 - φ)(c - √Φ(ℓ_T)))`. With
`c = μ` this is the source's statement. -/
theorem condVar_div_bernVarSum_le (hP : IsProb P) {T : Finset ι} (hu : 0 < prob P (avoid A T))
    {c φ : ℝ} (hc : 0 < c) (hφ : φ < 1) (hf : ∀ s ∉ T, condProb P A T s ≤ φ)
    (hΦ : capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T))) <
      c ^ 2) :
    condVar P A T / bernVarSum P A T ≤
      capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T))) /
        ((1 - φ) * (c - Real.sqrt (capVar (lawOf P (eventNum A)) (Fintype.card ι) c
          (-Real.log (prob P (avoid A T)))))) := by
  set Φ := capVar (lawOf P (eventNum A)) (Fintype.card ι) c (-Real.log (prob P (avoid A T)))
  have hV := condVar_le_capVar hP hu (A := A) c
  have hV0 := condVar_nonneg hP (A := A) T
  have hM := abs_condMean_sub_le hP hu (A := A) c
  have hs : Real.sqrt Φ < c := by
    rw [Real.sqrt_lt' hc]
    exact hΦ
  have hM' : c - Real.sqrt Φ ≤ condMean P A T := by
    have := neg_abs_le (condMean P A T - c)
    linarith
  have hB : (1 - φ) * condMean P A T ≤ bernVarSum P A T := by
    rw [condMean, mul_sum]
    exact sum_le_sum fun s hs ↦ by
      have := hf s (mem_compl.mp hs)
      nlinarith [condProb_nonneg hP (A := A) T s]
  have hden : 0 < (1 - φ) * (c - Real.sqrt Φ) := mul_pos (by linarith) (by linarith)
  have hB' : (1 - φ) * (c - Real.sqrt Φ) ≤ bernVarSum P A T :=
    (mul_le_mul_of_nonneg_left hM' (by linarith)).trans hB
  exact div_le_div₀ (hV0.trans hV) hV hden hB'

end Barrier

end Pairing
