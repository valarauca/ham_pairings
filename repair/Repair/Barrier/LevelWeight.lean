import Repair.BoundedRadius
import Suppression.MixtureBarrier

/-!
# Level-weight blindness (fbr-contra Theorem 1)

Source: `results/fbr-contra.md` (b2ea07c) §2.1, Theorem 1. The spike states it for the uniform law
`U` on perfect matchings and `Z = L_0 = {X = 0}`. Here it is stated for any probability weight
`P` on a finite set `Ω` (`ChainRule.IsProb`) and any event `Z`, with law `U(S) = prob P S` and
`q = U(Z)`. For `c > -1` the level-weight law is

  `ν_c = (1 + c 1_Z) U / (1 + c q)` (`boost P Z c`).

* `isProb_boost` : `ν_c` is a probability weight. `boost_of_mem`, `boost_of_notMem` (item 2) :
  `dν_c / dU` takes the two values `(1 + c) / (1 + c q)` on `Z` and `1 / (1 + c q)` off `Z`.
* `condLaw_boost_inter`, `condLaw_boost_compl` (item 1) : `ν_c(· | Z) = U(· | Z)` and
  `ν_c(· | Zᶜ) = U(· | Zᶜ)`.
* `boost_comp` (item 2) : every symmetry `g` of `(U, Z)` is a symmetry of `ν_c`. With `Z = L_0`
  and `g` an AGL(1, n) map this is the AGL(1, n)-invariance of the spike.
* For events `A : ι → Set Ω` with `Z ⊆ ⋂_t A_tᶜ` (no `A_t` occurs on `Z`; `Z = L_0` is the case
  of equality): `prob_interSet_boost`, `interRatio_boost` (item 3) :
  `U(∩_S A_t)` scales by `1 / (1 + c q)` and `R_S(ν_c) = (1 + c q)^(|S| - 1) R_S(U)` for
  nonempty `S`, `interRatio_div_pow_boost` : `R_S / R_{S₂}^(|S| - 1)` is unchanged for every pair
  `S₂`, and `sum_prob_boost` : `μ(ν_c) = μ / (1 + c q)`.
* For `X : Ω → ℕ` and `Z = {X = 0}`: `lawOf_boost` (the law of `X` under `ν_c`),
  `lawOf_boost_succ_div` (item 3) : `P_(k+1) / P_k` is unchanged for every `k ≥ 1`,
  `bottomRatio_boost` (item 4) : `ρ_j(ν_c) = ρ_j(U) F(j) (1 + c q) / (F(j) + c q)`, and
  `bottomRatio_zero_boost` : `ρ_0(ν_c) = ρ_0(U) (1 + c q) / (1 + c)`. Both hold with no extra
  hypothesis in Lean's conventions (`x / 0 = 0`), since `F(j) = 0` forces `q = 0` and both sides
  vanish.

`interSet A S = ⋂_{t ∈ S} A_t` and `interRatio P A S = U(∩_S A_t) / ∏_{t ∈ S} U(A_t)` are the
general forms of the `k`-point ratio. `jointRatio_eq_interRatio` identifies
`MixtureBarrier.jointRatio` with the instance `A_t = {t ∈ H}`.
-/

namespace Pairing

namespace Barrier

open Finset ChainRule

variable {Ω ι : Type*}

/-- `⋂_{t ∈ S} A_t`, the event that every `A_t` with `t ∈ S` occurs (`results/fbr-contra.md`
(b2ea07c) §2.1). -/
def interSet (A : ι → Set Ω) (S : Finset ι) : Set Ω :=
  {ω | ∀ t ∈ S, ω ∈ A t}

/-- The `|S|`-point ratio `R_S = U(∩_{t ∈ S} A_t) / ∏_{t ∈ S} U(A_t)` (`results/fbr-contra.md`
(b2ea07c) §2.1, Theorem 1 item 3). -/
noncomputable def interRatio [Fintype Ω] (P : Ω → ℝ) (A : ι → Set Ω) (S : Finset ι) : ℝ :=
  prob P (interSet A S) / ∏ t ∈ S, prob P (A t)

/-- `MixtureBarrier.jointRatio` is `interRatio` for the events `A_t = {t ∈ H}`
(`results/fbr-contra.md` (b2ea07c) §2.1). -/
theorem jointRatio_eq_interRatio {n : ℕ} (w : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    MixtureBarrier.jointRatio w S = interRatio w (fun t ↦ {H | t ∈ H}) S := by
  rfl

/-- The level-weight law `ν_c = (1 + c 1_Z) U / (1 + c U(Z))` of Theorem 1 of
`results/fbr-contra.md` (b2ea07c) §2.1. -/
noncomputable def boost [Fintype Ω] (P : Ω → ℝ) (Z : Set Ω) (c : ℝ) (ω : Ω) : ℝ :=
  (1 + c * Z.indicator 1 ω) * P ω / (1 + c * prob P Z)

variable [Fintype Ω] {P : Ω → ℝ} {Z : Set Ω} {c : ℝ}

/-- `1 + c q > 0` for `c > -1` and `0 ≤ q ≤ 1` (`results/fbr-contra.md` (b2ea07c), Theorem 1). -/
theorem one_add_mul_prob_pos (hP : IsProb P) (hc : -1 < c) (Z : Set Ω) :
    0 < 1 + c * prob P Z := by
  have h0 := prob_nonneg hP Z
  have h1 := prob_le_one hP Z
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 + c)]

/-- `ν_c(S) = (U(S) + c U(Z ∩ S)) / (1 + c q)` (`results/fbr-contra.md` (b2ea07c), proof of
Theorem 1). -/
theorem prob_boost (P : Ω → ℝ) (Z S : Set Ω) (c : ℝ) :
    prob (boost P Z c) S = (prob P S + c * prob P (Z ∩ S)) / (1 + c * prob P Z) := by
  set D := 1 + c * prob P Z
  have e : ∀ ω, S.indicator (boost P Z c) ω =
      (S.indicator P ω + c * (Z ∩ S).indicator P ω) / D := by
    intro ω
    by_cases hS : ω ∈ S
    · by_cases hZ : ω ∈ Z
      · simp only [Set.indicator, boost, hS, hZ, Set.mem_inter_iff, and_self, ↓reduceIte,
          Pi.one_apply, D]
        ring
      · simp [Set.indicator, boost, hS, hZ, D]
    · simp [Set.indicator, hS]
  rw [prob, sum_congr rfl fun ω _ ↦ e ω, ← sum_div, sum_add_distrib, ← mul_sum]
  rfl

/-- Theorem 1 of `results/fbr-contra.md` (b2ea07c): `ν_c` is a probability weight for `c > -1`. -/
theorem isProb_boost (hP : IsProb P) (hc : -1 < c) (Z : Set Ω) : IsProb (boost P Z c) where
  nonneg ω := by
    have hD := one_add_mul_prob_pos hP hc Z
    refine div_nonneg (mul_nonneg ?_ (hP.nonneg ω)) hD.le
    by_cases h : ω ∈ Z
    · simp only [Set.indicator, h, ↓reduceIte, Pi.one_apply, mul_one]
      linarith
    · simp [Set.indicator, h]
  sum_eq_one := by
    have h := prob_boost P Z Set.univ c
    rw [Set.inter_univ, prob_univ hP, div_self (one_add_mul_prob_pos hP hc Z).ne'] at h
    simpa [prob] using h

/-- Theorem 1 item 2 of `results/fbr-contra.md` (b2ea07c): on `Z`,
`dν_c / dU = (1 + c) / (1 + c q)`. -/
theorem boost_of_mem {ω : Ω} (h : ω ∈ Z) :
    boost P Z c ω = (1 + c) / (1 + c * prob P Z) * P ω := by
  simp only [boost, Set.indicator_of_mem h, Pi.one_apply, mul_one]
  ring

/-- Theorem 1 item 2 of `results/fbr-contra.md` (b2ea07c): off `Z`, `dν_c / dU = 1 / (1 + c q)`. -/
theorem boost_of_notMem {ω : Ω} (h : ω ∉ Z) :
    boost P Z c ω = 1 / (1 + c * prob P Z) * P ω := by
  simp only [boost, Set.indicator_of_notMem h, mul_zero, add_zero, one_mul]
  ring

/-- Theorem 1 item 2 of `results/fbr-contra.md` (b2ea07c): every map `g` that preserves `U`
pointwise and maps `Z` and its complement into themselves preserves `ν_c`. For the uniform law
and `Z = L_0` this is the AGL(1, n)-invariance of `ν_c`. -/
theorem boost_comp {g : Ω → Ω} (hPg : ∀ ω, P (g ω) = P ω) (hZg : ∀ ω, g ω ∈ Z ↔ ω ∈ Z)
    (ω : Ω) : boost P Z c (g ω) = boost P Z c ω := by
  by_cases h : ω ∈ Z
  · rw [boost_of_mem ((hZg ω).2 h), boost_of_mem h, hPg]
  · rw [boost_of_notMem (mt (hZg ω).1 h), boost_of_notMem h, hPg]

/-- Theorem 1 item 1 of `results/fbr-contra.md` (b2ea07c): `ν_c(· | Z) = U(· | Z)`. -/
theorem condLaw_boost_inter (hP : IsProb P) (hc : -1 < c) (S : Set Ω) :
    prob (boost P Z c) (Z ∩ S) / prob (boost P Z c) Z = prob P (Z ∩ S) / prob P Z := by
  have hD := (one_add_mul_prob_pos hP hc Z).ne'
  have h1 : (1 + c) ≠ 0 := by linarith
  rw [prob_boost, prob_boost, ← Set.inter_assoc, Set.inter_self, div_div_div_cancel_right₀ hD]
  rw [show prob P (Z ∩ S) + c * prob P (Z ∩ S) = (1 + c) * prob P (Z ∩ S) by ring,
    show prob P Z + c * prob P Z = (1 + c) * prob P Z by ring, mul_div_mul_left _ _ h1]

/-- Theorem 1 item 1 of `results/fbr-contra.md` (b2ea07c): `ν_c(· | Zᶜ) = U(· | Zᶜ)`. -/
theorem condLaw_boost_compl (hP : IsProb P) (hc : -1 < c) (S : Set Ω) :
    prob (boost P Z c) (Zᶜ ∩ S) / prob (boost P Z c) Zᶜ = prob P (Zᶜ ∩ S) / prob P Zᶜ := by
  have hD := (one_add_mul_prob_pos hP hc Z).ne'
  have e1 : Z ∩ (Zᶜ ∩ S) = ∅ := by
    rw [← Set.inter_assoc, Set.inter_compl_self, Set.empty_inter]
  have e2 : Z ∩ Zᶜ = ∅ := Set.inter_compl_self Z
  rw [prob_boost, prob_boost, e1, e2, div_div_div_cancel_right₀ hD]
  simp [prob]

/-- `ν_c(S) = U(S) / (1 + c q)` for every event `S` disjoint from `Z`
(`results/fbr-contra.md` (b2ea07c), proof of Theorem 1 item 3). -/
theorem prob_boost_of_disjoint {S : Set Ω} (h : Z ∩ S = ∅) :
    prob (boost P Z c) S = prob P S / (1 + c * prob P Z) := by
  rw [prob_boost, h]
  simp [prob]

omit [Fintype Ω] in
/-- `∩_{t ∈ S} A_t` is disjoint from `Z ⊆ ⋂_t A_tᶜ` for nonempty `S` (`results/fbr-contra.md`
(b2ea07c), proof of Theorem 1 item 3). -/
theorem inter_interSet_eq_empty [Fintype ι] {A : ι → Set Ω} (hZ : Z ⊆ avoid A univ)
    {S : Finset ι} (hS : S.Nonempty) : Z ∩ interSet A S = ∅ := by
  obtain ⟨t, ht⟩ := hS
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hω h ↦ hZ hω t (mem_univ t) (h t ht)

/-- Theorem 1 item 3 of `results/fbr-contra.md` (b2ea07c): for nonempty `S`,
`ν_c(∩_S A_t) = U(∩_S A_t) / (1 + c q)`, when no `A_t` occurs on `Z`. -/
theorem prob_interSet_boost [Fintype ι] {A : ι → Set Ω} (hZ : Z ⊆ avoid A univ) {S : Finset ι}
    (hS : S.Nonempty) :
    prob (boost P Z c) (interSet A S) = prob P (interSet A S) / (1 + c * prob P Z) :=
  prob_boost_of_disjoint (inter_interSet_eq_empty hZ hS)

/-- `ν_c(A_t) = U(A_t) / (1 + c q)` when no `A_t` occurs on `Z` (`results/fbr-contra.md`
(b2ea07c), proof of Theorem 1 item 3). -/
theorem prob_boost_event [Fintype ι] {A : ι → Set Ω} (hZ : Z ⊆ avoid A univ) (t : ι) :
    prob (boost P Z c) (A t) = prob P (A t) / (1 + c * prob P Z) := by
  have h := prob_interSet_boost (P := P) (c := c) hZ (singleton_nonempty t)
  have e : interSet A {t} = A t := by
    ext ω
    simp [interSet]
  rwa [e] at h

/-- Theorem 1 item 3 of `results/fbr-contra.md` (b2ea07c): `μ(ν_c) = μ / (1 + c q)`. -/
theorem sum_prob_boost [Fintype ι] {A : ι → Set Ω} (hZ : Z ⊆ avoid A univ) :
    ∑ t, prob (boost P Z c) (A t) = (∑ t, prob P (A t)) / (1 + c * prob P Z) := by
  rw [sum_div]
  exact sum_congr rfl fun t _ ↦ prob_boost_event hZ t

/-- Theorem 1 item 3 of `results/fbr-contra.md` (b2ea07c): for nonempty `S`,
`R_S(ν_c) = (1 + c q)^(|S| - 1) R_S(U)`, when no `A_t` occurs on `Z`. -/
theorem interRatio_boost [Fintype ι] (hP : IsProb P) (hc : -1 < c) {A : ι → Set Ω}
    (hZ : Z ⊆ avoid A univ) {S : Finset ι} (hS : S.Nonempty) :
    interRatio (boost P Z c) A S = (1 + c * prob P Z) ^ (S.card - 1) * interRatio P A S := by
  have hD := (one_add_mul_prob_pos hP hc Z).ne'
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by have := hS.card_pos; omega⟩
  rw [interRatio, interRatio, prob_interSet_boost hZ hS,
    prod_congr rfl fun t _ ↦ prob_boost_event hZ t, prod_div_distrib, prod_const, hk,
    Nat.add_sub_cancel, pow_succ]
  by_cases hpr : ∏ t ∈ S, prob P (A t) = 0
  · simp [hpr]
  · field_simp

/-- Theorem 1 item 3 of `results/fbr-contra.md` (b2ea07c): the normalized ratio
`R_S / R_{S₂}^(|S| - 1)` is the same under `ν_c` and `U`, for nonempty `S` and every pair `S₂`,
when no `A_t` occurs on `Z`. -/
theorem interRatio_div_pow_boost [Fintype ι] (hP : IsProb P) (hc : -1 < c) {A : ι → Set Ω}
    (hZ : Z ⊆ avoid A univ) {S S₂ : Finset ι} (hS : S.Nonempty) (hS₂ : S₂.card = 2) :
    interRatio (boost P Z c) A S / interRatio (boost P Z c) A S₂ ^ (S.card - 1) =
      interRatio P A S / interRatio P A S₂ ^ (S.card - 1) := by
  have hD := (one_add_mul_prob_pos hP hc Z).ne'
  have h2 : S₂.Nonempty := card_pos.mp (by omega)
  rw [interRatio_boost hP hc hZ hS, interRatio_boost hP hc hZ h2, hS₂, mul_pow, pow_one,
    mul_div_mul_left _ _ (pow_ne_zero _ hD)]

/-- The law of `X` under `ν_c` with `Z = {X = 0}` (`results/fbr-contra.md` (b2ea07c), proof of
Theorem 1 items 3 and 4): `ν_c(X = k) = (U(X = k) + [k = 0] c q) / (1 + c q)`. -/
theorem lawOf_boost (P : Ω → ℝ) (X : Ω → ℕ) (c : ℝ) (k : ℕ) :
    lawOf (boost P {ω | X ω = 0} c) X k =
      (lawOf P X k + if k = 0 then c * lawOf P X 0 else 0) / (1 + c * lawOf P X 0) := by
  rw [lawOf, prob_boost]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lawOf]
  · have e : {ω | X ω = 0} ∩ {ω | X ω = k} = ∅ := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        exact absurd ((show X ω = 0 from h1).symm.trans h2) hk.ne
      · rintro ⟨⟩
    simp [e, prob, lawOf, hk.ne']

/-- Theorem 1 item 3 of `results/fbr-contra.md` (b2ea07c): with `Z = {X = 0}`, every level
ratio `P_(k+1) / P_k` with `k ≥ 1` is the same under `ν_c` and `U`. -/
theorem lawOf_boost_succ_div (hP : IsProb P) (hc : -1 < c) (X : Ω → ℕ) {k : ℕ} (hk : 1 ≤ k) :
    lawOf (boost P {ω | X ω = 0} c) X (k + 1) / lawOf (boost P {ω | X ω = 0} c) X k =
      lawOf P X (k + 1) / lawOf P X k := by
  have hD := (one_add_mul_prob_pos hP hc {ω | X ω = 0}).ne'
  rw [lawOf_boost, lawOf_boost, ite_eq_right (by omega), ite_eq_right (by omega), add_zero,
    add_zero]
  exact div_div_div_cancel_right₀ hD _ _

/-- `F_ν(j) = (F(j) + c q) / (1 + c q)` for the law of `X` under `ν_c`, `Z = {X = 0}`
(`results/fbr-contra.md` (b2ea07c), proof of Theorem 1 item 4). -/
theorem cdf_lawOf_boost (P : Ω → ℝ) (X : Ω → ℕ) (c : ℝ) (j : ℕ) :
    SizeBias.cdf (lawOf (boost P {ω | X ω = 0} c) X) j =
      (SizeBias.cdf (lawOf P X) j + c * lawOf P X 0) / (1 + c * lawOf P X 0) := by
  simp only [SizeBias.cdf, lawOf_boost, ← sum_div, sum_add_distrib]
  rw [sum_ite_eq' (range (j + 1)) 0, ite_eq_left (by simp)]

/-- `G_ν(j) = G(j) / (1 + c q)` for the law of `X` under `ν_c`, `Z = {X = 0}`
(`results/fbr-contra.md` (b2ea07c), proof of Theorem 1 item 4). -/
theorem partialMean_lawOf_boost (P : Ω → ℝ) (X : Ω → ℕ) (c : ℝ) (j : ℕ) :
    SizeBias.partialMean (lawOf (boost P {ω | X ω = 0} c) X) j =
      SizeBias.partialMean (lawOf P X) j / (1 + c * lawOf P X 0) := by
  simp only [SizeBias.partialMean, lawOf_boost, sum_div]
  refine sum_congr rfl fun k _ ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [ite_eq_right hk.ne', add_zero, mul_div_assoc]

/-- Theorem 1 item 4 of `results/fbr-contra.md` (b2ea07c): with `Z = {X = 0}`,
`ρ_j(ν_c) = ρ_j(U) F(j) (1 + c q) / (F(j) + c q)` for every `j` and every `N`. -/
theorem bottomRatio_boost (hP : IsProb P) (hc : -1 < c) (X : Ω → ℕ) (N j : ℕ) :
    SizeBias.bottomRatio (lawOf (boost P {ω | X ω = 0} c) X) N j =
      SizeBias.bottomRatio (lawOf P X) N j *
        (SizeBias.cdf (lawOf P X) j * (1 + c * lawOf P X 0) /
          (SizeBias.cdf (lawOf P X) j + c * lawOf P X 0)) := by
  have hD : 0 < 1 + c * lawOf P X 0 := one_add_mul_prob_pos hP hc {ω | X ω = 0}
  have hq0 : 0 ≤ lawOf P X 0 := prob_nonneg hP _
  have hqF : lawOf P X 0 ≤ SizeBias.cdf (lawOf P X) j := by
    rw [SizeBias.cdf]
    exact single_le_sum (f := lawOf P X) (fun k _ ↦ prob_nonneg hP _) (by simp)
  rw [SizeBias.bottomRatio, SizeBias.bottomRatio, partialMean_lawOf_boost, partialMean_lawOf_boost,
    cdf_lawOf_boost]
  set q := lawOf P X 0
  set F := SizeBias.cdf (lawOf P X) j
  set G := SizeBias.partialMean (lawOf P X) (j + 1)
  set μ := SizeBias.partialMean (lawOf P X) N
  rcases eq_or_lt_of_le (hq0.trans hqF) with hF | hF
  · have hq : q = 0 := le_antisymm (hF ▸ hqF) hq0
    rw [← hF, hq]
    simp
  rcases eq_or_ne μ 0 with hμ | hμ
  · simp [hμ]
  have hFc : 0 < F + c * q := by nlinarith [mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ 1 + c)]
  field_simp

/-- Theorem 1 item 4 of `results/fbr-contra.md` (b2ea07c) at `j = 0`: with `Z = {X = 0}`,
`ρ_0(ν_c) = ρ_0(U) (1 + c q) / (1 + c)`. -/
theorem bottomRatio_zero_boost (hP : IsProb P) (hc : -1 < c) (X : Ω → ℕ) (N : ℕ) :
    SizeBias.bottomRatio (lawOf (boost P {ω | X ω = 0} c) X) N 0 =
      SizeBias.bottomRatio (lawOf P X) N 0 * ((1 + c * lawOf P X 0) / (1 + c)) := by
  rw [bottomRatio_boost hP hc]
  have hF : SizeBias.cdf (lawOf P X) 0 = lawOf P X 0 := by simp [SizeBias.cdf]
  rw [hF]
  rcases eq_or_ne (lawOf P X 0) 0 with hq | hq
  · simp [SizeBias.bottomRatio, SizeBias.cdf, hq]
  have h1 : (1 + c) ≠ 0 := by linarith
  congr 1
  rw [show lawOf P X 0 + c * lawOf P X 0 = lawOf P X 0 * (1 + c) by ring,
    mul_div_mul_left _ _ hq]

end Barrier

end Pairing
