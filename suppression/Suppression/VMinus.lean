import Suppression.Reweighted
import Suppression.Tilt

/-!
# The (V−) side of the re-weighted ordering (COD-198)

A follow-up to `Reweighted.lean` (COD-215), in its notation: `V_T = condVar`, `B_T = bernVarSum`,
`D_T = condSlack`, `L_T = entSum`, `M_T = condMean`, `μ = ∑_t U(A_t)`, `q = U(Z_ι)` and the
`(1 - f)`-weighted ordering `reweight`. `X = eventCount A`, and `eventNum A` is the same count as
a natural number, so that `lawOf P (eventNum A)` is the law of `X` and `Tilt.lean` applies to it.

From `cod-198-attempt.md` (COD-198):

* `neg_log_le_div_add_sum`, `neg_log_le_div_add_of_le_condVar`,
  `neg_log_le_div_add_of_le_condVar_condMean` (Corollary 4(ii), (iii)) : (V−) `V_T ≥ c L_T`, or
  (V−_M) `V_T ≥ c M_T`, for every `T` with `⌊δ / p⌋ ≤ |T| ≤ n - 1` gives `-log q ≤ μ / c + C_δ`
  with `C_δ = μ δ / ((1 - δ - p)(μ - δ))`. No pair-ratio bound is needed, since the low levels
  use `L_T ≤ M_T` and not a bound on `V_T`.
* `pow_eventNum_eq_sum` (Section 4.3 of COD-190) : `w^X = ∑_T (1 - w)^|T| w^(n - |T|) 1_{Z_T}`.
* `mul_tiltMean_le_tiltVar`, `fano_le_one_sub_of_le_condVar` (Corollary 4(iv)) : (V−_M) for every
  `T` gives `Var_w X ≥ c E_w X` on `(0, 1]` for the law of `X`, which is the hypothesis
  `Δ(w) ≤ δ` of COD-190 with `δ = 1 - c`.
* `exp_neg_div_le_prob_avoid_of_le_condVar`, `neg_log_le_div_of_le_condVar` : with the Fano
  criterion of COD-177 (`Tilt.exp_neg_div_le_of_fano_le`), (V−_M) for every `T` and `c > 0` give
  `q ≥ exp(-μ / c)`.
* `sum_corrLevel_le_harmonic`, `div_le_neg_log_prob_avoid_of_reweight_harmonic`,
  `neg_log_prob_avoid_le_div_of_reweight_harmonic` and their `pairInfo` forms (Corollary 5) :
  Theorem 7 of COD-196 through Theorem 3 with `η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`,
  `H_n = ∑_{N=2}^n 1 / N`. `harmonic_le_log` is `H_n ≤ log n`, and
  `div_le_neg_log_prob_avoid_of_reweight'`, `neg_log_prob_avoid_le_div_of_reweight'` recover the
  `log n` forms of `Reweighted.lean` from the `H_n` forms.
-/

namespace Pairing

namespace ChainRule

open Finset

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

section Corollary4ii

/-- Corollary 4(ii) of COD-198 (`cod-198-attempt.md`), general form. Assume `q > 0`, `c > 0`,
`L_T / D_T ≤ b(|T|)` for `|T| < k₀`, and (V−) `c L_T ≤ V_T` for every `T ≠ ι` with `k₀ ≤ |T|`.
Then `-log q ≤ μ / c + ∑_{k < min(k₀, n)} b(k)`. -/
theorem neg_log_le_div_add_sum (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {c : ℝ}
    (hc : 0 < c) {k₀ : ℕ} {b : ℕ → ℝ}
    (hlow : ∀ T : Finset ι, T.card < k₀ → T ≠ univ → entSum P A T / condSlack P A T ≤ b T.card)
    (hV : ∀ T : Finset ι, k₀ ≤ T.card → T ≠ univ → c * entSum P A T ≤ condVar P A T) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t)) / c + ∑ k ∈ range (min k₀ (Fintype.card ι)), b k := by
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  set h : ℕ → ℝ := fun i ↦ if i < k₀ then b i else 0 with hh
  have hpt : ∀ T : Finset ι, ∀ s, s ∉ T → entSum P A T / condSlack P A T ≤
      h T.card + c⁻¹ * (condVar P A T / condSlack P A T) := by
    intro T s hs
    have hT : T ≠ univ := fun e ↦ hs (e ▸ mem_univ s)
    have hD := condSlack_pos hP hq (A := A) hT
    have hV0 : 0 ≤ c⁻¹ * (condVar P A T / condSlack P A T) :=
      mul_nonneg (inv_nonneg.2 hc.le) (div_nonneg (condVar_nonneg hP T) hD.le)
    simp only [hh]
    by_cases h1 : T.card < k₀
    · simp only [h1, ↓reduceIte]
      linarith [hlow T h1 hT]
    · simp only [h1, ↓reduceIte, zero_add]
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hD.le
      rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hV T (not_lt.mp h1) hT
  have hmono := kerExp_mono (w := reweight P A) (fun T s _ ↦ reweight_nonneg hP T s) hpt
    (Fintype.card ι) ∅
  rw [kerExp_reweight_entSum hP hq, kerExp_add, kerExp_const_mul,
    kerExp_card hw h _ ∅ (by rw [compl_empty, card_univ]), kerExp_reweight_condVar hP hq,
    card_empty] at hmono
  simp only [zero_add, hh] at hmono
  have e1 : ∑ i ∈ range (Fintype.card ι), (if i < k₀ then b i else 0) =
      ∑ k ∈ range (min k₀ (Fintype.card ι)), b k := by
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range, lt_min_iff]
    omega
  rw [e1] at hmono
  rw [div_eq_inv_mul]
  linarith

omit [DecidableEq ι] in
/-- The proof of Corollary 4 of COD-198 (`cod-198-attempt.md`): if `U(A_t) ≤ p`, `p > 0`,
`δ ≥ 0` and `δ < μ`, then `k₀ = ⌊δ / p⌋ < n`. -/
theorem floor_div_lt_card {p δ : ℝ} (hp : ∀ t, prob P (A t) ≤ p) (hp0 : 0 < p)
    (hδ0 : 0 ≤ δ) (hμ : δ < ∑ t, prob P (A t)) : ⌊δ / p⌋₊ < Fintype.card ι := by
  have hfl : (⌊δ / p⌋₊ : ℝ) * p ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ0 hp0.le)
    rwa [le_div_iff₀ hp0] at this
  have hμn : ∑ t, prob P (A t) ≤ Fintype.card ι * p :=
    calc ∑ t, prob P (A t) ≤ ∑ _t : ι, p := sum_le_sum fun t _ ↦ hp t
      _ = Fintype.card ι * p := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hk₀n : (⌊δ / p⌋₊ : ℝ) < Fintype.card ι := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h hp0.le]
  exact_mod_cast hk₀n

omit [DecidableEq ι] in
/-- The low levels of Corollary 4 of COD-198 (`cod-198-attempt.md`): if `U(A_t) ≤ p`, `p > 0`,
`δ ≥ 0`, `δ + p < 1`, `δ < μ` and `V ≥ 0`, then
`∑_{k < ⌊δ / p⌋} V / ((1 - δ - p)(n - k)) ≤ V δ / ((1 - δ - p)(μ - δ))`. -/
theorem sum_range_floor_div_le {p δ V : ℝ} (hp : ∀ t, prob P (A t) ≤ p)
    (hp0 : 0 < p) (hδ0 : 0 ≤ δ) (hδp : δ + p < 1) (hμ : δ < ∑ t, prob P (A t)) (hV : 0 ≤ V) :
    ∑ k ∈ range ⌊δ / p⌋₊, V / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k)) ≤
      V * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) := by
  have ha : 0 < 1 - δ - p := by linarith
  have hfl : (⌊δ / p⌋₊ : ℝ) * p ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ0 hp0.le)
    rwa [le_div_iff₀ hp0] at this
  have hμn : ∑ t, prob P (A t) ≤ Fintype.card ι * p :=
    calc ∑ t, prob P (A t) ≤ ∑ _t : ι, p := sum_le_sum fun t _ ↦ hp t
      _ = Fintype.card ι * p := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hk₀n : (⌊δ / p⌋₊ : ℝ) < Fintype.card ι := by
    exact_mod_cast floor_div_lt_card hp hp0 hδ0 hμ
  have hnk : (0 : ℝ) < Fintype.card ι - ⌊δ / p⌋₊ := by linarith
  have h1 : ∀ k ∈ range ⌊δ / p⌋₊, V / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k)) ≤
      V / ((1 - δ - p) * ((Fintype.card ι : ℝ) - ⌊δ / p⌋₊)) := fun k hk ↦ by
    have : (k : ℝ) < ⌊δ / p⌋₊ := by exact_mod_cast mem_range.mp hk
    exact div_le_div_of_nonneg_left hV (mul_pos ha hnk)
      (mul_le_mul_of_nonneg_left (by linarith) ha.le)
  refine (sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [card_range, nsmul_eq_mul, mul_div_assoc',
    div_le_div_iff₀ (mul_pos ha hnk) (mul_pos ha (by linarith))]
  have hkey : (⌊δ / p⌋₊ : ℝ) * ∑ t, prob P (A t) ≤ δ * Fintype.card ι := by
    nlinarith [mul_le_mul_of_nonneg_left hμn (Nat.cast_nonneg ⌊δ / p⌋₊),
      mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (Fintype.card ι))]
  nlinarith [mul_nonneg (mul_nonneg hV ha.le) (sub_nonneg.2 hkey)]

/-- The proof of Corollary 4 of COD-198 (`cod-198-attempt.md`), low levels: if `U(A_t) ≤ p`,
`p > 0`, `δ ≥ 0`, `δ + p < 1`, `|T| < ⌊δ / p⌋` and `T ≠ ι`, then
`M_T / D_T ≤ μ / ((1 - δ - p) N_T)`, from `U(Z_T) ≥ 1 - δ`, `M_T U(Z_T) ≤ μ` and
`D_T (1 - δ) ≥ N_T (1 - δ - p)`. -/
theorem condMean_div_condSlack_le (hP : IsProb P) {p δ : ℝ} (hp : ∀ t, prob P (A t) ≤ p)
    (hp0 : 0 < p) (hδ0 : 0 ≤ δ) (hδp : δ + p < 1) {T : Finset ι} (hT : T.card < ⌊δ / p⌋₊)
    (hTu : T ≠ univ) :
    condMean P A T / condSlack P A T ≤
      (∑ t, prob P (A t)) / ((1 - δ - p) * ((Fintype.card ι : ℝ) - T.card)) := by
  have ha : 0 < 1 - δ - p := by linarith
  have hδ1 : 0 < 1 - δ := by linarith
  have hfl : (⌊δ / p⌋₊ : ℝ) * p ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ0 hp0.le)
    rwa [le_div_iff₀ hp0] at this
  have hTp : (T.card : ℝ) * p ≤ δ := by
    have : (T.card : ℝ) ≤ ⌊δ / p⌋₊ := by exact_mod_cast hT.le
    nlinarith
  have hU : 1 - δ ≤ prob P (avoid A T) := by
    have h1 := one_sub_sum_le_prob_avoid hP (A := A) T
    have h2 : ∑ u ∈ T, prob P (A u) ≤ T.card * p :=
      calc ∑ u ∈ T, prob P (A u) ≤ ∑ _u ∈ T, p := sum_le_sum fun u _ ↦ hp u
        _ = T.card * p := by rw [sum_const, nsmul_eq_mul]
    linarith
  have hf : ∀ s, condProb P A T s ≤ p / (1 - δ) := fun s ↦
    (condProb_le_div hP hp hp0.le (by linarith) s).trans
      (div_le_div_of_nonneg_left hp0.le hδ1 (by linarith))
  have hN : (Tᶜ.card : ℝ) = Fintype.card ι - T.card := by
    rw [card_compl, Nat.cast_sub (card_le_univ T)]
  have hNpos : (0 : ℝ) < Tᶜ.card := by
    have : 0 < Tᶜ.card :=
      card_pos.mpr (by rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]; exact hTu)
    exact_mod_cast this
  have hD : Tᶜ.card * (1 - δ - p) ≤ condSlack P A T * (1 - δ) := by
    have h1 : ∑ s ∈ Tᶜ, (1 - p / (1 - δ)) ≤ condSlack P A T :=
      sum_le_sum fun s _ ↦ by linarith [hf s]
    rw [sum_const, nsmul_eq_mul] at h1
    have e : (1 - p / (1 - δ)) * (1 - δ) = 1 - δ - p := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hδ1.ne']
    nlinarith [mul_le_mul_of_nonneg_right h1 hδ1.le]
  have hDpos : 0 < condSlack P A T := by nlinarith [mul_pos hNpos ha]
  have hMU : condMean P A T * prob P (avoid A T) ≤ ∑ t, prob P (A t) := by
    rw [condMean, sum_mul]
    calc ∑ s ∈ Tᶜ, condProb P A T s * prob P (avoid A T) ≤ ∑ s ∈ Tᶜ, prob P (A s) :=
          sum_le_sum fun s _ ↦ by
            rw [condProb_mul_prob hP]
            exact prob_mono hP Set.inter_subset_left
      _ ≤ ∑ t, prob P (A t) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun t _ _ ↦ prob_nonneg hP _
  have hM := condMean_nonneg hP (A := A) T
  have hMδ : condMean P A T * (1 - δ) ≤ ∑ t, prob P (A t) :=
    (mul_le_mul_of_nonneg_left hU hM).trans hMU
  rw [← hN, div_le_div_iff₀ hDpos (mul_pos ha hNpos)]
  nlinarith [mul_le_mul_of_nonneg_left hD hM, mul_le_mul_of_nonneg_left hMδ hDpos.le]

/-- Corollary 4(ii) of COD-198 (`cod-198-attempt.md`). Assume `q > 0`, `c > 0`, `U(A_t) ≤ p`
with `p > 0`, `δ ≥ 0`, `δ + p < 1`, `δ < μ`, and (V−) `c L_T ≤ V_T` for every `T` with
`⌊δ / p⌋ ≤ |T| ≤ n - 1`. Then `-log q ≤ μ / c + C_δ` with
`C_δ = μ δ / ((1 - δ - p)(μ - δ))`. The paper writes `C_δ = (1 + o(1)) / (1 - δ)`; here
`C_δ → δ / (1 - δ)` as `μ → ∞` and `p → 0`, with no pair-ratio hypothesis, because the levels
`|T| < ⌊δ / p⌋` are bounded through `L_T ≤ M_T ≤ μ / (1 - δ)`. -/
theorem neg_log_le_div_add_of_le_condVar (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {p δ c : ℝ} (hp : ∀ t, prob P (A t) ≤ p) (hp0 : 0 < p) (hδ0 : 0 ≤ δ) (hδp : δ + p < 1)
    (hμ : δ < ∑ t, prob P (A t)) (hc : 0 < c)
    (hV : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → T ≠ univ → c * entSum P A T ≤ condVar P A T) :
    -Real.log (prob P (avoid A univ)) ≤ (∑ t, prob P (A t)) / c +
      (∑ t, prob P (A t)) * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) := by
  have hk := floor_div_lt_card hp hp0 hδ0 hμ
  have hgen := neg_log_le_div_add_sum hP hq hc (k₀ := ⌊δ / p⌋₊)
    (b := fun k ↦ (∑ t, prob P (A t)) / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k)))
    (fun T hT hTu ↦ (div_le_div_of_nonneg_right (entSum_le_condMean hP T)
      (condSlack_nonneg hP T)).trans (condMean_div_condSlack_le hP hp hp0 hδ0 hδp hT hTu)) hV
  rw [min_eq_left hk.le] at hgen
  have hs := sum_range_floor_div_le hp hp0 hδ0 hδp hμ (V := ∑ t, prob P (A t))
    (sum_nonneg fun t _ ↦ prob_nonneg hP (A t))
  linarith

/-- Corollary 4(iii) of COD-198 (`cod-198-attempt.md`), (V−) side: the clean form (V−_M)
`V_T ≥ c M_T` on the window `⌊δ / p⌋ ≤ |T| ≤ n - 1` implies (V−) there, since `L_T ≤ M_T`, and so
gives the bound of `neg_log_le_div_add_of_le_condVar`. -/
theorem neg_log_le_div_add_of_le_condVar_condMean (hP : IsProb P)
    (hq : 0 < prob P (avoid A univ)) {p δ c : ℝ} (hp : ∀ t, prob P (A t) ≤ p) (hp0 : 0 < p)
    (hδ0 : 0 ≤ δ) (hδp : δ + p < 1) (hμ : δ < ∑ t, prob P (A t)) (hc : 0 < c)
    (hV : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → T ≠ univ → c * condMean P A T ≤ condVar P A T) :
    -Real.log (prob P (avoid A univ)) ≤ (∑ t, prob P (A t)) / c +
      (∑ t, prob P (A t)) * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) :=
  neg_log_le_div_add_of_le_condVar hP hq hp hp0 hδ0 hδp hμ hc fun T h1 h2 ↦
    (mul_le_mul_of_nonneg_left (entSum_le_condMean hP T) hc.le).trans (hV T h1 h2)

end Corollary4ii

section Corollary4iv

omit [DecidableEq ι] in
open Classical in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): `X(ω) = #{t : ω ∈ A_t}` as a natural
number, so that `lawOf P (eventNum A)` is the law of `X`. -/
noncomputable def eventNum (A : ι → Set Ω) (ω : Ω) : ℕ :=
  (univ.filter fun t ↦ ω ∈ A t).card

omit [Fintype Ω] [DecidableEq ι] in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): `X = eventNum`. -/
theorem eventCount_eq_eventNum (A : ι → Set Ω) (ω : Ω) : eventCount A ω = eventNum A ω := by
  classical
  rw [eventCount, eventNum, natCast_card_filter]
  exact sum_congr rfl fun t _ ↦ by simp [Set.indicator_apply]

omit [Fintype Ω] [DecidableEq ι] in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): `X ≤ n`. -/
theorem eventNum_le (A : ι → Set Ω) (ω : Ω) : eventNum A ω ≤ Fintype.card ι :=
  card_le_univ _

omit [Fintype Ω] [DecidableEq ι] in
/-- Section 4.3 of COD-190 (`cod-190-delta-proof-attempt.md`), used for Corollary 4(iv) of
COD-198 (`cod-198-attempt.md`): `w^X = ∑_T (1 - w)^|T| w^(n - |T|) 1_{Z_T}`, so the `w^X`-tilt
of `U` is a mixture of the laws `U(· | Z_T)` with weights `∝ (1 - w)^|T| w^(n - |T|) U(Z_T)`. -/
theorem pow_eventNum_eq_sum (A : ι → Set Ω) (w : ℝ) (ω : Ω) :
    w ^ eventNum A ω = ∑ T : Finset ι, (1 - w) ^ T.card * w ^ (Fintype.card ι - T.card) *
      (avoid A T).indicator (1 : Ω → ℝ) ω := by
  classical
  set S := univ.filter fun t ↦ ω ∉ A t with hS
  have hmem : ∀ T : Finset ι, ω ∈ avoid A T ↔ T ⊆ S := fun T ↦ by
    simp [avoid, subset_iff, hS]
  have hcard : eventNum A ω + S.card = Fintype.card ι := by
    rw [eventNum, hS, ← card_univ]
    convert card_filter_add_card_filter_not (s := univ) (fun t ↦ ω ∈ A t)
  have e : ∀ T : Finset ι, (1 - w) ^ T.card * w ^ (Fintype.card ι - T.card) *
      (avoid A T).indicator (1 : Ω → ℝ) ω =
        if T ⊆ S then (1 - w) ^ T.card * w ^ (S.card - T.card) * w ^ eventNum A ω else 0 := by
    intro T
    by_cases hT : T ⊆ S
    · simp only [hT, ↓reduceIte]
      rw [Set.indicator_of_mem ((hmem T).2 hT), Pi.one_apply, mul_one, mul_assoc, ← pow_add]
      have := card_le_card hT
      congr 2
      omega
    · simp only [hT, ↓reduceIte]
      rw [Set.indicator_of_notMem (fun h ↦ hT ((hmem T).1 h)), mul_zero]
  have hpw : univ.filter (fun T : Finset ι ↦ T ⊆ S) = S.powerset := by
    ext T
    simp
  rw [sum_congr rfl fun T _ ↦ e T, ← sum_filter, hpw, ← sum_mul, sum_pow_mul_eq_add_pow,
    sub_add_cancel, one_pow, one_mul]

omit [DecidableEq ι] in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): the law of `X` has
`M_r(w) = ∑_ω P(ω) X(ω)^r w^X(ω)`. -/
theorem tiltSum_lawOf_eventNum (P : Ω → ℝ) (A : ι → Set Ω) (r : ℕ) (w : ℝ) :
    Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) r w =
      ∑ ω, P ω * (eventCount A ω ^ r * w ^ eventNum A ω) := by
  simp only [eventCount_eq_eventNum]
  rw [sum_mul_lawOf P (eventNum_le A) fun k ↦ (k : ℝ) ^ r * w ^ k, Tilt.tiltSum]
  exact sum_congr rfl fun k _ ↦ by ring

omit [DecidableEq ι] in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): the law of `X` has `U(X = 0) = q`. -/
theorem lawOf_eventNum_zero (P : Ω → ℝ) (A : ι → Set Ω) :
    lawOf P (eventNum A) 0 = prob P (avoid A univ) := by
  rw [lawOf]
  congr 1
  ext ω
  simp [eventNum, avoid, filter_eq_empty_iff]

omit [DecidableEq ι] in
/-- For Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): the law of `X` has mean `μ`. -/
theorem partialMean_lawOf_eventNum (hP : IsProb P) :
    SizeBias.partialMean (lawOf P (eventNum A)) (Fintype.card ι) = ∑ t, prob P (A t) := by
  classical
  have h := sum_avoid_mul_eventCount hP (A := A) ∅
  rw [avoid_empty, Set.indicator_univ, prob_univ hP, mul_one, condMean_empty hP] at h
  rw [← h, SizeBias.partialMean]
  simp only [eventCount_eq_eventNum]
  rw [sum_mul_lawOf P (eventNum_le A) fun k ↦ (k : ℝ)]
  exact sum_congr rfl fun k _ ↦ mul_comm _ _

/-- The proof of Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): if `0 ≤ w ≤ 1` and
`c M_T ≤ V_T` for every `T ≠ ι`, then `c E[X w^X] ≤ E[(X - a)² w^X]` for every `a`. By
`pow_eventNum_eq_sum` both sides are mixtures over `T` with weights `(1 - w)^|T| w^(n - |T|)`,
and `E[(X - a)² 1_{Z_T}] ≥ V_T U(Z_T) ≥ c M_T U(Z_T) = c E[X 1_{Z_T}]`. -/
theorem mul_sum_pow_le_sum_pow_sq (hP : IsProb P) {c w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hV : ∀ T : Finset ι, T ≠ univ → c * condMean P A T ≤ condVar P A T) (a : ℝ) :
    c * ∑ ω, P ω * (eventCount A ω * w ^ eventNum A ω) ≤
      ∑ ω, P ω * ((eventCount A ω - a) ^ 2 * w ^ eventNum A ω) := by
  have hα0 : ∀ T : Finset ι, 0 ≤ (1 - w) ^ T.card * w ^ (Fintype.card ι - T.card) := fun T ↦
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hw0 _)
  have hmix : ∀ g : Ω → ℝ, ∑ ω, P ω * (g ω * w ^ eventNum A ω) =
      ∑ T : Finset ι, (1 - w) ^ T.card * w ^ (Fintype.card ι - T.card) *
        ∑ ω, (avoid A T).indicator P ω * g ω := by
    intro g
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [pow_eventNum_eq_sum A w ω, mul_sum, mul_sum]
    refine sum_congr rfl fun T _ ↦ ?_
    by_cases h : ω ∈ avoid A T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  have hT : ∀ T : Finset ι, c * (condMean P A T * prob P (avoid A T)) ≤
      ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 := by
    intro T
    have hS : 0 ≤ ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 :=
      sum_nonneg fun ω _ ↦ mul_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω)
        (sq_nonneg _)
    by_cases hz : prob P (avoid A T) = 0
    · rw [hz, mul_zero, mul_zero]
      exact hS
    have e : ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 =
        condVar P A T * prob P (avoid A T) := by
      rw [condVar, div_mul_cancel₀ _ hz]
    rw [e, ← mul_assoc]
    by_cases hu : T = univ
    · rw [hu, condMean_univ, mul_zero, zero_mul]
      exact mul_nonneg (condVar_nonneg hP _) (prob_nonneg hP _)
    · exact mul_le_mul_of_nonneg_right (hV T hu) (prob_nonneg hP _)
  rw [hmix (eventCount A), hmix fun ω ↦ (eventCount A ω - a) ^ 2, mul_sum]
  refine sum_le_sum fun T _ ↦ ?_
  rw [sum_avoid_mul_eventCount hP T, mul_left_comm]
  exact mul_le_mul_of_nonneg_left ((hT T).trans (sum_avoid_sq_le hP T a)) (hα0 T)

/-- Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): if (V−_M) `c M_T ≤ V_T` holds for every
`T ≠ ι`, then the law of `X` has `Var_w X ≥ c E_w X` for every `w ∈ (0, 1]`. The proof is the law
of total variance for the mixture of `pow_eventNum_eq_sum`, as in the paper. -/
theorem mul_tiltMean_le_tiltVar (hP : IsProb P) {c : ℝ}
    (hV : ∀ T : Finset ι, T ≠ univ → c * condMean P A T ≤ condVar P A T) {w : ℝ}
    (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    c * Tilt.tiltMean (lawOf P (eventNum A)) (Fintype.card ι) w ≤
      Tilt.tiltVar (lawOf P (eventNum A)) (Fintype.card ι) w := by
  have hlaw := isLaw_lawOf hP (eventNum_le A)
  have hG := Tilt.genFun_pos_of_pos hlaw hw.1
  have e0 : Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w =
      ∑ ω, P ω * w ^ eventNum A ω := by
    rw [Tilt.genFun_eq_tiltSum, tiltSum_lawOf_eventNum]
    simp
  have e1 := tiltSum_lawOf_eventNum P A 1 w
  have e2 := tiltSum_lawOf_eventNum P A 2 w
  simp only [pow_one] at e1
  have hexp : ∀ m : ℝ, ∑ ω, P ω * ((eventCount A ω - m) ^ 2 * w ^ eventNum A ω) =
      ∑ ω, P ω * (eventCount A ω ^ 2 * w ^ eventNum A ω) -
        2 * m * ∑ ω, P ω * (eventCount A ω * w ^ eventNum A ω) +
          m ^ 2 * ∑ ω, P ω * w ^ eventNum A ω := by
    intro m
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ ↦ by ring
  have h := mul_sum_pow_le_sum_pow_sq hP hw.1.le hw.2 hV
    (Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 1 w /
      Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w)
  rw [hexp, ← e0, ← e1, ← e2] at h
  have key : Tilt.tiltVar (lawOf P (eventNum A)) (Fintype.card ι) w -
      c * Tilt.tiltMean (lawOf P (eventNum A)) (Fintype.card ι) w =
        (Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 2 w -
          2 * (Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 1 w /
            Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w) *
              Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 1 w +
          (Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 1 w /
            Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w) ^ 2 *
              Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w -
          c * Tilt.tiltSum (lawOf P (eventNum A)) (Fintype.card ι) 1 w) /
            Tilt.genFun (lawOf P (eventNum A)) (Fintype.card ι) w := by
    rw [Tilt.tiltVar, Tilt.tiltMean]
    field_simp
    ring
  have := div_nonneg (sub_nonneg.2 h) hG.le
  linarith

/-- Corollary 4(iv) of COD-198 (`cod-198-attempt.md`): under (V−_M) `c M_T ≤ V_T` for every
`T ≠ ι`, the law of `X` satisfies the hypothesis `Δ(w) ≤ δ` of COD-190 with `δ = 1 - c` at every
`w ∈ (0, 1]` with `E_w X > 0`. -/
theorem fano_le_one_sub_of_le_condVar (hP : IsProb P) {c : ℝ}
    (hV : ∀ T : Finset ι, T ≠ univ → c * condMean P A T ≤ condVar P A T) {w : ℝ}
    (hw : w ∈ Set.Ioc (0 : ℝ) 1)
    (hE : 0 < Tilt.tiltMean (lawOf P (eventNum A)) (Fintype.card ι) w) :
    Tilt.fano (lawOf P (eventNum A)) (Fintype.card ι) w ≤ 1 - c := by
  rw [Tilt.fano, sub_le_sub_iff_left, le_div_iff₀ hE]
  exact mul_tiltMean_le_tiltVar hP hV hw

/-- Corollary 4(iv) of COD-198 (`cod-198-attempt.md`) with the Fano criterion of COD-177
(`Tilt.exp_neg_div_le_of_fano_le`): if `c > 0` and (V−_M) `c M_T ≤ V_T` for every `T ≠ ι`, then
`q ≥ exp(-μ / c)`. No hypothesis `q > 0` is needed. -/
theorem exp_neg_div_le_prob_avoid_of_le_condVar (hP : IsProb P) {c : ℝ} (hc : 0 < c)
    (hV : ∀ T : Finset ι, T ≠ univ → c * condMean P A T ≤ condVar P A T) :
    Real.exp (-((∑ t, prob P (A t)) / c)) ≤ prob P (avoid A univ) := by
  have hlaw := isLaw_lawOf hP (eventNum_le A)
  rw [← partialMean_lawOf_eventNum hP, ← lawOf_eventNum_zero, ← sub_sub_cancel 1 c]
  by_cases hk : ∃ k, 0 < k ∧ 0 < lawOf P (eventNum A) k
  · exact Tilt.exp_neg_div_le_of_fano_le hlaw (by linarith) fun w hw _ ↦
      fano_le_one_sub_of_le_condVar hP hV hw (Tilt.tiltMean_pos hlaw hk hw.1)
  · obtain ⟨h0, hμ⟩ := Tilt.eq_one_and_partialMean_eq_zero hlaw hk
    rw [h0, hμ]
    simp

/-- Corollary 4(iv) of COD-198 (`cod-198-attempt.md`) in the form of Corollary 4(ii): if `c > 0`
and (V−_M) `c M_T ≤ V_T` for every `T ≠ ι`, then `-log q ≤ μ / c`, with no `C_δ`. -/
theorem neg_log_le_div_of_le_condVar (hP : IsProb P) {c : ℝ} (hc : 0 < c)
    (hV : ∀ T : Finset ι, T ≠ univ → c * condMean P A T ≤ condVar P A T) :
    -Real.log (prob P (avoid A univ)) ≤ (∑ t, prob P (A t)) / c := by
  have h := exp_neg_div_le_prob_avoid_of_le_condVar hP hc hV
  have h2 := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp] at h2
  linarith

end Corollary4iv

section Corollary5

/-- For Corollary 5 of COD-198 (`cod-198-attempt.md`): `∑_{N=2}^n g(N) = ∑_{j < n - 1} g(j + 2)`. -/
theorem sum_Icc_two_eq (g : ℕ → ℝ) (n : ℕ) :
    ∑ N ∈ Icc 2 n, g N = ∑ j ∈ range (n - 1), g (j + 2) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  exact sum_congr (by congr 1) fun j _ ↦ by rw [add_comm]

/-- For Corollary 5 of COD-198 (`cod-198-attempt.md`): `H_n = ∑_{N=2}^n 1 / N ≤ log n`, so the
`H_n` form of `η` implies the `log n` form. -/
theorem harmonic_le_log (n : ℕ) : ∑ N ∈ Icc 2 n, (1 : ℝ) / N ≤ Real.log n := by
  rw [sum_Icc_two_eq (fun N ↦ (1 : ℝ) / N)]
  push_cast
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have := sum_inv_add_two_le_log (n - 1)
    rwa [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at this

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`): the level corrections of Theorem 7 of COD-196
sum to at most `4 J H_n + K (K + 1) φ / 2`, with `H_n = ∑_{N=2}^n 1 / N`. No sign of `J` is
needed. -/
theorem sum_corr_le_harmonic (n K : ℕ) {J φ : ℝ} (hφ : 0 ≤ φ) :
    ∑ i ∈ range (n - 1), (4 * J / ((n - i : ℕ) : ℝ) +
      if n - i ≤ K + 1 then (((n - i : ℕ) : ℝ) - 1) * φ else 0) ≤
        4 * J * ∑ N ∈ Icc 2 n, (1 : ℝ) / N + K * (K + 1) * φ / 2 := by
  have h0 := sum_corr_le n K (J := 0) le_rfl hφ
  simp only [mul_zero, zero_mul, zero_div, zero_add] at h0
  have e : ∑ i ∈ range (n - 1), 4 * J / ((n - i : ℕ) : ℝ) =
      4 * J * ∑ N ∈ Icc 2 n, (1 : ℝ) / N := by
    rw [sum_range_reflect_two (fun N ↦ 4 * J / (N : ℝ)), sum_Icc_two_eq (fun N ↦ (1 : ℝ) / N),
      mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [sum_add_distrib, e]
  linarith

/-- The allowances of Corollary 5 of COD-198 (`cod-198-attempt.md`) sum to at most
`η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`, with `H_n = ∑_{N=2}^n 1 / N`. -/
theorem sum_corrLevel_le_harmonic (n K : ℕ) {J φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    ∑ i ∈ range n, corrLevel n K J φ i ≤
      (4 * J * ∑ N ∈ Icc 2 n, (1 : ℝ) / N + K * (K + 1) * φ / 2) / (1 - φ) := by
  have e : ∑ i ∈ range n, corrLevel n K J φ i = (∑ i ∈ range (n - 1), (4 * J /
      ((n - i : ℕ) : ℝ) + if n - i ≤ K + 1 then (((n - i : ℕ) : ℝ) - 1) * φ else 0)) /
        (1 - φ) := by
    rw [sum_div]
    simp only [corrLevel]
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [e]
  exact div_le_div_of_nonneg_right (sum_corr_le_harmonic n K hφ0) (by linarith)

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`), as stated: Theorem 7(i) of COD-196 through
Theorem 3. Under (A) `f_t(T) ≤ φ < 1` and (B′) `∑_{s ≠ t ∉ T} |Cov_T(s, t)| ≤ 2 √J M_T + 4 J` for
`N_T ≥ K + 2`, `-log q ≥ (μ - η) / (1 + θ)` with `θ = 2 √J / (1 - φ)` and
`η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`, `H_n = ∑_{N=2}^n 1 / N`. -/
theorem div_le_neg_log_prob_avoid_of_reweight_harmonic (hP : IsProb P) {φ J : ℝ} {K : ℕ}
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    (∑ t, prob P (A t) - (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N +
      K * (K + 1) * φ / 2) / (1 - φ)) / (1 + 2 * √J / (1 - φ)) ≤
        -Real.log (prob P (avoid A univ)) := by
  have hq := prob_avoid_pos hP hφ1 hA
  have h1φ : 0 < 1 - φ := by linarith
  have hθ : 0 ≤ 2 * √J / (1 - φ) := div_nonneg (by positivity) h1φ.le
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  have hpt : ∀ T : Finset ι, ∀ s, s ∉ T → condVar P A T / condSlack P A T ≤
      (1 + 2 * √J / (1 - φ)) * (bernVarSum P A T / condSlack P A T) +
        corrLevel (Fintype.card ι) K J φ T.card := by
    intro T s hs
    have hT : T ≠ univ := fun e ↦ hs (e ▸ mem_univ s)
    have hDpos := condSlack_pos hP hq (A := A) hT
    obtain ⟨h1, h2⟩ := abs_condVar_sub_le_and_div_le hP hφ0 hφ1 hJ hA hB hT
    have h3 := mul_condMean_le_bernVarSum hP hA T
    have hM : 2 * √J * condMean P A T ≤ 2 * √J / (1 - φ) * bernVarSum P A T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1φ]
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * √J)]
    have hV : condVar P A T ≤ (1 + 2 * √J / (1 - φ)) * bernVarSum P A T +
        (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) := by
      linarith [(abs_le.mp h1).2]
    calc condVar P A T / condSlack P A T ≤ ((1 + 2 * √J / (1 - φ)) * bernVarSum P A T +
          (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ)) /
            condSlack P A T := div_le_div_of_nonneg_right hV hDpos.le
      _ = (1 + 2 * √J / (1 - φ)) * (bernVarSum P A T / condSlack P A T) +
          (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) /
            condSlack P A T := by ring
      _ ≤ _ := by linarith
  have hmono := kerExp_mono (w := reweight P A) (fun T s _ ↦ reweight_nonneg hP T s) hpt
    (Fintype.card ι) ∅
  rw [kerExp_reweight_condVar hP hq, kerExp_add, kerExp_const_mul,
    kerExp_card hw (corrLevel (Fintype.card ι) K J φ) _ ∅ (by rw [compl_empty, card_univ]),
    card_empty] at hmono
  simp only [zero_add] at hmono
  have hS := kerExp_bernVarSum_le_neg_log hP hq
  have hη := sum_corrLevel_le_harmonic (Fintype.card ι) K (J := J) hφ0 hφ1
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 1 + 2 * √J / (1 - φ))]

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`), as stated: Theorem 7(ii) of COD-196 through
Theorem 3. Under the hypotheses of `div_le_neg_log_prob_avoid_of_reweight_harmonic`, if `θ < 1`,
then `-log q ≤ (μ + η) / ((1 - φ)(1 - θ))` with `η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`. -/
theorem neg_log_prob_avoid_le_div_of_reweight_harmonic (hP : IsProb P) {φ J : ℝ} {K : ℕ}
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J)
    (hθ1 : 2 * √J / (1 - φ) < 1) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t) + (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N +
        K * (K + 1) * φ / 2) / (1 - φ)) / ((1 - φ) * (1 - 2 * √J / (1 - φ))) := by
  have hq := prob_avoid_pos hP hφ1 hA
  have h1φ : 0 < 1 - φ := by linarith
  have hc : 0 < (1 - φ) * (1 - 2 * √J / (1 - φ)) := mul_pos h1φ (by linarith)
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  have hpt : ∀ T : Finset ι, ∀ s, s ∉ T → condMean P A T / condSlack P A T ≤
      (1 / ((1 - φ) * (1 - 2 * √J / (1 - φ)))) * (condVar P A T / condSlack P A T) +
        (1 / ((1 - φ) * (1 - 2 * √J / (1 - φ)))) * corrLevel (Fintype.card ι) K J φ T.card := by
    intro T s hs
    have hT : T ≠ univ := fun e ↦ hs (e ▸ mem_univ s)
    have hDpos := condSlack_pos hP hq (A := A) hT
    obtain ⟨h1, h2⟩ := abs_condVar_sub_le_and_div_le hP hφ0 hφ1 hJ hA hB hT
    have h3 := mul_condMean_le_bernVarSum hP hA T
    have e : (1 - φ) * (1 - 2 * √J / (1 - φ)) = 1 - φ - 2 * √J := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ h1φ.ne']
    have hV : (1 - φ) * (1 - 2 * √J / (1 - φ)) * condMean P A T ≤ condVar P A T +
        (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) := by
      rw [e]
      linarith [(abs_le.mp h1).1]
    rw [← mul_add, div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, div_mul_eq_mul_div,
      div_le_iff₀ hDpos]
    have h4 : condVar P A T + (if K + 2 ≤ Tᶜ.card then 4 * J else
        Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) ≤ (condVar P A T / condSlack P A T +
          corrLevel (Fintype.card ι) K J φ T.card) * condSlack P A T := by
      rw [add_mul, div_mul_cancel₀ _ hDpos.ne']
      have := (div_le_iff₀ hDpos).mp h2
      linarith
    nlinarith
  have hmono := kerExp_mono (w := reweight P A) (fun T s _ ↦ reweight_nonneg hP T s) hpt
    (Fintype.card ι) ∅
  rw [kerExp_add, kerExp_const_mul, kerExp_const_mul (G := fun T _ ↦
    corrLevel (Fintype.card ι) K J φ T.card), kerExp_reweight_condVar hP hq,
    kerExp_card hw (corrLevel (Fintype.card ι) K J φ) _ ∅ (by rw [compl_empty, card_univ]),
    card_empty] at hmono
  simp only [zero_add] at hmono
  have hS := neg_log_le_kerExp_condMean hP hq
  have hη := sum_corrLevel_le_harmonic (Fintype.card ι) K (J := J) hφ0 hφ1
  rw [le_div_iff₀ hc]
  have h5 : -Real.log (prob P (avoid A univ)) ≤ 1 / ((1 - φ) * (1 - 2 * √J / (1 - φ))) *
      (∑ t, prob P (A t) + (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N +
        K * (K + 1) * φ / 2) / (1 - φ)) := by
    have := mul_le_mul_of_nonneg_left hη (one_div_nonneg.mpr hc.le)
    linarith
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc] at h5
  exact h5

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`) with hypothesis (B) `J_T ≤ J` of Theorem 7 of
COD-196, `H_n` form: `-log q ≥ (μ - η) / (1 + θ)` with
`η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`. -/
theorem div_le_neg_log_prob_avoid_of_pairInfo_of_reweight_harmonic (hP : IsProb P) {φ J : ℝ}
    {K : ℕ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hJ : 0 ≤ J)
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card → pairInfo P A T ≤ J) :
    (∑ t, prob P (A t) - (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N +
      K * (K + 1) * φ / 2) / (1 - φ)) / (1 + 2 * √J / (1 - φ)) ≤
        -Real.log (prob P (avoid A univ)) :=
  div_le_neg_log_prob_avoid_of_reweight_harmonic hP hφ0 hφ1 hJ hA (hB'_of_pairInfo hP hB)

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`) with hypothesis (B) `J_T ≤ J` of Theorem 7 of
COD-196, `H_n` form: if `θ < 1`, then `-log q ≤ (μ + η) / ((1 - φ)(1 - θ))` with
`η = (4 J H_n + K (K + 1) φ / 2) / (1 - φ)`. -/
theorem neg_log_prob_avoid_le_div_of_pairInfo_of_reweight_harmonic (hP : IsProb P) {φ J : ℝ}
    {K : ℕ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hJ : 0 ≤ J)
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card → pairInfo P A T ≤ J)
    (hθ1 : 2 * √J / (1 - φ) < 1) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t) + (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N +
        K * (K + 1) * φ / 2) / (1 - φ)) / ((1 - φ) * (1 - 2 * √J / (1 - φ))) :=
  neg_log_prob_avoid_le_div_of_reweight_harmonic hP hφ0 hφ1 hJ hA (hB'_of_pairInfo hP hB) hθ1

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`), the `log n` form of
`div_le_neg_log_prob_avoid_of_reweight`, derived from the `H_n` form through `H_n ≤ log n`. -/
theorem div_le_neg_log_prob_avoid_of_reweight' (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    (∑ t, prob P (A t) - (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ)) /
        (1 + 2 * √J / (1 - φ)) ≤ -Real.log (prob P (avoid A univ)) := by
  refine le_trans ?_ (div_le_neg_log_prob_avoid_of_reweight_harmonic hP hφ0 hφ1 hJ hA hB)
  have h1φ : 0 < 1 - φ := by linarith
  refine div_le_div_of_nonneg_right ?_ (add_nonneg zero_le_one (div_nonneg (by positivity) h1φ.le))
  have h1 := mul_le_mul_of_nonneg_left (harmonic_le_log (Fintype.card ι))
    (by positivity : (0 : ℝ) ≤ 4 * J)
  have h2 : (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N + K * (K + 1) * φ / 2) /
      (1 - φ) ≤ (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ) :=
    div_le_div_of_nonneg_right (by linarith) h1φ.le
  linarith

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`), the `log n` form of
`neg_log_prob_avoid_le_div_of_reweight`, derived from the `H_n` form through `H_n ≤ log n`. -/
theorem neg_log_prob_avoid_le_div_of_reweight' (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J)
    (hθ1 : 2 * √J / (1 - φ) < 1) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t) + (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) /
        (1 - φ)) / ((1 - φ) * (1 - 2 * √J / (1 - φ))) := by
  refine (neg_log_prob_avoid_le_div_of_reweight_harmonic hP hφ0 hφ1 hJ hA hB hθ1).trans ?_
  have h1φ : 0 < 1 - φ := by linarith
  refine div_le_div_of_nonneg_right ?_ (mul_pos h1φ (by linarith)).le
  have h1 := mul_le_mul_of_nonneg_left (harmonic_le_log (Fintype.card ι))
    (by positivity : (0 : ℝ) ≤ 4 * J)
  have h2 : (4 * J * ∑ N ∈ Icc 2 (Fintype.card ι), (1 : ℝ) / N + K * (K + 1) * φ / 2) /
      (1 - φ) ≤ (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ) :=
    div_le_div_of_nonneg_right (by linarith) h1φ.le
  linarith

end Corollary5

end ChainRule

end Pairing
