import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Suppression.HamCount

/-!
# Tilted-law reductions (COD-177)

Let `p` be a law on `ℕ` supported on `[0, N]` (`SizeBias.IsLaw p N`), usually with some
`p k > 0` for `k ≥ 1` (the standing assumption `hk`), and put `μ = partialMean p N`. For
`w ∈ (0, 1]` the `w^X`-tilted law is `P_w(X = k) = p k w^k / G(w)` with `G(w) = ∑ p k w^k`.
Write `E_w X`, `Var_w X` and `E_w[X(X - 1)]` for its mean, variance and second factorial moment,
`Δ(w) = 1 - Var_w X / E_w X`, `R(z) = G'(z) / (μ G(z))` and
`D(w) = μ (1 - E_w[X(X - 1)] / (E_w X)²)`.

* `tiltMean_eq_deriv` : `E_w X = w G'(w) / G(w)`.
* `hasDerivAt_log_tiltMean` (Lemma 1(2)) : `(log E_w X)' = (1 - Δ(w)) / w`.
* `integral_tiltMean_div` (Lemma 1(1)) : `-log p 0 = ∫_0^1 E_w X dw / w`, for `p 0 > 0`.
* `fano_le_tiltMean` (Lemma 1(3)) : `Δ(w) ≤ E_w X`.
* `hasDerivAt_inv_sbRatio`, `fano_eq_mul_pairDeficit` (Lemma 1(4)) : `(1 / R)' = D` and
  `Δ(w) = (E_w X / μ) D(w)`.
* `tiltMean_le` : `E_w X ≤ μ` on `(0, 1]`.
* `tiltMean_le_rpow`, `mul_rpow_le_tiltMean` : `Δ ≤ δ` on `(0, 1]` gives `E_w X ≤ μ w^(1 - δ)`,
  and `Δ ≥ δ` gives `E_w X ≥ μ w^(1 - δ)`.
* `exp_sub_le_of_tiltMean_div_le`, `le_exp_sub_of_le_tiltMean_div` : the comparison that every
  reduction to `p 0` below goes through. Since `(log G)' = E_w X / w` and `G(1) = 1`, a bound
  `E_x X / x ≤ φ'(x)` on `(0, 1)` gives `p 0 ≥ exp(φ(0) - φ(1))`, and the reverse bound gives
  `p 0 ≤ exp(φ(0) - φ(1))`. Neither needs `p 0 > 0`.
* `eq_one_and_partialMean_eq_zero` : without the standing assumption, `p` is the point mass at
  `0`. The Proposition 4 and 5(1), 5(3) bounds below that are named by their conclusion hold for
  every law on `[0, N]` and treat that case directly.
* `exp_neg_div_le_of_fano_le` (Proposition 4, the Fano criterion) : if `δ < 1` and `Δ(w) ≤ δ`
  wherever `E_w X ≥ δ`, then `p 0 ≥ exp(-μ / (1 - δ))`. The paper's `δ ≥ 0`, `p 0 > 0` and the
  standing assumption are not needed.
* `le_exp_neg_div_of_le_fano` : if `δ < 1` and `Δ ≥ δ` on `(0, 1]`, then
  `p 0 ≤ exp(-μ / (1 - δ))`. At `δ = 0` it is `le_exp_neg_of_fano_nonneg` (Section 4),
  `p 0 ≤ exp(-μ)`.
* `fano_le_mul_tiltMean`, `fano_le_of_pairDeficit_le` (Proposition 5(2)) : if `D ≤ c` on
  `(0, 1]`, then `Δ(w) ≤ c E_w X / μ`, and `Δ(w) ≤ c` when `c ≥ 0`.
* `sbRatio_le_of_pairDeficit_le`, `partialMean_one_le` (Proposition 5(1)) : if also `c < 1`, then
  `R(z) ≤ 1 / (1 - c (1 - z))` on `[0, 1]` and `ρ_0 ≤ 1 / (1 - c)`.
* `exp_neg_mul_log_le_of_pairDeficit_le`, `exp_neg_div_le_of_pairDeficit_le` (Proposition 5(3),
  the pair criterion) : for `0 < c < 1`,
  `p 0 ≥ exp(-(μ / c) log(1 / (1 - c))) ≥ exp(-μ / (1 - c))`.

For the round-robin count `X = hamCount m` and its law `hamLaw m`:

* `sum_hamCount_mul` : `∑_P X(P) f(X P) = n ∑_{P | A_0} f(X P)`, from `card_ham_and_eq_mul`.
* `sum_pow_mul_hamCount_pair` (Lemma 2) :
  `∑_P w^X(P) X(P) (X(P) - 1) = n ∑_{P | A_0} w^X(P) (X(P) - 1)`.
* `tiltMean_hamLaw` (Lemma 2(2)) : `E_w X = n U_w(A_0)`.
* `fano_hamLaw` (Lemma 2(2)) : `Δ(w) = E_w X - E_w[X' | A_0]` with `X' = X - 1`, for every
  `m ≥ 1`.
-/

namespace Pairing

namespace Tilt

open Finset SizeBias

/-- `G(w) = ∑_{k ≤ N} p k w^k`, the generating function of a law supported on `[0, N]`. -/
def genFun (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), p k * w ^ k

/-- `G'(z) = ∑_{k ≤ N} k p k z^(k - 1)`. -/
def genDeriv (p : ℕ → ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), (k : ℝ) * p k * z ^ (k - 1)

/-- `M_r(w) = ∑_{k ≤ N} k^r p k w^k`. `M_r(w) / G(w)` is the `r`-th moment of the `w^X`-tilted
law `P_w(X = k) = p k w^k / G(w)`, and `M_1(w) = w G'(w)`. -/
def tiltSum (p : ℕ → ℝ) (N r : ℕ) (w : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), (k : ℝ) ^ r * p k * w ^ k

/-- `E_w X = M_1(w) / G(w)`, the mean of the `w^X`-tilted law. It equals `w G'(w) / G(w)`
(`tiltMean_eq_deriv`). -/
noncomputable def tiltMean (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  tiltSum p N 1 w / genFun p N w

/-- `Var_w X = M_2(w) / G(w) - (E_w X)²`, the variance of the `w^X`-tilted law. -/
noncomputable def tiltVar (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  tiltSum p N 2 w / genFun p N w - tiltMean p N w ^ 2

/-- `E_w[X(X - 1)] = (M_2(w) - M_1(w)) / G(w)`, the second factorial moment of the tilted law. -/
noncomputable def tiltPair (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  (tiltSum p N 2 w - tiltSum p N 1 w) / genFun p N w

/-- `Δ(w) = 1 - Var_w X / E_w X`, the Fano deficit of the tilted law. -/
noncomputable def fano (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  1 - tiltVar p N w / tiltMean p N w

variable {p : ℕ → ℝ} {N : ℕ}

/-- `G = M_0`. -/
theorem genFun_eq_tiltSum (p : ℕ → ℝ) (N : ℕ) : genFun p N = tiltSum p N 0 := by
  funext w
  simp [genFun, tiltSum]

/-- `M_r'(w) = M_(r + 1)(w) / w` for `w ≠ 0`. -/
theorem hasDerivAt_tiltSum (p : ℕ → ℝ) (N r : ℕ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (tiltSum p N r) (tiltSum p N (r + 1) w / w) w := by
  refine (HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k w).const_mul ((k : ℝ) ^ r * p k)).congr_deriv ?_
  rw [tiltSum, sum_div]
  refine sum_congr rfl fun k _ ↦ ?_
  rcases k with _ | k
  · simp
  · rw [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

/-- `G'(z) = genDeriv p N z` for every `z`. -/
theorem hasDerivAt_genFun (p : ℕ → ℝ) (N : ℕ) (z : ℝ) :
    HasDerivAt (genFun p N) (genDeriv p N z) z := by
  refine (HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k z).const_mul (p k)).congr_deriv ?_
  exact sum_congr rfl fun k _ ↦ by ring

/-- `deriv G = genDeriv`. -/
theorem deriv_genFun (p : ℕ → ℝ) (N : ℕ) : deriv (genFun p N) = genDeriv p N :=
  funext fun z ↦ (hasDerivAt_genFun p N z).deriv

/-- `G'(z) = M_1(z) / z` for `z ≠ 0`. -/
theorem genDeriv_eq (p : ℕ → ℝ) (N : ℕ) {z : ℝ} (hz : z ≠ 0) :
    genDeriv p N z = tiltSum p N 1 z / z := by
  have h := hasDerivAt_tiltSum p N 0 hz
  rw [← genFun_eq_tiltSum] at h
  exact (hasDerivAt_genFun p N z).unique h

/-- `E_w X = w G'(w) / G(w)`. -/
theorem tiltMean_eq_deriv (p : ℕ → ℝ) (N : ℕ) {w : ℝ} (hw : w ≠ 0) :
    tiltMean p N w = w * deriv (genFun p N) w / genFun p N w := by
  rw [deriv_genFun, genDeriv_eq p N hw, mul_div_cancel₀ _ hw, tiltMean]

/-- `G` is continuous. -/
theorem continuous_genFun (p : ℕ → ℝ) (N : ℕ) : Continuous (genFun p N) :=
  continuous_finsetSum _ fun k _ ↦ continuous_const.mul (continuous_pow k)

/-- `G'` is continuous. -/
theorem continuous_genDeriv (p : ℕ → ℝ) (N : ℕ) : Continuous (genDeriv p N) :=
  continuous_finsetSum _ fun _ _ ↦ continuous_const.mul (continuous_pow _)

/-- `G(0) = p 0`. -/
theorem genFun_zero (p : ℕ → ℝ) (N : ℕ) : genFun p N 0 = p 0 := by
  simp [genFun, sum_range_succ']

/-- `G(1) = 1`. -/
theorem genFun_one (hp : IsLaw p N) : genFun p N 1 = 1 := by
  simpa [genFun] using hp.sum_eq_one

/-- `M_1(1) = μ`. -/
theorem tiltSum_one_one (p : ℕ → ℝ) (N : ℕ) : tiltSum p N 1 1 = partialMean p N := by
  simp [tiltSum, partialMean]

/-- `G'(0) = p 1`. -/
theorem genDeriv_zero (hp : IsLaw p N) : genDeriv p N 0 = p 1 := by
  rw [genDeriv, sum_eq_single 1]
  · simp
  · intro k _ hk
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel, zero_pow (by omega), mul_zero]
  · intro h
    rw [hp.eq_zero 1 (by simpa using h)]
    simp

/-- `G(w) ≥ p 0` for `w ≥ 0`. -/
theorem le_genFun (hp : IsLaw p N) {w : ℝ} (hw : 0 ≤ w) : p 0 ≤ genFun p N w := by
  simpa [genFun] using single_le_sum (f := fun k ↦ p k * w ^ k)
    (fun k _ ↦ mul_nonneg (hp.nonneg k) (pow_nonneg hw k)) (mem_range.mpr (Nat.succ_pos N))

/-- `G(w) > 0` for `w ≥ 0` when `p 0 > 0`. -/
theorem genFun_pos (hp : IsLaw p N) (hp0 : 0 < p 0) {w : ℝ} (hw : 0 ≤ w) : 0 < genFun p N w :=
  hp0.trans_le (le_genFun hp hw)

/-- `G(w) > 0` for `w > 0`. -/
theorem genFun_pos_of_pos (hp : IsLaw p N) {w : ℝ} (hw : 0 < w) : 0 < genFun p N w := by
  obtain ⟨k, hk, hpk⟩ := exists_lt_of_sum_lt (s := range (N + 1)) (f := fun _ ↦ (0 : ℝ)) (g := p)
    (by rw [hp.sum_eq_one, sum_const_zero]; exact one_pos)
  exact lt_of_lt_of_le (mul_pos hpk (pow_pos hw k)) (single_le_sum (f := fun i ↦ p i * w ^ i)
    (fun i _ ↦ mul_nonneg (hp.nonneg i) (pow_nonneg hw.le i)) hk)

/-- `M_r(w) > 0` for `w > 0` when some `p k` with `k ≥ 1` is positive. -/
theorem tiltSum_pos (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) (r : ℕ) {w : ℝ} (hw : 0 < w) :
    0 < tiltSum p N r w := by
  obtain ⟨k, hk0, hpk⟩ := hk
  have hkN : k < N + 1 := by
    by_contra h
    exact hpk.ne' (hp.eq_zero k (by omega))
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun i : ℕ ↦ (i : ℝ) ^ r * p i * w ^ i)
    (fun i _ ↦ mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg i) r) (hp.nonneg i))
      (pow_nonneg hw.le i)) (mem_range.mpr hkN))
  exact mul_pos (mul_pos (pow_pos (Nat.cast_pos.mpr hk0) r) hpk) (pow_pos hw k)

/-- `μ > 0` when some `p k` with `k ≥ 1` is positive. -/
theorem partialMean_pos (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) : 0 < partialMean p N := by
  simpa [tiltSum_one_one] using tiltSum_pos hp hk 1 one_pos

/-- If no `p k` with `k ≥ 1` is positive, then the law is the point mass at `0`, so `p 0 = 1` and
`μ = 0`. -/
theorem eq_one_and_partialMean_eq_zero (hp : IsLaw p N) (hk : ¬∃ k, 0 < k ∧ 0 < p k) :
    p 0 = 1 ∧ partialMean p N = 0 := by
  have h0 : ∀ k, 0 < k → p k = 0 := fun k hk0 ↦
    le_antisymm (not_lt.mp fun h ↦ hk ⟨k, hk0, h⟩) (hp.nonneg k)
  refine ⟨?_, sum_eq_zero fun k _ ↦ ?_⟩
  · rw [← hp.sum_eq_one, sum_range_succ', sum_eq_zero fun k _ ↦ h0 (k + 1) k.succ_pos, zero_add]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [h0 k hk0, mul_zero]

/-- `E_w X > 0` for `w > 0`. -/
theorem tiltMean_pos (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ} (hw : 0 < w) :
    0 < tiltMean p N w :=
  div_pos (tiltSum_pos hp hk 1 hw) (genFun_pos_of_pos hp hw)

/-- `E_1 X = μ`. -/
theorem tiltMean_one (hp : IsLaw p N) : tiltMean p N 1 = partialMean p N := by
  rw [tiltMean, genFun_one hp, div_one, tiltSum_one_one]

/-- `M_1(w) ≤ M_2(w)` for `w ≥ 0`, since `k ≤ k²` on `ℕ`. -/
theorem tiltSum_one_le_two (hp : IsLaw p N) {w : ℝ} (hw : 0 ≤ w) :
    tiltSum p N 1 w ≤ tiltSum p N 2 w := by
  refine sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ?_ (hp.nonneg k)) (pow_nonneg hw k)
  rw [pow_one]
  exact_mod_cast Nat.le_self_pow two_ne_zero k

/-- Cauchy–Schwarz, `M_1(w)² ≤ G(w) M_2(w)` for `w ≥ 0`. -/
theorem tiltSum_one_sq_le (hp : IsLaw p N) {w : ℝ} (hw : 0 ≤ w) :
    tiltSum p N 1 w ^ 2 ≤ genFun p N w * tiltSum p N 2 w :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun k _ ↦ mul_nonneg (hp.nonneg k) (pow_nonneg hw k))
    (fun k _ ↦ mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) 2) (hp.nonneg k))
      (pow_nonneg hw k))
    fun k _ ↦ le_of_eq (by ring)

/-- `Var_w X ≥ 0` for `w > 0`. -/
theorem tiltVar_nonneg (hp : IsLaw p N) {w : ℝ} (hw : 0 < w) : 0 ≤ tiltVar p N w := by
  have hG := genFun_pos_of_pos hp hw
  have h := tiltSum_one_sq_le hp hw.le
  rw [tiltVar, tiltMean, div_pow, sub_nonneg, div_le_div_iff₀ (pow_pos hG 2) hG]
  nlinarith

/-- Lemma 1(3), `Δ(w) = E_w X - E_w[X(X - 1)] / E_w X` for `w > 0`. -/
theorem fano_eq (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ} (hw : 0 < w) :
    fano p N w = tiltMean p N w - tiltPair p N w / tiltMean p N w := by
  have hG := (genFun_pos_of_pos hp hw).ne'
  have hM := (tiltSum_pos hp hk 1 hw).ne'
  simp only [fano, tiltVar, tiltPair, tiltMean]
  field_simp
  ring

/-- `E_w[X(X - 1)] ≥ 0` for `w > 0`. -/
theorem tiltPair_nonneg (hp : IsLaw p N) {w : ℝ} (hw : 0 < w) : 0 ≤ tiltPair p N w :=
  div_nonneg (sub_nonneg.mpr (tiltSum_one_le_two hp hw.le)) (genFun_pos_of_pos hp hw).le

/-- Lemma 1(3), `Δ(w) ≤ E_w X` for `w > 0`. -/
theorem fano_le_tiltMean (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ} (hw : 0 < w) :
    fano p N w ≤ tiltMean p N w := by
  rw [fano_eq hp hk hw, sub_le_self_iff]
  exact div_nonneg (tiltPair_nonneg hp hw) (tiltMean_pos hp hk hw).le

/-- `(E_w X)' = Var_w X / w` for `w > 0`. -/
theorem hasDerivAt_tiltMean (hp : IsLaw p N) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (tiltMean p N) (tiltVar p N w / w) w := by
  have hG := (genFun_pos_of_pos hp hw).ne'
  have h0 := hasDerivAt_tiltSum p N 0 hw.ne'
  rw [← genFun_eq_tiltSum] at h0
  refine ((hasDerivAt_tiltSum p N 1 hw.ne').div h0 hG).congr_deriv ?_
  simp only [tiltVar, tiltMean]
  field_simp

/-- Lemma 1(2), `(log E_w X)' = (1 - Δ(w)) / w` for `w > 0`. -/
theorem hasDerivAt_log_tiltMean (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ}
    (hw : 0 < w) :
    HasDerivAt (fun w ↦ Real.log (tiltMean p N w)) ((1 - fano p N w) / w) w := by
  refine ((hasDerivAt_tiltMean hp hw).log (tiltMean_pos hp hk hw).ne').congr_deriv ?_
  rw [fano]
  ring

/-- `(log G(w))' = E_w X / w` for `w > 0`. -/
theorem hasDerivAt_log_genFun (hp : IsLaw p N) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w ↦ Real.log (genFun p N w)) (tiltMean p N w / w) w := by
  have h0 := hasDerivAt_tiltSum p N 0 hw.ne'
  rw [← genFun_eq_tiltSum] at h0
  refine (h0.log (genFun_pos_of_pos hp hw).ne').congr_deriv ?_
  rw [tiltMean]
  ring

/-- `log G` is continuous on `[0, 1]` when `p 0 > 0`. -/
theorem continuousOn_log_genFun (hp : IsLaw p N) (hp0 : 0 < p 0) :
    ContinuousOn (fun w ↦ Real.log (genFun p N w)) (Set.Icc 0 1) :=
  (continuous_genFun p N).continuousOn.log fun _ hw ↦ (genFun_pos hp hp0 hw.1).ne'

/-- Lemma 1(1), `-log p 0 = ∫_0^1 E_w X dw / w`. -/
theorem integral_tiltMean_div (hp : IsLaw p N) (hp0 : 0 < p 0) :
    ∫ w in (0 : ℝ)..1, tiltMean p N w / w = -Real.log (p 0) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_log_genFun hp hp0) (fun w hw ↦ hasDerivAt_log_genFun hp hw.1), genFun_one hp,
    genFun_zero, Real.log_one, zero_sub]
  refine (ContinuousOn.intervalIntegrable ?_).congr (f := fun w ↦ genDeriv p N w / genFun p N w)
    fun w hw ↦ ?_
  · rw [Set.uIcc_of_le zero_le_one]
    exact (continuous_genDeriv p N).continuousOn.div (continuous_genFun p N).continuousOn
      fun _ hw ↦ (genFun_pos hp hp0 hw.1).ne'
  · rw [Set.uIoc_of_le zero_le_one] at hw
    simp only [genDeriv_eq p N hw.1.ne', tiltMean]
    ring

/-- A function that is continuous on `(a, b]` and has a nonnegative derivative on `(a, b)` is
monotone on `(a, b]`. -/
theorem monotoneOn_Ioc_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Set.Ioc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (h : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) :
    MonotoneOn f (Set.Ioc a b) :=
  monotoneOn_of_deriv_nonneg (convex_Ioc a b) hc
    (fun x hx ↦ by
      rw [interior_Ioc] at hx
      exact (hf x hx).differentiableAt.differentiableWithinAt)
    fun x hx ↦ by
      rw [interior_Ioc] at hx
      rw [(hf x hx).deriv]
      exact h x hx

/-- A function that is continuous on `(a, b]` and has a nonpositive derivative on `(a, b)` is
antitone on `(a, b]`. -/
theorem antitoneOn_Ioc_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Set.Ioc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (h : ∀ x ∈ Set.Ioo a b, f' x ≤ 0) :
    AntitoneOn f (Set.Ioc a b) :=
  antitoneOn_of_deriv_nonpos (convex_Ioc a b) hc
    (fun x hx ↦ by
      rw [interior_Ioc] at hx
      exact (hf x hx).differentiableAt.differentiableWithinAt)
    fun x hx ↦ by
      rw [interior_Ioc] at hx
      rw [(hf x hx).deriv]
      exact h x hx

/-- The comparison behind the lower reductions for `p 0`. Let `φ` be continuous on `[0, 1]` with
derivative `φ'` on `(0, 1)`. If `E_x X / x ≤ φ'(x)` on `(0, 1)`, then `p 0 ≥ exp(φ(0) - φ(1))`.
Since `(log G)' = E_x X / x`, `log G - φ` is antitone on `(0, 1]`, so `G(x) ≥ exp(φ(x) - φ(1))`
there, and `x → 0` gives the bound. It does not assume `p 0 > 0`. -/
theorem exp_sub_le_of_tiltMean_div_le (hp : IsLaw p N) {φ φ' : ℝ → ℝ}
    (hc : ContinuousOn φ (Set.Icc 0 1)) (hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hle : ∀ x ∈ Set.Ioo (0 : ℝ) 1, tiltMean p N x / x ≤ φ' x) :
    Real.exp (φ 0 - φ 1) ≤ p 0 := by
  have hanti := antitoneOn_Ioc_of_hasDerivAt (f := fun x ↦ Real.log (genFun p N x) - φ x)
    (((continuous_genFun p N).continuousOn.log fun _ hx ↦ (genFun_pos_of_pos hp hx.1).ne').sub
      (hc.mono Set.Ioc_subset_Icc_self))
    (fun x hx ↦ (hasDerivAt_log_genFun hp hx.1).sub (hd x hx))
    (fun x hx ↦ sub_nonpos.mpr (hle x hx))
  have hIoc : ∀ x ∈ Set.Ioc (0 : ℝ) 1, Real.exp (φ x - φ 1) ≤ genFun p N x := fun x hx ↦ by
    have h1 := hanti hx ⟨one_pos, le_rfl⟩ hx.2
    simp only [genFun_one hp, Real.log_one, zero_sub] at h1
    rw [← Real.exp_log (genFun_pos_of_pos hp hx.1)]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [← genFun_zero p N]
  exact ContinuousWithinAt.closure_le (by rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩)
    (((hc 0 ⟨le_rfl, zero_le_one⟩).mono Set.Ioc_subset_Icc_self).sub continuousWithinAt_const).rexp
    (continuous_genFun p N).continuousWithinAt hIoc

/-- The mirror comparison, behind the upper reductions for `p 0`. Let `φ` be continuous on
`[0, 1]` with derivative `φ'` on `(0, 1)`. If `φ'(x) ≤ E_x X / x` on `(0, 1)`, then
`p 0 ≤ exp(φ(0) - φ(1))`. It does not assume `p 0 > 0`. -/
theorem le_exp_sub_of_le_tiltMean_div (hp : IsLaw p N) {φ φ' : ℝ → ℝ}
    (hc : ContinuousOn φ (Set.Icc 0 1)) (hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hle : ∀ x ∈ Set.Ioo (0 : ℝ) 1, φ' x ≤ tiltMean p N x / x) :
    p 0 ≤ Real.exp (φ 0 - φ 1) := by
  have hmono := monotoneOn_Ioc_of_hasDerivAt (f := fun x ↦ Real.log (genFun p N x) - φ x)
    (((continuous_genFun p N).continuousOn.log fun _ hx ↦ (genFun_pos_of_pos hp hx.1).ne').sub
      (hc.mono Set.Ioc_subset_Icc_self))
    (fun x hx ↦ (hasDerivAt_log_genFun hp hx.1).sub (hd x hx))
    (fun x hx ↦ sub_nonneg.mpr (hle x hx))
  have hIoc : ∀ x ∈ Set.Ioc (0 : ℝ) 1, genFun p N x ≤ Real.exp (φ x - φ 1) := fun x hx ↦ by
    have h1 := hmono hx ⟨one_pos, le_rfl⟩ hx.2
    simp only [genFun_one hp, Real.log_one, zero_sub] at h1
    rw [← Real.exp_log (genFun_pos_of_pos hp hx.1)]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [← genFun_zero p N]
  exact ContinuousWithinAt.closure_le (by rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩)
    (continuous_genFun p N).continuousWithinAt
    (((hc 0 ⟨le_rfl, zero_le_one⟩).mono Set.Ioc_subset_Icc_self).sub continuousWithinAt_const).rexp
    hIoc

/-- `E_w X ≤ μ` for `w ∈ (0, 1]`, since `(E_w X)' = Var_w X / w ≥ 0`. -/
theorem tiltMean_le (hp : IsLaw p N) {w : ℝ} (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    tiltMean p N w ≤ partialMean p N := by
  rw [← tiltMean_one hp]
  exact monotoneOn_Ioc_of_hasDerivAt
    (fun x hx ↦ (hasDerivAt_tiltMean hp hx.1).continuousAt.continuousWithinAt)
    (fun x hx ↦ hasDerivAt_tiltMean hp hx.1)
    (fun x hx ↦ div_nonneg (tiltVar_nonneg hp hx.1) hx.1.le) hw ⟨one_pos, le_rfl⟩ hw.2

/-- If `Δ ≤ δ` on `(0, 1]`, then `E_w X ≤ μ w^(1 - δ)` on `(0, 1]`. -/
theorem tiltMean_le_rpow (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {δ : ℝ}
    (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, fano p N w ≤ δ) {w : ℝ} (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    tiltMean p N w ≤ partialMean p N * w ^ (1 - δ) := by
  have hd : ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun x ↦ Real.log (tiltMean p N x) - (1 - δ) * Real.log x)
        ((1 - fano p N x) / x - (1 - δ) * x⁻¹) x := fun x hx ↦
    (hasDerivAt_log_tiltMean hp hk hx.1).sub ((Real.hasDerivAt_log hx.1.ne').const_mul (1 - δ))
  have hmono := monotoneOn_Ioc_of_hasDerivAt
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ hd x (Set.Ioo_subset_Ioc_self hx))
    (fun x hx ↦ by
      rw [show (1 - fano p N x) / x - (1 - δ) * x⁻¹ = (δ - fano p N x) / x by ring]
      exact div_nonneg (sub_nonneg.mpr (hΔ x (Set.Ioo_subset_Ioc_self hx))) hx.1.le)
    hw ⟨one_pos, le_rfl⟩ hw.2
  simp only [tiltMean_one hp, Real.log_one, mul_zero, sub_zero] at hmono
  have hμ := partialMean_pos hp hk
  rw [← Real.log_le_log_iff (tiltMean_pos hp hk hw.1) (mul_pos hμ (Real.rpow_pos_of_pos hw.1 _)),
    Real.log_mul hμ.ne' (Real.rpow_pos_of_pos hw.1 _).ne', Real.log_rpow hw.1]
  linarith

/-- If `Δ ≥ δ` on `(0, 1]`, then `E_w X ≥ μ w^(1 - δ)` on `(0, 1]`, the mirror of
`tiltMean_le_rpow`. -/
theorem mul_rpow_le_tiltMean (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {δ : ℝ}
    (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, δ ≤ fano p N w) {w : ℝ} (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    partialMean p N * w ^ (1 - δ) ≤ tiltMean p N w := by
  have hd : ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun x ↦ Real.log (tiltMean p N x) - (1 - δ) * Real.log x)
        ((1 - fano p N x) / x - (1 - δ) * x⁻¹) x := fun x hx ↦
    (hasDerivAt_log_tiltMean hp hk hx.1).sub ((Real.hasDerivAt_log hx.1.ne').const_mul (1 - δ))
  have hanti := antitoneOn_Ioc_of_hasDerivAt
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ hd x (Set.Ioo_subset_Ioc_self hx))
    (fun x hx ↦ by
      rw [show (1 - fano p N x) / x - (1 - δ) * x⁻¹ = (δ - fano p N x) / x by ring]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hΔ x (Set.Ioo_subset_Ioc_self hx)))
        hx.1.le)
    hw ⟨one_pos, le_rfl⟩ hw.2
  simp only [tiltMean_one hp, Real.log_one, mul_zero, sub_zero] at hanti
  have hμ := partialMean_pos hp hk
  rw [← Real.log_le_log_iff (mul_pos hμ (Real.rpow_pos_of_pos hw.1 _)) (tiltMean_pos hp hk hw.1),
    Real.log_mul hμ.ne' (Real.rpow_pos_of_pos hw.1 _).ne', Real.log_rpow hw.1]
  linarith

/-- Proposition 4, the Fano criterion, for every law on `[0, N]`. If `δ < 1` and `Δ(w) ≤ δ` for
every `w ∈ (0, 1]` with `E_w X ≥ δ`, then `p 0 ≥ exp(-μ / (1 - δ))`. -/
theorem exp_neg_div_le_of_fano_le (hp : IsLaw p N) {δ : ℝ}
    (hδ : δ < 1) (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, δ ≤ tiltMean p N w → fano p N w ≤ δ) :
    Real.exp (-(partialMean p N / (1 - δ))) ≤ p 0 := by
  by_cases hk : ∃ k, 0 < k ∧ 0 < p k
  swap
  · obtain ⟨h0, hμ⟩ := eq_one_and_partialMean_eq_zero hp hk
    simp [h0, hμ]
  have hΔ' : ∀ w ∈ Set.Ioc (0 : ℝ) 1, fano p N w ≤ δ := fun w hw ↦ by
    by_cases h : δ ≤ tiltMean p N w
    · exact hΔ w hw h
    · exact (fano_le_tiltMean hp hk hw.1).trans (not_le.mp h).le
  have hpos : 0 < 1 - δ := by linarith
  set μ := partialMean p N
  have h := exp_sub_le_of_tiltMean_div_le hp (φ := fun x ↦ μ / (1 - δ) * x ^ (1 - δ))
    (continuousOn_const.mul (Real.continuous_rpow_const hpos.le).continuousOn)
    (fun x hx ↦ (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).const_mul _) fun x hx ↦ by
      change tiltMean p N x / x ≤ μ / (1 - δ) * ((1 - δ) * x ^ (1 - δ - 1))
      have h := tiltMean_le_rpow hp hk hΔ' (Set.Ioo_subset_Ioc_self hx)
      rw [Real.rpow_sub_one hx.1.ne',
        show μ / (1 - δ) * ((1 - δ) * (x ^ (1 - δ) / x)) = μ * x ^ (1 - δ) / x by field_simp]
      exact div_le_div_of_nonneg_right h hx.1.le
  simpa only [Real.zero_rpow hpos.ne', Real.one_rpow, mul_zero, mul_one, zero_sub] using h

@[deprecated exp_neg_div_le_of_fano_le (since := "2026-11-26")]
alias fano_criterion := exp_neg_div_le_of_fano_le

/-- If `Δ ≥ 0` on `(0, 1]`, then `E_w X ≥ μ w` on `(0, 1]`. -/
theorem mul_le_tiltMean (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k)
    (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ fano p N w) {w : ℝ} (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    partialMean p N * w ≤ tiltMean p N w := by
  simpa only [sub_zero, Real.rpow_one] using mul_rpow_le_tiltMean hp hk hΔ hw

/-- The mirror of the Fano criterion, for every law on `[0, N]`. If `δ < 1` and `Δ(w) ≥ δ` for
every `w ∈ (0, 1]`, then `p 0 ≤ exp(-μ / (1 - δ))`. -/
theorem le_exp_neg_div_of_le_fano (hp : IsLaw p N) {δ : ℝ}
    (hδ : δ < 1) (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, δ ≤ fano p N w) :
    p 0 ≤ Real.exp (-(partialMean p N / (1 - δ))) := by
  by_cases hk : ∃ k, 0 < k ∧ 0 < p k
  swap
  · obtain ⟨h0, hμ⟩ := eq_one_and_partialMean_eq_zero hp hk
    simp [h0, hμ]
  have hpos : 0 < 1 - δ := by linarith
  set μ := partialMean p N
  have h := le_exp_sub_of_le_tiltMean_div hp (φ := fun x ↦ μ / (1 - δ) * x ^ (1 - δ))
    (continuousOn_const.mul (Real.continuous_rpow_const hpos.le).continuousOn)
    (fun x hx ↦ (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).const_mul _) fun x hx ↦ by
      change μ / (1 - δ) * ((1 - δ) * x ^ (1 - δ - 1)) ≤ tiltMean p N x / x
      have h := mul_rpow_le_tiltMean hp hk hΔ (Set.Ioo_subset_Ioc_self hx)
      rw [Real.rpow_sub_one hx.1.ne',
        show μ / (1 - δ) * ((1 - δ) * (x ^ (1 - δ) / x)) = μ * x ^ (1 - δ) / x by field_simp]
      exact div_le_div_of_nonneg_right h hx.1.le
  simpa only [Real.zero_rpow hpos.ne', Real.one_rpow, mul_zero, mul_one, zero_sub] using h

/-- The Section 4 mirror. If `Δ(w) ≥ 0` for every `w ∈ (0, 1]`, then `p 0 ≤ exp(-μ)`. It is
`le_exp_neg_div_of_le_fano` at `δ = 0`, for every law on `[0, N]`. -/
theorem le_exp_neg_of_fano_nonneg (hp : IsLaw p N)
    (hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ fano p N w) : p 0 ≤ Real.exp (-partialMean p N) := by
  simpa only [sub_zero, div_one] using le_exp_neg_div_of_le_fano hp zero_lt_one hΔ

/-- `R(z) = G'(z) / (μ G(z))`, the ratio `E z^Y / E z^X` for the size-biased shift `Y`. -/
noncomputable def sbRatio (p : ℕ → ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  deriv (genFun p N) z / (partialMean p N * genFun p N z)

/-- `D(w) = μ (1 - E_w[X(X - 1)] / (E_w X)²)`, the quantity of the pair criterion. It is
`(1 / R)'(w)` (`hasDerivAt_inv_sbRatio`). -/
noncomputable def pairDeficit (p : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  partialMean p N * (1 - tiltPair p N w / tiltMean p N w ^ 2)

/-- `R(1) = 1`. -/
theorem sbRatio_one (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) : sbRatio p N 1 = 1 := by
  rw [sbRatio, deriv_genFun, genDeriv_eq p N one_ne_zero, div_one, tiltSum_one_one,
    genFun_one hp, mul_one, div_self (partialMean_pos hp hk).ne']

/-- Lemma 1(4), `(1 / R)'(w) = D(w)` for `w > 0`. -/
theorem hasDerivAt_inv_sbRatio (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ}
    (hw : 0 < w) : HasDerivAt (fun z ↦ 1 / sbRatio p N z) (pairDeficit p N w) w := by
  have hG := (genFun_pos_of_pos hp hw).ne'
  have hM := (tiltSum_pos hp hk 1 hw).ne'
  have h0 := hasDerivAt_tiltSum p N 0 hw.ne'
  rw [← genFun_eq_tiltSum] at h0
  refine ((((hasDerivAt_id w).const_mul (partialMean p N)).mul h0).div
    (hasDerivAt_tiltSum p N 1 hw.ne') hM).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hw] with y hy
    have hGy := (genFun_pos_of_pos hp hy).ne'
    have hMy := (tiltSum_pos hp hk 1 hy).ne'
    have hμ := (partialMean_pos hp hk).ne'
    rw [sbRatio, deriv_genFun, genDeriv_eq p N (ne_of_gt hy)]
    simp only [Pi.mul_apply, Pi.div_apply, id]
    field_simp
  · simp only [pairDeficit, tiltPair, tiltMean, Pi.mul_apply, id]
    field_simp
    ring

/-- Lemma 1(4), `Δ(w) = (E_w X / μ) D(w)` for `w > 0`. -/
theorem fano_eq_mul_pairDeficit (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {w : ℝ}
    (hw : 0 < w) : fano p N w = tiltMean p N w / partialMean p N * pairDeficit p N w := by
  have hμ := (partialMean_pos hp hk).ne'
  have hE := (tiltMean_pos hp hk hw).ne'
  rw [fano_eq hp hk hw, pairDeficit]
  field_simp

/-- Proposition 5(2), the pair criterion. If `D(w) ≤ c` on `(0, 1]`, then
`Δ(w) ≤ c E_w X / μ` on `(0, 1]`. -/
theorem fano_le_mul_tiltMean (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {c : ℝ}
    (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) {w : ℝ}
    (hw : w ∈ Set.Ioc (0 : ℝ) 1) : fano p N w ≤ c * tiltMean p N w / partialMean p N := by
  rw [fano_eq_mul_pairDeficit hp hk hw.1, mul_comm c, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left (hc w hw)
    (div_nonneg (tiltMean_pos hp hk hw.1).le (partialMean_pos hp hk).le)

/-- Proposition 5(2), the pair criterion. If `c ≥ 0` and `D(w) ≤ c` on `(0, 1]`, then
`Δ(w) ≤ c` on `(0, 1]`. -/
theorem fano_le_of_pairDeficit_le (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) {w : ℝ}
    (hw : w ∈ Set.Ioc (0 : ℝ) 1) : fano p N w ≤ c := by
  refine (fano_le_mul_tiltMean hp hk hc hw).trans ?_
  rw [div_le_iff₀ (partialMean_pos hp hk)]
  exact mul_le_mul_of_nonneg_left (tiltMean_le hp hw) hc0

/-- `1 - c (1 - z) > 0` for `c < 1` and `z ∈ [0, 1]`. -/
theorem one_sub_mul_pos {c z : ℝ} (hc1 : c < 1) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - c * (1 - z) := by
  rcases hz.1.eq_or_lt with rfl | hz0
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (sub_pos.mpr hc1).le]

/-- Proposition 5(1) multiplied out. If `D(w) ≤ c` on `(0, 1]`, then
`G'(z) (1 - c (1 - z)) ≤ μ G(z)` on `[0, 1]`. -/
theorem genDeriv_mul_le (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {c : ℝ}
    (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    genDeriv p N z * (1 - c * (1 - z)) ≤ partialMean p N * genFun p N z := by
  have hd : ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun x ↦ 1 / sbRatio p N x - c * x) (pairDeficit p N x - c * 1) x :=
    fun x hx ↦ (hasDerivAt_inv_sbRatio hp hk hx.1).sub ((hasDerivAt_id x).const_mul c)
  have hanti := antitoneOn_Ioc_of_hasDerivAt
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ hd x (Set.Ioo_subset_Ioc_self hx))
    (fun x hx ↦ by
      rw [mul_one, sub_nonpos]
      exact hc x (Set.Ioo_subset_Ioc_self hx))
  have hIoc : Set.Ioc (0 : ℝ) 1 ⊆
      {x | genDeriv p N x * (1 - c * (1 - x)) ≤ partialMean p N * genFun p N x} := by
    intro x hx
    have h := hanti hx ⟨one_pos, le_rfl⟩ hx.2
    simp only [sbRatio_one hp hk, div_one, mul_one] at h
    have hD : 0 < genDeriv p N x := by
      rw [genDeriv_eq p N hx.1.ne']
      exact div_pos (tiltSum_pos hp hk 1 hx.1) hx.1
    rw [sbRatio, deriv_genFun, one_div_div] at h
    have h' : 1 - c * (1 - x) ≤ partialMean p N * genFun p N x / genDeriv p N x := by linarith
    rw [le_div_iff₀ hD] at h'
    change genDeriv p N x * (1 - c * (1 - x)) ≤ partialMean p N * genFun p N x
    linarith
  have hcl : IsClosed {x | genDeriv p N x * (1 - c * (1 - x)) ≤ partialMean p N * genFun p N x} :=
    isClosed_le ((continuous_genDeriv p N).mul (continuous_const.sub
      (continuous_const.mul (continuous_const.sub continuous_id))))
      (continuous_const.mul (continuous_genFun p N))
  rw [← closure_Ioc (zero_ne_one' ℝ)] at hz
  exact closure_minimal hIoc hcl hz

/-- Proposition 5(1), for every law on `[0, N]`. If `c < 1` and `D(w) ≤ c` on `(0, 1]`, then
`R(z) ≤ 1 / (1 - c (1 - z))` on `[0, 1]`. Where `μ G(z) = 0` the ratio is `0` by convention. -/
theorem sbRatio_le_of_pairDeficit_le (hp : IsLaw p N) {c : ℝ}
    (hc1 : c < 1) (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) : sbRatio p N z ≤ 1 / (1 - c * (1 - z)) := by
  by_cases hk : ∃ k, 0 < k ∧ 0 < p k
  swap
  · rw [sbRatio, (eq_one_and_partialMean_eq_zero hp hk).2, zero_mul, div_zero]
    exact (one_div_pos.mpr (one_sub_mul_pos hc1 hz)).le
  rcases ((hp.nonneg 0).trans (le_genFun hp hz.1)).eq_or_lt with hG | hG
  · rw [sbRatio, ← hG, mul_zero, div_zero]
    exact (one_div_pos.mpr (one_sub_mul_pos hc1 hz)).le
  rw [sbRatio, deriv_genFun, div_le_div_iff₀ (mul_pos (partialMean_pos hp hk) hG)
    (one_sub_mul_pos hc1 hz), one_mul]
  exact genDeriv_mul_le hp hk hc hz

/-- Proposition 5(1) at `z = 0`, `ρ_0 ≤ 1 / (1 - c)`, in the multiplied-out form
`G(1) ≤ (1 - c)⁻¹ μ F(0)` used by `SizeBias.lower_reduction`. -/
theorem partialMean_one_le (hp : IsLaw p N) (hk : ∃ k, 0 < k ∧ 0 < p k) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) :
    partialMean p 1 ≤ (1 - c)⁻¹ * partialMean p N * cdf p 0 := by
  have h := genDeriv_mul_le hp hk hc ⟨le_rfl, zero_le_one⟩
  rw [genDeriv_zero hp, genFun_zero, sub_zero, mul_one] at h
  have hp1 : partialMean p 1 = p 1 := by simp [partialMean, sum_range_succ]
  have hc0 : cdf p 0 = p 0 := by simp [cdf]
  rw [hp1, hc0, mul_assoc, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hc1)]
  linarith

/-- Proposition 5(3), for every law on `[0, N]`. If `0 < c < 1` and `D(w) ≤ c` on `(0, 1]`, then
`p 0 ≥ exp(-(μ / c) log(1 / (1 - c)))`. -/
theorem exp_neg_mul_log_le_of_pairDeficit_le (hp : IsLaw p N) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) :
    Real.exp (-(partialMean p N / c * Real.log (1 / (1 - c)))) ≤ p 0 := by
  by_cases hk : ∃ k, 0 < k ∧ 0 < p k
  swap
  · obtain ⟨h0, hμ⟩ := eq_one_and_partialMean_eq_zero hp hk
    simp [h0, hμ]
  set μ := partialMean p N
  have h := exp_sub_le_of_tiltMean_div_le hp (φ := fun x ↦ μ / c * Real.log (1 - c * (1 - x)))
    (continuousOn_const.mul (ContinuousOn.log (continuousOn_const.sub (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))) fun x hx ↦ (one_sub_mul_pos hc1 hx).ne'))
    (fun x hx ↦ ((((hasDerivAt_const x 1).sub (((hasDerivAt_const x 1).sub
      (hasDerivAt_id x)).const_mul c)).log
        (one_sub_mul_pos hc1 (Set.Ioo_subset_Icc_self hx)).ne').const_mul _)) fun x hx ↦ by
      have ha := one_sub_mul_pos hc1 (Set.Ioo_subset_Icc_self hx)
      have hG := genFun_pos_of_pos hp hx.1
      have h := genDeriv_mul_le hp hk hc (Set.Ioo_subset_Icc_self hx)
      rw [genDeriv_eq p N hx.1.ne'] at h
      have h3 : μ / c * ((0 - c * (0 - 1)) / (1 - c * (1 - x))) = μ / (1 - c * (1 - x)) := by
        rw [show (0 : ℝ) - c * (0 - 1) = c by ring]
        field_simp
      change tiltMean p N x / x ≤ μ / c * ((0 - c * (0 - 1)) / (1 - c * (1 - x)))
      rw [tiltMean, h3, div_right_comm, div_le_div_iff₀ hG ha]
      linarith
  rw [one_div, Real.log_inv]
  simpa only [sub_zero, mul_one, sub_self, mul_zero, Real.log_one, mul_neg, neg_neg] using h

@[deprecated exp_neg_mul_log_le_of_pairDeficit_le (since := "2026-11-26")]
alias pair_criterion := exp_neg_mul_log_le_of_pairDeficit_le

/-- Proposition 5(3), weak form, for every law on `[0, N]`. If `0 < c < 1` and `D(w) ≤ c` on
`(0, 1]`, then `p 0 ≥ exp(-μ / (1 - c))`. -/
theorem exp_neg_div_le_of_pairDeficit_le (hp : IsLaw p N) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hc : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p N w ≤ c) :
    Real.exp (-(partialMean p N / (1 - c))) ≤ p 0 := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_mul_log_le_of_pairDeficit_le hp hc0 hc1 hc)
  have hc' : 1 - c ≠ 0 := (sub_pos.mpr hc1).ne'
  have hl : Real.log (1 / (1 - c)) ≤ c / (1 - c) := by
    have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr (sub_pos.mpr hc1))
    rwa [div_sub_one hc', sub_sub_cancel] at h
  have h := mul_le_mul_of_nonneg_left hl (div_nonneg (hp.partialMean_nonneg N) hc0.le)
  have e : partialMean p N / c * (c / (1 - c)) = partialMean p N / (1 - c) := by
    field_simp
  linarith

end Tilt

namespace RoundRobin.Canonical

open Finset PerfectMatching Tilt

/-- A sum over perfect matchings of a function of `X` splits by the value of `X`,
`∑_P g(X P) = ∑_{k ≤ n} #{P | X P = k} g(k)`. It is `ChainRule.sum_mul_lawOf` for the weight
`1`. -/
theorem sum_hamCount_eq (m : ℕ) [NeZero m] (g : ℕ → ℝ) :
    ∑ P : PerfectMatching (Vertex m), g (hamCount m P) =
      ∑ k ∈ range (2 * m - 1 + 1), ((univ.filter fun P ↦ hamCount m P = k).card : ℝ) * g k := by
  simpa [ChainRule.lawOf_eq_sum] using ChainRule.sum_mul_lawOf (fun _ ↦ (1 : ℝ)) (hamCount_le m) g

/-- The size-bias identity against a weight `f`, `∑_P X(P) f(X P) = n ∑_{P | A_0} f(X P)`.
It is `card_ham_and_eq_mul` summed against `f` over `k`. -/
theorem sum_hamCount_mul (m : ℕ) [NeZero m] (f : ℕ → ℝ) :
    ∑ P : PerfectMatching (Vertex m), (hamCount m P : ℝ) * f (hamCount m P) =
      ((2 * m - 1 : ℕ) : ℝ) *
        ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), f (hamCount m P) := by
  rw [sum_hamCount_eq m fun k ↦ (k : ℝ) * f k, ← sum_fiberwise_of_maps_to
    (s := univ.filter fun P ↦ Ham P (factor m 0)) (t := range (2 * m - 1 + 1)) (g := hamCount m)
    fun P _ ↦ mem_range.mpr (Nat.lt_succ_of_le (hamCount_le m P)), mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_congr rfl (g := fun _ ↦ f k) fun P hP ↦ congrArg f (mem_filter.mp hP).2, sum_const,
    nsmul_eq_mul, filter_filter]
  have h : ((2 * m - 1 : ℕ) : ℝ) *
      ((univ.filter fun P ↦ Ham P (factor m 0) ∧ hamCount m P = k).card : ℝ) =
        k * (univ.filter fun P ↦ hamCount m P = k).card := by
    exact_mod_cast card_ham_and_eq_mul m k
  linear_combination -(f k) * h

/-- Lemma 2(2), the tilted mean identity, `∑_P w^X(P) X(P) = n ∑_{P | A_0} w^X(P)`. -/
theorem sum_pow_mul_hamCount (m : ℕ) [NeZero m] (w : ℝ) :
    ∑ P : PerfectMatching (Vertex m), w ^ hamCount m P * (hamCount m P : ℝ) =
      ((2 * m - 1 : ℕ) : ℝ) * ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), w ^ hamCount m P := by
  rw [← sum_hamCount_mul m fun k ↦ w ^ k]
  exact sum_congr rfl fun P _ ↦ mul_comm _ _

/-- Lemma 2, the tilted size-bias identity,
`∑_P w^X(P) X(P) (X(P) - 1) = n ∑_{P | A_0} w^X(P) (X(P) - 1)`. -/
theorem sum_pow_mul_hamCount_pair (m : ℕ) [NeZero m] (w : ℝ) :
    ∑ P : PerfectMatching (Vertex m),
        w ^ hamCount m P * ((hamCount m P : ℝ) * ((hamCount m P : ℝ) - 1)) =
      ((2 * m - 1 : ℕ) : ℝ) * ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0),
        w ^ hamCount m P * ((hamCount m P : ℝ) - 1) := by
  rw [← sum_hamCount_mul m fun k ↦ w ^ k * ((k : ℝ) - 1)]
  exact sum_congr rfl fun P _ ↦ by ring

/-- `M_r(w)` for the law of `X` is `∑_P X(P)^r w^X(P) / |PM(V_m)|`. -/
theorem tiltSum_hamLaw (m : ℕ) [NeZero m] (r : ℕ) (w : ℝ) :
    tiltSum (hamLaw m) (2 * m - 1) r w =
      (∑ P : PerfectMatching (Vertex m), (hamCount m P : ℝ) ^ r * w ^ hamCount m P) /
        Fintype.card (PerfectMatching (Vertex m)) := by
  rw [sum_hamCount_eq m fun k ↦ (k : ℝ) ^ r * w ^ k, sum_div, tiltSum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [hamLaw]
  ring

/-- Lemma 2(2), `E_w X = n U_w(A_0)`, where `U_w(A_0) = ∑_{P | A_0} w^X(P) / ∑_P w^X(P)`. -/
theorem tiltMean_hamLaw (m : ℕ) [NeZero m] (w : ℝ) :
    tiltMean (hamLaw m) (2 * m - 1) w =
      ((2 * m - 1 : ℕ) : ℝ) * (∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), w ^ hamCount m P) /
        ∑ P : PerfectMatching (Vertex m), w ^ hamCount m P := by
  rw [tiltMean, genFun_eq_tiltSum, tiltSum_hamLaw, tiltSum_hamLaw,
    div_div_div_cancel_right₀ (cast_card_perfectMatching_ne_zero m), ← sum_pow_mul_hamCount]
  simp only [pow_one, pow_zero, one_mul, mul_comm]

/-- Lemma 2(2), `Δ(w) = E_w X - E_w[X' | A_0]` for `w > 0`, where `X' = X - 1` and
`E_w[X' | A_0] = ∑_{P | A_0} X'(P) w^X'(P) / ∑_{P | A_0} w^X'(P)` is the mean of `X'` under the
`w^X'`-tilt of the uniform law on `A_0`. It holds for every `m ≥ 1`. -/
theorem fano_hamLaw (m : ℕ) [NeZero m] {w : ℝ} (hw : 0 < w) :
    fano (hamLaw m) (2 * m - 1) w = tiltMean (hamLaw m) (2 * m - 1) w -
      (∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0),
          ((hamCount m P - 1 : ℕ) : ℝ) * w ^ (hamCount m P - 1)) /
        ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), w ^ (hamCount m P - 1) := by
  have hT := cast_card_perfectMatching_ne_zero m
  have hn : ((2 * m - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hX : ∀ P ∈ univ.filter fun P ↦ Ham P (factor m 0), ∃ j, hamCount m P = j + 1 :=
    fun P hP ↦ ⟨hamCount m P - 1, by
      have : 0 < hamCount m P := Finset.card_pos.mpr ⟨0, by simpa using (mem_filter.mp hP).2⟩
      omega⟩
  have hG := (genFun_pos_of_pos (isLaw_hamLaw m) hw).ne'
  have hS1 : ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0),
      w ^ hamCount m P * ((hamCount m P : ℝ) - 1) =
        w * ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0),
          ((hamCount m P - 1 : ℕ) : ℝ) * w ^ (hamCount m P - 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun P hP ↦ ?_
    obtain ⟨j, hj⟩ := hX P hP
    rw [hj, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  have hS0 : ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), w ^ hamCount m P =
      w * ∑ P ∈ univ.filter fun P ↦ Ham P (factor m 0), w ^ (hamCount m P - 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun P hP ↦ ?_
    obtain ⟨j, hj⟩ := hX P hP
    rw [hj, Nat.add_sub_cancel, pow_succ, mul_comm]
  rw [fano_eq (isLaw_hamLaw m) (exists_pos_hamLaw m) hw]
  congr 1
  rw [tiltPair, tiltMean, div_div_div_cancel_right₀ hG, tiltSum_hamLaw, tiltSum_hamLaw, ← sub_div,
    div_div_div_cancel_right₀ hT, ← sum_sub_distrib]
  rw [sum_congr rfl fun P _ ↦ show (hamCount m P : ℝ) ^ 2 * w ^ hamCount m P -
      (hamCount m P : ℝ) ^ 1 * w ^ hamCount m P =
        w ^ hamCount m P * ((hamCount m P : ℝ) * ((hamCount m P : ℝ) - 1)) by ring,
    sum_congr rfl fun P _ ↦ show (hamCount m P : ℝ) ^ 1 * w ^ hamCount m P =
        w ^ hamCount m P * (hamCount m P : ℝ) by ring,
    sum_pow_mul_hamCount_pair, sum_pow_mul_hamCount, hS1, hS0, mul_div_mul_left _ _ hn,
    mul_div_mul_left _ _ hw.ne']

end RoundRobin.Canonical

end Pairing
