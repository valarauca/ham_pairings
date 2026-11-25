import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Size-bias reductions for a law on `ℕ` (COD-183)

A finitely supported law on `ℕ` is a family of point masses `p k ≥ 0` with `p k = 0` for
`k > N` and `∑_{k ≤ N} p k = 1` (`IsLaw p N`). Put `F(j) = cdf p j = ∑_{k ≤ j} p k`,
`G(j) = partialMean p j = ∑_{k ≤ j} k p k` and `μ = G(N)`. The size-bias ratio is
`ρ_j = G(j + 1) / (μ F(j))`. The statements use `ρ_j ≥ 1` and `ρ_j ≤ K` in the multiplied-out
forms `μ F(j) ≤ G(j + 1)` and `G(j + 1) ≤ K μ F(j)`.

* `IsLaw.markov` : `(m + 1)(1 - F(m)) ≤ μ`.
* `IsLaw.deriv_ge` : if `μ F(j) ≤ G(j + 1)` for every `j ≤ J`, then `L(x) = ∑ p k x^k` satisfies
  `L'(x) ≥ μ L(x) - μ x^(J + 1)` on `[0, 1]`. At `x = e^(-θ)` this is the size-bias bound
  `E e^(-θX^s) ≥ e^(-θ) L - e^(-θ(J + 2))`.
* `upper_reduction_floor` : if `μ F(j) ≤ G(j + 1)` for every `j ≤ J`, `m ≤ J + 1` and
  `μ < m + 1`, then `p 0 ≤ exp(-μ + μ (m + 1) / ((m + 1 - μ)(J + 2 - m)))`. The proof shows
  that `x ↦ L(x) exp(c x^(J + 2 - m) / (J + 2 - m) - μ x)` is monotone on `[0, 1]`, where
  `L(x) = ∑ p k x^k` and `c = μ (m + 1) / (m + 1 - μ)`.
* `upper_reduction_of_lt` : for `0 < δ < ε` and `(1 + ε) μ ≤ J + 2` the same hypothesis gives
  `p 0 ≤ exp(-μ + (1 + δ) / (δ (ε - δ)))`.
* `upper_reduction` (A) : for `ε > 0` and `(1 + ε) μ ≤ J`, `p 0 ≤ exp(-μ + 2 (2 + ε) / ε²)`.
* `upper_reduction_sqrt` : under the same hypotheses `p 0 ≤ exp(-μ + (1 + √(1 + ε))² / ε²)`,
  the constant of `upper_reduction_of_lt` at the optimal `δ = √(1 + ε) - 1`.
* `lower_reduction` (B) : for `K ≥ 0`, if `G(j + 1) ≤ K μ F(j)` for every `j < J = ⌈2μ⌉`, then
  `p 0 ≥ ½ (e (1 + K / 2))^(-J)`.
-/

namespace Pairing

namespace SizeBias

open Finset

/-- `p` is a probability law on `ℕ` supported on `[0, N]`. -/
structure IsLaw (p : ℕ → ℝ) (N : ℕ) : Prop where
  nonneg : ∀ k, 0 ≤ p k
  eq_zero : ∀ k, N < k → p k = 0
  sum_eq_one : ∑ k ∈ range (N + 1), p k = 1

/-- `F(j) = ∑_{k ≤ j} p k`. -/
def cdf (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (j + 1), p k

/-- `G(j) = ∑_{k ≤ j} k p k`. For a law supported on `[0, N]` the mean is `G(N)`. -/
def partialMean (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (j + 1), (k : ℝ) * p k

variable {p : ℕ → ℝ} {N : ℕ}

/-- Sums against `p` may run over any range past the support. -/
theorem IsLaw.sum_range_mul (hp : IsLaw p N) (f : ℕ → ℝ) {R : ℕ} (hR : N + 1 ≤ R) :
    ∑ k ∈ range R, f k * p k = ∑ k ∈ range (N + 1), f k * p k := by
  rw [← sum_range_add_sum_Ico _ hR, add_eq_left]
  exact sum_eq_zero fun k hk ↦ by
    rw [hp.eq_zero k (by have := (mem_Ico.mp hk).1; omega), mul_zero]

/-- The masses sum to `1` over any range past the support. -/
theorem IsLaw.sum_range_eq_one (hp : IsLaw p N) {R : ℕ} (hR : N + 1 ≤ R) :
    ∑ k ∈ range R, p k = 1 := by
  simpa [hp.sum_eq_one] using hp.sum_range_mul (fun _ ↦ 1) hR

/-- `F(j) = 1` for `j ≥ N`. -/
theorem IsLaw.cdf_eq_one (hp : IsLaw p N) {j : ℕ} (hj : N ≤ j) : cdf p j = 1 :=
  hp.sum_range_eq_one (by omega)

/-- `F(j) ≥ 0`. -/
theorem IsLaw.cdf_nonneg (hp : IsLaw p N) (j : ℕ) : 0 ≤ cdf p j :=
  sum_nonneg fun k _ ↦ hp.nonneg k

/-- `F(j) ≤ 1`. -/
theorem IsLaw.cdf_le_one (hp : IsLaw p N) (j : ℕ) : cdf p j ≤ 1 := by
  rw [← hp.cdf_eq_one (j := j + N) (by omega)]
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
    fun k _ _ ↦ hp.nonneg k

/-- `G(j) ≥ 0`. -/
theorem IsLaw.partialMean_nonneg (hp : IsLaw p N) (j : ℕ) : 0 ≤ partialMean p j :=
  sum_nonneg fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) (hp.nonneg k)

/-- `G(j) = μ` for `j ≥ N`. -/
theorem IsLaw.partialMean_eq (hp : IsLaw p N) {j : ℕ} (hj : N ≤ j) :
    partialMean p j = partialMean p N :=
  hp.sum_range_mul (fun k ↦ (k : ℝ)) (by omega)

/-- `G(j + 1) = ∑_{k ≤ j} (k + 1) p (k + 1)`. -/
theorem partialMean_succ (j : ℕ) :
    partialMean p (j + 1) = ∑ k ∈ range (j + 1), ((k : ℝ) + 1) * p (k + 1) := by
  rw [partialMean, sum_range_succ']
  push_cast
  ring

/-- Markov's inequality, `(m + 1) P(X > m) ≤ μ`. -/
theorem IsLaw.markov (hp : IsLaw p N) (m : ℕ) : (m + 1) * (1 - cdf p m) ≤ partialMean p N := by
  have hR : m + 1 ≤ N + m + 2 := by omega
  have h1 := hp.sum_range_eq_one (R := N + m + 2) (by omega)
  have hμ := hp.sum_range_mul (fun k ↦ (k : ℝ)) (R := N + m + 2) (by omega)
  rw [← sum_range_add_sum_Ico _ hR] at h1 hμ
  rw [cdf, partialMean, ← hμ,
    show 1 - ∑ k ∈ range (m + 1), p k = ∑ k ∈ Ico (m + 1) (N + m + 2), p k by linarith, mul_sum]
  refine le_add_of_nonneg_of_le
    (sum_nonneg fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) (hp.nonneg k)) (sum_le_sum fun k hk ↦ ?_)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Ico.mp hk).1) (hp.nonneg k)

/-- Abel summation, `∑_{k < R} b_k x^k = ∑_{i < R} B_i (x^i - x^(i+1)) + B_{R-1} x^R` with
`B_i = ∑_{k ≤ i} b_k`. -/
theorem sum_mul_pow_eq (b : ℕ → ℝ) (x : ℝ) (R : ℕ) :
    ∑ k ∈ range R, b k * x ^ k =
      ∑ i ∈ range R, (∑ k ∈ range (i + 1), b k) * (x ^ i - x ^ (i + 1)) +
        (∑ k ∈ range R, b k) * x ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ, ih, sum_range_succ _ R, sum_range_succ b R]
    ring

/-- `∑_{J < i < R} (x^i - x^(i+1)) = x^(J+1) - x^R`. -/
theorem sum_Ico_pow_sub (x : ℝ) {J R : ℕ} (hJR : J + 1 ≤ R) :
    ∑ i ∈ Ico (J + 1) R, (x ^ i - x ^ (i + 1)) = x ^ (J + 1) - x ^ R := by
  induction R, hJR using Nat.le_induction with
  | base => simp
  | succ R hR ih =>
    rw [sum_Ico_succ_top hR, ih]
    ring

/-- If the partial sums `B_i` of `b` are nonnegative for `i ≤ J`, at least `-μ` for all `i`,
and vanish at `R - 1`, then `∑_{k < R} b_k x^k ≥ -μ x^(J+1)` on `[0, 1]`. -/
theorem le_sum_mul_pow {b : ℕ → ℝ} {x μ : ℝ} {J R : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hμ : 0 ≤ μ) (hJR : J + 1 ≤ R) (hle : ∀ i ≤ J, 0 ≤ ∑ k ∈ range (i + 1), b k)
    (hge : ∀ i, -μ ≤ ∑ k ∈ range (i + 1), b k) (hR : ∑ k ∈ range R, b k = 0) :
    -μ * x ^ (J + 1) ≤ ∑ k ∈ range R, b k * x ^ k := by
  have hstep : ∀ i : ℕ, 0 ≤ x ^ i - x ^ (i + 1) := fun i ↦
    sub_nonneg.mpr (pow_le_pow_of_le_one hx0 hx1 (Nat.le_succ i))
  rw [sum_mul_pow_eq, hR, zero_mul, add_zero, ← sum_range_add_sum_Ico _ hJR]
  have h1 : 0 ≤ ∑ i ∈ range (J + 1), (∑ k ∈ range (i + 1), b k) * (x ^ i - x ^ (i + 1)) :=
    sum_nonneg fun i hi ↦ mul_nonneg (hle i (by have := mem_range.mp hi; omega)) (hstep i)
  have h2 : ∑ i ∈ Ico (J + 1) R, -μ * (x ^ i - x ^ (i + 1)) ≤
      ∑ i ∈ Ico (J + 1) R, (∑ k ∈ range (i + 1), b k) * (x ^ i - x ^ (i + 1)) :=
    sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hge i) (hstep i)
  rw [← mul_sum, sum_Ico_pow_sub x hJR] at h2
  nlinarith [pow_nonneg hx0 R]

/-- The comparison step. If `μ F(j) ≤ G(j + 1)` for `j ≤ J`, then on `[0, 1]` the generating
function `L(x) = ∑ p k x^k` satisfies `L'(x) ≥ μ L(x) - μ x^(J+1)`. -/
theorem IsLaw.deriv_ge (hp : IsLaw p N) {J : ℕ}
    (hρ : ∀ j ≤ J, partialMean p N * cdf p j ≤ partialMean p (j + 1)) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    partialMean p N * ∑ k ∈ range (N + J + 2), p k * x ^ k - partialMean p N * x ^ (J + 1) ≤
      ∑ k ∈ range (N + J + 2), p k * ((k : ℝ) * x ^ (k - 1)) := by
  set μ := partialMean p N with hμ
  have hlow := le_sum_mul_pow (b := fun k ↦ ((k : ℝ) + 1) * p (k + 1) - μ * p k) (μ := μ)
    (J := J) (R := N + J + 1) hx0 hx1 (hp.partialMean_nonneg N) (by omega)
    (fun i hi ↦ by
      rw [sum_sub_distrib, ← mul_sum, ← partialMean_succ]
      exact sub_nonneg.mpr (hρ i hi))
    (fun i ↦ by
      rw [sum_sub_distrib, ← mul_sum, ← partialMean_succ]
      change -μ ≤ partialMean p (i + 1) - μ * cdf p i
      nlinarith [hp.partialMean_nonneg (i + 1), hp.cdf_le_one i, hp.partialMean_nonneg N])
    (by
      rw [sum_sub_distrib, ← mul_sum, ← partialMean_succ, hp.partialMean_eq (by omega),
        show ∑ k ∈ range (N + J + 1), p k = cdf p (N + J) from rfl, hp.cdf_eq_one (by omega)]
      ring)
  rw [sum_range_succ' (fun k ↦ p k * ((k : ℝ) * x ^ (k - 1))), sum_range_succ (fun k ↦ p k * x ^ k),
    hp.eq_zero (N + J + 1) (by omega)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] at hlow ⊢
  have : ∑ k ∈ range (N + J + 1), (((k : ℝ) + 1) * p (k + 1) - μ * p k) * x ^ k =
      ∑ k ∈ range (N + J + 1), p (k + 1) * (((k : ℝ) + 1) * x ^ k) -
        μ * ∑ k ∈ range (N + J + 1), p k * x ^ k := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  linarith

/-- The Markov step. `(m + 1) L(x) ≥ (m + 1 - μ) x^m` on `[0, 1]` for `m < R`. -/
theorem IsLaw.markov_pow (hp : IsLaw p N) {m R : ℕ} (hmR : m < R) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    (m + 1 - partialMean p N) * x ^ m ≤ (m + 1) * ∑ k ∈ range R, p k * x ^ k := by
  have h1 : x ^ m * cdf p m ≤ ∑ k ∈ range R, p k * x ^ k := by
    rw [cdf, mul_sum]
    refine (sum_le_sum fun k hk ↦ ?_).trans
      (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun k _ _ ↦
        mul_nonneg (hp.nonneg k) (pow_nonneg hx0 k))
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx0 hx1 (by have := mem_range.mp hk; omega)) (hp.nonneg k)
  have h2 := hp.markov m
  nlinarith [pow_nonneg hx0 m]

/-- The upper reduction with an explicit Markov cut `m`. If `μ F(j) ≤ G(j + 1)` for every
`j ≤ J`, `m ≤ J + 1` and `μ < m + 1`, then
`p 0 ≤ exp(-μ + μ (m + 1) / ((m + 1 - μ)(J + 2 - m)))`. -/
theorem upper_reduction_floor (hp : IsLaw p N) {μ : ℝ} (hμ : partialMean p N = μ) {J m : ℕ}
    (hmJ : m ≤ J + 1) (hμm : μ < m + 1)
    (hρ : ∀ j ≤ J, μ * cdf p j ≤ partialMean p (j + 1)) :
    p 0 ≤ Real.exp (-μ + μ * (m + 1) / ((m + 1 - μ) * (J + 2 - m))) := by
  subst hμ
  set μ := partialMean p N with hμ
  set d := J + 1 - m with hd
  have hdm : d + m = J + 1 := by omega
  have hpos : 0 < (m : ℝ) + 1 - μ := by linarith
  set c := μ * (m + 1) / (m + 1 - μ) with hc
  let L : ℝ → ℝ := fun x ↦ ∑ k ∈ range (N + J + 2), p k * x ^ k
  let g : ℝ → ℝ := fun x ↦ c / (d + 1) * x ^ (d + 1) - μ * x
  let ψ : ℝ → ℝ := fun x ↦ L x * Real.exp (g x)
  have hL : ∀ x, HasDerivAt L (∑ k ∈ range (N + J + 2), p k * ((k : ℝ) * x ^ (k - 1))) x :=
    fun x ↦ HasDerivAt.fun_sum fun k _ ↦ (hasDerivAt_pow k x).const_mul (p k)
  have hg : ∀ x, HasDerivAt g (c * x ^ d - μ) x := fun x ↦ by
    convert ((hasDerivAt_pow (d + 1) x).const_mul (c / (d + 1))).fun_sub
      ((hasDerivAt_id' (x := x)).const_mul μ) using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hψ : ∀ x, HasDerivAt ψ (Real.exp (g x) *
      ((∑ k ∈ range (N + J + 2), p k * ((k : ℝ) * x ^ (k - 1))) - μ * L x +
        c * x ^ d * L x)) x := fun x ↦ by
    convert (hL x).mul (hg x).exp using 1
    ring
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun x _ ↦ (hψ x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hψ x).differentiableAt.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Icc] at hx
    rw [(hψ x).deriv]
    have hx0 := hx.1.le
    have hx1 := hx.2.le
    have h1 := hp.deriv_ge hρ hx0 hx1
    have h2 := hp.markov_pow (m := m) (R := N + J + 2) (by omega) hx0 hx1
    have h3 : μ * x ^ (J + 1) ≤ c * x ^ d * L x := by
      rw [hc, ← hdm, pow_add, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (hp.partialMean_nonneg N) (pow_nonneg hx0 d))
      linarith
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have h0 : ψ 0 = p 0 := by
    simp [ψ, L, g, sum_range_succ']
  have h1 : ψ 1 = Real.exp (-μ + μ * (m + 1) / ((m + 1 - μ) * (J + 2 - m))) := by
    have hL1 : L 1 = 1 := by simpa [L] using hp.sum_range_eq_one (R := N + J + 2) (by omega)
    simp only [ψ, hL1, one_mul, g, one_pow, mul_one]
    congr 1
    rw [hc, hd, Nat.cast_sub hmJ]
    push_cast
    field_simp
    ring
  rw [← h0, ← h1]
  exact hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one

/-- The upper reduction for the Markov cut `M = (1 + δ) μ`. If `0 < δ < ε`,
`(1 + ε) μ ≤ J + 2` and `μ F(j) ≤ G(j + 1)` for every `j ≤ J`, then
`p 0 ≤ exp(-μ + (1 + δ) / (δ (ε - δ)))`. -/
theorem upper_reduction_of_lt (hp : IsLaw p N) {μ ε δ : ℝ} (hμ : partialMean p N = μ) {J : ℕ}
    (hδ : 0 < δ) (hδε : δ < ε) (hJ : (1 + ε) * μ ≤ J + 2)
    (hρ : ∀ j ≤ J, μ * cdf p j ≤ partialMean p (j + 1)) :
    p 0 ≤ Real.exp (-μ + (1 + δ) / (δ * (ε - δ))) := by
  have hμ0 : 0 ≤ μ := hμ ▸ hp.partialMean_nonneg N
  set m := ⌊(1 + δ) * μ⌋₊ with hm
  have hm1 : (m : ℝ) ≤ (1 + δ) * μ := Nat.floor_le (by positivity)
  have hm2 : (1 + δ) * μ < m + 1 := Nat.lt_floor_add_one _
  have hmJ' : (m : ℝ) < J + 2 := by nlinarith
  have hmJ : m ≤ J + 1 := by
    have : m < J + 2 := by exact_mod_cast hmJ'
    omega
  have hμm : μ < m + 1 := by nlinarith
  refine (upper_reduction_floor hp hμ hmJ hμm hρ).trans (Real.exp_le_exp.mpr ?_)
  have hA : δ * (m + 1) ≤ (1 + δ) * (m + 1 - μ) := by nlinarith
  have hC : μ * (ε - δ) ≤ J + 2 - m := by nlinarith
  have hprod := mul_le_mul hA hC (by nlinarith) (by nlinarith)
  have hJm : (0 : ℝ) < J + 2 - m := by linarith
  rw [add_le_add_iff_left, div_le_div_iff₀ (mul_pos (by linarith) hJm)
    (mul_pos hδ (by linarith))]
  nlinarith

/-- (A) Upper reduction. If `ε > 0`, `(1 + ε) μ ≤ J` and `μ F(j) ≤ G(j + 1)` for every
`j ≤ J`, then `p 0 ≤ exp(-μ + 2 (2 + ε) / ε²)`. -/
theorem upper_reduction (hp : IsLaw p N) {μ ε : ℝ} (hμ : partialMean p N = μ) {J : ℕ}
    (hε : 0 < ε) (hJ : (1 + ε) * μ ≤ J)
    (hρ : ∀ j ≤ J, μ * cdf p j ≤ partialMean p (j + 1)) :
    p 0 ≤ Real.exp (-μ + 2 * (2 + ε) / ε ^ 2) := by
  refine (upper_reduction_of_lt hp hμ (ε := ε) (δ := ε / 2) (by positivity) (by linarith)
    (by linarith) hρ).trans_eq ?_
  congr 2
  field_simp
  ring

/-- The upper reduction with the best constant of the method, `δ = √(1 + ε) - 1`. If `ε > 0`,
`(1 + ε) μ ≤ J` and `μ F(j) ≤ G(j + 1)` for every `j ≤ J`, then
`p 0 ≤ exp(-μ + (1 + √(1 + ε))² / ε²)`. -/
theorem upper_reduction_sqrt (hp : IsLaw p N) {μ ε : ℝ} (hμ : partialMean p N = μ) {J : ℕ}
    (hε : 0 < ε) (hJ : (1 + ε) * μ ≤ J)
    (hρ : ∀ j ≤ J, μ * cdf p j ≤ partialMean p (j + 1)) :
    p 0 ≤ Real.exp (-μ + (1 + √(1 + ε)) ^ 2 / ε ^ 2) := by
  have hs2 : √(1 + ε) ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
  have hs1 : 1 < √(1 + ε) := by
    rw [Real.lt_sqrt zero_le_one]
    linarith
  refine (upper_reduction_of_lt hp hμ (ε := ε) (δ := √(1 + ε) - 1) (by linarith)
    (by nlinarith) (by linarith) hρ).trans_eq ?_
  congr 2
  generalize √(1 + ε) = s at hs2 hs1
  rw [div_eq_div_iff (mul_ne_zero (by linarith) (by nlinarith)) (pow_pos hε 2).ne',
    show ε = s ^ 2 - 1 by linarith]
  ring

/-- (B) Lower reduction. For `K ≥ 0` and `J = ⌈2μ⌉`, if `G(j + 1) ≤ K μ F(j)` for every
`j < J`, then `p 0 ≥ ½ (e (1 + K / 2))^(-J)`. -/
theorem lower_reduction (hp : IsLaw p N) {μ K : ℝ} (hμ : partialMean p N = μ) (hK : 0 ≤ K)
    (hρ : ∀ j < ⌈2 * μ⌉₊, partialMean p (j + 1) ≤ K * μ * cdf p j) :
    1 / 2 * ((Real.exp 1 * (1 + K / 2)) ^ ⌈2 * μ⌉₊)⁻¹ ≤ p 0 := by
  have hμ0 : 0 ≤ μ := hμ ▸ hp.partialMean_nonneg N
  set J := ⌈2 * μ⌉₊ with hJ
  have hJμ : 2 * μ ≤ J := Nat.le_ceil _
  have hKμ : 0 ≤ K * μ := mul_nonneg hK hμ0
  have hstep : ∀ j ≤ J, cdf p j * j.factorial ≤ p 0 * ∏ i ∈ range j, ((i : ℝ) + 1 + K * μ) := by
    intro j hj
    induction j with
    | zero => simp [cdf]
    | succ j ih =>
      have h1 : ((j : ℝ) + 1) * p (j + 1) ≤ partialMean p (j + 1) := by
        rw [partialMean_succ]
        exact single_le_sum (f := fun k : ℕ ↦ ((k : ℝ) + 1) * p (k + 1))
          (fun k _ ↦ mul_nonneg (by positivity) (hp.nonneg _)) (self_mem_range_succ j)
      have h2 := mul_le_mul_of_nonneg_left (h1.trans (hρ j (by omega)))
        (Nat.cast_nonneg (α := ℝ) j.factorial)
      have h3 := mul_le_mul_of_nonneg_right (ih (by omega))
        (by positivity : (0 : ℝ) ≤ j + 1 + K * μ)
      rw [cdf, sum_range_succ, ← cdf, Nat.factorial_succ, prod_range_succ]
      push_cast
      nlinarith
  have hF : 1 / 2 ≤ cdf p J := by
    have h1 := hp.markov J
    have h2 := mul_le_mul_of_nonneg_right hJμ (sub_nonneg.mpr (hp.cdf_le_one J))
    rw [hμ] at h1
    nlinarith
  have hprod : ∏ i ∈ range J, ((i : ℝ) + 1 + K * μ) ≤ (J : ℝ) ^ J * (1 + K / 2) ^ J := by
    calc ∏ i ∈ range J, ((i : ℝ) + 1 + K * μ) ≤ ∏ _i ∈ range J, ((J : ℝ) * (1 + K / 2)) :=
          prod_le_prod₀ (fun i _ ↦ by positivity) fun i hi ↦ by
            have : (i : ℝ) + 1 ≤ J := by exact_mod_cast mem_range.mp hi
            nlinarith
      _ = (J : ℝ) ^ J * (1 + K / 2) ^ J := by rw [prod_const, card_range, mul_pow]
  have hfac : (J : ℝ) ^ J ≤ Real.exp 1 ^ J * J.factorial := by
    rw [Real.exp_one_pow, ← div_le_iff₀ (by positivity)]
    exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg J) J
  have hpos : (0 : ℝ) < J.factorial := by positivity
  have hK2 : (0 : ℝ) < (1 + K / 2) ^ J := pow_pos (by linarith) J
  have hp0 := hp.nonneg 0
  rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos (mul_pos (Real.exp_pos 1) (by linarith)) J),
    mul_pow]
  have key : 1 / 2 * (J.factorial : ℝ) ≤
      p 0 * (Real.exp 1 ^ J * (1 + K / 2) ^ J) * J.factorial :=
    calc 1 / 2 * (J.factorial : ℝ) ≤ cdf p J * J.factorial := by nlinarith
      _ ≤ p 0 * ∏ i ∈ range J, ((i : ℝ) + 1 + K * μ) := hstep J le_rfl
      _ ≤ p 0 * ((J : ℝ) ^ J * (1 + K / 2) ^ J) := mul_le_mul_of_nonneg_left hprod hp0
      _ ≤ p 0 * (Real.exp 1 ^ J * J.factorial * (1 + K / 2) ^ J) := by gcongr
      _ = p 0 * (Real.exp 1 ^ J * (1 + K / 2) ^ J) * J.factorial := by ring
  exact le_of_mul_le_mul_right key hpos

end SizeBias

end Pairing
