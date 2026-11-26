import Repair.PairVariance

/-!
# The spectral pair formula and its first-order term (Theorem 1)

Source: `results/hybrid-pair-averaged.md` (aed6f2d), §2, Theorem 1 and Corollary 1.1.

* `pairProb A B = h(A, B) = P_R(R ∪ A and R ∪ B both one cycle)`, and `pairProb_eq_k2Count` :
  it depends only on the type of `A ∪ B`, through the Lemma K2 recursion.
* `HamSpectral.omega` : `ω_ν(A, B) = |PM| E_ν(A, B) / d_ν`, the spherical function of a spectral
  resolution `S` of `H`, with `d_ν = tr E_ν`.
* `HamSpectral.pairProb_div_sq` : Theorem 1,
  `h(A, B) / p² = Σ_ν d_ν ω_ν((e))² ω_ν(A, B)` with `ω_ν((e)) = λ_ν / |Ham(B)|`.
* `levelOne e l = (2e - 3)((2e - 1) l - e) / (8 (e - 1)³)`, and `levelOne_eq` : it is
  `d ω((e))² ω(τ)` at `d = e(2e - 3)`, `ω((e)) = -1/(2(e - 1))` and
  `ω(τ) = ((2e - 1) l - e)/(2e(e - 1))`, the source's level-1 data.
* Corollary 1.1 : `levelOne_succ_sub` (the slope), `levelOne_zero` (the constant), and
  `abs_levelOne_sub_le` : `|L₁(l) - (l - 1/2)/(2e)| ≤ 4 (l + 1) / e²` for `e ≥ 2`, `l ≥ 0`.

The values of `d`, `ω((e))` and `ω(τ)` for `ν = (e - 1, 1)` are inputs to `levelOne_eq`. Their
derivation from the edge-sum description of `V_{(e)} ⊕ V_{(e-1,1)}` is not formalized here.
-/

open Finset

open scoped Matrix

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `h(A, B) = P_R(R ∪ A and R ∪ B both one cycle)` for `R` uniform on `PM`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
noncomputable def pairProb (A B : PerfectMatching W) : ℝ :=
  hamPairCount A B / Fintype.card (PerfectMatching W)

/-- `h(A, B)` depends only on the type of `A ∪ B`, through the Lemma K2 recursion
(`results/hybrid-pair-averaged.md`, Theorem 1; `results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem pairProb_eq_k2Count (A B : PerfectMatching W) :
    pairProb A B = k2Count (pairType A B) / Fintype.card (PerfectMatching W) := by
  rw [pairProb, hamPairCount_eq_k2Count]

/-- `|PM| h(A, B) = (H²)(A, B)` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem hamPairCount_eq_hamMat_sq (A B : PerfectMatching W) :
    (hamPairCount A B : ℝ) = ((hamMat * hamMat : Matrix _ _ ℝ) A B) := by
  rw [Matrix.mul_apply, hamPairCount, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun R _ ↦ ?_
  simp only [hamMat, Matrix.of_apply, hamInd, ham_comm A R]
  split_ifs <;> simp_all

namespace HamSpectral

variable {I : Type*} [Fintype I] [DecidableEq I] (S : HamSpectral W I)

/-- `ω_ν(A, B) = |PM| E_ν(A, B) / d_ν` with `d_ν = tr E_ν`, the spherical function of the
resolution (`results/hybrid-pair-averaged.md`, Theorem 1). -/
noncomputable def omega (ν : I) (A B : PerfectMatching W) : ℝ :=
  Fintype.card (PerfectMatching W) * S.E ν A B / (S.E ν).trace

/-- `tr E_ν = Σ_{A, C} E_ν(A, C)²`, so `tr E_ν = 0` forces `E_ν = 0`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem trace_eq_sum_sq (ν : I) : (S.E ν).trace = ∑ A, ∑ C, S.E ν A C ^ 2 := by
  have hEE : S.E ν * S.E ν = S.E ν := by rw [S.mul_E, ite_eq_left rfl]
  conv_lhs => rw [← hEE]
  rw [Matrix.trace]
  refine sum_congr rfl fun A _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine sum_congr rfl fun C _ ↦ ?_
  rw [sq]
  congr 1
  exact congrFun (congrFun (S.transpose_E ν) A) C

/-- A projection of trace `0` vanishes (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem E_eq_zero_of_trace (ν : I) (h : (S.E ν).trace = 0) (A C : PerfectMatching W) :
    S.E ν A C = 0 := by
  rw [trace_eq_sum_sq] at h
  have h1 := (sum_eq_zero_iff_of_nonneg fun A _ ↦
    sum_nonneg fun C _ ↦ sq_nonneg (S.E ν A C)).mp h A (mem_univ A)
  have h2 := (sum_eq_zero_iff_of_nonneg fun C _ ↦ sq_nonneg (S.E ν A C)).mp h1 C (mem_univ C)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2

/-- Theorem 1, the spectral pair formula `h(A, B) / p² = Σ_ν d_ν ω_ν((e))² ω_ν(A, B)` with
`ω_ν((e)) = λ_ν / |Ham(B)|` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem pairProb_div_sq (A B : PerfectMatching W) (hk : hamDeg B ≠ 0) :
    pairProb A B / hamProb B ^ 2 =
      ∑ ν, (S.E ν).trace * (S.eig ν / hamDeg B) ^ 2 * S.omega ν A B := by
  have hN : (Fintype.card (PerfectMatching W) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne'
  have hk' : (hamDeg B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [pairProb, hamProb, hamPairCount_eq_hamMat_sq, S.hamMat_eq, S.sum_smul_mul_sum_smul,
    Matrix.sum_apply, sum_div, sum_div]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [Matrix.smul_apply, smul_eq_mul, omega]
  by_cases htr : (S.E ν).trace = 0
  · rw [S.E_eq_zero_of_trace ν htr A B, htr]
    simp
  · field_simp

end HamSpectral

/-- `L₁(l) = (2e - 3)((2e - 1) l - e) / (8 (e - 1)³)`, the level-1 term of Theorem 1
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
noncomputable def levelOne (e l : ℝ) : ℝ :=
  (2 * e - 3) * ((2 * e - 1) * l - e) / (8 * (e - 1) ^ 3)

/-- `L₁(l) = d ω((e))² ω(τ)` at the level-1 data `d = e(2e - 3)`, `ω((e)) = -1/(2(e - 1))`,
`ω(τ) = ((2e - 1) l - e)/(2e(e - 1))` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem levelOne_eq {e : ℝ} (he0 : e ≠ 0) (he1 : e ≠ 1) (l : ℝ) :
    e * (2 * e - 3) * (-1 / (2 * (e - 1))) ^ 2 * (((2 * e - 1) * l - e) / (2 * e * (e - 1))) =
      levelOne e l := by
  have h1 : e - 1 ≠ 0 := sub_ne_zero.mpr he1
  rw [levelOne]
  field_simp
  ring

/-- Corollary 1.1, the slope of `L₁` in `l` is `(2e - 1)(2e - 3)/(8(e - 1)³)`
(`results/hybrid-pair-averaged.md`, Corollary 1.1). -/
theorem levelOne_succ_sub (e l : ℝ) :
    levelOne e (l + 1) - levelOne e l = (2 * e - 1) * (2 * e - 3) / (8 * (e - 1) ^ 3) := by
  rw [levelOne, levelOne, ← sub_div]
  ring

/-- Corollary 1.1, the constant `L₁(0) = -e(2e - 3)/(8(e - 1)³)`
(`results/hybrid-pair-averaged.md`, Corollary 1.1). -/
theorem levelOne_zero (e : ℝ) : levelOne e 0 = -(e * (2 * e - 3)) / (8 * (e - 1) ^ 3) := by
  rw [levelOne]
  ring

/-- The exact error `L₁(l) - (l - 1/2)/(2e) = (l(4e² - 9e + 4) - 3e² + 6e - 2)/(8e(e - 1)³)`
(`results/hybrid-pair-averaged.md`, Corollary 1.1). -/
theorem levelOne_sub {e : ℝ} (he0 : e ≠ 0) (he1 : e ≠ 1) (l : ℝ) :
    levelOne e l - (l - 1 / 2) / (2 * e) =
      (l * (4 * e ^ 2 - 9 * e + 4) - 3 * e ^ 2 + 6 * e - 2) / (8 * e * (e - 1) ^ 3) := by
  have h1 : e - 1 ≠ 0 := sub_ne_zero.mpr he1
  rw [levelOne]
  field_simp
  ring

/-- Corollary 1.1, `L₁(l) = (l - 1/2)/(2e) + O((l + 1)/e²)`, with constant `4` for `e ≥ 2` and
`l ≥ 0` (`results/hybrid-pair-averaged.md`, Corollary 1.1). -/
theorem abs_levelOne_sub_le {e l : ℝ} (he : 2 ≤ e) (hl : 0 ≤ l) :
    |levelOne e l - (l - 1 / 2) / (2 * e)| ≤ 4 * (l + 1) / e ^ 2 := by
  have he0 : e ≠ 0 := by positivity
  have he1 : e ≠ 1 := by intro h; rw [h] at he; norm_num at he
  rw [levelOne_sub he0 he1]
  have hden : e ^ 4 ≤ 8 * e * (e - 1) ^ 3 := by
    have h1 : e / 2 ≤ e - 1 := by linarith
    have h2 : (e / 2) ^ 3 ≤ (e - 1) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    nlinarith [pow_pos (show (0 : ℝ) < e by linarith) 3]
  have hpos : 0 < 8 * e * (e - 1) ^ 3 := by
    have : 0 < e - 1 := by linarith
    positivity
  have hnum : |l * (4 * e ^ 2 - 9 * e + 4) - 3 * e ^ 2 + 6 * e - 2| ≤ 4 * e ^ 2 * (l + 1) := by
    have h8 : 0 ≤ 8 * e ^ 2 - 9 * e + 4 := by nlinarith
    have h9 : 0 ≤ 9 * e - 4 := by linarith
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hl h8]
    · nlinarith [mul_nonneg hl h9]
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  calc |l * (4 * e ^ 2 - 9 * e + 4) - 3 * e ^ 2 + 6 * e - 2| * e ^ 2
      ≤ 4 * e ^ 2 * (l + 1) * e ^ 2 := by gcongr
    _ = 4 * (l + 1) * e ^ 4 := by ring
    _ ≤ 4 * (l + 1) * (8 * e * (e - 1) ^ 3) := by gcongr

end PerfectMatching

end Pairing
