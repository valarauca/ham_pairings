import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Suppression.SizeBias

/-!
# Factorial cumulants, central moments and the lower tail (`hybrid-assembly.md`, §4)

The probability core of the hybrid-tail route of `results/hybrid-assembly.md`, for an abstract
law `p` on `[0, N]` (`SizeBias.IsLaw p N`) with mean `μ = partialMean p N`. Generating functions
are formal power series over `ℝ`.

* `mgf p N = E e^(sX)`, `fmgf p N = E (1 + z)^X` and `cmgf p N = E e^(s(X - μ))`.
* `cumulant p N r = r! [s^r] log E e^(sX)`, the cumulant `κ_r`.
* `factCumulant p N j = j! [z^j] log E (1 + z)^X`, the factorial cumulant `κ^f_j` of §1.
* `centralMoment p N n = E (X - μ)^n`.

The results, in the order of the note.

* `factCumulant_one`, `cumulant_one` : `κ^f_1 = κ_1 = μ`.
* `logOf_mgf_eq_subst` : `log E e^(sX) = (log E(1 + z)^X)(e^s - 1)`.
* `abs_cumulant_le` (Lemma 7) : if `|κ^f_j| ≤ j! H μ A^(j - 2)` for `2 ≤ j ≤ r` with `H, A ≥ 1`,
  then `|κ_r| ≤ r! (2H) μ (2A)^(r - 2)`.
* `centralMoment_le_sum` and `centralMoment_le_cosh` (Lemma 6) : if
  `|κ_r| ≤ r! H' μ A'^(r - 2)` for `2 ≤ r ≤ 2k`, then
  `E(X - μ)^(2k) ≤ (2k)! ∑_(b ≤ k) (H' μ)^b A'^(2k - 2b) C(2k - b - 1, b - 1) / b!
  ≤ (2k H' μ)^k cosh(2 A' k^(3/2) (H' μ)^(-1/2))`.
* `centralMoment_le_of_factCumulant` (Proposition 8, the inequality (H-JI*)) and
  `prob_zero_le_of_factCumulant` (Proposition 8) : if `H ≥ 1`, `H μ ≥ 8k` and
  `|κ^f_j| ≤ j! H μ (H μ / (8k))^((j - 2)/2)` for `2 ≤ j ≤ 2k`, then
  `E(X - μ)^(2k) ≤ (4e H k μ)^k` and `P(X = 0) ≤ (4e H k / μ)^k`.

The general power-series facts used on the way are `coeff_subst_eq_sum` (coefficients of a
substitution as a finite sum), `abs_coeff_pow_le` (coefficientwise majorants pass to powers),
`exp_subst_add` (`e^(f + g) = e^f e^g`) and `exp_subst_logOf` (`e^(log f) = f`).
-/

namespace Pairing

namespace CumulantTail

open PowerSeries Finset SizeBias Nat

section Series

/-- `[s^n] b^d = 0` for `n < d` when `b` has no constant term. -/
theorem coeff_pow_eq_zero_of_lt {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) {n d : ℕ} (h : n < d) :
    coeff n (b ^ d) = 0 := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hb
  rw [mul_pow, coeff_X_pow_mul']
  split_ifs
  · omega
  · rfl

/-- The coefficients of a substitution `f(b)` with `b(0) = 0`, as a finite sum:
`[s^n] f(b) = ∑_(d ≤ n) [z^d] f · [s^n] b^d`. -/
theorem coeff_subst_eq_sum {b : ℝ⟦X⟧} (hb : constantCoeff b = 0) (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (f.subst b) = ∑ d ∈ range (n + 1), coeff d f * coeff n (b ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hb),
    finsum_eq_sum_of_support_subset (s := range (n + 1))]
  · simp only [smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [coeff_pow_eq_zero_of_lt hb (by omega), smul_zero])

/-- Powers of a series with nonnegative coefficients have nonnegative coefficients. -/
theorem coeff_pow_nonneg {g : ℝ⟦X⟧} (hg : ∀ i, 0 ≤ coeff i g) (b i : ℕ) :
    0 ≤ coeff i (g ^ b) := by
  induction b generalizing i with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ b ih =>
    rw [pow_succ, coeff_mul]
    exact sum_nonneg fun x _ ↦ mul_nonneg (ih _) (hg _)

/-- Coefficientwise majorants pass to powers. If `|[s^i] f| ≤ [s^i] g` for `i ≤ n` and `g` has
nonnegative coefficients, then `|[s^i] f^b| ≤ [s^i] g^b` for `i ≤ n`. -/
theorem abs_coeff_pow_le {f g : ℝ⟦X⟧} {n : ℕ} (hfg : ∀ i ≤ n, |coeff i f| ≤ coeff i g)
    (hg : ∀ i, 0 ≤ coeff i g) (b : ℕ) : ∀ i ≤ n, |coeff i (f ^ b)| ≤ coeff i (g ^ b) := by
  induction b with
  | zero =>
    intro i _
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ b ih =>
    intro i hi
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x hx ↦ ?_)
    have hx' := mem_antidiagonal.mp hx
    rw [abs_mul]
    exact mul_le_mul (ih _ (by omega)) (hfg _ (by omega)) (abs_nonneg _)
      (coeff_pow_nonneg hg _ _)

/-- `[s^n] (s^e (1 - As)^(-1))^(d + 1) = A^(n - e(d + 1)) C(d + n - e(d + 1), d)` when
`e(d + 1) ≤ n`, and `0` otherwise. -/
theorem coeff_X_pow_mul_rescale_pow (e : ℕ) (A : ℝ) (d n : ℕ) :
    coeff n ((X ^ e * rescale A (mk 1 : ℝ⟦X⟧)) ^ (d + 1)) =
      if e * (d + 1) ≤ n then A ^ (n - e * (d + 1)) * ((d + (n - e * (d + 1))).choose d : ℝ)
      else 0 := by
  rw [mul_pow, ← pow_mul, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_X_pow_mul']
  split_ifs
  · rw [coeff_rescale, coeff_mk]
  · rfl

/-- `e^f(0) = 1` when `f(0) = 0`. -/
theorem constantCoeff_exp_subst {f : ℝ⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff ((exp ℝ).subst f) = 1 := by
  rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hf, constantCoeff_exp, map_one]

/-- `(e^f)' = e^f f'` when `f(0) = 0`. -/
theorem derivative_exp_subst {f : ℝ⟦X⟧} (hf : constantCoeff f = 0) :
    d⁄dX ((exp ℝ).subst f) = (exp ℝ).subst f * d⁄dX f := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hf), derivative_exp]

/-- Uniqueness for `Y' = hY`. Two series with `Y' = hY`, `Z' = hZ` and `Y(0) = Z(0) = 1` are
equal. -/
theorem eq_of_derivative_eq_mul {h Y Z : ℝ⟦X⟧} (hY : d⁄dX Y = h * Y) (hZ : d⁄dX Z = h * Z)
    (hY0 : constantCoeff Y = 1) (hZ0 : constantCoeff Z = 1) : Y = Z := by
  have : HasUniqueDiv ℝ := .of_module_rat ℝ
  have : Invertible Z := (isUnit_iff_constantCoeff.mpr (by rw [hZ0]; exact isUnit_one)).invertible
  have hZZ : ⅟Z * Z = 1 := invOf_mul_self Z
  have hc : constantCoeff (⅟Z) = 1 := by
    have h := congrArg (constantCoeff (R := ℝ)) hZZ
    rwa [map_mul, hZ0, mul_one, map_one] at h
  have key : Y * ⅟Z = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, derivative_invOf, hY, hZ, derivative_one, smul_eq_mul, smul_eq_mul]
      linear_combination (-(Y * h * ⅟Z)) * hZZ
    · rw [map_mul, hY0, hc, map_one, one_mul]
  calc Y = Y * ⅟Z * Z := by rw [mul_assoc, hZZ, mul_one]
    _ = Z := by rw [key, one_mul]

/-- `e^(f + g) = e^f e^g` when `f(0) = g(0) = 0`. -/
theorem exp_subst_add {f g : ℝ⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (exp ℝ).subst (f + g) = (exp ℝ).subst f * (exp ℝ).subst g := by
  have hfg : constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  refine eq_of_derivative_eq_mul (h := d⁄dX (f + g)) ?_ ?_ (constantCoeff_exp_subst hfg) ?_
  · rw [derivative_exp_subst hfg, mul_comm]
  · rw [Derivation.leibniz, derivative_exp_subst hf, derivative_exp_subst hg, map_add,
      smul_eq_mul, smul_eq_mul]
    ring
  · rw [map_mul, constantCoeff_exp_subst hf, constantCoeff_exp_subst hg, one_mul]

/-- `e^(log f) = f` when `f(0) = 1`. -/
theorem exp_subst_logOf {f : ℝ⟦X⟧} (hf : constantCoeff f = 1) :
    (exp ℝ).subst (logOf f) = f := by
  have h1 : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by rw [map_sub, hf, map_one,
    sub_self])
  rw [logOf_eq, ← subst_comp_subst_apply HasSubst.log h1, subst_exp_log, subst_add h1,
    subst_X h1, ← coe_substAlgHom h1, map_one]
  ring

/-- `log f(u) = (log f)(u)` when `f(0) = 1` and `u(0) = 0`. -/
theorem logOf_subst {f u : ℝ⟦X⟧} (hf : constantCoeff f = 1) (hu : constantCoeff u = 0) :
    logOf (f.subst u) = (logOf f).subst u := by
  have h1 : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by rw [map_sub, hf, map_one,
    sub_self])
  have hu' : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  rw [logOf_eq, logOf_eq, subst_comp_subst_apply h1 hu', subst_sub hu', ← coe_substAlgHom hu',
    map_one]

/-- `[s^n] s^e (1 - As)^(-1) = A^(n - e)` for `e ≤ n`, and `0` otherwise. -/
theorem coeff_X_pow_mul_rescale (e : ℕ) (A : ℝ) (n : ℕ) :
    coeff n (X ^ e * rescale A (mk 1 : ℝ⟦X⟧)) = if e ≤ n then A ^ (n - e) else 0 := by
  rw [coeff_X_pow_mul']
  split_ifs
  · rw [coeff_rescale, coeff_mk, Pi.one_apply, mul_one]
  · rfl

/-- `[s^n] e^(as) = a^n / n!`. -/
theorem coeff_rescale_exp (a : ℝ) (n : ℕ) : coeff n (rescale a (exp ℝ)) = a ^ n / n ! := by
  rw [coeff_rescale, coeff_exp, map_div₀, map_one, map_natCast, mul_one_div]

/-- `[s^1] log f = [s^1] f` when `f(0) = 1`. -/
theorem coeff_one_logOf {f : ℝ⟦X⟧} (hf : constantCoeff f = 1) : coeff 1 (logOf f) = coeff 1 f := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  rw [logOf_eq, coeff_subst_eq_sum h1, sum_range_succ, sum_range_one, pow_zero, pow_one,
    coeff_one_log, coeff_zero_eq_constantCoeff_apply, constantCoeff_log, zero_mul, zero_add,
    one_mul, map_sub, coeff_one, ite_eq_right one_ne_zero, sub_zero]

end Series

section Laws

variable {p : ℕ → ℝ} {N : ℕ}

/-- The moment generating function `E e^(sX) = ∑_k p k e^(ks)` of a law on `[0, N]`. -/
noncomputable def mgf (p : ℕ → ℝ) (N : ℕ) : ℝ⟦X⟧ :=
  ∑ k ∈ range (N + 1), p k • rescale (k : ℝ) (exp ℝ)

/-- The factorial moment generating function `E (1 + z)^X = ∑_k p k (1 + z)^k`. -/
noncomputable def fmgf (p : ℕ → ℝ) (N : ℕ) : ℝ⟦X⟧ :=
  ∑ k ∈ range (N + 1), p k • (1 + X) ^ k

/-- The central moment generating function `E e^(s(X - μ))`. -/
noncomputable def cmgf (p : ℕ → ℝ) (N : ℕ) : ℝ⟦X⟧ :=
  ∑ k ∈ range (N + 1), p k • rescale ((k : ℝ) - partialMean p N) (exp ℝ)

/-- The cumulant `κ_r = r! [s^r] log E e^(sX)`. -/
noncomputable def cumulant (p : ℕ → ℝ) (N r : ℕ) : ℝ :=
  (r ! : ℝ) * coeff r (logOf (mgf p N))

/-- The factorial cumulant `κ^f_j = j! [z^j] log E (1 + z)^X` (`hybrid-assembly.md`, §1). -/
noncomputable def factCumulant (p : ℕ → ℝ) (N j : ℕ) : ℝ :=
  (j ! : ℝ) * coeff j (logOf (fmgf p N))

/-- The central moment `E (X - μ)^n`. -/
noncomputable def centralMoment (p : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), p k * ((k : ℝ) - partialMean p N) ^ n

/-- `[s^n] E e^(sX) = E X^n / n!`. -/
theorem coeff_mgf (n : ℕ) :
    coeff n (mgf p N) = (∑ k ∈ range (N + 1), p k * (k : ℝ) ^ n) / n ! := by
  rw [mgf, map_sum, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [coeff_smul, coeff_rescale_exp, smul_eq_mul]
  ring

/-- `[s^n] E e^(s(X - μ)) = E (X - μ)^n / n!`. -/
theorem coeff_cmgf (n : ℕ) : coeff n (cmgf p N) = centralMoment p N n / n ! := by
  rw [cmgf, centralMoment, map_sum, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [coeff_smul, coeff_rescale_exp, smul_eq_mul]
  ring

/-- `E e^(sX)` has constant term `1`. -/
theorem constantCoeff_mgf (hp : IsLaw p N) : constantCoeff (mgf p N) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mgf]
  simp [hp.sum_eq_one]

/-- `[s^1] E e^(sX) = μ`. -/
theorem coeff_one_mgf : coeff 1 (mgf p N) = partialMean p N := by
  rw [coeff_mgf, partialMean]
  simp [mul_comm]

/-- `E (1 + z)^X` has constant term `1`. -/
theorem constantCoeff_fmgf (hp : IsLaw p N) : constantCoeff (fmgf p N) = 1 := by
  rw [fmgf, map_sum]
  simp [hp.sum_eq_one]

/-- `E e^(sX) = E (1 + (e^s - 1))^X`. -/
theorem fmgf_subst : (fmgf p N).subst (exp ℝ - 1) = mgf p N := by
  have hu : HasSubst (exp ℝ - 1) := HasSubst.exp_sub_one
  rw [fmgf, ← coe_substAlgHom hu, map_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_pow, map_add, map_one, coe_substAlgHom, subst_X hu, add_sub_cancel,
    exp_pow_eq_rescale_exp]

/-- `log E e^(sX) = (log E (1 + z)^X)(e^s - 1)`, the generating-function form of
`κ_r = ∑_j S(r, j) κ^f_j` (proof of Lemma 7 of `hybrid-assembly.md`). -/
theorem logOf_mgf_eq_subst (hp : IsLaw p N) :
    logOf (mgf p N) = (logOf (fmgf p N)).subst (exp ℝ - 1) := by
  rw [← fmgf_subst, logOf_subst (constantCoeff_fmgf hp) (by simp [constantCoeff_exp])]

/-- `κ_1 = μ`. -/
theorem cumulant_one (hp : IsLaw p N) : cumulant p N 1 = partialMean p N := by
  rw [cumulant, coeff_one_logOf (constantCoeff_mgf hp), coeff_one_mgf, factorial_one, cast_one,
    one_mul]

/-- `κ^f_1 = μ` (`hybrid-assembly.md`, §1). -/
theorem factCumulant_one (hp : IsLaw p N) : factCumulant p N 1 = partialMean p N := by
  have hu : constantCoeff (exp ℝ - 1 : ℝ⟦X⟧) = 0 := by simp [constantCoeff_exp]
  have h := cumulant_one hp
  rw [cumulant, logOf_mgf_eq_subst hp, coeff_subst_eq_sum hu, sum_range_succ, sum_range_one,
    pow_zero, pow_one, coeff_one, ite_eq_right one_ne_zero, mul_zero, zero_add, map_sub, coeff_one,
    ite_eq_right one_ne_zero, sub_zero, coeff_exp] at h
  rw [factCumulant, ← h]
  simp

/-- The majorant `s / (1 - s)` of `e^s - 1`: `|[s^i] (e^s - 1)| ≤ [s^i] s (1 - s)^(-1)`. -/
theorem abs_coeff_exp_sub_one_le (i : ℕ) :
    |coeff i (exp ℝ - 1 : ℝ⟦X⟧)| ≤ coeff i (X ^ 1 * rescale (1 : ℝ) (mk 1 : ℝ⟦X⟧)) := by
  rw [coeff_X_pow_mul_rescale, map_sub, coeff_exp, coeff_one, map_div₀, map_one, map_natCast]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [ite_eq_right hi.ne', ite_eq_left (show 1 ≤ i from hi), sub_zero, one_pow,
      abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (factorial_ne_zero i))
      (by positivity)

/-- `∑_(j ≤ r) [s^r] (s / (1 - s))^j = 2^(r - 1)` for `r ≥ 1`, the Fubini-type bound of the
proof of Lemma 7 of `hybrid-assembly.md`. -/
theorem sum_coeff_geom_pow {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ range (r + 1), coeff r ((X ^ 1 * rescale (1 : ℝ) (mk 1 : ℝ⟦X⟧)) ^ j) =
      2 ^ (r - 1) := by
  rw [sum_range_succ', pow_zero, coeff_one, ite_eq_right (by omega), add_zero]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [add_tsub_cancel_right, show (2 : ℝ) ^ s = ((2 ^ s : ℕ) : ℝ) by push_cast; rfl,
    ← Nat.sum_range_choose s, cast_sum]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd' := mem_range.mp hd
  rw [coeff_X_pow_mul_rescale_pow, ite_eq_left (by omega), one_pow, one_mul]
  congr 2
  omega

/-- The bound `|[z^j] log E(1 + z)^X| ≤ H μ A^(r - 2)` for `1 ≤ j ≤ r`, from the hypothesis of
Lemma 7 of `hybrid-assembly.md`. -/
theorem abs_coeff_logOf_fmgf_le (hp : IsLaw p N) {H A : ℝ} (hH : 1 ≤ H) (hA : 1 ≤ A) {r : ℕ}
    (hr : 2 ≤ r)
    (hκ : ∀ j, 2 ≤ j → j ≤ r → |factCumulant p N j| ≤ j ! * H * partialMean p N * A ^ (j - 2))
    {j : ℕ} (hj : j ≤ r) : |coeff j (logOf (fmgf p N))| ≤ H * partialMean p N * A ^ (r - 2) := by
  have hμ := hp.partialMean_nonneg N
  have hAr : 1 ≤ A ^ (r - 2) := one_le_pow₀ hA
  rcases j with _ | _ | j
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf (constantCoeff_fmgf hp), abs_zero]
    positivity
  · have h := factCumulant_one hp
    rw [factCumulant, factorial_one, cast_one, one_mul] at h
    rw [zero_add, h, abs_of_nonneg hμ]
    calc partialMean p N = 1 * partialMean p N * 1 := by ring
      _ ≤ H * partialMean p N * A ^ (r - 2) := by gcongr
  · have h := hκ (j + 2) (by omega) hj
    rw [factCumulant, abs_mul, abs_of_nonneg (by positivity)] at h
    have hf : (0 : ℝ) < (j + 2) ! := by exact_mod_cast factorial_pos (j + 2)
    calc |coeff (j + 2) (logOf (fmgf p N))| ≤ H * partialMean p N * A ^ (j + 2 - 2) := by
          rw [← mul_le_mul_iff_right₀ hf]
          linarith
      _ ≤ H * partialMean p N * A ^ (r - 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega)) (by positivity)

/-- Lemma 7 of `hybrid-assembly.md` (factorial to ordinary cumulants). For a law on `[0, N]`, if
`|κ^f_j| ≤ j! H μ A^(j - 2)` for `2 ≤ j ≤ r` with `H, A ≥ 1`, then
`|κ_r| ≤ r! (2H) μ (2A)^(r - 2)`. The file's hypothesis `κ^f_1 = μ` is `factCumulant_one`. -/
theorem abs_cumulant_le (hp : IsLaw p N) {H A : ℝ} (hH : 1 ≤ H) (hA : 1 ≤ A) {r : ℕ} (hr : 2 ≤ r)
    (hκ : ∀ j, 2 ≤ j → j ≤ r → |factCumulant p N j| ≤ j ! * H * partialMean p N * A ^ (j - 2)) :
    |cumulant p N r| ≤ r ! * (2 * H) * partialMean p N * (2 * A) ^ (r - 2) := by
  have hu : constantCoeff (exp ℝ - 1 : ℝ⟦X⟧) = 0 := by simp [constantCoeff_exp]
  have hμ := hp.partialMean_nonneg N
  set B := H * partialMean p N * A ^ (r - 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have hg : ∀ i, 0 ≤ coeff i (X ^ 1 * rescale (1 : ℝ) (mk 1 : ℝ⟦X⟧)) := fun i ↦ by
    rw [coeff_X_pow_mul_rescale]
    split_ifs <;> norm_num
  have hcoeff : |coeff r (logOf (mgf p N))| ≤ B * 2 ^ (r - 1) := by
    rw [logOf_mgf_eq_subst hp, coeff_subst_eq_sum hu, ← sum_coeff_geom_pow (by omega), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul
      (abs_coeff_logOf_fmgf_le hp hH hA hr hκ (Nat.lt_succ_iff.mp (mem_range.mp hj)))
      (abs_coeff_pow_le (fun i _ ↦ abs_coeff_exp_sub_one_le i) hg j r le_rfl) (abs_nonneg _) hB0
  rw [cumulant, abs_mul, abs_of_nonneg (by positivity)]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have hf : (0 : ℝ) ≤ (s + 2) ! := by positivity
  calc ((s + 2) ! : ℝ) * |coeff (s + 2) (logOf (mgf p N))| ≤ (s + 2) ! * (B * 2 ^ (s + 2 - 1)) :=
        mul_le_mul_of_nonneg_left hcoeff hf
    _ = (s + 2) ! * (2 * H) * partialMean p N * (2 * A) ^ (s + 2 - 2) := by
        rw [hB, show s + 2 - 1 = s + 1 by omega, show s + 2 - 2 = s by omega]
        ring

/-- `E e^(s(X - μ)) = e^(log E e^(sX) - μ s)`. -/
theorem cmgf_eq_exp_subst (hp : IsLaw p N) :
    cmgf p N = (exp ℝ).subst (logOf (mgf p N) + (-partialMean p N) • X) := by
  rw [exp_subst_add (constantCoeff_logOf (constantCoeff_mgf hp)) (by simp),
    exp_subst_logOf (constantCoeff_mgf hp), ← rescale_eq_subst, mgf, sum_mul, cmgf]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [smul_mul_assoc, exp_mul_exp_eq_exp_add, sub_eq_add_neg]

/-- The majorant of the centered cumulant series. If `|κ_r| ≤ r! a A^(r - 2)` for
`2 ≤ r ≤ n`, then `|[s^i] (log E e^(sX) - μ s)| ≤ [s^i] a s² (1 - As)^(-1)` for `i ≤ n`. -/
theorem abs_coeff_centCum_le (hp : IsLaw p N) {a A : ℝ} {n : ℕ}
    (hκ : ∀ r, 2 ≤ r → r ≤ n → |cumulant p N r| ≤ r ! * a * A ^ (r - 2)) {i : ℕ} (hi : i ≤ n) :
    |coeff i (logOf (mgf p N) + (-partialMean p N) • X)| ≤
      coeff i (a • (X ^ 2 * rescale A (mk 1 : ℝ⟦X⟧))) := by
  rw [map_add, coeff_smul, coeff_smul, coeff_X_pow_mul_rescale, coeff_X, smul_eq_mul, smul_eq_mul]
  rcases i with _ | _ | i
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf (constantCoeff_mgf hp)]
    simp
  · rw [zero_add, coeff_one_logOf (constantCoeff_mgf hp), coeff_one_mgf]
    simp
  · rw [ite_eq_right (by omega), mul_zero, add_zero, ite_eq_left (by omega),
      show i + 2 - 2 = i by omega]
    have h := hκ (i + 2) (by omega) hi
    rw [cumulant, abs_mul, abs_of_nonneg (by positivity), add_tsub_cancel_right] at h
    have hf : (0 : ℝ) < (i + 2) ! := by exact_mod_cast factorial_pos (i + 2)
    rw [← mul_le_mul_iff_right₀ hf]
    linarith

/-- The first half of Lemma 6 of `hybrid-assembly.md` (cumulants to central moments). If
`|κ_r| ≤ r! a A^(r - 2)` for `2 ≤ r ≤ 2k` with `a, A ≥ 0`, then
`E(X - μ)^(2k) ≤ (2k)! ∑_(1 ≤ b ≤ k) a^b A^(2k - 2b) C(2k - b - 1, b - 1) / b!`, written with
`b = d + 1`. -/
theorem centralMoment_le_sum (hp : IsLaw p N) {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) {k : ℕ}
    (hk : 1 ≤ k) (hκ : ∀ r, 2 ≤ r → r ≤ 2 * k → |cumulant p N r| ≤ r ! * a * A ^ (r - 2)) :
    centralMoment p N (2 * k) ≤ (2 * k) ! * ∑ d ∈ range k,
      a ^ (d + 1) * A ^ (2 * k - 2 * (d + 1)) * ((2 * k - d - 2).choose d : ℝ) / (d + 1) ! := by
  set L := logOf (mgf p N) + (-partialMean p N) • X with hLdef
  set G := X ^ 2 * rescale A (mk 1 : ℝ⟦X⟧) with hGdef
  have hL0 : constantCoeff L = 0 := by
    rw [hLdef, map_add, constantCoeff_logOf (constantCoeff_mgf hp)]
    simp
  have hG : ∀ i, 0 ≤ coeff i (a • G) := fun i ↦ by
    rw [coeff_smul, hGdef, coeff_X_pow_mul_rescale, smul_eq_mul]
    split_ifs <;> positivity
  have hmaj := abs_coeff_pow_le (fun i hi ↦ abs_coeff_centCum_le hp hκ hi) hG
  have hf : (0 : ℝ) < (2 * k) ! := by exact_mod_cast factorial_pos (2 * k)
  have hc : centralMoment p N (2 * k) = (2 * k) ! * coeff (2 * k) (cmgf p N) := by
    rw [coeff_cmgf]
    field_simp
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ hf.le
  rw [cmgf_eq_exp_subst hp, ← hLdef, coeff_subst_eq_sum hL0]
  calc ∑ b ∈ range (2 * k + 1), coeff b (exp ℝ) * coeff (2 * k) (L ^ b)
      ≤ ∑ b ∈ range (2 * k + 1), coeff b (exp ℝ) * coeff (2 * k) ((a • G) ^ b) := by
        refine sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hmaj b _ le_rfl)) ?_
        rw [coeff_exp, map_div₀, map_one, map_natCast]
        positivity
    _ = ∑ d ∈ range k,
          a ^ (d + 1) * A ^ (2 * k - 2 * (d + 1)) * ((2 * k - d - 2).choose d : ℝ) / (d + 1) ! := by
        rw [sum_range_succ', pow_zero, coeff_one, ite_eq_right (by omega), mul_zero, add_zero,
          show 2 * k = k + k by omega, sum_range_add, show k + k = 2 * k by omega]
        have h2 : ∑ x ∈ range k, coeff (k + x + 1) (exp ℝ) *
            coeff (2 * k) ((a • G) ^ (k + x + 1)) = 0 := by
          refine sum_eq_zero fun x _ ↦ ?_
          rw [smul_pow, coeff_smul, hGdef, coeff_X_pow_mul_rescale_pow, ite_eq_right (by omega)]
          simp
        rw [h2, add_zero]
        refine sum_congr rfl fun d hd ↦ ?_
        have hd' := mem_range.mp hd
        rw [smul_pow, coeff_smul, hGdef, coeff_X_pow_mul_rescale_pow, ite_eq_left (by omega),
          coeff_exp, map_div₀, map_one, map_natCast, smul_eq_mul,
          show d + (2 * k - 2 * (d + 1)) = 2 * k - d - 2 by omega]
        ring

/-- The counting step of Lemma 6 of `hybrid-assembly.md`. For `k = d + 1 + i`,
`(2k)! C(d + 2i, d) (2i)! ≤ (2k)^k (4k³)^i (d + 1)!`, which is
`(k! / (k - i)!) C(k + i - 1, 2i) ≤ (4k³)^i / (2i)!` times `(2k)! / k! ≤ (2k)^k`. -/
theorem factorial_mul_choose_le {d i k : ℕ} (hk : k = d + 1 + i) :
    (2 * k) ! * (d + 2 * i).choose d * (2 * i) ! ≤ (2 * k) ^ k * (4 * k ^ 3) ^ i * (d + 1) ! := by
  have h1 : k ! * (2 * k).descFactorial k = (2 * k) ! := by
    have h := factorial_mul_descFactorial (show k ≤ 2 * k by omega)
    rwa [show 2 * k - k = k by omega] at h
  have h2 : (d + 1) ! * k.descFactorial i = k ! := by
    have h := factorial_mul_descFactorial (show i ≤ k by omega)
    rwa [show k - i = d + 1 by omega] at h
  have h3 : (d + 2 * i).choose d * (2 * i) ! = (d + 2 * i).descFactorial (2 * i) := by
    rw [choose_symm_add, descFactorial_eq_factorial_mul_choose, mul_comm]
  calc (2 * k) ! * (d + 2 * i).choose d * (2 * i) !
      = (d + 1) ! * k.descFactorial i * (2 * k).descFactorial k *
          (d + 2 * i).descFactorial (2 * i) := by
        rw [h2, h1, mul_assoc, h3]
    _ ≤ (d + 1) ! * k ^ i * (2 * k) ^ k * (2 * k) ^ (2 * i) := by
        gcongr
        · exact descFactorial_le_pow k i
        · exact descFactorial_le_pow (2 * k) k
        · exact (descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
    _ = (2 * k) ^ k * (4 * k ^ 3) ^ i * (d + 1) ! := by
        rw [pow_mul, mul_pow, mul_pow, mul_pow, mul_pow]
        ring

/-- The cosh step of Lemma 6 of `hybrid-assembly.md`. If `a > 0`, `A ≥ 0` and
`y² = 4k³ A² / a`, then
`(2k)! ∑_(1 ≤ b ≤ k) a^b A^(2k - 2b) C(2k - b - 1, b - 1) / b! ≤ (2ka)^k cosh y`. -/
theorem sum_le_cosh {a A y : ℝ} (ha : 0 < a) (hA : 0 ≤ A) {k : ℕ}
    (hy : y ^ 2 = 4 * k ^ 3 * A ^ 2 / a) :
    (2 * k) ! * ∑ d ∈ range k,
      a ^ (d + 1) * A ^ (2 * k - 2 * (d + 1)) * ((2 * k - d - 2).choose d : ℝ) / (d + 1) ! ≤
        (2 * k * a) ^ k * Real.cosh y := by
  rw [mul_sum, ← sum_range_reflect]
  calc ∑ i ∈ range k, (2 * k) ! * (a ^ (k - 1 - i + 1) * A ^ (2 * k - 2 * (k - 1 - i + 1)) *
        ((2 * k - (k - 1 - i) - 2).choose (k - 1 - i) : ℝ) / (k - 1 - i + 1) !)
      ≤ ∑ i ∈ range k, (2 * k * a) ^ k * (y ^ (2 * i) / (2 * i) !) := by
        refine sum_le_sum fun i hi ↦ ?_
        have hi' := mem_range.mp hi
        set d := k - 1 - i with hd
        have hk : k = d + 1 + i := by omega
        have hN := factorial_mul_choose_le hk
        rw [show 2 * k - 2 * (d + 1) = 2 * i by omega, show 2 * k - d - 2 = d + 2 * i by omega,
          pow_mul y, hy]
        have hW : 0 ≤ a ^ (d + 1) * A ^ (2 * i) / ((d + 1) ! * (2 * i) !) := by positivity
        have hfd : (0 : ℝ) < (d + 1) ! := by exact_mod_cast factorial_pos _
        have hfi : (0 : ℝ) < (2 * i) ! := by exact_mod_cast factorial_pos _
        have hak : a ^ k = a ^ (d + 1) * a ^ i := by rw [← pow_add, ← hk]
        have e1 : ((2 * k) ! : ℝ) * (a ^ (d + 1) * A ^ (2 * i) * ((d + 2 * i).choose d : ℝ) /
            (d + 1) !) = a ^ (d + 1) * A ^ (2 * i) / ((d + 1) ! * (2 * i) !) *
              (((2 * k) ! * (d + 2 * i).choose d * (2 * i) ! : ℕ) : ℝ) := by
          push_cast
          field_simp
        have e2 : (2 * k * a) ^ k * ((4 * k ^ 3 * A ^ 2 / a) ^ i / (2 * i) !) =
            a ^ (d + 1) * A ^ (2 * i) / ((d + 1) ! * (2 * i) !) *
              (((2 * k) ^ k * (4 * k ^ 3) ^ i * (d + 1) ! : ℕ) : ℝ) := by
          rw [mul_pow (2 * (k : ℝ)) a k, hak, div_pow, mul_pow (4 * (k : ℝ) ^ 3) (A ^ 2) i,
            ← pow_mul]
          push_cast
          field_simp
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hN) hW
    _ = (2 * k * a) ^ k * ∑ i ∈ range k, y ^ (2 * i) / (2 * i) ! := by rw [mul_sum]
    _ ≤ (2 * k * a) ^ k * Real.cosh y := by
        refine mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun n _ ↦ ?_) (Real.hasSum_cosh y))
          (by positivity)
        rw [pow_mul]
        positivity

/-- Lemma 6 of `hybrid-assembly.md` (cumulants to central moments), in the file's form. Let `X`
have law `p` on `[0, N]` and mean `μ > 0`. If `|κ_r| ≤ r! H' μ A'^(r - 2)` for `2 ≤ r ≤ 2k`, with
`H' > 0` and `A' ≥ 0`, then `E(X - μ)^(2k) ≤ (2k H' μ)^k cosh(2 A' k^(3/2) (H' μ)^(-1/2))`. -/
theorem centralMoment_le_cosh (hp : IsLaw p N) {H' A' : ℝ} (hH' : 0 < H') (hμ : 0 < partialMean p N)
    (hA' : 0 ≤ A') {k : ℕ} (hk : 1 ≤ k)
    (hκ : ∀ r, 2 ≤ r → r ≤ 2 * k → |cumulant p N r| ≤ r ! * H' * partialMean p N * A' ^ (r - 2)) :
    centralMoment p N (2 * k) ≤ (2 * k * H' * partialMean p N) ^ k *
      Real.cosh (2 * A' * k * Real.sqrt k / Real.sqrt (H' * partialMean p N)) := by
  have ha : 0 < H' * partialMean p N := mul_pos hH' hμ
  have h := centralMoment_le_sum hp ha.le hA' hk fun r hr hr' ↦ by
    rw [← mul_assoc]
    exact hκ r hr hr'
  refine h.trans ?_
  rw [mul_assoc (2 * (k : ℝ))]
  refine sum_le_cosh ha hA' ?_
  rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt ha.le]
  ring

/-- Proposition 8 of `hybrid-assembly.md`, the moment half, which is the inequality (H-JI*). Let
`X` have law `p` on `[0, N]` with mean `μ > 0`, and let `H ≥ 1` and `k ≥ 1` with `H μ ≥ 8k`. If
the factorial cumulants satisfy (H-JI),
`|κ^f_j| ≤ j! H μ (H μ / (8k))^((j - 2)/2)` for `2 ≤ j ≤ 2k`, then
`E(X - μ)^(2k) ≤ (4e H k μ)^k`. -/
theorem centralMoment_le_of_factCumulant (hp : IsLaw p N) {H : ℝ} {k : ℕ} (hH : 1 ≤ H)
    (hk : 1 ≤ k) (hμ : 0 < partialMean p N) (hHμ : 8 * k ≤ H * partialMean p N)
    (hκ : ∀ j, 2 ≤ j → j ≤ 2 * k → |factCumulant p N j| ≤
      j ! * H * partialMean p N * Real.sqrt (H * partialMean p N / (8 * k)) ^ (j - 2)) :
    centralMoment p N (2 * k) ≤ (4 * Real.exp 1 * H * k * partialMean p N) ^ k := by
  set μ := partialMean p N with hμdef
  set A := Real.sqrt (H * μ / (8 * k)) with hAdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hA1 : 1 ≤ A := Real.one_le_sqrt.mpr ((one_le_div (by positivity)).mpr hHμ)
  have hA2 : A ^ 2 = H * μ / (8 * k) := Real.sq_sqrt (by positivity)
  have h7 : ∀ r, 2 ≤ r → r ≤ 2 * k → |cumulant p N r| ≤ r ! * (2 * H) * μ * (2 * A) ^ (r - 2) :=
    fun r hr hr' ↦ abs_cumulant_le hp hH hA1 hr fun j hj hj' ↦ hκ j hj (hj'.trans hr')
  have ha : 0 < 2 * H * μ := by positivity
  have h6 := centralMoment_le_sum hp ha.le (A := 2 * A) (by positivity) hk fun r hr hr' ↦ by
    rw [← mul_assoc]
    exact h7 r hr hr'
  have hcosh := sum_le_cosh (y := k) ha (by positivity : (0 : ℝ) ≤ 2 * A) (k := k) (by
    rw [mul_pow, hA2]
    field_simp
    ring)
  have hce : Real.cosh k ≤ Real.exp k := by
    rw [Real.cosh_eq]
    linarith [Real.exp_le_exp.mpr (show -(k : ℝ) ≤ k by linarith)]
  calc centralMoment p N (2 * k) ≤ (2 * k * (2 * H * μ)) ^ k * Real.cosh k := h6.trans hcosh
    _ ≤ (2 * k * (2 * H * μ)) ^ k * Real.exp k :=
        mul_le_mul_of_nonneg_left hce (by positivity)
    _ = (4 * Real.exp 1 * H * k * μ) ^ k := by
        rw [← Real.exp_one_pow, ← mul_pow]
        ring

/-- Chebyshev at order `2k`: `P(X = 0) μ^(2k) ≤ E(X - μ)^(2k)`. -/
theorem prob_zero_mul_le_centralMoment (hp : IsLaw p N) (k : ℕ) :
    p 0 * partialMean p N ^ (2 * k) ≤ centralMoment p N (2 * k) := by
  have h := single_le_sum (f := fun j ↦ p j * ((j : ℝ) - partialMean p N) ^ (2 * k))
    (fun j _ ↦ mul_nonneg (hp.nonneg j) (by rw [pow_mul]; positivity))
    (mem_range.mpr (Nat.succ_pos N))
  simp only [cast_zero, zero_sub] at h
  rwa [pow_mul, neg_sq, ← pow_mul] at h

/-- Proposition 8 of `hybrid-assembly.md` ((H-JI) ⇒ Poisson-like moments ⇒ the lower tail). Let
`X` have law `p` on `[0, N]` with mean `μ > 0`, and let `H ≥ 1` and `k ≥ 1` with `H μ ≥ 8k`. If
`|κ^f_j| ≤ j! H μ (H μ / (8k))^((j - 2)/2)` for `2 ≤ j ≤ 2k`, then
`P(X = 0) ≤ (4e H k / μ)^k`. -/
theorem prob_zero_le_of_factCumulant (hp : IsLaw p N) {H : ℝ} {k : ℕ} (hH : 1 ≤ H)
    (hk : 1 ≤ k) (hμ : 0 < partialMean p N) (hHμ : 8 * k ≤ H * partialMean p N)
    (hκ : ∀ j, 2 ≤ j → j ≤ 2 * k → |factCumulant p N j| ≤
      j ! * H * partialMean p N * Real.sqrt (H * partialMean p N / (8 * k)) ^ (j - 2)) :
    p 0 ≤ (4 * Real.exp 1 * H * k / partialMean p N) ^ k := by
  have h := (prob_zero_mul_le_centralMoment hp k).trans
    (centralMoment_le_of_factCumulant hp hH hk hμ hHμ hκ)
  have hpos : 0 < partialMean p N ^ (2 * k) := by positivity
  rw [← le_div_iff₀ hpos] at h
  refine h.trans_eq ?_
  rw [div_pow, pow_mul, mul_pow (4 * Real.exp 1 * H * k), sq, mul_pow]
  field_simp
  ring

end Laws

end CumulantTail

end Pairing
