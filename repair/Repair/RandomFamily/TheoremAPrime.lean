import Mathlib.Analysis.Real.Pi.Bounds
import Repair.RandomFamily.TheoremA

/-!
# The corollary of Theorem A′: radius `⌊(√(πm) - 1 - 2 log m) / log(2m)⌋ - 2` (COD-281)

Source: `results/random-family-lb-contra.md` §1.6, Theorem A′ and its corollary (organize-archive
fc1a04f), checked in `results/random-family-lb-factcheck-contra.md`, section "Theorem A′, step by
step" (2f3e50f).

Families `M : ι → PerfectMatching (Vertex m)` with `|ι| = 2m - 1` carry the counting measure, the
law of `2m - 1` i.i.d. uniform perfect matchings. Put `μ = (2m - 1)p` and
`K_m = ⌊(√(πm) - 1 - 2 log m) / log(2m)⌋ - 3` in `ℤ`. The corollary says that with probability at
least `1 - m^(-3/2)` every six-vertex gadget `G` has `N(M, G) ≥ K_m + 1`. When `K_m < 0` there is
nothing to prove, so the statements take `K : ℕ` with `K ≤ K_m`.

* `RandomFamily.sqrt_pi_lt_log_two_mul` : `√π < log(2m)` for `m ≥ 3`, from `log 6 > 1.78`.
* `RandomFamily.kAPrime` : the integer `K_m`.
* `RandomFamily.add_three_mul_log_le_of_le_kAPrime` : `K ≤ K_m` gives
  `(K + 3) log(2m) ≤ √(πm) - 1 - 2 log m`.
* `RandomFamily.exp_neg_mul_pow_le_rpow` : then `μ ≥ √(πm) - 1` gives
  `e^(-μ)(K + 1)(2m)^(K+3) ≤ (K + 1) / m² ≤ m^(-3/2)`.
* `RandomFamily.corollaryAPrime_of_le`, `RandomFamily.corollaryAPrime` : at most a fraction
  `m^(-3/2)` of the families have `N(M, G) ≤ K` at some gadget, for every `K ≤ K_m`.
* `RandomFamily.corollaryAPrime_good` : at least a fraction `1 - m^(-3/2)` have `N(M, G) ≥ K + 1`
  at every gadget.
* `RandomFamily.corollaryAPrime_fin`, `RandomFamily.corollaryAPrime_fin_good` : the same for
  `M : Fin (2m - 1) → PerfectMatching (Vertex m)` at `K = K_m ≥ 0`.
-/

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching Real

/-- `√π < log 6`, since `6^7 > 2^18` gives `log 6 > (18/7) log 2 > 1.78` and `π < 3.15`
(`random-family-lb-factcheck-contra.md`, "Theorem A′, step by step", 2f3e50f). -/
theorem sqrt_pi_lt_log_six : √π < log 6 := by
  have h2 := log_two_gt_d9
  have h := log_lt_log (by norm_num) (show (2 : ℝ) ^ 18 < 6 ^ 7 by norm_num)
  rw [log_pow, log_pow] at h
  push_cast at h
  have h6 : (1.78 : ℝ) < log 6 := by linarith
  rw [sqrt_lt' (by linarith)]
  nlinarith [pi_lt_d2]

/-- `√π < log(2m)` for `m ≥ 3` (`random-family-lb-factcheck-contra.md`, "Theorem A′, step by
step", 2f3e50f). -/
theorem sqrt_pi_lt_log_two_mul {m : ℕ} (hm : 3 ≤ m) : √π < log (2 * m) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  exact sqrt_pi_lt_log_six.trans_le (log_le_log (by norm_num) (by linarith))

/-- `K_m = ⌊(√(πm) - 1 - 2 log m) / log(2m)⌋ - 3`, the radius of the corollary of Theorem A′
(`random-family-lb-contra.md` §1.6, fc1a04f). -/
noncomputable def kAPrime (m : ℕ) : ℤ :=
  ⌊(√(π * m) - 1 - 2 * log m) / log (2 * m)⌋ - 3

/-- If `K ≤ K_m` and `m ≥ 3`, then `(K + 3) log(2m) ≤ √(πm) - 1 - 2 log m`
(`random-family-lb-factcheck-contra.md`, "Theorem A′, step by step", 2f3e50f). -/
theorem add_three_mul_log_le_of_le_kAPrime {m : ℕ} (hm : 3 ≤ m) {K : ℕ}
    (hK : (K : ℤ) ≤ kAPrime m) :
    (K + 3) * log (2 * m) ≤ √(π * m) - 1 - 2 * log m := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < log (2 * (m : ℝ)) := log_pos (by linarith)
  have h : (K : ℤ) + 3 ≤ ⌊(√(π * m) - 1 - 2 * log m) / log (2 * m)⌋ := by
    unfold kAPrime at hK
    omega
  rw [Int.le_floor] at h
  push_cast at h
  rwa [le_div_iff₀ hlog] at h

/-- The arithmetic of the corollary of Theorem A′ (`random-family-lb-contra.md` §1.6, fc1a04f;
`random-family-lb-factcheck-contra.md`, "Theorem A′, step by step", 2f3e50f). For `m ≥ 3`,
`μ ≥ √(πm) - 1` and `(K + 3) log(2m) ≤ √(πm) - 1 - 2 log m`, the bound
`e^(-μ)(K + 1)(2m)^(K+3)` of Theorem A′ is at most `(K + 1) / m² ≤ m^(-3/2)`, since
`K + 1 ≤ √m` by `log(2m) > √π`. -/
theorem exp_neg_mul_pow_le_rpow {m : ℕ} (hm : 3 ≤ m) {μ : ℝ} (hμ : √(π * m) - 1 ≤ μ) {K : ℕ}
    (hK : (K + 3) * log (2 * m) ≤ √(π * m) - 1 - 2 * log m) :
    exp (-μ) * (K + 1) * (2 * m) ^ (K + 3) ≤ (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog : 0 < log (2 * (m : ℝ)) := log_pos (by linarith)
  have hlogm : 0 ≤ log (m : ℝ) := log_nonneg (by linarith)
  have hsq : 0 < √(m : ℝ) := sqrt_pos.mpr hm0
  have hK1 : (K + 1 : ℝ) ≤ √m := by
    have h1 : √(π * m) < √m * log (2 * m) := by
      rw [sqrt_mul pi_pos.le, mul_comm]
      exact mul_lt_mul_of_pos_left (sqrt_pi_lt_log_two_mul hm) hsq
    have h2 : ((K : ℝ) + 3) * log (2 * m) < √m * log (2 * m) := by linarith
    have h3 := lt_of_mul_lt_mul_right h2 hlog.le
    linarith
  have hpow : (2 * m : ℝ) ^ (K + 3) = exp ((K + 3) * log (2 * m)) := by
    rw [show ((K : ℝ) + 3) = ((K + 3 : ℕ) : ℝ) by push_cast; ring, exp_nat_mul,
      exp_log (by positivity)]
  have hsqrt : √(m : ℝ) = exp (log m * (1 / 2)) := by rw [sqrt_eq_rpow, rpow_def_of_pos hm0]
  rw [rpow_def_of_pos hm0, hpow]
  calc exp (-μ) * (K + 1) * exp ((K + 3) * log (2 * m))
      = (K + 1) * exp (-μ + (K + 3) * log (2 * m)) := by rw [exp_add]; ring
    _ ≤ √m * exp (-(2 * log m)) :=
        mul_le_mul hK1 (exp_le_exp.mpr (by linarith)) (exp_pos _).le hsq.le
    _ = exp (log m * -(3 / 2)) := by
        rw [hsqrt, ← exp_add]
        ring_nf

variable {m : ℕ} [NeZero m]

/-- **Corollary of Theorem A′**, real form (`random-family-lb-contra.md` §1.6, fc1a04f; checked in
`random-family-lb-factcheck-contra.md`, "Theorem A′, step by step", 2f3e50f), at
`n = |ι| = 2m - 1`. For `m ≥ 3` and `K` with `(K + 3) log(2m) ≤ √(πm) - 1 - 2 log m`, at most a
fraction `m^(-3/2)` of the families `M : ι → PerfectMatching (Vertex m)` have `N(M, G) ≤ K` at
some six-vertex gadget `G`. The proof is `card_badFamilies_le_exp` with
`μ ≥ √(πm) - √π / (2√m) ≥ √(πm) - 1` and `exp_neg_mul_pow_le_rpow`. -/
theorem corollaryAPrime_of_le (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {K : ℕ}
    (hK : (K + 3) * log (2 * m) ≤ √(π * m) - 1 - 2 * log m) :
    ((badFamilies ι m K).card : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : (Fintype.card ι : ℝ) = 2 * m - 1 := by
    rw [hι, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hμ : √(π * m) - 1 ≤ (2 * m - 1 : ℝ) * pHam m := by
    have h1 : √π ≤ 2 := (sqrt_le_left (by norm_num)).mpr (by have := pi_le_four; linarith)
    have h2 : 1 ≤ √(m : ℝ) := by
      rw [le_sqrt zero_le_one (Nat.cast_nonneg _), one_pow]
      linarith
    have h3 : √π / (2 * √m) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith [(sub_le_mul_pHam (m := m)).1]
  have h := card_badFamilies_le_exp hm ι K
  rw [hn] at h
  exact h.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_pow_le_rpow hm hμ hK) (Nat.cast_nonneg _))

/-- **Corollary of Theorem A′** (`random-family-lb-contra.md` §1.6, fc1a04f; checked in
`random-family-lb-factcheck-contra.md`, "Theorem A′, step by step", 2f3e50f), at
`n = |ι| = 2m - 1`. For `m ≥ 3` and every `K : ℕ` with `K ≤ K_m`, at most a fraction `m^(-3/2)`
of the families `M : ι → PerfectMatching (Vertex m)` have `N(M, G) ≤ K` at some six-vertex
gadget `G`. -/
theorem corollaryAPrime (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {K : ℕ} (hK : (K : ℤ) ≤ kAPrime m) :
    ((badFamilies ι m K).card : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
  corollaryAPrime_of_le hm ι hι (add_three_mul_log_le_of_le_kAPrime hm hK)

open Classical in
/-- **Corollary of Theorem A′**, probability form (`random-family-lb-contra.md` §1.6, fc1a04f).
For `m ≥ 3`, `|ι| = 2m - 1` and `K ≤ K_m`, at least a fraction `1 - m^(-3/2)` of the families
`M : ι → PerfectMatching (Vertex m)` have `N(M, G) ≥ K + 1`, that is `¬ N(M, G) ≤ K`, at every
six-vertex gadget `G` at once. -/
theorem corollaryAPrime_good (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {K : ℕ} (hK : (K : ℤ) ≤ kAPrime m) :
    (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * (1 - (m : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ((Finset.univ.filter fun M : ι → PerfectMatching (Vertex m) ↦
        ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K).card : ℝ) := by
  have e : (Finset.univ.filter fun M : ι → PerfectMatching (Vertex m) ↦
      ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K) =
        Finset.univ \ badFamilies ι m K := by
    ext M
    simp [mem_badFamilies]
  rw [e, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ _)]
  linarith [corollaryAPrime hm ι hι hK]

/-- **Corollary of Theorem A′** at `K = K_m` (`random-family-lb-contra.md` §1.6, fc1a04f), for
the families `M : Fin (2m - 1) → PerfectMatching (Vertex m)`. If `m ≥ 3` and `K_m ≥ 0`, at most
a fraction `m^(-3/2)` of them have `N(M, G) ≤ K_m` at some six-vertex gadget `G`. -/
theorem corollaryAPrime_fin (hm : 3 ≤ m) (h0 : 0 ≤ kAPrime m) :
    ((badFamilies (Fin (2 * m - 1)) m (kAPrime m).toNat).card : ℝ) ≤
      (Fintype.card (Fin (2 * m - 1) → PerfectMatching (Vertex m)) : ℝ) *
        (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
  corollaryAPrime hm _ (Fintype.card_fin _) (Int.toNat_of_nonneg h0).le

open Classical in
/-- **Corollary of Theorem A′** at `K = K_m`, probability form (`random-family-lb-contra.md` §1.6,
fc1a04f). If `m ≥ 3` and `K_m ≥ 0`, at least a fraction `1 - m^(-3/2)` of the families
`M : Fin (2m - 1) → PerfectMatching (Vertex m)` have `N(M, G) ≥ K_m + 1` at every six-vertex
gadget `G`. -/
theorem corollaryAPrime_fin_good (hm : 3 ≤ m) (h0 : 0 ≤ kAPrime m) :
    (Fintype.card (Fin (2 * m - 1) → PerfectMatching (Vertex m)) : ℝ) *
        (1 - (m : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ((Finset.univ.filter fun M : Fin (2 * m - 1) → PerfectMatching (Vertex m) ↦
        ∀ G : Finset (Vertex m), G.card = 6 →
          ¬RepairBoundFor (zeroStates M) G (kAPrime m).toNat).card : ℝ) :=
  corollaryAPrime_good hm _ (Fintype.card_fin _) (Int.toNat_of_nonneg h0).le

end RoundRobin.Canonical.RandomFamily

end Pairing
