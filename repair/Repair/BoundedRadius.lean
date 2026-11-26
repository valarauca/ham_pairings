import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Repair.DensityGlue
import Suppression.Density

/-!
# Fixed-depth bottom ratios refute a bounded repair radius (COD-146)

This file formalizes Proposition 1 and Corollary 3 of the bounded-radius spike
(`results/bounded-radius-spike.md`). Notation is that of the spike and of `SizeBias.lean`: for a
law `p` on `[0, N]`, `F(j) = cdf p j`, `G(j) = partialMean p j = ∑_{k ≤ j} k p k` and
`μ = G(N)`. The bottom ratio is `ρ_j = G(j + 1) / (μ F(j))`, so that `μ ρ_j F(j) = G(j + 1)`
whenever `μ F(j) ≠ 0`. For the round-robin count `X = hamCount m` its law is `hamLaw m`,
`q_m = P(X = 0) = hamLaw m 0` and `ρ_j(m) = hamBottomRatio m j`.

* `SizeBias.bottomRatio p N j = ρ_j`, and `SizeBias.IsLaw.mul_bottomRatio_mul_cdf` :
  `μ ρ_j F(j) = G(j + 1)` when `μ F(j) ≠ 0`.
* `SizeBias.IsLaw.cdf_zero_mul_pow_mul_prod_le` (Proposition 1, iterated inequality) :
  `F(0) μ^J ∏_{j < J} ρ_j ≤ J! F(J)` for every law and every `J`.
  `SizeBias.IsLaw.cdf_zero_le_div` is the division form
  `F(0) ≤ J! F(J) / (μ^J ∏_{j < J} ρ_j)` when `μ > 0` and every `ρ_j > 0`.
* `RoundRobin.Canonical.partialMean_hamLaw_eq` : the mean of `hamLaw m` is
  `μ_m = ∑_t U(A_t)`.
* `RoundRobin.Canonical.hamLaw_zero_mul_pow_mul_prod_le` : `q_m μ_m^J ∏_{j < J} ρ_j(m) ≤ J!`.
* `RoundRobin.Canonical.hamLaw_zero_le_of_le_hamBottomRatio` (Proposition 1, the displayed
  bound) : if `ρ_j(m) ≥ m^(-θ)` for every `j < J`, then
  `q_m ≤ J! (2 / √π)^J m^(-(1/2 - θ) J)`.
* `RoundRobin.Canonical.not_repairBound_of_le_hamBottomRatio` (Proposition 1) : if `θ < 1/2` and
  for every `J` there are infinitely many `m` with `ρ_j(m) ≥ m^(-θ)` for all `j < J`, then for
  every `K` there are infinitely many `m` at which `RepairBound m G K` fails for every six-vertex
  gadget `G`. `RoundRobin.Canonical.not_boundedRadius_of_le_hamBottomRatio` is the negation of
  (BK).
* `RoundRobin.Canonical.prod_hamBottomRatio_le` (Corollary 3, product form) : if
  `RepairBound m G K` holds for a six-vertex gadget, then
  `∏_{j < 2K + 7} ρ_j(m) ≤ (2K + 7)! (K + 1) 2^(K + 3) (2 / √π)^(2K + 7) / √m`.
* `RoundRobin.Canonical.exists_hamBottomRatio_le` (Corollary 3) : there is `C_K > 0` such that
  `RepairBound m G K` forces `min_{j < 2K + 7} ρ_j(m) ≤ C_K m^(-1/(4K + 14))`, at every `m`.

The spike assumes `0 ≤ θ`. The proof here does not use it.
-/

namespace Pairing

namespace SizeBias

open Finset

variable {p : ℕ → ℝ} {N : ℕ}

/-- The bottom ratio `ρ_j = G(j + 1) / (μ F(j))` of `results/bounded-radius-spike.md` (frontier
R1), with `G(j) = ∑_{k ≤ j} k p k`, `μ = G(N)` and `F(j) = ∑_{k ≤ j} p k`. -/
noncomputable def bottomRatio (p : ℕ → ℝ) (N j : ℕ) : ℝ :=
  partialMean p (j + 1) / (partialMean p N * cdf p j)

/-- `ρ_j ≥ 0` (`results/bounded-radius-spike.md`, Proposition 1). -/
theorem IsLaw.bottomRatio_nonneg (hp : IsLaw p N) (j : ℕ) : 0 ≤ bottomRatio p N j :=
  div_nonneg (hp.partialMean_nonneg _) (mul_nonneg (hp.partialMean_nonneg _) (hp.cdf_nonneg _))

/-- The defining identity of the bottom ratio (`results/bounded-radius-spike.md`, Proposition 1):
`μ ρ_j F(j) = ∑_{k ≤ j + 1} k P(X = k)` when `μ F(j) ≠ 0`. -/
theorem mul_bottomRatio_mul_cdf {j : ℕ} (h : partialMean p N * cdf p j ≠ 0) :
    partialMean p N * bottomRatio p N j * cdf p j = partialMean p (j + 1) := by
  rw [show partialMean p N * bottomRatio p N j * cdf p j =
    bottomRatio p N j * (partialMean p N * cdf p j) by ring, bottomRatio, div_mul_cancel₀ _ h]

/-- `μ ρ_j F(j) ≤ G(j + 1)` for every `j` (`results/bounded-radius-spike.md`, Proposition 1).
It is an equality unless `μ F(j) = 0`, where `ρ_j = 0`. -/
theorem IsLaw.mul_bottomRatio_mul_cdf_le (hp : IsLaw p N) (j : ℕ) :
    partialMean p N * bottomRatio p N j * cdf p j ≤ partialMean p (j + 1) := by
  rcases eq_or_ne (partialMean p N * cdf p j) 0 with h | h
  · rw [bottomRatio, h, div_zero, mul_zero, zero_mul]
    exact hp.partialMean_nonneg _
  · exact (mul_bottomRatio_mul_cdf h).le

/-- `G(j) ≤ j F(j)` (`results/bounded-radius-spike.md`, proof of Proposition 1). -/
theorem IsLaw.partialMean_le_mul_cdf (hp : IsLaw p N) (j : ℕ) :
    partialMean p j ≤ j * cdf p j := by
  rw [partialMean, cdf, mul_sum]
  exact sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)) (hp.nonneg k)

/-- The iterated inequality of Proposition 1 (`results/bounded-radius-spike.md`) in multiplied
form: `F(0) μ^J ∏_{j < J} ρ_j ≤ J! F(J)` for every law on `[0, N]` and every `J`. Each step is
`μ ρ_j F(j) = G(j + 1) ≤ (j + 1) F(j + 1)`. -/
theorem IsLaw.cdf_zero_mul_pow_mul_prod_le (hp : IsLaw p N) (J : ℕ) :
    cdf p 0 * partialMean p N ^ J * ∏ j ∈ range J, bottomRatio p N j ≤
      J.factorial * cdf p J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hμ := hp.partialMean_nonneg N
    have hρ := hp.bottomRatio_nonneg J
    calc cdf p 0 * partialMean p N ^ (J + 1) * ∏ j ∈ range (J + 1), bottomRatio p N j
        = (cdf p 0 * partialMean p N ^ J * ∏ j ∈ range J, bottomRatio p N j) *
            (partialMean p N * bottomRatio p N J) := by
          rw [prod_range_succ, pow_succ]
          ring
      _ ≤ (J.factorial * cdf p J) * (partialMean p N * bottomRatio p N J) :=
          mul_le_mul_of_nonneg_right ih (mul_nonneg hμ hρ)
      _ = J.factorial * (partialMean p N * bottomRatio p N J * cdf p J) := by ring
      _ ≤ J.factorial * partialMean p (J + 1) :=
          mul_le_mul_of_nonneg_left (hp.mul_bottomRatio_mul_cdf_le J) (by positivity)
      _ ≤ J.factorial * (((J + 1 : ℕ) : ℝ) * cdf p (J + 1)) :=
          mul_le_mul_of_nonneg_left (hp.partialMean_le_mul_cdf (J + 1)) (by positivity)
      _ = (J + 1).factorial * cdf p (J + 1) := by
          push_cast [Nat.factorial_succ]
          ring

/-- The iterated inequality of Proposition 1 (`results/bounded-radius-spike.md`) as displayed:
`q = F(0) ≤ J! F(J) / (μ^J ∏_{j < J} ρ_j)` when `μ > 0` and every `ρ_j > 0`. -/
theorem IsLaw.cdf_zero_le_div (hp : IsLaw p N) (J : ℕ) (hμ : 0 < partialMean p N)
    (hρ : ∀ j < J, 0 < bottomRatio p N j) :
    cdf p 0 ≤ J.factorial * cdf p J / (partialMean p N ^ J * ∏ j ∈ range J, bottomRatio p N j) := by
  have hprod : 0 < ∏ j ∈ range J, bottomRatio p N j :=
    prod_pos fun j hj ↦ hρ j (mem_range.mp hj)
  rw [le_div_iff₀ (mul_pos (pow_pos hμ J) hprod), ← mul_assoc]
  exact hp.cdf_zero_mul_pow_mul_prod_le J

end SizeBias

namespace RoundRobin.Canonical

open Finset ChainRule PerfectMatching Real

/-- The bottom ratio `ρ_j(m) = (∑_{k ≤ j + 1} k P(X = k)) / (μ_m P(X ≤ j))` of the round-robin
count `X = hamCount m` (`results/bounded-radius-spike.md`, frontier R1). By `cond_hamLaw` it is
`P(X - 1 ≤ j | A_0) / P(X ≤ j)`. -/
noncomputable def hamBottomRatio (m : ℕ) [NeZero m] (j : ℕ) : ℝ :=
  SizeBias.bottomRatio (hamLaw m) (2 * m - 1) j

/-- The mean of `hamLaw m` is `μ_m = ∑_t U(A_t)` (`results/bounded-radius-spike.md`,
Proposition 1, which uses `μ_m ≥ (√π / 2) √m`). -/
theorem partialMean_hamLaw_eq (m : ℕ) [NeZero m] :
    SizeBias.partialMean (hamLaw m) (2 * m - 1) = ∑ t, prob (unifWeight m) (hamEvent m t) := by
  classical
  have hm := NeZero.pos m
  rw [partialMean_hamLaw, sum_prob_hamEvent, prob_unifWeight m (hamEvent m 0), mul_div_assoc]
  congr 1
  · rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · congr 3
    ext P
    simp only [mem_filter, mem_univ, true_and, hamCount_le m P, and_true]
    exact Iff.rfl

/-- `μ_m ≥ (√π / 2) √m` for the mean of `hamLaw m` (`results/bounded-radius-spike.md`,
Proposition 1). -/
theorem sqrt_mul_sqrt_le_partialMean_hamLaw (m : ℕ) [NeZero m] :
    Real.sqrt π / 2 * Real.sqrt m ≤ SizeBias.partialMean (hamLaw m) (2 * m - 1) := by
  rw [partialMean_hamLaw_eq]
  exact (sqrt_mul_sqrt_le_sum_prob_hamEvent m).1

/-- `(√π / 2) √m > 0` (`results/bounded-radius-spike.md`, Proposition 1). -/
theorem sqrt_mul_sqrt_pos (m : ℕ) [NeZero m] : 0 < Real.sqrt π / 2 * Real.sqrt m :=
  mul_pos (div_pos (sqrt_pos.mpr pi_pos) two_pos)
    (sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos m)))

/-- The iterated inequality of Proposition 1 (`results/bounded-radius-spike.md`) for the
round-robin law: `q_m μ_m^J ∏_{j < J} ρ_j(m) ≤ J!`. -/
theorem hamLaw_zero_mul_pow_mul_prod_le (m : ℕ) [NeZero m] (J : ℕ) :
    hamLaw m 0 * SizeBias.partialMean (hamLaw m) (2 * m - 1) ^ J *
        ∏ j ∈ range J, hamBottomRatio m j ≤ J.factorial := by
  have hp := isLaw_hamLaw m
  have h := hp.cdf_zero_mul_pow_mul_prod_le J
  rw [show SizeBias.cdf (hamLaw m) 0 = hamLaw m 0 by simp [SizeBias.cdf]] at h
  exact h.trans (mul_le_of_le_one_right (by positivity) (hp.cdf_le_one J))

/-- The displayed bound of Proposition 1 (`results/bounded-radius-spike.md`): if
`ρ_j(m) ≥ m^(-θ)` for every `j < J`, then `q_m ≤ J! (2 / √π)^J m^(-(1/2 - θ) J)`. -/
theorem hamLaw_zero_le_of_le_hamBottomRatio {m : ℕ} [NeZero m] {θ : ℝ} {J : ℕ}
    (h : ∀ j < J, (m : ℝ) ^ (-θ) ≤ hamBottomRatio m j) :
    hamLaw m 0 ≤ J.factorial * (2 / Real.sqrt π) ^ J * (m : ℝ) ^ (-((1 / 2 - θ) * J)) := by
  have hs : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hpi : 0 < Real.sqrt π := sqrt_pos.mpr pi_pos
  have hq : 0 ≤ hamLaw m 0 := (isLaw_hamLaw m).nonneg 0
  have hμ := sqrt_mul_sqrt_le_partialMean_hamLaw m
  have ha := sqrt_mul_sqrt_pos m
  have hprod : ((m : ℝ) ^ (-θ)) ^ J ≤ ∏ j ∈ range J, hamBottomRatio m j := by
    rw [show ((m : ℝ) ^ (-θ)) ^ J = ∏ _j ∈ range J, (m : ℝ) ^ (-θ) by rw [prod_const, card_range]]
    exact prod_le_prod₀ (fun _ _ ↦ (rpow_pos_of_pos hs _).le) fun j hj ↦ h j (mem_range.mp hj)
  have hpow : (Real.sqrt π / 2 * Real.sqrt m) ^ J ≤
      SizeBias.partialMean (hamLaw m) (2 * m - 1) ^ J :=
    pow_le_pow_left₀ ha.le hμ J
  have key : hamLaw m 0 * ((Real.sqrt π / 2 * Real.sqrt m) ^ J * ((m : ℝ) ^ (-θ)) ^ J) ≤
      J.factorial := by
    refine le_trans ?_ (hamLaw_zero_mul_pow_mul_prod_le m J)
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hq) hprod
      (pow_nonneg (rpow_pos_of_pos hs _).le J) (mul_nonneg hq (pow_nonneg (ha.le.trans hμ) J))
  have e : (Real.sqrt π / 2 * Real.sqrt m) ^ J * ((m : ℝ) ^ (-θ)) ^ J =
      (Real.sqrt π / 2) ^ J * (m : ℝ) ^ ((1 / 2 - θ) * J) := by
    rw [← mul_pow, mul_assoc, sqrt_eq_rpow (m : ℝ), ← rpow_add hs, mul_pow, ← rpow_natCast
      ((m : ℝ) ^ (1 / 2 + -θ)), ← rpow_mul hs.le]
    ring_nf
  rw [e] at key
  have hD : 0 < (Real.sqrt π / 2) ^ J * (m : ℝ) ^ ((1 / 2 - θ) * J) :=
    mul_pos (pow_pos (div_pos hpi two_pos) J) (rpow_pos_of_pos hs _)
  rw [← le_div_iff₀ hD] at key
  refine key.trans (le_of_eq ?_)
  rw [rpow_neg hs.le, div_pow, div_pow]
  field_simp

/-- `(2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K ≤ (K + 1) 2^(K + 3) m^(K + 3)` for `m ≥ 3`, the
second inequality of C1 (`results/bounded-radius-spike.md` §1.1), used in Proposition 1. -/
theorem density_denom_le {m : ℕ} (hm : 3 ≤ m) (K : ℕ) :
    (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K ≤
      ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) : ℝ) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) ≤ 2 * m - 5 := by linarith
  have h3 : (2 * m - 1 : ℝ) * (2 * m - 3) * (2 * m - 5) ≤ (2 * m) ^ 3 := by
    have ha : (2 * m - 1 : ℝ) * (2 * m - 3) ≤ (2 * m) * (2 * m) := by nlinarith
    calc (2 * m - 1 : ℝ) * (2 * m - 3) * (2 * m - 5) ≤ (2 * m) * (2 * m) * (2 * m) :=
          mul_le_mul ha (by linarith) h1 (by positivity)
      _ = (2 * m) ^ 3 := by ring
  calc (2 * m - 1 : ℝ) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K
      = (2 * m - 1 : ℝ) * (2 * m - 3) * (2 * m - 5) * ((K + 1) * (2 * m) ^ K) := by ring
    _ ≤ (2 * m) ^ 3 * ((K + 1) * (2 * m) ^ K) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) := by ring

/-- C1 in closed form (`results/bounded-radius-spike.md` §1.1, from `density_ge`), the floor
that Proposition 1 and Corollary 3 contradict: if
`RepairBound m G K` holds for a six-vertex gadget `G`, then
`1 ≤ q_m (K + 1) 2^(K + 3) m^(K + 3)`. -/
theorem one_le_hamLaw_zero_mul {m : ℕ} [NeZero m] {G : Finset (Vertex m)} (hG : G.card = 6)
    {K : ℕ} (hK : RepairBound m G K) :
    1 ≤ hamLaw m 0 * ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  have hd := density_ge hG hK
  rw [← hamLaw_zero] at hd
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast h3
  have hpos : (0 : ℝ) < (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K := by
    have : (0 : ℝ) < 2 * m - 5 := by linarith
    have : (0 : ℝ) < 2 * m - 3 := by linarith
    have : (0 : ℝ) < 2 * m - 1 := by linarith
    positivity
  rw [div_le_iff₀ hpos] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left (density_denom_le h3 K) ((isLaw_hamLaw m).nonneg 0))

/-- Proposition 1 of `results/bounded-radius-spike.md` (fixed-depth bottom ratios refute bounded
radius). Let `θ < 1/2`. Suppose that for every depth `J` and every `M` there is `m ≥ M` with
`ρ_j(m) ≥ m^(-θ)` for all `j < J`. Then for every `K` and every `M` there is `m ≥ M` at which
`RepairBound m G K` fails for every six-vertex gadget `G`, so `N_m` is unbounded. The spike also
assumes `0 ≤ θ`, which is not needed. -/
theorem not_repairBound_of_le_hamBottomRatio {θ : ℝ} (hθ : θ < 1 / 2)
    (h : ∀ J M : ℕ, ∃ (m : ℕ) (_ : NeZero m), M ≤ m ∧
      ∀ j < J, (m : ℝ) ^ (-θ) ≤ hamBottomRatio m j)
    (K M : ℕ) :
    ∃ (m : ℕ) (_ : NeZero m), M ≤ m ∧
      ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBound m G K := by
  have hb : 0 < 1 / 2 - θ := by linarith
  obtain ⟨J, hJ⟩ := exists_nat_gt ((K + 3) / (1 / 2 - θ))
  have hJ' : (K + 3 : ℝ) < (1 / 2 - θ) * J := by
    rwa [div_lt_iff₀ hb, mul_comm] at hJ
  set a : ℝ := (1 / 2 - θ) * J - (K + 3) with ha_def
  have ha : 0 < a := by linarith
  set C : ℝ := J.factorial * (2 / Real.sqrt π) ^ J * ((K + 1) * 2 ^ (K + 3)) with hC_def
  have hlim : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ a) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨M', hM'⟩ := Filter.eventually_atTop.mp (hlim.eventually_gt_atTop C)
  obtain ⟨m, _, hmM, hρ⟩ := h J (max M M')
  refine ⟨m, inferInstance, le_of_max_le_left hmM, fun G hG hK ↦ ?_⟩
  have hs : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hlow := one_le_hamLaw_zero_mul hG hK
  have hup := hamLaw_zero_le_of_le_hamBottomRatio hρ
  have hgt := hM' m (le_of_max_le_right hmM)
  have hD : (0 : ℝ) ≤ (K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) := by positivity
  have h1 : 1 ≤ J.factorial * (2 / Real.sqrt π) ^ J * (m : ℝ) ^ (-((1 / 2 - θ) * J)) *
      ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) :=
    hlow.trans (mul_le_mul_of_nonneg_right hup hD)
  have e : J.factorial * (2 / Real.sqrt π) ^ J * (m : ℝ) ^ (-((1 / 2 - θ) * J)) *
      ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) = C / (m : ℝ) ^ a := by
    rw [ha_def, rpow_sub hs, rpow_neg hs.le, ← rpow_natCast (m : ℝ) (K + 3), hC_def]
    push_cast
    field_simp
  rw [e, le_div_iff₀ (rpow_pos_of_pos hs a), one_mul] at h1
  linarith

/-- Proposition 1 of `results/bounded-radius-spike.md` as the negation of (BK). Under the
hypothesis of `not_repairBound_of_le_hamBottomRatio` there are no `K` and `m₀` such that every
`m ≥ m₀` has a six-vertex gadget `G` with `RepairBound m G K`. -/
theorem not_boundedRadius_of_le_hamBottomRatio {θ : ℝ} (hθ : θ < 1 / 2)
    (h : ∀ J M : ℕ, ∃ (m : ℕ) (_ : NeZero m), M ≤ m ∧
      ∀ j < J, (m : ℝ) ^ (-θ) ≤ hamBottomRatio m j) :
    ¬∃ K m₀ : ℕ, ∀ (m : ℕ) [NeZero m], m₀ ≤ m →
      ∃ G : Finset (Vertex m), G.card = 6 ∧ RepairBound m G K := by
  rintro ⟨K, m₀, hBK⟩
  obtain ⟨m, _, hm, hno⟩ := not_repairBound_of_le_hamBottomRatio hθ h K m₀
  obtain ⟨G, hG, hK⟩ := hBK m hm
  exact hno G hG hK

/-- Corollary 3 of `results/bounded-radius-spike.md`, product form. If `RepairBound m G K` holds
for a six-vertex gadget `G`, then
`∏_{j < 2K + 7} ρ_j(m) ≤ (2K + 7)! (K + 1) 2^(K + 3) (2 / √π)^(2K + 7) / √m`. -/
theorem prod_hamBottomRatio_le {m : ℕ} [NeZero m] {G : Finset (Vertex m)} (hG : G.card = 6)
    {K : ℕ} (hK : RepairBound m G K) :
    ∏ j ∈ range (2 * K + 7), hamBottomRatio m j ≤
      (2 * K + 7).factorial * ((K + 1) * 2 ^ (K + 3)) * (2 / Real.sqrt π) ^ (2 * K + 7) /
        Real.sqrt m := by
  set J := 2 * K + 7 with hJ
  have hs : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hsq : 0 < Real.sqrt m := sqrt_pos.mpr hs
  have hpi : 0 < Real.sqrt π := sqrt_pos.mpr pi_pos
  have hq : 0 ≤ hamLaw m 0 := (isLaw_hamLaw m).nonneg 0
  have hμ := sqrt_mul_sqrt_le_partialMean_hamLaw m
  have ha := sqrt_mul_sqrt_pos m
  have hprod : 0 ≤ ∏ j ∈ range J, hamBottomRatio m j :=
    prod_nonneg fun j _ ↦ (isLaw_hamLaw m).bottomRatio_nonneg j
  have hlow := one_le_hamLaw_zero_mul hG hK
  have hit := hamLaw_zero_mul_pow_mul_prod_le m J
  have hpow : (Real.sqrt π / 2 * Real.sqrt m) ^ J ≤
      SizeBias.partialMean (hamLaw m) (2 * m - 1) ^ J :=
    pow_le_pow_left₀ ha.le hμ J
  have h2 : hamLaw m 0 * (Real.sqrt π / 2 * Real.sqrt m) ^ J *
      ∏ j ∈ range J, hamBottomRatio m j ≤ J.factorial :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hq) hprod) hit
  have hD : (0 : ℝ) ≤ (K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) := by positivity
  have h3 : (Real.sqrt π / 2 * Real.sqrt m) ^ J * ∏ j ∈ range J, hamBottomRatio m j ≤
      J.factorial * ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) := by
    calc (Real.sqrt π / 2 * Real.sqrt m) ^ J * ∏ j ∈ range J, hamBottomRatio m j
        ≤ (hamLaw m 0 * ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3))) *
            ((Real.sqrt π / 2 * Real.sqrt m) ^ J * ∏ j ∈ range J, hamBottomRatio m j) :=
          le_mul_of_one_le_left (mul_nonneg (pow_nonneg ha.le J) hprod) hlow
      _ = (hamLaw m 0 * (Real.sqrt π / 2 * Real.sqrt m) ^ J *
            ∏ j ∈ range J, hamBottomRatio m j) * ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) := by
          ring
      _ ≤ J.factorial * ((K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3)) :=
          mul_le_mul_of_nonneg_right h2 hD
  have hsJ : Real.sqrt m ^ J = (m : ℝ) ^ (K + 3) * Real.sqrt m := by
    rw [hJ, show 2 * K + 7 = 2 * (K + 3) + 1 by ring, pow_succ, pow_mul, sq_sqrt hs.le]
  rw [mul_pow, hsJ] at h3
  have hc : 0 < (Real.sqrt π / 2) ^ J * ((m : ℝ) ^ (K + 3) * Real.sqrt m) :=
    mul_pos (pow_pos (div_pos hpi two_pos) J) (mul_pos (pow_pos hs _) hsq)
  rw [mul_comm, ← le_div_iff₀ hc] at h3
  refine h3.trans (le_of_eq ?_)
  simp only [div_pow]
  field_simp

/-- Corollary 3 of `results/bounded-radius-spike.md`. For every `K` there is `C_K > 0` such that,
at every `m` where `RepairBound m G K` holds for some six-vertex gadget `G`, some `j < 2K + 7`
has `ρ_j(m) ≤ C_K m^(-1/(4K + 14))`. -/
theorem exists_hamBottomRatio_le (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (G : Finset (Vertex m)), G.card = 6 →
      RepairBound m G K →
        ∃ j < 2 * K + 7, hamBottomRatio m j ≤ C * (m : ℝ) ^ (-(1 / (4 * K + 14) : ℝ)) := by
  set J := 2 * K + 7 with hJ
  set D : ℝ := J.factorial * ((K + 1) * 2 ^ (K + 3)) * (2 / Real.sqrt π) ^ J with hD_def
  have hpi : 0 < Real.sqrt π := sqrt_pos.mpr pi_pos
  have hD : 0 < D := by positivity
  have hJpos : (0 : ℝ) < J := by positivity
  refine ⟨D ^ (1 / (J : ℝ)), rpow_pos_of_pos hD _, fun m _ G hG hK ↦ ?_⟩
  have hs : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  by_contra hcon
  push Not at hcon
  set x : ℝ := D ^ (1 / (J : ℝ)) * (m : ℝ) ^ (-(1 / (4 * K + 14) : ℝ)) with hx_def
  have hx : 0 < x := mul_pos (rpow_pos_of_pos hD _) (rpow_pos_of_pos hs _)
  have hlt : x ^ J < ∏ j ∈ range J, hamBottomRatio m j := by
    rw [show x ^ J = ∏ _j ∈ range J, x by rw [prod_const, card_range]]
    exact prod_lt_prod_of_nonempty₀ (fun _ _ ↦ hx) (fun j hj ↦ hcon j (mem_range.mp hj))
      (nonempty_range_iff.mpr (by omega))
  have hxJ : x ^ J = D / Real.sqrt m := by
    rw [hx_def, mul_pow, ← rpow_natCast (D ^ (1 / (J : ℝ))), ← rpow_mul hD.le,
      one_div_mul_cancel hJpos.ne', rpow_one, ← rpow_natCast ((m : ℝ) ^ _), ← rpow_mul hs.le,
      sqrt_eq_rpow (m : ℝ), div_eq_mul_inv D, ← rpow_neg hs.le]
    congr 2
    rw [hJ]
    push_cast
    field_simp
    ring
  have hle := prod_hamBottomRatio_le hG hK
  rw [← hJ] at hle
  rw [hxJ] at hlt
  linarith

end RoundRobin.Canonical

end Pairing
