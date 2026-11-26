import Repair.BoundedRadius
import Repair.CycleCount

/-!
# The cycle-step reduction (COD-146)

This file formalizes Identity D, Proposition D and Corollary D′ of the switching spike
(`results/switching-j0-spike.md`, ce14dda) and Proposition G of the merge-step spike
(`results/merge-step-spike.md`, fea4a1d). Notation is that of the spikes. `κ_t(P)` is the number
of cycles of `P ∪ F_t`, `Y_0 = X - 1[A_0]` is the number of `t ≠ 0` with `P ∪ F_t` Hamiltonian,
and `g_j(k) = P(Y_0 ≤ j | κ_0 = k)`.

* `cycleProfile m j k = g_j(k)`, `cycleMoment m C = E[C^(κ_0 - 1)]`.
* `hamBottomRatio_eq_cycleProfile` : `ρ_j = g_j(1) / P(X ≤ j)`, the size-bias identity.
* `inv_cycleMoment_le_hamBottomRatio` (Proposition D, first bound) : if `C ≥ 1` and
  `g_j(k) ≤ C^(k - 1) g_j(1)` for every `k ≥ 2`, then `ρ_j ≥ 1 / E[C^(κ_0 - 1)]`.
* `cycleMoment_le` : `E[C^(κ_0 - 1)] ≤ (2m - 1)^((C - 1)/2)` for `C ≥ 1`.
* `rpow_neg_le_hamBottomRatio` (Proposition D) : under the same hypothesis,
  `ρ_j ≥ (2m - 1)^(-(C - 1)/2)`.
* `not_boundedRadius_of_cycleProfile_le` (Corollary D′) : if `0 ≤ C < 2` and for every `J` there
  are infinitely many `m` with `g_j(k) ≤ C^(k - 1) g_j(1)` for all `k ≥ 2` and `j < J`, then (BK)
  fails. The proof goes through `not_boundedRadius_of_le_hamBottomRatio` (Proposition 1 of
  `results/bounded-radius-spike.md`).
* `cycleProfile_zero_eq` (Identity D) : `g_0(k) = P_0 E[D_k | Z] / E[D_k]` for `k ≥ 2`, with
  `D_k = #{t : κ_t = k}` (`cycleLevelCount`) and `E[D_k | Z] / E[D_k] = zeroTilt m k`.
  `hamBottomRatio_zero_eq` : `ρ_0 = g_0(1) / P_0`.
* `cycleProfile_two_le_iff` (Proposition G, (a) ⇔ (b)) : for `C > 0` and `P_0 > 0`,
  `g_0(2) ≤ C g_0(1) ↔ ρ_0 ≥ (E[D_2 | Z] / E[D_2]) / C`. The two consequences stated after it
  are `div_le_hamBottomRatio_of_cycleProfile_two_le` and
  `cycleProfile_two_le_of_le_hamBottomRatio`. Item (c) of Proposition G needs the exact value
  `E[D_2] = μ H_(m-1) / 2`, which is not formalized here.

Proposition D in the spike requires `P(X ≤ j) > 0` implicitly, since `ρ_j` is a ratio with that
denominator. Corollary D′ gets it from (BK) itself, which forces `P(X = 0) > 0`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open Finset PerfectMatching Real

/-- `κ_0(P)`, the number of cycles of `P ∪ F_0` (`results/switching-j0-spike.md`, Identity D). -/
noncomputable def cycleCountZero (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) : ℕ :=
  cycleCount P (factor m 0)

/-- `Y_0(P) = #{t ≠ 0 : P ∪ F_t is Hamiltonian}` (`results/switching-j0-spike.md`, Identity D). -/
def hamCountOff (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) : ℕ :=
  (univ.filter fun t ↦ t ≠ 0 ∧ Ham P (factor m t)).card

/-- `g_j(k) = P(Y_0 ≤ j | κ_0 = k)` under the uniform matching (`results/switching-j0-spike.md`,
Identity D). It is `0` when `P(κ_0 = k) = 0`. -/
noncomputable def cycleProfile (m : ℕ) [NeZero m] (j k : ℕ) : ℝ :=
  ((univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ j).card : ℝ) /
    (univ.filter fun P ↦ cycleCountZero m P = k).card

/-- `E[C^(κ_0 - 1)]` under the uniform matching (`results/switching-j0-spike.md`,
Proposition D). -/
noncomputable def cycleMoment (m : ℕ) [NeZero m] (C : ℝ) : ℝ :=
  (∑ P : PerfectMatching (Vertex m), C ^ (cycleCountZero m P - 1)) /
    Fintype.card (PerfectMatching (Vertex m))

/-- `X = Y_0 + 1[A_0]` (`results/switching-j0-spike.md`, Identity D). -/
theorem hamCount_eq_hamCountOff_add (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) :
    hamCount m P = hamCountOff m P + if Ham P (factor m 0) then 1 else 0 := by
  unfold hamCount hamCountOff
  split_ifs with h
  · rw [← card_insert_of_notMem (s := univ.filter fun t ↦ t ≠ 0 ∧ Ham P (factor m t))
      (a := 0) (by simp)]
    congr 1
    ext t
    by_cases ht : t = 0
    · simp [ht, h]
    · simp [ht]
  · congr 1
    ext t
    by_cases ht : t = 0
    · simp [ht, h]
    · simp [ht]

/-- `Y_0 ≤ X` (`results/switching-j0-spike.md`, Proposition D). -/
theorem hamCountOff_le (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) :
    hamCountOff m P ≤ hamCount m P := by
  rw [hamCount_eq_hamCountOff_add]
  exact Nat.le_add_right _ _

/-- `κ_0 = 1` is the event `A_0` (`results/switching-j0-spike.md`, Identity D). -/
theorem cycleCountZero_eq_one_iff (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) :
    cycleCountZero m P = 1 ↔ Ham P (factor m 0) :=
  (ham_iff_cycleCount_eq_one P (factor m 0)).symm

/-- `κ_0 ≥ 1` (`results/switching-j0-spike.md`, Identity D). -/
theorem cycleCountZero_pos (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) :
    0 < cycleCountZero m P :=
  cycleCount_pos P (factor m 0)

/-- `g_j(k) ≥ 0` (`results/switching-j0-spike.md`, Identity D). -/
theorem cycleProfile_nonneg (m : ℕ) [NeZero m] (j k : ℕ) : 0 ≤ cycleProfile m j k := by
  unfold cycleProfile
  positivity

/-- `#{κ_0 = k, Y_0 ≤ j} = g_j(k) #{κ_0 = k}` (`results/switching-j0-spike.md`, proof of
Proposition D). -/
theorem card_filter_eq_cycleProfile_mul (m : ℕ) [NeZero m] (j k : ℕ) :
    ((univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ j).card : ℝ) =
      cycleProfile m j k * (univ.filter fun P ↦ cycleCountZero m P = k).card := by
  unfold cycleProfile
  rcases eq_or_ne ((univ.filter fun P ↦ cycleCountZero m P = k).card : ℝ) 0 with h | h
  · have hle : (univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ j).card ≤
        (univ.filter fun P ↦ cycleCountZero m P = k).card :=
      card_le_card fun P hP ↦ by
        rw [mem_filter] at hP ⊢
        exact ⟨hP.1, hP.2.1⟩
    rw [h, mul_zero]
    have h' : (univ.filter fun P ↦ cycleCountZero m P = k).card = 0 := by exact_mod_cast h
    rw [h'] at hle
    exact_mod_cast Nat.le_zero.mp hle
  · rw [div_mul_cancel₀ _ h]

/-- `P(X ≤ j) = #{X ≤ j} / (2m - 1)!!` (`results/switching-j0-spike.md`, Proposition D). -/
theorem cdf_hamLaw (m : ℕ) [NeZero m] (j : ℕ) :
    SizeBias.cdf (hamLaw m) j =
      ((univ.filter fun P ↦ hamCount m P ≤ j).card : ℝ) /
        Fintype.card (PerfectMatching (Vertex m)) := by
  rw [SizeBias.cdf]
  simp only [hamLaw, ← sum_div]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := hamCount m) (t := range (j + 1))
    fun P hP ↦ mem_coe.mpr (mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hP).2))]
  push_cast
  refine sum_congr rfl fun k hk ↦ ?_
  congr 2
  ext P
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h ↦ ⟨h ▸ Nat.lt_succ_iff.mp (mem_range.mp hk), h⟩, fun h ↦ h.2⟩

/-- `g_j(1) = P(X - 1 ≤ j | A_0) = G(j + 1) / μ` (`results/switching-j0-spike.md`,
Proposition D, by the size-bias identity of frontier R1). -/
theorem cycleProfile_one (m : ℕ) [NeZero m] (j : ℕ) :
    cycleProfile m j 1 =
      SizeBias.partialMean (hamLaw m) (j + 1) / SizeBias.partialMean (hamLaw m) (2 * m - 1) := by
  rw [← cond_hamLaw, cycleProfile]
  congr 3
  · ext P
    simp only [mem_filter, mem_univ, true_and, cycleCountZero_eq_one_iff]
    refine and_congr_right fun h ↦ ?_
    rw [hamCount_eq_hamCountOff_add]
    simp [h]
  · ext P
    simp only [mem_filter, mem_univ, true_and, cycleCountZero_eq_one_iff]

/-- `ρ_j = g_j(1) / P(X ≤ j)` (`results/switching-j0-spike.md`, proof of Proposition D). -/
theorem hamBottomRatio_eq_cycleProfile (m : ℕ) [NeZero m] (j : ℕ) :
    hamBottomRatio m j = cycleProfile m j 1 / SizeBias.cdf (hamLaw m) j := by
  rw [hamBottomRatio, SizeBias.bottomRatio, cycleProfile_one, div_div]

/-- The counting step of Proposition D (`results/switching-j0-spike.md`): if
`g_j(k) ≤ C^(k - 1) g_j(1)` for every `k ≥ 2`, then
`#{X ≤ j} ≤ g_j(1) ∑_P C^(κ_0(P) - 1)`. -/
theorem card_le_cycleProfile_mul_sum {m : ℕ} [NeZero m] {j : ℕ} {C : ℝ}
    (h : ∀ k, 2 ≤ k → cycleProfile m j k ≤ C ^ (k - 1) * cycleProfile m j 1) :
    ((univ.filter fun P ↦ hamCount m P ≤ j).card : ℝ) ≤
      cycleProfile m j 1 * ∑ P : PerfectMatching (Vertex m), C ^ (cycleCountZero m P - 1) := by
  classical
  set t := (univ : Finset (PerfectMatching (Vertex m))).image (cycleCountZero m)
  have h1 : (univ.filter fun P ↦ hamCount m P ≤ j).card ≤
      (univ.filter fun P ↦ hamCountOff m P ≤ j).card :=
    card_le_card fun P hP ↦ by
      rw [mem_filter] at hP ⊢
      exact ⟨hP.1, (hamCountOff_le m P).trans hP.2⟩
  have h2 : ((univ.filter fun P ↦ hamCountOff m P ≤ j).card : ℝ) =
      ∑ k ∈ t, ((univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ j).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := cycleCountZero m) (t := t)
      fun P _ ↦ mem_coe.mpr (mem_image_of_mem _ (mem_univ P))]
    push_cast
    refine sum_congr rfl fun k _ ↦ ?_
    rw [filter_filter]
    congr 2
    ext P
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  have h3 : ∀ k ∈ t,
      ((univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ j).card : ℝ) ≤
        (univ.filter fun P ↦ cycleCountZero m P = k).card •
          (cycleProfile m j 1 * C ^ (k - 1)) := by
    intro k hk
    obtain ⟨P, -, rfl⟩ := mem_image.mp hk
    rw [card_filter_eq_cycleProfile_mul, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hpos := cycleCountZero_pos m P
    rcases Nat.lt_or_ge (cycleCountZero m P) 2 with hk1 | hk2
    · rw [show cycleCountZero m P = 1 by omega, Nat.sub_self, pow_zero, mul_one]
    · rw [mul_comm]
      exact h _ hk2
  calc ((univ.filter fun P ↦ hamCount m P ≤ j).card : ℝ)
      ≤ (univ.filter fun P ↦ hamCountOff m P ≤ j).card := by exact_mod_cast h1
    _ ≤ ∑ k ∈ t, (univ.filter fun P ↦ cycleCountZero m P = k).card •
          (cycleProfile m j 1 * C ^ (k - 1)) := by
        rw [h2]
        exact sum_le_sum h3
    _ = ∑ P : PerfectMatching (Vertex m), cycleProfile m j 1 * C ^ (cycleCountZero m P - 1) :=
        (sum_comp (fun k ↦ cycleProfile m j 1 * C ^ (k - 1)) (cycleCountZero m)).symm
    _ = cycleProfile m j 1 * ∑ P : PerfectMatching (Vertex m), C ^ (cycleCountZero m P - 1) :=
        (mul_sum _ _ _).symm

/-- `E[C^(κ_0 - 1)] ≥ 1` for `C ≥ 1` (`results/switching-j0-spike.md`, Proposition D). -/
theorem one_le_cycleMoment (m : ℕ) [NeZero m] {C : ℝ} (hC : 1 ≤ C) : 1 ≤ cycleMoment m C := by
  rw [cycleMoment, le_div_iff₀ (Nat.cast_pos.mpr (card_perfectMatching_pos m)), one_mul]
  calc (Fintype.card (PerfectMatching (Vertex m)) : ℝ)
      = ∑ _P : PerfectMatching (Vertex m), (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun P _ ↦ one_le_pow₀ hC

/-- Proposition D of `results/switching-j0-spike.md`, first bound. Let `C ≥ 1`. If
`g_j(k) ≤ C^(k - 1) g_j(1)` for every `k ≥ 2` and `P(X ≤ j) > 0`, then
`ρ_j ≥ 1 / E[C^(κ_0 - 1)]`. -/
theorem inv_cycleMoment_le_hamBottomRatio {m : ℕ} [NeZero m] {j : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (h : ∀ k, 2 ≤ k → cycleProfile m j k ≤ C ^ (k - 1) * cycleProfile m j 1)
    (hF : 0 < SizeBias.cdf (hamLaw m) j) :
    (cycleMoment m C)⁻¹ ≤ hamBottomRatio m j := by
  have hE := one_le_cycleMoment m hC
  have hE0 : 0 < cycleMoment m C := lt_of_lt_of_le one_pos hE
  have hN : (0 : ℝ) < Fintype.card (PerfectMatching (Vertex m)) :=
    Nat.cast_pos.mpr (card_perfectMatching_pos m)
  have key : SizeBias.cdf (hamLaw m) j ≤ cycleProfile m j 1 * cycleMoment m C := by
    rw [cdf_hamLaw, cycleMoment, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (card_le_cycleProfile_mul_sum h) hN.le
  rw [hamBottomRatio_eq_cycleProfile, le_div_iff₀ hF]
  calc (cycleMoment m C)⁻¹ * SizeBias.cdf (hamLaw m) j
      ≤ (cycleMoment m C)⁻¹ * (cycleProfile m j 1 * cycleMoment m C) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hE0.le)
    _ = cycleProfile m j 1 := by field_simp

/-- `(2n + 1)!! = ∏_{i < n} (2i + 3)` (`results/switching-j0-spike.md`, Proposition D). -/
theorem doubleFactorial_eq_prod (n : ℕ) :
    ((Nat.doubleFactorial (2 * n + 1) : ℕ) : ℝ) = ∏ i ∈ range n, (2 * (i : ℝ) + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← ih, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring,
      Nat.doubleFactorial_add_two]
    push_cast
    ring

/-- One step of the product bound in Proposition D (`results/switching-j0-spike.md`):
`(C + 2n + 2)(2n + 1)^a ≤ (2n + 3)^a (2n + 3)` with `a = (C - 1)/2` and `C ≥ 1`. -/
theorem add_mul_rpow_le {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    (C + 2 * n + 2) * (2 * (n : ℝ) + 1) ^ ((C - 1) / 2) ≤
      (2 * (n : ℝ) + 3) ^ ((C - 1) / 2) * (2 * n + 3) := by
  set a := (C - 1) / 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hn1 : (0 : ℝ) < 2 * n + 1 := by positivity
  have hn3 : (0 : ℝ) < 2 * n + 3 := by positivity
  set r := (2 * (n : ℝ) + 3) / (2 * n + 1) with hr
  have hr0 : 0 < r := div_pos hn3 hn1
  have hlog : 2 / (2 * (n : ℝ) + 3) ≤ Real.log r := by
    refine le_trans (le_of_eq ?_) (Real.one_sub_inv_le_log_of_pos hr0)
    rw [hr, inv_div]
    field_simp
    ring
  have hra : 1 + a * (2 / (2 * (n : ℝ) + 3)) ≤ r ^ a := by
    rw [Real.rpow_def_of_pos hr0]
    have := Real.add_one_le_exp (Real.log r * a)
    nlinarith [mul_le_mul_of_nonneg_left hlog ha0]
  have hsplit : (2 * (n : ℝ) + 3) ^ a = r ^ a * (2 * n + 1) ^ a := by
    rw [← Real.mul_rpow hr0.le hn1.le, hr, div_mul_cancel₀ _ hn1.ne']
  rw [hsplit]
  have hpow : 0 ≤ (2 * (n : ℝ) + 1) ^ a := Real.rpow_nonneg hn1.le a
  have hCeq : C + 2 * n + 2 = (2 * n + 3) * (1 + a * (2 / (2 * (n : ℝ) + 3))) := by
    rw [ha]
    field_simp
    ring
  rw [hCeq]
  calc (2 * (n : ℝ) + 3) * (1 + a * (2 / (2 * n + 3))) * (2 * n + 1) ^ a
      ≤ (2 * n + 3) * r ^ a * (2 * n + 1) ^ a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hra hn3.le) hpow
    _ = r ^ a * (2 * n + 1) ^ a * (2 * n + 3) := by ring

/-- The product bound of Proposition D (`results/switching-j0-spike.md`):
`∏_{i < n} (C + 2i + 2) ≤ (2n + 1)^((C - 1)/2) ∏_{i < n} (2i + 3)` for `C ≥ 1`. -/
theorem prod_le_rpow_mul_prod {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    ∏ i ∈ range n, (C + 2 * (i : ℝ) + 2) ≤
      (2 * (n : ℝ) + 1) ^ ((C - 1) / 2) * ∏ i ∈ range n, (2 * (i : ℝ) + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, prod_range_succ]
    have hC0 : 0 ≤ C + 2 * (n : ℝ) + 2 := by positivity
    have hP : 0 ≤ ∏ i ∈ range n, (2 * (i : ℝ) + 3) := prod_nonneg fun i _ ↦ by positivity
    calc (∏ i ∈ range n, (C + 2 * (i : ℝ) + 2)) * (C + 2 * n + 2)
        ≤ ((2 * (n : ℝ) + 1) ^ ((C - 1) / 2) * ∏ i ∈ range n, (2 * (i : ℝ) + 3)) *
            (C + 2 * n + 2) := mul_le_mul_of_nonneg_right ih hC0
      _ = ((C + 2 * n + 2) * (2 * (n : ℝ) + 1) ^ ((C - 1) / 2)) *
            ∏ i ∈ range n, (2 * (i : ℝ) + 3) := by ring
      _ ≤ ((2 * (n : ℝ) + 3) ^ ((C - 1) / 2) * (2 * n + 3)) *
            ∏ i ∈ range n, (2 * (i : ℝ) + 3) :=
          mul_le_mul_of_nonneg_right (add_mul_rpow_le hC n) hP
      _ = (2 * ((n + 1 : ℕ) : ℝ) + 1) ^ ((C - 1) / 2) *
            ((∏ i ∈ range n, (2 * (i : ℝ) + 3)) * (2 * n + 3)) := by
          push_cast
          ring_nf

/-- The moment bound of Proposition D (`results/switching-j0-spike.md`):
`E[C^(κ_0 - 1)] ≤ (2m - 1)^((C - 1)/2)` for `C ≥ 1`. It uses
`∑_P C^κ_0(P) ≤ C (C + 2) ⋯ (C + 2m - 2)` from `sum_pow_cycleCount_le`. -/
theorem cycleMoment_le (m : ℕ) [NeZero m] {C : ℝ} (hC : 1 ≤ C) :
    cycleMoment m C ≤ (2 * (m : ℝ) - 1) ^ ((C - 1) / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hsum := sum_pow_cycleCount_le hC (n + 1) (factor (n + 1) 0) (card_vertex (n + 1))
  rw [prod_range_succ'] at hsum
  have hsum' : ∑ P : PerfectMatching (Vertex (n + 1)), C ^ (cycleCountZero (n + 1) P - 1) ≤
      ∏ i ∈ range n, (C + 2 * (i : ℝ) + 2) := by
    have e : ∑ P : PerfectMatching (Vertex (n + 1)), C ^ cycleCount P (factor (n + 1) 0) =
        (∑ P : PerfectMatching (Vertex (n + 1)), C ^ (cycleCountZero (n + 1) P - 1)) * C := by
      rw [sum_mul]
      refine sum_congr rfl fun P _ ↦ ?_
      rw [← pow_succ, Nat.sub_add_cancel (cycleCountZero_pos (n + 1) P)]
      rfl
    rw [e] at hsum
    have e2 : (∏ i ∈ range n, (C + 2 * ((i + 1 : ℕ) : ℝ))) * (C + 2 * ((0 : ℕ) : ℝ)) =
        (∏ i ∈ range n, (C + 2 * (i : ℝ) + 2)) * C := by
      push_cast
      congr 1
      · exact prod_congr rfl fun i _ ↦ by ring
      · ring
    rw [e2] at hsum
    exact le_of_mul_le_mul_right hsum hC0
  have hcard : (Fintype.card (PerfectMatching (Vertex (n + 1))) : ℝ) =
      ∏ i ∈ range n, (2 * (i : ℝ) + 3) := by
    rw [card_eq_doubleFactorial (card_vertex (n + 1)), show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      doubleFactorial_eq_prod]
  have hpos : 0 < ∏ i ∈ range n, (2 * (i : ℝ) + 3) := prod_pos fun i _ ↦ by positivity
  rw [cycleMoment, hcard, div_le_iff₀ hpos]
  refine hsum'.trans (le_of_eq_of_le ?_ (prod_le_rpow_mul_prod hC n) |>.trans (le_of_eq ?_))
  · rfl
  · push_cast
    ring_nf

/-- Proposition D of `results/switching-j0-spike.md`. Let `C ≥ 1`. If
`g_j(k) ≤ C^(k - 1) g_j(1)` for every `k ≥ 2` and `P(X ≤ j) > 0`, then
`ρ_j ≥ (2m - 1)^(-(C - 1)/2)`. -/
theorem rpow_neg_le_hamBottomRatio {m : ℕ} [NeZero m] {j : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (h : ∀ k, 2 ≤ k → cycleProfile m j k ≤ C ^ (k - 1) * cycleProfile m j 1)
    (hF : 0 < SizeBias.cdf (hamLaw m) j) :
    (2 * (m : ℝ) - 1) ^ (-((C - 1) / 2)) ≤ hamBottomRatio m j := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
  have hE0 : 0 < cycleMoment m C := lt_of_lt_of_le one_pos (one_le_cycleMoment m hC)
  rw [Real.rpow_neg (by linarith)]
  exact (inv_anti₀ hE0 (cycleMoment_le m hC)).trans (inv_cycleMoment_le_hamBottomRatio hC h hF)

/-- `P(X ≤ j) ≥ P(X = 0)` (`results/switching-j0-spike.md`, Corollary D′). -/
theorem hamLaw_zero_le_cdf (m : ℕ) [NeZero m] (j : ℕ) :
    hamLaw m 0 ≤ SizeBias.cdf (hamLaw m) j :=
  single_le_sum (fun k _ ↦ (isLaw_hamLaw m).nonneg k) (mem_range.mpr (Nat.succ_pos j))

/-- (BK) forces `P(X = 0) > 0` at every `m` with a six-vertex gadget of repair radius `K`
(`results/bounded-radius-spike.md` C1, used in Corollary D′ of `results/switching-j0-spike.md`). -/
theorem hamLaw_zero_pos_of_repairBound {m : ℕ} [NeZero m] {G : Finset (Vertex m)}
    (hG : G.card = 6) {K : ℕ} (hK : RepairBound m G K) : 0 < hamLaw m 0 := by
  have h := one_le_hamLaw_zero_mul hG hK
  by_contra hq
  have hD : (0 : ℝ) ≤ (K + 1) * 2 ^ (K + 3) * (m : ℝ) ^ (K + 3) := by positivity
  have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) hD
  linarith

/-- `(2m - 1)^a ≤ m^(a + δ)` once `m^δ ≥ 2^a`, for `a ≥ 0` (`results/switching-j0-spike.md`,
Corollary D′). -/
theorem two_mul_sub_one_rpow_le {m : ℕ} (hm : 1 ≤ m) {a δ : ℝ} (ha : 0 ≤ a)
    (hδ : (2 : ℝ) ^ a ≤ (m : ℝ) ^ δ) :
    (2 * (m : ℝ) - 1) ^ a ≤ (m : ℝ) ^ (a + δ) := by
  have hm' : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hs : (0 : ℝ) < m := by linarith
  calc (2 * (m : ℝ) - 1) ^ a ≤ (2 * (m : ℝ)) ^ a :=
        Real.rpow_le_rpow (by linarith) (by linarith) ha
    _ = (2 : ℝ) ^ a * (m : ℝ) ^ a := Real.mul_rpow (by norm_num) hs.le
    _ ≤ (m : ℝ) ^ δ * (m : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hδ (Real.rpow_nonneg hs.le a)
    _ = (m : ℝ) ^ (a + δ) := by rw [Real.rpow_add hs, mul_comm]

/-- Corollary D′ of `results/switching-j0-spike.md`. Let `0 ≤ C < 2`. Suppose that for every
depth `J` and every `M` there is `m ≥ M` with `g_j(k) ≤ C^(k - 1) g_j(1)` for all `k ≥ 2` and all
`j < J`. Then (BK) fails: there are no `K` and `m₀` such that every `m ≥ m₀` has a six-vertex
gadget `G` with `RepairBound m G K`. The proof feeds Proposition D, with `C` replaced by
`max C 1`, into `not_boundedRadius_of_le_hamBottomRatio` (Proposition 1 of
`results/bounded-radius-spike.md`) at `θ = max C 1 / 4`. -/
theorem not_boundedRadius_of_cycleProfile_le {C : ℝ} (hC0 : 0 ≤ C) (hC2 : C < 2)
    (h : ∀ J M : ℕ, ∃ (m : ℕ) (_ : NeZero m), M ≤ m ∧
      ∀ j < J, ∀ k, 2 ≤ k → cycleProfile m j k ≤ C ^ (k - 1) * cycleProfile m j 1) :
    ¬∃ K m₀ : ℕ, ∀ (m : ℕ) [NeZero m], m₀ ≤ m →
      ∃ G : Finset (Vertex m), G.card = 6 ∧ RepairBound m G K := by
  set C' := max C 1 with hC'
  have h1 : 1 ≤ C' := le_max_right C 1
  have h2 : C' < 2 := max_lt hC2 (by norm_num)
  set a := (C' - 1) / 2 with ha
  set δ := (2 - C') / 4 with hδ
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hθ : a + δ < 1 / 2 := by rw [ha, hδ]; linarith
  rintro ⟨K, m₀, hBK⟩
  refine not_boundedRadius_of_le_hamBottomRatio hθ (fun J M ↦ ?_) ⟨K, m₀, hBK⟩
  have hlim : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop ((2 : ℝ) ^ a))
  obtain ⟨m, _, hm, hg⟩ := h J (max (max M m₀) M₁)
  refine ⟨m, inferInstance, le_of_max_le_left (le_of_max_le_left hm), fun j hj ↦ ?_⟩
  obtain ⟨G, hG, hK⟩ := hBK m (le_of_max_le_right (le_of_max_le_left hm))
  have hF : 0 < SizeBias.cdf (hamLaw m) j :=
    lt_of_lt_of_le (hamLaw_zero_pos_of_repairBound hG hK) (hamLaw_zero_le_cdf m j)
  have hg' : ∀ k, 2 ≤ k → cycleProfile m j k ≤ C' ^ (k - 1) * cycleProfile m j 1 :=
    fun k hk ↦ (hg j hj k hk).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hC0 (le_max_left C 1) _) (cycleProfile_nonneg m j 1))
  have hD := rpow_neg_le_hamBottomRatio h1 hg' hF
  have hm1 : 1 ≤ m := NeZero.pos m
  have hs : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
  have hb : (2 * (m : ℝ) - 1) ^ a ≤ (m : ℝ) ^ (a + δ) :=
    two_mul_sub_one_rpow_le hm1 ha0 (hM₁ m (le_of_max_le_right hm))
  have hm' : (0 : ℝ) < 2 * m - 1 := by
    have : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm1
    linarith
  have hpos : 0 < (2 * (m : ℝ) - 1) ^ a := Real.rpow_pos_of_pos hm' a
  refine le_trans ?_ hD
  rw [Real.rpow_neg hs.le, Real.rpow_neg hm'.le]
  exact inv_anti₀ hpos hb

/-- `κ` is invariant under relabelling both matchings (`results/switching-j0-spike.md`,
Identity D, translation symmetry). -/
theorem cycleCount_smul {V : Type*} (σ : Equiv.Perm V) (P Q : PerfectMatching V) :
    cycleCount (σ • P) (σ • Q) = cycleCount P Q :=
  (Nat.card_congr (unionIso σ P Q).connectedComponentEquiv).symm

/-- `D_k(P) = #{t : κ_t(P) = k}`, the number of factors `F_t` with `P ∪ F_t` made of `k` cycles
(`results/switching-j0-spike.md`, Identity D). `D_2` is the number of two-cycle factors. -/
noncomputable def cycleLevelCount (m : ℕ) [NeZero m] (k : ℕ) (P : PerfectMatching (Vertex m)) :
    ℕ :=
  (univ.filter fun t ↦ cycleCount P (factor m t) = k).card

/-- `#{P | κ_t(P) = k ∧ q (X P)}` does not depend on `t` (`results/switching-j0-spike.md`,
Identity D, translation symmetry). -/
theorem card_cycleCount_and_eq (m : ℕ) [NeZero m] (k : ℕ) (q : ℕ → Prop) [DecidablePred q]
    (t : ZMod (2 * m - 1)) :
    (univ.filter fun P ↦ cycleCount P (factor m t) = k ∧ q (hamCount m P)).card =
      (univ.filter fun P ↦ cycleCount P (factor m 0) = k ∧ q (hamCount m P)).card := by
  refine card_equiv (MulAction.toPerm (shift m (-t))) fun P ↦ ?_
  simp only [mem_filter, mem_univ, true_and, MulAction.toPerm_apply, hamCount_shift_smul]
  rw [← cycleCount_smul (shift m (-t)) P (factor m t), shift_smul_factor, add_neg_cancel]

/-- Double counting of the pairs `(P, t)` with `κ_t(P) = k`,
`∑_{P | q (X P)} D_k(P) = n · #{P | κ_0(P) = k ∧ q (X P)}` (`results/switching-j0-spike.md`,
Identity D). -/
theorem sum_cycleLevelCount (m : ℕ) [NeZero m] (k : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ∑ P ∈ univ.filter fun P ↦ q (hamCount m P), cycleLevelCount m k P =
      (2 * m - 1) * (univ.filter fun P ↦ cycleCountZero m P = k ∧ q (hamCount m P)).card := by
  have e : ∑ t, (univ.filter fun P ↦ cycleCount P (factor m t) = k ∧ q (hamCount m P)).card =
      ∑ P ∈ univ.filter fun P ↦ q (hamCount m P), cycleLevelCount m k P := by
    simp only [card_filter]
    rw [sum_comm, sum_filter]
    refine sum_congr rfl fun P _ ↦ ?_
    by_cases h : q (hamCount m P)
    · simp only [h, and_true, ite_true]
      rw [cycleLevelCount, card_filter]
    · simp [h]
  rw [← e, sum_congr rfl fun t _ ↦ card_cycleCount_and_eq m k q t, sum_const, card_univ,
    ZMod.card, smul_eq_mul]
  rfl

/-- The zero-set tilt `E[D_k | Z] / E[D_k]` of the number of `k`-cycle factors
(`results/switching-j0-spike.md`, Identity D, and `results/merge-step-spike.md`,
Proposition G, where `k = 2`). It is `0` when `Z` is empty or `E[D_k] = 0`. -/
noncomputable def zeroTilt (m : ℕ) [NeZero m] (k : ℕ) : ℝ :=
  ((∑ P ∈ univ.filter fun P ↦ hamCount m P = 0, (cycleLevelCount m k P : ℝ)) /
      (univ.filter fun P : PerfectMatching (Vertex m) ↦ hamCount m P = 0).card) /
    ((∑ P : PerfectMatching (Vertex m), (cycleLevelCount m k P : ℝ)) /
      Fintype.card (PerfectMatching (Vertex m)))

/-- Identity D of `results/switching-j0-spike.md`: for `k ≥ 2`,
`g_0(k) = P_0 · E[D_k | Z] / E[D_k]`, that is,
`g_0(k) / P_0 = E[#{t : κ_t = k} | Z] / (n P(κ_0 = k))`. -/
theorem cycleProfile_zero_eq (m : ℕ) [NeZero m] {k : ℕ} (hk : 2 ≤ k) :
    cycleProfile m 0 k = hamLaw m 0 * zeroTilt m k := by
  have hA := sum_cycleLevelCount m k (· = 0)
  have hB := sum_cycleLevelCount m k (fun _ ↦ True)
  simp only [and_true, filter_true] at hB
  have ha : (univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCountOff m P ≤ 0) =
      univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCount m P = 0 := by
    ext P
    simp only [mem_filter, mem_univ, true_and]
    refine and_congr_right fun h ↦ ?_
    have hn : ¬Ham P (factor m 0) := fun hh ↦ by
      rw [← cycleCountZero_eq_one_iff, h] at hh
      omega
    simp only [hamCount_eq_hamCountOff_add, hn, ↓reduceIte, add_zero, Nat.le_zero]
  set a := (univ.filter fun P ↦ cycleCountZero m P = k ∧ hamCount m P = 0).card
  set b := (univ.filter fun P ↦ cycleCountZero m P = k).card
  set z := (univ.filter fun P : PerfectMatching (Vertex m) ↦ hamCount m P = 0).card
  set N := Fintype.card (PerfectMatching (Vertex m))
  have hN : (N : ℝ) ≠ 0 := cast_card_perfectMatching_ne_zero m
  have hn : ((2 * m - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hA' : (∑ P ∈ univ.filter fun P ↦ hamCount m P = 0, (cycleLevelCount m k P : ℝ)) =
      ((2 * m - 1 : ℕ) : ℝ) * a := by exact_mod_cast hA
  have hB' : (∑ P : PerfectMatching (Vertex m), (cycleLevelCount m k P : ℝ)) =
      ((2 * m - 1 : ℕ) : ℝ) * b := by exact_mod_cast hB
  have hq : hamLaw m 0 = (z : ℝ) / N := rfl
  rw [cycleProfile, ha, zeroTilt, hA', hB', hq]
  rcases eq_or_ne (z : ℝ) 0 with hz | hz
  · have haz : a ≤ z := card_le_card fun P hP ↦ by
      rw [mem_filter] at hP ⊢
      exact ⟨hP.1, hP.2.2⟩
    have ha0 : (a : ℝ) = 0 := by
      have : z = 0 := by exact_mod_cast hz
      rw [this] at haz
      exact_mod_cast Nat.le_zero.mp haz
    rw [ha0, hz]
    simp
  rcases eq_or_ne (b : ℝ) 0 with hb | hb
  · rw [hb]
    simp
  change (a : ℝ) / b =
    (z : ℝ) / N * (((2 * m - 1 : ℕ) : ℝ) * a / z / (((2 * m - 1 : ℕ) : ℝ) * b / N))
  field_simp

/-- `ρ_0 = g_0(1) / P_0` (`results/switching-j0-spike.md`, Identity D). -/
theorem hamBottomRatio_zero_eq (m : ℕ) [NeZero m] :
    hamBottomRatio m 0 = cycleProfile m 0 1 / hamLaw m 0 := by
  rw [hamBottomRatio_eq_cycleProfile, show SizeBias.cdf (hamLaw m) 0 = hamLaw m 0 by
    simp [SizeBias.cdf]]

/-- Proposition G of `results/merge-step-spike.md`, (a) ⇔ (b). For `C > 0` and `P_0 > 0`,
`g_0(2) ≤ C g_0(1)` iff `ρ_0 ≥ (E[D_2 | Z] / E[D_2]) / C`. -/
theorem cycleProfile_two_le_iff {m : ℕ} [NeZero m] {C : ℝ} (hC : 0 < C) (hq : 0 < hamLaw m 0) :
    cycleProfile m 0 2 ≤ C * cycleProfile m 0 1 ↔ zeroTilt m 2 / C ≤ hamBottomRatio m 0 := by
  rw [hamBottomRatio_zero_eq, cycleProfile_zero_eq m le_rfl, div_le_div_iff₀ hC hq,
    mul_comm (zeroTilt m 2) (hamLaw m 0), mul_comm (cycleProfile m 0 1) C]

/-- Proposition G of `results/merge-step-spike.md`, first consequence. If
`E[D_2 | Z] ≥ c E[D_2]`, that is `E[D_2 | Z] / E[D_2] ≥ c`, then `g_0(2) ≤ C g_0(1)` gives
`ρ_0 ≥ c / C`. -/
theorem div_le_hamBottomRatio_of_cycleProfile_two_le {m : ℕ} [NeZero m] {C c : ℝ} (hC : 0 < C)
    (hq : 0 < hamLaw m 0) (hc : c ≤ zeroTilt m 2)
    (h : cycleProfile m 0 2 ≤ C * cycleProfile m 0 1) : c / C ≤ hamBottomRatio m 0 :=
  (div_le_div_of_nonneg_right hc hC.le).trans ((cycleProfile_two_le_iff hC hq).mp h)

/-- Proposition G of `results/merge-step-spike.md`, converse. If `ρ_0 ≥ c > 0` then
`g_0(2) ≤ C g_0(1)` with `C = (E[D_2 | Z] / E[D_2]) / c`, provided the tilt is positive. -/
theorem cycleProfile_two_le_of_le_hamBottomRatio {m : ℕ} [NeZero m] {c : ℝ} (hc : 0 < c)
    (hq : 0 < hamLaw m 0) (hτ : 0 < zeroTilt m 2) (h : c ≤ hamBottomRatio m 0) :
    cycleProfile m 0 2 ≤ zeroTilt m 2 / c * cycleProfile m 0 1 := by
  refine (cycleProfile_two_le_iff (div_pos hτ hc) hq).mpr ?_
  rwa [div_div_cancel₀ hτ.ne']

end RoundRobin.Canonical

end Pairing
