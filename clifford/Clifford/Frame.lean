import Clifford.Dimension

/-!
# Hyperbolic frame (sketch §6)

Indices are shifted by one from the sketch. For a gap `k : Fin (n - 1)`,
`frameE k = ∑_{a ≤ k} Γ_{2a, 2a+1}` is the sketch's `E_{k+1}` and
`frameF k = Γ_{2k+1, 2k+2}` is the sketch's `F_{k+1}`.

* `lower k = ∑_{a ≤ k} (Γ_{2a,2a+1} + 1)` acts on the basis by `lower_w`,
  `w_S ↦ [k ∈ S] w_{S \ k}`.
* `frameF_w` : `F_k w_S = w_{{k} Δ S}`.
* `frameE_eq` : `E_k = lower k + (k + 1) I`.
* Frame relations `frameE_sq`, `frameF_sq`, `frameE_anticomm_frameF`, and commutation for
  distinct gaps.
-/

namespace Pairing.PerfectMatching

open Equiv

variable (n : ℕ)

theorem W_add_self {V : Type*} [Fintype V] [DecidableEq V] (x : W V) : x + x = 0 := by
  rw [← two_smul F₂ x, show (2 : F₂) = 0 by decide, zero_smul]

theorem sum_filter_val_eq {M : Type*} [AddCommMonoid M] (S : Finset (Fin (n - 1))) (j : ℕ)
    (hj : j < n - 1) (f : Fin (n - 1) → M) :
    ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = j), f g =
      if (⟨j, hj⟩ : Fin (n - 1)) ∈ S then f ⟨j, hj⟩ else 0 := by
  rw [Finset.filter_congr (q := fun g ↦ g = ⟨j, hj⟩) (fun g _ ↦ by rw [Fin.ext_iff]),
    Finset.sum_filter, Finset.sum_ite_eq']

/-- `Γ_{2a,2a+1} + 1` on the basis. -/
theorem N_w (a : Fin n) (S : Finset (Fin (n - 1))) :
    (B n a + 1) (w n S) =
      ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a), w n (S.erase g) := by
  rw [LinearMap.add_apply, B_w, Module.End.one_apply, add_comm, ← add_assoc, W_add_self, zero_add]

/-- The lowering operator at gap `k`. -/
def lower (k : ℕ) (hk : k < n - 1) : Module.End F₂ (W (Fin (2 * n))) :=
  ∑ a : Fin (k + 1), (B n ⟨a, by omega⟩ + 1)

theorem lower_succ (k : ℕ) (hk : k + 1 < n - 1) :
    lower n (k + 1) hk = lower n k (by omega) + (B n ⟨k + 1, by omega⟩ + 1) := by
  rw [lower, Fin.sum_univ_castSucc]
  rfl

/-- `lower k` on the basis, `w_S ↦ [k ∈ S] w_{S \ k}`. -/
theorem lower_w (k : ℕ) (hk : k < n - 1) (S : Finset (Fin (n - 1))) :
    lower n k hk (w n S) =
      if (⟨k, hk⟩ : Fin (n - 1)) ∈ S then w n (S.erase ⟨k, hk⟩) else 0 := by
  induction k with
  | zero =>
    rw [lower, Fin.sum_univ_one, N_w,
      Finset.filter_congr (q := fun g : Fin (n - 1) ↦ (g : ℕ) = 0) (fun g _ ↦ by simp),
      sum_filter_val_eq n S 0 hk]
  | succ k ih =>
    rw [lower_succ, LinearMap.add_apply, ih (by omega), N_w, Finset.filter_or,
      Finset.sum_union (Finset.disjoint_filter.mpr fun g _ h1 h2 ↦ by simp only at h1 h2; omega),
      sum_filter_val_eq n S (k + 1) hk,
      Finset.filter_congr (q := fun g : Fin (n - 1) ↦ (g : ℕ) = k) (fun g _ ↦ by simp),
      sum_filter_val_eq n S k (by omega)]
    split_ifs <;> simp [W_add_self, add_comm, add_left_comm]

/-- `E_k = ∑_{a ≤ k} Γ_{2a, 2a+1}`, the sketch's `E_{k+1}`. -/
def frameE (k : Fin (n - 1)) : Module.End F₂ (W (Fin (2 * n))) :=
  ∑ a : Fin (k + 1), B n ⟨a, by omega⟩

/-- `F_k = Γ_{2k+1, 2k+2}`, the sketch's `F_{k+1}`. -/
def frameF (k : Fin (n - 1)) : Module.End F₂ (W (Fin (2 * n))) :=
  ρW (sigma n {k})

theorem frameE_eq (k : Fin (n - 1)) :
    frameE n k = lower n k k.2 + ((k + 1 : ℕ) : F₂) • 1 := by
  rw [lower, frameE, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    add_assoc, ← Nat.cast_smul_eq_nsmul F₂, ← add_smul, CharTwo.add_self_eq_zero, zero_smul,
    add_zero]

theorem frameF_w (k : Fin (n - 1)) (S : Finset (Fin (n - 1))) :
    frameF n k (w n S) = w n (symmDiff {k} S) :=
  ρW_sigma_w n S {k}

theorem lower_w' (k : Fin (n - 1)) (S : Finset (Fin (n - 1))) :
    lower n k k.2 (w n S) = if k ∈ S then w n (S.erase k) else 0 :=
  lower_w n k k.2 S

/-- `({k} Δ S) \ k = S` for `k ∉ S`. -/
theorem symmDiff_single_erase_self {k : Fin (n - 1)} {S : Finset (Fin (n - 1))}
    (h : k ∉ S) : (symmDiff {k} S).erase k = S := by
  ext x
  by_cases hx : x = k
  · subst hx
    simp [h]
  · simp [hx, Finset.mem_symmDiff]

/-- `{k} Δ (S \ k) = S` for `k ∈ S`. -/
theorem symmDiff_single_erase {k : Fin (n - 1)} {S : Finset (Fin (n - 1))}
    (h : k ∈ S) : symmDiff {k} (S.erase k) = S := by
  ext x
  by_cases hx : x = k
  · subst hx
    simp [h, Finset.mem_symmDiff]
  · simp [hx, Finset.mem_symmDiff]

/-- `k ∈ {l} Δ S ↔ k ∈ S` for `k ≠ l`. -/
theorem mem_symmDiff_single {k l : Fin (n - 1)} {S : Finset (Fin (n - 1))} (h : k ≠ l) :
    k ∈ symmDiff {l} S ↔ k ∈ S := by
  simp [Finset.mem_symmDiff, h]

/-- `({l} Δ S) \ k = {l} Δ (S \ k)` for `k ≠ l`. -/
theorem symmDiff_single_erase_comm {k l : Fin (n - 1)} {S : Finset (Fin (n - 1))}
    (h : k ≠ l) : (symmDiff {l} S).erase k = symmDiff {l} (S.erase k) := by
  ext x
  by_cases hx : x = k
  · subst hx
    simp [Finset.mem_symmDiff, h]
  · simp [Finset.mem_symmDiff, hx]

theorem lower_sq (k : Fin (n - 1)) : lower n k k.2 * lower n k k.2 = 0 := by
  have hn : 1 ≤ n := by have := k.2; omega
  refine (wBasis n hn).ext fun S ↦ ?_
  rw [wBasis_apply, Module.End.mul_apply, lower_w', LinearMap.zero_apply]
  split_ifs with h
  · rw [lower_w', ite_eq_right (Finset.notMem_erase k S)]
  · rw [map_zero]

theorem lower_anticomm_frameF (k : Fin (n - 1)) :
    lower n k k.2 * frameF n k + frameF n k * lower n k k.2 = 1 := by
  have hn : 1 ≤ n := by have := k.2; omega
  refine (wBasis n hn).ext fun S ↦ ?_
  rw [wBasis_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, frameF_w,
    lower_w', lower_w', Module.End.one_apply]
  by_cases h : k ∈ S
  · rw [ite_eq_right (by simp [Finset.mem_symmDiff, h]), ite_eq_left h, zero_add, frameF_w,
      symmDiff_single_erase n h]
  · rw [ite_eq_left (by simp [Finset.mem_symmDiff, h]), ite_eq_right h, map_zero, add_zero,
      symmDiff_single_erase_self n h]

/-- `F_k² = I`. -/
theorem frameF_sq (k : Fin (n - 1)) : frameF n k * frameF n k = 1 := by
  rw [frameF, ← map_mul, sigma_mul_self, map_one]

/-- `E_k² = (k + 1 mod 2) I`, the sketch's `E_k² = (k mod 2) I`. -/
theorem frameE_sq (k : Fin (n - 1)) :
    frameE n k * frameE n k = ((k + 1 : ℕ) : F₂) • 1 := by
  rw [frameE_eq]
  generalize ((k + 1 : ℕ) : F₂) = c
  rw [add_mul, mul_add, mul_add, lower_sq, zero_add, smul_mul_assoc, one_mul, mul_smul_comm,
    mul_one, smul_mul_smul_comm, one_mul, ← add_assoc, end_add_self, zero_add]
  rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl <;> simp

/-- `{E_k, F_k} = I`. -/
theorem frameE_anticomm_frameF (k : Fin (n - 1)) :
    frameE n k * frameF n k + frameF n k * frameE n k = 1 := by
  rw [frameE_eq, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    add_add_add_comm, lower_anticomm_frameF, end_add_self, add_zero]

/-- Frame operators at distinct gaps commute. -/
theorem frame_commute {k l : Fin (n - 1)} (hkl : k ≠ l) :
    Commute (lower n k k.2) (lower n l l.2) ∧ Commute (lower n k k.2) (frameF n l) ∧
      Commute (frameF n k) (frameF n l) := by
  have hn : 1 ≤ n := by have := k.2; omega
  refine ⟨?_, ?_, ?_⟩
  · refine (wBasis n hn).ext fun S ↦ ?_
    simp only [wBasis_apply, Module.End.mul_apply, lower_w']
    by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;>
      simp [hk, hl, lower_w', Finset.mem_erase, hkl, Ne.symm hkl, Finset.erase_right_comm]
  · refine (wBasis n hn).ext fun S ↦ ?_
    simp only [wBasis_apply, Module.End.mul_apply, lower_w', frameF_w]
    rw [if_congr (mem_symmDiff_single n hkl) rfl rfl]
    split_ifs
    · rw [frameF_w, symmDiff_single_erase_comm n hkl]
    · rw [map_zero]
  · rw [Commute, SemiconjBy, frameF, frameF, ← map_mul, ← map_mul, sigma_mul, sigma_mul,
      symmDiff_comm]

theorem frameE_commute {k l : Fin (n - 1)} (hkl : k ≠ l) :
    Commute (frameE n k) (frameE n l) ∧ Commute (frameE n k) (frameF n l) ∧
      Commute (frameF n k) (frameF n l) := by
  obtain ⟨h1, h2, h3⟩ := frame_commute n hkl
  rw [frameE_eq, frameE_eq]
  refine ⟨?_, ?_, h3⟩
  · exact (h1.add_right ((Commute.one_right _).smul_right _)).add_left
      (((Commute.one_left _).smul_left _).add_right
        ((Commute.one_left _).smul_left _ |>.smul_right _))
  · exact h2.add_left ((Commute.one_left _).smul_left _)

end Pairing.PerfectMatching
