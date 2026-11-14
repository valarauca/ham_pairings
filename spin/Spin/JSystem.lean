import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# M3. Anticommuting involutions bound the dimension of a simple module

Let `J_0, …, J_{2p}` be pairwise anticommuting involutions on a finite-dimensional `K`-vector
space `Y`, with `2 ≠ 0` and `I² = -1` in `K`. If the only `J`-stable subspaces of `Y ≠ 0` are
`⊥` and `⊤` then `dim Y ≤ 2^p` (`finrank_le_of_jSystem`).

The proof uses `E_k = J_{2k} + I J_{2k+1}` and `F_k = J_{2k} - I J_{2k+1}`, which satisfy
`E_k² = F_k² = 0` and `E_k F_k + F_k E_k = 4`, and `U = J_{2p}`. A vacuum `m₀` is killed by every
`E_k` and is an eigenvector of `U`. The tower `A_0 = K m₀`, `A_{j+1} = A_j + F_j A_j` is stable
under every `E_k`, `F_k` and `U`, so `A_p = Y`.
-/

namespace Pairing

variable {K Y : Type*} [Field K] [AddCommGroup Y] [Module K Y]

/-- `X Y + Y X = 0`. -/
def AntiComm (X Z : Module.End K Y) : Prop :=
  X * Z + Z * X = 0

theorem AntiComm.symm {X Z : Module.End K Y} (h : AntiComm X Z) : AntiComm Z X := by
  rw [AntiComm, add_comm]
  exact h

theorem AntiComm.add_right {X Z Z' : Module.End K Y} (h : AntiComm X Z) (h' : AntiComm X Z') :
    AntiComm X (Z + Z') := by
  rw [AntiComm] at *
  calc X * (Z + Z') + (Z + Z') * X = (X * Z + Z * X) + (X * Z' + Z' * X) := by noncomm_ring
    _ = 0 := by rw [h, h', add_zero]

theorem AntiComm.smul_right {X Z : Module.End K Y} (h : AntiComm X Z) (c : K) :
    AntiComm X (c • Z) := by
  rw [AntiComm] at *
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, h, smul_zero]

theorem AntiComm.sub_right {X Z Z' : Module.End K Y} (h : AntiComm X Z) (h' : AntiComm X Z') :
    AntiComm X (Z - Z') := by
  rw [sub_eq_add_neg, ← neg_one_smul K Z']
  exact h.add_right (h'.smul_right _)

theorem AntiComm.apply {X Z : Module.End K Y} (h : AntiComm X Z) (y : Y) : X (Z y) = -Z (X y) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, eq_neg_iff_add_eq_zero,
    ← LinearMap.add_apply, h,
    LinearMap.zero_apply]

theorem mul_pair {A B : Module.End K Y} (hA : A * A = 1) (hB : B * B = 1) (s t : K) :
    (A + s • B) * (A + t • B) = (1 + s * t) • 1 + t • (A * B) + s • (B * A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hA, hB]
  module

variable (p : ℕ) (J : Fin (2 * p + 1) → Module.End K Y) (I : K)

/-- Pairwise anticommuting involutions. -/
structure IsJSystem : Prop where
  sq : ∀ j, J j * J j = 1
  anti : ∀ i j, i ≠ j → AntiComm (J i) (J j)

/-- `E_k = J_{2k} + I J_{2k+1}`. -/
def jE (k : Fin p) : Module.End K Y :=
  J ⟨2 * k, by omega⟩ + I • J ⟨2 * k + 1, by omega⟩

/-- `F_k = J_{2k} - I J_{2k+1}`. -/
def jF (k : Fin p) : Module.End K Y :=
  J ⟨2 * k, by omega⟩ + (-I) • J ⟨2 * k + 1, by omega⟩

/-- `U = J_{2p}`. -/
def jU : Module.End K Y :=
  J ⟨2 * p, by omega⟩

variable {p J I}

theorem jE_sq (hJ : IsJSystem p J) (hI : I * I = -1) (k : Fin p) : jE p J I k * jE p J I k = 0 := by
  have hAB : AntiComm (J ⟨2 * k, by omega⟩) (J ⟨2 * k + 1, by omega⟩) :=
    hJ.anti _ _ (Fin.ne_of_val_ne (by simp))
  rw [AntiComm] at hAB
  rw [jE, mul_pair (hJ.sq _) (hJ.sq _), hI, add_assoc, ← smul_add, hAB, smul_zero, add_zero,
    add_neg_cancel, zero_smul]

theorem jF_sq (hJ : IsJSystem p J) (hI : I * I = -1) (k : Fin p) : jF p J I k * jF p J I k = 0 := by
  have hAB : AntiComm (J ⟨2 * k, by omega⟩) (J ⟨2 * k + 1, by omega⟩) :=
    hJ.anti _ _ (Fin.ne_of_val_ne (by simp))
  rw [AntiComm] at hAB
  rw [jF, mul_pair (hJ.sq _) (hJ.sq _), neg_mul_neg, hI, add_assoc, ← smul_add, hAB, smul_zero,
    add_zero, add_neg_cancel, zero_smul]

theorem jE_jF (hJ : IsJSystem p J) (hI : I * I = -1) (k : Fin p) :
    jE p J I k * jF p J I k + jF p J I k * jE p J I k = (4 : K) • 1 := by
  have hAB : AntiComm (J ⟨2 * k, by omega⟩) (J ⟨2 * k + 1, by omega⟩) :=
    hJ.anti _ _ (Fin.ne_of_val_ne (by simp))
  rw [AntiComm] at hAB
  have e : J ⟨2 * k + 1, by omega⟩ * J ⟨2 * k, by omega⟩ =
      -(J ⟨2 * k, by omega⟩ * J ⟨2 * k + 1, by omega⟩) := eq_neg_of_add_eq_zero_right hAB
  rw [jE, jF, mul_pair (hJ.sq _) (hJ.sq _), mul_pair (hJ.sq _) (hJ.sq _), mul_neg, neg_mul, hI, e]
  module

theorem antiComm_J_E (hJ : IsJSystem p J) {j : Fin (2 * p + 1)} {k : Fin p}
    (h0 : (j : ℕ) ≠ 2 * k) (h1 : (j : ℕ) ≠ 2 * k + 1) : AntiComm (J j) (jE p J I k) :=
  (hJ.anti _ _ (Fin.ne_of_val_ne (by simpa using h0))).add_right
    ((hJ.anti _ _ (Fin.ne_of_val_ne (by simpa using h1))).smul_right _)

theorem antiComm_J_F (hJ : IsJSystem p J) {j : Fin (2 * p + 1)} {k : Fin p}
    (h0 : (j : ℕ) ≠ 2 * k) (h1 : (j : ℕ) ≠ 2 * k + 1) : AntiComm (J j) (jF p J I k) :=
  (hJ.anti _ _ (Fin.ne_of_val_ne (by simpa using h0))).add_right
    ((hJ.anti _ _ (Fin.ne_of_val_ne (by simpa using h1))).smul_right _)

theorem antiComm_E_E (hJ : IsJSystem p J) {k l : Fin p} (h : k ≠ l) :
    AntiComm (jE p J I k) (jE p J I l) := by
  have hv := Fin.val_ne_of_ne h
  exact ((antiComm_J_E hJ (by simp; omega) (by simp; omega)).symm.add_right
    ((antiComm_J_E hJ (by simp; omega) (by simp; omega)).symm.smul_right _)).symm

theorem antiComm_E_F (hJ : IsJSystem p J) {k l : Fin p} (h : k ≠ l) :
    AntiComm (jE p J I k) (jF p J I l) := by
  have hv := Fin.val_ne_of_ne h
  exact ((antiComm_J_F hJ (by simp; omega) (by simp; omega)).symm.add_right
    ((antiComm_J_F hJ (by simp; omega) (by simp; omega)).symm.smul_right _)).symm

theorem antiComm_F_F (hJ : IsJSystem p J) {k l : Fin p} (h : k ≠ l) :
    AntiComm (jF p J I k) (jF p J I l) := by
  have hv := Fin.val_ne_of_ne h
  exact ((antiComm_J_F hJ (by simp; omega) (by simp; omega)).symm.add_right
    ((antiComm_J_F hJ (by simp; omega) (by simp; omega)).symm.smul_right _)).symm

theorem antiComm_U_E (hJ : IsJSystem p J) (k : Fin p) : AntiComm (jU p J) (jE p J I k) :=
  antiComm_J_E hJ (by simp; omega) (by simp; omega)

theorem antiComm_U_F (hJ : IsJSystem p J) (k : Fin p) : AntiComm (jU p J) (jF p J I k) :=
  antiComm_J_F hJ (by simp; omega) (by simp; omega)

variable (p J I) in
/-- `A_0 = K m₀`, `A_{j+1} = A_j + F_j A_j`. -/
def jTower (m₀ : Y) : ℕ → Submodule K Y
  | 0 => K ∙ m₀
  | j + 1 => if h : j < p then jTower m₀ j ⊔ (jTower m₀ j).map (jF p J I ⟨j, h⟩) else jTower m₀ j

theorem jTower_succ {m₀ : Y} {j : ℕ} (h : j < p) :
    jTower p J I m₀ (j + 1) = jTower p J I m₀ j ⊔ (jTower p J I m₀ j).map (jF p J I ⟨j, h⟩) := by
  simp only [jTower, h, ↓reduceDIte]

theorem jTower_succ_of_le {m₀ : Y} {j : ℕ} (h : p ≤ j) :
    jTower p J I m₀ (j + 1) = jTower p J I m₀ j := by
  simp only [jTower, show ¬j < p by omega, ↓reduceDIte]

theorem mem_jTower_succ {m₀ : Y} {j : ℕ} (h : j < p) {y : Y} (hy : y ∈ jTower p J I m₀ (j + 1)) :
    ∃ a ∈ jTower p J I m₀ j, ∃ a' ∈ jTower p J I m₀ j, y = a + jF p J I ⟨j, h⟩ a' := by
  rw [jTower_succ h, Submodule.mem_sup] at hy
  obtain ⟨a, ha, z, hz, rfl⟩ := hy
  obtain ⟨a', ha', rfl⟩ := Submodule.mem_map.mp hz
  exact ⟨a, ha, a', ha', rfl⟩

theorem mem_jTower_succ_of_mem {m₀ : Y} {j : ℕ} {y : Y} (hy : y ∈ jTower p J I m₀ j) :
    y ∈ jTower p J I m₀ (j + 1) := by
  by_cases h : j < p
  · rw [jTower_succ h]
    exact Submodule.mem_sup_left hy
  · rwa [jTower_succ_of_le (by omega)]

theorem F_mem_jTower_succ {m₀ : Y} {j : ℕ} (h : j < p) {a : Y} (ha : a ∈ jTower p J I m₀ j) :
    jF p J I ⟨j, h⟩ a ∈ jTower p J I m₀ (j + 1) := by
  rw [jTower_succ h]
  exact Submodule.mem_sup_right (Submodule.mem_map_of_mem ha)

theorem jU_mem_jTower (hJ : IsJSystem p J) {m₀ : Y} (hm : jU p J m₀ = m₀ ∨ jU p J m₀ = -m₀)
    (j : ℕ) {y : Y} (hy : y ∈ jTower p J I m₀ j) : jU p J y ∈ jTower p J I m₀ j := by
  induction j generalizing y with
  | zero =>
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul]
    rcases hm with h | h <;> rw [h]
    · exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self m₀)
    · exact Submodule.smul_mem _ c (Submodule.neg_mem _ (Submodule.mem_span_singleton_self m₀))
  | succ j ih =>
    by_cases h : j < p
    · obtain ⟨a, ha, a', ha', rfl⟩ := mem_jTower_succ h hy
      rw [map_add, (antiComm_U_F hJ _).apply]
      exact add_mem (mem_jTower_succ_of_mem (ih ha))
        (Submodule.neg_mem _ (F_mem_jTower_succ h (ih ha')))
    · rw [jTower_succ_of_le (by omega)] at hy ⊢
      exact ih hy

theorem jE_mem_jTower (hJ : IsJSystem p J) (hI : I * I = -1) {m₀ : Y}
    (hm : ∀ k, jE p J I k m₀ = 0) (k : Fin p) (j : ℕ) {y : Y} (hy : y ∈ jTower p J I m₀ j) :
    jE p J I k y ∈ jTower p J I m₀ j := by
  induction j generalizing y with
  | zero =>
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hm k, smul_zero]
    exact zero_mem _
  | succ j ih =>
    by_cases h : j < p
    · obtain ⟨a, ha, a', ha', rfl⟩ := mem_jTower_succ h hy
      rw [map_add]
      refine add_mem (mem_jTower_succ_of_mem (ih ha)) ?_
      by_cases hkj : k = ⟨j, h⟩
      · subst hkj
        have e := congrArg (fun f : Module.End K Y ↦ f a') (jE_jF hJ hI ⟨j, h⟩)
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
          Module.End.one_apply] at e
        rw [eq_sub_of_add_eq e]
        exact sub_mem (Submodule.smul_mem _ _ (mem_jTower_succ_of_mem ha'))
          (F_mem_jTower_succ h (ih ha'))
      · rw [(antiComm_E_F hJ hkj).apply]
        exact Submodule.neg_mem _ (F_mem_jTower_succ h (ih ha'))
    · rw [jTower_succ_of_le (by omega)] at hy ⊢
      exact ih hy

theorem jF_mem_jTower (hJ : IsJSystem p J) (hI : I * I = -1) {m₀ : Y} (k : Fin p) (j : ℕ)
    (hkj : (k : ℕ) < j) {y : Y} (hy : y ∈ jTower p J I m₀ j) :
    jF p J I k y ∈ jTower p J I m₀ j := by
  induction j generalizing y with
  | zero => omega
  | succ j ih =>
    by_cases h : j < p
    · obtain ⟨a, ha, a', ha', rfl⟩ := mem_jTower_succ h hy
      rw [map_add]
      by_cases hk : (k : ℕ) = j
      · have e : k = ⟨j, h⟩ := Fin.ext hk
        subst e
        rw [← Module.End.mul_apply (jF p J I _) (jF p J I _), jF_sq hJ hI, LinearMap.zero_apply,
          add_zero]
        exact F_mem_jTower_succ h ha
      · have hk' : k ≠ ⟨j, h⟩ := fun e ↦ hk (by rw [e])
        rw [(antiComm_F_F hJ hk').apply]
        exact add_mem (mem_jTower_succ_of_mem (ih (by omega) ha))
          (Submodule.neg_mem _ (F_mem_jTower_succ h (ih (by omega) ha')))
    · rw [jTower_succ_of_le (by omega)] at hy ⊢
      exact ih (by omega) hy

theorem finrank_jTower_le [FiniteDimensional K Y] (m₀ : Y) (j : ℕ) :
    Module.finrank K (jTower p J I m₀ j) ≤ 2 ^ j := by
  induction j with
  | zero =>
    rw [pow_zero]
    exact (finrank_span_le_card ({m₀} : Set Y)).trans (by simp)
  | succ j ih =>
    by_cases h : j < p
    · rw [jTower_succ h]
      calc Module.finrank K ↥(jTower p J I m₀ j ⊔ (jTower p J I m₀ j).map (jF p J I ⟨j, h⟩))
          ≤ Module.finrank K (jTower p J I m₀ j) +
            Module.finrank K ((jTower p J I m₀ j).map (jF p J I ⟨j, h⟩)) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ 2 ^ j + 2 ^ j := add_le_add ih ((Submodule.finrank_map_le _ _).trans ih)
        _ = 2 ^ (j + 1) := by ring
    · rw [jTower_succ_of_le (by omega)]
      exact ih.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem exists_jVacuum (hJ : IsJSystem p J) (hI : I * I = -1) [Nontrivial Y] :
    ∃ m : Y, m ≠ 0 ∧ (∀ k, jE p J I k m = 0) ∧ (jU p J m = m ∨ jU p J m = -m) := by
  have key : ∀ j ≤ p, ∃ m : Y, m ≠ 0 ∧ ∀ k : Fin p, (k : ℕ) < j → jE p J I k m = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨m, hm⟩ := exists_ne (0 : Y)
      exact ⟨m, hm, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨m, hm0, hm⟩ := ih (by omega)
      have hsplit : ∀ k : Fin p, (k : ℕ) < j + 1 → (k : ℕ) < j ∨ k = ⟨j, hj⟩ := by
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      by_cases hb : jE p J I ⟨j, hj⟩ m = 0
      · refine ⟨m, hm0, fun k hk ↦ ?_⟩
        rcases hsplit k hk with h | rfl
        · exact hm k h
        · exact hb
      · refine ⟨jE p J I ⟨j, hj⟩ m, hb, fun k hk ↦ ?_⟩
        rcases hsplit k hk with h | rfl
        · have hne : k ≠ ⟨j, hj⟩ := fun e ↦ by rw [e] at h; simp at h
          rw [(antiComm_E_E hJ hne).apply, hm k h, map_zero, neg_zero]
        · rw [← Module.End.mul_apply, jE_sq hJ hI, LinearMap.zero_apply]
  obtain ⟨m, hm0, hm⟩ := key p le_rfl
  have hE : ∀ k, jE p J I k m = 0 := fun k ↦ hm k k.2
  have hEU : ∀ k, jE p J I k (jU p J m) = 0 := fun k ↦ by
    rw [(antiComm_U_E hJ k).symm.apply, hE k, map_zero, neg_zero]
  have hUU : ∀ y, jU p J (jU p J y) = y := fun y ↦ by
    rw [← Module.End.mul_apply, jU, hJ.sq, Module.End.one_apply]
  by_cases hc : jU p J m + m = 0
  · exact ⟨m, hm0, hE, Or.inr (eq_neg_of_add_eq_zero_left hc)⟩
  · refine ⟨jU p J m + m, hc, fun k ↦ by rw [map_add, hEU k, hE k, add_zero], Or.inl ?_⟩
    rw [map_add, hUU, add_comm]

theorem mem_jTower_self (m₀ : Y) (j : ℕ) : m₀ ∈ jTower p J I m₀ j := by
  induction j with
  | zero => exact Submodule.mem_span_singleton_self m₀
  | succ j ih => exact mem_jTower_succ_of_mem ih

/-- Pairwise anticommuting involutions `J_0, …, J_{2p}` acting irreducibly force
`dim Y ≤ 2^p`. -/
theorem finrank_le_of_jSystem [FiniteDimensional K Y] [Nontrivial Y] (hJ : IsJSystem p J)
    (hI : I * I = -1) (h2 : (2 : K) ≠ 0)
    (hsimple : ∀ N : Submodule K Y, (∀ j, ∀ y ∈ N, J j y ∈ N) → N = ⊥ ∨ N = ⊤) :
    Module.finrank K Y ≤ 2 ^ p := by
  obtain ⟨m₀, hm0, hE, hU⟩ := exists_jVacuum (I := I) hJ hI
  set A := jTower p J I m₀ p with hA
  have hI0 : I ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_eq_neg] at hI
    exact one_ne_zero hI
  have hJA : ∀ j, ∀ y ∈ A, J j y ∈ A := by
    intro j y hy
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
    · by_cases hkp : k < p
      · have hj : j = ⟨2 * k, by omega⟩ := Fin.ext hk
        rw [hj]
        have e2 : jE p J I ⟨k, hkp⟩ + jF p J I ⟨k, hkp⟩ = (2 : K) • J ⟨2 * k, by omega⟩ := by
          rw [jE, jF]
          module
        rw [← inv_smul_smul₀ h2 (J _ y), ← LinearMap.smul_apply, ← e2, LinearMap.add_apply]
        exact A.smul_mem _ (add_mem (jE_mem_jTower hJ hI hE _ p hy)
          (jF_mem_jTower hJ hI _ p (by simpa using hkp) hy))
      · have hj2 := j.2
        have hj : j = ⟨2 * p, by omega⟩ := Fin.ext (show (j : ℕ) = 2 * p by omega)
        rw [hj]
        exact jU_mem_jTower hJ hU p hy
    · have hkp : k < p := by have := j.2; omega
      have hj : j = ⟨2 * k + 1, by omega⟩ := Fin.ext hk
      rw [hj]
      have e2 : jE p J I ⟨k, hkp⟩ - jF p J I ⟨k, hkp⟩ = (2 * I) • J ⟨2 * k + 1, by omega⟩ := by
        rw [jE, jF]
        module
      rw [← inv_smul_smul₀ (mul_ne_zero h2 hI0) (J _ y), ← LinearMap.smul_apply, ← e2,
        LinearMap.sub_apply]
      exact A.smul_mem _ (sub_mem (jE_mem_jTower hJ hI hE _ p hy)
        (jF_mem_jTower hJ hI _ p (by simpa using hkp) hy))
  have htop : A = ⊤ := (hsimple A hJA).resolve_left fun h ↦ hm0 (by
    have hmem := mem_jTower_self (J := J) (I := I) m₀ p
    rw [← hA, h] at hmem
    exact (Submodule.mem_bot K).mp hmem)
  calc Module.finrank K Y = Module.finrank K A := by rw [htop, finrank_top]
    _ ≤ 2 ^ p := finrank_jTower_le m₀ p

end Pairing
