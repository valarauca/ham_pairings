import Clifford.ThreeCycle

/-!
# T2. Edge relations (sketch §4)

`Γ i j = ρ((i j))` on `W`, and `{X, Y} = XY + YX`.

* R1 `Γ_mul_self` : `Γ_e² = I`.
* R2 `Γ_anticomm_of_disjoint` : `{Γ_e, Γ_f} = 0` for disjoint edges.
* R3 `Γ_anticomm_of_adj` : `{Γ_e, Γ_f} = I` for edges sharing one vertex, from T1.
* R4 `Γ_add_Γ_add_Γ` : `Γ_ij + Γ_jk + Γ_ik = 0`.
* `Γ_anticomm` : the uniform form `{Γ_e, Γ_f} = |e ∩ f| I`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In `End_{𝔽₂}(W)` every element is its own negative. -/
theorem end_add_self (x : Module.End F₂ (W V)) : x + x = 0 := by
  rw [← two_smul F₂ x, show (2 : F₂) = 0 by decide, zero_smul]

/-- `Γ_{ij} = ρ((i j))` on `W`. -/
def Γ (i j : V) : Module.End F₂ (W V) :=
  ρW (swap i j)

theorem Γ_comm (i j : V) : Γ i j = Γ j i := by
  rw [Γ, Γ, swap_comm]

/-- R1. -/
theorem Γ_mul_self (i j : V) : Γ i j * Γ i j = 1 := by
  rw [Γ, ← map_mul, swap_mul_self, _root_.map_one]

/-- Disjoint transpositions commute. -/
theorem Γ_mul_comm_of_disjoint {i j k l : V} (h : [i, j, k, l].Nodup) :
    Γ i j * Γ k l = Γ k l * Γ i j := by
  rw [Γ, Γ, ← map_mul, ← map_mul, (Perm.disjoint_swap_swap h).commute.eq]

/-- R2. -/
theorem Γ_anticomm_of_disjoint {i j k l : V} (h : [i, j, k, l].Nodup) :
    Γ i j * Γ k l + Γ k l * Γ i j = 0 := by
  rw [Γ_mul_comm_of_disjoint h, end_add_self]

/-- R3, from T1 applied to `(i j)(j k)`. -/
theorem Γ_anticomm_of_adj {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Γ i j * Γ j k + Γ j k * Γ i j = 1 := by
  have hτ : (swap j i * swap j k).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same hij.symm hjk hik
  have h3 : (swap j i * swap j k) ^ 3 = 1 := by rw [← hτ.orderOf, pow_orderOf_eq_one]
  have hinv : (swap j i * swap j k)⁻¹ = (swap j i * swap j k) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)
  have hT := one_add_ρW_add_sq hτ
  rw [← map_pow, ← hinv, mul_inv_rev, swap_inv, swap_inv] at hT
  rw [Γ, Γ, ← map_mul, ← map_mul, swap_comm i j]
  have h11 : (1 : Module.End F₂ (W V)) + 1 = 0 := end_add_self 1
  calc ρW (swap j i * swap j k) + ρW (swap j k * swap j i)
      = ρW (swap j i * swap j k) + ρW (swap j k * swap j i) + (1 + 1) := by
        rw [h11, add_zero]
    _ = (1 + ρW (swap j i * swap j k) + ρW (swap j k * swap j i)) + 1 := by abel
    _ = 1 := by rw [hT, zero_add]

/-- `Γ_ij Γ_jk Γ_ij = Γ_ik`. -/
theorem Γ_conj {i j k : V} (hjk : j ≠ k) (hik : i ≠ k) : Γ i j * Γ j k * Γ i j = Γ i k := by
  rw [Γ, Γ, Γ, ← map_mul, ← map_mul, swap_comm i j, swap_comm j k,
    swap_mul_swap_mul_swap hjk.symm hik.symm]

/-- R4. -/
theorem Γ_add_Γ_add_Γ {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Γ i j + Γ j k + Γ i k = 0 := by
  have e : Γ i k + Γ j k = Γ i j := by
    calc Γ i k + Γ j k = Γ i j * Γ j k * Γ i j + Γ j k * (Γ i j * Γ i j) := by
          rw [Γ_conj hjk hik, Γ_mul_self, mul_one]
      _ = (Γ i j * Γ j k + Γ j k * Γ i j) * Γ i j := by rw [add_mul, mul_assoc (Γ j k)]
      _ = Γ i j := by rw [Γ_anticomm_of_adj hij hjk hik, one_mul]
  calc Γ i j + Γ j k + Γ i k = Γ i j + (Γ i k + Γ j k) := by abel
    _ = 0 := by rw [e, end_add_self]

/-- `Γ_ik = Γ_ij + Γ_jk`. -/
theorem Γ_eq_add {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Γ i k = Γ i j + Γ j k := by
  have h := Γ_add_Γ_add_Γ hij hjk hik
  calc Γ i k = Γ i j + Γ j k + Γ i k + (Γ i j + Γ j k) := by
        rw [add_assoc (Γ i j + Γ j k), add_comm (Γ i k), ← add_assoc, end_add_self, zero_add]
    _ = Γ i j + Γ j k := by rw [h, zero_add]

/-- The uniform form, `{Γ_e, Γ_f} = |e ∩ f| I`. -/
theorem Γ_anticomm {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    Γ i j * Γ k l + Γ k l * Γ i j = ((({i, j} : Finset V) ∩ {k, l}).card : F₂) • 1 := by
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      rw [end_add_self, Finset.inter_self, Finset.card_pair hij,
        show ((2 : ℕ) : F₂) = 0 by decide, zero_smul]
    · rw [Γ_comm i j, Γ_anticomm_of_adj hij.symm hkl hjl,
        show ({i, j} ∩ {i, l} : Finset V) = {i} by ext x; simp; grind]
      simp
  · by_cases hil : i = l
    · subst hil
      by_cases hjk : j = k
      · subst hjk
        rw [Γ_comm j i, end_add_self, show ({i, j} ∩ {j, i} : Finset V) = {i, j} by
          ext x; simp; grind, Finset.card_pair hij, show ((2 : ℕ) : F₂) = 0 by decide, zero_smul]
      · rw [Γ_comm i j, Γ_comm k i, Γ_anticomm_of_adj hij.symm hik hjk,
          show ({i, j} ∩ {k, i} : Finset V) = {i} by ext x; simp; grind]
        simp
    · by_cases hjk : j = k
      · subst hjk
        rw [Γ_anticomm_of_adj hij hkl hil,
          show ({i, j} ∩ {j, l} : Finset V) = {j} by ext x; simp; grind]
        simp
      · by_cases hjl : j = l
        · subst hjl
          rw [Γ_comm k j, Γ_anticomm_of_adj hij hkl.symm hik,
            show ({i, j} ∩ {k, j} : Finset V) = {j} by ext x; simp; grind]
          simp
        · rw [Γ_anticomm_of_disjoint (by simp [*]),
            show ({i, j} ∩ {k, l} : Finset V) = ∅ by ext x; simp; grind]
          simp

end Pairing.PerfectMatching
