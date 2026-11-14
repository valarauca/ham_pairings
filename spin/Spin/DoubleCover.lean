import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# M2. Schur's double cover `S̃_m`

`S̃_m` is presented on `z` and `t_0, …, t_{m-2}` by `z² = 1`, `z` central, `t_j² = z`,
`(t_j t_{j+1})³ = z` and `(t_i t_j)² = z` for `j ≥ i + 2`. These are Maas's relations.

* `Stilde.lift` : a hom out of `S̃_m` from elements satisfying the relations.
* `Stilde.toPerm` : the projection `S̃_m → S_m`, `t_j ↦ (j, j+1)`, `z ↦ 1`.
-/

namespace Pairing

/-- The relators of `S̃_m` on `z = none` and `t_j = some j`, for `j < k = m - 1`. -/
def stildeRels (k : ℕ) : Set (FreeGroup (Option (Fin k))) :=
  {FreeGroup.of none ^ 2} ∪
    Set.range (fun j : Fin k ↦ FreeGroup.of none * FreeGroup.of (some j) *
      (FreeGroup.of none)⁻¹ * (FreeGroup.of (some j))⁻¹) ∪
    Set.range (fun j : Fin k ↦ FreeGroup.of (some j) ^ 2 * (FreeGroup.of none)⁻¹) ∪
    {r | ∃ i j : Fin k, (j : ℕ) = i + 1 ∧
      r = (FreeGroup.of (some i) * FreeGroup.of (some j)) ^ 3 * (FreeGroup.of none)⁻¹} ∪
    {r | ∃ i j : Fin k, (i : ℕ) + 2 ≤ j ∧
      r = (FreeGroup.of (some i) * FreeGroup.of (some j)) ^ 2 * (FreeGroup.of none)⁻¹}

/-- Schur's double cover `S̃_m`. -/
abbrev Stilde (m : ℕ) : Type :=
  PresentedGroup (stildeRels (m - 1))

namespace Stilde

variable {G : Type*} [Group G]

/-- Elements `z` and `t_j` of `G` satisfying the relations of `S̃_m`. -/
structure IsData (k : ℕ) (z : G) (t : Fin k → G) : Prop where
  z_sq : z ^ 2 = 1
  z_comm : ∀ j, z * t j = t j * z
  t_sq : ∀ j, t j ^ 2 = z
  braid : ∀ i j : Fin k, (j : ℕ) = i + 1 → (t i * t j) ^ 3 = z
  far : ∀ i j : Fin k, (i : ℕ) + 2 ≤ j → (t i * t j) ^ 2 = z

/-- The hom `S̃_m → G` with `z ↦ z` and `t_j ↦ t_j`. -/
def lift {m : ℕ} {z : G} {t : Fin (m - 1) → G} (h : IsData (m - 1) z t) : Stilde m →* G :=
  PresentedGroup.toGroup (f := fun o ↦ o.elim z t) (by
    intro r hr
    simp only [stildeRels, Set.mem_union, Set.mem_singleton_iff, Set.mem_range,
      Set.mem_ofPred_eq] at hr
    rcases hr with ((((rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨i, j, hij, rfl⟩) | ⟨i, j, hij, rfl⟩)
    · simp [h.z_sq]
    · simp [h.z_comm j]
    · simp [h.t_sq j]
    · simp [h.braid i j hij]
    · simp [h.far i j hij])

/-- The generator `z`. -/
def z (m : ℕ) : Stilde m :=
  PresentedGroup.of none

/-- The generator `t_j`. -/
def t {m : ℕ} (j : Fin (m - 1)) : Stilde m :=
  PresentedGroup.of (some j)

theorem lift_z {m : ℕ} {z : G} {t : Fin (m - 1) → G} (h : IsData (m - 1) z t) :
    lift h (Stilde.z m) = z :=
  PresentedGroup.toGroup.of _

theorem lift_t {m : ℕ} {z : G} {t : Fin (m - 1) → G} (h : IsData (m - 1) z t) (j : Fin (m - 1)) :
    lift h (Stilde.t j) = t j :=
  PresentedGroup.toGroup.of _

/-- Two homs out of `S̃_m` agreeing on the generators are equal. -/
theorem hom_ext {m : ℕ} {f g : Stilde m →* G} (hz : f (Stilde.z m) = g (Stilde.z m))
    (ht : ∀ j, f (Stilde.t j) = g (Stilde.t j)) : f = g :=
  PresentedGroup.ext fun o ↦ by
    cases o with
    | none => exact hz
    | some j => exact ht j

open Equiv

/-- The transposition `(j, j+1)` of `Fin m`. -/
def adjSwap {m : ℕ} (j : Fin (m - 1)) : Perm (Fin m) :=
  swap ⟨j, by omega⟩ ⟨j + 1, by omega⟩

theorem adjSwap_sq {m : ℕ} (j : Fin (m - 1)) : adjSwap j ^ 2 = 1 := by
  rw [adjSwap, pow_two, swap_mul_self]

theorem isData_perm (m : ℕ) : IsData (m - 1) (1 : Perm (Fin m)) adjSwap where
  z_sq := one_pow 2
  z_comm j := by rw [one_mul, mul_one]
  t_sq j := adjSwap_sq j
  braid i j hij := by
    have e1 : (⟨i + 1, by omega⟩ : Fin m) = ⟨j, by omega⟩ := Fin.ext hij.symm
    have e : adjSwap (m := m) i = swap (⟨j, by omega⟩ : Fin m) ⟨i, by omega⟩ := by
      rw [adjSwap, swap_comm, e1]
    rw [e, adjSwap]
    have h3 := Perm.isThreeCycle_swap_mul_swap_same (α := Fin m) (a := ⟨j, by omega⟩)
      (b := ⟨i, by omega⟩) (c := ⟨j + 1, by omega⟩) (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp; omega))
    rw [← h3.orderOf, pow_orderOf_eq_one]
  far i j hij := by
    have hc : Commute (adjSwap (m := m) i) (adjSwap j) := by
      refine (Perm.disjoint_swap_swap ?_).commute
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true, Fin.ext_iff]
      omega
    rw [pow_two, mul_assoc, ← mul_assoc (adjSwap j), ← hc.eq, mul_assoc, ← mul_assoc, ← pow_two,
      ← pow_two, adjSwap_sq, adjSwap_sq, mul_one]

/-- The projection `S̃_m → S_m`. -/
def toPerm (m : ℕ) : Stilde m →* Perm (Fin m) :=
  lift (isData_perm m)

theorem toPerm_t {m : ℕ} (j : Fin (m - 1)) : toPerm m (Stilde.t j) = adjSwap j :=
  lift_t _ j

theorem toPerm_z (m : ℕ) : toPerm m (Stilde.z m) = 1 :=
  lift_z _

end Stilde

end Pairing
