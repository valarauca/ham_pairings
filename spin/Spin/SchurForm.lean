import Spin.Char2Modules
import Spin.DoubleCover
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.NoncommRing

/-!
# M2. Schur's form and the two Clifford realizations of `S̃_m`

* `schurQ R m` on `R^m` is `Q(x) = -∑ x_j² + ∑ x_j x_{j+1}`, the negated `A_m` root form. It is
  defined over any commutative ring. `schurQ_single` gives `Q(b_j) = -1`, and
  `polar_schurQ_single` gives the integer Gram matrix `schurG`.
* `Stilde.isData_clifford` : elements with `a² = -1`, adjacent anticommutator `1` and distant
  anticommutator `0` satisfy the relations of `S̃_m` with `z = -1`.
* `schurHom R m : S̃_m → Cl(schurQ R (m-1))ˣ`, `t_j ↦ ι(b_j)`, `z ↦ -1`. This is Schur's
  realization.
* `stildeCl n : S̃_{2n} → Cl(U_n, q)ˣ`, `t_j ↦ ι(v_{j,j+1})`, its characteristic 2 analogue.
* `cliffordRep_stildeCl` : on `W_n` it is `ρ ∘ toPerm`.
-/

namespace Pairing

open Equiv

section Form

variable (R : Type*) [CommRing R] (m : ℕ)

/-- `-1` on the diagonal and `1` just above it. -/
def schurA : Matrix (Fin m) (Fin m) R :=
  fun s t ↦ if s = t then -1 else if (t : ℕ) = s + 1 then 1 else 0

/-- Schur's form `Q(x) = -∑ x_j² + ∑ x_j x_{j+1}`. -/
def schurQ : QuadraticForm R (Fin m → R) :=
  (Matrix.toBilin' (schurA R m)).toQuadraticMap

/-- The Gram matrix of the polar form of `schurQ`. -/
def schurG (s t : Fin m) : ℤ :=
  if s = t then -2 else if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0

variable {R m}

theorem schurQ_single (j : Fin m) : schurQ R m (Pi.single j 1) = -1 := by
  rw [schurQ, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_single]
  simp [schurA]

theorem polar_schurQ_single (s t : Fin m) :
    QuadraticMap.polar (schurQ R m) (Pi.single s 1) (Pi.single t 1) = (schurG m s t : R) := by
  rw [schurQ, LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_single,
    Matrix.toBilin'_single, schurA, schurA, schurG]
  by_cases hst : s = t
  · subst hst
    simp only [↓reduceIte]
    push_cast
    ring
  · have hts : t ≠ s := Ne.symm hst
    simp only [hst, hts, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | simp

end Form

namespace Stilde

/-- `a` with `a² = -1` as a unit, with inverse `-a`. -/
def unitOfSqNegOne {A : Type*} [Ring A] (a : A) (ha : a * a = -1) : Aˣ :=
  ⟨a, -a, by rw [mul_neg, ha, neg_neg], by rw [neg_mul, ha, neg_neg]⟩

theorem braid_of_anticomm {A : Type*} [Ring A] {a b : A} (ha : a * a = -1) (hb : b * b = -1)
    (h : a * b + b * a = 1) : (a * b) ^ 3 = -1 := by
  have hba : b * a = 1 - a * b := eq_sub_of_add_eq' h
  have hx2 : a * b * (a * b) = a * b - 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by noncomm_ring
      _ = a * b - a * a * (b * b) := by rw [hba]; noncomm_ring
      _ = a * b - 1 := by rw [ha, hb]; noncomm_ring
  calc (a * b) ^ 3 = a * b * (a * b) * (a * b) := by noncomm_ring
    _ = (a * b - 1) * (a * b) := by rw [hx2]
    _ = a * b * (a * b) - a * b := by noncomm_ring
    _ = -1 := by rw [hx2]; noncomm_ring

theorem far_of_anticomm {A : Type*} [Ring A] {a b : A} (ha : a * a = -1) (hb : b * b = -1)
    (h : a * b + b * a = 0) : (a * b) ^ 2 = -1 := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right h
  calc (a * b) ^ 2 = a * (b * a) * b := by noncomm_ring
    _ = -(a * a * (b * b)) := by rw [hba]; noncomm_ring
    _ = -1 := by rw [ha, hb]; noncomm_ring

/-- Elements with `a² = -1`, adjacent anticommutator `1` and distant anticommutator `0` satisfy
the relations of `S̃_m` with `z = -1`. -/
theorem isData_clifford {A : Type*} [Ring A] {k : ℕ} (T : Fin k → A) (h1 : ∀ j, T j * T j = -1)
    (h2 : ∀ i j : Fin k, (j : ℕ) = i + 1 → T i * T j + T j * T i = 1)
    (h3 : ∀ i j : Fin k, (i : ℕ) + 2 ≤ j → T i * T j + T j * T i = 0) :
    IsData k (-1 : Aˣ) (fun j ↦ unitOfSqNegOne (T j) (h1 j)) where
  z_sq := by rw [neg_one_sq]
  z_comm j := by rw [neg_one_mul, mul_neg_one]
  t_sq j := Units.ext (by simp [unitOfSqNegOne, pow_two, h1 j])
  braid i j hij := Units.ext (by
    simp [unitOfSqNegOne, braid_of_anticomm (h1 i) (h1 j) (h2 i j hij)])
  far i j hij := Units.ext (by
    simp [unitOfSqNegOne, far_of_anticomm (h1 i) (h1 j) (h3 i j hij)])

end Stilde

section Schur

variable (R : Type*) [CommRing R] (m : ℕ)

/-- `T_j = ι(b_j)` in `Cl(schurQ)`. -/
def schurT (j : Fin m) : CliffordAlgebra (schurQ R m) :=
  CliffordAlgebra.ι _ (Pi.single j 1)

variable {R m}

theorem schurT_sq (j : Fin m) : schurT R m j * schurT R m j = -1 := by
  rw [schurT, CliffordAlgebra.ι_sq_scalar, schurQ_single, map_neg, map_one]

theorem schurT_anticomm (i j : Fin m) :
    schurT R m i * schurT R m j + schurT R m j * schurT R m i =
      (schurG m i j : CliffordAlgebra _) := by
  rw [schurT, schurT, CliffordAlgebra.ι_mul_ι_add_swap, polar_schurQ_single, map_intCast]

theorem schurG_adj {i j : Fin m} (h : (j : ℕ) = i + 1) : schurG m i j = 1 := by
  have hne : i ≠ j := fun e ↦ by rw [e] at h; omega
  simp [schurG, hne, h]

theorem schurG_far {i j : Fin m} (h : (i : ℕ) + 2 ≤ j) : schurG m i j = 0 := by
  have hne : i ≠ j := fun e ↦ by rw [e] at h; omega
  simp only [schurG, hne, ↓reduceIte]
  rw [ite_eq_right_iff]
  intro h'
  omega

variable (R m)

/-- Schur's realization `S̃_m → Cl(schurQ R (m-1))ˣ`, `t_j ↦ ι(b_j)`, `z ↦ -1`. -/
def schurHom : Stilde m →* (CliffordAlgebra (schurQ R (m - 1)))ˣ :=
  Stilde.lift (Stilde.isData_clifford (schurT R (m - 1)) schurT_sq
    (fun i j h ↦ by rw [schurT_anticomm, schurG_adj h, Int.cast_one])
    (fun i j h ↦ by rw [schurT_anticomm, schurG_far h, Int.cast_zero]))

theorem schurHom_t (j : Fin (m - 1)) :
    ((schurHom R m (Stilde.t j) : (CliffordAlgebra (schurQ R (m - 1)))ˣ) :
      CliffordAlgebra (schurQ R (m - 1))) = schurT R (m - 1) j := by
  rw [schurHom, Stilde.lift_t]
  rfl

theorem schurHom_z :
    ((schurHom R m (Stilde.z m) : (CliffordAlgebra (schurQ R (m - 1)))ˣ) :
      CliffordAlgebra (schurQ R (m - 1))) = -1 := by
  rw [schurHom, Stilde.lift_z]
  rfl

end Schur

end Pairing
