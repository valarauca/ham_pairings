import Clifford.Descent
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# T3. The Clifford action (sketch §5)

* `gammaL_anticomm` : `{Γ(x), Γ(y)} = b(x, y) I` on `U` (polarization).
* `gammaL_sq` : `Γ(x)² = q(x) I` on `U`.
* `ΓU_anticomm`, `ΓU_sq` : the same identities for `Γ : U_n → End(W)` with `b = polar q`.
* `cliffordRep o : Cl(U_n, q) →ₐ End(W)`, the Clifford action, with `cliffordRep_ι_v` sending
  `ι(v_e)` to `Γ_e`.
* `ρW_conj_Γ`, `ρW_conj_gammaL` : `ρ(σ) Γ(x) ρ(σ)⁻¹ = Γ(σ x)`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem dot_add_right (x y z : V → F₂) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

omit [DecidableEq V] in
theorem dot_smul_right (c : F₂) (x y : V → F₂) : dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm]

omit [DecidableEq V] in
theorem dot_zero_right (x : V → F₂) : dot x 0 = 0 := by
  simp [dot]

omit [DecidableEq V] in
theorem qfun_smul (c : F₂) (x : V → F₂) : qfun (c • x) = c * c * qfun x := by
  rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl
  · simp [qfun_zero]
  · simp

/-- `{G_i, G_j} = b(v_{oi}, v_{oj}) I`. -/
theorem G_anticomm (o i j : V) :
    G o i * G o j + G o j * G o i = dot (v o i) (v o j) • 1 := by
  by_cases hi : i = o
  · subst hi
    simp [G, v_self, dot]
  by_cases hj : j = o
  · subst hj
    simp [G, v_self, dot]
  simp only [G, hi, hj, ↓reduceIte]
  rw [Γ_anticomm (Ne.symm hi) (Ne.symm hj), dot_v (Ne.symm hi) (Ne.symm hj)]

private theorem anticomm_gen (o i : V) {y : V → F₂} (hy : y ∈ Submodule.span F₂ (Set.range (v o))) :
    G o i * gammaL o y + gammaL o y * G o i = dot (v o i) y • 1 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [gammaL_v_base]
    exact G_anticomm o i j
  | zero => simp [dot_zero_right]
  | add y z _ _ ihy ihz =>
    calc G o i * gammaL o (y + z) + gammaL o (y + z) * G o i
        = (G o i * gammaL o y + gammaL o y * G o i) +
          (G o i * gammaL o z + gammaL o z * G o i) := by
          rw [map_add]
          noncomm_ring
      _ = dot (v o i) (y + z) • 1 := by rw [ihy, ihz, dot_add_right, add_smul]
  | smul c y _ ih =>
    rw [map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add, ih, dot_smul_right, mul_smul]

/-- Polarization, `{Γ(x), Γ(y)} = b(x, y) I` on `U`. -/
theorem gammaL_anticomm (o : V) {x y : V → F₂} (hx : x ∈ U V) (hy : y ∈ U V) :
    gammaL o x * gammaL o y + gammaL o y * gammaL o x = dot x y • 1 := by
  rw [U_eq_span o] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [gammaL_v_base]
    exact anticomm_gen o i hy
  | zero => simp [dot]
  | add x z _ _ ihx ihz =>
    calc gammaL o (x + z) * gammaL o y + gammaL o y * gammaL o (x + z)
        = (gammaL o x * gammaL o y + gammaL o y * gammaL o x) +
          (gammaL o z * gammaL o y + gammaL o y * gammaL o z) := by
          rw [map_add]
          noncomm_ring
      _ = dot (x + z) y • 1 := by
          rw [ihx, ihz, dot_comm (x + z), dot_add_right, dot_comm y, dot_comm y, add_smul]
  | smul c x _ ih =>
    rw [map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add, ih, dot_comm (c • x),
      dot_smul_right, dot_comm y, mul_smul]

/-- `Γ(x)² = q(x) I` on `U`. -/
theorem gammaL_sq (o : V) {x : V → F₂} (hx : x ∈ U V) : gammaL o x * gammaL o x = qfun x • 1 := by
  have hx' := hx
  rw [U_eq_span o] at hx'
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [gammaL_v_base]
    by_cases hj : j = o
    · subst hj
      simp [G, v_self, qfun_zero]
    · simp only [G, hj, ↓reduceIte]
      rw [Γ_mul_self, qfun_v (Ne.symm hj), one_smul]
  | zero => simp [qfun_zero]
  | add y z hy hz ihy ihz =>
    have hyU : y ∈ U V := (U_eq_span o) ▸ hy
    have hzU : z ∈ U V := (U_eq_span o) ▸ hz
    calc gammaL o (y + z) * gammaL o (y + z)
        = gammaL o y * gammaL o y + gammaL o z * gammaL o z +
          (gammaL o y * gammaL o z + gammaL o z * gammaL o y) := by
          rw [map_add]
          noncomm_ring
      _ = qfun (y + z) • 1 := by
          rw [ihy hyU, ihz hzU, gammaL_anticomm o hyU hzU, qfun_add hyU hzU, add_smul, add_smul]
  | smul c y hy ih =>
    have hyU : y ∈ U V := (U_eq_span o) ▸ hy
    rw [map_smul, smul_mul_smul_comm, ih hyU, qfun_smul, smul_smul]

/-- `{Γ(x), Γ(y)} = polar q (x, y) I`. -/
theorem ΓU_anticomm (o : V) (x y : U V) :
    ΓU o x * ΓU o y + ΓU o y * ΓU o x = QuadraticMap.polar (qForm V) x y • 1 := by
  rw [polar_qForm, ΓU_apply, ΓU_apply]
  exact gammaL_anticomm o x.2 y.2

/-- `Γ(x)² = q(x) I`. -/
theorem ΓU_sq (o : V) (x : U V) : ΓU o x * ΓU o x = qForm V x • 1 := by
  rw [qForm_apply, ΓU_apply]
  exact gammaL_sq o x.2

/-- T3. The Clifford action `Cl(U_n, q) → End(W)`. -/
def cliffordRep (o : V) : CliffordAlgebra (qForm V) →ₐ[F₂] Module.End F₂ (W V) :=
  CliffordAlgebra.lift (qForm V) ⟨ΓU o, fun m ↦ by rw [ΓU_sq, Algebra.algebraMap_eq_smul_one]⟩

theorem cliffordRep_ι (o : V) (m : U V) :
    cliffordRep o (CliffordAlgebra.ι (qForm V) m) = ΓU o m :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- `ι(v_e) ↦ Γ_e`. -/
theorem cliffordRep_ι_v (o : V) {i j : V} (hij : i ≠ j) :
    cliffordRep o (CliffordAlgebra.ι (qForm V) ⟨v i j, v_mem i j⟩) = Γ i j := by
  rw [cliffordRep_ι, ΓU_apply]
  exact gammaL_v o hij

/-- `ρ(σ) Γ_{ij} ρ(σ)⁻¹ = Γ_{σi σj}`. -/
theorem ρW_conj_Γ (σ : Perm V) (i j : V) : ρW σ * Γ i j * ρW σ⁻¹ = Γ (σ i) (σ j) := by
  rw [Γ, Γ, ← map_mul, ← map_mul, swap_apply_apply]

omit [Fintype V] in
theorem v_comp_inv (σ : Perm V) (i j : V) : (fun k ↦ v i j (σ⁻¹ k)) = v (σ i) (σ j) := by
  funext k
  simp only [v, Pi.add_apply, Pi.single_apply, Perm.inv_eq_iff_eq]

/-- Equivariance, `ρ(σ) Γ(x) ρ(σ)⁻¹ = Γ(σ x)`. -/
theorem ρW_conj_gammaL (o : V) (σ : Perm V) {x : V → F₂} (hx : x ∈ U V) :
    ρW σ * gammaL o x * ρW σ⁻¹ = gammaL o (fun k ↦ x (σ⁻¹ k)) := by
  rw [U_eq_span o] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [v_comp_inv]
    by_cases hj : j = o
    · subst hj
      rw [v_self, v_self, map_zero, mul_zero, zero_mul]
    · rw [gammaL_v o (Ne.symm hj), gammaL_v o (σ.injective.ne (Ne.symm hj)), ρW_conj_Γ]
  | zero =>
    rw [map_zero, mul_zero, zero_mul]
    exact (map_zero _).symm
  | add y z _ _ ihy ihz =>
    rw [map_add, mul_add, add_mul, ihy, ihz, ← map_add]
    rfl
  | smul c y _ ih =>
    rw [map_smul, mul_smul_comm, smul_mul_assoc, ih, ← map_smul]
    rfl

end Pairing.PerfectMatching
