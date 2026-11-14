import Clifford.Corollaries

/-!
# C4, partial (sketch §7)

* `cliffordRep_surjective` : the Clifford action `Cl(U_n, q) → End(W_n)` is onto.
* `ι_ones_commute`, `ι_ones_sq` : `ι(𝟙)` commutes with every `ι(x)`, and `ι(𝟙)² = n`.
* `cliffordRep_ι_ones` : `Γ(𝟙) = (n mod 2) I`.

The full decomposition `Cl(U_n, q) ≅ M_{2^(n-1)}(𝔽₂) ⊗ 𝔽₂[z]/(z² + n)`, and with it the
uniqueness of the simple module, needs `dim Cl(V, q) = 2^(dim V)` in characteristic 2. Mathlib
does not provide that, so it is not formalized here. Nothing in T3 or T4 depends on it.
-/

namespace Pairing.PerfectMatching

open Equiv

theorem add_self_F₂ {M : Type*} [AddCommGroup M] [Module F₂ M] (x : M) : x + x = 0 := by
  rw [← two_smul F₂ x, show (2 : F₂) = 0 by decide, zero_smul]

variable (n : ℕ)

/-- The Clifford action is onto `End(W_n)`. -/
theorem cliffordRep_surjective (hn : 1 ≤ n) (o : Fin (2 * n)) :
    Function.Surjective (cliffordRep o) := by
  have hρ : ∀ σ : Perm (Fin (2 * n)), ρW σ ∈ (cliffordRep o).range := by
    intro σ
    have hσ : σ ∈ Submonoid.closure {τ : Perm (Fin (2 * n)) | τ.IsSwap} := by
      rw [Perm.mclosure_isSwap]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem τ hτ =>
      obtain ⟨i, j, hij, rfl⟩ := hτ
      exact ⟨_, cliffordRep_ι_v o hij⟩
    | one =>
      rw [map_one]
      exact one_mem _
    | mul τ τ' _ _ h h' =>
      rw [map_mul]
      exact mul_mem h h'
  have htop : (cliffordRep o).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_ρW_eq_top n hn, Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    exact hρ σ
  intro f
  have hf : f ∈ (cliffordRep o).range := htop ▸ Algebra.mem_top
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, hx⟩

/-- `𝟙 ∈ U_n` as an element of the quadratic space. -/
def onesU : U (Fin (2 * n)) :=
  ⟨ones n, ones_mem n⟩

/-- `ι(𝟙)` commutes with every generator, because `b(𝟙, ·) = 0` on `U_n`. -/
theorem ι_ones_commute (m : U (Fin (2 * n))) :
    Commute (CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n))
      (CliffordAlgebra.ι (qForm (Fin (2 * n))) m) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := qForm (Fin (2 * n))) (onesU n) m
  have hpolar : QuadraticMap.polar (qForm (Fin (2 * n))) (onesU n) m = 0 := by
    rw [polar_qForm]
    have hm := m.2
    rw [mem_U] at hm
    simpa [dot, onesU, ones] using hm
  rw [hpolar, map_zero] at h
  calc CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) * CliffordAlgebra.ι _ m
      = CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) * CliffordAlgebra.ι _ m +
        (CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) * CliffordAlgebra.ι _ m +
          CliffordAlgebra.ι _ m * CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n)) := by
        rw [h, add_zero]
    _ = CliffordAlgebra.ι _ m * CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) := by
        rw [← add_assoc, add_self_F₂, zero_add]

/-- `ι(𝟙)² = q(𝟙) = n`. -/
theorem ι_ones_sq :
    CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) *
        CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n) =
      algebraMap F₂ _ (n : F₂) := by
  rw [CliffordAlgebra.ι_sq_scalar, qForm_apply]
  exact congrArg _ (qfun_ones n)

/-- `Γ(𝟙) = (n mod 2) I`. -/
theorem cliffordRep_ι_ones (hn : 1 ≤ n) (o : Fin (2 * n)) :
    cliffordRep o (CliffordAlgebra.ι (qForm (Fin (2 * n))) (onesU n)) = (n : F₂) • 1 := by
  rw [cliffordRep_ι, ΓU_apply, ← sum_Γ_matching n hn (P0 n)]
  change gammaL o (ones n) = _
  rw [ones_eq_sum n (P0 n), map_sum]
  exact Finset.sum_congr rfl fun v _ ↦ gammaL_v o ((P0 n).mate_ne v).symm

end Pairing.PerfectMatching
