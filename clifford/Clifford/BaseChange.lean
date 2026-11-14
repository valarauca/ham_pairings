import Clifford.Corollaries
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Extension of scalars (COD-105 follow-up, gap 4)

Let `K` be a field of characteristic 2, regarded as an `𝔽₂`-algebra, and let
`ρ_K(σ) = ρ(σ) ⊗ K` act on `K ⊗ W_n`.

* `adjoin_ρK_eq_top` : `ρ_K(K S_{2n}) = End_K(K ⊗ W_n)`.
* `ρK_invariant_eq_bot_or_top` : `K ⊗ W_n` is irreducible.
* `ρK_threeCycle_ne_smul_one` : a three-cycle does not act as a scalar on `K ⊗ W_n`. The proof
  uses that a three-cycle is conjugate to its inverse, so it holds even when `x² + x + 1` splits
  over `K`.
* `minpoly_ρK_threeCycle` : the minimal polynomial of a three-cycle over `K` is `x² + x + 1`.

With `K = F̄₂` these are the facts that `clifford/basic_spin.md` needs.
-/

namespace Pairing.PerfectMatching

open Equiv Polynomial TensorProduct

variable (n : ℕ) (K : Type*) [Field K] [Algebra F₂ K]

/-- `ρ_K(σ) = ρ(σ) ⊗ K`. -/
def ρK (σ : Perm (Fin (2 * n))) : Module.End K (K ⊗[F₂] W (Fin (2 * n))) :=
  (ρW σ).baseChange K

theorem ρK_mul (σ τ : Perm (Fin (2 * n))) : ρK n K (σ * τ) = ρK n K σ * ρK n K τ := by
  rw [ρK, ρK, ρK, map_mul, LinearMap.baseChange_mul]

theorem ρK_one : ρK n K 1 = 1 := by
  rw [ρK, map_one, LinearMap.baseChange_one]

theorem baseChange_mem_adjoin (hn : 1 ≤ n) (f : Module.End F₂ (W (Fin (2 * n)))) :
    f.baseChange K ∈ Algebra.adjoin K (Set.range (ρK n K)) := by
  have hf : f ∈ Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) := by
    rw [adjoin_ρW_eq_top n hn]
    exact Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨σ, rfl⟩ := hg
    exact Algebra.subset_adjoin ⟨σ, rfl⟩
  | algebraMap c =>
    rcases f2_cases c with rfl | rfl
    · rw [map_zero, LinearMap.baseChange_zero]
      exact zero_mem _
    · rw [map_one, LinearMap.baseChange_one]
      exact one_mem _
  | add f g _ _ hf hg =>
    rw [LinearMap.baseChange_add]
    exact add_mem hf hg
  | mul f g _ _ hf hg =>
    rw [LinearMap.baseChange_mul]
    exact mul_mem hf hg

/-- `ρ_K(K S_{2n}) = End_K(K ⊗ W_n)`. -/
theorem adjoin_ρK_eq_top (hn : 1 ≤ n) : Algebra.adjoin K (Set.range (ρK n K)) = ⊤ := by
  set b := (wBasis n hn).baseChange K with hb
  rw [eq_top_iff]
  intro g _
  have hunit : ∀ i j k, (((wBasis n hn).coord j).smulRight (wBasis n hn i)).baseChange K (b k) =
      if j = k then b i else 0 := by
    intro i j k
    rw [hb, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Module.Basis.baseChange_apply]
    by_cases hjk : j = k
    · rw [ite_eq_left hjk.symm, ite_eq_left hjk, one_smul]
    · rw [ite_eq_right (Ne.symm hjk), ite_eq_right hjk, zero_smul, tmul_zero]
  have hg : g = ∑ i, ∑ j, b.repr (g (b j)) i •
      (((wBasis n hn).coord j).smulRight (wBasis n hn i)).baseChange K := by
    refine b.ext fun k ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hunit, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (b.sum_repr (g (b k))).symm
  rw [hg]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.sum_mem _ fun j _ ↦
    Subalgebra.smul_mem _ (baseChange_mem_adjoin n K hn _) _

theorem nontrivial_baseChange (hn : 1 ≤ n) : Nontrivial (K ⊗[F₂] W (Fin (2 * n))) :=
  Module.nontrivial_of_finrank_pos (R := K)
    (by rw [Module.finrank_eq_card_basis ((wBasis n hn).baseChange K)]; simp)

/-- `K ⊗ W_n` is irreducible. -/
theorem ρK_invariant_eq_bot_or_top (hn : 1 ≤ n) (M : Submodule K (K ⊗[F₂] W (Fin (2 * n))))
    (hM : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ M, ρK n K σ x ∈ M) : M = ⊥ ∨ M = ⊤ := by
  have hall : ∀ f : Module.End K (K ⊗[F₂] W (Fin (2 * n))), ∀ x ∈ M, f x ∈ M := by
    intro f
    have hf : f ∈ Algebra.adjoin K (Set.range (ρK n K)) := by
      rw [adjoin_ρK_eq_top n K hn]
      exact Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨σ, rfl⟩ := hg
      exact hM σ
    | algebraMap c =>
      intro x hx
      rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      exact M.smul_mem c hx
    | add f g _ _ hf hg =>
      intro x hx
      rw [LinearMap.add_apply]
      exact add_mem (hf x hx) (hg x hx)
    | mul f g _ _ hf hg =>
      intro x hx
      rw [Module.End.mul_apply]
      exact hf _ (hg x hx)
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (K ⊗[F₂] W (Fin (2 * n))), φ m ≠ 0 := by
    by_contra! h
    exact hm0 ((Module.forall_dual_apply_eq_zero_iff K m).mp h)
  rw [eq_top_iff]
  intro x _
  have hx := hall ((φ m)⁻¹ • φ.smulRight x) m hm
  rwa [LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ,
    one_smul] at hx

theorem two_eq_zero_K : (2 : K) = 0 := by
  rw [← map_ofNat (algebraMap F₂ K) 2, show (2 : F₂) = 0 by decide, map_zero]

theorem ρK_threeCycle_sq_add {τ : Perm (Fin (2 * n))} (hτ : τ.IsThreeCycle) :
    ρK n K τ ^ 2 + ρK n K τ + 1 = 0 := by
  have h := congrArg (fun f ↦ LinearMap.baseChange K f) (ρW_threeCycle_sq_add hτ)
  simp only [ρK]
  simpa only [LinearMap.baseChange_add, LinearMap.baseChange_pow, LinearMap.baseChange_one,
    LinearMap.baseChange_zero] using h

/-- A three-cycle is not a scalar on `K ⊗ W_n`. -/
theorem ρK_threeCycle_ne_smul_one (hn : 1 ≤ n) {τ : Perm (Fin (2 * n))} (hτ : τ.IsThreeCycle)
    (c : K) : ρK n K τ ≠ c • 1 := by
  have := nontrivial_baseChange n K hn
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr (Perm.cycleType_inv τ).symm)
  have h3 : τ ^ 3 = 1 := by rw [← hτ.orderOf, pow_orderOf_eq_one]
  have hinv : τ⁻¹ = τ * τ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← pow_succ']; exact h3)
  have hsq : ρK n K τ * ρK n K τ = c • 1 := by
    have hconj : ρK n K τ⁻¹ = ρK n K g * ρK n K τ * ρK n K g⁻¹ := by
      rw [← hg, ρK_mul, ρK_mul]
    rw [← ρK_mul, ← hinv, hconj, h, mul_smul_comm, mul_one, smul_mul_assoc, ← ρK_mul,
      mul_inv_cancel, ρK_one]
  rw [h, smul_mul_smul_comm, one_mul] at hsq
  have hcc : c * c = c := by
    by_contra hne
    have : (c * c - c) • (1 : Module.End K (K ⊗[F₂] W (Fin (2 * n)))) = 0 := by
      rw [sub_smul, hsq, sub_self]
    exact hne (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right one_ne_zero))
  have hc : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hrel := ρK_threeCycle_sq_add n K hτ
  rw [h, pow_two, smul_mul_smul_comm, one_mul] at hrel
  rcases hc with rfl | rfl
  · simp at hrel
  · rw [mul_one, one_smul, ← two_smul K (1 : Module.End K _), two_eq_zero_K, zero_smul,
      zero_add] at hrel
    exact one_ne_zero hrel

/-- The minimal polynomial of a three-cycle over `K` is `x² + x + 1`. -/
theorem minpoly_ρK_threeCycle (hn : 1 ≤ n) {τ : Perm (Fin (2 * n))} (hτ : τ.IsThreeCycle) :
    minpoly K (ρK n K τ) = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have := nontrivial_baseChange n K hn
  have : Module.Finite K (K ⊗[F₂] W (Fin (2 * n))) :=
    Module.Finite.of_basis ((wBasis n hn).baseChange K)
  have hint : IsIntegral K (ρK n K τ) := IsIntegral.of_finite K _
  have hmon : (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]).Monic := by monicity!
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have haeval : Polynomial.aeval (ρK n K τ) (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]) = 0 := by
    simp [ρK_threeCycle_sq_add n K hτ]
  have hdvd := minpoly.dvd K (ρK n K τ) haeval
  have hpos := minpoly.natDegree_pos hint
  have hle : (minpoly K (ρK n K τ)).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd hdvd hmon.ne_zero
    omega
  have hne1 : (minpoly K (ρK n K τ)).natDegree ≠ 1 := by
    intro h1
    have hm := minpoly.monic hint
    have hform := hm.eq_X_add_C h1
    have h0 := minpoly.aeval K (ρK n K τ)
    rw [hform] at h0
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      at h0
    exact ρK_threeCycle_ne_smul_one n K hn hτ (-(minpoly K (ρK n K τ)).coeff 0)
      (by rw [neg_smul, eq_neg_iff_add_eq_zero, h0])
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd (by omega)).symm

end Pairing.PerfectMatching
