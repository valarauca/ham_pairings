import Clifford.Irreducible
import Clifford.Action
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Corollaries C3 and C5 (sketch §7)

**C5 / COD-105.** For every three-cycle `τ`:
* `ρW_threeCycle_sq_add` : `ρ(τ)² + ρ(τ) + 1 = 0`.
* `minpoly_ρW_threeCycle` : the minimal polynomial of `ρ(τ)` is exactly `x² + x + 1`.
* `ρW_threeCycle_ne_smul_one` : `ρ(τ)` is not a scalar.
* `eq_zero_of_ρW_threeCycle_fixed` and `not_isNilpotent_ρW_threeCycle_sub_one` : `ρ(τ)` has no
  fixed vector, so it is not unipotent. For `2n = 4` this is the step the archive only checked
  directly.

`W_n` is absolutely irreducible (`adjoin_ρW_eq_top`), so it has one composition factor, and the
facts above hold on that factor.

**C3.** `sum_Γ_matching` : `∑_{e ∈ M} Γ_e = (n mod 2) I` for every perfect matching `M`.
-/

namespace Pairing.PerfectMatching

open Equiv Polynomial

theorem f2_cases (c : F₂) : c = 0 ∨ c = 1 := by
  revert c
  decide

section ThreeCycle

variable {V : Type*} [Fintype V] [DecidableEq V] {τ : Perm V}

theorem ρW_threeCycle_sq_add (hτ : τ.IsThreeCycle) : ρW τ ^ 2 + ρW τ + 1 = 0 := by
  rw [← one_add_ρW_add_sq hτ]
  abel

theorem ρW_threeCycle_pow_three (hτ : τ.IsThreeCycle) : ρW τ ^ 3 = 1 := by
  rw [← map_pow, ← hτ.orderOf, pow_orderOf_eq_one, map_one]

/-- A three-cycle fixes no nonzero vector of `W`. -/
theorem eq_zero_of_ρW_threeCycle_fixed (hτ : τ.IsThreeCycle) {x : W V} (hx : ρW τ x = x) :
    x = 0 := by
  have h := congrArg (fun T : Module.End F₂ (W V) ↦ T x) (one_add_ρW_add_sq hτ)
  simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, hx,
    LinearMap.zero_apply] at h
  rwa [W_add_self, zero_add] at h

/-- `ρ(τ) - 1` is not nilpotent, so `ρ(τ)` is not unipotent. -/
theorem not_isNilpotent_ρW_threeCycle_sub_one [Nontrivial (W V)] (hτ : τ.IsThreeCycle) :
    ¬IsNilpotent (ρW τ - 1) := by
  rintro ⟨m, hm⟩
  have hneg : (-1 : Module.End F₂ (W V)) = 1 := neg_eq_of_add_eq_zero_left (end_add_self 1)
  have hsub : ρW τ - 1 = ρW τ + 1 := by rw [sub_eq_add_neg, hneg]
  have hsq : (ρW τ + 1) ^ 2 = ρW τ := by
    calc (ρW τ + 1) ^ 2 = ρW τ ^ 2 + 1 + (ρW τ + ρW τ) := by noncomm_ring
      _ = (ρW τ ^ 2 + ρW τ + 1) + ρW τ := by abel
      _ = ρW τ := by rw [ρW_threeCycle_sq_add hτ, zero_add]
  have hzero : ρW τ ^ m = 0 := by
    rw [← hsq, ← pow_mul, mul_comm, pow_mul, ← hsub, hm, zero_pow two_ne_zero]
  have hone : ρW τ ^ (3 * m) = 1 := by rw [pow_mul, ρW_threeCycle_pow_three hτ, one_pow]
  have : (1 : Module.End F₂ (W V)) = 0 := by
    rw [← hone, mul_comm, pow_mul, hzero, zero_pow three_ne_zero]
  exact one_ne_zero this

/-- `ρ(τ)` is not a scalar. -/
theorem ρW_threeCycle_ne_smul_one [Nontrivial (W V)] (hτ : τ.IsThreeCycle) (c : F₂) :
    ρW τ ≠ c • 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : W V)
  rcases f2_cases c with rfl | rfl
  · have h3 := ρW_threeCycle_pow_three hτ
    rw [h, zero_smul, zero_pow three_ne_zero] at h3
    exact one_ne_zero h3.symm
  · rw [one_smul] at h
    exact hx (eq_zero_of_ρW_threeCycle_fixed hτ (by rw [h, Module.End.one_apply]))

theorem irreducible_X_sq_add_X_add_one :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : F₂[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : F₂[X]).natDegree = 2 := by
      compute_degree!
    rw [hdeg]
    decide
  · intro x
    rcases f2_cases x with rfl | rfl <;>
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] <;> decide

/-- The minimal polynomial of a three-cycle on `W` is `x² + x + 1`. -/
theorem minpoly_ρW_threeCycle [Nontrivial (W V)] (hτ : τ.IsThreeCycle) :
    minpoly F₂ (ρW τ) = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  refine (minpoly.eq_of_irreducible_of_monic irreducible_X_sq_add_X_add_one ?_ ?_).symm
  · simp [ρW_threeCycle_sq_add hτ]
  · monicity!

end ThreeCycle

section Radical

/-- An operator commuting with every rank-one map is a scalar. -/
theorem eq_smul_one_of_commute_rankOne {K ι M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (b : Module.Basis ι K M) (Z : Module.End K M)
    (h : ∀ i j, Commute Z ((b.coord j).smulRight (b i))) (i0 : ι) :
    Z = b.coord i0 (Z (b i0)) • 1 := by
  refine b.ext fun i ↦ ?_
  have e := congrArg (fun T : Module.End K M ↦ T (b i0)) (h i i0).eq
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, one_smul] at e
  rw [LinearMap.smul_apply, Module.End.one_apply, e, Module.Basis.coord_apply]

variable (n : ℕ)

/-- The all-ones vector, the radical of `b` on `U_n`. -/
def ones : Fin (2 * n) → F₂ :=
  fun _ ↦ 1

theorem ones_mem : ones n ∈ U (Fin (2 * n)) := by
  rw [mem_U]
  simp only [ones, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_mul]
  rw [show ((2 : ℕ) : F₂) = 0 by decide, zero_mul]

theorem ones_eq_sum (M : PerfectMatching (Fin (2 * n))) :
    ones n = ∑ v ∈ Finset.univ.filter (fun v ↦ v < M.mate v), PerfectMatching.v v (M.mate v) := by
  funext k
  have e : ∀ x, (k = M.mate x) ↔ (x = M.mate k) :=
    fun x ↦ ⟨fun h ↦ by rw [h, mate_mate], fun h ↦ by rw [h, mate_mate]⟩
  simp only [ones, Finset.sum_apply, PerfectMatching.v, Pi.add_apply, Finset.sum_add_distrib,
    Pi.single_apply, e, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, mate_mate]
  rcases lt_or_gt_of_ne (M.mate_ne k).symm with h | h
  · rw [ite_eq_left h, ite_eq_right (lt_asymm h), add_zero]
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h, zero_add]

theorem qfun_ones : qfun (ones n) = (n : F₂) := by
  have hs : supp (ones n) = Finset.univ := by
    ext k
    simp [supp, ones]
  rw [qfun, hs, Finset.card_univ, Fintype.card_fin, Nat.mul_div_cancel_left n two_pos]

theorem f2_mul_self (a : F₂) : a * a = a := by
  revert a
  decide

/-- C3. `∑_{e ∈ M} Γ_e = (n mod 2) I`. -/
theorem sum_Γ_matching (hn : 1 ≤ n) (M : PerfectMatching (Fin (2 * n))) :
    ∑ v ∈ Finset.univ.filter (fun v ↦ v < M.mate v), Γ v (M.mate v) = (n : F₂) • 1 := by
  have := nontrivial_W n hn
  obtain ⟨o, -⟩ : ∃ o : Fin (2 * n), True := ⟨⟨0, by omega⟩, trivial⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = gammaL o (ones n) := ⟨_, rfl⟩
  have hsum : Z = ∑ v ∈ Finset.univ.filter (fun v ↦ v < M.mate v), Γ v (M.mate v) := by
    rw [hZ, ones_eq_sum n M, map_sum]
    exact Finset.sum_congr rfl fun v _ ↦ gammaL_v o (M.mate_ne v).symm
  rw [← hsum]
  have hcomm_Γ : ∀ i j : Fin (2 * n), Commute Z (Γ i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Γ, swap_self, ← Perm.one_def, map_one]
      exact Commute.one_right Z
    have h := gammaL_anticomm o (ones_mem n) (v_mem i j)
    rw [gammaL_v o hij, ← hZ] at h
    have hd : dot (ones n) (v i j) = 0 := by
      rw [dot_eq_card, supp_v hij]
      have hs : supp (ones n) = Finset.univ := by
        ext k
        simp [supp, ones]
      rw [hs, Finset.univ_inter, Finset.card_pair hij]
      decide
    rw [hd, zero_smul] at h
    calc Z * Γ i j = Z * Γ i j + (Z * Γ i j + Γ i j * Z) := by rw [h, add_zero]
      _ = (Z * Γ i j + Z * Γ i j) + Γ i j * Z := by abel
      _ = Γ i j * Z := by rw [end_add_self, zero_add]
  have hcomm_ρW : ∀ σ : Perm (Fin (2 * n)), Commute Z (ρW σ) := by
    intro σ
    have hσ : σ ∈ Submonoid.closure {τ : Perm (Fin (2 * n)) | τ.IsSwap} := by
      rw [Perm.mclosure_isSwap]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem τ hτ =>
      obtain ⟨i, j, -, rfl⟩ := hτ
      exact hcomm_Γ i j
    | one =>
      rw [map_one]
      exact Commute.one_right Z
    | mul τ τ' _ _ h h' =>
      rw [map_mul]
      exact h.mul_right h'
  have hcomm : ∀ f : Module.End F₂ (W (Fin (2 * n))), Commute Z f := by
    intro f
    have hf : f ∈ Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) := by
      rw [adjoin_ρW_eq_top n hn]
      exact Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨σ, rfl⟩ := hg
      exact hcomm_ρW σ
    | algebraMap c => exact Algebra.commute_algebraMap_right c Z
    | add f g _ _ hf hg => exact hf.add_right hg
    | mul f g _ _ hf hg => exact hf.mul_right hg
  have hscalar := eq_smul_one_of_commute_rankOne (wBasis n hn) Z (fun i j ↦ hcomm _) ∅
  have hidem : Z * Z = Z := by
    rw [hscalar, smul_mul_smul_comm, one_mul, f2_mul_self]
  have hsq : Z * Z = (n : F₂) • 1 := by
    rw [hZ, gammaL_sq o (ones_mem n), qfun_ones n]
  rw [← hidem, hsq]

end Radical

end Pairing.PerfectMatching
