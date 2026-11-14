import Spin.SchurForm
import Spin.JSystem
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# M3. Basic spin modules in characteristic 0

A basic spin representation over an algebraically closed field `K` of characteristic 0 is a
simple module over Schur's Clifford algebra `Cl_K(schurQ K (2p+1))`, viewed as a representation
of `S̃_{2p+2}` through `schurHom`.

* `polar_schurQ_single_right` : `b(x, b_t) = -2x_t + x_{t-1} + x_{t+1}`.
* `schurQ_nondegenerate` : in characteristic 0 the polar form is nondegenerate.
* `finrank_le_of_simple` : a simple module has dimension at most `2^p`.
-/

namespace Pairing

variable {K : Type*} [Field K]

theorem sum_ite_pred {m : ℕ} (x : Fin m → K) (t : Fin m) :
    ∑ i : Fin m, (if (t : ℕ) = i + 1 then x i else 0) =
      if h : 0 < (t : ℕ) then x ⟨t - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t - 1, by omega⟩]
    · exact ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))
    · intro b _ hb
      exact ite_eq_right_of_eq_false _ _ (eq_false fun e ↦ hb (Fin.ext (by simp; omega)))
    · simp
  · exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right_of_eq_false _ _ (eq_false (by omega))

theorem sum_ite_succ {m : ℕ} (x : Fin m → K) (t : Fin m) :
    ∑ i : Fin m, (if (i : ℕ) = t + 1 then x i else 0) =
      if h : (t : ℕ) + 1 < m then x ⟨t + 1, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t + 1, h⟩]
    · exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
    · intro b _ hb
      exact ite_eq_right_of_eq_false _ _ (eq_false fun e ↦ hb (Fin.ext e))
    · simp
  · exact Finset.sum_eq_zero fun i _ ↦
      ite_eq_right_of_eq_false _ _ (eq_false (by have := i.2; omega))

/-- `b(x, b_t) = -2x_t + x_{t-1} + x_{t+1}`. -/
theorem polar_schurQ_single_right {m : ℕ} (x : Fin m → K) (t : Fin m) :
    QuadraticMap.polar (schurQ K m) x (Pi.single t 1) =
      -2 * x t + (if h : 0 < (t : ℕ) then x ⟨t - 1, by omega⟩ else 0) +
        (if h : (t : ℕ) + 1 < m then x ⟨t + 1, h⟩ else 0) := by
  rw [schurQ, LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_apply,
    Matrix.toBilin'_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h1 : ∀ i, x i * schurA K m i t =
      (if i = t then -x i else 0) + (if (t : ℕ) = i + 1 then x i else 0) := by
    intro i
    simp only [schurA]
    by_cases a : i = t
    · subst a
      simp
    · by_cases b : (t : ℕ) = i + 1 <;> simp [a, b]
  have h2 : ∀ j, schurA K m t j * x j =
      (if j = t then -x j else 0) + (if (j : ℕ) = t + 1 then x j else 0) := by
    intro j
    simp only [schurA]
    by_cases a : t = j
    · subst a
      simp
    · have a' : j ≠ t := Ne.symm a
      by_cases b : (j : ℕ) = t + 1 <;> simp [a, a', b]
  rw [Finset.sum_congr rfl (fun i _ ↦ h1 i), Finset.sum_congr rfl (fun j _ ↦ h2 j),
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_pred, sum_ite_succ]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- In characteristic 0 the polar form of `schurQ` is nondegenerate. -/
theorem schurQ_nondegenerate [CharZero K] {m : ℕ} {x : Fin m → K}
    (hx : ∀ t, QuadraticMap.polar (schurQ K m) x (Pi.single t 1) = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Subsingleton.elim _ _
  have key : ∀ s (hs : s < m), x ⟨s, hs⟩ = ((s : K) + 1) * x ⟨0, hm⟩ := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      match s, ih, hs with
      | 0, _, _ => simp
      | 1, _, hs =>
        have e := hx ⟨0, hm⟩
        rw [polar_schurQ_single_right] at e
        simp only [lt_self_iff_false, dite_false, add_zero, zero_add, show 0 + 1 < m from hs,
          dite_true] at e
        push_cast
        linear_combination e
      | s + 2, ih, hs =>
        have e := hx ⟨s + 1, by omega⟩
        rw [polar_schurQ_single_right] at e
        simp only [show 0 < s + 1 by omega, show s + 1 + 1 < m from hs, dite_true] at e
        have h1 := ih (s + 1) (by omega) (by omega)
        have h0 := ih s (by omega) (by omega)
        have e' : x ⟨s + 1 - 1, by omega⟩ = x ⟨s, by omega⟩ := rfl
        rw [e', h1, h0] at e
        push_cast at e ⊢
        linear_combination e
  have hlast := hx ⟨m - 1, by omega⟩
  rw [polar_schurQ_single_right] at hlast
  simp only [show ¬(m - 1 + 1 < m) by omega, dite_false, add_zero] at hlast
  have hx0 : x ⟨0, hm⟩ = 0 := by
    rw [key (m - 1) (by omega)] at hlast
    by_cases hm1 : 0 < m - 1
    · rw [dite_eq_left_of_eq_true (eq_true hm1), key (m - 1 - 1) (by omega)] at hlast
      have hcast : ((m - 1 - 1 : ℕ) : K) = ((m - 1 : ℕ) : K) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast] at hlast
      have hne : ((m - 1 : ℕ) : K) + 2 ≠ 0 := by
        exact_mod_cast (show (m - 1 : ℕ) + 2 ≠ 0 by omega)
      have : (((m - 1 : ℕ) : K) + 2) * x ⟨0, hm⟩ = 0 := by linear_combination -hlast
      exact (mul_eq_zero.mp this).resolve_left hne
    · rw [dite_eq_right_of_eq_false (eq_false hm1), add_zero] at hlast
      have hm1' : m - 1 = 0 := by omega
      rw [hm1', Nat.cast_zero, zero_add, one_mul] at hlast
      have : (2 : K) * x ⟨0, hm⟩ = 0 := by linear_combination -hlast
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  funext t
  rw [Pi.zero_apply, show t = ⟨t, t.2⟩ from rfl, key t t.2, hx0, mul_zero]

variable [CharZero K] [IsAlgClosed K]

/-- `schurQ` has an orthonormal basis over an algebraically closed field of characteristic 0. -/
theorem exists_orthonormal_schurQ (m : ℕ) :
    ∃ w : Fin m → (Fin m → K), (∀ i, schurQ K m (w i) = 1) ∧
      (∀ i j, i ≠ j → QuadraticMap.polar (schurQ K m) (w i) (w j) = 0) ∧
        Submodule.span K (Set.range w) = ⊤ := by
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hsymm : (QuadraticMap.polarBilin (schurQ K m)).IsSymm :=
    LinearMap.isSymm_def.mpr fun x y ↦ by
      rw [RingHom.id_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hfin : Module.finrank K (Fin m → K) = m := Module.finrank_fin_fun K
  have hortho : ∀ i j, i ≠ j → QuadraticMap.polar (schurQ K m) (v i) (v j) = 0 := fun i j hij ↦ by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact hv hij
  have hQ : ∀ i, schurQ K m (v i) ≠ 0 := by
    intro i h
    apply v.ne_zero i
    apply schurQ_nondegenerate
    intro t
    have hzero : QuadraticMap.polarBilin (schurQ K m) (v i) = 0 := v.ext fun j ↦ by
      rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
      by_cases hij : i = j
      · rw [← hij, QuadraticMap.polar_self, h, smul_zero]
      · exact hortho i j hij
    rw [← QuadraticMap.polarBilin_apply_apply, hzero, LinearMap.zero_apply]
  choose r hr using fun i ↦ IsAlgClosed.exists_pow_nat_eq (schurQ K m (v i)) two_pos
  have hr0 : ∀ i, r i ≠ 0 := fun i h ↦ hQ i (by rw [← hr i, h, zero_pow two_ne_zero])
  let e : Fin m ≃ Fin (Module.finrank K (Fin m → K)) := finCongr hfin.symm
  refine ⟨fun i ↦ (r (e i))⁻¹ • v (e i), fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · rw [QuadraticMap.map_smul, ← hr (e i), smul_eq_mul, pow_two, ← mul_inv, inv_mul_cancel₀
      (mul_ne_zero (hr0 _) (hr0 _))]
  · rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      hortho _ _ (e.injective.ne hij), smul_zero, smul_zero]
  · rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hvi : v i = r i • ((r (e (e.symm i)))⁻¹ • v (e (e.symm i))) := by
      rw [Equiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hr0 i), one_smul]
    rw [hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm i, rfl⟩)

/-- A simple `Cl_K(schurQ K (2p+1))`-module has dimension at most `2^p`. -/
theorem finrank_le_of_simple (p : ℕ) {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K Y] [Nontrivial Y]
    (ρ : CliffordAlgebra (schurQ K (2 * p + 1)) →ₐ[K] Module.End K Y)
    (hsimple : ∀ N : Submodule K Y, (∀ x, ∀ y ∈ N, ρ x y ∈ N) → N = ⊥ ∨ N = ⊤) :
    Module.finrank K Y ≤ 2 ^ p := by
  obtain ⟨w, hw1, hw0, hspan⟩ := exists_orthonormal_schurQ (K := K) (2 * p + 1)
  obtain ⟨I, hI⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  rw [pow_two] at hI
  set J : Fin (2 * p + 1) → Module.End K Y := fun j ↦ ρ (CliffordAlgebra.ι _ (w j)) with hJdef
  have hJ : IsJSystem p J := by
    refine ⟨fun j ↦ ?_, fun i j hij ↦ ?_⟩
    · simp only [hJdef]
      rw [← map_mul ρ, CliffordAlgebra.ι_sq_scalar, hw1, map_one, map_one]
    · simp only [AntiComm, hJdef]
      rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, CliffordAlgebra.ι_mul_ι_add_swap, hw0 i j hij,
        map_zero, map_zero]
  refine finrank_le_of_jSystem hJ hI two_ne_zero fun N hN ↦ hsimple N fun x ↦ ?_
  have hι : ∀ v : Fin (2 * p + 1) → K, ∀ y ∈ N, ρ (CliffordAlgebra.ι _ v) y ∈ N := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range w) := hspan ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      exact hN j
    | zero =>
      intro y _
      rw [map_zero, map_zero, LinearMap.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      intro y hy
      rw [map_add, map_add, LinearMap.add_apply]
      exact add_mem (ha y hy) (hb y hy)
    | smul c a _ ha =>
      intro y hy
      rw [map_smul, map_smul, LinearMap.smul_apply]
      exact N.smul_mem c (ha y hy)
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    intro y hy
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    exact N.smul_mem r hy
  | ι v => exact hι v
  | mul a b ha hb =>
    intro y hy
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb y hy)
  | add a b ha hb =>
    intro y hy
    rw [map_add, LinearMap.add_apply]
    exact add_mem (ha y hy) (hb y hy)

theorem finrank_le_of_simple' {m p : ℕ} (hm : m = 2 * p + 1) {Y : Type*} [AddCommGroup Y]
    [Module K Y] [FiniteDimensional K Y] [Nontrivial Y]
    (ρ : CliffordAlgebra (schurQ K m) →ₐ[K] Module.End K Y)
    (hsimple : ∀ N : Submodule K Y, (∀ x, ∀ y ∈ N, ρ x y ∈ N) → N = ⊥ ∨ N = ⊤) :
    Module.finrank K Y ≤ 2 ^ p := by
  subst hm
  exact finrank_le_of_simple p ρ hsimple

end Pairing
