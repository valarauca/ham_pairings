import Spin.BasicSpin
import Spin.Reduce

/-!
# M5. Reduction mod 2 of Schur's basic spin representation

Let `K` be algebraically closed of characteristic 0 and `Y` a simple module over Schur's
Clifford algebra `Cl_K(schurQ K (2n-1))`, a basic spin representation of `S̃_{2n}`. Let `b` be a
basis of `Y` in which the matrices of the generators `t_j` have entries in a subring `R ⊆ K`, and
let `ψ : R → k` be a ring hom to a field of characteristic 2.

* `redMat t` is the reduction of the matrix of `t_j`, and `redHom` the resulting action of
  `Cl(U_n, q)` on `k^ι`.
* `finrank_eq_of_lattice` : `dim Y = 2^(n-1)`.
* `reduction_basicSpin` : `k^ι ≅ k ⊗ W_n` as `k S̃_{2n}`-modules, with `S̃_{2n}` acting on
  `k ⊗ W_n` through `S_{2n}`.
* `reduction_irreducible` : the reduction is irreducible.
-/

namespace Pairing

open Equiv PerfectMatching TensorProduct

variable {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n)
  {Y : Type*} [AddCommGroup Y] [Module K Y]
  (ρ : CliffordAlgebra (schurQ K (2 * n - 1)) →ₐ[K] Module.End K Y)
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K Y) (R : Subring K)
  (hR : ∀ t i j, LinearMap.toMatrix b b (ρ (schurT K (2 * n - 1) t)) i j ∈ R)
  (k : Type*) [Field k] [Algebra F₂ k] (ψ : R →+* k)

/-- The matrix of `t_j` in the basis `b`, as a matrix over `R`. -/
noncomputable def intMat (t : Fin (2 * n - 1)) : Matrix ι ι R :=
  fun i j ↦ ⟨LinearMap.toMatrix b b (ρ (schurT K (2 * n - 1) t)) i j, hR t i j⟩

/-- The reduction of the matrix of `t_j`. -/
noncomputable def redMat (t : Fin (2 * n - 1)) : Matrix ι ι k :=
  ψ.mapMatrix (intMat ρ b R hR t)

theorem intMat_map (t : Fin (2 * n - 1)) :
    R.subtype.mapMatrix (intMat ρ b R hR t) = LinearMap.toMatrix b b (ρ (schurT K _ t)) :=
  rfl

theorem toMatrix_ρ_mul (x y : CliffordAlgebra (schurQ K (2 * n - 1))) :
    LinearMap.toMatrix b b (ρ (x * y)) =
      LinearMap.toMatrix b b (ρ x) * LinearMap.toMatrix b b (ρ y) := by
  rw [map_mul, LinearMap.toMatrix_mul]

theorem toMatrix_ρ_intCast (z : ℤ) :
    LinearMap.toMatrix b b (ρ (z : CliffordAlgebra (schurQ K (2 * n - 1)))) =
      (z : Matrix ι ι K) := by
  rw [map_intCast, ← map_intCast (LinearMap.toMatrixAlgEquiv b)]
  rfl

theorem intMat_sq (t : Fin (2 * n - 1)) :
    intMat ρ b R hR t * intMat ρ b R hR t = -1 := by
  apply Matrix.map_injective R.subtype_injective
  change R.subtype.mapMatrix _ = R.subtype.mapMatrix _
  rw [map_mul, map_neg, map_one, intMat_map, ← toMatrix_ρ_mul, schurT_sq, map_neg, map_one,
    map_neg, LinearMap.toMatrix_one]

theorem intMat_anticomm (s t : Fin (2 * n - 1)) :
    intMat ρ b R hR s * intMat ρ b R hR t + intMat ρ b R hR t * intMat ρ b R hR s =
      (schurG _ s t : Matrix ι ι R) := by
  apply Matrix.map_injective R.subtype_injective
  change R.subtype.mapMatrix _ = R.subtype.mapMatrix _
  rw [map_add, map_mul, map_mul, map_intCast, intMat_map, intMat_map, ← toMatrix_ρ_mul,
    ← toMatrix_ρ_mul, ← map_add, ← map_add ρ, schurT_anticomm, toMatrix_ρ_intCast]

theorem two_eq_zero_of_F₂ : (2 : k) = 0 := by
  rw [← map_ofNat (algebraMap F₂ k) 2, show (2 : F₂) = 0 by decide, map_zero]

theorem redMat_sq (t : Fin (2 * n - 1)) : redMat ρ b R hR k ψ t * redMat ρ b R hR k ψ t = 1 := by
  rw [redMat, ← map_mul, intMat_sq, map_neg, map_one, neg_eq_self_F₂]

theorem redMat_anticomm (s t : Fin (2 * n - 1)) :
    redMat ρ b R hR k ψ s * redMat ρ b R hR k ψ t + redMat ρ b R hR k ψ t * redMat ρ b R hR k ψ s =
      if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0 := by
  rw [redMat, redMat, ← map_mul, ← map_mul, ← map_add, intMat_anticomm, map_intCast, schurG]
  by_cases hst : s = t
  · have hc : ¬((t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1) := by rw [hst]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hst), ite_eq_right_of_eq_false _ _ (eq_false hc),
      Int.cast_neg, Int.cast_ofNat]
    rw [show (2 : Matrix ι ι k) = (2 : k) • 1 by rw [ofNat_smul_eq_nsmul]; norm_num,
      two_eq_zero_of_F₂, zero_smul, neg_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hst)]
    split_ifs <;> simp

/-- The reduced action of `Cl(U_n, q)` on `k^ι`. -/
noncomputable def redHom : Cl n →ₐ[F₂] Matrix ι ι k :=
  reduceHom hn (redMat ρ b R hR k ψ) (redMat_sq ρ b R hR k ψ) (redMat_anticomm ρ b R hR k ψ)

theorem redHom_ι_adjU (t : Fin (2 * n - 1)) :
    redHom hn ρ b R hR k ψ (CliffordAlgebra.ι _ (adjU n t)) = redMat ρ b R hR k ψ t :=
  reduceHom_ι_adjU hn _ _ _ t

/-- The reduced action as endomorphisms of `k^ι`. -/
noncomputable def redRep : Cl n →+* Module.End k (ι → k) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k)).toRingEquiv.toRingHom.comp
    (redHom hn ρ b R hR k ψ).toRingHom

theorem redRep_apply (x : Cl n) :
    redRep hn ρ b R hR k ψ x = Matrix.toLin' (redHom hn ρ b R hR k ψ x) :=
  rfl

theorem redHom_stildeCl_t (j : Fin (2 * n - 1)) :
    redHom hn ρ b R hR k ψ (stildeCl n (Stilde.t j) : Cl n) = redMat ρ b R hR k ψ j := by
  rw [stildeCl_t, adjT, redHom_ι_adjU]

theorem redHom_stildeCl_z :
    redHom hn ρ b R hR k ψ (stildeCl n (Stilde.z (2 * n)) : Cl n) = 1 := by
  rw [stildeCl_z, map_one]

omit [DecidableEq ι] [Algebra F₂ k] in
include hn in
/-- A subspace stable under `α(ι(v_{t,t+1}))` for every `t` is stable under all of `Cl(U_n, q)`. -/
theorem stable_of_adjU {M : Type*} [AddCommGroup M] [Module k M] (α : Cl n →+* Module.End k M)
    (N : Submodule k M) (hN : ∀ t, ∀ v ∈ N, α (CliffordAlgebra.ι _ (adjU n t)) v ∈ N)
    (x : Cl n) : ∀ v ∈ N, α x v ∈ N := by
  have hι : ∀ u : U (Fin (2 * n)), ∀ v ∈ N, α (CliffordAlgebra.ι _ u) v ∈ N := by
    intro u
    have hu : u ∈ Submodule.span F₂ (Set.range (adjU n)) := (span_adjU n hn) ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, rfl⟩ := hy
      exact hN t
    | zero =>
      intro v _
      rw [map_zero, map_zero, LinearMap.zero_apply]
      exact zero_mem _
    | add a c _ _ ha hc =>
      intro v hv
      rw [map_add, map_add, LinearMap.add_apply]
      exact add_mem (ha v hv) (hc v hv)
    | smul c a _ ha =>
      intro v hv
      rcases f2_cases c with rfl | rfl
      · rw [zero_smul, map_zero, map_zero, LinearMap.zero_apply]
        exact zero_mem _
      · rw [one_smul]
        exact ha v hv
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    intro v hv
    rcases f2_cases r with rfl | rfl
    · rw [map_zero, map_zero, LinearMap.zero_apply]
      exact zero_mem _
    · rw [map_one, map_one, Module.End.one_apply]
      exact hv
  | ι u => exact hι u
  | mul a c ha hc =>
    intro v hv
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hc v hv)
  | add a c ha hc =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact add_mem (ha v hv) (hc v hv)

variable [CharZero K] [IsAlgClosed K] [Nontrivial Y]
  (hsimple : ∀ N : Submodule K Y, (∀ x, ∀ y ∈ N, ρ x y ∈ N) → N = ⊥ ∨ N = ⊤)

include hn b hR ψ hsimple in
/-- The lattice has rank `2^(n-1)`. -/
theorem card_eq_of_lattice : Fintype.card ι = 2 ^ (n - 1) := by
  have : FiniteDimensional K Y := Module.Finite.of_basis b
  have hle := finrank_le_of_simple' (show 2 * n - 1 = 2 * (n - 1) + 1 by omega) ρ hsimple
  rw [Module.finrank_eq_card_basis b] at hle
  have hpos : 0 < Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos
  have : Nonempty ι := Fintype.card_pos_iff.mp hpos
  have : FiniteDimensional k (k ⊗[F₂] W (Fin (2 * n))) :=
    Module.Finite.of_basis ((wBasis n hn).baseChange k)
  obtain ⟨φ, hinj, -⟩ := exists_injective_intertwiner n k hn (redRep hn ρ b R hR k ψ)
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_baseChange_W n k hn, Module.finrank_fintype_fun_eq_card] at hge
  omega

include hn b hR ψ hsimple in
/-- A basic spin representation with a lattice has dimension `2^(n-1)`. -/
theorem finrank_eq_of_lattice : Module.finrank K Y = 2 ^ (n - 1) := by
  rw [Module.finrank_eq_card_basis b, card_eq_of_lattice hn ρ b R hR k ψ hsimple]

include hsimple in
/-- Wales 7.7 at `p = 2`: the reduction mod 2 of a basic spin representation of `S̃_{2n}` is
`k ⊗ W_n`, with `S̃_{2n}` acting on `k ⊗ W_n` through `S_{2n}`. -/
theorem reduction_basicSpin :
    ∃ e : k ⊗[F₂] W (Fin (2 * n)) ≃ₗ[k] (ι → k),
      (∀ x : Cl n, e.toLinearMap ∘ₗ cliffordRepK n k hn x =
        redRep hn ρ b R hR k ψ x ∘ₗ e.toLinearMap) ∧
      ∀ g : Stilde (2 * n), e.toLinearMap ∘ₗ ρK n k (Stilde.toPerm (2 * n) g) =
        Matrix.toLin' (redHom hn ρ b R hR k ψ (stildeCl n g : Cl n)) ∘ₗ e.toLinearMap := by
  obtain ⟨e, he⟩ := exists_intertwining_equiv n k hn (redRep hn ρ b R hR k ψ)
    (by rw [Module.finrank_fintype_fun_eq_card, card_eq_of_lattice hn ρ b R hR k ψ hsimple])
  refine ⟨e, he, fun g ↦ ?_⟩
  have h := he (stildeCl n g : Cl n)
  rwa [cliffordRepK_apply, cliffordRep_stildeCl, redRep_apply] at h

include hn hsimple in
/-- The reduction is irreducible. -/
theorem reduction_irreducible (N : Submodule k (ι → k))
    (hN : ∀ t, ∀ v ∈ N, (redMat ρ b R hR k ψ t).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  obtain ⟨e, he, -⟩ := reduction_basicSpin hn ρ b R hR k ψ hsimple
  have hall := stable_of_adjU hn k (redRep hn ρ b R hR k ψ) N (fun t v hv ↦ by
    rw [redRep_apply, redHom_ι_adjU, Matrix.toLin'_apply]
    exact hN t v hv)
  have hinv : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ N.comap e.toLinearMap,
      ρK n k σ x ∈ N.comap e.toLinearMap := by
    intro σ x hx
    obtain ⟨y, hy⟩ := cliffordRep_surjective n hn (base n hn) (ρW σ)
    have e1 : ρK n k σ = cliffordRepK n k hn y := by rw [ρK, cliffordRepK_apply, hy]
    rw [Submodule.mem_comap, e1, ← LinearMap.comp_apply, he y, LinearMap.comp_apply]
    exact hall y _ hx
  rcases ρK_invariant_eq_bot_or_top n k hn _ hinv with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e.symm v ∈ N.comap e.toLinearMap := by
      rw [Submodule.mem_comap]
      simpa using hv
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← e.apply_symm_apply v, this, map_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have : e.symm v ∈ N.comap e.toLinearMap := h ▸ Submodule.mem_top
    simpa using this

end Pairing
