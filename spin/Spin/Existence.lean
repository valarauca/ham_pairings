import Spin.Reduction
import Spin.Monomials
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold

/-!
# M4. Existence of basic spin representations and of their lattices

* `module_finite_cl` : `Cl_K(schurQ)` is spanned by ordered monomials, so it is finite over `K`.
* `exists_simple` : there is a simple `Cl_K(schurQ)`-module, a basic spin representation.
* `exists_lattice` : every finite-dimensional `Cl_K(schurQ)`-module has a basis in which the
  generators have entries in a valuation subring `V ⊆ K` with `2` in its maximal ideal.
-/

namespace Pairing

open PerfectMatching

variable {K : Type*} [Field K]

theorem schurT_anticomm_int (m : ℕ) (i j : Fin m) :
    ∃ g : ℤ, schurT K m i * schurT K m j + schurT K m j * schurT K m i = g :=
  ⟨schurG m i j, schurT_anticomm i j⟩

theorem monoSpan_le_span {A : Type*} [Ring A] [Algebra K A] {m : ℕ} (T : Fin m → A)
    (U : Finset (Fin m)) :
    monoSpan T U ≤ (Submodule.span K (Set.range (mono T))).restrictScalars ℤ :=
  Submodule.span_le.mpr fun _ ⟨S, _, e⟩ ↦ e ▸ Submodule.subset_span ⟨S, rfl⟩

theorem ι_eq_sum (m : ℕ) (v : Fin m → K) :
    CliffordAlgebra.ι (schurQ K m) v = ∑ j, v j • schurT K m j := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [schurT, ← map_smul]
  congr 1
  ext t
  simp [Pi.single_apply]

/-- Every element of `Cl_K(schurQ)` is a combination of ordered monomials. -/
theorem mem_span_mono (m : ℕ) (x : CliffordAlgebra (schurQ K m)) :
    x ∈ Submodule.span K (Set.range (mono (schurT K m))) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← mono_empty (schurT K m)]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨∅, rfl⟩)
  | add x y hx hy => exact add_mem hx hy
  | ι_mul x v hx =>
    rw [ι_eq_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨S, rfl⟩ := hy
      exact monoSpan_le_span _ _ (monoSpan_mono _ (Finset.subset_univ _)
        (T_mul_mono_mem schurT_sq (schurT_anticomm_int m) S j))
    | zero => rw [mul_zero]; exact zero_mem _
    | add a c _ _ ha hc => rw [mul_add]; exact add_mem ha hc
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

instance module_finite_cl (m : ℕ) : Module.Finite K (CliffordAlgebra (schurQ K m)) := by
  classical
  refine Module.finite_def.mpr ⟨Finset.univ.image (mono (schurT K m)), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  exact fun x _ ↦ mem_span_mono m x

/-- `ρ` restricted to an invariant subspace. -/
def restrictHom {A Z : Type*} [Ring A] [Algebra K A] [AddCommGroup Z] [Module K Z]
    (ρ : A →ₐ[K] Module.End K Z) (N : Submodule K Z) (hN : ∀ x, ∀ y ∈ N, ρ x y ∈ N) :
    A →ₐ[K] Module.End K N where
  toFun x := (ρ x).restrict (hN x)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp [Algebra.algebraMap_eq_smul_one]

theorem restrictHom_apply {A Z : Type*} [Ring A] [Algebra K A] [AddCommGroup Z] [Module K Z]
    (ρ : A →ₐ[K] Module.End K Z) (N : Submodule K Z) (hN : ∀ x, ∀ y ∈ N, ρ x y ∈ N) (x : A)
    (y : N) : (restrictHom ρ N hN x y : Z) = ρ x y :=
  rfl

/-- A nonzero finite-dimensional module contains a simple submodule. -/
theorem exists_simple_submodule {A Z : Type*} [Ring A] [Algebra K A] [AddCommGroup Z]
    [Module K Z] [FiniteDimensional K Z] [Nontrivial Z] (ρ : A →ₐ[K] Module.End K Z) :
    ∃ N : Submodule K Z, ∃ hN : ∀ x, ∀ y ∈ N, ρ x y ∈ N, N ≠ ⊥ ∧
      ∀ N' : Submodule K N, (∀ x, ∀ y ∈ N', restrictHom ρ N hN x y ∈ N') → N' = ⊥ ∨ N' = ⊤ := by
  set S : Set (Submodule K Z) := {N | N ≠ ⊥ ∧ ∀ x, ∀ y ∈ N, ρ x y ∈ N}
  have hS : S.Nonempty := ⟨⊤, top_ne_bot, fun _ _ _ ↦ Submodule.mem_top⟩
  obtain ⟨N, ⟨hN0, hN⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  refine ⟨N, hN, hN0, fun N' hN' ↦ ?_⟩
  by_cases hb : N' = ⊥
  · exact Or.inl hb
  right
  have hmap : N'.map N.subtype ∈ S := by
    refine ⟨fun h ↦ hb ?_, fun x y hy ↦ ?_⟩
    · exact Submodule.map_injective_of_injective N.injective_subtype
        (h.trans (Submodule.map_bot _).symm)
    · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact Submodule.mem_map.mpr ⟨_, hN' x z hz, rfl⟩
  have hle : N'.map N.subtype ≤ N := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have heq : N'.map N.subtype = N := by
    by_contra hne
    exact hmin _ hmap (lt_of_le_of_ne hle hne)
  rw [eq_top_iff]
  intro z _
  have hz : (z : Z) ∈ N'.map N.subtype := by
    rw [heq]
    exact z.2
  obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
  rwa [show w = z from Subtype.ext hwz] at hw

variable [CharZero K]

/-- There is a valuation subring of `K` in which `2` is not a unit. -/
theorem exists_valuationSubring_two : ∃ V : ValuationSubring K, (2 : K) ∈ V.nonunits := by
  have h2 : (2 : K) ∈ (⊥ : Subring K) := Subring.mem_bot.mpr ⟨2, by norm_num⟩
  have hI : Ideal.span {(⟨2, h2⟩ : (⊥ : Subring K))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hunit
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    obtain ⟨z, hz⟩ := Subring.mem_bot.mp w.2
    have e : (2 : K) * (z : K) = 1 := by
      have := congrArg Subtype.val hw
      simpa [hz] using this
    have e' : ((2 * z : ℤ) : K) = ((1 : ℤ) : K) := by push_cast; exact e
    have := Int.cast_injective e'
    omega
  obtain ⟨V, -, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨V, hV ⟨⟨2, h2⟩, Ideal.subset_span rfl, rfl⟩⟩

omit [CharZero K] in
/-- Every finite-dimensional `Cl_K(schurQ)`-module has a basis in which the generators have
entries in a given valuation subring `V`. -/
theorem exists_lattice (V : ValuationSubring K) (m : ℕ) {Y : Type*} [AddCommGroup Y]
    [Module K Y] [FiniteDimensional K Y]
    (ρ : CliffordAlgebra (schurQ K m) →ₐ[K] Module.End K Y) :
    ∃ b : Module.Basis (Fin (Module.finrank K Y)) K Y,
      ∀ t i j, LinearMap.toMatrix b b (ρ (schurT K m t)) i j ∈ V := by
  classical
  set d := Module.finrank K Y
  let b0 : Module.Basis (Fin d) K Y := Module.finBasis K Y
  let g : Finset (Fin m) × Fin d → (Fin d → K) :=
    fun q ↦ b0.equivFun (ρ (mono (schurT K m) q.1) (b0 q.2))
  let M : Submodule V (Fin d → K) := Submodule.span V (Set.range g)
  let Tt : Fin m → (Fin d → K) →ₗ[K] (Fin d → K) := fun t ↦
    b0.equivFun.toLinearMap ∘ₗ ρ (schurT K m t) ∘ₗ b0.equivFun.symm.toLinearMap
  have hTg : ∀ t q, Tt t (g q) ∈ M := by
    rintro t ⟨S, i⟩
    have e : Tt t (g (S, i)) = b0.equivFun (ρ (schurT K m t * mono (schurT K m) S) (b0 i)) := by
      simp [Tt, g, map_mul]
    rw [e]
    have hmem := monoSpan_mono _ (Finset.subset_univ _)
      (T_mul_mono_mem (schurT_sq (R := K) (m := m)) (schurT_anticomm_int m) S t)
    generalize schurT K m t * mono (schurT K m) S = x at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S', -, rfl⟩ := hx
      exact Submodule.subset_span ⟨(S', i), rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply, map_add]
      exact add_mem hx hy
    | smul c x _ hx =>
      rw [map_zsmul, LinearMap.smul_apply, map_zsmul]
      exact zsmul_mem hx c
  have hTM : ∀ t, ∀ y ∈ M, Tt t y ∈ M := by
    intro t y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hTg t q
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact M.smul_mem c hx
  have : Module.Finite V M := Module.Finite.span_of_finite V (Set.finite_range g)
  have htf : Module.IsTorsionFree V M := inferInstance
  have : Module.Flat V M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp htf)
  have : Module.Free V M := Module.free_of_flat_of_isLocalRing
  let bM := Module.Free.chooseBasis V M
  let vecs : Module.Free.ChooseBasisIndex V M → (Fin d → K) := fun i ↦ (bM i : Fin d → K)
  have hlinV : LinearIndependent V vecs :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hlinK : LinearIndependent K vecs := (LinearIndependent.iff_fractionRing V K).mp hlinV
  have hexp : ∀ y : M, (y : Fin d → K) = ∑ i, ((bM.repr y i : V) : K) • vecs i := by
    intro y
    conv_lhs => rw [← bM.sum_repr y]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Submodule.coe_smul]
    rfl
  have hspanM : ∀ y ∈ M, y ∈ Submodule.span K (Set.range vecs) := by
    intro y hy
    rw [show y = ((⟨y, hy⟩ : M) : Fin d → K) from rfl, hexp]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span K (Set.range vecs) := by
    rw [← (Pi.basisFun K (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    apply hspanM
    have e : Pi.basisFun K (Fin d) j = g (∅, j) := by
      rw [Pi.basisFun_apply]
      simp only [g, mono_empty, map_one, Module.End.one_apply]
      funext k
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    rw [e]
    exact Submodule.subset_span ⟨(∅, j), rfl⟩
  let bE := Module.Basis.mk hlinK hspan
  have hint : ∀ t i j, bE.repr (Tt t (vecs j)) i ∈ V := by
    intro t i j
    have hy := hTM t (vecs j) (bM j).2
    have e := hexp ⟨_, hy⟩
    rw [show ((⟨Tt t (vecs j), hy⟩ : M) : Fin d → K) = Tt t (vecs j) from rfl] at e
    rw [e]
    have : ∑ l, ((bM.repr ⟨_, hy⟩ l : V) : K) • vecs l =
        ∑ l, ((bM.repr ⟨_, hy⟩ l : V) : K) • bE l := by
      simp [bE, Module.Basis.mk_apply]
    rw [this, bE.repr_sum_self]
    exact (bM.repr ⟨_, hy⟩ i).2
  let b' : Module.Basis _ K Y := bE.map b0.equivFun.symm
  let e : Module.Free.ChooseBasisIndex V M ≃ Fin d := b'.indexEquiv b0
  refine ⟨b'.reindex e, fun t i j ↦ ?_⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  have : b'.repr (ρ (schurT K m t) (b' (e.symm j))) (e.symm i) =
      bE.repr (Tt t (vecs (e.symm j))) (e.symm i) := by
    simp [b', Tt, bE, Module.Basis.mk_apply]
  rw [this]
  exact hint t _ _

end Pairing
