import Spin.Existence
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Algebra.Algebra.ZMod

/-!
# M5. COD-105

`cod105` : over an algebraically closed field `K` of characteristic 0 there is a basic spin
representation `N` of `S̃_{2n}` (a simple `Cl_K(schurQ)`-module), a basis of `N` in which the
generators are integral over a valuation subring of `K` with `2` in its maximal ideal, and a
reduction map to its residue field `k`, such that the reduction mod 2 is `k ⊗ W_n`, with `S̃_{2n}`
acting on `k ⊗ W_n` through `S_{2n}`. By `reduction_basicSpin` the same holds for every basic
spin representation, every such lattice and every reduction map to a field of characteristic 2.
-/

universe u

namespace Pairing

open PerfectMatching TensorProduct

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

omit [CharZero K] [IsAlgClosed K] in
theorem residue_two_eq_zero {V : ValuationSubring K} (hV : (2 : K) ∈ V.nonunits) :
    (2 : IsLocalRing.ResidueField V) = 0 := by
  rw [ValuationSubring.mem_nonunits_iff] at hV
  have hmem : (2 : V) ∈ IsLocalRing.maximalIdeal V := by
    rw [ValuationSubring.valuation_lt_one_iff]
    exact hV
  rw [← map_ofNat (IsLocalRing.residue V) 2]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem

variable (K)

/-- COD-105. `k ⊗ W_n` is the reduction mod 2 of a basic spin representation of `S̃_{2n}`. -/
theorem cod105 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : Submodule K (CliffordAlgebra (schurQ K (2 * n - 1))))
      (ρ : CliffordAlgebra (schurQ K (2 * n - 1)) →ₐ[K] Module.End K N),
      Nontrivial N ∧ (∀ N' : Submodule K N, (∀ x, ∀ y ∈ N', ρ x y ∈ N') → N' = ⊥ ∨ N' = ⊤) ∧
      ∃ (b : Module.Basis (Fin (Module.finrank K N)) K N) (R : Subring K)
        (hR : ∀ t i j, LinearMap.toMatrix b b (ρ (schurT K (2 * n - 1) t)) i j ∈ R)
        (k : Type u) (_ : Field k) (_ : Algebra F₂ k) (ψ : R →+* k),
        ∃ e : k ⊗[F₂] W (Fin (2 * n)) ≃ₗ[k] (Fin (Module.finrank K N) → k),
          ∀ g : Stilde (2 * n), e.toLinearMap ∘ₗ ρK n k (Stilde.toPerm (2 * n) g) =
            Matrix.toLin' (redHom hn ρ b R hR k ψ (stildeCl n g : Cl n)) ∘ₗ e.toLinearMap := by
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨N, hN, hN0, hsimple⟩ :=
    exists_simple_submodule (Algebra.lmul K (CliffordAlgebra (schurQ K (2 * n - 1))))
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
  obtain ⟨V, hV⟩ := exists_valuationSubring_two (K := K)
  obtain ⟨b, hb⟩ := exists_lattice V _ (restrictHom _ N hN)
  have : CharP (IsLocalRing.ResidueField V) 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast residue_two_eq_zero hV)
  let : Algebra F₂ (IsLocalRing.ResidueField V) := ZMod.algebra _ 2
  obtain ⟨e, -, he⟩ := reduction_basicSpin hn (restrictHom _ N hN) b V.toSubring hb
    (IsLocalRing.ResidueField V) (IsLocalRing.residue V) hsimple
  exact ⟨N, restrictHom _ N hN, inferInstance, hsimple, b, V.toSubring, hb, _, inferInstance,
    inferInstance, IsLocalRing.residue V, e, he⟩

end Pairing
