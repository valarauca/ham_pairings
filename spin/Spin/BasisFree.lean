import Spin.Reduction
import Clifford.BasisFree

/-!
# The basic-spin identification on any vertex type of size `2n`

`reduction_basicSpin` (commit 4a31a12) identifies the reduction mod 2 of a basic spin
representation of `S̃_{2n}` with `k ⊗ W (Fin (2 * n))`. For any `V` with `e : V ≃ Fin (2 * n)`,
`S̃_{2n}` acts on `V` through `e`, and the same identification holds for `k ⊗ W V` and for the
basis-free model `k ⊗ (𝔽₂^𝓜 ⧸ rad B)` of `Clifford.BasisFree`.

* `reduction_basicSpin_congr` : `k^ι ≅ k ⊗ W V` as `k S̃_{2n}`-modules.
* `reduction_basicSpin_quotRad` : `k^ι ≅ k ⊗ (𝔽₂^𝓜 ⧸ rad B)` as `k S̃_{2n}`-modules.
-/

namespace Pairing

open Equiv PerfectMatching TensorProduct

variable {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n)
  {Y : Type*} [AddCommGroup Y] [Module K Y]
  (ρ : CliffordAlgebra (schurQ K (2 * n - 1)) →ₐ[K] Module.End K Y)
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K Y) (R : Subring K)
  (hR : ∀ t i j, LinearMap.toMatrix b b (ρ (schurT K (2 * n - 1) t)) i j ∈ R)
  (k : Type*) [Field k] [Algebra F₂ k] (ψ : R →+* k)
  [CharZero K] [IsAlgClosed K] [Nontrivial Y]
  (hsimple : ∀ N : Submodule K Y, (∀ x, ∀ y ∈ N, ρ x y ∈ N) → N = ⊥ ∨ N = ⊤)
  {V : Type*} [Fintype V] [DecidableEq V] (e : V ≃ Fin (2 * n))

include hsimple in
/-- Wales 7.7 at `p = 2` on any vertex type of size `2n`: the reduction mod 2 of a basic spin
representation of `S̃_{2n}` is `k ⊗ W V`, with `S̃_{2n}` acting on `V` through `e`. `W V` is the
row space of the CKN matrix (arXiv:1211.1506). Transported from `reduction_basicSpin` (commit
4a31a12) along `wCongr e`. -/
theorem reduction_basicSpin_congr :
    ∃ φ : k ⊗[F₂] W V ≃ₗ[k] (ι → k),
      ∀ g : Stilde (2 * n),
        φ.toLinearMap ∘ₗ (ρW (e.symm.permCongr (Stilde.toPerm (2 * n) g))).baseChange k =
          Matrix.toLin' (redHom hn ρ b R hR k ψ (stildeCl n g : Cl n)) ∘ₗ φ.toLinearMap := by
  obtain ⟨φ, -, hφ⟩ := reduction_basicSpin hn ρ b R hR k ψ hsimple
  refine ⟨(LinearEquiv.baseChange F₂ k _ _ (wCongr e)).trans φ, fun g ↦ ?_⟩
  have h1 : (wCongr e).toLinearMap ∘ₗ ρW (e.symm.permCongr (Stilde.toPerm (2 * n) g)) =
      ρW (Stilde.toPerm (2 * n) g) ∘ₗ (wCongr e).toLinearMap := by
    rw [wCongr_comp_ρW, ← permCongr_symm, apply_symm_apply]
  have h2 := hφ g
  rw [ρK] at h2
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_baseChange, LinearMap.comp_assoc,
    ← LinearMap.baseChange_comp, h1, LinearMap.baseChange_comp, ← LinearMap.comp_assoc, h2,
    LinearMap.comp_assoc]

include hsimple in
/-- Basis-free form of Wales 7.7 at `p = 2`: the reduction mod 2 of a basic spin representation
of `S̃_{2n}` is `k ⊗ (𝔽₂^𝓜 ⧸ rad B)`, the quotient by the radical of the Hamiltonicity form, with
`S̃_{2n}` acting on `V` through `e`. Its dimension is the CKN rank `2^(n-1)` (arXiv:1211.1506).
From `reduction_basicSpin` (commit 4a31a12) through `reduction_basicSpin_congr` and
`quotRadEquiv`. -/
theorem reduction_basicSpin_quotRad :
    ∃ φ : k ⊗[F₂] ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) ≃ₗ[k] (ι → k),
      ∀ g : Stilde (2 * n),
        φ.toLinearMap ∘ₗ (ρRad (e.symm.permCongr (Stilde.toPerm (2 * n) g))).baseChange k =
          Matrix.toLin' (redHom hn ρ b R hR k ψ (stildeCl n g : Cl n)) ∘ₗ φ.toLinearMap := by
  obtain ⟨φ, hφ⟩ := reduction_basicSpin_congr hn ρ b R hR k ψ hsimple e
  refine ⟨(LinearEquiv.baseChange F₂ k _ _ quotRadEquiv).trans φ, fun g ↦ ?_⟩
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_baseChange, LinearMap.comp_assoc,
    ← LinearMap.baseChange_comp, quotRadEquiv_comp_ρRad, LinearMap.baseChange_comp,
    ← LinearMap.comp_assoc, hφ g, LinearMap.comp_assoc]

end Pairing
