import Clifford.Dimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# A basis-free form of the CKN rank theorem

Cygan, Kratsch and Nederlof (arXiv:1211.1506, §3.1) prove `rank_{𝔽₂} H_t = 2^(t/2-1)` from an
explicit family of basis matchings. At commit 4a31a12 this is `finrank_W_eq` and `rank_H_eq` in
`Clifford.Dimension`, stated on `Fin (2 * n)` and proved through the basis `wBasis`. Here the
vertex type is any finite `V` with `|V| = 2n`, and `W V` is described without a basis.

* `wCongr` : `W V ≃ W V'` along `e : V ≃ V'`, and `wCongr_ρW` : it carries `ρW σ` to
  `ρW (e.permCongr σ)`.
* `finrank_W_eq_of_card`, `rank_H_eq_of_card` : `dim W V = rank H = 2^(n-1)`.
* `hamForm` : the form `B(P, Q) = [P ∪ Q is one cycle]` on `𝔽₂^𝓜`, and `quotRadEquiv` :
  `𝔽₂^𝓜 ⧸ rad B ≃ W V`, sending the class of `P` to the row `r_P`.
* `finrank_quot_rad` : `dim 𝔽₂^𝓜 ⧸ rad B = 2^(n-1)`.
* `ρRad`, `quotRadEquiv_ρRad` : `S_V` acts on `𝔽₂^𝓜 ⧸ rad B`, and `quotRadEquiv` is
  `S_V`-equivariant.
-/

namespace Pairing.PerfectMatching

open Equiv Matrix

section Transport

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

/-- Relabelling `f ↦ f ∘ (congr e)⁻¹` of `𝔽₂^𝓜` along `e : V ≃ V'`, with `congr` as at commit
4a31a12. -/
def funCongr (e : V ≃ V') : (PerfectMatching V → F₂) ≃ₗ[F₂] (PerfectMatching V' → F₂) :=
  LinearEquiv.funCongrLeft F₂ F₂ (congr e).symm

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] in
/-- Relabelling evaluates through `congr e` (`congr` at commit 4a31a12). Used for the
vertex-type-free CKN rank formula, arXiv:1211.1506. -/
theorem funCongr_apply (e : V ≃ V') (f : PerfectMatching V → F₂) (Q : PerfectMatching V') :
    funCongr e f Q = f ((congr e).symm Q) :=
  rfl

/-- Relabelling sends the row `r_P` of the CKN matching connectivity matrix `H`
(arXiv:1211.1506) to `r_{congr e P}`, by `H_congr` at commit 4a31a12. -/
theorem funCongr_H (e : V ≃ V') (P : PerfectMatching V) : funCongr e (H P) = H (congr e P) := by
  funext Q
  rw [funCongr_apply, ← H_congr e P ((congr e).symm Q), apply_symm_apply]

/-- Relabelling carries the row space `W V` of the CKN matrix `H` (arXiv:1211.1506) onto `W V'`.
`W` and `H` are the definitions at commit 4a31a12. -/
theorem map_funCongr_W (e : V ≃ V') : (W V).map (funCongr e : _ →ₗ[F₂] _) = W V' := by
  rw [W, W, Submodule.map_span, ← Set.range_comp]
  have h : (funCongr e : (PerfectMatching V → F₂) →ₗ[F₂] _) ∘ H.row = H.row ∘ congr e :=
    funext fun P ↦ funCongr_H e P
  rw [h, (congr e).surjective.range_comp]

/-- The CKN row space (arXiv:1211.1506) is natural in the vertex type, `W V ≃ W V'` along
`e : V ≃ V'`. `W` is the definition at commit 4a31a12. -/
def wCongr (e : V ≃ V') : W V ≃ₗ[F₂] W V' :=
  ((funCongr e).submoduleMap (W V)).trans (LinearEquiv.ofEq _ _ (map_funCongr_W e))

/-- `wCongr e` is relabelling on the ambient space. For the CKN row space `W`
(arXiv:1211.1506, `W` at commit 4a31a12). -/
theorem coe_wCongr (e : V ≃ V') (x : W V) :
    (wCongr e x : PerfectMatching V' → F₂) = funCongr e x :=
  rfl

/-- `wCongr e r_P = r_{congr e P}` for the rows `rowW` (commit 4a31a12) of the CKN matrix,
arXiv:1211.1506. -/
theorem wCongr_rowW (e : V ≃ V') (P : PerfectMatching V) : wCongr e (rowW P) = rowW (congr e P) :=
  Subtype.ext (funCongr_H e P)

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] in
/-- `(e.permCongr σ)⁻¹` acts on transported matchings as `σ⁻¹` does before transport, by
`congr_smul` at commit 4a31a12. Used to transport the CKN row space, arXiv:1211.1506. -/
theorem congr_symm_inv_smul (e : V ≃ V') (σ : Perm V) (Q : PerfectMatching V') :
    (congr e).symm ((e.permCongr σ)⁻¹ • Q) = σ⁻¹ • (congr e).symm Q := by
  apply (congr e).injective
  rw [congr_smul, apply_symm_apply, apply_symm_apply]
  congr 1

/-- Naturality of the CKN row space (arXiv:1211.1506): `wCongr e` intertwines `ρW σ` on `W V`
with `ρW (e.permCongr σ)` on `W V'`. `W`, `ρW` are the definitions at commit 4a31a12. -/
theorem wCongr_ρW (e : V ≃ V') (σ : Perm V) (x : W V) :
    wCongr e (ρW σ x) = ρW (e.permCongr σ) (wCongr e x) := by
  apply Subtype.ext
  funext Q
  change (x : PerfectMatching V → F₂) (σ⁻¹ • (congr e).symm Q) =
    (x : PerfectMatching V → F₂) ((congr e).symm ((e.permCongr σ)⁻¹ • Q))
  rw [congr_symm_inv_smul]

/-- `wCongr_ρW` as an identity of linear maps, for the CKN row space (arXiv:1211.1506) and
`ρW` at commit 4a31a12. -/
theorem wCongr_comp_ρW (e : V ≃ V') (σ : Perm V) :
    (wCongr e).toLinearMap ∘ₗ ρW σ = ρW (e.permCongr σ) ∘ₗ (wCongr e).toLinearMap :=
  LinearMap.ext (wCongr_ρW e σ)

/-- CKN rank formula for any vertex type (arXiv:1211.1506, §3.1): if `|V| = 2n` with `n ≥ 1` then
`dim W V = 2^(n-1)`. Transported from `finrank_W_eq` (commit 4a31a12) along `wCongr`. -/
theorem finrank_W_eq_of_card {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Module.finrank F₂ (W V) = 2 ^ (n - 1) := by
  rw [(wCongr (Fintype.equivFinOfCardEq hV)).finrank_eq, finrank_W_eq n hn]

/-- CKN rank formula for any vertex type (arXiv:1211.1506, §3.1): if `|V| = 2n` with `n ≥ 1` then
`rank_{𝔽₂} H = 2^(n-1)`. Generalizes `rank_H_eq` (commit 4a31a12) via `finrank_W`. -/
theorem rank_H_eq_of_card {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    (H (V := V)).rank = 2 ^ (n - 1) := by
  rw [← finrank_W, finrank_W_eq_of_card hV hn]

end Transport

section Radical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Hamiltonicity form on the free module `𝔽₂^𝓜`, `B(x, y) = ∑_{P,Q} x_P [P ∪ Q is one
cycle] y_Q`. Its Gram matrix is the CKN matrix `H` (arXiv:1211.1506, `H` at commit 4a31a12). -/
def hamForm : LinearMap.BilinForm F₂ (PerfectMatching V → F₂) :=
  Matrix.toBilin' (H (V := V))

/-- On matchings, `B(P, Q) = [P ∪ Q is one Hamiltonian cycle]`, the CKN matching connectivity
entry (arXiv:1211.1506; `H`, `Ham` at commit 4a31a12). -/
theorem hamForm_single (P Q : PerfectMatching V) :
    hamForm (Pi.single P 1) (Pi.single Q 1) = if Ham P Q then 1 else 0 := by
  rw [hamForm, Matrix.toBilin'_single, H_apply]

/-- `B(x, y) = (x H) · y` for the CKN matrix `H` (arXiv:1211.1506, `H` at commit 4a31a12). -/
theorem hamForm_apply (x y : PerfectMatching V → F₂) : hamForm x y = (x ᵥ* H) ⬝ᵥ y := by
  rw [hamForm, Matrix.toBilin'_apply', Matrix.dotProduct_mulVec]

/-- `B` is symmetric, since the CKN matrix is (arXiv:1211.1506; `H_comm` at commit 4a31a12). So
its left and right radicals agree. -/
theorem hamForm_comm (x y : PerfectMatching V → F₂) : hamForm x y = hamForm y x := by
  have hT : (H (V := V))ᵀ = H := Matrix.ext fun P Q ↦ H_comm Q P
  rw [hamForm_apply, hamForm_apply, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, hT]

/-- The radical of `B` is the left kernel of the CKN matrix `H` (arXiv:1211.1506; `H` at commit
4a31a12). -/
theorem ker_hamForm :
    LinearMap.ker (hamForm (V := V)) = LinearMap.ker (H (V := V)).vecMulLinear := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.vecMulLinear_apply]
  constructor
  · intro h
    funext Q
    have hQ := LinearMap.congr_fun h (Pi.single Q 1)
    rwa [hamForm_apply, dotProduct_single, mul_one, LinearMap.zero_apply] at hQ
  · intro h
    refine LinearMap.ext fun y ↦ ?_
    rw [hamForm_apply, h, zero_dotProduct, LinearMap.zero_apply]

/-- The image of `x ↦ x H` is the row space `W V` of the CKN matrix (arXiv:1211.1506; `W` at
commit 4a31a12). -/
theorem range_vecMulLinear_H : LinearMap.range (H (V := V)).vecMulLinear = W V :=
  range_vecMulLinear _

/-- `𝔽₂^𝓜 ⧸ rad B ≃ W V`, sending the class of `x` to `x H`, where `W V` is the row space of the
CKN matrix (arXiv:1211.1506, `W` at commit 4a31a12). -/
noncomputable def quotRadEquiv :
    ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) ≃ₗ[F₂] W V :=
  (Submodule.quotEquivOfEq _ _ ker_hamForm).trans
    ((LinearMap.quotKerEquivRange _).trans (LinearEquiv.ofEq _ _ range_vecMulLinear_H))

/-- `quotRadEquiv [x] = x H`, for the CKN matrix `H` (arXiv:1211.1506; `W`, `H` at commit
4a31a12). -/
theorem coe_quotRadEquiv_mk (x : PerfectMatching V → F₂) :
    (quotRadEquiv (Submodule.Quotient.mk x) : PerfectMatching V → F₂) = x ᵥ* H :=
  rfl

/-- `quotRadEquiv [P] = r_P`, the row of the CKN matrix at `P` (arXiv:1211.1506; `rowW` at commit
4a31a12). -/
theorem quotRadEquiv_single (P : PerfectMatching V) :
    quotRadEquiv (Submodule.Quotient.mk (Pi.single P 1)) = rowW P :=
  Subtype.ext ((coe_quotRadEquiv_mk _).trans (single_one_vecMul P H))

/-- Basis-free CKN rank theorem (arXiv:1211.1506, §3.1): if `|V| = 2n` with `n ≥ 1`, the
quotient of `𝔽₂^𝓜` by the radical of the Hamiltonicity form has dimension `2^(n-1)`. From
`finrank_W_eq` (commit 4a31a12) through `finrank_W_eq_of_card`. -/
theorem finrank_quot_rad {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Module.finrank F₂ ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) =
      2 ^ (n - 1) := by
  rw [quotRadEquiv.finrank_eq, finrank_W_eq_of_card hV hn]

/-- `x ↦ x H` intertwines the permutation action `ρ` (commit 4a31a12) with itself, since the CKN
matrix (arXiv:1211.1506) is `S_V`-invariant (`H_smul`). -/
theorem vecMul_ρ (σ : Perm V) (x : PerfectMatching V → F₂) : ρ σ x ᵥ* H = ρ σ (x ᵥ* H) := by
  funext Q
  simp only [Matrix.vecMul, dotProduct, ρ_apply]
  exact Fintype.sum_equiv (MulAction.toPerm σ⁻¹) _ _ fun P ↦ by
    rw [MulAction.toPerm_apply, H_smul]

/-- `B` is `S_V`-invariant under `ρ` (commit 4a31a12), as the CKN matrix is
(arXiv:1211.1506). -/
theorem hamForm_ρ (σ : Perm V) (x y : PerfectMatching V → F₂) :
    hamForm (ρ σ x) (ρ σ y) = hamForm x y := by
  rw [hamForm_apply, hamForm_apply, vecMul_ρ]
  simp only [dotProduct, ρ_apply]
  exact Fintype.sum_equiv (MulAction.toPerm σ⁻¹) _ _ fun Q ↦ rfl

/-- The radical of `B` is `S_V`-stable under `ρ` (commit 4a31a12). For the CKN matrix,
arXiv:1211.1506. -/
theorem ρ_mem_ker_hamForm (σ : Perm V) {x : PerfectMatching V → F₂}
    (hx : x ∈ LinearMap.ker (hamForm (V := V))) : ρ σ x ∈ LinearMap.ker (hamForm (V := V)) := by
  rw [ker_hamForm, LinearMap.mem_ker, Matrix.vecMulLinear_apply] at hx ⊢
  rw [vecMul_ρ, hx, map_zero]

/-- `rad B` as a subrepresentation of `ρ` (commit 4a31a12). -/
def radSub : Subrepresentation (ρ (V := V)) where
  toSubmodule := LinearMap.ker hamForm
  apply_mem_toSubmodule σ _ hx := ρ_mem_ker_hamForm σ hx

/-- The action of `S_V` on `𝔽₂^𝓜 ⧸ rad B`, `σ [x] = [ρ σ x]`, induced by `ρ` (commit 4a31a12). -/
def ρRad :
    Representation F₂ (Perm V) ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) :=
  (radSub (V := V)).quotient

/-- `ρRad σ [x] = [ρ σ x]`, so the `S_V` action on the CKN quotient (arXiv:1211.1506) is induced
by `ρ` (commit 4a31a12). -/
theorem ρRad_mk (σ : Perm V) (x : PerfectMatching V → F₂) :
    ρRad σ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ σ x) :=
  rfl

/-- Equivariance of the basis-free CKN identification (arXiv:1211.1506): `quotRadEquiv` carries
`ρRad σ` to `ρW σ`, the action on `W V` at commit 4a31a12. -/
theorem quotRadEquiv_ρRad (σ : Perm V)
    (x : (PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) :
    quotRadEquiv (ρRad σ x) = ρW σ (quotRadEquiv x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact Subtype.ext (vecMul_ρ σ y)

/-- `quotRadEquiv_ρRad` as an identity of linear maps, for the CKN quotient (arXiv:1211.1506) and
`ρW` at commit 4a31a12. -/
theorem quotRadEquiv_comp_ρRad (σ : Perm V) :
    (quotRadEquiv (V := V)).toLinearMap ∘ₗ ρRad σ = ρW σ ∘ₗ (quotRadEquiv (V := V)).toLinearMap :=
  LinearMap.ext (quotRadEquiv_ρRad σ)

/-- Basis-free CKN theorem (arXiv:1211.1506, §3.1): for `|V| = 2n` with `n ≥ 1`, the quotient of
`𝔽₂^𝓜` by the radical of the Hamiltonicity form has dimension `2^(n-1)` and is `S_V`-isomorphic
to the row space `W V` with its action `ρW` (`W`, `ρW`, `finrank_W_eq` at commit 4a31a12). -/
theorem exists_equivariant_quotRad {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Module.finrank F₂ ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) =
        2 ^ (n - 1) ∧
      ∃ φ : ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) ≃ₗ[F₂] W V,
        ∀ σ x, φ (ρRad σ x) = ρW σ (φ x) :=
  ⟨finrank_quot_rad hV hn, quotRadEquiv, quotRadEquiv_ρRad⟩

end Radical

end Pairing.PerfectMatching
