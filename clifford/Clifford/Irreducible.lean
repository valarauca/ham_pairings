import Clifford.Assembly

/-!
# C2 / T4. Absolute irreducibility (sketch §6)

* `adjoin_ρW_eq_top` : `ρ(𝔽₂ S_{2n}) = End_{𝔽₂}(W_n)`. This is Burnside's form of absolute
  irreducibility, and it survives every extension of scalars.
* `invariant_eq_bot_or_top` : every `S_{2n}`-invariant subspace of `W_n` is `0` or `W_n`.
* `nontrivial_W` and `finrank_W_eq` (COD-103) : `W_n ≠ 0` and `dim W_n = 2^(n-1)`.

The rank of `H` enters only through `finrank_W_eq`, which is proved, so no `[EXT]` input remains.
-/

namespace Pairing.PerfectMatching

open Equiv

variable (n : ℕ)

theorem nontrivial_W (hn : 1 ≤ n) : Nontrivial (W (Fin (2 * n))) :=
  Module.nontrivial_of_finrank_pos (R := F₂) (by rw [finrank_W_eq n hn]; positivity)

theorem frameAlg_le_adjoin :
    frameAlg n ≤ Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) := by
  apply Algebra.adjoin_le
  rintro x (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact Subalgebra.sum_mem _ fun a _ ↦ Algebra.subset_adjoin ⟨_, rfl⟩
  · exact Algebra.subset_adjoin ⟨_, rfl⟩

/-- T4. `ρ(𝔽₂ S_{2n}) = End(W_n)`. -/
theorem adjoin_ρW_eq_top (hn : 1 ≤ n) :
    Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) = ⊤ :=
  top_le_iff.mp (adjoin_frame_eq_top n hn ▸ frameAlg_le_adjoin n)

/-- Every endomorphism of `W_n` is a polynomial in the `ρ(σ)`, so it preserves any
`S_{2n}`-invariant subspace. -/
theorem preserves_of_invariant (hn : 1 ≤ n) (M : Submodule F₂ (W (Fin (2 * n))))
    (hM : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ M, ρW σ x ∈ M) (f : Module.End F₂ (W (Fin (2 * n)))) :
    ∀ x ∈ M, f x ∈ M := by
  have hf : f ∈ Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) := by
    rw [adjoin_ρW_eq_top n hn]
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

/-- `W_n` is irreducible. -/
theorem invariant_eq_bot_or_top (hn : 1 ≤ n) (M : Submodule F₂ (W (Fin (2 * n))))
    (hM : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ M, ρW σ x ∈ M) : M = ⊥ ∨ M = ⊤ := by
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F₂ (W (Fin (2 * n))), φ m ≠ 0 := by
    by_contra! h
    exact hm0 ((Module.forall_dual_apply_eq_zero_iff F₂ m).mp h)
  rw [eq_top_iff]
  intro x _
  have hx := preserves_of_invariant n hn M hM ((φ m)⁻¹ • φ.smulRight x) m hm
  rwa [LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ,
    one_smul] at hx

end Pairing.PerfectMatching
