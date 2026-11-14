import Clifford.LocalFour
import Clifford.LocalSix

/-!
# T1. Three-cycle annihilation (sketch §3)

Let `τ = (a b c)` and `P ∈ 𝓜`. At most one edge of `P` lies in `{a, b, c}`.

* Case 1, `ab ∈ P` up to cyclic relabelling (`sum_H_three_cycle_of_mate_eq`). With `d = P c`
  and `A = {a, b, c, d}`, the orbit `P, τP, τ²P` is `X ∪ P'` for `X` over the `⟨τ⟩`-orbit of
  `P|_A`, so L-A and L-B give parity `0`.
* Case 2, `aa', bb', cc' ∈ P` (`sum_H_three_cycle_of_cross`). With
  `A = {a, b, c, a', b', c'}`, L-A and L-C give parity `0`.

`glue_smul` and `sum_H_of_local` carry out the reduction from `P` to `P|_A` in both cases.

* `sum_H_isThreeCycle` : `H[P,Q] + H[τP,Q] + H[τ²P,Q] = 0`.
* `row_sum_isThreeCycle` : `r_P + r_{τP} + r_{τ²P} = 0`.
* `one_add_ρW_add_sq` : `I + ρ(τ) + ρ(τ)² = 0` on `W`.
-/

namespace Pairing.PerfectMatching

open Equiv

private theorem injective_vec4 {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem injective_vec6 {α : Type*} {a b c d e f : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hbf : b ≠ f) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f)
    (hef : e ≠ f) : Function.Injective ![a, b, c, d, e, f] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem swap_mul_swap_rotate {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    swap a b * swap b c = swap b c * swap c a := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> simp_all

omit [Fintype V] in
/-- `glue` intertwines `σ ∈ Perm A` with its extension to `V` by the identity. -/
theorem glue_smul (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)
    (σ : Perm A) (X : PerfectMatching A) :
    glue P A hA (σ • X) = Perm.ofSubtype σ • glue P A hA X := by
  ext v
  by_cases h : v ∈ A
  · have h' : (Perm.ofSubtype σ)⁻¹ v = σ⁻¹ ⟨v, h⟩ := by
      rw [← map_inv, Perm.ofSubtype_apply_of_mem _ h]
    rw [smul_mate, h', glue_mate_coe, Perm.ofSubtype_apply_coe, glue_mate_of_mem P A hA _ h,
      smul_mate]
  · have h' : (Perm.ofSubtype σ)⁻¹ v = v := by
      rw [← map_inv, Perm.ofSubtype_apply_of_not_mem _ h]
    have hP : P.mate v ∉ A := fun h'' ↦ h ((mate_mem_iff P A hA v).mp h'')
    rw [smul_mate, h', glue_mate_of_notMem P A hA _ h, glue_mate_of_notMem P A hA _ h,
      Perm.ofSubtype_apply_of_not_mem _ hP]

/-- Orbit parity for `P|_A` under `σ` lifts to `P` under the extension of `σ`. -/
theorem sum_H_of_local {A : Finset V} {P : PerfectMatching V} (hA : ∀ v ∈ A, P.mate v ∈ A)
    (hA0 : A.Nonempty) (σ : Perm A)
    (hloc : ∀ κ, H (restrict P A hA) κ + H (σ • restrict P A hA) κ +
      H (σ ^ 2 • restrict P A hA) κ = 0) (Q : PerfectMatching V) :
    H P Q + H (Perm.ofSubtype σ • P) Q + H (Perm.ofSubtype σ ^ 2 • P) Q = 0 := by
  have e0 : H P Q = H (glue P A hA (restrict P A hA)) Q := by rw [glue_restrict]
  have e1 : Perm.ofSubtype σ • P = glue P A hA (σ • restrict P A hA) := by
    rw [glue_smul, glue_restrict]
  have e2 : Perm.ofSubtype σ ^ 2 • P = glue P A hA (σ ^ 2 • restrict P A hA) := by
    rw [glue_smul, map_pow, glue_restrict]
  rw [e1, e2, e0]
  by_cases hC : HasClosedCycle P Q A
  · simp only [H_glue_of_hasClosedCycle P Q A hA hC hA0, add_zero]
  · rw [H_glue P Q A hA hC, H_glue P Q A hA hC, H_glue P Q A hA hC]
    exact hloc _

/-- T1, case 1, `ab ∈ P`. -/
theorem sum_H_three_cycle_of_mate_eq {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    {P : PerfectMatching V} (h : P.mate a = b) (Q : PerfectMatching V) :
    H P Q + H ((swap a b * swap b c) • P) Q + H ((swap a b * swap b c) ^ 2 • P) Q = 0 := by
  have hba : P.mate b = a := by rw [← h, mate_mate]
  have hdc : P.mate c ≠ c := P.mate_ne c
  have hda : P.mate c ≠ a := fun h' ↦ hbc (by rw [← h, ← h', mate_mate])
  have hdb : P.mate c ≠ b := fun h' ↦ hca (by rw [← hba, ← h', mate_mate])
  have hinj : Function.Injective ![a, b, c, P.mate c] :=
    injective_vec4 hab hca.symm hda.symm hbc hdb.symm hdc.symm
  set A : Finset V := Finset.univ.image ![a, b, c, P.mate c]
  have hmem : ∀ i, ![a, b, c, P.mate c] i ∈ A :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hA : ∀ v ∈ A, P.mate v ∈ A := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    fin_cases i
    · simpa [h] using hmem 1
    · simpa [hba] using hmem 0
    · simpa using hmem 3
    · simpa using hmem 2
  have hcard : Fintype.card A = 4 := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ hinj]
    simp
  let pt : Fin 4 → A := fun i ↦ ⟨_, hmem i⟩
  have hinjA : Function.Injective ![pt 0, pt 1, pt 2, pt 3] := by
    have hpt : ![pt 0, pt 1, pt 2, pt 3] = pt := by
      funext i
      fin_cases i <;> rfl
    rw [hpt]
    exact fun i j hij ↦ hinj (congrArg Subtype.val hij)
  have hσ : Perm.ofSubtype (swap (pt 0) (pt 1) * swap (pt 1) (pt 2)) = swap a b * swap b c := by
    simp [pt]
  have key := sum_H_of_local hA ⟨a, hmem 0⟩ (swap (pt 0) (pt 1) * swap (pt 1) (pt 2))
    (fun κ ↦ sum_H_orbit_four hcard hinjA (X := restrict P A hA) (Subtype.ext h) rfl κ) Q
  rwa [hσ] at key

/-- T1, case 2, `aa', bb', cc' ∈ P` with `a', b', c' ∉ {a, b, c}`. -/
theorem sum_H_three_cycle_of_cross {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    {P : PerfectMatching V} (ha : P.mate a ≠ b) (ha' : P.mate a ≠ c) (hb : P.mate b ≠ c)
    (hb' : P.mate b ≠ a) (hc : P.mate c ≠ a) (hc' : P.mate c ≠ b) (Q : PerfectMatching V) :
    H P Q + H ((swap a b * swap b c) • P) Q + H ((swap a b * swap b c) ^ 2 • P) Q = 0 := by
  have hinj : Function.Injective ![a, b, c, P.mate a, P.mate b, P.mate c] :=
    injective_vec6 hab hca.symm (P.mate_ne a).symm hb'.symm hc.symm hbc ha.symm
      (P.mate_ne b).symm hc'.symm ha'.symm hb.symm (P.mate_ne c).symm
      (P.mate.injective.ne hab) (P.mate.injective.ne hca.symm) (P.mate.injective.ne hbc)
  set A : Finset V := Finset.univ.image ![a, b, c, P.mate a, P.mate b, P.mate c]
  have hmem : ∀ i, ![a, b, c, P.mate a, P.mate b, P.mate c] i ∈ A :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hA : ∀ v ∈ A, P.mate v ∈ A := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    fin_cases i
    · simpa using hmem 3
    · simpa using hmem 4
    · simpa using hmem 5
    · simpa using hmem 0
    · simpa using hmem 1
    · simpa using hmem 2
  have hcard : Fintype.card A = 6 := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ hinj]
    simp
  let pt : Fin 6 → A := fun i ↦ ⟨_, hmem i⟩
  have hinjA : Function.Injective ![pt 0, pt 1, pt 2, pt 3, pt 4, pt 5] := by
    have hpt : ![pt 0, pt 1, pt 2, pt 3, pt 4, pt 5] = pt := by
      funext i
      fin_cases i <;> rfl
    rw [hpt]
    exact fun i j hij ↦ hinj (congrArg Subtype.val hij)
  have hσ : Perm.ofSubtype (swap (pt 0) (pt 1) * swap (pt 1) (pt 2)) = swap a b * swap b c := by
    simp [pt]
  have key := sum_H_of_local hA ⟨a, hmem 0⟩ (swap (pt 0) (pt 1) * swap (pt 1) (pt 2))
    (fun κ ↦ sum_H_orbit_six hcard hinjA (X := restrict P A hA) rfl rfl rfl κ) Q
  rwa [hσ] at key

/-- T1 for `τ = (a b c)`. -/
theorem sum_H_three_cycle {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (P Q : PerfectMatching V) :
    H P Q + H ((swap a b * swap b c) • P) Q + H ((swap a b * swap b c) ^ 2 • P) Q = 0 := by
  by_cases h1 : P.mate a = b
  · exact sum_H_three_cycle_of_mate_eq hab hbc hca h1 Q
  by_cases h2 : P.mate b = c
  · rw [swap_mul_swap_rotate hab hbc hca]
    exact sum_H_three_cycle_of_mate_eq hbc hca hab h2 Q
  by_cases h3 : P.mate c = a
  · rw [← swap_mul_swap_rotate hca hab hbc]
    exact sum_H_three_cycle_of_mate_eq hca hab hbc h3 Q
  refine sum_H_three_cycle_of_cross hab hbc hca h1 ?_ h2 ?_ h3 ?_ Q
  · intro h
    apply h3
    rw [← h, mate_mate]
  · intro h
    apply h1
    rw [← h, mate_mate]
  · intro h
    apply h2
    rw [← h, mate_mate]

/-- T1. `H[P,Q] + H[τP,Q] + H[τ²P,Q] = 0` for every three-cycle `τ`. -/
theorem sum_H_isThreeCycle {τ : Perm V} (hτ : τ.IsThreeCycle) (P Q : PerfectMatching V) :
    H P Q + H (τ • P) Q + H (τ ^ 2 • P) Q = 0 := by
  obtain ⟨a, ha⟩ : τ.support.Nonempty :=
    Finset.card_pos.mp (by rw [hτ.card_support]; norm_num)
  have hnd := hτ.nodup_iff_mem_support.mpr ha
  have hab : a ≠ τ a := fun h ↦ Perm.mem_support.mp ha h.symm
  have hbc : τ a ≠ τ (τ a) := fun h ↦ hab (τ.injective h)
  have hca : τ (τ a) ≠ a := fun h ↦ (List.nodup_cons.mp hnd).1 (by simp [h])
  rw [hτ.eq_swap_mul_swap_iff_mem_support.mpr ha]
  exact sum_H_three_cycle hab hbc hca P Q

/-- `r_P + r_{τP} + r_{τ²P} = 0`. -/
theorem row_sum_isThreeCycle {τ : Perm V} (hτ : τ.IsThreeCycle) (P : PerfectMatching V) :
    H P + H (τ • P) + H (τ ^ 2 • P) = 0 := by
  funext Q
  exact sum_H_isThreeCycle hτ P Q

/-- `f + ρ(τ) f + ρ(τ)² f = 0` for `f ∈ W`. -/
theorem ρ_isThreeCycle_apply {τ : Perm V} (hτ : τ.IsThreeCycle) {f : PerfectMatching V → F₂}
    (hf : f ∈ W V) : f + ρ τ f + ρ τ (ρ τ f) = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨P, rfl⟩ := hg
    change H P + ρ τ (H P) + ρ τ (ρ τ (H P)) = 0
    rw [ρ_row, ρ_row, ← mul_smul, ← pow_two]
    exact row_sum_isThreeCycle hτ P
  | zero => simp
  | add f g _ _ hf hg =>
    calc f + g + ρ τ (f + g) + ρ τ (ρ τ (f + g))
        = (f + ρ τ f + ρ τ (ρ τ f)) + (g + ρ τ g + ρ τ (ρ τ g)) := by
          simp only [map_add]
          abel
      _ = 0 := by rw [hf, hg, add_zero]
  | smul r f _ hf =>
    rw [map_smul, map_smul, ← smul_add, ← smul_add, hf, smul_zero]

/-- T1. `I + ρ(τ) + ρ(τ)² = 0` on `W`. -/
theorem one_add_ρW_add_sq {τ : Perm V} (hτ : τ.IsThreeCycle) :
    (1 + ρW τ + ρW τ ^ 2 : Module.End F₂ (W V)) = 0 := by
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply,
    Submodule.coe_add, ρW_apply_coe, LinearMap.zero_apply, Submodule.coe_zero]
  exact ρ_isThreeCycle_apply hτ f.2

end Pairing.PerfectMatching
