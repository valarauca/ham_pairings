import Clifford.BaseChange
import Clifford.ConceptualForm
import Mathlib.Data.Finset.NoncommProd

/-!
# M1. Clifford modules in characteristic 2

Let `k` be a field of characteristic 2 and `M` a `k`-vector space with a ring hom
`α : Cl(U_n, q) → End_k(M)`.

* `blkC a = ι(v_{2a,2a+1}) + 1` and `gapC g = ι(v_{2g+1,2g+2})` satisfy, inside `Cl(U_n, q)`,
  `blkC_sq`, `blkC_comm`, `gapC_sq`, `gapC_comm` and `blkC_mul_gapC`.
* `exists_vacuum` : a nonzero `M` has a nonzero `m₀` killed by every `blkC a`.
* `exists_injective_intertwiner` : `w_S ↦ gapProd S · m₀` embeds `k ⊗ W_n` into `M` as a
  `Cl(U_n, q)`-module.
* `exists_intertwining_equiv` : if `dim M = 2^(n-1)` then `M ≅ k ⊗ W_n` as `Cl(U_n, q)`-modules.
-/

namespace Pairing.PerfectMatching

open Equiv TensorProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `b(v_ij, v_kl) = [i = k] + [i = l] + [j = k] + [j = l]`. -/
theorem dot_v_v (i j k l : V) :
    dot (v i j) (v k l) =
      (if i = k then 1 else 0) + (if i = l then 1 else 0) + (if j = k then 1 else 0) +
        (if j = l then 1 else 0) := by
  simp only [dot, v, Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  abel

theorem eq_add_of_add_eq_F₂ {A : Type*} [AddCommGroup A] [Module F₂ A] {x y z : A}
    (h : x + y = z) : x = y + z := by
  rw [← h, add_comm x y, ← add_assoc, add_self_F₂, zero_add]

variable (n : ℕ)

/-- `Cl(U_n, q)`. -/
abbrev Cl : Type :=
  CliffordAlgebra (qForm (Fin (2 * n)))

/-- The block edge `v_{2a,2a+1}` in `U_n`. -/
def blkU (a : Fin n) : U (Fin (2 * n)) :=
  ⟨v (blockLo n a) (blockHi n a), v_mem _ _⟩

/-- The gap edge `v_{2g+1,2g+2}` in `U_n`. -/
def gapU (g : Fin (n - 1)) : U (Fin (2 * n)) :=
  ⟨v (gapLo n g) (gapHi n g), v_mem _ _⟩

/-- `blkC a = ι(v_{2a,2a+1}) + 1`. -/
def blkC (a : Fin n) : Cl n :=
  CliffordAlgebra.ι _ (blkU n a) + 1

/-- `gapC g = ι(v_{2g+1,2g+2})`. -/
def gapC (g : Fin (n - 1)) : Cl n :=
  CliffordAlgebra.ι _ (gapU n g)

theorem blockLo_ne_blockHi (a : Fin n) : blockLo n a ≠ blockHi n a :=
  Fin.ne_of_val_ne (by simp [blockLo, blockHi])

theorem gapLo_ne_gapHi (g : Fin (n - 1)) : gapLo n g ≠ gapHi n g :=
  Fin.ne_of_val_ne (by simp [gapLo, gapHi])

theorem ι_sq_one {x : U (Fin (2 * n))} (hx : qForm _ x = 1) :
    CliffordAlgebra.ι (qForm (Fin (2 * n))) x * CliffordAlgebra.ι _ x = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar, hx, map_one]

theorem ι_mul_ι_eq (x y : U (Fin (2 * n))) :
    CliffordAlgebra.ι (qForm (Fin (2 * n))) x * CliffordAlgebra.ι _ y =
      CliffordAlgebra.ι _ y * CliffordAlgebra.ι _ x +
        algebraMap F₂ (Cl n) (dot (x : Fin (2 * n) → F₂) y) := by
  rw [← polar_qForm]
  exact eq_add_of_add_eq_F₂ (CliffordAlgebra.ι_mul_ι_add_swap x y)

theorem qForm_blkU (a : Fin n) : qForm _ (blkU n a) = 1 :=
  qfun_v (blockLo_ne_blockHi n a)

theorem qForm_gapU (g : Fin (n - 1)) : qForm _ (gapU n g) = 1 :=
  qfun_v (gapLo_ne_gapHi n g)

theorem dot_blkU_blkU {a b : Fin n} (hab : a ≠ b) :
    dot (blkU n a : Fin (2 * n) → F₂) (blkU n b) = 0 := by
  have h := Fin.val_ne_of_ne hab
  simp only [blkU, dot_v_v, blockLo, blockHi, Fin.mk.injEq]
  split_ifs <;> first | decide | omega

theorem dot_gapU_gapU {g h : Fin (n - 1)} (hgh : g ≠ h) :
    dot (gapU n g : Fin (2 * n) → F₂) (gapU n h) = 0 := by
  have h' := Fin.val_ne_of_ne hgh
  simp only [gapU, dot_v_v, gapLo, gapHi, Fin.mk.injEq]
  split_ifs <;> first | decide | omega

theorem dot_blkU_gapU (a : Fin n) (g : Fin (n - 1)) :
    dot (blkU n a : Fin (2 * n) → F₂) (gapU n g) =
      if (g : ℕ) = a ∨ (g : ℕ) + 1 = a then 1 else 0 := by
  simp only [blkU, gapU, dot_v_v, blockLo, blockHi, gapLo, gapHi, Fin.mk.injEq]
  split_ifs <;> first | decide | omega

theorem blkC_sq (a : Fin n) : blkC n a * blkC n a = 0 := by
  rw [blkC, add_mul, mul_add, mul_add, ι_sq_one n (qForm_blkU n a), mul_one, one_mul, mul_one]
  calc (1 : Cl n) + CliffordAlgebra.ι _ (blkU n a) + (CliffordAlgebra.ι _ (blkU n a) + 1)
      = (CliffordAlgebra.ι _ (blkU n a) + CliffordAlgebra.ι _ (blkU n a)) + (1 + 1) := by abel
    _ = 0 := by rw [add_self_F₂, add_self_F₂, add_zero]

theorem blkC_comm (a b : Fin n) : Commute (blkC n a) (blkC n b) := by
  by_cases hab : a = b
  · rw [hab]
  have h := ι_mul_ι_eq n (blkU n a) (blkU n b)
  rw [dot_blkU_blkU n hab, map_zero, add_zero] at h
  exact ((show Commute _ _ from h).add_right (Commute.one_right _)).add_left (Commute.one_left _)

theorem gapC_sq (g : Fin (n - 1)) : gapC n g * gapC n g = 1 :=
  ι_sq_one n (qForm_gapU n g)

theorem gapC_comm (g h : Fin (n - 1)) : Commute (gapC n g) (gapC n h) := by
  by_cases hgh : g = h
  · rw [hgh]
  have e := ι_mul_ι_eq n (gapU n g) (gapU n h)
  rw [dot_gapU_gapU n hgh, map_zero, add_zero] at e
  exact e

/-- `blkC a · gapC g = gapC g · blkC a + [g adjacent to a]`. -/
theorem blkC_mul_gapC (a : Fin n) (g : Fin (n - 1)) :
    blkC n a * gapC n g =
      gapC n g * blkC n a + if (g : ℕ) = a ∨ (g : ℕ) + 1 = a then 1 else 0 := by
  have h := ι_mul_ι_eq n (blkU n a) (gapU n g)
  rw [dot_blkU_gapU, apply_ite (algebraMap F₂ (Cl n)), map_one, map_zero] at h
  rw [blkC, gapC, add_mul, h, mul_add, one_mul, mul_one]
  abel

/-- `gapProd S = ∏_{g ∈ S} gapC g`. -/
def gapProd (S : Finset (Fin (n - 1))) : Cl n :=
  S.noncommProd (gapC n) (fun g _ h _ _ ↦ gapC_comm n g h)

theorem gapProd_empty : gapProd n ∅ = 1 :=
  Finset.noncommProd_empty _ _

theorem gapProd_insert {g : Fin (n - 1)} {S : Finset (Fin (n - 1))} (hg : g ∉ S) :
    gapProd n (insert g S) = gapC n g * gapProd n S :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hg

theorem gapC_mul_gapProd (g : Fin (n - 1)) (S : Finset (Fin (n - 1))) :
    gapC n g * gapProd n S = gapProd n (symmDiff {g} S) := by
  by_cases hg : g ∈ S
  · have hS : S = insert g (S.erase g) := (Finset.insert_erase hg).symm
    conv_lhs => rw [hS]
    rw [gapProd_insert n (Finset.notMem_erase g S), ← mul_assoc, gapC_sq, one_mul]
    congr 1
    ext x
    by_cases hx : x = g
    · subst hx
      simp [Finset.mem_symmDiff, hg]
    · simp [Finset.mem_symmDiff, hx]
  · rw [symmDiff_single_of_notMem n hg, gapProd_insert n hg]

/-- `blkC a · F_S = F_S · blkC a + ∑_{g ∈ S adjacent to a} F_{S \ g}`. -/
theorem blkC_mul_gapProd (a : Fin n) (S : Finset (Fin (n - 1))) :
    blkC n a * gapProd n S = gapProd n S * blkC n a +
      ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a),
        gapProd n (S.erase g) := by
  induction S using Finset.induction_on with
  | empty => simp [gapProd_empty]
  | insert g S hg ih =>
    have herase : ∀ h ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a),
        gapProd n ((insert g S).erase h) = gapC n g * gapProd n (S.erase h) := by
      intro h hh
      have hne : g ≠ h := fun e ↦ hg (e ▸ (Finset.mem_filter.mp hh).1)
      rw [Finset.erase_insert_of_ne hne,
        gapProd_insert n (fun m ↦ hg (Finset.mem_of_mem_erase m))]
    rw [gapProd_insert n hg, ← mul_assoc, blkC_mul_gapC, add_mul, mul_assoc, ih, mul_add,
      ← mul_assoc, Finset.filter_insert]
    split_ifs with hadj
    · rw [Finset.sum_insert (fun m ↦ hg (Finset.mem_filter.mp m).1), Finset.erase_insert hg,
        Finset.sum_congr rfl herase, ← Finset.mul_sum, one_mul]
      abel
    · rw [Finset.sum_congr rfl herase, ← Finset.mul_sum, zero_mul, add_zero]

section Vacuum

variable {n} {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  (α : Cl n →+* Module.End k M)

/-- `m` is a vacuum vector when every `blkC a` kills it. -/
def IsVacuum (m : M) : Prop :=
  ∀ a, α (blkC n a) m = 0

theorem blkC_gapProd_apply {m : M} (hm : IsVacuum α m) (a : Fin n) (S : Finset (Fin (n - 1))) :
    α (blkC n a) (α (gapProd n S) m) =
      ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a),
        α (gapProd n (S.erase g)) m := by
  rw [← Module.End.mul_apply, ← map_mul, blkC_mul_gapProd, map_add, map_mul, LinearMap.add_apply,
    Module.End.mul_apply, hm a, map_zero, zero_add, map_sum, LinearMap.sum_apply]

/-- A nonzero module has a nonzero vacuum vector. -/
theorem exists_vacuum [Nontrivial M] : ∃ m : M, m ≠ 0 ∧ IsVacuum α m := by
  have key : ∀ j ≤ n, ∃ m : M, m ≠ 0 ∧ ∀ a : Fin n, (a : ℕ) < j → α (blkC n a) m = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      exact ⟨m, hm, fun a ha ↦ absurd ha (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨m, hm0, hm⟩ := ih (by omega)
      have hsplit : ∀ a : Fin n, (a : ℕ) < j + 1 → (a : ℕ) < j ∨ a = ⟨j, hj⟩ := by
        intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      by_cases hb : α (blkC n ⟨j, hj⟩) m = 0
      · refine ⟨m, hm0, fun a ha ↦ ?_⟩
        rcases hsplit a ha with h | rfl
        · exact hm a h
        · exact hb
      · refine ⟨α (blkC n ⟨j, hj⟩) m, hb, fun a ha ↦ ?_⟩
        rcases hsplit a ha with h | rfl
        · rw [← Module.End.mul_apply, ← map_mul, (blkC_comm n a ⟨j, hj⟩).eq, map_mul,
            Module.End.mul_apply, hm a h, map_zero]
        · rw [← Module.End.mul_apply, ← map_mul, blkC_sq, map_zero, LinearMap.zero_apply]
  obtain ⟨m, hm0, hm⟩ := key n le_rfl
  exact ⟨m, hm0, fun a ↦ hm a a.isLt⟩

end Vacuum

/-- The base vertex `0` of `Fin (2n)`. -/
def base (hn : 1 ≤ n) : Fin (2 * n) :=
  ⟨0, by omega⟩

section Embed

variable (k : Type*) [Field k] [Algebra F₂ k] (hn : 1 ≤ n)
  {M : Type*} [AddCommGroup M] [Module k M] (α : Cl n →+* Module.End k M)

/-- `Cl(U_n, q)` acting on `k ⊗ W_n`. -/
def cliffordRepK : Cl n →+* Module.End k (k ⊗[F₂] W (Fin (2 * n))) :=
  ((Module.End.baseChangeHom F₂ k (W (Fin (2 * n)))).comp (cliffordRep (base n hn))).toRingHom

theorem cliffordRepK_apply (x : Cl n) :
    cliffordRepK n k hn x = (cliffordRep (base n hn) x).baseChange k :=
  rfl

theorem cliffordRepK_gapC (g : Fin (n - 1)) (S : Finset (Fin (n - 1))) :
    cliffordRepK n k hn (gapC n g) (1 ⊗ₜ w n S) = 1 ⊗ₜ w n (symmDiff {g} S) := by
  rw [cliffordRepK_apply, gapC, gapU, cliffordRep_ι_v _ (gapLo_ne_gapHi n g), Γ_gap,
    LinearMap.baseChange_tmul, ρW_sigma_w]

theorem cliffordRepK_isVacuum : IsVacuum (cliffordRepK n k hn) (1 ⊗ₜ w n ∅) := by
  intro a
  rw [cliffordRepK_apply, blkC, map_add, map_one, blkU,
    cliffordRep_ι_v _ (blockLo_ne_blockHi n a), LinearMap.baseChange_tmul, LinearMap.add_apply,
    Module.End.one_apply, w_empty]
  change (1 : k) ⊗ₜ (B n a (rowW (P0 n)) + rowW (P0 n)) = 0
  rw [B_rowW_P0, W_add_self, tmul_zero]

theorem cliffordRepK_gapProd (S : Finset (Fin (n - 1))) :
    cliffordRepK n k hn (gapProd n S) (1 ⊗ₜ w n ∅) = 1 ⊗ₜ w n S := by
  induction S using Finset.induction_on with
  | empty => rw [gapProd_empty, map_one, Module.End.one_apply]
  | insert g S hg ih =>
    rw [gapProd_insert n hg, map_mul, Module.End.mul_apply, ih, cliffordRepK_gapC,
      symmDiff_single_of_notMem n hg]

/-- `w_S ↦ gapProd S · m₀`. -/
noncomputable def embed (m₀ : M) : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M :=
  ((wBasis n hn).baseChange k).constr k fun S ↦ α (gapProd n S) m₀

theorem embed_tmul_w (m₀ : M) (S : Finset (Fin (n - 1))) :
    embed n k hn α m₀ (1 ⊗ₜ w n S) = α (gapProd n S) m₀ := by
  have h := ((wBasis n hn).baseChange k).constr_basis k (fun S ↦ α (gapProd n S) m₀) S
  rwa [Module.Basis.baseChange_apply, wBasis_apply] at h

/-- `φ` intertwines `x`. -/
def Intertwines (φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M) (x : Cl n) : Prop :=
  φ ∘ₗ cliffordRepK n k hn x = α x ∘ₗ φ

variable {n k hn α}

theorem Intertwines.add {φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M} {x y : Cl n}
    (hx : Intertwines n k hn α φ x) (hy : Intertwines n k hn α φ y) :
    Intertwines n k hn α φ (x + y) := by
  rw [Intertwines, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

theorem Intertwines.mul {φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M} {x y : Cl n}
    (hx : Intertwines n k hn α φ x) (hy : Intertwines n k hn α φ y) :
    Intertwines n k hn α φ (x * y) := by
  rw [Intertwines, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]

theorem Intertwines.algebraMap (φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M) (r : F₂) :
    Intertwines n k hn α φ (algebraMap F₂ (Cl n) r) := by
  rcases f2_cases r with rfl | rfl
  · rw [Intertwines, map_zero, map_zero, map_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  · rw [Intertwines, map_one, map_one, map_one, Module.End.one_eq_id, Module.End.one_eq_id,
      LinearMap.comp_id, LinearMap.id_comp]

theorem Intertwines.zero (φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M) : Intertwines n k hn α φ 0 := by
  simpa using Intertwines.algebraMap (hn := hn) (α := α) φ 0

theorem Intertwines.one (φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M) : Intertwines n k hn α φ 1 := by
  simpa using Intertwines.algebraMap (hn := hn) (α := α) φ 1

omit [Algebra F₂ k] in
theorem v_trans {V : Type*} [DecidableEq V] (i j l : V) : v i j + v j l = v i l := by
  funext x
  simp only [v, Pi.add_apply]
  rw [add_assoc, ← add_assoc (Pi.single j 1 x), CharTwo.add_self_eq_zero, zero_add]

/-- Intertwining the block and gap generators gives intertwining of all of `Cl(U_n, q)`. -/
theorem intertwines_of_generators {φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M}
    (hblk : ∀ a, Intertwines n k hn α φ (blkC n a))
    (hgap : ∀ g, Intertwines n k hn α φ (gapC n g)) (x : Cl n) : Intertwines n k hn α φ x := by
  have hadj : ∀ t (ht : t + 1 < 2 * n), Intertwines n k hn α φ
      (CliffordAlgebra.ι _ ⟨v (⟨t, by omega⟩ : Fin (2 * n)) ⟨t + 1, ht⟩, v_mem _ _⟩) := by
    intro t ht
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' t
    · have e : CliffordAlgebra.ι (qForm (Fin (2 * n)))
          ⟨v (⟨2 * a, by omega⟩ : Fin (2 * n)) ⟨2 * a + 1, ht⟩, v_mem _ _⟩ =
            blkC n ⟨a, by omega⟩ + 1 := by
        rw [blkC, add_assoc, add_self_F₂ (1 : Cl n), add_zero]
        rfl
      rw [e]
      exact (hblk _).add (Intertwines.one φ)
    · exact hgap ⟨a, by omega⟩
  have h0 : ∀ j (hj : j < 2 * n), Intertwines n k hn α φ
      (CliffordAlgebra.ι _ ⟨v (base n hn) ⟨j, hj⟩, v_mem _ _⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [show (⟨v (base n hn) ⟨0, hj⟩, v_mem _ _⟩ : U (Fin (2 * n))) = 0 from
        Subtype.ext (v_self _), map_zero]
      exact Intertwines.zero φ
    | succ j ih =>
      intro hj
      have e : (⟨v (base n hn) ⟨j + 1, hj⟩, v_mem _ _⟩ : U (Fin (2 * n))) =
          ⟨v (base n hn) ⟨j, by omega⟩, v_mem _ _⟩ + ⟨v ⟨j, by omega⟩ ⟨j + 1, hj⟩, v_mem _ _⟩ :=
        Subtype.ext (v_trans _ _ _).symm
      rw [e, map_add]
      exact (ih (by omega)).add (hadj j hj)
  have hι : ∀ u : U (Fin (2 * n)), Intertwines n k hn α φ (CliffordAlgebra.ι _ u) := by
    rintro ⟨u, hu⟩
    have hu' := hu
    rw [U_eq_span (base n hn)] at hu'
    induction hu' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact h0 j j.2
    | zero =>
      rw [show (⟨0, hu⟩ : U (Fin (2 * n))) = 0 from rfl, map_zero]
      exact Intertwines.zero φ
    | add a b ha hb iha ihb =>
      rw [show (⟨a + b, hu⟩ : U (Fin (2 * n))) =
          ⟨a, (U_eq_span (base n hn)) ▸ ha⟩ + ⟨b, (U_eq_span (base n hn)) ▸ hb⟩ from rfl,
        map_add]
      exact (iha _).add (ihb _)
    | smul c a ha iha =>
      rcases f2_cases c with rfl | rfl
      · rw [show (⟨(0 : F₂) • a, hu⟩ : U (Fin (2 * n))) = 0 from Subtype.ext (zero_smul _ _),
          map_zero]
        exact Intertwines.zero φ
      · rw [show (⟨(1 : F₂) • a, hu⟩ : U (Fin (2 * n))) =
            ⟨a, (U_eq_span (base n hn)) ▸ ha⟩ from Subtype.ext (one_smul _ _)]
        exact iha _
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact Intertwines.algebraMap φ r
  | ι u => exact hι u
  | mul x y hx hy => exact hx.mul hy
  | add x y hx hy => exact hx.add hy

variable (n k hn α)

theorem embed_intertwines {m₀ : M} (hm : IsVacuum α m₀) (x : Cl n) :
    Intertwines n k hn α (embed n k hn α m₀) x := by
  have hb : ∀ S, (wBasis n hn).baseChange k S = (1 : k) ⊗ₜ w n S := fun S ↦ by
    rw [Module.Basis.baseChange_apply, wBasis_apply]
  refine intertwines_of_generators (fun a ↦ ?_) (fun g ↦ ?_) x
  · refine ((wBasis n hn).baseChange k).ext fun S ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hb, embed_tmul_w, blkC_gapProd_apply α hm,
      ← cliffordRepK_gapProd n k hn S,
      blkC_gapProd_apply (cliffordRepK n k hn) (cliffordRepK_isVacuum n k hn), map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [cliffordRepK_gapProd, embed_tmul_w]
  · refine ((wBasis n hn).baseChange k).ext fun S ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hb, cliffordRepK_gapC, embed_tmul_w,
      embed_tmul_w, ← Module.End.mul_apply, ← map_mul, gapC_mul_gapProd]

theorem embed_injective {m₀ : M} (hm0 : m₀ ≠ 0) (hm : IsVacuum α m₀) :
    Function.Injective (embed n k hn α m₀) := by
  set φ := embed n k hn α m₀ with hφ
  have hinv : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ LinearMap.ker φ, ρK n k σ x ∈ LinearMap.ker φ := by
    intro σ x hx
    obtain ⟨y, hy⟩ := cliffordRep_surjective n hn (base n hn) (ρW σ)
    rw [LinearMap.mem_ker] at hx ⊢
    have e : ρK n k σ = cliffordRepK n k hn y := by rw [ρK, cliffordRepK_apply, hy]
    rw [e, ← LinearMap.comp_apply, embed_intertwines n k hn α hm y, LinearMap.comp_apply, hx,
      map_zero]
  rcases ρK_invariant_eq_bot_or_top n k hn (LinearMap.ker φ) hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exfalso
    apply hm0
    have hmem : ((1 : k) ⊗ₜ w n ∅ : k ⊗[F₂] W (Fin (2 * n))) ∈ LinearMap.ker φ :=
      h ▸ Submodule.mem_top
    rwa [LinearMap.mem_ker, hφ, embed_tmul_w, gapProd_empty, map_one, Module.End.one_apply]
      at hmem

/-- Every nonzero `Cl(U_n, q)`-module over a field of characteristic 2 contains `k ⊗ W_n`. -/
theorem exists_injective_intertwiner [Nontrivial M] :
    ∃ φ : k ⊗[F₂] W (Fin (2 * n)) →ₗ[k] M, Function.Injective φ ∧
      ∀ x : Cl n, φ ∘ₗ cliffordRepK n k hn x = α x ∘ₗ φ := by
  obtain ⟨m₀, hm0, hm⟩ := exists_vacuum α
  exact ⟨embed n k hn α m₀, embed_injective n k hn α hm0 hm, embed_intertwines n k hn α hm⟩

include hn in
theorem finrank_baseChange_W :
    Module.finrank k (k ⊗[F₂] W (Fin (2 * n))) = 2 ^ (n - 1) := by
  rw [Module.finrank_eq_card_basis ((wBasis n hn).baseChange k)]
  simp

/-- A `Cl(U_n, q)`-module of dimension `2^(n-1)` over a field of characteristic 2 is
`k ⊗ W_n`. -/
theorem exists_intertwining_equiv [FiniteDimensional k M]
    (hM : Module.finrank k M = 2 ^ (n - 1)) :
    ∃ e : k ⊗[F₂] W (Fin (2 * n)) ≃ₗ[k] M,
      ∀ x : Cl n, e.toLinearMap ∘ₗ cliffordRepK n k hn x = α x ∘ₗ e.toLinearMap := by
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (by rw [hM]; positivity)
  have : FiniteDimensional k (k ⊗[F₂] W (Fin (2 * n))) :=
    Module.Finite.of_basis ((wBasis n hn).baseChange k)
  obtain ⟨φ, hinj, hφ⟩ := exists_injective_intertwiner n k hn α
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hM, finrank_baseChange_W n k hn])).mp hinj
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, hφ⟩

end Embed

end Pairing.PerfectMatching
