import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.NoncommRing

/-!
# M4. Ordered monomials

Let `T_0, …, T_{m-1}` in a ring satisfy `T_j² = -1` and `T_i T_j + T_j T_i ∈ ℤ`. Then the
`ℤ`-span of the ordered monomials `T_{i₁} ⋯ T_{iᵣ}`, `i₁ < ⋯ < iᵣ`, is closed under left
multiplication by every `T_t` (`T_mul_mem_monoSpan`). This is the finiteness input for the
existence of lattices.
-/

namespace Pairing

variable {A : Type*} [Ring A] {m : ℕ} (T : Fin m → A)

/-- The ordered monomial `T_{i₁} ⋯ T_{iᵣ}` for `S = {i₁ < ⋯ < iᵣ}`. -/
def mono (S : Finset (Fin m)) : A :=
  ((S.sort (· ≤ ·)).map T).prod

theorem mono_empty : mono T ∅ = 1 := by
  simp [mono]

theorem mono_insert {a : Fin m} {S : Finset (Fin m)} (h : ∀ x ∈ S, a < x) :
    mono T (insert a S) = T a * mono T S := by
  rw [mono, Finset.sort_insert (· ≤ ·) (fun b hb ↦ (h b hb).le) (fun ha ↦ lt_irrefl a (h a ha)),
    List.map_cons, List.prod_cons]
  rfl

/-- The `ℤ`-span of the ordered monomials supported in `U`. -/
def monoSpan (U : Finset (Fin m)) : Submodule ℤ A :=
  Submodule.span ℤ {x | ∃ S ⊆ U, x = mono T S}

theorem mono_mem_monoSpan {S U : Finset (Fin m)} (h : S ⊆ U) : mono T S ∈ monoSpan T U :=
  Submodule.subset_span ⟨S, h, rfl⟩

theorem monoSpan_mono {U U' : Finset (Fin m)} (h : U ⊆ U') : monoSpan T U ≤ monoSpan T U' :=
  Submodule.span_mono fun _ ⟨S, hS, e⟩ ↦ ⟨S, hS.trans h, e⟩

theorem T_mul_mem_monoSpan_of_lt {a : Fin m} {U : Finset (Fin m)} (ha : ∀ x ∈ U, a < x)
    {y : A} (hy : y ∈ monoSpan T U) : T a * y ∈ monoSpan T (insert a U) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    rw [← mono_insert T fun x hx ↦ ha x (hS hx)]
    exact mono_mem_monoSpan T (Finset.insert_subset_insert a hS)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

variable {T}

theorem T_mul_mono_mem (h1 : ∀ j, T j * T j = -1) (h2 : ∀ i j, ∃ g : ℤ, T i * T j + T j * T i = g)
    (S : Finset (Fin m)) : ∀ t, T t * mono T S ∈ monoSpan T (insert t S) := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro t
    rw [mono_empty, mul_one, show T t = mono T {t} by
      rw [show ({t} : Finset (Fin m)) = insert t ∅ from rfl, mono_insert T (by simp), mono_empty,
        mul_one]]
    exact mono_mem_monoSpan T (by simp)
  | insert a S ha ih =>
    intro t
    rw [mono_insert T ha]
    rcases lt_trichotomy t a with hlt | rfl | hgt
    · have hall : ∀ x ∈ insert a S, t < x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hlt
        · exact hlt.trans (ha x hx)
      rw [← mono_insert T ha, ← mono_insert T hall]
      exact mono_mem_monoSpan T le_rfl
    · rw [← mul_assoc, h1, neg_one_mul]
      exact neg_mem (mono_mem_monoSpan T (by
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
    · obtain ⟨g, hg⟩ := h2 t a
      have e : T t * (T a * mono T S) = -(T a * (T t * mono T S)) + g • mono T S := by
        rw [zsmul_eq_mul, ← mul_assoc, eq_sub_of_add_eq hg]
        noncomm_ring
      rw [e]
      refine add_mem (neg_mem ?_) (Submodule.smul_mem _ g (mono_mem_monoSpan T (by
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
      have hU : ∀ x ∈ insert t S, a < x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hgt
        · exact ha x hx
      have := T_mul_mem_monoSpan_of_lt T hU (ih t)
      rwa [Finset.insert_comm] at this

/-- The `ℤ`-span of all ordered monomials is closed under left multiplication by each `T_t`. -/
theorem T_mul_mem_monoSpan (h1 : ∀ j, T j * T j = -1)
    (h2 : ∀ i j, ∃ g : ℤ, T i * T j + T j * T i = g) (t : Fin m) {y : A}
    (hy : y ∈ monoSpan T Finset.univ) : T t * y ∈ monoSpan T Finset.univ := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, -, rfl⟩ := hx
    exact monoSpan_mono T (Finset.subset_univ _) (T_mul_mono_mem h1 h2 S t)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end Pairing
