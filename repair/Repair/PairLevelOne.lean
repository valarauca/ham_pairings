import Repair.PairFormula

/-!
# The level-1 eigenprojection of `H` (Theorem 1, `ν = (e - 1, 1)`)

Source: `results/hybrid-pair-averaged.md` (aed6f2d), §2, Theorem 1.

`|W| = 2e` with `e ≥ 2`. `shared2 A C = #{x : A(x) = C(x)} = 2 l(A, C)`, twice the number of
shared edges. The level-1 kernel is `E₁(A, B) = (sh(A, B) - 2e/(2e - 1)) / (4 (e - 1) (2e - 5)!!)`
with `sh = shared2`. In the source it is the projection onto `V_{(e-1,1)}`, the edge-sum
functions orthogonal to the constants. Only the properties below are proved here, not the
identification of its range with `V_{(e-1,1)}`.

* `card_mate_eq_doubleFactorial` : `#{C : C(x) = y} = (2e - 3)!!`, and
  `card_mate_mate_eq_doubleFactorial` : two disjoint edges lie in `(2e - 5)!!` matchings.
* `sum_shared2` : `Σ_C sh(A, C) = 2e (2e - 3)!!`.
* `sum_shared2_mul` :
  `Σ_C sh(A, C) sh(C, B) = 2 sh(A, B) (2e - 3)!! + (2e(2e - 4) + 2 sh(A, B)) (2e - 5)!!`.
* `sum_hamInd_shared2` : `Σ_C h(A, C) sh(C, B) = (2e - sh(A, B)) |Ham(A)| / (2e - 2)`.
* `levelOneKer_comm`, `levelOneKer_mul_self`, `sum_levelOneKer`, `hamMat_levelOneKer`,
  `levelOneKer_self`, `sum_levelOneKer_self`, `levelOneKer_omega` : `E₁` is a symmetric
  idempotent orthogonal to the constants,
  `H E₁ = -|Ham(A)|/(2(e - 1)) E₁` (and `|Ham(A)| = |Ham(B)|` by `hamDeg_eq`), and
  `E₁(A, A) = e(2e - 3)/|PM|`. So `d = tr E₁ = e(2e - 3)` and `ω((e)) = -1/(2(e - 1))`, and
  `ω(A, B) = |PM| E₁(A, B)/d = ((2e - 1) l - e)/(2e(e - 1))`.
* `levelOne_term` : the level-1 term `(|PM| / |Ham(B)|²) λ₁² E₁(A, B)` of `h(A, B)/p²` is
  `L₁(l(A, B))`.
-/

open Finset

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `sh(A, C) = #{x : A(x) = C(x)} = 2 l(A, C)`, twice the number of shared edges
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
def shared2 (A C : PerfectMatching W) : ℕ :=
  #{x | A.mate x = C.mate x}

/-- `sh(A, C) = sh(C, A)` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem shared2_comm (A C : PerfectMatching W) : shared2 A C = shared2 C A := by
  simp only [shared2, eq_comm]

/-- The matchings containing the edge `xy` correspond to the matchings of `V ∖ {x, y}`, and a
predicate `Q` transported along the correspondence is counted the same
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_mate_and (F : PerfectMatching W) {x y : W} (hxy : x ≠ y)
    (Q : PerfectMatching W → Prop) [DecidablePred Q]
    (Q' : PerfectMatching (redSet x y) → Prop) [DecidablePred Q']
    (hQ : ∀ C (h : C.mate x = y), Q C ↔ Q' (restrict C (redSet x y) (mate_mem_redSet_of h))) :
    #{C : PerfectMatching W | C.mate x = y ∧ Q C} = #{X : PerfectMatching (redSet x y) | Q' X} := by
  have hK := switch_mem_redSet F hxy
  refine card_bij' (fun C hC ↦ restrict C (redSet x y)
      (mate_mem_redSet_of (mem_filter.mp hC).2.1))
    (fun X _ ↦ glue (switch F x y) (redSet x y) hK X) ?_ ?_ ?_ ?_
  · intro C hC
    obtain ⟨-, hCx, hQC⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨mem_univ _, (hQ C hCx).mp hQC⟩
  · intro X hX
    have hv : x ∉ redSet x y := fun h ↦ (mem_redSet.mp h).1 rfl
    have hgv : (glue (switch F x y) (redSet x y) hK X).mate x = y := by
      rw [glue_mate_of_notMem _ _ hK X hv, switch_mate_self F hxy]
    have hr : restrict (glue (switch F x y) (redSet x y) hK X) (redSet x y)
        (mate_mem_redSet_of hgv) = X := restrict_glue _ _ hK X
    refine mem_filter.mpr ⟨mem_univ _, hgv, (hQ _ hgv).mpr ?_⟩
    rw [hr]
    exact (mem_filter.mp hX).2
  · intro C hC
    have hCx := (mem_filter.mp hC).2.1
    have hCy : C.mate y = x := by rw [← hCx, mate_mate]
    ext z
    by_cases hz : z ∈ redSet x y
    · rw [glue_mate_of_mem _ _ hK _ hz]
      rfl
    · rw [glue_mate_of_notMem _ _ hK _ hz]
      rw [mem_redSet] at hz
      by_cases hzx : z = x
      · rw [hzx, switch_mate_self F hxy, hCx]
      · have hzy : z = y := by tauto
        rw [hzy, switch_mate_right F hxy, hCy]
  · intro X _
    exact restrict_glue _ _ hK X

/-- `|V ∖ {x, y}| = |V| - 2` as a type (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_redSet_coe {x y : W} (hxy : x ≠ y) :
    Fintype.card (redSet x y) = Fintype.card W - 2 := by
  rw [Fintype.card_coe, card_redSet hxy]

/-- `#{C : C(x) = y} = |PM(V ∖ {x, y})|` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_mate_eq (F : PerfectMatching W) {x y : W} (hxy : x ≠ y) :
    #{C : PerfectMatching W | C.mate x = y} = Fintype.card (PerfectMatching (redSet x y)) := by
  have h := card_mate_and F hxy (fun _ ↦ True) (fun _ ↦ True) fun _ _ ↦ Iff.rfl
  simp only [and_true] at h
  rw [h, filter_true_of_mem fun _ _ ↦ trivial, card_univ]

/-- Two disjoint edges `xx'` and `yy'` lie in `|PM(V ∖ {x, x', y, y'})|` matchings
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_mate_mate_eq (F : PerfectMatching W) {x x' y y' : W} (hx : x ≠ x') (hy : y ≠ y')
    (hyx : y ≠ x) (hyx' : y ≠ x') (hy'x : y' ≠ x) (hy'x' : y' ≠ x') :
    #{C : PerfectMatching W | C.mate x = x' ∧ C.mate y = y'} =
      Fintype.card (PerfectMatching (redSet (⟨y, mem_redSet.mpr ⟨hyx, hyx'⟩⟩ : redSet x x')
        ⟨y', mem_redSet.mpr ⟨hy'x, hy'x'⟩⟩)) := by
  set Y : redSet x x' := ⟨y, mem_redSet.mpr ⟨hyx, hyx'⟩⟩
  set Y' : redSet x x' := ⟨y', mem_redSet.mpr ⟨hy'x, hy'x'⟩⟩
  have hYY : Y ≠ Y' := fun h ↦ hy (congrArg Subtype.val h)
  rw [card_mate_and F hx (fun C ↦ C.mate y = y') (fun X ↦ X.mate Y = Y') fun C h ↦ by
    rw [Subtype.ext_iff]
    rfl]
  exact card_mate_eq (red F hx) hYY

omit [Fintype W] [DecidableEq W] in
/-- `[p] [q] = [p ∧ q]` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem ite_one_mul_ite_one (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : ℕ)) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

section Count

variable {e : ℕ} (hW : Fintype.card W = 2 * e) (he : 2 ≤ e)
include hW he

/-- `#{C : C(x) = y} = (2e - 3)!!` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_mate_eq_doubleFactorial (F : PerfectMatching W) {x y : W} (hxy : x ≠ y) :
    #{C : PerfectMatching W | C.mate x = y} = (2 * e - 3).doubleFactorial := by
  rw [card_mate_eq F hxy,
    card_eq_doubleFactorial (n := e - 1) (by rw [card_redSet_coe hxy, hW]; omega)]
  congr 1
  omega

/-- Two disjoint edges lie in `(2e - 5)!!` matchings (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem card_mate_mate_eq_doubleFactorial (F : PerfectMatching W) {x x' y y' : W} (hx : x ≠ x')
    (hy : y ≠ y') (hyx : y ≠ x) (hyx' : y ≠ x') (hy'x : y' ≠ x) (hy'x' : y' ≠ x') :
    #{C : PerfectMatching W | C.mate x = x' ∧ C.mate y = y'} = (2 * e - 5).doubleFactorial := by
  rw [card_mate_mate_eq F hx hy hyx hyx' hy'x hy'x', card_eq_doubleFactorial (n := e - 2)]
  · congr 1
    omega
  · rw [card_redSet_coe (fun h ↦ hy (congrArg Subtype.val h)), card_redSet_coe hx, hW]
    omega

/-- `Σ_C sh(A, C) = 2e (2e - 3)!!` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem sum_shared2 (A : PerfectMatching W) :
    ∑ C, shared2 A C = 2 * e * (2 * e - 3).doubleFactorial := by
  simp only [shared2, card_filter]
  rw [sum_comm]
  have h : ∀ x, ∑ C : PerfectMatching W, (if A.mate x = C.mate x then 1 else 0) =
      (2 * e - 3).doubleFactorial := by
    intro x
    rw [← card_filter]
    simp_rw [eq_comm (a := A.mate x)]
    exact card_mate_eq_doubleFactorial hW he A (A.mate_ne x).symm
  rw [sum_congr rfl fun x _ ↦ h x, sum_const, card_univ, hW, smul_eq_mul]

/-- For fixed `x`, `Σ_y #{C : C(x) = A(x), C(y) = B(y)}`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem sum_card_mate_mate (A B : PerfectMatching W) (x : W) :
    ∑ y, #{C : PerfectMatching W | C.mate x = A.mate x ∧ C.mate y = B.mate y} =
      2 * (if B.mate x = A.mate x then (2 * e - 3).doubleFactorial else 0) +
        (2 * e - 4 + 2 * (if B.mate x = A.mate x then 1 else 0)) *
          (2 * e - 5).doubleFactorial := by
  have hxx' : x ≠ A.mate x := (A.mate_ne x).symm
  have hBx : ∀ y, B.mate y = x ↔ y = B.mate x :=
    fun y ↦ ⟨fun h ↦ by rw [← h, mate_mate], fun h ↦ by rw [h, mate_mate]⟩
  have hBx' : ∀ y, B.mate y = A.mate x ↔ y = B.mate (A.mate x) :=
    fun y ↦ ⟨fun h ↦ by rw [← h, mate_mate], fun h ↦ by rw [h, mate_mate]⟩
  have hfx : #{C : PerfectMatching W | C.mate x = A.mate x ∧ C.mate x = B.mate x} =
      if B.mate x = A.mate x then (2 * e - 3).doubleFactorial else 0 := by
    split_ifs with h
    · rw [← card_mate_eq_doubleFactorial hW he A hxx']
      congr 1
      ext C
      simp only [mem_filter, mem_univ, true_and, h, and_self]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro C - ⟨h1, h2⟩
      exact h (h2 ▸ h1)
  have hfx' : #{C : PerfectMatching W | C.mate x = A.mate x ∧
      C.mate (A.mate x) = B.mate (A.mate x)} =
      if B.mate x = A.mate x then (2 * e - 3).doubleFactorial else 0 := by
    split_ifs with h
    · rw [← card_mate_eq_doubleFactorial hW he A hxx']
      congr 1
      ext C
      simp only [mem_filter, mem_univ, true_and, and_iff_left_iff_imp]
      intro hC
      rw [← hC, mate_mate, hC, ← h, mate_mate]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro C - ⟨h1, h2⟩
      apply h
      have h3 : B.mate (A.mate x) = x := by rw [← h2, ← h1, mate_mate]
      calc B.mate x = B.mate (B.mate (A.mate x)) := by rw [h3]
        _ = A.mate x := mate_mate _ _
  have hfy : ∀ y ∈ (univ.erase x).erase (A.mate x),
      #{C : PerfectMatching W | C.mate x = A.mate x ∧ C.mate y = B.mate y} =
        if B.mate y = x ∨ B.mate y = A.mate x then 0 else (2 * e - 5).doubleFactorial := by
    intro y hy
    simp only [mem_erase, mem_univ, and_true] at hy
    split_ifs with h
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro C - ⟨h1, h2⟩
      rcases h with h | h
      · apply hy.1
        rw [← C.mate_mate y, h2, h, h1]
      · apply hy.2
        rw [← C.mate_mate y, h2, h, ← h1, mate_mate]
    · simp only [not_or] at h
      exact card_mate_mate_eq_doubleFactorial hW he A hxx' (B.mate_ne y).symm hy.2 hy.1 h.1 h.2
  have hR : #((univ.erase x).erase (A.mate x)) = 2 * e - 2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨hxx'.symm, mem_univ _⟩), card_erase_of_mem (mem_univ _),
      card_univ, hW]
    omega
  have hcard : #(((univ.erase x).erase (A.mate x)).filter
      fun y ↦ ¬(B.mate y = x ∨ B.mate y = A.mate x)) =
      2 * e - 4 + 2 * (if B.mate x = A.mate x then 1 else 0) := by
    split_ifs with h
    · rw [filter_true_of_mem, hR]
      · omega
      intro y hy
      simp only [mem_erase, mem_univ, and_true] at hy
      rw [hBx, hBx']
      have h' : B.mate (A.mate x) = x := by rw [← h, mate_mate]
      rw [h, h']
      tauto
    · have hset : ((univ.erase x).erase (A.mate x)).filter
          (fun y ↦ ¬(B.mate y = x ∨ B.mate y = A.mate x)) =
          (((univ.erase x).erase (A.mate x)).erase (B.mate x)).erase (B.mate (A.mate x)) := by
        ext y
        simp only [mem_filter, mem_erase, mem_univ, and_true, not_or, hBx, hBx']
        tauto
      have h1 : B.mate x ∈ (univ.erase x).erase (A.mate x) := by
        simp only [mem_erase, mem_univ, and_true]
        exact ⟨h, B.mate_ne x⟩
      have h2 : B.mate (A.mate x) ∈ ((univ.erase x).erase (A.mate x)).erase (B.mate x) := by
        simp only [mem_erase, mem_univ, and_true]
        refine ⟨fun h' ↦ hxx' (B.mate.injective h').symm, B.mate_ne _, fun h' ↦ h ?_⟩
        calc B.mate x = B.mate (B.mate (A.mate x)) := by rw [h']
          _ = A.mate x := mate_mate _ _
      rw [hset, card_erase_of_mem h2, card_erase_of_mem h1, hR]
      omega
  rw [← add_sum_erase _ _ (mem_univ x), ← add_sum_erase _ _ (mem_erase.mpr ⟨hxx'.symm, mem_univ _⟩),
    hfx, hfx', sum_congr rfl hfy, sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, hcard]
  split_ifs <;> ring

/-- `Σ_C sh(A, C) sh(C, B) = 2 sh(A, B) (2e - 3)!! + (2e(2e - 4) + 2 sh(A, B)) (2e - 5)!!`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem sum_shared2_mul (A B : PerfectMatching W) :
    ∑ C, shared2 A C * shared2 C B = 2 * shared2 A B * (2 * e - 3).doubleFactorial +
      (2 * e * (2 * e - 4) + 2 * shared2 A B) * (2 * e - 5).doubleFactorial := by
  have h1 : ∀ C, shared2 A C * shared2 C B = ∑ x, ∑ y,
      (if C.mate x = A.mate x ∧ C.mate y = B.mate y then 1 else 0) := by
    intro C
    simp only [shared2, card_filter, sum_mul_sum, ite_one_mul_ite_one, eq_comm (a := A.mate _)]
  rw [sum_congr rfl fun C _ ↦ h1 C, sum_comm]
  have h2 : ∀ x, ∑ C : PerfectMatching W, ∑ y,
      (if C.mate x = A.mate x ∧ C.mate y = B.mate y then 1 else 0) =
      ∑ y, #{C : PerfectMatching W | C.mate x = A.mate x ∧ C.mate y = B.mate y} := by
    intro x
    rw [sum_comm]
    simp only [card_filter]
  simp only [h2, sum_card_mate_mate hW he]
  have h3 : ∀ x, 2 * (if B.mate x = A.mate x then (2 * e - 3).doubleFactorial else 0) +
      (2 * e - 4 + 2 * (if B.mate x = A.mate x then 1 else 0)) * (2 * e - 5).doubleFactorial =
      (if B.mate x = A.mate x then 1 else 0) *
        (2 * (2 * e - 3).doubleFactorial + 2 * (2 * e - 5).doubleFactorial) +
        (2 * e - 4) * (2 * e - 5).doubleFactorial := by
    intro x
    split_ifs <;> ring
  rw [sum_congr rfl fun x _ ↦ h3 x, sum_add_distrib, ← sum_mul, sum_const, card_univ, hW,
    smul_eq_mul, ← card_filter, shared2_comm A B, shared2]
  ring

omit [Fintype W] [DecidableEq W] hW he in
/-- Every step of the walk of `(A, A)` uses `A` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem stepMatching_self (A : PerfectMatching W) (k : ℕ) : stepMatching A A k = A := by
  unfold stepMatching
  split_ifs <;> rfl

omit hW he in
/-- The cycles of `A ∪ A` are the doubled edges `{x, A(x)}` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem cycLen_self (A : PerfectMatching W) (x : W) : cycLen A A x = 2 := by
  rw [cycLen, Nat.find_eq_iff]
  refine ⟨⟨two_pos, ?_⟩, fun n hn ⟨h0, h1⟩ ↦ ?_⟩
  · simp [alt_succ, stepMatching_self]
  · obtain rfl : n = 1 := by omega
    simp only [alt_succ, alt_zero, stepMatching_self] at h1
    exact A.mate_ne x h1

omit hW he in
/-- The cycle of `A ∪ A` through `x` is `{x, A(x)}` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem mem_cycleOf_self_iff (A : PerfectMatching W) {x u : W} :
    u ∈ cycleOf A A x ↔ u = x ∨ u = A.mate x := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := exists_lt_of_mem_cycleOf h
    rw [cycLen_self] at hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (by simp [alt_succ, stepMatching_self])
  · rintro (rfl | rfl)
    · exact mem_cycleOf_self u
    · exact (mate_mem_cycleOf (mem_cycleOf_self x)).1

omit hW he in
/-- A Hamiltonian partner of `A` through a fixed non-`A` edge `xu`: there are
`k2Count (1 :: μ - 1 - 1)` of them with `μ` the type of `A ∪ A`, whatever the edge
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem card_mate_ham (A : PerfectMatching W) {x u : W} (hxu : x ≠ u) (hAu : A.mate x ≠ u) :
    #{C : PerfectMatching W | C.mate x = u ∧ Ham C A} =
      k2Count (1 ::ₘ ((pairType A A).erase 1).erase 1) := by
  have h := card_fiber_eq A A hxu hAu hAu
  simp only [and_self] at h
  have hu : u ∉ cycleOf A A x := by
    rw [mem_cycleOf_self_iff]
    rintro (h' | h')
    · exact hxu h'.symm
    · exact hAu h'.symm
  have h2 : #(cycleOf A A x) = 2 * 1 := by rw [card_cycleOf, cycLen_self]
  have h3 : #(cycleOf A A u) = 2 * 1 := by rw [card_cycleOf, cycLen_self]
  have hT := redType_of_notMem hu h2 h3
  rw [redType, dite_eq_right hxu] at hT
  rw [h, jointCount_eq_k2Count, hT]

/-- `|Ham(A)| = (2e - 2) · #{C ∈ Ham(A) : C(x) = u}` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem hamDeg_eq_mul (A : PerfectMatching W) :
    hamDeg A = (2 * e - 2) * k2Count (1 ::ₘ ((pairType A A).erase 1).erase 1) := by
  have hne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hne
  have h1 : hamDeg A = jointCount A A := by
    simp only [hamDeg, jointCount, and_self]
  rw [h1, jointCount_eq_sum_redCount A A x (by omega)]
  have h2 : ∀ u ∈ ((univ.erase x).erase (A.mate x)).erase (A.mate x),
      redCount A A x u = k2Count (1 ::ₘ ((pairType A A).erase 1).erase 1) := by
    intro u hu
    simp only [mem_erase, mem_univ, and_true] at hu
    rw [← card_mate_ham A (Ne.symm hu.2.2) (Ne.symm hu.1), redCount, dite_eq_right (Ne.symm hu.2.2),
      ← card_fiber_eq A A (Ne.symm hu.2.2) (Ne.symm hu.1) (Ne.symm hu.1)]
    simp only [and_self]
  rw [sum_congr rfl h2, sum_const, smul_eq_mul, erase_idem,
    card_erase_of_mem (mem_erase.mpr ⟨(A.mate_ne x), mem_univ _⟩), card_erase_of_mem (mem_univ _),
    card_univ, hW, Nat.sub_sub]

/-- `(2e - 2) Σ_C h(A, C) sh(C, B) = (2e - sh(A, B)) |Ham(A)|`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem sum_hamInd_shared2 (A B : PerfectMatching W) :
    (2 * e - 2) * ∑ C, (if Ham A C then 1 else 0) * shared2 C B =
      (2 * e - shared2 A B) * hamDeg A := by
  set c := k2Count (1 ::ₘ ((pairType A A).erase 1).erase 1)
  have h1 : ∀ C, (if Ham A C then 1 else 0) * shared2 C B =
      ∑ x, (if C.mate x = B.mate x ∧ Ham C A then 1 else 0) := by
    intro C
    rw [shared2, card_filter, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    by_cases hC : Ham A C
    · have hC' : Ham C A := (ham_comm A C).mp hC
      by_cases hx : C.mate x = B.mate x <;> simp [hC, hC', hx]
    · have hC' : ¬Ham C A := fun h ↦ hC ((ham_comm A C).mpr h)
      by_cases hx : C.mate x = B.mate x <;> simp [hC, hC', hx]
  rw [sum_congr rfl fun C _ ↦ h1 C, sum_comm]
  have h2 : ∀ x, ∑ C : PerfectMatching W, (if C.mate x = B.mate x ∧ Ham C A then 1 else 0) =
      if A.mate x = B.mate x then 0 else c := by
    intro x
    rw [← card_filter]
    split_ifs with h
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro C - ⟨h1, h2⟩
      exact not_ham_of_mate_eq_of_two_lt (by omega) (h1.trans h.symm) h2
    · exact card_mate_ham A (B.mate_ne x).symm h
  rw [sum_congr rfl fun x _ ↦ h2 x, sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul,
    hamDeg_eq_mul hW he A]
  have h3 : #(univ.filter fun x ↦ ¬A.mate x = B.mate x) = 2 * e - shared2 A B := by
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, hW, shared2]
  rw [h3]
  ring

end Count

section Kernel

/-- `(2e - 3)!! = (2e - 3)(2e - 5)!!` for `e ≥ 2` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem doubleFactorial_sub_three {e : ℕ} (he : 2 ≤ e) :
    (2 * e - 3).doubleFactorial = (2 * e - 3) * (2 * e - 5).doubleFactorial := by
  rcases Nat.lt_or_ge e 3 with h | h
  · obtain rfl : e = 2 := by omega
    rfl
  · rw [show 2 * e - 3 = 2 * e - 5 + 2 by omega, Nat.doubleFactorial_add_two]

/-- `(2e - 1)!! = (2e - 1)(2e - 3)!!` for `e ≥ 2` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem doubleFactorial_sub_one {e : ℕ} (he : 2 ≤ e) :
    (2 * e - 1).doubleFactorial = (2 * e - 1) * (2 * e - 3).doubleFactorial := by
  rw [show 2 * e - 1 = 2 * e - 3 + 2 by omega, Nat.doubleFactorial_add_two]

/-- The level-1 kernel `E₁(A, B) = (sh(A, B) - 2e/(2e - 1)) / (4(e - 1)(2e - 5)!!)`, the
projection onto the edge-sum functions orthogonal to the constants
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
noncomputable def levelOneKer (e : ℕ) (A B : PerfectMatching W) : ℝ :=
  ((shared2 A B : ℝ) - 2 * e / (2 * e - 1)) /
    (4 * ((e : ℝ) - 1) * ((2 * e - 5).doubleFactorial : ℝ))

/-- `E₁` is symmetric (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem levelOneKer_comm (e : ℕ) (A B : PerfectMatching W) :
    levelOneKer e A B = levelOneKer e B A := by
  rw [levelOneKer, levelOneKer, shared2_comm]

variable {e : ℕ} (hW : Fintype.card W = 2 * e) (he : 2 ≤ e)
include hW he

/-- `|PM| = (2e - 1)(2e - 3)(2e - 5)!!` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem real_card_pm :
    (Fintype.card (PerfectMatching W) : ℝ) =
      (2 * e - 1) * (2 * e - 3) * ((2 * e - 5).doubleFactorial : ℝ) := by
  rw [card_eq_doubleFactorial hW, doubleFactorial_sub_one he, doubleFactorial_sub_three he]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * e), Nat.cast_sub (by omega : 3 ≤ 2 * e)]
  ring

/-- `Σ_C sh(A, C) = 2e (2e - 3) (2e - 5)!!` in `ℝ` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem real_sum_shared2 (A : PerfectMatching W) :
    ∑ C, (shared2 A C : ℝ) = 2 * e * (2 * e - 3) * ((2 * e - 5).doubleFactorial : ℝ) := by
  rw [← Nat.cast_sum, sum_shared2 hW he, doubleFactorial_sub_three he]
  push_cast [Nat.cast_sub (by omega : 3 ≤ 2 * e)]
  ring

/-- `E₁` is orthogonal to the constants, `Σ_C E₁(A, C) = 0` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem sum_levelOneKer (A : PerfectMatching W) : ∑ C, levelOneKer e A C = 0 := by
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ e := by exact_mod_cast he
    linarith
  simp only [levelOneKer]
  rw [← sum_div, sum_sub_distrib, real_sum_shared2 hW he, sum_const, card_univ, nsmul_eq_mul,
    real_card_pm hW he]
  field_simp
  ring

/-- `E₁` is idempotent, `Σ_C E₁(A, C) E₁(C, B) = E₁(A, B)` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem levelOneKer_mul_self (A B : PerfectMatching W) :
    ∑ C, levelOneKer e A C * levelOneKer e C B = levelOneKer e A B := by
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((e : ℝ) - 1) ≠ 0 := by linarith
  have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  have hS3 : ∑ C, (shared2 A C : ℝ) * shared2 C B =
      2 * shared2 A B * ((2 * e - 3) * ((2 * e - 5).doubleFactorial : ℝ)) +
        (2 * e * (2 * e - 4) + 2 * shared2 A B) * ((2 * e - 5).doubleFactorial : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) (sum_shared2_mul hW he A B)
    push_cast [Nat.cast_sum, doubleFactorial_sub_three he,
      Nat.cast_sub (by omega : 3 ≤ 2 * e), Nat.cast_sub (by omega : 4 ≤ 2 * e)] at this
    rw [this]
  have hS2 : ∑ C, (shared2 C B : ℝ) =
      2 * e * (2 * e - 3) * ((2 * e - 5).doubleFactorial : ℝ) := by
    simp_rw [shared2_comm _ B]
    exact real_sum_shared2 hW he B
  have he1 : ∀ C, levelOneKer e A C * levelOneKer e C B =
      ((shared2 A C : ℝ) * shared2 C B - 2 * e / (2 * e - 1) * shared2 A C -
        2 * e / (2 * e - 1) * shared2 C B + (2 * e / (2 * e - 1)) ^ 2) /
        (4 * ((e : ℝ) - 1) * ((2 * e - 5).doubleFactorial : ℝ)) ^ 2 := by
    intro C
    simp only [levelOneKer]
    rw [div_mul_div_comm, ← sq]
    congr 1
    ring
  rw [sum_congr rfl fun C _ ↦ he1 C, ← sum_div, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, hS3, hS2, real_sum_shared2 hW he, sum_const, card_univ, nsmul_eq_mul,
    real_card_pm hW he, levelOneKer]
  field_simp
  ring

/-- `H E₁ = λ₁ E₁` with `λ₁ = -|Ham(A)|/(2(e - 1))`, so `ω_{(e-1,1)}((e)) = -1/(2(e - 1))`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem hamMat_levelOneKer (A B : PerfectMatching W) :
    ∑ C, hamInd A C * levelOneKer e C B =
      -((hamDeg A : ℝ) / (2 * ((e : ℝ) - 1))) * levelOneKer e A B := by
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((e : ℝ) - 1) ≠ 0 := by linarith
  have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  have hX : ∑ C, hamInd A C * (shared2 C B : ℝ) =
      (2 * e - shared2 A B) * hamDeg A / (2 * e - 2) := by
    have h := congrArg (Nat.cast (R := ℝ)) (sum_hamInd_shared2 hW he A B)
    have hsh : shared2 A B ≤ 2 * e := by
      rw [shared2, ← hW]
      exact card_le_univ _
    push_cast [Nat.cast_sum, Nat.cast_sub (by omega : 2 ≤ 2 * e), Nat.cast_sub hsh] at h
    have h3 : (2 * (e : ℝ) - 2) ≠ 0 := by linarith
    rw [eq_div_iff h3, mul_comm, ← h]
    rfl
  have hH : ∑ C, hamInd A C = hamDeg A := by
    simp_rw [hamInd_comm A]
    exact sum_hamInd A
  simp only [levelOneKer, mul_div_assoc']
  rw [← sum_div]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hX, hH]
  field_simp
  ring

/-- `E₁(A, A) = e(2e - 3)/|PM|`, so `d_{(e-1,1)} = tr E₁ = e(2e - 3)`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem levelOneKer_self (A : PerfectMatching W) :
    levelOneKer e A A = e * (2 * e - 3) / Fintype.card (PerfectMatching W) := by
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((e : ℝ) - 1) ≠ 0 := by linarith
  have h3 : (2 * (e : ℝ) - 3) ≠ 0 := by linarith
  have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  have hsh : shared2 A A = 2 * e := by
    rw [shared2, filter_true_of_mem fun _ _ ↦ rfl, card_univ, hW]
  rw [levelOneKer, hsh, real_card_pm hW he]
  push_cast
  field_simp
  ring

/-- `d_{(e-1,1)} = tr E₁ = e(2e - 3)` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem sum_levelOneKer_self :
    ∑ A : PerfectMatching W, levelOneKer e A A = e * (2 * e - 3) := by
  have hN : (Fintype.card (PerfectMatching W) : ℝ) ≠ 0 := by
    rw [real_card_pm hW he]
    have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
    have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
    have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
    have h3 : (2 * (e : ℝ) - 3) ≠ 0 := by linarith
    exact mul_ne_zero (mul_ne_zero h1 h3) hM
  simp only [levelOneKer_self hW he, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- `ω_{(e-1,1)}(A, B) = |PM| E₁(A, B) / d = ((2e - 1) l - e)/(2e(e - 1))` with `l = sh/2`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem levelOneKer_omega (A B : PerfectMatching W) :
    (Fintype.card (PerfectMatching W) : ℝ) * levelOneKer e A B / (e * (2 * e - 3)) =
      ((2 * e - 1) * ((shared2 A B : ℝ) / 2) - e) / (2 * e * (e - 1)) := by
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((e : ℝ) - 1) ≠ 0 := by linarith
  have h3 : (2 * (e : ℝ) - 3) ≠ 0 := by linarith
  have h0 : (e : ℝ) ≠ 0 := by linarith
  have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  rw [real_card_pm hW he, levelOneKer]
  field_simp
  ring

/-- The level-1 term of Theorem 1: `(|PM| / |Ham(B)|²) λ₁² E₁(A, B) = L₁(l(A, B))` with
`l = sh/2` the number of shared edges and `λ₁ = -|Ham(B)|/(2(e - 1))`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem levelOne_term (A B : PerfectMatching W) (hk : hamDeg B ≠ 0) :
    (Fintype.card (PerfectMatching W) : ℝ) / (hamDeg B : ℝ) ^ 2 *
        (-((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1)))) ^ 2 * levelOneKer e A B =
      levelOne e ((shared2 A B : ℝ) / 2) := by
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (2 * (e : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((e : ℝ) - 1) ≠ 0 := by linarith
  have hM : ((2 * e - 5).doubleFactorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  have hk' : (hamDeg B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [real_card_pm hW he, levelOneKer, levelOne]
  field_simp
  ring

end Kernel

end PerfectMatching

end Pairing
