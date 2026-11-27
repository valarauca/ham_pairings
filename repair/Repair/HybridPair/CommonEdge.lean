import Repair.HybridPair.MeanCount

/-!
# The common-edge factor (Lemma 2 of pair incoherence)

`A` and `B` are perfect matchings of a type `V` with `|V| = 2e` that share the edge
`f = {a, b}`, `b = A a = B a`. Put `S = V ∖ {a, b}` (`pairCompl a b`) and `A' = A|_S`,
`B' = B|_S`. `jointCount A B = #{R | Ham R A ∧ Ham R B}` counts the matchings `R` for which both
`R ∪ A` and `R ∪ B` are one cycle, and `jointHamProb A B = jointCount A B / (2e - 1)!!` is the
paper's `h_e(A, B)`.

* `contract_mate_of_two_step` : a `Q ∪ P'` path of one `P`-edge is closed by `κ_Q`.
* `contract_mate_pairCompl` : for `R ∌ f`, the contraction of `R` along `f` is the paper's `R'`.
  It joins `R a` to `R b` and keeps every other edge of `R`.
* `ham_iff_contract_pairCompl` : for `R ∌ f`, `R ∪ A` is one cycle iff `R' ∪ A'` is.
* `dropEquiv` : `R ↦ (R', R a)` is a bijection from `{R | R ∌ f}` onto `PM(S) × S`. So each `R'`
  has exactly `2e - 2` preimages.
* `jointCount_eq_of_mate_eq` (Lemma 2, counting form) :
  `jointCount A B = (2e - 2) · jointCount A' B'`.
* `jointHamProb_eq_of_mate_eq` (Lemma 2) : `h_e(A, B) = ((2e - 2)/(2e - 1)) h_{e-1}(A', B')`, and
  `hamProb_succ` : `p_e = ((2e - 2)/(2e - 1)) p_{e-1}` (the case `A = B`).
* `jointHamProb_div_sq_eq_of_mate_eq` (Lemma 2, ratio form) :
  `h_e(A, B)/p_e² = (1 + 1/(2e - 2)) h_{e-1}(A', B')/p_{e-1}²`.

Source: `results/hybrid-pair-incoherence.md` (organize-archive 0dca0a5), §2, Lemma 2.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One step of the contraction walk (`results/hybrid-pair-incoherence.md`, Lemma 2). If the
`Q`-partner of `s ∈ A` lies off `A` and the walk re-enters `A` after one `P`-edge, then `κ_Q`
pairs `s` with `Q (P (Q s))`. -/
theorem contract_mate_of_two_step (P Q : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) (s : A) (h0 : Q.mate s ∉ A)
    (h1 : Q.mate (P.mate (Q.mate s)) ∈ A) :
    ((contract P Q A hA).mate s : V) = Q.mate (P.mate (Q.mate s)) := by
  have e0 : oddPt P Q s 0 = Q.mate s := by
    rw [oddPt, evenPt_zero]
  have e1 : oddPt P Q s 1 = Q.mate (P.mate (Q.mate s)) := by
    rw [oddPt, evenPt_succ P Q s 0, e0]
  have hidx : exitIdx P Q A hA s = 1 := by
    rw [exitIdx, Nat.find_eq_iff]
    refine ⟨by rw [e1]; exact h1, fun i hi ↦ ?_⟩
    rw [show i = 0 by omega, e0]
    exact h0
  rw [contract_mate, coe_contractFun, hidx, e1]

/-- `V ∖ {a, b}`, the vertices left after deleting the common edge `{a, b}`
(`results/hybrid-pair-incoherence.md`, Lemma 2). -/
def pairCompl (a b : V) : Finset V :=
  ({a, b} : Finset V)ᶜ

/-- Membership in `V ∖ {a, b}`. -/
theorem mem_pairCompl {a b v : V} : v ∈ pairCompl a b ↔ v ≠ a ∧ v ≠ b := by
  simp [pairCompl]

/-- `|V ∖ {a, b}| = |V| - 2` for `a ≠ b`. -/
theorem card_pairCompl {a b : V} (hab : a ≠ b) : (pairCompl a b).card = Fintype.card V - 2 := by
  rw [pairCompl, card_compl, card_pair hab]

/-- `V ∖ {a, b}` is a union of edges of any matching that contains `{a, b}`. -/
theorem mate_mem_pairCompl {P : PerfectMatching V} {a b : V} (h : P.mate a = b) :
    ∀ v ∈ pairCompl a b, P.mate v ∈ pairCompl a b := by
  intro v hv
  rw [mem_pairCompl] at hv ⊢
  refine ⟨fun h' ↦ hv.2 ?_, fun h' ↦ hv.1 ?_⟩
  · rw [← h, ← h', mate_mate]
  · rw [← P.mate_mate v, h', ← h, mate_mate]

/-- A matching `R` without the edge `{a, b}` closes no cycle with `P'` off `V ∖ {a, b}`
(`results/hybrid-pair-incoherence.md`, Lemma 2). -/
theorem not_hasClosedCycle_pairCompl {P R : PerfectMatching V} {a b : V} (hR : R.mate a ≠ b) :
    ¬HasClosedCycle P R (pairCompl a b) := by
  rintro ⟨C, ⟨v, hv⟩, hdisj, -, hRC⟩
  have hout : ∀ u ∈ C, u = a ∨ u = b := fun u hu ↦ by
    have h := Finset.disjoint_left.mp hdisj hu
    rw [mem_pairCompl] at h
    tauto
  have hRb : R.mate b ≠ a := fun h ↦ hR (by rw [← h, mate_mate])
  rcases hout v hv with rfl | rfl
  · rcases hout _ (hRC _ hv) with h | h
    · exact R.mate_ne _ h
    · exact hR h
  · rcases hout _ (hRC _ hv) with h | h
    · exact hRb h
    · exact R.mate_ne _ h

/-- The contraction of `R` along the common edge `{a, b}` of `P`, for `R ∌ {a, b}`
(`results/hybrid-pair-incoherence.md`, Lemma 2). It joins `R a` and `R b`, the two vertices
whose `R`-edges `{a, x}`, `{b, y}` are replaced by `{x, y}`, and keeps every other edge of `R`. -/
theorem contract_mate_pairCompl {P R : PerfectMatching V} {a b : V} (hP : P.mate a = b)
    (hR : R.mate a ≠ b) (s : pairCompl a b) :
    ((contract P R (pairCompl a b) (mate_mem_pairCompl hP)).mate s : V) =
      if R.mate s = a then R.mate b else if R.mate s = b then R.mate a else R.mate s := by
  have hPb : P.mate b = a := by rw [← hP, mate_mate]
  have hRb : R.mate b ≠ a := fun h ↦ hR (by rw [← h, mate_mate])
  split_ifs with h1 h2
  · rw [contract_mate_of_two_step _ _ _ _ s (by rw [h1, mem_pairCompl]; simp)
      (by rw [h1, hP, mem_pairCompl]; exact ⟨hRb, R.mate_ne b⟩), h1, hP]
  · rw [contract_mate_of_two_step _ _ _ _ s (by rw [h2, mem_pairCompl]; simp)
      (by rw [h2, hPb, mem_pairCompl]; exact ⟨R.mate_ne a, hR⟩), h2, hPb]
  · exact contract_mate_of_mem _ _ _ _ s (mem_pairCompl.mpr ⟨h1, h2⟩)

/-- The contraction along a common edge does not depend on which of the two matchings
supplies the edge (`results/hybrid-pair-incoherence.md`, Lemma 2). -/
theorem contract_pairCompl_eq {P Q R : PerfectMatching V} {a b : V} (hP : P.mate a = b)
    (hQ : Q.mate a = b) (hR : R.mate a ≠ b) :
    contract P R (pairCompl a b) (mate_mem_pairCompl hP) =
      contract Q R (pairCompl a b) (mate_mem_pairCompl hQ) := by
  ext s
  rw [contract_mate_pairCompl hP hR, contract_mate_pairCompl hQ hR]

/-- For `R ∌ {a, b}`, `R ∪ P` is one cycle iff the contracted `R' ∪ P|_S` is one cycle on
`S = V ∖ {a, b}` (`results/hybrid-pair-incoherence.md`, Lemma 2: the path `x a b y` becomes the
edge `x y`). -/
theorem ham_iff_contract_pairCompl {P R : PerfectMatching V} {a b : V} (hP : P.mate a = b)
    (hR : R.mate a ≠ b) :
    Ham R P ↔ Ham (contract P R (pairCompl a b) (mate_mem_pairCompl hP))
      (restrict P (pairCompl a b) (mate_mem_pairCompl hP)) := by
  have h := ham_glue_iff P R _ (mate_mem_pairCompl hP) (not_hasClosedCycle_pairCompl hR)
    (restrict P _ (mate_mem_pairCompl hP))
  rw [glue_restrict] at h
  rw [ham_comm, h, ham_comm]

section Insert

variable (P : PerfectMatching V) {a b : V} (hP : P.mate a = b)

/-- The inverse of the contraction: `R'` with `x ∈ S` gives the matching with `{a, x}`,
`{b, R' x}` and the other edges of `R'` (`results/hybrid-pair-incoherence.md`, Lemma 2). -/
def insertEdge (R' : PerfectMatching (pairCompl a b)) (x : pairCompl a b) : PerfectMatching V :=
  Equiv.swap b x • glue P (pairCompl a b) (mate_mem_pairCompl hP) R'

variable {P}

theorem insertEdge_mate_left (R' : PerfectMatching (pairCompl a b)) (x : pairCompl a b) :
    (insertEdge P hP R' x).mate a = x := by
  have hx := mem_pairCompl.mp x.2
  have hab : a ≠ b := fun h ↦ P.mate_ne a (by rw [hP, h])
  have ha : a ∉ pairCompl a b := fun h ↦ (mem_pairCompl.mp h).1 rfl
  rw [insertEdge, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hab hx.1.symm,
    glue_mate_of_notMem _ _ _ _ ha, hP, Equiv.swap_apply_left]

theorem insertEdge_mate_right (R' : PerfectMatching (pairCompl a b)) (x : pairCompl a b) :
    (insertEdge P hP R' x).mate b = R'.mate x := by
  have hy := mem_pairCompl.mp (R'.mate x).2
  have hyx : (R'.mate x : V) ≠ x := fun h ↦ R'.mate_ne x (Subtype.ext h)
  rw [insertEdge, smul_mate, Equiv.swap_inv, Equiv.swap_apply_left, glue_mate_coe,
    Equiv.swap_apply_of_ne_of_ne hy.2 hyx]

theorem insertEdge_mate_coe (R' : PerfectMatching (pairCompl a b)) (x s : pairCompl a b) :
    (insertEdge P hP R' x).mate s =
      if s = x then a else if s = R'.mate x then b else R'.mate s := by
  have hab : a ≠ b := fun h ↦ P.mate_ne a (by rw [hP, h])
  have hPb : P.mate b = a := by rw [← hP, mate_mate]
  have hb : b ∉ pairCompl a b := fun h ↦ (mem_pairCompl.mp h).2 rfl
  have hs := mem_pairCompl.mp s.2
  have hx := mem_pairCompl.mp x.2
  rw [insertEdge, smul_mate, Equiv.swap_inv]
  split_ifs with h1 h2
  · rw [h1, Equiv.swap_apply_right, glue_mate_of_notMem _ _ _ _ hb, hPb,
      Equiv.swap_apply_of_ne_of_ne hab hx.1.symm]
  · have hsx : (s : V) ≠ x := fun h ↦ h1 (Subtype.ext h)
    rw [Equiv.swap_apply_of_ne_of_ne hs.2 hsx, glue_mate_coe, h2, mate_mate,
      Equiv.swap_apply_right]
  · have hsx : (s : V) ≠ x := fun h ↦ h1 (Subtype.ext h)
    have hy := mem_pairCompl.mp (R'.mate s).2
    have hyx : (R'.mate s : V) ≠ x := fun h ↦ h2 (by rw [← Subtype.ext h, mate_mate])
    rw [Equiv.swap_apply_of_ne_of_ne hs.2 hsx, glue_mate_coe,
      Equiv.swap_apply_of_ne_of_ne hy.2 hyx]

theorem insertEdge_mate_ne (R' : PerfectMatching (pairCompl a b)) (x : pairCompl a b) :
    (insertEdge P hP R' x).mate a ≠ b := by
  rw [insertEdge_mate_left]
  exact (mem_pairCompl.mp x.2).2

theorem contract_insertEdge (R' : PerfectMatching (pairCompl a b)) (x : pairCompl a b) :
    contract P (insertEdge P hP R' x) (pairCompl a b) (mate_mem_pairCompl hP) = R' := by
  have hab : a ≠ b := fun h ↦ P.mate_ne a (by rw [hP, h])
  ext s
  rw [contract_mate_pairCompl hP (insertEdge_mate_ne hP R' x), insertEdge_mate_coe,
    insertEdge_mate_left, insertEdge_mate_right]
  have hs := mem_pairCompl.mp s.2
  have hx := mem_pairCompl.mp x.2
  by_cases h1 : s = x
  · subst h1
    simp
  by_cases h2 : s = R'.mate x
  · subst h2
    simp [h1, Ne.symm hab]
  have hy := mem_pairCompl.mp (R'.mate s).2
  simp [h1, h2, hy.1, hy.2]

theorem insertEdge_contract {R : PerfectMatching V} (hR : R.mate a ≠ b) :
    insertEdge P hP (contract P R (pairCompl a b) (mate_mem_pairCompl hP))
      ⟨R.mate a, mem_pairCompl.mpr ⟨R.mate_ne a, hR⟩⟩ = R := by
  have hab : a ≠ b := fun h ↦ P.mate_ne a (by rw [hP, h])
  have hRb : R.mate b ≠ a := fun h ↦ hR (by rw [← h, mate_mate])
  have hκx : ((contract P R (pairCompl a b) (mate_mem_pairCompl hP)).mate
      ⟨R.mate a, mem_pairCompl.mpr ⟨R.mate_ne a, hR⟩⟩ : V) = R.mate b := by
    rw [contract_mate_pairCompl hP hR]
    simp
  ext v
  by_cases hva : v = a
  · subst hva
    rw [insertEdge_mate_left]
  by_cases hvb : v = b
  · subst hvb
    rw [insertEdge_mate_right, hκx]
  have hv : v ∈ pairCompl a b := mem_pairCompl.mpr ⟨hva, hvb⟩
  rw [show v = ((⟨v, hv⟩ : pairCompl a b) : V) from rfl, insertEdge_mate_coe]
  split_ifs with h1 h2
  · rw [Subtype.ext_iff] at h1
    simp only at h1
    change a = R.mate v
    rw [h1, mate_mate]
  · rw [Subtype.ext_iff, hκx] at h2
    simp only at h2
    change b = R.mate v
    rw [h2, mate_mate]
  · rw [contract_mate_pairCompl hP hR]
    have h1' : R.mate v ≠ a := fun h ↦ h1 (Subtype.ext (by simp [← h]))
    have h2' : R.mate v ≠ b := fun h ↦ h2 (Subtype.ext (by rw [hκx]; simp [← h]))
    simp [h1', h2']

/-- `R ↦ (R', R a)` is a bijection from the matchings without the edge `{a, b}` onto
`PM(V ∖ {a, b}) × (V ∖ {a, b})` (`results/hybrid-pair-incoherence.md`, Lemma 2: each `R'` has
exactly `2(e - 1)` preimages). -/
def dropEquiv :
    {R : PerfectMatching V // R.mate a ≠ b} ≃
      PerfectMatching (pairCompl a b) × pairCompl a b where
  toFun R := (contract P R.1 (pairCompl a b) (mate_mem_pairCompl hP),
    ⟨R.1.mate a, mem_pairCompl.mpr ⟨R.1.mate_ne a, R.2⟩⟩)
  invFun p := ⟨insertEdge P hP p.1 p.2, insertEdge_mate_ne hP p.1 p.2⟩
  left_inv R := Subtype.ext (insertEdge_contract hP R.2)
  right_inv p := by
    refine Prod.ext (contract_insertEdge hP p.1 p.2) (Subtype.ext ?_)
    exact insertEdge_mate_left hP p.1 p.2

end Insert

/-- `#{R | R ∪ A and R ∪ B are both one cycle}` (`results/hybrid-pair-incoherence.md` §1, the
numerator of `h(A, B)`). -/
def jointCount (A B : PerfectMatching V) : ℕ :=
  (univ.filter fun R : PerfectMatching V ↦ Ham R A ∧ Ham R B).card

/-- Lemma 2 of `results/hybrid-pair-incoherence.md`, counting form. If `A` and `B` share the
edge `{a, b}` and `|V| > 2`, then `jointCount A B = (|V| - 2) · jointCount A' B'`, where `A'`,
`B'` are `A`, `B` restricted to `V ∖ {a, b}`. -/
theorem jointCount_eq_of_mate_eq {A B : PerfectMatching V} {a b : V} (hA : A.mate a = b)
    (hB : B.mate a = b) (hV : 2 < Fintype.card V) :
    jointCount A B = (Fintype.card V - 2) *
      jointCount (restrict A (pairCompl a b) (mate_mem_pairCompl hA))
        (restrict B (pairCompl a b) (mate_mem_pairCompl hB)) := by
  have hab : a ≠ b := fun h ↦ A.mate_ne a (by rw [hA, h])
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset V)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt hV)
  have hwa : w ≠ a := fun h ↦ hw (by simp [h])
  have hwb : w ≠ b := fun h ↦ hw (by simp [h])
  set S := pairCompl a b
  set A' := restrict A S (mate_mem_pairCompl hA)
  set B' := restrict B S (mate_mem_pairCompl hB)
  let good : PerfectMatching S → Prop := fun R' ↦ Ham R' A' ∧ Ham R' B'
  have hfilter : ∀ R : PerfectMatching V, (Ham R A ∧ Ham R B) ↔
      (R.mate a ≠ b ∧ good (contract A R S (mate_mem_pairCompl hA))) := by
    intro R
    by_cases hR : R.mate a = b
    · refine iff_of_false (fun h ↦ not_ham_of_mate_eq (hR.trans hA.symm) hwa
        (by rw [hA]; exact hwb) h.1) fun h ↦ h.1 hR
    · rw [ham_iff_contract_pairCompl hA hR, ham_iff_contract_pairCompl hB hR,
        contract_pairCompl_eq hB hA hR]
      exact ⟨fun h ↦ ⟨hR, h⟩, fun h ↦ h.2⟩
  have e : {R : PerfectMatching V // R.mate a ≠ b ∧
      good (contract A R S (mate_mem_pairCompl hA))} ≃ {R' // good R'} × S :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
      (((dropEquiv hA).subtypeEquiv fun R ↦ Iff.rfl).trans
        (Equiv.prodSubtypeFstEquivSubtypeProd (p := good)))
  rw [jointCount, filter_congr fun R _ ↦ hfilter R, ← Fintype.card_subtype, Fintype.card_congr e,
    Fintype.card_prod, Fintype.card_coe, card_pairCompl hab, Fintype.card_subtype, mul_comm]
  rfl

/-- `h(A, B) = jointCount A B / (2e - 1)!!`, the probability that `R ∪ A` and `R ∪ B` are both
one cycle for `R` uniform (`results/hybrid-pair-incoherence.md` §1). -/
noncomputable def jointHamProb (A B : PerfectMatching V) : ℝ :=
  (jointCount A B : ℝ) / (Fintype.card (PerfectMatching V) : ℝ)

end PerfectMatching

/-- `p_e = 2^(e-1) (e-1)! / (2e - 1)!!`, the probability that a uniform `R` makes `R ∪ c` one
cycle on `2e` points (`results/hybrid-pair-incoherence.md` §1, ULZD Lemma 3). -/
noncomputable def hamProb (e : ℕ) : ℝ :=
  (2 ^ (e - 1) * (e - 1).factorial : ℝ) / (Nat.doubleFactorial (2 * e - 1) : ℝ)

/-- `p_e > 0`. -/
theorem hamProb_pos (e : ℕ) : 0 < hamProb e :=
  div_pos (by positivity) (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))

/-- `p_{k+2} = ((2k + 2)/(2k + 3)) p_{k+1}`, the case `A = B` of Lemma 2
(`results/hybrid-pair-incoherence.md`). -/
theorem hamProb_succ (k : ℕ) :
    hamProb (k + 2) = ((2 * k + 2 : ℝ) / (2 * k + 3)) * hamProb (k + 1) := by
  rw [hamProb, hamProb, show 2 * (k + 2) - 1 = 2 * k + 1 + 2 by omega,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_two,
    show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, Nat.factorial_succ]
  have h := Nat.cast_pos (α := ℝ).mpr (Nat.doubleFactorial_pos (2 * k + 1))
  field_simp
  push_cast
  ring

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma 2 of `results/hybrid-pair-incoherence.md`, probability form. If `|V| = 2e`, `e ≥ 2`,
and `A`, `B` share the edge `{a, b}`, then `h_e(A, B) = ((2e - 2)/(2e - 1)) h_{e-1}(A', B')`. -/
theorem jointHamProb_eq_of_mate_eq {e : ℕ} (hV : Fintype.card V = 2 * e) (he : 2 ≤ e)
    {A B : PerfectMatching V} {a b : V} (hA : A.mate a = b) (hB : B.mate a = b) :
    jointHamProb A B = ((2 * e - 2 : ℝ) / (2 * e - 1)) *
      jointHamProb (restrict A (pairCompl a b) (mate_mem_pairCompl hA))
        (restrict B (pairCompl a b) (mate_mem_pairCompl hB)) := by
  have hab : a ≠ b := fun h ↦ A.mate_ne a (by rw [hA, h])
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  have hS : Fintype.card (pairCompl a b) = 2 * (k + 1) := by
    rw [Fintype.card_coe, card_pairCompl hab, hV]
    omega
  rw [jointHamProb, jointHamProb, jointCount_eq_of_mate_eq hA hB (by omega),
    card_eq_doubleFactorial hV, card_eq_doubleFactorial hS, hV,
    show 2 * (k + 2) - 1 = 2 * k + 1 + 2 by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    Nat.doubleFactorial_add_two, show 2 * (k + 2) - 2 = 2 * k + 2 by omega]
  have h := (Nat.cast_pos (α := ℝ).mpr (Nat.doubleFactorial_pos (2 * k + 1))).ne'
  have h3 : (2 * k + 3 : ℝ) ≠ 0 := by positivity
  push_cast
  rw [show 2 * ((k : ℝ) + 2) - 2 = 2 * k + 2 by ring,
    show 2 * ((k : ℝ) + 2) - 1 = 2 * k + 3 by ring]
  field_simp
  ring

/-- Lemma 2 of `results/hybrid-pair-incoherence.md`, ratio form. If `|V| = 2e`, `e ≥ 2`, and `A`,
`B` share the edge `{a, b}`, then `h_e(A, B)/p_e² = (1 + 1/(2e - 2)) h_{e-1}(A', B')/p_{e-1}²`,
with `A'`, `B'` the restrictions to `V ∖ {a, b}`. -/
theorem jointHamProb_div_sq_eq_of_mate_eq {e : ℕ} (hV : Fintype.card V = 2 * e) (he : 2 ≤ e)
    {A B : PerfectMatching V} {a b : V} (hA : A.mate a = b) (hB : B.mate a = b) :
    jointHamProb A B / hamProb e ^ 2 = (1 + 1 / (2 * e - 2 : ℝ)) *
      (jointHamProb (restrict A (pairCompl a b) (mate_mem_pairCompl hA))
        (restrict B (pairCompl a b) (mate_mem_pairCompl hB)) / hamProb (e - 1) ^ 2) := by
  rw [jointHamProb_eq_of_mate_eq hV he hA hB]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  rw [hamProb_succ, show k + 2 - 1 = k + 1 by omega]
  have h := (hamProb_pos (k + 1)).ne'
  have h2 : (2 * k + 2 : ℝ) ≠ 0 := by positivity
  have h3 : (2 * k + 3 : ℝ) ≠ 0 := by positivity
  push_cast
  rw [show 2 * ((k : ℝ) + 2) - 2 = 2 * k + 2 by ring,
    show 2 * ((k : ℝ) + 2) - 1 = 2 * k + 3 by ring]
  field_simp
  ring

end PerfectMatching

end Pairing
