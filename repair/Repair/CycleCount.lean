import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Pairing.Basic

/-!
# The cycle count of `P ∪ F` and its generating function (COD-146)

This file supplies the cycle count `κ(P ∪ F)` used by Identity D and Proposition D of
`results/switching-j0-spike.md` (ce14dda), and the bound on its generating function that
Proposition D needs.

* `PerfectMatching.cycleCount P Q = κ(P ∪ Q)`, the number of connected components of the union
  graph. A common edge is one component, the digon.
* `PerfectMatching.ham_iff_cycleCount_eq_one` : `Ham P Q ↔ κ(P ∪ Q) = 1`.
* `PerfectMatching.contractAt P F u`, the matching on `V ∖ {u, F u}` obtained from `P` by deleting
  the digon `{u, F u}` when `P u = F u`, and otherwise by replacing the path
  `P u, u, F u, P (F u)` with the single edge `{P u, P (F u)}`.
* `PerfectMatching.cycleCount_le_contractAt` and
  `PerfectMatching.cycleCount_le_contractAt_add_one` :
  the contraction keeps every cycle except possibly the digon `{u, F u}`.
* `PerfectMatching.sum_pow_cycleCount_le` : for `x ≥ 1` and `|V| = 2m`,
  `∑_P x^κ(P ∪ F) ≤ ∏_{i < m} (x + 2i)`. The spike uses the exact identity
  `∑_P x^κ(P ∪ F) = x (x + 2) ⋯ (x + 2m - 2)` (as in COD-171). Only the inequality is needed for
  Proposition D, and it follows from injectivity of the contraction alone.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*}

/-- `κ(P ∪ Q)`, the number of cycles of the union of two perfect matchings, counted as connected
components of the union graph (`results/switching-j0-spike.md` §1). -/
noncomputable def cycleCount (P Q : PerfectMatching V) : ℕ :=
  Nat.card (P.toGraph ⊔ Q.toGraph).ConnectedComponent

/-- `κ(P ∪ Q) ≥ 1` on a nonempty vertex set (`results/switching-j0-spike.md`, Identity D). -/
theorem cycleCount_pos [Finite V] [Nonempty V] (P Q : PerfectMatching V) :
    0 < cycleCount P Q := by
  have : Nonempty (P.toGraph ⊔ Q.toGraph).ConnectedComponent :=
    ⟨(P.toGraph ⊔ Q.toGraph).connectedComponentMk (Classical.arbitrary V)⟩
  exact Nat.card_pos

/-- `P ∪ Q` is one cycle iff `κ(P ∪ Q) = 1` (`results/switching-j0-spike.md`, Identity D, where
`A_0` is the event `κ_0 = 1`). -/
theorem ham_iff_cycleCount_eq_one [Nonempty V] (P Q : PerfectMatching V) :
    Ham P Q ↔ cycleCount P Q = 1 := by
  rw [Ham, cycleCount, Nat.card_eq_one_iff_unique, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨h.subsingleton_connectedComponent,
      ⟨(P.toGraph ⊔ Q.toGraph).connectedComponentMk (Classical.arbitrary V)⟩⟩
  · rintro ⟨hs, -⟩
    exact ⟨fun u v ↦ SimpleGraph.ConnectedComponent.eq.mp (Subsingleton.elim _ _), inferInstance⟩

/-- `κ(P ∪ Q) = 0` on the empty vertex set (`results/switching-j0-spike.md`, Identity D). -/
theorem cycleCount_of_isEmpty [IsEmpty V] (P Q : PerfectMatching V) : cycleCount P Q = 0 := by
  have : IsEmpty (P.toGraph ⊔ Q.toGraph).ConnectedComponent :=
    ⟨fun c ↦ c.ind fun v ↦ isEmptyElim v⟩
  exact Nat.card_of_isEmpty

/-- `P a = b ↔ P b = a` for a perfect matching (used in Identity D of
`results/switching-j0-spike.md`). -/
theorem mate_eq_comm (P : PerfectMatching V) {a b : V} : P.mate a = b ↔ P.mate b = a :=
  ⟨fun h ↦ h ▸ P.mate_mate a, fun h ↦ h ▸ P.mate_mate b⟩

section Contract

variable [DecidableEq V]

/-- The vertices other than `u` and its `F`-partner. -/
abbrev Rest (F : PerfectMatching V) (u : V) : Type _ :=
  {v : V // v ≠ u ∧ v ≠ F.mate u}

/-- The partner function of the contraction of `P` at the `F`-edge `{u, F u}`: the ends
`P u` and `P (F u)` become partners, and every other vertex keeps its `P`-partner. -/
def contractFn (P F : PerfectMatching V) (u v : V) : V :=
  if v = P.mate u then P.mate (F.mate u)
  else if v = P.mate (F.mate u) then P.mate u else P.mate v

/-- The contraction maps `V ∖ {u, F u}` into itself (`results/switching-j0-spike.md`,
Identity D). -/
theorem contractFn_mem (P F : PerfectMatching V) (u : V) {v : V}
    (hv : v ≠ u ∧ v ≠ F.mate u) :
    contractFn P F u v ≠ u ∧ contractFn P F u v ≠ F.mate u := by
  unfold contractFn
  by_cases h1 : v = P.mate u
  · subst h1
    simp only [↓reduceIte]
    exact ⟨fun h ↦ hv.2 (P.mate_eq_comm.mp h), P.mate_ne _⟩
  · by_cases h2 : v = P.mate (F.mate u)
    · subst h2
      simp only [h1, ↓reduceIte]
      exact ⟨P.mate_ne u, fun h ↦ hv.1 (P.mate_eq_comm.mp h)⟩
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨fun h ↦ h1 (P.mate_eq_comm.mp h).symm, fun h ↦ h2 (P.mate_eq_comm.mp h).symm⟩

/-- The contraction is an involution on `V ∖ {u, F u}` (`results/switching-j0-spike.md`,
Identity D). -/
theorem contractFn_contractFn (P F : PerfectMatching V) (u : V) {v : V}
    (hv : v ≠ u ∧ v ≠ F.mate u) : contractFn P F u (contractFn P F u v) = v := by
  have hab : P.mate (F.mate u) ≠ P.mate u := fun h ↦ F.mate_ne u (P.mate.injective h)
  unfold contractFn
  by_cases h1 : v = P.mate u
  · subst h1
    simp [hab]
  · by_cases h2 : v = P.mate (F.mate u)
    · subst h2
      simp [h1]
    · have h3 : P.mate v ≠ P.mate u := fun h ↦ hv.1 (P.mate.injective h)
      have h4 : P.mate v ≠ P.mate (F.mate u) := fun h ↦ hv.2 (P.mate.injective h)
      simp [h1, h2, h3, h4]

/-- The contraction has no fixed point (`results/switching-j0-spike.md`, Identity D). -/
theorem contractFn_ne (P F : PerfectMatching V) (u v : V) : contractFn P F u v ≠ v := by
  have hab : P.mate (F.mate u) ≠ P.mate u := fun h ↦ F.mate_ne u (P.mate.injective h)
  unfold contractFn
  by_cases h1 : v = P.mate u
  · subst h1
    simpa using hab
  · by_cases h2 : v = P.mate (F.mate u)
    · subst h2
      simpa [h1] using hab.symm
    · simpa [h1, h2] using P.mate_ne v

/-- The contraction sends `P u` to `P (F u)` (`results/switching-j0-spike.md`, Identity D). -/
theorem contractFn_left (P F : PerfectMatching V) (u : V) :
    contractFn P F u (P.mate u) = P.mate (F.mate u) := by
  simp [contractFn]

/-- Off `P u` and `P (F u)` the contraction agrees with `P` (`results/switching-j0-spike.md`,
Identity D). -/
theorem contractFn_of_ne (P F : PerfectMatching V) (u : V) {v : V} (h1 : v ≠ P.mate u)
    (h2 : v ≠ P.mate (F.mate u)) : contractFn P F u v = P.mate v := by
  simp only [contractFn, h1, h2, ↓reduceIte]

/-- The contraction of `P` at the `F`-edge `{u, F u}`, a perfect matching of `V ∖ {u, F u}`.
If `P u = F u` it is the restriction of `P`. Otherwise the path `P u, u, F u, P (F u)` of
`P ∪ F` becomes the edge `{P u, P (F u)}`. -/
def contractAt (P F : PerfectMatching V) (u : V) : PerfectMatching (Rest F u) where
  mate := Function.Involutive.toPerm (fun v ↦ ⟨contractFn P F u v, contractFn_mem P F u v.2⟩)
    fun v ↦ Subtype.ext (contractFn_contractFn P F u v.2)
  mate_mate v := Subtype.ext (contractFn_contractFn P F u v.2)
  mate_ne v h := contractFn_ne P F u v (congrArg Subtype.val h)

/-- The partner function of `contractAt P F u` is `contractFn P F u`
(`results/switching-j0-spike.md`, Identity D). -/
@[simp]
theorem contractAt_mate_val (P F : PerfectMatching V) (u : V) (v : Rest F u) :
    ((contractAt P F u).mate v).1 = contractFn P F u v :=
  rfl

/-- On `V ∖ {u, F u}` the contraction of `F` itself is `F` (`results/switching-j0-spike.md`,
Identity D). -/
theorem contractFn_self (F : PerfectMatching V) (u : V) {v : V} (hv : v ≠ u ∧ v ≠ F.mate u) :
    contractFn F F u v = F.mate v := by
  have h1 : v ≠ F.mate (F.mate u) := by rw [mate_mate]; exact hv.1
  simp only [contractFn, hv.2, h1, ↓reduceIte]

/-- An edge of the contracted union is a path of the original union
(`results/switching-j0-spike.md`, Identity D). -/
theorem reachable_of_adj_contractAt (P F : PerfectMatching V) (u : V) {v w : Rest F u}
    (h : ((contractAt P F u).toGraph ⊔ (contractAt F F u).toGraph).Adj v w) :
    (P.toGraph ⊔ F.toGraph).Reachable v.1 w.1 := by
  set G := P.toGraph ⊔ F.toGraph
  have hP : ∀ a b, P.mate a = b → G.Adj a b := fun a b h ↦ Or.inl h
  have hF : ∀ a b, F.mate a = b → G.Adj a b := fun a b h ↦ Or.inr h
  rcases h with h | h
  · have h' := congrArg Subtype.val h
    rw [contractAt_mate_val] at h'
    unfold contractFn at h'
    by_cases h1 : v.1 = P.mate u
    · simp only [h1, ↓reduceIte] at h'
      exact ((hP _ _ (by rw [h1, mate_mate])).reachable.trans
        (hF _ _ rfl).reachable).trans (hP _ _ h').reachable
    · by_cases h2 : v.1 = P.mate (F.mate u)
      · have hab : P.mate (F.mate u) ≠ P.mate u := fun h ↦ F.mate_ne u (P.mate.injective h)
        simp only [h2, hab, ↓reduceIte] at h'
        exact ((hP _ _ (by rw [h2, mate_mate])).reachable.trans
          (hF _ _ (mate_mate F u)).reachable).trans (hP _ _ h').reachable
      · simp only [h1, h2, ↓reduceIte] at h'
        exact (hP _ _ h').reachable
  · have h' := congrArg Subtype.val h
    rw [contractAt_mate_val, contractFn_self F u v.2] at h'
    exact (hF _ _ h').reachable

/-- Reachability in the contracted union implies reachability in the original union
(`results/switching-j0-spike.md`, Identity D). -/
theorem reachable_of_reachable_contractAt (P F : PerfectMatching V) (u : V) {v w : Rest F u}
    (h : ((contractAt P F u).toGraph ⊔ (contractAt F F u).toGraph).Reachable v w) :
    (P.toGraph ⊔ F.toGraph).Reachable v.1 w.1 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  exact Relation.ReflTransGen.lift' (p := (P.toGraph ⊔ F.toGraph).Adj) Subtype.val
    (fun a b hab ↦ (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (reachable_of_adj_contractAt P F u hab)) v w h

/-- The map sending a component of the contracted union to the component of `P ∪ F` that
contains it. -/
def componentMap (P F : PerfectMatching V) (u : V) :
    ((contractAt P F u).toGraph ⊔ (contractAt F F u).toGraph).ConnectedComponent →
      (P.toGraph ⊔ F.toGraph).ConnectedComponent :=
  Quot.lift (fun v ↦ (P.toGraph ⊔ F.toGraph).connectedComponentMk v.1)
    fun _ _ h ↦ SimpleGraph.ConnectedComponent.eq.mpr (reachable_of_reachable_contractAt P F u h)

/-- `componentMap` sends the component of `v` to the component of `v`
(`results/switching-j0-spike.md`, Identity D). -/
theorem componentMap_mk (P F : PerfectMatching V) (u : V) (v : Rest F u) :
    componentMap P F u
        (((contractAt P F u).toGraph ⊔ (contractAt F F u).toGraph).connectedComponentMk v) =
      (P.toGraph ⊔ F.toGraph).connectedComponentMk v.1 :=
  rfl

/-- If `P u ≠ F u`, contracting at `{u, F u}` loses no cycle (`results/switching-j0-spike.md`,
Identity D): `κ(P ∪ F) ≤ κ(P' ∪ F')`. -/
theorem cycleCount_le_contractAt [Finite V] (P F : PerfectMatching V) (u : V)
    (hu : P.mate u ≠ F.mate u) :
    cycleCount P F ≤ cycleCount (contractAt P F u) (contractAt F F u) := by
  refine Nat.card_le_card_of_surjective (componentMap P F u) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := c.exists_rep
  set G := P.toGraph ⊔ F.toGraph
  have hx : ∀ y : V, (hy : y ≠ u ∧ y ≠ F.mate u) → G.Reachable x y →
      ∃ c', componentMap P F u c' = G.connectedComponentMk x :=
    fun y hy hr ↦ ⟨_, (componentMap_mk P F u ⟨y, hy⟩).trans
      (SimpleGraph.ConnectedComponent.eq.mpr hr.symm)⟩
  by_cases h1 : x = u
  · subst h1
    exact hx (P.mate x) ⟨P.mate_ne x, hu⟩ (SimpleGraph.Adj.reachable (Or.inl rfl))
  by_cases h2 : x = F.mate u
  · subst h2
    exact hx (P.mate (F.mate u)) ⟨fun h ↦ hu (P.mate_eq_comm.mp h), P.mate_ne _⟩
      (SimpleGraph.Adj.reachable (Or.inl rfl))
  exact hx x ⟨h1, h2⟩ (SimpleGraph.Reachable.refl _)

/-- Contracting at `{u, F u}` loses at most the digon `{u, F u}`
(`results/switching-j0-spike.md`, Identity D): `κ(P ∪ F) ≤ κ(P' ∪ F') + 1`. -/
theorem cycleCount_le_contractAt_add_one [Finite V] (P F : PerfectMatching V) (u : V) :
    cycleCount P F ≤ cycleCount (contractAt P F u) (contractAt F F u) + 1 := by
  rw [cycleCount, cycleCount, ← Finite.card_option]
  set G := P.toGraph ⊔ F.toGraph
  refine Nat.card_le_card_of_surjective
    (fun o ↦ o.elim (G.connectedComponentMk u) (componentMap P F u)) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := c.exists_rep
  by_cases h1 : x = u
  · exact ⟨none, by rw [h1]; rfl⟩
  by_cases h2 : x = F.mate u
  · refine ⟨none, SimpleGraph.ConnectedComponent.eq.mpr ?_⟩
    rw [h2]
    exact SimpleGraph.Adj.reachable (Or.inr rfl)
  exact ⟨some (((contractAt P F u).toGraph ⊔ (contractAt F F u).toGraph).connectedComponentMk
    ⟨x, h1, h2⟩), rfl⟩

/-- Contraction is injective on the matchings with `P u = F u` (`results/switching-j0-spike.md`,
Identity D). -/
theorem contractAt_injOn_eq (F : PerfectMatching V) (u : V) {P Q : PerfectMatching V}
    (hP : P.mate u = F.mate u) (hQ : Q.mate u = F.mate u)
    (h : contractAt P F u = contractAt Q F u) :
    P = Q := by
  ext v
  by_cases h1 : v = u
  · rw [h1, hP, hQ]
  by_cases h2 : v = F.mate u
  · rw [h2]
    exact (P.mate_eq_comm.mp hP).trans (Q.mate_eq_comm.mp hQ).symm
  have e := congrArg Subtype.val
    (congrArg (fun R : PerfectMatching (Rest F u) ↦ R.mate ⟨v, h1, h2⟩) h)
  simp only [contractAt_mate_val] at e
  rwa [contractFn_of_ne P F u (hP ▸ h2) (by rwa [P.mate_eq_comm.mp hP]),
    contractFn_of_ne Q F u (hQ ▸ h2) (by rwa [Q.mate_eq_comm.mp hQ])] at e

/-- Contraction together with `P u` is injective on the matchings with `P u ≠ F u`
(`results/switching-j0-spike.md`, Identity D). -/
theorem contractAt_injOn_ne (F : PerfectMatching V) (u : V) {P Q : PerfectMatching V}
    (hPQ : P.mate u = Q.mate u) (h : contractAt P F u = contractAt Q F u) : P = Q := by
  have hwu : P.mate u ≠ u := P.mate_ne u
  by_cases hw : P.mate u = F.mate u
  · exact contractAt_injOn_eq F u hw (hPQ ▸ hw) h
  have hval : ∀ v (hv : v ≠ u ∧ v ≠ F.mate u), contractFn P F u v = contractFn Q F u v :=
    fun v hv ↦ congrArg Subtype.val
      (congrArg (fun R : PerfectMatching (Rest F u) ↦ R.mate ⟨v, hv⟩) h)
  have hw' : P.mate (F.mate u) = Q.mate (F.mate u) := by
    have := hval (P.mate u) ⟨hwu, hw⟩
    rwa [contractFn_left, hPQ, contractFn_left] at this
  ext v
  by_cases h1 : v = u
  · rw [h1, hPQ]
  by_cases h2 : v = F.mate u
  · rw [h2, hw']
  by_cases h3 : v = P.mate u
  · rw [h3, mate_mate, hPQ, mate_mate]
  by_cases h4 : v = P.mate (F.mate u)
  · rw [h4, mate_mate, hw', mate_mate]
  have e := hval v ⟨h1, h2⟩
  rwa [contractFn_of_ne P F u h3 h4, contractFn_of_ne Q F u (hPQ ▸ h3) (hw' ▸ h4)] at e

/-- `|V ∖ {u, F u}| = |V| - 2` (`results/switching-j0-spike.md`, Identity D). -/
theorem card_rest [Fintype V] (F : PerfectMatching V) (u : V) :
    Fintype.card (Rest F u) = Fintype.card V - 2 := by
  rw [Fintype.card_subtype]
  have e : (univ.filter fun v : V ↦ v ≠ u ∧ v ≠ F.mate u) = (univ.erase u).erase (F.mate u) := by
    ext v
    simp [and_comm]
  rw [e, card_erase_of_mem (by simp [F.mate_ne u]), card_erase_of_mem (mem_univ u), card_univ]
  omega

/-- The cycle-count generating function (`results/switching-j0-spike.md`, Identity D and
Proposition D): for `x ≥ 1` and `|V| = 2m`, `∑_P x^κ(P ∪ F) ≤ ∏_{i < m} (x + 2i)`. The spike
states the equality `∑_P x^κ(P ∪ F) = x (x + 2) ⋯ (x + 2m - 2)`, from COD-171. -/
theorem sum_pow_cycleCount_le {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (F : PerfectMatching V),
      Fintype.card V = 2 * m →
        ∑ P : PerfectMatching V, x ^ cycleCount P F ≤ ∏ i ∈ range m, (x + 2 * i) := by
  induction m with
  | zero =>
    intro V _ _ F hV
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp (by simpa using hV)
    have hcard : Fintype.card (PerfectMatching V) = 1 := by
      rw [card_eq_doubleFactorial (n := 0) (by simp)]
      rfl
    simp [cycleCount_of_isEmpty, hcard]
  | succ m ih =>
    intro V _ _ F hV
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    set u := Classical.arbitrary V
    have hR : Fintype.card (Rest F u) = 2 * m := by rw [card_rest, hV]; omega
    have hIH := ih (contractAt F F u) hR
    set S := ∑ P' : PerfectMatching (Rest F u), x ^ cycleCount P' (contractAt F F u) with hS
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hnn : ∀ P' : PerfectMatching (Rest F u), 0 ≤ x ^ cycleCount P' (contractAt F F u) :=
      fun _ ↦ pow_nonneg hx0 _
    have h1 : ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ P.mate u = F.mate u),
        x ^ cycleCount P F ≤ x * S := by
      calc ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ P.mate u = F.mate u),
            x ^ cycleCount P F
          ≤ ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ P.mate u = F.mate u),
              x * x ^ cycleCount (contractAt P F u) (contractAt F F u) := by
            refine sum_le_sum fun P _ ↦ ?_
            rw [← pow_succ']
            exact pow_le_pow_right₀ hx (cycleCount_le_contractAt_add_one P F u)
        _ = x * ∑ P' ∈ (univ.filter (fun P : PerfectMatching V ↦ P.mate u = F.mate u)).image
              (fun P ↦ contractAt P F u), x ^ cycleCount P' (contractAt F F u) := by
            rw [mul_sum, sum_image fun P hP Q hQ h ↦ contractAt_injOn_eq F u (mem_filter.mp hP).2
              (mem_filter.mp hQ).2 h]
        _ ≤ x * S := mul_le_mul_of_nonneg_left
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun P' _ _ ↦ hnn P') hx0
    set T := univ.filter fun v : V ↦ v ≠ u ∧ v ≠ F.mate u
    have hT : T.card = 2 * m := by rw [← Fintype.card_subtype, hR]
    have h2 : ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ ¬P.mate u = F.mate u),
        x ^ cycleCount P F ≤ (2 * m : ℕ) * S := by
      calc ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ ¬P.mate u = F.mate u),
            x ^ cycleCount P F
          ≤ ∑ P ∈ univ.filter (fun P : PerfectMatching V ↦ ¬P.mate u = F.mate u),
              x ^ cycleCount (contractAt P F u) (contractAt F F u) :=
            sum_le_sum fun P hP ↦ pow_le_pow_right₀ hx
              (cycleCount_le_contractAt P F u (mem_filter.mp hP).2)
        _ = ∑ y ∈ (univ.filter (fun P : PerfectMatching V ↦ ¬P.mate u = F.mate u)).image
              (fun P ↦ (contractAt P F u, P.mate u)), x ^ cycleCount y.1 (contractAt F F u) := by
            rw [sum_image fun P _ Q _ h ↦ contractAt_injOn_ne F u (Prod.ext_iff.mp h).2
              (Prod.ext_iff.mp h).1]
        _ ≤ ∑ y ∈ (univ : Finset (PerfectMatching (Rest F u))) ×ˢ T,
              x ^ cycleCount y.1 (contractAt F F u) := by
            refine sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ ↦ hnn y.1
            intro y hy
            obtain ⟨P, hP, rfl⟩ := mem_image.mp hy
            exact mem_product.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, P.mate_ne u,
              (mem_filter.mp hP).2⟩⟩
        _ = (2 * m : ℕ) * S := by
            rw [sum_product, hS, mul_sum]
            refine sum_congr rfl fun P' _ ↦ ?_
            dsimp only
            rw [sum_const, hT, nsmul_eq_mul]
    rw [← sum_filter_add_sum_filter_not univ (fun P : PerfectMatching V ↦ P.mate u = F.mate u),
      prod_range_succ]
    have hprod : 0 ≤ ∏ i ∈ range m, (x + 2 * i) :=
      prod_nonneg fun i _ ↦ by positivity
    calc _ ≤ x * S + (2 * m : ℕ) * S := add_le_add h1 h2
      _ = (x + 2 * m) * S := by push_cast; ring
      _ ≤ (x + 2 * m) * ∏ i ∈ range m, (x + 2 * i) :=
          mul_le_mul_of_nonneg_left hIH (by positivity)
      _ = _ := mul_comm _ _

end Contract

end PerfectMatching

end Pairing
