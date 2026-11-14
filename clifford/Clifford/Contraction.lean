import Pairing.Basic

/-!
# L-A. Contraction lemma (sketch §1)

`A ⊆ V` is a union of edges of `P` (the vertices of the active edges `S`), and `P'` is `P`
off `A`. For `X ∈ PM(A)`, `glue P A hA X` is the matching `X ∪ P'`.

The alternating walk that leaves `a ∈ A` along `Q` visits `evenPt a i = (P Q)^i a` and
`oddPt a i = Q (evenPt a i)`, using `P'`-steps between them. It re-enters `A` at the first
`oddPt a i` lying in `A`. That vertex is `κ_Q a`, and `contract P Q A hA` is the endpoint
pairing `κ_Q ∈ PM(A)`.

`HasClosedCycle P Q A` says `Q ∪ P'` has a closed cycle, encoded as a nonempty vertex set
avoiding `A` and closed under `P` and `Q`.

* `not_ham_glue`, `H_glue_of_hasClosedCycle` : a closed cycle forces `H[X ∪ P', Q] = 0`.
* `ham_glue_iff`, `H_glue` : otherwise `H[X ∪ P', Q] = H_A[X, κ_Q]`.
* `contract_mate_of_mem` : a `Q`-edge inside `A` is a path of length `1` and `κ_Q` keeps it.
  If `X` also contains it, `X ∪ κ_Q` has a doubled edge, which is one cycle on `A` exactly when
  `|A| = 2`, matching the convention in `Ham`.
-/

namespace Pairing

private theorem reachable_map_of_adj {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    (f : α → β) (h : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b)) {a b : α}
    (hab : G.Reachable a b) : G'.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

private theorem mem_of_reachable {α : Type*} {G : SimpleGraph α} {D : Set α}
    (hD : ∀ v w, G.Adj v w → v ∈ D → w ∈ D) {a b : α} (hab : G.Reachable a b) (ha : a ∈ D) :
    b ∈ D := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hD _ _ hadj ha)

namespace PerfectMatching

section Union

variable {W : Type*} (X Y : PerfectMatching W)

/-- Adjacency in the union graph `X ∪ Y`. -/
theorem sup_toGraph_adj (v w : W) :
    (X.toGraph ⊔ Y.toGraph).Adj v w ↔ X.mate v = w ∨ Y.mate v = w :=
  Iff.rfl

/-- `v` is joined to its `X`-partner in `X ∪ Y`. -/
theorem adj_mate_left (v : W) : (X.toGraph ⊔ Y.toGraph).Adj v (X.mate v) :=
  Or.inl rfl

/-- `v` is joined to its `Y`-partner in `X ∪ Y`. -/
theorem adj_mate_right (v : W) : (X.toGraph ⊔ Y.toGraph).Adj v (Y.mate v) :=
  Or.inr rfl

end Union

variable {V : Type*}

section Glue

variable [DecidableEq V] (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)

omit [DecidableEq V] in
include hA in
/-- A union of edges of `P` is closed under `P` in both directions. -/
theorem mate_mem_iff (v : V) : P.mate v ∈ A ↔ v ∈ A :=
  ⟨fun h ↦ P.mate_mate v ▸ hA _ h, hA v⟩

/-- The vertex map of `X ∪ P'`. -/
def glueFun (X : PerfectMatching A) (v : V) : V :=
  if h : v ∈ A then X.mate ⟨v, h⟩ else P.mate v

include hA in
theorem glueFun_involutive (X : PerfectMatching A) : Function.Involutive (glueFun P A X) := by
  intro v
  by_cases h : v ∈ A
  · simp [glueFun, h]
  · have h' : P.mate v ∉ A := fun h' ↦ h ((mate_mem_iff P A hA v).mp h')
    simp [glueFun, h, h']

/-- `X ∪ P'`, equal to `X` on `A` and to `P` off `A`. -/
def glue (X : PerfectMatching A) : PerfectMatching V where
  mate := Function.Involutive.toPerm _ (glueFun_involutive P A hA X)
  mate_mate := glueFun_involutive P A hA X
  mate_ne v := by
    by_cases h : v ∈ A
    · simpa [glueFun, h, Subtype.ext_iff] using X.mate_ne ⟨v, h⟩
    · simpa [glueFun, h] using P.mate_ne v

theorem glue_mate_of_mem (X : PerfectMatching A) {v : V} (h : v ∈ A) :
    (glue P A hA X).mate v = X.mate ⟨v, h⟩ := by
  simp [glue, glueFun, h]

theorem glue_mate_coe (X : PerfectMatching A) (a : A) : (glue P A hA X).mate a = X.mate a := by
  simp [glue, glueFun]

theorem glue_mate_of_notMem (X : PerfectMatching A) {v : V} (h : v ∉ A) :
    (glue P A hA X).mate v = P.mate v := by
  simp [glue, glueFun, h]

/-- `P|_A`, the active edges `S` as a matching of `A`. -/
def restrict : PerfectMatching A where
  mate := P.mate.subtypePerm fun v ↦ mate_mem_iff P A hA v
  mate_mate a := Subtype.ext (P.mate_mate a)
  mate_ne a h := P.mate_ne a (congrArg Subtype.val h)

/-- `P = P|_A ∪ P'`. -/
theorem glue_restrict : glue P A hA (restrict P A hA) = P := by
  ext v
  by_cases h : v ∈ A
  · rw [glue_mate_of_mem P A hA _ h]
    rfl
  · rw [glue_mate_of_notMem P A hA _ h]

end Glue

section Walk

variable (P Q : PerfectMatching V)

/-- `w_{2i} = (P Q)^i a`, the even positions of the alternating walk leaving `a` along `Q`. -/
def evenPt (a : V) (i : ℕ) : V :=
  ((P.mate * Q.mate) ^ i) a

/-- `w_{2i+1} = Q w_{2i}`. -/
def oddPt (a : V) (i : ℕ) : V :=
  Q.mate (evenPt P Q a i)

@[simp]
theorem evenPt_zero (a : V) : evenPt P Q a 0 = a := by
  simp [evenPt]

theorem evenPt_succ (a : V) (i : ℕ) : evenPt P Q a (i + 1) = P.mate (oddPt P Q a i) := by
  simp [evenPt, oddPt, pow_succ']

@[simp]
theorem mate_oddPt (a : V) (i : ℕ) : Q.mate (oddPt P Q a i) = evenPt P Q a i := by
  simp [oddPt]

theorem mate_evenPt_succ (a : V) (i : ℕ) : P.mate (evenPt P Q a (i + 1)) = oddPt P Q a i := by
  rw [evenPt_succ, mate_mate]

/-- The walk leaving `w_{2m+1}` along `Q` retraces `w_{2m+1}, w_{2m}, …, w_0`. -/
theorem evenPt_oddPt_rev (a : V) (m : ℕ) {i : ℕ} (hi : i ≤ m) :
    evenPt P Q (oddPt P Q a m) i = oddPt P Q a (m - i) ∧
      oddPt P Q (oddPt P Q a m) i = evenPt P Q a (m - i) := by
  induction i with
  | zero => simp [oddPt]
  | succ i ih =>
    have h2 := (ih (by omega)).2
    have he : evenPt P Q (oddPt P Q a m) (i + 1) = oddPt P Q a (m - (i + 1)) := by
      rw [evenPt_succ, h2, show m - i = m - (i + 1) + 1 by omega, mate_evenPt_succ]
    refine ⟨he, ?_⟩
    change Q.mate (evenPt P Q (oddPt P Q a m) (i + 1)) = _
    rw [he, mate_oddPt]

end Walk

section Contract

variable [Fintype V] [DecidableEq V] (P Q : PerfectMatching V) (A : Finset V)
  (hA : ∀ v ∈ A, P.mate v ∈ A)

omit [Fintype V] [DecidableEq V] in
include hA in
/-- The walk leaving `a ∈ A` along `Q` re-enters `A` on some `Q`-step. -/
theorem exists_oddPt_mem [Finite V] {a : V} (ha : a ∈ A) : ∃ i, oddPt P Q a i ∈ A := by
  have hpos := orderOf_pos (P.mate * Q.mate)
  have h1 : P.mate (oddPt P Q a (orderOf (P.mate * Q.mate) - 1)) = a := by
    rw [← evenPt_succ, Nat.sub_add_cancel hpos, evenPt, pow_orderOf_eq_one,
      Equiv.Perm.one_apply]
  refine ⟨orderOf (P.mate * Q.mate) - 1, ?_⟩
  rw [← P.mate_mate (oddPt P Q a _), h1]
  exact hA a ha

/-- The number of `P'`-steps the walk from `a` takes before re-entering `A`. -/
def exitIdx (a : A) : ℕ :=
  Nat.find (exists_oddPt_mem P Q A hA a.2)

theorem oddPt_exitIdx_mem (a : A) : oddPt P Q a (exitIdx P Q A hA a) ∈ A :=
  Nat.find_spec (exists_oddPt_mem P Q A hA a.2)

theorem oddPt_notMem (a : A) {i : ℕ} (hi : i < exitIdx P Q A hA a) : oddPt P Q a i ∉ A :=
  Nat.find_min (exists_oddPt_mem P Q A hA a.2) hi

theorem evenPt_notMem (a : A) {i : ℕ} (h0 : 0 < i) (hi : i ≤ exitIdx P Q A hA a) :
    evenPt P Q a i ∉ A := by
  cases i with
  | zero => omega
  | succ j =>
    rw [evenPt_succ, mate_mem_iff P A hA]
    exact oddPt_notMem P Q A hA a (by omega)

/-- The exit vertex `κ_Q a`. -/
def contractFun (a : A) : A :=
  ⟨oddPt P Q a (exitIdx P Q A hA a), oddPt_exitIdx_mem P Q A hA a⟩

theorem coe_contractFun (a : A) :
    (contractFun P Q A hA a : V) = oddPt P Q a (exitIdx P Q A hA a) :=
  rfl

/-- The path from `κ_Q a` back to `a` has the same length. -/
theorem exitIdx_contractFun (a : A) :
    exitIdx P Q A hA (contractFun P Q A hA a) = exitIdx P Q A hA a := by
  change Nat.find (exists_oddPt_mem P Q A hA (contractFun P Q A hA a).2) = _
  rw [Nat.find_eq_iff]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [coe_contractFun, (evenPt_oddPt_rev P Q a (exitIdx P Q A hA a) le_rfl).2, Nat.sub_self,
      evenPt_zero]
    exact a.2
  · rw [coe_contractFun, (evenPt_oddPt_rev P Q a (exitIdx P Q A hA a) hi.le).2]
    exact evenPt_notMem P Q A hA a (by omega) (by omega)

theorem contractFun_involutive : Function.Involutive (contractFun P Q A hA) := by
  intro a
  apply Subtype.ext
  rw [coe_contractFun, exitIdx_contractFun, coe_contractFun,
    (evenPt_oddPt_rev P Q a (exitIdx P Q A hA a) le_rfl).2, Nat.sub_self, evenPt_zero]

/-- A path of `Q ∪ P'` has two distinct ends. -/
theorem contractFun_ne (a : A) : contractFun P Q A hA a ≠ a := by
  intro h
  have hc : oddPt P Q a (exitIdx P Q A hA a) = a := congrArg Subtype.val h
  generalize exitIdx P Q A hA a = m at hc
  have hrev : ∀ i ≤ m, evenPt P Q a i = oddPt P Q a (m - i) := fun i hi ↦ by
    have := (evenPt_oddPt_rev P Q a m hi).1
    rwa [hc] at this
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' m
  · have := hrev t (by omega)
    rw [show 2 * t - t = t by omega] at this
    exact Q.mate_ne (evenPt P Q a t) this.symm
  · have := hrev (t + 1) (by omega)
    rw [show 2 * t + 1 - (t + 1) = t by omega, evenPt_succ] at this
    exact P.mate_ne _ this

/-- `κ_Q ∈ PM(A)`, pairing the two ends of each path of `Q ∪ P'`. -/
def contract : PerfectMatching A where
  mate := Function.Involutive.toPerm _ (contractFun_involutive P Q A hA)
  mate_mate := contractFun_involutive P Q A hA
  mate_ne := contractFun_ne P Q A hA

theorem contract_mate (a : A) : (contract P Q A hA).mate a = contractFun P Q A hA a :=
  rfl

/-- A `Q`-edge inside `A` is a path of length `1`, so `κ_Q` keeps it. -/
theorem contract_mate_of_mem (a : A) (h : Q.mate a ∈ A) :
    ((contract P Q A hA).mate a : V) = Q.mate a := by
  have h0 : exitIdx P Q A hA a = 0 := Nat.find_eq_zero _ |>.mpr (by simpa [oddPt] using h)
  rw [contract_mate, coe_contractFun, h0]
  simp [oddPt]

/-- Each `a ∈ A` is joined to `κ_Q a` in `(X ∪ P') ∪ Q`. -/
theorem reachable_contract (X : PerfectMatching A) (a : A) :
    ((glue P A hA X).toGraph ⊔ Q.toGraph).Reachable a ((contract P Q A hA).mate a) := by
  have key : ∀ i ≤ exitIdx P Q A hA a,
      ((glue P A hA X).toGraph ⊔ Q.toGraph).Reachable a (oddPt P Q a i) := by
    intro i hi
    induction i with
    | zero =>
      have h0 : oddPt P Q a 0 = Q.mate a := by simp [oddPt]
      rw [h0]
      exact (adj_mate_right _ _ _).reachable
    | succ i ih =>
      have hn := oddPt_notMem P Q A hA a (i := i) (by omega)
      have h1 : ((glue P A hA X).toGraph ⊔ Q.toGraph).Adj (oddPt P Q a i)
          (evenPt P Q a (i + 1)) := by
        rw [evenPt_succ, ← glue_mate_of_notMem P A hA X hn]
        exact adj_mate_left _ _ _
      exact (ih (by omega)).trans
        (h1.reachable.trans (adj_mate_right _ _ (evenPt P Q a (i + 1))).reachable)
  rw [contract_mate, coe_contractFun]
  exact key _ le_rfl

end Contract

/-- `Q ∪ P'` contains a closed cycle, encoded as a nonempty vertex set avoiding `A` and closed
under `P` and `Q`. -/
def HasClosedCycle [DecidableEq V] (P Q : PerfectMatching V) (A : Finset V) : Prop :=
  ∃ C : Finset V, C.Nonempty ∧ Disjoint C A ∧ (∀ v ∈ C, P.mate v ∈ C) ∧ ∀ v ∈ C, Q.mate v ∈ C

section Main

variable [Fintype V] [DecidableEq V] (P Q : PerfectMatching V) (A : Finset V)
  (hA : ∀ v ∈ A, P.mate v ∈ A)

omit [Fintype V] in
/-- Sketch §1, closed-cycle case. -/
theorem not_ham_glue (hC : HasClosedCycle P Q A) (hA0 : A.Nonempty) (X : PerfectMatching A) :
    ¬Ham (glue P A hA X) Q := by
  obtain ⟨C, ⟨v, hv⟩, hdisj, hP, hQ⟩ := hC
  obtain ⟨a, ha⟩ := hA0
  intro hU
  have hD : ∀ x y, ((glue P A hA X).toGraph ⊔ Q.toGraph).Adj x y →
      x ∈ (C : Set V) → y ∈ (C : Set V) := by
    intro x y hxy hx
    have hxA : x ∉ A := Finset.disjoint_left.mp hdisj hx
    rcases (sup_toGraph_adj _ _ x y).mp hxy with rfl | rfl
    · rw [glue_mate_of_notMem P A hA X hxA]
      exact hP x hx
    · exact hQ x hx
  exact Finset.disjoint_left.mp hdisj (mem_of_reachable hD (hU.preconnected v a) hv) ha

/-- Sketch §1, path case: `X ∪ P' ∪ Q` is one cycle iff `X ∪ κ_Q` is one cycle on `A`. -/
theorem ham_glue_iff (hC : ¬HasClosedCycle P Q A) (X : PerfectMatching A) :
    Ham (glue P A hA X) Q ↔ Ham X (contract P Q A hA) := by
  classical
  unfold Ham
  constructor
  · intro hU
    have hA0 : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      obtain ⟨v⟩ := hU.nonempty
      exact hC ⟨Finset.univ, ⟨v, Finset.mem_univ v⟩, Finset.disjoint_empty_right _,
        fun _ _ ↦ Finset.mem_univ _, fun _ _ ↦ Finset.mem_univ _⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun a b ↦ ?_, hA0.to_subtype⟩
    let D : Set V := {v | ∃ c : A, (X.toGraph ⊔ (contract P Q A hA).toGraph).Reachable a c ∧
      ∃ i ≤ exitIdx P Q A hA c, v = evenPt P Q c i ∨ v = oddPt P Q c i}
    have hQ : ∀ v ∈ D, Q.mate v ∈ D := by
      rintro v ⟨c, hac, i, hi, rfl | rfl⟩
      · exact ⟨c, hac, i, hi, Or.inr rfl⟩
      · exact ⟨c, hac, i, hi, Or.inl (mate_oddPt P Q c i)⟩
    have hY : ∀ v ∈ D, (glue P A hA X).mate v ∈ D := by
      rintro v ⟨c, hac, i, hi, rfl | rfl⟩
      · cases i with
        | zero =>
          refine ⟨X.mate c, hac.trans (adj_mate_left _ _ c).reachable, 0, Nat.zero_le _,
            Or.inl ?_⟩
          simp only [evenPt_zero]
          exact glue_mate_coe P A hA X c
        | succ j =>
          have hn : evenPt P Q c (j + 1) ∉ A := evenPt_notMem P Q A hA c (Nat.succ_pos j) hi
          refine ⟨c, hac, j, by omega, Or.inr ?_⟩
          rw [glue_mate_of_notMem P A hA X hn, mate_evenPt_succ]
      · rcases lt_or_eq_of_le hi with hlt | rfl
        · have hn := oddPt_notMem P Q A hA c hlt
          refine ⟨c, hac, i + 1, hlt, Or.inl ?_⟩
          rw [glue_mate_of_notMem P A hA X hn, evenPt_succ]
        · refine ⟨X.mate ((contract P Q A hA).mate c),
            (hac.trans (adj_mate_right _ _ c).reachable).trans (adj_mate_left _ _ _).reachable,
            0, Nat.zero_le _, Or.inl ?_⟩
          rw [evenPt_zero, ← coe_contractFun, ← contract_mate, glue_mate_coe]
    have hD : ∀ v w, ((glue P A hA X).toGraph ⊔ Q.toGraph).Adj v w → v ∈ D → w ∈ D := by
      intro v w hvw hv
      rcases (sup_toGraph_adj _ _ v w).mp hvw with rfl | rfl
      · exact hY v hv
      · exact hQ v hv
    have hb : (b : V) ∈ D := mem_of_reachable hD (hU.preconnected a b)
      ⟨a, SimpleGraph.Reachable.refl _, 0, Nat.zero_le _, Or.inl (evenPt_zero P Q a).symm⟩
    obtain ⟨c, hac, i, hi, hb | hb⟩ := hb
    · cases i with
      | zero =>
        rw [evenPt_zero] at hb
        rwa [Subtype.ext hb]
      | succ j => exact absurd (hb ▸ b.2) (evenPt_notMem P Q A hA c (Nat.succ_pos j) hi)
    · rcases lt_or_eq_of_le hi with hlt | rfl
      · exact absurd (hb ▸ b.2) (oddPt_notMem P Q A hA c hlt)
      · rw [← coe_contractFun, ← contract_mate] at hb
        rw [Subtype.ext hb]
        exact hac.trans (adj_mate_right _ _ c).reachable
  · intro hK
    have hreach : ∀ v, ∃ a ∈ A, ((glue P A hA X).toGraph ⊔ Q.toGraph).Reachable v a := by
      by_contra! hv
      obtain ⟨v, hv⟩ := hv
      refine hC ⟨Finset.univ.filter fun w ↦
          ∀ a ∈ A, ¬((glue P A hA X).toGraph ⊔ Q.toGraph).Reachable w a,
        ⟨v, by simpa using hv⟩, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro w hw hwA
        exact (Finset.mem_filter.mp hw).2 w hwA (SimpleGraph.Reachable.refl _)
      · intro w hw
        have hw' := (Finset.mem_filter.mp hw).2
        have hwA : w ∉ A := fun h ↦ hw' w h (SimpleGraph.Reachable.refl _)
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha hr ↦ hw' a ha ?_⟩
        rw [← glue_mate_of_notMem P A hA X hwA] at hr
        exact (adj_mate_left _ _ w).reachable.trans hr
      · intro w hw
        have hw' := (Finset.mem_filter.mp hw).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha hr ↦ hw' a ha ?_⟩
        exact (adj_mate_right _ _ w).reachable.trans hr
    have hAA : ∀ a b : A, ((glue P A hA X).toGraph ⊔ Q.toGraph).Reachable a b := by
      intro a b
      refine reachable_map_of_adj Subtype.val (fun c d hcd ↦ ?_) (hK.preconnected a b)
      rcases (sup_toGraph_adj _ _ c d).mp hcd with rfl | rfl
      · rw [← glue_mate_coe P A hA X c]
        exact (adj_mate_left _ _ _).reachable
      · exact reachable_contract P Q A hA X c
    obtain ⟨a0⟩ := hK.nonempty
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v ↦ ?_, ⟨a0⟩⟩
    obtain ⟨a, ha, hua⟩ := hreach u
    obtain ⟨b, hb, hvb⟩ := hreach v
    exact hua.trans ((hAA ⟨a, ha⟩ ⟨b, hb⟩).trans hvb.symm)

/-- `H[X ∪ P', Q] = 0` when `Q ∪ P'` has a closed cycle. -/
theorem H_glue_of_hasClosedCycle (hC : HasClosedCycle P Q A) (hA0 : A.Nonempty)
    (X : PerfectMatching A) : H (glue P A hA X) Q = 0 := by
  simp [H_apply, not_ham_glue P Q A hA hC hA0 X]

/-- `H[X ∪ P', Q] = H_A[X, κ_Q]` when `Q ∪ P'` is a union of paths. -/
theorem H_glue (hC : ¬HasClosedCycle P Q A) (X : PerfectMatching A) :
    H (glue P A hA X) Q = H X (contract P Q A hA) := by
  simp only [H_apply, ham_glue_iff P Q A hA hC X]

end Main

end PerfectMatching

end Pairing
