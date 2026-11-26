import Repair.Insertion

/-!
# Free defects (Corollary 5.1 of the joint-incoherence spike, corrected)

`B` is `F_0` restricted to `V(E)`, so its edges are the labels of `E`. `A = V(E_0)` is a union
of edges of `B`, and the labels outside `A` form `Y`. The restriction of a context `C` of `E` to
`E_0` (skip the `Y`-labels) is `contract B C A`, and `R_0 = contract B R A` is `R` shortcut at
all of `Y`. `closedCount R B A = c_Y` counts the cycles of `R ∪ B` that avoid `A`, the cycles
that `R ∪ F_0|_Y` closes inside `Y`.

* `exists_context_extension` : every context `C'` of `E_0` extends to a context `C` of `E` that
  restricts to `C'`, with `κ(R ∪ C) ≤ 1` or `κ(R ∪ C) + |Y| ≤ κ(R_0 ∪ C') + c_Y`.
* `free_defects` : Corollary 5.1 in corrected form. If `Y` is free over `E_0` and `X(E, R) = 0`,
  every realized context `C'` of `E_0` has `κ(R_0 ∪ C') ≥ |Y| − c_Y + 2`, and
  `|Y| − c_Y ≤ |E_0| − 2`.

Source: `results/hybrid-joint-incoherence.md` (organize-archive 4f82c7d), Corollary 5.1. As
stated there the bound `|Y| ≤ |E_0| − 2` is false when `R ∪ F_0|_Y` closes cycles inside `Y`,
which `R ∩ F_0 = ∅` allows (`results/review-hybrid-joint-incoherence.md`). The reinsertion of a
label on such a cycle meets `R(y₊) = y₋` and cannot lower `κ`. The corrected bound subtracts
`c_Y`.
-/

namespace Pairing

namespace PerfectMatching

section General

variable {V : Type*}

private theorem mem_of_reachable'' {G : SimpleGraph V} {D : Set V}
    (hD : ∀ v w, G.Adj v w → v ∈ D → w ∈ D) {a b : V} (hab : G.Reachable a b) (ha : a ∈ D) :
    b ∈ D := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hD _ _ hadj ha)

/-- `offGraph` shrinks as `A` grows.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem offGraph_mono (P : PerfectMatching V) {A A' : Finset V} (hA : ∀ v ∈ A, P.mate v ∈ A)
    (hA' : ∀ v ∈ A', P.mate v ∈ A') (h : A ⊆ A') : offGraph P A' hA' ≤ offGraph P A hA :=
  fun _ _ hvw ↦ ⟨hvw.1, fun hv ↦ hvw.2 (h hv)⟩

variable [Fintype V] [DecidableEq V]

/-- `κ_Q a` is the unique `w ∈ A`, `w ≠ a`, joined to `a` in `Q ∪ (P off A)`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem contract_mate_eq (P Q : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)
    (a w : A) (hw : w ≠ a) (h : (Q.toGraph ⊔ offGraph P A hA).Reachable a w) :
    (contract P Q A hA).mate a = w := by
  rcases eq_or_eq_contractFun_of_reachable P Q A hA a w.2 h with h' | h'
  · exact absurd (Subtype.ext h') hw
  · rw [contract_mate]
    exact (Subtype.ext h').symm

omit [Fintype V] [DecidableEq V] in
/-- `R ∪ C` and its transport along `e` have the same cycles.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem cycleCount_congr {W : Type*} (e : V ≃ W) (P Q : PerfectMatching V) :
    cycleCount (congr e P) (congr e Q) = cycleCount P Q :=
  (card_connectedComponent_eq_of_retract e.symm e
    (fun v w h ↦ (congrUnionIso e P Q).symm.map_adj_iff.mpr h |>.reachable)
    (fun v w h ↦ ((congrUnionIso e P Q).map_adj_iff.mpr h).reachable)
    (fun v ↦ by simp) (fun w ↦ by simp))

omit [Fintype V] [DecidableEq V] in
/-- Reachability is transported along `e`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem reachable_congr {W : Type*} (e : V ≃ W) (P Q : PerfectMatching V) (u v : V) :
    ((congr e P).toGraph ⊔ (congr e Q).toGraph).Reachable (e u) (e v) ↔
      (P.toGraph ⊔ Q.toGraph).Reachable u v :=
  (congrUnionIso e P Q).reachable_iff

end General

section Count

variable {W : Type*} [Finite W]

/-- Components of a graph in which every vertex is joined to a distinct partner have at least
two vertices each.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem two_mul_card_le (G : SimpleGraph W) (σ : W → W) (hσ : ∀ v, σ v ≠ v)
    (hr : ∀ v, G.Reachable v (σ v)) (K : G.ConnectedComponent → Prop) (S : Finset W)
    (hS : ∀ v, K (G.connectedComponentMk v) → v ∈ S) :
    2 * Nat.card {c // K c} ≤ S.card := by
  classical
  have hout : ∀ c : G.ConnectedComponent, G.connectedComponentMk (Quot.out c) = c :=
    fun c ↦ Quot.out_eq c
  let f : {c // K c} × Bool → S := fun x ↦
    if x.2 then ⟨Quot.out x.1.1, hS _ ((hout x.1.1).symm ▸ x.1.2)⟩
    else ⟨σ (Quot.out x.1.1), hS _ (by
      rw [show G.connectedComponentMk (σ (Quot.out x.1.1)) = x.1.1 from
        (SimpleGraph.ConnectedComponent.sound (hr _)).symm.trans (hout _)]
      exact x.1.2)⟩
  have hf : Function.Injective f := by
    have key : ∀ x : {c // K c} × Bool, G.connectedComponentMk (f x : W) = x.1.1 := by
      rintro ⟨c, b⟩
      cases b
      · exact (SimpleGraph.ConnectedComponent.sound (hr _)).symm.trans (hout _)
      · exact hout _
    rintro ⟨c, b⟩ ⟨c', b'⟩ h
    have hc : c = c' := Subtype.ext ((key (c, b)).symm.trans
      ((congrArg (fun z : S ↦ G.connectedComponentMk (z : W)) h).trans (key (c', b'))))
    subst hc
    cases b <;> cases b'
    · rfl
    · exact absurd (congrArg Subtype.val h) (hσ _)
    · exact absurd (congrArg Subtype.val h).symm (hσ _)
    · rfl
  have := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card Bool = 2 := by simp
  have hS' : Nat.card S = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_prod, h2, hS'] at this
  omega

end Count

section Step

variable [Fintype V] [DecidableEq V] (B R : PerfectMatching V) {A : Finset V}
  (hA : ∀ v ∈ A, B.mate v ∈ A) {yp : V}

/-- `A ∪ {y₊, y₋}`, the vertex set after reinserting the label `y = {y₊, B y₊}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
def grow (A : Finset V) (yp : V) : Finset V := insert yp (insert (B.mate yp) A)

omit [Fintype V] in
/-- Membership in `A ∪ {y₊, y₋}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem mem_grow {v : V} : v ∈ grow B A yp ↔ v = yp ∨ v = B.mate yp ∨ v ∈ A := by
  simp [grow]

omit [Fintype V] in
include hA in
/-- `A ∪ {y₊, y₋}` is a union of edges of `B`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem grow_closed : ∀ v ∈ grow B A yp, B.mate v ∈ grow B A yp := by
  intro v hv
  rw [mem_grow] at hv ⊢
  rcases hv with h | h | hv
  · rw [h]
    exact Or.inr (Or.inl rfl)
  · rw [h, mate_mate]
    exact Or.inl rfl
  · exact Or.inr (Or.inr (hA v hv))

omit [Fintype V] [DecidableEq V] in
include hA in
/-- The partner `y₋ = B y₊` of a label outside `A` is outside `A`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem mate_notMem (hyp : yp ∉ A) : B.mate yp ∉ A := fun h ↦ hyp (B.mate_mate yp ▸ hA _ h)

omit [Fintype V] in
/-- `A ⊆ A ∪ {y₊, y₋}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem subset_grow : A ⊆ grow B A yp := fun _ hv ↦ (mem_grow B).mpr (Or.inr (Or.inr hv))

/-- `c_Y`, the number of cycles of `R ∪ B` that avoid `A`: the cycles that `R ∪ F_0|_Y`
closes inside `Y` (`results/hybrid-joint-incoherence.md`, Corollary 5.1, corrected). -/
noncomputable def closedCount (R B : PerfectMatching V) (A : Finset V) : ℕ :=
  Set.ncard {c : (R.toGraph ⊔ B.toGraph).ConnectedComponent |
    ∀ v, (R.toGraph ⊔ B.toGraph).connectedComponentMk v = c → v ∉ A}

/-- `c_Y ≤ |Y|`: every cycle of `R ∪ B` inside `Y` contains a whole label.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem closedCount_le (n : ℕ) (hn : Aᶜ.card = 2 * n) : closedCount R B A ≤ n := by
  have h := two_mul_card_le (R.toGraph ⊔ B.toGraph) B.mate B.mate_ne
    (fun v ↦ (adj_mate_right R B v).reachable)
    (fun c ↦ ∀ v, (R.toGraph ⊔ B.toGraph).connectedComponentMk v = c → v ∉ A) Aᶜ
    (fun v hv ↦ Finset.mem_compl.mpr (hv v rfl))
  rw [closedCount, ← Nat.card_coe_set_eq, Set.coe_ofPred]
  omega

variable (hyp : yp ∉ A)

/-- The two ends of the reinserted label as points of `A ∪ {y₊, y₋}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
def yP : grow B A yp := ⟨yp, (mem_grow B).mpr (Or.inl rfl)⟩

/-- The second end `y₋ = B y₊`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
def yM : grow B A yp := ⟨B.mate yp, (mem_grow B).mpr (Or.inr (Or.inl rfl))⟩

omit [Fintype V] [DecidableEq V] in
include hA hyp in
/-- Points of `A` are neither `y₊` nor `y₋`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem lift_ne (v : A) : (v : V) ≠ yp ∧ (v : V) ≠ B.mate yp :=
  ⟨fun h ↦ hyp (h ▸ v.2), fun h ↦ mate_notMem B hA hyp (h ▸ v.2)⟩

omit [Fintype V] in
/-- A point of `A ∪ {y₊, y₋}` other than `y₊`, `y₋` lies in `A`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem mem_A_of_grow (v : grow B A yp) (h1 : (v : V) ≠ yp) (h2 : (v : V) ≠ B.mate yp) :
    (v : V) ∈ A := by
  rcases (mem_grow B).mp v.2 with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

omit [Fintype V] in
include hA in
/-- The walk graph of `R` grows when the level shrinks from `A ∪ {y₊, y₋}` to `A`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem walkGraph_mono (Q : PerfectMatching V) :
    Q.toGraph ⊔ offGraph B (grow B A yp) (grow_closed B hA) ≤ Q.toGraph ⊔ offGraph B A hA :=
  sup_le_sup_left (offGraph_mono B hA (grow_closed B hA) (subset_grow B)) _

omit [Fintype V] [DecidableEq V] in
include hyp in
/-- The label `{y₊, y₋}` is an edge of `B` off `A`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem offGraph_adj_y : (offGraph B A hA).Adj yp (B.mate yp) := ⟨rfl, hyp⟩

include hA hyp in
/-- A non-degenerate reinsertion step: `R` shortcut at `A` is `R` shortcut at `A ∪ {y₊, y₋}`
with `{y₊, a}`, `{y₋, b}` replaced by `{a, b}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem contract_step_nondeg
    (hnd : (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) ≠ yM B) :
    ∃ a b : A, ((contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) : V) = a ∧
      ((contract B R (grow B A yp) (grow_closed B hA)).mate (yM B) : V) = b ∧
      (contract B R A hA).mate a = b ∧
      ∀ v : A, v ≠ a → v ≠ b → ((contract B R A hA).mate v : V) =
        (contract B R (grow B A yp) (grow_closed B hA)).mate ⟨v, subset_grow B v.2⟩ := by
  set K := contract B R (grow B A yp) (grow_closed B hA) with hK
  have hJ := walkGraph_mono B hA (yp := yp) R
  have hreach : ∀ v : grow B A yp, (R.toGraph ⊔ offGraph B A hA).Reachable (v : V) (K.mate v) :=
    fun v ↦
    (reachable_contractFun B R _ (grow_closed B hA) v).mono hJ
  have ha1 : (K.mate (yP B) : V) ≠ yp := fun h ↦ K.mate_ne (yP B) (Subtype.ext h)
  have ha2 : (K.mate (yP B) : V) ≠ B.mate yp := fun h ↦ hnd (Subtype.ext h)
  have hb1 : (K.mate (yM B) : V) ≠ B.mate yp := fun h ↦ K.mate_ne (yM B) (Subtype.ext h)
  have hb2 : (K.mate (yM B) : V) ≠ yp := fun h ↦ hnd (by
    rw [← Subtype.ext (a1 := K.mate (yM B)) (a2 := yP B) h, K.mate_mate])
  have haA := mem_A_of_grow B (K.mate (yP B)) ha1 ha2
  have hbA := mem_A_of_grow B (K.mate (yM B)) hb2 hb1
  refine ⟨⟨_, haA⟩, ⟨_, hbA⟩, rfl, rfl, ?_, fun v hva hvb ↦ ?_⟩
  · apply contract_mate_eq
    · intro h
      have h' : K.mate (yM B) = K.mate (yP B) := Subtype.ext
        (congrArg (fun z : A ↦ (z : V)) h)
      exact absurd (K.mate.injective h') (fun h'' ↦ (B.mate_ne yp) (congrArg Subtype.val h''))
    · exact (hreach (yP B)).symm.trans ((offGraph_adj_y B hA hyp).reachable.mono le_sup_right
        |>.trans (hreach (yM B)))
  · have hv1 : (K.mate ⟨v, subset_grow B v.2⟩ : V) ≠ yp := fun h ↦ hva (by
      apply Subtype.ext
      have : K.mate ⟨v, subset_grow B v.2⟩ = yP B := Subtype.ext h
      change (v : V) = K.mate (yP B)
      rw [← this, K.mate_mate])
    have hv2 : (K.mate ⟨v, subset_grow B v.2⟩ : V) ≠ B.mate yp := fun h ↦ hvb (by
      apply Subtype.ext
      have : K.mate ⟨v, subset_grow B v.2⟩ = yM B := Subtype.ext h
      change (v : V) = K.mate (yM B)
      rw [← this, K.mate_mate])
    have hm := mem_A_of_grow B _ hv1 hv2
    have := contract_mate_eq B R A hA v ⟨_, hm⟩
      (fun h ↦ K.mate_ne ⟨v, subset_grow B v.2⟩ (Subtype.ext
        (congrArg (fun z : A ↦ (z : V)) h)))
      (hreach ⟨v, subset_grow B v.2⟩)
    rw [this]

include hA hyp in
/-- A degenerate reinsertion step, `R(y₊) = y₋` at level `A ∪ {y₊, y₋}`: shortcutting `y`
changes nothing on `A`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem contract_step_deg
    (hd : (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) = yM B) :
    ∀ v : A, ((contract B R A hA).mate v : V) =
      (contract B R (grow B A yp) (grow_closed B hA)).mate ⟨v, subset_grow B v.2⟩ := by
  set K := contract B R (grow B A yp) (grow_closed B hA) with hK
  have hJ := walkGraph_mono B hA (yp := yp) R
  intro v
  have hne := lift_ne B hA hyp v
  have hv1 : (K.mate ⟨v, subset_grow B v.2⟩ : V) ≠ yp := fun h ↦ hne.2 (by
    have : K.mate ⟨v, subset_grow B v.2⟩ = yP B := Subtype.ext h
    have h2 := congrArg (fun z ↦ (K.mate z : V)) this
    simp only [K.mate_mate, hd] at h2
    exact h2)
  have hv2 : (K.mate ⟨v, subset_grow B v.2⟩ : V) ≠ B.mate yp := fun h ↦ hne.1 (by
    have : K.mate ⟨v, subset_grow B v.2⟩ = yM B := Subtype.ext h
    have h2 := congrArg (fun z ↦ (K.mate z : V)) this
    rw [K.mate_mate, ← hd, K.mate_mate] at h2
    exact h2)
  have hm := mem_A_of_grow B _ hv1 hv2
  have := contract_mate_eq B R A hA v ⟨_, hm⟩
    (fun h ↦ K.mate_ne ⟨v, subset_grow B v.2⟩ (Subtype.ext
      (congrArg (fun z : A ↦ (z : V)) h)))
    ((reachable_contractFun B R _ (grow_closed B hA) ⟨v, subset_grow B v.2⟩).mono hJ)
  rw [this]

include hA hyp in
/-- Reinserting `y` is degenerate (`R(y₊) = y₋` at level `A ∪ {y₊, y₋}`) exactly when the cycle
of `R ∪ B` through `y` avoids `A`, and then it is one of the cycles counted by `c_Y`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem closedCount_step :
    closedCount R B A = closedCount R B (grow B A yp) +
      if (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) = yM B then 1 else 0 := by
  classical
  set K := contract B R (grow B A yp) (grow_closed B hA) with hK
  let G := R.toGraph ⊔ B.toGraph
  let SA : Set G.ConnectedComponent := {c | ∀ v, G.connectedComponentMk v = c → v ∉ A}
  let SG : Set G.ConnectedComponent :=
    {c | ∀ v, G.connectedComponentMk v = c → v ∉ grow B A yp}
  have hsub : SG ⊆ SA := fun c hc v hv hvA ↦ hc v hv (subset_grow B hvA)
  have hyG : G.connectedComponentMk yp ∉ SG := fun h ↦ h yp rfl ((mem_grow B).mpr (Or.inl rfl))
  have hdiff : ∀ c ∈ SA, c ∉ SG → c = G.connectedComponentMk yp := by
    intro c hc hcG
    simp only [SG, Set.mem_ofPred_eq, not_forall, not_not] at hcG
    obtain ⟨v, rfl, hv⟩ := hcG
    rcases (mem_grow B).mp hv with h | h | h
    · rw [h]
    · rw [h]
      exact SimpleGraph.ConnectedComponent.sound (adj_mate_right R B yp).reachable.symm
    · exact absurd h (hc v rfl)
  have hJG : R.toGraph ⊔ offGraph B (grow B A yp) (grow_closed B hA) ≤ G :=
    sup_le_sup_left (fun _ _ h ↦ h.1) _
  have hreach := reachable_contractFun B R (grow B A yp) (grow_closed B hA) (yP B)
  rw [← contract_mate] at hreach
  have hfin : SG.Finite := Set.toFinite _
  change SA.ncard = SG.ncard + _
  split_ifs with hd
  · have hyA : G.connectedComponentMk yp ∈ SA := by
      intro v hv
      have hrv : G.Reachable yp v := (SimpleGraph.ConnectedComponent.exact hv).symm
      let T : Set V := {w | (R.toGraph ⊔ offGraph B (grow B A yp) (grow_closed B hA)).Reachable
        yp w}
      have hym : B.mate yp ∈ T := by
        have := hreach
        rw [hd] at this
        exact this
      have hT : ∀ w z, G.Adj w z → w ∈ T → z ∈ T := by
        intro w z hwz hw
        rcases hwz with hwz | hwz
        · exact hw.trans (SimpleGraph.Adj.reachable (Or.inl hwz))
        · change B.mate w = z at hwz
          by_cases hwg : w ∈ grow B A yp
          · rcases eq_or_eq_contractFun_of_reachable B R _ (grow_closed B hA) (yP B) hwg hw
              with h | h
            · rw [← hwz]
              change w = yp at h
              rw [h]
              exact hym
            · rw [← contract_mate, hd] at h
              change w = B.mate yp at h
              rw [← hwz, h, mate_mate]
              exact SimpleGraph.Reachable.refl _
          · exact hw.trans (SimpleGraph.Adj.reachable (Or.inr ⟨hwz, hwg⟩))
      have hvT : v ∈ T := mem_of_reachable'' hT hrv (SimpleGraph.Reachable.refl _)
      intro hvA
      rcases eq_or_eq_contractFun_of_reachable B R _ (grow_closed B hA) (yP B)
        (subset_grow B hvA) hvT with h | h
      · rw [h] at hvA
        exact hyp hvA
      · rw [← contract_mate, hd] at h
        rw [h] at hvA
        exact mate_notMem B hA hyp hvA
    have hSA : SA = insert (G.connectedComponentMk yp) SG := by
      ext c
      refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
      · by_cases hcG : c ∈ SG
        · exact Set.mem_insert_of_mem _ hcG
        · rw [hdiff c hc hcG]
          exact Set.mem_insert _ _
      · rcases hc with rfl | hc
        · exact hyA
        · exact hsub hc
    rw [hSA, Set.ncard_insert_of_notMem hyG hfin]
  · have hnot : G.connectedComponentMk yp ∉ SA := by
      intro h
      have ha1 : (K.mate (yP B) : V) ≠ yp := fun h' ↦ K.mate_ne (yP B) (Subtype.ext h')
      have ha2 : (K.mate (yP B) : V) ≠ B.mate yp := fun h' ↦ hd (Subtype.ext h')
      have haA := mem_A_of_grow B (K.mate (yP B)) ha1 ha2
      exact h _ (SimpleGraph.ConnectedComponent.sound (hreach.mono hJG).symm) haA
    have hSA : SA = SG := by
      ext c
      refine ⟨fun hc ↦ ?_, fun hc ↦ hsub hc⟩
      by_contra hcG
      exact hnot (hdiff c hc hcG ▸ hc)
    rw [hSA, add_zero]

variable (C' : PerfectMatching A) (p : A) {ent : V}

/-- The context `C'` of `E_0` with the label `y` inserted at the slot `{p, C' p}`, entered at
`ent`, as a matching of `V` that is `B` off `A ∪ {y₊, y₋}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
def insertV (ent : V) : PerfectMatching V :=
  Equiv.swap ((C'.mate p : A) : V) ent • glue B A hA C'

variable (hent : ent = yp ∨ ent = B.mate yp)

omit [Fintype V] [DecidableEq V] in
include hA hyp hent in
/-- The two ends of the inserted label lie outside `A` and are distinct.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem ent_notMem : ent ∉ A ∧ B.mate ent ∉ A ∧ ent ≠ B.mate ent := by
  rcases hent with rfl | rfl
  · exact ⟨hyp, mate_notMem B hA hyp, (B.mate_ne _).symm⟩
  · rw [mate_mate]
    exact ⟨mate_notMem B hA hyp, hyp, B.mate_ne _⟩

omit [Fintype V] in
include hyp hent in
/-- The partners in the inserted context: `p–entry`, `q–exit`, and `C'` elsewhere.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem insertV_mate :
    (insertV B hA C' p ent).mate p = ent ∧
      (insertV B hA C' p ent).mate (C'.mate p) = B.mate ent ∧
      (insertV B hA C' p ent).mate ent = p ∧
      (insertV B hA C' p ent).mate (B.mate ent) = C'.mate p ∧
      ∀ v : V, v ≠ p → v ≠ C'.mate p → v ≠ ent → v ≠ B.mate ent →
        (insertV B hA C' p ent).mate v = (glue B A hA C').mate v := by
  obtain ⟨he1, he2, he3⟩ := ent_notMem B hA hyp hent
  set q := C'.mate p with hq
  have hqp : (q : V) ≠ p := fun h ↦ C'.mate_ne p (Subtype.ext h)
  have hpe : (p : V) ≠ ent := fun h ↦ he1 (h ▸ p.2)
  have hqx : (q : V) ≠ B.mate ent := fun h ↦ he2 (h ▸ q.2)
  have g_p : (glue B A hA C').mate p = q := glue_mate_coe B A hA C' p
  have g_q : (glue B A hA C').mate q = p := by rw [glue_mate_coe, hq, C'.mate_mate]
  have g_e : (glue B A hA C').mate ent = B.mate ent := glue_mate_of_notMem B A hA C' he1
  have g_x : (glue B A hA C').mate (B.mate ent) = ent := by
    rw [glue_mate_of_notMem B A hA C' he2, mate_mate]
  have hm : ∀ v, (insertV B hA C' p ent).mate v =
      Equiv.swap (q : V) ent ((glue B A hA C').mate (Equiv.swap (q : V) ent v)) := by
    intro v
    rw [insertV, smul_mate, Equiv.swap_inv]
  refine ⟨?_, ?_, ?_, ?_, fun v h1 h2 h3 h4 ↦ ?_⟩
  · rw [hm, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp) hpe, g_p, Equiv.swap_apply_left]
  · rw [hm, Equiv.swap_apply_left, g_e, Equiv.swap_apply_of_ne_of_ne hqx.symm he3.symm]
  · rw [hm, Equiv.swap_apply_right, g_q, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp) hpe]
  · rw [hm, Equiv.swap_apply_of_ne_of_ne hqx.symm he3.symm, g_x, Equiv.swap_apply_right]
  · rw [hm, Equiv.swap_apply_of_ne_of_ne h2 h3]
    refine Equiv.swap_apply_of_ne_of_ne (fun h ↦ h1 ?_) (fun h ↦ h4 ?_)
    · rw [← (glue B A hA C').mate_mate v, h, g_q]
    · rw [← (glue B A hA C').mate_mate v, h, g_e]

omit [Fintype V] in
include hent in
/-- `A ∪ {y₊, y₋}` described through the entry end of `y`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem mem_grow_iff_ent {v : V} : v ∈ grow B A yp ↔ v = ent ∨ v = B.mate ent ∨ v ∈ A := by
  rw [mem_grow]
  rcases hent with rfl | rfl
  · rfl
  · rw [mate_mate]
    tauto

omit [Fintype V] in
include hyp hent in
/-- The inserted context maps `A ∪ {y₊, y₋}` into itself.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem insertV_closed : ∀ v ∈ grow B A yp, (insertV B hA C' p ent).mate v ∈ grow B A yp := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := insertV_mate B hA hyp C' p hent
  intro v hv
  rw [mem_grow_iff_ent B hent] at hv ⊢
  by_cases h1 : v = p
  · rw [h1, m1]
    exact Or.inl rfl
  by_cases h2 : v = C'.mate p
  · rw [h2, m2]
    exact Or.inr (Or.inl rfl)
  by_cases h3 : v = ent
  · rw [h3, m3]
    exact Or.inr (Or.inr p.2)
  by_cases h4 : v = B.mate ent
  · rw [h4, m4]
    exact Or.inr (Or.inr (C'.mate p).2)
  rcases hv with h | h | h
  · exact absurd h h3
  · exact absurd h h4
  · rw [m5 v h1 h2 h3 h4, glue_mate_of_mem B A hA C' h]
    exact Or.inr (Or.inr (C'.mate ⟨v, h⟩).2)

/-- The inserted context on `A ∪ {y₊, y₋}`: `C'` with the slot `f = {p, C' p}` replaced by
`p–entry(y)`, `exit(y)–C' p` (`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def insertCtx : PerfectMatching (grow B A yp) :=
  restrict (insertV B hA C' p ent) (grow B A yp) (insertV_closed B hA hyp C' p hent)

omit [Fintype V] in
/-- Partners in the inserted context on `A ∪ {y₊, y₋}`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem insertCtx_mate (v : grow B A yp) :
    ((insertCtx B hA hyp C' p hent).mate v : V) = (insertV B hA C' p ent).mate v :=
  rfl

include hent in
/-- Restricting a context that extends the inserted context to `E_0` gives back `C'`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem contract_insert (C : PerfectMatching V)
    (hC : contract B C (grow B A yp) (grow_closed B hA) = insertCtx B hA hyp C' p hent) :
    contract B C A hA = C' := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := insertV_mate B hA hyp C' p hent
  obtain ⟨he1, he2, he3⟩ := ent_notMem B hA hyp hent
  have hJ := walkGraph_mono B hA (yp := yp) C
  have hr : ∀ (v : V) (hv : v ∈ grow B A yp), (C.toGraph ⊔ offGraph B A hA).Reachable v
      ((insertV B hA C' p ent).mate v) := by
    intro v hv
    have := reachable_contractFun B C _ (grow_closed B hA) ⟨v, hv⟩
    rw [← contract_mate, hC, insertCtx_mate] at this
    exact this.mono hJ
  have hg : ∀ v : V, v ∈ A → v ∈ grow B A yp := fun v hv ↦ subset_grow B hv
  have hge : ent ∈ grow B A yp := (mem_grow_iff_ent B hent).mpr (Or.inl rfl)
  have hgx : B.mate ent ∈ grow B A yp := (mem_grow_iff_ent B hent).mpr (Or.inr (Or.inl rfl))
  refine PerfectMatching.ext (Equiv.ext fun a ↦ ?_)
  apply contract_mate_eq B C A hA a (C'.mate a) (C'.mate_ne a)
  by_cases h1 : a = p
  · subst h1
    have r1 := hr a (hg a a.2)
    have r2 := hr _ hgx
    rw [m1] at r1
    rw [m4] at r2
    exact r1.trans ((SimpleGraph.Adj.reachable (Or.inr ⟨rfl, he1⟩)).trans r2)
  by_cases h2 : a = C'.mate p
  · subst h2
    have r1 := hr _ (hg _ (C'.mate p).2)
    have r2 := hr _ hge
    rw [m2] at r1
    rw [m3] at r2
    rw [C'.mate_mate]
    refine r1.trans ((SimpleGraph.Adj.reachable (Or.inr ⟨?_, he2⟩)).trans r2)
    exact B.mate_mate ent
  have hae : (a : V) ≠ ent := fun h ↦ he1 (h ▸ a.2)
  have hax : (a : V) ≠ B.mate ent := fun h ↦ he2 (h ▸ a.2)
  have r := hr a (hg a a.2)
  rw [m5 a (fun h ↦ h1 (Subtype.ext h)) (fun h ↦ h2 (Subtype.ext h)) hae hax,
    glue_mate_coe] at r
  exact r

omit [Fintype V] in
include hent in
/-- Inserting `y` into a slot of `C'` subdivides that slot when `P₁` pairs `y₊` with `y₋`, so
the number of cycles is unchanged.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem cycleCount_insert (P₁ : PerfectMatching (grow B A yp)) (P₀ : PerfectMatching A)
    (h1 : P₁.mate (yP B) = yM B)
    (h0 : ∀ v : A, (P₁.mate ⟨v, subset_grow B v.2⟩ : V) = P₀.mate v) :
    cycleCount P₁ (insertCtx B hA hyp C' p hent) = cycleCount P₀ C' := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := insertV_mate B hA hyp C' p hent
  obtain ⟨he1, he2, he3⟩ := ent_notMem B hA hyp hent
  set D := insertCtx B hA hyp C' p hent with hD
  set q := C'.mate p with hq
  have hge : ent ∈ grow B A yp := (mem_grow_iff_ent B hent).mpr (Or.inl rfl)
  have hgx : B.mate ent ∈ grow B A yp := (mem_grow_iff_ent B hent).mpr (Or.inr (Or.inl rfl))
  let E : grow B A yp := ⟨ent, hge⟩
  let X : grow B A yp := ⟨B.mate ent, hgx⟩
  let ι : A → grow B A yp := fun v ↦ ⟨v, subset_grow B v.2⟩
  have hP1 : P₁.mate E = X := by
    rcases hent with h | h
    · have hE : E = yP B := Subtype.ext h
      have hX : X = yM B := Subtype.ext (show B.mate ent = B.mate yp by rw [h])
      rw [hE, hX, h1]
    · have hE : E = yM B := Subtype.ext h
      have hX : X = yP B := Subtype.ext (show B.mate ent = yp by rw [h, mate_mate])
      rw [hE, hX, ← h1, mate_mate]
  have hP1' : P₁.mate X = E := by rw [← hP1, mate_mate]
  have hDp : D.mate (ι p) = E := Subtype.ext (by rw [insertCtx_mate]; exact m1)
  have hDq : D.mate (ι q) = X := Subtype.ext (by rw [insertCtx_mate]; exact m2)
  have hDe : D.mate E = ι p := Subtype.ext (by rw [insertCtx_mate]; exact m3)
  have hDx : D.mate X = ι q := Subtype.ext (by rw [insertCtx_mate]; exact m4)
  have hDo : ∀ v : A, v ≠ p → v ≠ q → D.mate (ι v) = ι (C'.mate v) := fun v hp hq' ↦
    Subtype.ext (by
      rw [insertCtx_mate]
      rw [m5 v (fun h ↦ hp (Subtype.ext h)) (fun h ↦ hq' (Subtype.ext h))
        (fun h ↦ he1 (h ▸ v.2)) (fun h ↦ he2 (h ▸ v.2)), glue_mate_coe])
  have hP1o : ∀ v : A, P₁.mate (ι v) = ι (P₀.mate v) := fun v ↦ Subtype.ext (h0 v)
  have cls : ∀ v : grow B A yp, (∃ a : A, v = ι a) ∨ v = E ∨ v = X := by
    intro v
    rcases (mem_grow_iff_ent B hent).mp v.2 with h | h | h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
    · exact Or.inl ⟨⟨v, h⟩, rfl⟩
  let π : grow B A yp → A := fun v ↦
    if h : (v : V) ∈ A then ⟨v, h⟩ else if (v : V) = ent then p else q
  have πι : ∀ a : A, π (ι a) = a := fun a ↦ by simp [π, ι, a.2]
  have πE : π E = p := by simp [π, E, he1]
  have πX : π X = q := by simp [π, X, he2, he3.symm]
  have G0pq : (P₀.toGraph ⊔ C'.toGraph).Reachable p q := (adj_mate_right P₀ C' p).reachable
  have key : ∀ a : A, ∀ w, (P₁.toGraph ⊔ D.toGraph).Adj (ι a) w →
      (P₀.toGraph ⊔ C'.toGraph).Reachable a (π w) := by
    intro a w haw
    rcases haw with haw | haw
    · change P₁.mate (ι a) = w at haw
      rw [← haw, hP1o, πι]
      exact (adj_mate_left P₀ C' a).reachable
    · change D.mate (ι a) = w at haw
      by_cases hp : a = p
      · subst hp
        rw [← haw, hDp, πE]
      by_cases hq' : a = q
      · subst hq'
        rw [← haw, hDq, πX]
      rw [← haw, hDo a hp hq', πι]
      exact (adj_mate_right P₀ C' a).reachable
  have h1' : ∀ v w, (P₁.toGraph ⊔ D.toGraph).Adj v w →
      (P₀.toGraph ⊔ C'.toGraph).Reachable (π v) (π w) := by
    intro v w hvw
    rcases cls v with ⟨a, rfl⟩ | hv | hv
    · rw [πι]
      exact key a w hvw
    · rcases cls w with ⟨b, rfl⟩ | hw | hw
      · rw [πι]
        exact (key b v hvw.symm).symm
      · exact absurd (hv.trans hw.symm) hvw.ne
      · rw [hv, hw, πE, πX]
        exact G0pq
    · rcases cls w with ⟨b, rfl⟩ | hw | hw
      · rw [πι]
        exact (key b v hvw.symm).symm
      · rw [hv, hw, πE, πX]
        exact G0pq.symm
      · exact absurd (hv.trans hw.symm) hvw.ne
  have pathpq : (P₁.toGraph ⊔ D.toGraph).Reachable (ι p) (ι q) := by
    have a1 : (P₁.toGraph ⊔ D.toGraph).Adj (ι p) E := Or.inr hDp
    have a2 : (P₁.toGraph ⊔ D.toGraph).Adj E X := Or.inl hP1
    have a3 : (P₁.toGraph ⊔ D.toGraph).Adj X (ι q) := Or.inr hDx
    exact a1.reachable.trans (a2.reachable.trans a3.reachable)
  have h2' : ∀ v w, (P₀.toGraph ⊔ C'.toGraph).Adj v w →
      (P₁.toGraph ⊔ D.toGraph).Reachable (ι v) (ι w) := by
    intro v w hvw
    rcases hvw with hvw | hvw
    · change P₀.mate v = w at hvw
      rw [← hvw, ← hP1o]
      exact (adj_mate_left P₁ D _).reachable
    · change C'.mate v = w at hvw
      by_cases hp : v = p
      · subst hp
        rw [← hvw]
        exact pathpq
      by_cases hq' : v = q
      · subst hq'
        rw [← hvw, C'.mate_mate]
        exact pathpq.symm
      rw [← hvw, ← hDo v hp hq']
      exact (adj_mate_right P₁ D _).reachable
  have h3' : ∀ v, (P₁.toGraph ⊔ D.toGraph).Reachable v (ι (π v)) := by
    intro v
    rcases cls v with ⟨a, rfl⟩ | rfl | rfl
    · rw [πι]
    · rw [πE, ← hDe]
      exact (adj_mate_right P₁ D _).reachable
    · rw [πX, ← hDx]
      exact (adj_mate_right P₁ D _).reachable
  exact card_connectedComponent_eq_of_retract π ι h1' h2' h3' (fun w ↦ by rw [πι])

omit [Fintype V] in
/-- The two ends of the inserted label are distinct.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem yP_ne_yM : yP B ≠ (yM B : grow B A yp) := fun h ↦
  B.mate_ne yp (congrArg (fun z : grow B A yp ↦ (z : V)) h).symm

/-- `V(E_0)` as the lower vertex set `V(E_0 ∪ {y}) ∖ {y₊, y₋}` of Lemma 5.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
def liftEquiv : A ≃ lowerSet (yP B) (yM B : grow B A yp) where
  toFun a := ⟨⟨a, subset_grow B a.2⟩, mem_lowerSet.mpr
    ⟨fun h ↦ (lift_ne B hA hyp a).1 (congrArg (fun z : grow B A yp ↦ (z : V)) h),
      fun h ↦ (lift_ne B hA hyp a).2 (congrArg (fun z : grow B A yp ↦ (z : V)) h)⟩⟩
  invFun w := ⟨w.1, mem_A_of_grow B w.1
    (fun h ↦ (mem_lowerSet.mp w.2).1 (Subtype.ext h))
    (fun h ↦ (mem_lowerSet.mp w.2).2 (Subtype.ext h))⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
/-- `liftEquiv` keeps the underlying vertex.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem coe_liftEquiv (a : A) : (((liftEquiv B hA hyp a : lowerSet (yP B) (yM B)) :
    grow B A yp) : V) = a :=
  rfl

omit [Fintype V] in
include hent in
/-- The inserted context satisfies the hypotheses of `insertion_cycleCount`.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem insertCtx_transport :
    (insertCtx B hA hyp C' p hent).mate (liftEquiv B hA hyp p) =
        ⟨ent, (mem_grow_iff_ent B hent).mpr (Or.inl rfl)⟩ ∧
      (insertCtx B hA hyp C' p hent).mate
          ((congr (liftEquiv B hA hyp) C').mate (liftEquiv B hA hyp p)) =
        ⟨B.mate ent, (mem_grow_iff_ent B hent).mpr (Or.inr (Or.inl rfl))⟩ ∧
      ∀ v, v ≠ liftEquiv B hA hyp p → v ≠ (congr (liftEquiv B hA hyp) C').mate
          (liftEquiv B hA hyp p) →
        (insertCtx B hA hyp C' p hent).mate v = (congr (liftEquiv B hA hyp) C').mate v := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := insertV_mate B hA hyp C' p hent
  obtain ⟨he1, he2, he3⟩ := ent_notMem B hA hyp hent
  set e := liftEquiv B hA hyp with he
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, fun v h1 h2 ↦ Subtype.ext ?_⟩
  · rw [insertCtx_mate]
    exact m1
  · rw [insertCtx_mate, congr_mate, Equiv.symm_apply_apply]
    exact m2
  · rw [insertCtx_mate, congr_mate]
    have hv : (v : grow B A yp) = (e (e.symm v) : grow B A yp) := by rw [Equiv.apply_symm_apply]
    have hvV : ((v : grow B A yp) : V) = (e.symm v : A) := congrArg Subtype.val hv
    have n1 : e.symm v ≠ p := fun h ↦ h1 (by rw [← h, Equiv.apply_symm_apply])
    have n2 : e.symm v ≠ C'.mate p := fun h ↦ h2 (by
      rw [congr_mate, Equiv.symm_apply_apply, ← h, Equiv.apply_symm_apply])
    rw [hvV, m5 _ (fun h ↦ n1 (Subtype.ext h)) (fun h ↦ n2 (Subtype.ext h))
      (fun h ↦ he1 (h ▸ (e.symm v).2)) (fun h ↦ he2 (h ▸ (e.symm v).2)), glue_mate_coe]
    rfl

include hent in
/-- Lemma 5 at a non-degenerate reinsertion step: inserting `y` into a slot on a cycle other
than the split edge's lowers `κ` by one.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem cycleCount_insert_nondeg
    (hnd : (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) ≠ yM B)
    (a : A) (ha : ((contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) : V) = a)
    (hpa : ¬((contract B R A hA).toGraph ⊔ C'.toGraph).Reachable p a) :
    cycleCount (contract B R (grow B A yp) (grow_closed B hA)) (insertCtx B hA hyp C' p hent) + 1 =
      cycleCount (contract B R A hA) C' := by
  obtain ⟨a', b, ha', hb, hab, hRo⟩ := contract_step_nondeg B R hA hyp hnd
  have haa : a' = a := Subtype.ext (ha'.symm.trans ha)
  subst haa
  set e := liftEquiv B hA hyp with he
  obtain ⟨t1, t2, t3⟩ := insertCtx_transport B hA hyp C' p hent
  have hent' : (⟨ent, (mem_grow_iff_ent B hent).mpr (Or.inl rfl)⟩ : grow B A yp) = yP B ∧
        (⟨B.mate ent, (mem_grow_iff_ent B hent).mpr (Or.inr (Or.inl rfl))⟩ : grow B A yp) =
          yM B ∨
      (⟨ent, (mem_grow_iff_ent B hent).mpr (Or.inl rfl)⟩ : grow B A yp) = yM B ∧
        (⟨B.mate ent, (mem_grow_iff_ent B hent).mpr (Or.inr (Or.inl rfl))⟩ : grow B A yp) =
          yP B := by
    rcases hent with h | h
    · exact Or.inl ⟨Subtype.ext h, Subtype.ext (by simp [yM, h])⟩
    · exact Or.inr ⟨Subtype.ext h, Subtype.ext (by simp [yP, h])⟩
  have L5 := insertion_cycleCount (yP_ne_yM B (A := A) (yp := yp))
    (contract B R (grow B A yp) (grow_closed B hA)) (e a') (e b)
    (Subtype.ext ha') (Subtype.ext hb) (congr e (contract B R A hA))
    (by rw [congr_mate, Equiv.symm_apply_apply, hab])
    (fun v h1 h2 ↦ by
      rw [congr_mate]
      apply Subtype.ext
      exact hRo (e.symm v) (fun h ↦ h1 (by rw [← h, Equiv.apply_symm_apply]))
        (fun h ↦ h2 (by rw [← h, Equiv.apply_symm_apply])))
    (congr e C') (e p) (insertCtx B hA hyp C' p hent) hent' t1 t2 t3
  have hr : ¬((congr e (contract B R A hA)).toGraph ⊔ (congr e C').toGraph).Reachable (e p)
      (e a') := by
    rw [reachable_congr]
    exact hpa
  rw [L5.1 hr, cycleCount_congr]

/-- Lemma 5 at a non-degenerate reinsertion step on a Hamiltonian context: one of the two signs
of `y` keeps it Hamiltonian.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem ham_insert_nondeg
    (hnd : (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) ≠ yM B)
    (hH : Ham (contract B R A hA) C') :
    Ham (contract B R (grow B A yp) (grow_closed B hA))
        (insertCtx B hA hyp C' p (ent := yp) (Or.inl rfl)) ∨
      Ham (contract B R (grow B A yp) (grow_closed B hA))
        (insertCtx B hA hyp C' p (ent := B.mate yp) (Or.inr rfl)) := by
  obtain ⟨a', b, ha', hb, hab, hRo⟩ := contract_step_nondeg B R hA hyp hnd
  set e := liftEquiv B hA hyp with he
  obtain ⟨t1, t2, t3⟩ := insertCtx_transport B hA hyp C' p (ent := yp) (Or.inl rfl)
  obtain ⟨u1, u2, u3⟩ := insertCtx_transport B hA hyp C' p (ent := B.mate yp) (Or.inr rfl)
  have L5 := insertion_ham_iff (yP_ne_yM B (A := A) (yp := yp))
    (contract B R (grow B A yp) (grow_closed B hA)) (e a') (e b)
    (Subtype.ext ha') (Subtype.ext hb) (congr e (contract B R A hA))
    (by rw [congr_mate, Equiv.symm_apply_apply, hab])
    (fun v h1 h2 ↦ by
      rw [congr_mate]
      apply Subtype.ext
      exact hRo (e.symm v) (fun h ↦ h1 (by rw [← h, Equiv.apply_symm_apply]))
        (fun h ↦ h2 (by rw [← h, Equiv.apply_symm_apply])))
    (congr e C') (e p) _ _ t1 t2 t3 u1 (u2.trans (Subtype.ext (B.mate_mate yp))) u3
    ((ham_congr e _ _).mpr hH)
  by_cases h : Ham (contract B R (grow B A yp) (grow_closed B hA))
      (insertCtx B hA hyp C' p (ent := yp) (Or.inl rfl))
  · exact Or.inl h
  · exact Or.inr (by
      by_contra h'
      exact h (L5.mpr h'))

end Step

section Main

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- When `A` is everything, `P ∪ Q` on `V` and its copy on `A` have the same cycles.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem cycleCount_eq_of_forall_mem {A : Finset V} (hall : ∀ v, v ∈ A)
    (P Q : PerfectMatching V) (P' Q' : PerfectMatching A) (hP : ∀ a : A, (P'.mate a : V) = P.mate a)
    (hQ : ∀ a : A, (Q'.mate a : V) = Q.mate a) : cycleCount P Q = cycleCount P' Q' := by
  let π : V → A := fun v ↦ ⟨v, hall v⟩
  refine card_connectedComponent_eq_of_retract π Subtype.val (fun v w h ↦ ?_) (fun v w h ↦ ?_)
    (fun v ↦ SimpleGraph.Reachable.refl _) (fun w ↦ SimpleGraph.Reachable.refl _)
  · rcases h with h | h
    · exact SimpleGraph.Adj.reachable (Or.inl (Subtype.ext ((hP (π v)).trans h)))
    · exact SimpleGraph.Adj.reachable (Or.inr (Subtype.ext ((hQ (π v)).trans h)))
  · rcases h with h | h
    · change P'.mate v = w at h
      exact SimpleGraph.Adj.reachable (Or.inl ((hP v).symm.trans (congrArg Subtype.val h)))
    · change Q'.mate v = w at h
      exact SimpleGraph.Adj.reachable (Or.inr ((hQ v).symm.trans (congrArg Subtype.val h)))

/-- Gluing a context of `E_0` to `B` and restricting back gives it again.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem contract_glue (B : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, B.mate v ∈ A)
    (C' : PerfectMatching A) : contract B (glue B A hA C') A hA = C' :=
  PerfectMatching.ext (Equiv.ext fun a ↦ contract_mate_eq B _ A hA a (C'.mate a) (C'.mate_ne a)
    (SimpleGraph.Adj.reachable (Or.inl (glue_mate_coe B A hA C' a))))

/-- Reinserting one label removes two vertices from the complement.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem card_compl_grow (B : PerfectMatching V) {A : Finset V} (hA : ∀ v ∈ A, B.mate v ∈ A)
    {yp : V} (hyp : yp ∉ A) : (grow B A yp)ᶜ.card + 2 = Aᶜ.card := by
  have h1 : B.mate yp ∉ A := mate_notMem B hA hyp
  have h2 : yp ∉ insert (B.mate yp) A := by
    rw [Finset.mem_insert, not_or]
    exact ⟨(B.mate_ne yp).symm, hyp⟩
  have hg : (grow B A yp).card = A.card + 2 := by
    rw [grow, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
  have hle := Finset.card_le_univ (grow B A yp)
  rw [Finset.card_compl, Finset.card_compl, hg]
  rw [hg] at hle
  omega

/-- **Reinsertion (proof of Corollary 5.1, corrected).** `results/hybrid-joint-incoherence.md`.
Every context `C'` of `E_0` extends to a context `C` of `E` with `C|_{E_0} = C'` such that
`κ(R ∪ C) ≤ 1` or `κ(R ∪ C) + |Y| ≤ κ(R_0 ∪ C') + c_Y`, where `|Y| = n` and `c_Y` counts the
cycles of `R ∪ F_0|_Y` inside `Y`. Labels of `Y` are reinserted one at a time. By Lemma 5 each
non-degenerate step lowers `κ` by one, or keeps `κ = 1` with the good sign, and each degenerate
step (`R(y₊) = y₋`) keeps `κ` and closes one of the cycles counted by `c_Y`. -/
theorem exists_context_extension (B R : PerfectMatching V) (n : ℕ) :
    ∀ (A : Finset V) (hA : ∀ v ∈ A, B.mate v ∈ A), Aᶜ.card = 2 * n →
      ∀ C' : PerfectMatching A, Ham (restrict B A hA) C' →
        ∃ C : PerfectMatching V, Ham B C ∧ contract B C A hA = C' ∧
          (cycleCount R C ≤ 1 ∨
            cycleCount R C + n ≤ cycleCount (contract B R A hA) C' + closedCount R B A) := by
  induction n with
  | zero =>
    intro A hA hcard C' hH
    have hall : ∀ v, v ∈ A := by
      intro v
      by_contra hv
      have : 0 < Aᶜ.card := Finset.card_pos.mpr ⟨v, Finset.mem_compl.mpr hv⟩
      omega
    have k1 := cycleCount_eq_of_forall_mem hall B (glue B A hA C') (restrict B A hA) C'
      (fun _ ↦ rfl) (fun a ↦ (glue_mate_coe B A hA C' a).symm)
    have k2 := cycleCount_eq_of_forall_mem hall R (glue B A hA C') (contract B R A hA) C'
      (fun a ↦ contract_mate_of_mem B R A hA a (hall _)) (fun a ↦ (glue_mate_coe B A hA C' a).symm)
    refine ⟨glue B A hA C', ?_, contract_glue B A hA C', Or.inr (by rw [k2]; omega)⟩
    rw [ham_iff_cycleCount_eq_one', k1, ← ham_iff_cycleCount_eq_one']
    exact hH
  | succ n ih =>
    intro A hA hcard C' hH
    obtain ⟨yp, hyp⟩ : ∃ yp, yp ∉ A := by
      by_contra h
      push Not at h
      have : Aᶜ = ∅ := Finset.eq_empty_of_forall_notMem fun v hv ↦ Finset.mem_compl.mp hv (h v)
      rw [this, Finset.card_empty] at hcard
      omega
    have hcard' : (grow B A yp)ᶜ.card = 2 * n := by
      have := card_compl_grow B hA hyp
      omega
    have hcl := closedCount_step B R hA hyp
    have hcle := closedCount_le B R n hcard'
    obtain ⟨p₀⟩ : Nonempty A := hH.nonempty
    have ext : ∀ (ent : V) (hent : ent = yp ∨ ent = B.mate yp) (p : A),
        ∃ C : PerfectMatching V, Ham B C ∧ contract B C A hA = C' ∧
          (cycleCount R C ≤ 1 ∨ cycleCount R C + n ≤
            cycleCount (contract B R (grow B A yp) (grow_closed B hA))
              (insertCtx B hA hyp C' p hent) + closedCount R B (grow B A yp)) := by
      intro ent hent p
      have hH' : Ham (restrict B (grow B A yp) (grow_closed B hA))
          (insertCtx B hA hyp C' p hent) := by
        rw [ham_iff_cycleCount_eq_one', cycleCount_insert B hA hyp C' p hent _
          (restrict B A hA) rfl (fun _ ↦ rfl), ← ham_iff_cycleCount_eq_one']
        exact hH
      obtain ⟨C, hC1, hC2, hC3⟩ := ih (grow B A yp) (grow_closed B hA) hcard' _ hH'
      exact ⟨C, hC1, contract_insert B hA hyp C' p hent C hC2, hC3⟩
    by_cases hd : (contract B R (grow B A yp) (grow_closed B hA)).mate (yP B) = yM B
    · simp only [hd, ↓reduceIte] at hcl
      obtain ⟨C, hC1, hC2, hC3⟩ := ext yp (Or.inl rfl) p₀
      have hk := cycleCount_insert B hA hyp C' p₀ (Or.inl rfl)
        (contract B R (grow B A yp) (grow_closed B hA)) (contract B R A hA) hd
        (fun v ↦ (contract_step_deg B R hA hyp hd v).symm)
      refine ⟨C, hC1, hC2, ?_⟩
      rw [hk] at hC3
      omega
    · simp only [hd, ↓reduceIte, add_zero] at hcl
      by_cases hH1 : Ham (contract B R A hA) C'
      · have hk1 := (ham_iff_cycleCount_eq_one' _ _).mp hH1
        rcases ham_insert_nondeg B R hA hyp C' p₀ hd hH1 with h | h
        · obtain ⟨C, hC1, hC2, hC3⟩ := ext yp (Or.inl rfl) p₀
          rw [(ham_iff_cycleCount_eq_one' _ _).mp h] at hC3
          exact ⟨C, hC1, hC2, by omega⟩
        · obtain ⟨C, hC1, hC2, hC3⟩ := ext (B.mate yp) (Or.inr rfl) p₀
          rw [(ham_iff_cycleCount_eq_one' _ _).mp h] at hC3
          exact ⟨C, hC1, hC2, by omega⟩
      · obtain ⟨a', b, ha', -, -, -⟩ := contract_step_nondeg B R hA hyp hd
        obtain ⟨p, hp⟩ : ∃ p : A,
            ¬((contract B R A hA).toGraph ⊔ C'.toGraph).Reachable p a' := by
          by_contra h
          push Not at h
          exact hH1 ((SimpleGraph.connected_iff _).mpr
            ⟨fun u v ↦ (h u).trans (h v).symm, ⟨p₀⟩⟩)
        have hk := cycleCount_insert_nondeg B R hA hyp C' p (Or.inl rfl) hd a' ha' hp
        obtain ⟨C, hC1, hC2, hC3⟩ := ext yp (Or.inl rfl) p
        exact ⟨C, hC1, hC2, by omega⟩

omit [DecidableEq V] in
/-- `κ(P ∪ Q) ≤ |V|/2`: every cycle has at least two vertices.
(`results/hybrid-joint-incoherence.md`, Corollary 5.1). -/
theorem two_mul_cycleCount_le (P Q : PerfectMatching V) :
    2 * cycleCount P Q ≤ Fintype.card V := by
  have h := two_mul_card_le (P.toGraph ⊔ Q.toGraph) P.mate P.mate_ne
    (fun v ↦ (adj_mate_left P Q v).reachable) (fun _ ↦ True) Finset.univ
    (fun v _ ↦ Finset.mem_univ v)
  rw [Finset.card_univ, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ trivial)] at h
  exact h

/-- **Corollary 5.1 (free defects), corrected.** `results/hybrid-joint-incoherence.md`.
`E = E_0 ⊔ Y` with `B = F_0|_E`, `A = V(E_0)`, `|Y| = n` and `|E_0| = m`. The contexts of `E`
are the `C` with `C ∪ B` one cycle, those of `E_0` the `C'` with `C' ∪ B|_A` one cycle, and
`C|_{E_0} = contract B C A` skips the `Y`-labels. `𝒞` and `𝒞₀` are the realized contexts of
`E` and `E_0`. `Y` is free over `E_0` when every context of `E` whose restriction is realized
by `E_0` is realized by `E`. If `X(E, R) = 0`, every realized context `C'` of `E_0` has
`κ(R_0 ∪ C') ≥ |Y| − c_Y + 2`, where `R_0` is `R` shortcut at all of `Y` and `c_Y` counts the
cycles of `R ∪ F_0|_Y` inside `Y`. Hence `|Y| − c_Y ≤ |E_0| − 2`. The source states
`|Y| ≤ |E_0| − 2`, which needs `c_Y = 0`. -/
theorem free_defects (B R : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, B.mate v ∈ A)
    {n m : ℕ} (hn : Aᶜ.card = 2 * n) (hm : A.card = 2 * m)
    (𝒞 : Set (PerfectMatching V)) (𝒞₀ : Set (PerfectMatching A))
    (h𝒞₀ : ∀ C' ∈ 𝒞₀, Ham (restrict B A hA) C')
    (hfree : ∀ C, Ham B C → contract B C A hA ∈ 𝒞₀ → C ∈ 𝒞)
    (hX : ∀ C ∈ 𝒞, ¬Ham R C) (C' : PerfectMatching A) (hC' : C' ∈ 𝒞₀) :
    n + 2 ≤ cycleCount (contract B R A hA) C' + closedCount R B A ∧
      n + 2 ≤ m + closedCount R B A := by
  have hH := h𝒞₀ C' hC'
  obtain ⟨C, hC1, hC2, hC3⟩ := exists_context_extension B R n A hA hn C' hH
  have hnH : ¬Ham R C := hX C (hfree C hC1 (hC2 ▸ hC'))
  obtain ⟨a⟩ : Nonempty A := hH.nonempty
  have hpos : 0 < cycleCount R C := by
    rw [cycleCount]
    have : Nonempty (R.toGraph ⊔ C.toGraph).ConnectedComponent :=
      ⟨(R.toGraph ⊔ C.toGraph).connectedComponentMk a⟩
    exact Nat.card_pos
  have h2 : 2 ≤ cycleCount R C := by
    by_contra h
    exact hnH ((ham_iff_cycleCount_eq_one' R C).mpr (by omega))
  have h1 : n + 2 ≤ cycleCount (contract B R A hA) C' + closedCount R B A := by omega
  refine ⟨h1, ?_⟩
  have hk := two_mul_cycleCount_le (contract B R A hA) C'
  rw [Fintype.card_coe, hm] at hk
  omega

/-- **Corollary 5.1 as stated in the source**, under the extra hypothesis that `R ∪ F_0|_Y`
closes no cycle inside `Y` (`c_Y = 0`): free defects number at most `|E_0| − 2`
(`results/hybrid-joint-incoherence.md`). -/
theorem free_defects_of_closedCount_eq_zero (B R : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, B.mate v ∈ A) {n m : ℕ} (hn : Aᶜ.card = 2 * n) (hm : A.card = 2 * m)
    (hc : closedCount R B A = 0)
    (𝒞 : Set (PerfectMatching V)) (𝒞₀ : Set (PerfectMatching A))
    (h𝒞₀ : ∀ C' ∈ 𝒞₀, Ham (restrict B A hA) C')
    (hfree : ∀ C, Ham B C → contract B C A hA ∈ 𝒞₀ → C ∈ 𝒞)
    (hX : ∀ C ∈ 𝒞, ¬Ham R C) (h𝒞₀ne : 𝒞₀.Nonempty) : n + 2 ≤ m := by
  obtain ⟨C', hC'⟩ := h𝒞₀ne
  have := (free_defects B R A hA hn hm 𝒞 𝒞₀ h𝒞₀ hfree hX C' hC').2
  omega

end Main



end PerfectMatching

end Pairing
