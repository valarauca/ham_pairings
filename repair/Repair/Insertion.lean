import Clifford.Contraction
import Pairing.Union

/-!
# One-defect insertion (Lemma 5 and Corollary 5.1 of the joint-incoherence spike)

`cycleCount P Q = κ(P ∪ Q)` (from `Pairing.Union`) is the number of cycles of the union of
two perfect matchings, that is the number of connected components of the union graph.

* `card_sup_edge_of_reachable`, `card_sup_edge_add_one` : adding an edge keeps the component
  count when its ends are already joined and lowers it by one otherwise.
* `card_connectedComponent_eq_of_retract`, `reachable_iff_of_retract` : two graphs related by
  maps that send edges to walks and are inverse up to reachability have the same components.
* `reachable_contractFun`, `eq_or_eq_contractFun_of_reachable` : in `Q ∪ (P off A)` every
  `a ∈ A` is joined to `κ_Q a` and to no other point of `A`.
* `pairing_of_four` : removing two edges of one matching leaves the four ends joined in pairs.
* `two_switch` : a 2-switch of one matching lowers `κ` by one when the two edges lie on
  different cycles, and otherwise keeps it or raises it by one.
* `insertion_cycleCount`, `insertion_sign_unique`, `insertion_ham_iff` : Lemma 5. Inserting a
  defect acts on every context as a 2-opt move, and on a Hamiltonian context exactly one sign
  of the new defect keeps it Hamiltonian.

Source: `results/hybrid-joint-incoherence.md` (organize-archive 4f82c7d), Lemma 5 and
Corollary 5.1. The 2-switch dichotomy is Theorem 11.1 of the archive conversation
"Mathematical Pattern Investigation" (`old-personal-chatgpt` doc
01a1e1d3-a7a1-728c-8db1-cd74249be926).
-/

namespace Pairing

section Graph

variable {W : Type*}

/-- The ends of an added edge are joined in the enlarged graph.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_sup_edge (G : SimpleGraph W) (u v : W) :
    (G ⊔ SimpleGraph.edge u v).Reachable u v := by
  by_cases h : u = v
  · subst h
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable
      ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr
        ⟨Or.inl ⟨rfl, rfl⟩, h⟩)))

/-- Reachability after adding the edge `uv`: a walk uses the new edge at most once.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_sup_edge_iff (G : SimpleGraph W) (u v a b : W) :
    (G ⊔ SimpleGraph.edge u v).Reachable a b ↔
      G.Reachable a b ∨ (G.Reachable a u ∧ G.Reachable v b) ∨
        (G.Reachable a v ∧ G.Reachable u b) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | cons hadj _ ih =>
      rcases (SimpleGraph.sup_adj _ _ _ _).mp hadj with h | h
      · have hr := h.reachable
        rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (hr.trans h1)
        · exact Or.inr (Or.inl ⟨hr.trans h1, h2⟩)
        · exact Or.inr (Or.inr ⟨hr.trans h1, h2⟩)
      · rw [SimpleGraph.edge_adj] at h
        obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩ := h
        · rcases ih with h1 | ⟨h1, h2⟩ | ⟨-, h2⟩
          · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h1⟩)
          · exact Or.inl (h1.symm.trans h2)
          · exact Or.inl h2
        · rcases ih with h1 | ⟨-, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h1⟩)
          · exact Or.inl h2
          · exact Or.inl (h1.symm.trans h2)
  · have hle : G ≤ G ⊔ SimpleGraph.edge u v := le_sup_left
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono hle
    · exact (h1.mono hle).trans ((reachable_sup_edge G u v).trans (h2.mono hle))
    · exact (h1.mono hle).trans ((reachable_sup_edge G u v).symm.trans (h2.mono hle))

/-- Adding an edge whose ends are already joined does not change reachability.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_sup_edge_iff_of_reachable (G : SimpleGraph W) {u v : W} (huv : G.Reachable u v)
    (a b : W) : (G ⊔ SimpleGraph.edge u v).Reachable a b ↔ G.Reachable a b := by
  rw [reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact h1.trans (huv.trans h2)
    · exact h1.trans (huv.symm.trans h2)
  · exact Or.inl

/-- Two graphs related by maps that send edges to walks, and that are inverse to each other up
to reachability, have the same number of components.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem card_connectedComponent_eq_of_retract {W' : Type*} {G : SimpleGraph W}
    {G' : SimpleGraph W'} (π : W → W') (ι : W' → W)
    (h1 : ∀ v w, G.Adj v w → G'.Reachable (π v) (π w))
    (h2 : ∀ v w, G'.Adj v w → G.Reachable (ι v) (ι w))
    (h3 : ∀ v, G.Reachable v (ι (π v))) (h4 : ∀ w, G'.Reachable (π (ι w)) w) :
    Nat.card G.ConnectedComponent = Nat.card G'.ConnectedComponent := by
  refine Nat.card_congr
    { toFun := SimpleGraph.ConnectedComponent.lift (fun v ↦ G'.connectedComponentMk (π v))
        (fun v w p _ ↦ SimpleGraph.ConnectedComponent.sound
          (reachable_map_of_forall_adj π h1 p.reachable))
      invFun := SimpleGraph.ConnectedComponent.lift (fun w ↦ G.connectedComponentMk (ι w))
        (fun v w p _ ↦ SimpleGraph.ConnectedComponent.sound
          (reachable_map_of_forall_adj ι h2 p.reachable))
      left_inv := fun c ↦ ?_
      right_inv := fun c ↦ ?_ }
  · induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      simp only [SimpleGraph.ConnectedComponent.lift_mk]
      exact SimpleGraph.ConnectedComponent.sound (h3 v).symm
  · induction c using SimpleGraph.ConnectedComponent.ind with
    | h w =>
      simp only [SimpleGraph.ConnectedComponent.lift_mk]
      exact SimpleGraph.ConnectedComponent.sound (h4 w)

/-- Under the hypotheses of `card_connectedComponent_eq_of_retract`, `π` preserves and reflects
reachability.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_iff_of_retract {W' : Type*} {G : SimpleGraph W} {G' : SimpleGraph W'}
    (π : W → W') (ι : W' → W)
    (h1 : ∀ v w, G.Adj v w → G'.Reachable (π v) (π w))
    (h2 : ∀ v w, G'.Adj v w → G.Reachable (ι v) (ι w))
    (h3 : ∀ v, G.Reachable v (ι (π v))) (a b : W) :
    G.Reachable a b ↔ G'.Reachable (π a) (π b) :=
  ⟨reachable_map_of_forall_adj π h1, fun h ↦
    (h3 a).trans ((reachable_map_of_forall_adj ι h2 h).trans (h3 b).symm)⟩

/-- Adding an edge inside a component keeps the number of components.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem card_sup_edge_of_reachable (G : SimpleGraph W) {u v : W} (h : G.Reachable u v) :
    Nat.card (G ⊔ SimpleGraph.edge u v).ConnectedComponent = Nat.card G.ConnectedComponent :=
  card_connectedComponent_eq_of_retract id id
    (fun a b hab ↦ (reachable_sup_edge_iff_of_reachable G h a b).mp hab.reachable)
    (fun _ _ hab ↦ (hab.reachable.mono le_sup_left))
    (fun _ ↦ SimpleGraph.Reachable.refl _) (fun _ ↦ SimpleGraph.Reachable.refl _)

/-- Adding an edge between two components merges them.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem card_sup_edge_add_one [Finite W] (G : SimpleGraph W) {u v : W} (h : ¬G.Reachable u v) :
    Nat.card (G ⊔ SimpleGraph.edge u v).ConnectedComponent + 1 =
      Nat.card G.ConnectedComponent := by
  classical
  let φ : G.ConnectedComponent → (G ⊔ SimpleGraph.edge u v).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift
      (fun w ↦ (G ⊔ SimpleGraph.edge u v).connectedComponentMk w)
      (fun a b p _ ↦ SimpleGraph.ConnectedComponent.sound (p.reachable.mono le_sup_left))
  let f : G.ConnectedComponent → Option (G ⊔ SimpleGraph.edge u v).ConnectedComponent :=
    fun c ↦ if c = G.connectedComponentMk v then none else some (φ c)
  have hf : Function.Bijective f := by
    constructor
    · intro c₁ c₂
      induction c₁ using SimpleGraph.ConnectedComponent.ind with
      | h a =>
        induction c₂ using SimpleGraph.ConnectedComponent.ind with
        | h b =>
          intro hc
          simp only [f, φ, SimpleGraph.ConnectedComponent.eq,
            SimpleGraph.ConnectedComponent.lift_mk] at hc ⊢
          by_cases ha : G.Reachable a v
          · by_cases hb : G.Reachable b v
            · exact ha.trans hb.symm
            · simp [ha, hb] at hc
          · by_cases hb : G.Reachable b v
            · simp [ha, hb] at hc
            · simp only [ha, hb, ↓reduceIte, Option.some_inj] at hc
              rw [SimpleGraph.ConnectedComponent.eq, reachable_sup_edge_iff] at hc
              rcases hc with hc | ⟨-, hc⟩ | ⟨hc, -⟩
              · exact hc
              · exact absurd hc.symm hb
              · exact absurd hc ha
    · intro o
      rcases o with _ | d
      · exact ⟨G.connectedComponentMk v, by simp [f]⟩
      · induction d using SimpleGraph.ConnectedComponent.ind with
        | h w =>
          by_cases hw : G.Reachable w v
          · refine ⟨G.connectedComponentMk u, ?_⟩
            simp only [f, φ, SimpleGraph.ConnectedComponent.eq,
              SimpleGraph.ConnectedComponent.lift_mk, h, ite_false, Option.some_inj]
            rw [reachable_sup_edge_iff]
            exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, hw.symm⟩)
          · refine ⟨G.connectedComponentMk w, ?_⟩
            simp [f, φ, hw]
  rw [← Finite.card_option, Nat.card_congr (Equiv.ofBijective f hf)]

end Graph

namespace PerfectMatching

variable {V : Type*}

@[deprecated ham_iff_cycleCount_eq_one (since := "2026-11-26")]
alias ham_iff_cycleCount_eq_one' := ham_iff_cycleCount_eq_one

section Off

variable (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- The edges of `P` with no end in `A`, for `A` a union of edges of `P`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def offGraph : SimpleGraph V where
  Adj v w := P.mate v = w ∧ v ∉ A
  symm := ⟨fun v w h ↦ ⟨by rw [← h.1, P.mate_mate], fun hw ↦ h.2 (by
    rw [← h.1] at hw
    exact (mate_mem_iff P A hA v).mp hw)⟩⟩
  loopless := ⟨fun v h ↦ P.mate_ne v h.1⟩

/-- Adjacency in `P` off `A`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
@[simp]
theorem offGraph_adj (v w : V) : (offGraph P A hA).Adj v w ↔ P.mate v = w ∧ v ∉ A :=
  Iff.rfl

/-- A matching that agrees with `P` off `A`, where `A` consists of the ends of two of its
edges, is `P` off `A` plus those two edges.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem toGraph_eq_offGraph_sup (M : PerfectMatching V) (hM : ∀ v ∉ A, M.mate v = P.mate v)
    (u w : V) (hcov : ∀ v ∈ A, v = u ∨ v = M.mate u ∨ v = w ∨ v = M.mate w) :
    M.toGraph = offGraph P A hA ⊔ SimpleGraph.edge u (M.mate u) ⊔
      SimpleGraph.edge w (M.mate w) := by
  ext v t
  simp only [SimpleGraph.sup_adj, toGraph_adj, offGraph_adj, SimpleGraph.edge_adj]
  constructor
  · intro h
    by_cases hv : v ∈ A
    · rcases hcov v hv with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inr ⟨Or.inl ⟨rfl, h.symm⟩, h ▸ (M.mate_ne v).symm⟩)
      · exact Or.inl (Or.inr ⟨Or.inr ⟨rfl, by rw [← h, mate_mate]⟩, h ▸ (M.mate_ne _).symm⟩)
      · exact Or.inr ⟨Or.inl ⟨rfl, h.symm⟩, h ▸ (M.mate_ne v).symm⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, by rw [← h, mate_mate]⟩, h ▸ (M.mate_ne _).symm⟩
    · exact Or.inl (Or.inl ⟨(hM v hv).symm.trans h, hv⟩)
  · rintro ((⟨h, hv⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩) | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩)
    · rw [hM v hv, h]
    · rfl
    · rw [mate_mate]
    · rfl
    · rw [mate_mate]

end Off

section Walk

variable [Fintype V] [DecidableEq V] (P Q : PerfectMatching V) (A : Finset V)
  (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- In `Q ∪ (P off A)` each `a ∈ A` is joined to its contraction partner `κ_Q a`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_contractFun (a : A) :
    (Q.toGraph ⊔ offGraph P A hA).Reachable a (contractFun P Q A hA a) := by
  have key : ∀ i ≤ exitIdx P Q A hA a,
      (Q.toGraph ⊔ offGraph P A hA).Reachable a (oddPt P Q a i) := by
    intro i hi
    induction i with
    | zero =>
      have h0 : (Q.toGraph ⊔ offGraph P A hA).Adj (a : V) (oddPt P Q a 0) :=
        Or.inl (by simp [oddPt])
      exact h0.reachable
    | succ i ih =>
      have hn := oddPt_notMem P Q A hA a (i := i) (by omega)
      have h1 : (Q.toGraph ⊔ offGraph P A hA).Adj (oddPt P Q a i) (evenPt P Q a (i + 1)) :=
        Or.inr ⟨(evenPt_succ P Q a i).symm, hn⟩
      have h2 : (Q.toGraph ⊔ offGraph P A hA).Adj (evenPt P Q a (i + 1))
          (oddPt P Q a (i + 1)) := Or.inl rfl
      exact (ih (by omega)).trans (h1.reachable.trans h2.reachable)
  rw [coe_contractFun]
  exact key _ le_rfl

/-- In `Q ∪ (P off A)` the only points of `A` joined to `a ∈ A` are `a` and `κ_Q a`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem eq_or_eq_contractFun_of_reachable (a : A) {w : V} (hw : w ∈ A)
    (h : (Q.toGraph ⊔ offGraph P A hA).Reachable a w) :
    w = a ∨ w = contractFun P Q A hA a := by
  let S : Set V := {v | ∃ i ≤ exitIdx P Q A hA a, v = evenPt P Q a i ∨ v = oddPt P Q a i}
  have hS : ∀ v u, (Q.toGraph ⊔ offGraph P A hA).Adj v u → v ∈ S → u ∈ S := by
    rintro v u hvu ⟨i, hi, rfl | rfl⟩
    · rcases hvu with hvu | ⟨hvu, hn⟩
      · exact ⟨i, hi, Or.inr (by simp only [oddPt]; exact ((toGraph_adj Q _ _).mp hvu).symm)⟩
      · cases i with
        | zero => exact absurd (by rw [evenPt_zero]; exact a.2) hn
        | succ j => exact ⟨j, by omega, Or.inr (by rw [← hvu, mate_evenPt_succ])⟩
    · rcases hvu with hvu | ⟨hvu, hn⟩
      · exact ⟨i, hi, Or.inl (by rw [← hvu, mate_oddPt])⟩
      · rcases lt_or_eq_of_le hi with hlt | rfl
        · exact ⟨i + 1, hlt, Or.inl (by rw [← hvu, evenPt_succ])⟩
        · exact absurd (oddPt_exitIdx_mem P Q A hA a) hn
  have hwS : w ∈ S :=
    mem_of_reachable_of_forall_adj hS h ⟨0, Nat.zero_le _, Or.inl (evenPt_zero P Q a).symm⟩
  obtain ⟨i, hi, rfl | rfl⟩ := hwS
  · cases i with
    | zero => exact Or.inl (evenPt_zero P Q a)
    | succ j => exact absurd hw (evenPt_notMem P Q A hA a (Nat.succ_pos j) hi)
  · rcases lt_or_eq_of_le hi with hlt | rfl
    · exact absurd hw (oddPt_notMem P Q A hA a hlt)
    · exact Or.inr rfl

/-- Every `a ∈ A` has exactly one partner `a' ≠ a` in `A` joined to it in `Q ∪ (P off A)`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem exists_partner {a : V} (ha : a ∈ A) :
    ∃ a' ∈ A, a' ≠ a ∧ (Q.toGraph ⊔ offGraph P A hA).Reachable a a' ∧
      ∀ w ∈ A, (Q.toGraph ⊔ offGraph P A hA).Reachable a w → w = a ∨ w = a' :=
  ⟨contractFun P Q A hA ⟨a, ha⟩, (contractFun P Q A hA ⟨a, ha⟩).2,
    fun h ↦ contractFun_ne P Q A hA ⟨a, ha⟩ (Subtype.ext h),
    reachable_contractFun P Q A hA ⟨a, ha⟩,
    fun _ hw hr ↦ eq_or_eq_contractFun_of_reachable P Q A hA ⟨a, ha⟩ hw hr⟩

end Walk

section Switch

variable [Fintype V] [DecidableEq V] (R C : PerfectMatching V) (p e : V)

/-- The four ends `p, q, e, x` of two edges `pq = {p, C p}` and `ex = {e, C e}` of `C`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def fourSet : Finset V := {p, C.mate p, e, C.mate e}

omit [Fintype V] in
/-- Membership in the four ends of two edges.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem mem_fourSet {v : V} :
    v ∈ fourSet C p e ↔ v = p ∨ v = C.mate p ∨ v = e ∨ v = C.mate e := by
  simp [fourSet]

omit [Fintype V] in
/-- The four ends of two edges of `C` are closed under `C`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem fourSet_closed : ∀ v ∈ fourSet C p e, C.mate v ∈ fourSet C p e := by
  intro v hv
  rw [mem_fourSet] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl <;> simp

/-- `H = R ∪ (C ∖ {pq, ex})`, the union with the two switched edges of `C` removed.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def switchCut : SimpleGraph V :=
  R.toGraph ⊔ offGraph C (fourSet C p e) (fourSet_closed C p e)

variable {R C p e}

/-- Removing two edges `pq`, `ex` of `C` from `R ∪ C` leaves the four ends joined in pairs:
exactly one of the pairings `{pq, ex}`, `{pe, qx}`, `{px, qe}` is realized by the remaining
paths (`results/hybrid-joint-incoherence.md`, proof of Lemma 5). -/
theorem pairing_of_four (hpe : p ≠ e) (hpx : p ≠ C.mate e) :
    ((switchCut R C p e).Reachable p (C.mate p) ∧ (switchCut R C p e).Reachable e (C.mate e) ∧
        ¬(switchCut R C p e).Reachable p e) ∨
      ((switchCut R C p e).Reachable p e ∧
          (switchCut R C p e).Reachable (C.mate p) (C.mate e) ∧
          ¬(switchCut R C p e).Reachable p (C.mate p)) ∨
      ((switchCut R C p e).Reachable p (C.mate e) ∧
          (switchCut R C p e).Reachable (C.mate p) e ∧
          ¬(switchCut R C p e).Reachable p (C.mate p)) := by
  have hpq : p ≠ C.mate p := (C.mate_ne p).symm
  have hex : e ≠ C.mate e := (C.mate_ne e).symm
  have hqe : C.mate p ≠ e := fun h ↦ hpx (by rw [← h, mate_mate])
  have hqx : C.mate p ≠ C.mate e := fun h ↦ hpe (C.mate.injective h)
  have hD := fourSet_closed C p e
  have part := fun {a : V} (ha : a ∈ fourSet C p e) ↦ exists_partner C R (fourSet C p e) hD ha
  have mp : p ∈ fourSet C p e := (mem_fourSet C p e).mpr (Or.inl rfl)
  have mq : C.mate p ∈ fourSet C p e := (mem_fourSet C p e).mpr (Or.inr (Or.inl rfl))
  have me : e ∈ fourSet C p e := (mem_fourSet C p e).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have mx : C.mate e ∈ fourSet C p e := (mem_fourSet C p e).mpr (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨k, hk, hkp, hpk, hku⟩ := part mp
  change (switchCut R C p e).Reachable p k at hpk
  change ∀ w ∈ fourSet C p e, (switchCut R C p e).Reachable p w → w = p ∨ w = k at hku
  rcases (mem_fourSet C p e).mp hk with h | h | h | h <;> rw [h] at hpk hku hkp
  · exact absurd rfl hkp
  · have hnpe : ¬(switchCut R C p e).Reachable p e := fun h ↦ by
      rcases hku e me h with h' | h'
      · exact hpe h'.symm
      · exact hqe h'.symm
    obtain ⟨k', hk', hk'e, hek', -⟩ := part me
    change (switchCut R C p e).Reachable e k' at hek'
    refine Or.inl ⟨hpk, ?_, hnpe⟩
    rcases (mem_fourSet C p e).mp hk' with h | h | h | h <;> rw [h] at hek' hk'e
    · exact absurd hek'.symm hnpe
    · exact absurd (hpk.trans hek'.symm) hnpe
    · exact absurd rfl hk'e
    · exact hek'
  · have hnpq : ¬(switchCut R C p e).Reachable p (C.mate p) := fun h ↦ by
      rcases hku _ mq h with h' | h'
      · exact hpq h'.symm
      · exact hqe h'
    obtain ⟨k', hk', hk'q, hqk', -⟩ := part mq
    change (switchCut R C p e).Reachable (C.mate p) k' at hqk'
    refine Or.inr (Or.inl ⟨hpk, ?_, hnpq⟩)
    rcases (mem_fourSet C p e).mp hk' with h | h | h | h <;> rw [h] at hqk' hk'q
    · exact absurd hqk'.symm hnpq
    · exact absurd rfl hk'q
    · exact absurd (hpk.trans hqk'.symm) hnpq
    · exact hqk'
  · have hnpq : ¬(switchCut R C p e).Reachable p (C.mate p) := fun h ↦ by
      rcases hku _ mq h with h' | h'
      · exact hpq h'.symm
      · exact hqx h'
    obtain ⟨k', hk', hk'q, hqk', -⟩ := part mq
    change (switchCut R C p e).Reachable (C.mate p) k' at hqk'
    refine Or.inr (Or.inr ⟨hpk, ?_, hnpq⟩)
    rcases (mem_fourSet C p e).mp hk' with h | h | h | h <;> rw [h] at hqk' hk'q
    · exact absurd hqk'.symm hnpq
    · exact absurd rfl hk'q
    · exact hqk'
    · exact absurd (hpk.trans hqk'.symm) hnpq

omit [Fintype V] in
/-- `R ∪ C` is `H` plus the two edges `pq`, `ex`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem sup_toGraph_eq_switchCut :
    R.toGraph ⊔ C.toGraph = switchCut R C p e ⊔ SimpleGraph.edge p (C.mate p) ⊔
      SimpleGraph.edge e (C.mate e) := by
  rw [toGraph_eq_offGraph_sup C (fourSet C p e) (fourSet_closed C p e) C (fun _ _ ↦ rfl) p e
    (fun v hv ↦ (mem_fourSet C p e).mp hv), switchCut]
  simp only [sup_assoc]

/-- When `pq` and `ex` lie on one cycle of `R ∪ C`, removing them joins `p` to exactly one of
`e`, `x` (`results/hybrid-joint-incoherence.md`, proof of Lemma 5). -/
theorem switchCut_reachable_iff (hpe : p ≠ e) (hpx : p ≠ C.mate e)
    (h : (R.toGraph ⊔ C.toGraph).Reachable p e) :
    (switchCut R C p e).Reachable p e ↔ ¬(switchCut R C p e).Reachable p (C.mate e) := by
  rcases pairing_of_four (R := R) hpe hpx with ⟨hpq, hex, hpe'⟩ | ⟨hpe', hqx, hpq⟩ |
      ⟨hpx', hqe, hpq⟩
  · rw [sup_toGraph_eq_switchCut, reachable_sup_edge_iff_of_reachable _ (hex.mono le_sup_left),
      reachable_sup_edge_iff_of_reachable _ hpq] at h
    exact absurd h hpe'
  · exact ⟨fun _ hx ↦ hpq (hx.trans hqx.symm), fun _ ↦ hpe'⟩
  · exact ⟨fun h' ↦ absurd (h'.trans hqe.symm) hpq, fun h' ↦ absurd hpx' h'⟩

/-- The 2-switch lemma. Let `C₁` replace the edges `pq`, `ex` of `C` by `pe`, `qx`. If `pq`
and `ex` lie on different cycles of `R ∪ C` the switch merges them and `κ` drops by one. If they
lie on the same cycle, `κ` rises by one when `p` and `e` stay joined after removing `pq` and
`ex`, and is unchanged otherwise. Theorem 11.1 of "Mathematical Pattern Investigation"
(`old-personal-chatgpt` doc 01a1e1d3-a7a1-728c-8db1-cd74249be926) and the 2-opt step in the
proof of Lemma 5 of `results/hybrid-joint-incoherence.md`. -/
theorem two_switch (C₁ : PerfectMatching V) (hpe : p ≠ e) (hpx : p ≠ C.mate e)
    (h1p : C₁.mate p = e) (h1q : C₁.mate (C.mate p) = C.mate e)
    (h1 : ∀ v ∉ fourSet C p e, C₁.mate v = C.mate v) :
    (¬(R.toGraph ⊔ C.toGraph).Reachable p e ∧ cycleCount R C₁ + 1 = cycleCount R C) ∨
      ((R.toGraph ⊔ C.toGraph).Reachable p e ∧ (switchCut R C p e).Reachable p e ∧
          cycleCount R C₁ = cycleCount R C + 1) ∨
      ((R.toGraph ⊔ C.toGraph).Reachable p e ∧ ¬(switchCut R C p e).Reachable p e ∧
          cycleCount R C₁ = cycleCount R C) := by
  have hD := fourSet_closed C p e
  set H := switchCut R C p e with hH
  have hG : R.toGraph ⊔ C.toGraph =
      H ⊔ SimpleGraph.edge p (C.mate p) ⊔ SimpleGraph.edge e (C.mate e) :=
    sup_toGraph_eq_switchCut
  have hG1 : R.toGraph ⊔ C₁.toGraph =
      H ⊔ SimpleGraph.edge p e ⊔ SimpleGraph.edge (C.mate p) (C.mate e) := by
    rw [toGraph_eq_offGraph_sup C (fourSet C p e) hD C₁ h1 p (C.mate p), h1p, h1q, hH, switchCut]
    · simp only [sup_assoc]
    · intro v hv
      rw [h1p, h1q]
      rcases (mem_fourSet C p e).mp hv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  have hle : H ≤ R.toGraph ⊔ C.toGraph := by
    rw [hG]
    exact le_sup_left.trans le_sup_left
  have k0 : cycleCount R C = Nat.card (H ⊔ SimpleGraph.edge p (C.mate p) ⊔
      SimpleGraph.edge e (C.mate e)).ConnectedComponent := by
    unfold cycleCount
    rw [hG]
  have k1 : cycleCount R C₁ = Nat.card (H ⊔ SimpleGraph.edge p e ⊔
      SimpleGraph.edge (C.mate p) (C.mate e)).ConnectedComponent := by
    unfold cycleCount
    rw [hG1]
  rcases pairing_of_four (R := R) hpe hpx with ⟨hpq, hex, hpe'⟩ | ⟨hpe', hqx, hpq⟩ |
      ⟨hpx', hqe, hpq⟩
  · left
    have hc1 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p (C.mate p))
      (hex.mono le_sup_left)
    have hc2 := card_sup_edge_of_reachable H hpq
    have hc3 := card_sup_edge_add_one H hpe'
    have hc4 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p e)
      (u := C.mate p) (v := C.mate e)
      ((reachable_sup_edge_iff H p e _ _).mpr (Or.inr (Or.inl ⟨hpq.symm, hex⟩)))
    refine ⟨fun h ↦ hpe' ?_, by omega⟩
    rw [hG, reachable_sup_edge_iff_of_reachable _ (hex.mono le_sup_left),
      reachable_sup_edge_iff_of_reachable _ hpq] at h
    exact h
  · right; left
    have hc1 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p (C.mate p))
      (u := e) (v := C.mate e)
      ((reachable_sup_edge_iff H p (C.mate p) _ _).mpr (Or.inr (Or.inl ⟨hpe'.symm, hqx⟩)))
    have hc2 := card_sup_edge_add_one H hpq
    have hc3 := card_sup_edge_of_reachable H hpe'
    have hc4 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p e)
      (hqx.mono le_sup_left)
    exact ⟨hpe'.mono hle, hpe', by omega⟩
  · right; right
    have hnpe : ¬H.Reachable p e := fun h ↦ hpq (h.trans hqe.symm)
    have hc1 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p (C.mate p))
      (u := e) (v := C.mate e)
      ((reachable_sup_edge_iff H p (C.mate p) _ _).mpr (Or.inr (Or.inr ⟨hqe.symm, hpx'⟩)))
    have hc2 := card_sup_edge_add_one H hpq
    have hc3 := card_sup_edge_add_one H hnpe
    have hc4 := card_sup_edge_of_reachable (H ⊔ SimpleGraph.edge p e)
      (u := C.mate p) (v := C.mate e)
      ((reachable_sup_edge_iff H p e _ _).mpr (Or.inr (Or.inr ⟨hqe, hpx'⟩)))
    refine ⟨?_, hnpe, by omega⟩
    exact (adj_mate_right R C p).reachable.trans (hqe.mono hle)

end Switch

section Insertion

variable [Fintype V] [DecidableEq V] {yp ym : V}

/-- `V(E⁻)`, the vertices other than the two ends `y₊, y₋` of the inserted defect `y`
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def lowerSet (yp ym : V) : Finset V := ({yp, ym} : Finset V)ᶜ

/-- `V(E⁻)` is everything but `y₊`, `y₋`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem mem_lowerSet {v : V} : v ∈ lowerSet yp ym ↔ v ≠ yp ∧ v ≠ ym := by
  simp [lowerSet]

/-- `(R⁻ ∖ {a, b}) ∪ (C⁻ ∖ f)` with `f = {p, C⁻ p}`: the lower union with the split edge of `R⁻`
and the slot `f` of `C⁻` removed (`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def cutGraph {A : Type*} (Rm Cm : PerfectMatching A) (a b p : A) : SimpleGraph A :=
  Rm.toGraph.deleteEdges {s(a, b)} ⊔ Cm.toGraph.deleteEdges {s(p, Cm.mate p)}

private theorem sym2_ne_of_ne {A : Type*} {v w a b : A} (ha : v ≠ a) (hb : v ≠ b) :
    s(v, w) ∉ ({s(a, b)} : Set (Sym2 A)) := by
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact ha h
  · exact hb h

/-- **Lemma 5 (insertion of one defect, exact).** `results/hybrid-joint-incoherence.md`.
The upper level lives on `V ⊇ V(E⁻) ∪ {y₊, y₋}`, the lower level on `V(E⁻) = lowerSet y₊ y₋`.
`R` has edges `{y₊, a}`, `{y₋, b}` and `R⁻` is `R` with these replaced by `{a, b}`. `C⁻` is a
lower context with slot `f = {p, q}`, `q = C⁻ p`, and `C` is `C⁻` with `f` replaced by
`p–entry(y)`, `exit(y)–q`, where `{entry, exit} = {y₊, y₋}` is the sign of `y`. Then
`κ(R ∪ C) − κ(R⁻ ∪ C⁻)` is `−1` when `f` and `{a, b}` lie on different cycles of `R⁻ ∪ C⁻`.
When they lie on one cycle it is `+1` if `p` is joined to `R(entry)` in
`(R⁻ ∖ {a, b}) ∪ (C⁻ ∖ f)` and `0` otherwise, and `p` is joined there to exactly one of
`a`, `b`. This last fact is the relative orientation of `f` and `{a, b}`, so the sign of `y`,
the orientation of `R` at `y` and that orientation decide between `0` and `+1`. -/
theorem insertion_cycleCount (hy : yp ≠ ym) (R : PerfectMatching V) (a b : lowerSet yp ym)
    (hRa : R.mate yp = a) (hRb : R.mate ym = b)
    (Rm : PerfectMatching (lowerSet yp ym)) (hRab : Rm.mate a = b)
    (hRm : ∀ v, v ≠ a → v ≠ b → (Rm.mate v : V) = R.mate v)
    (Cm : PerfectMatching (lowerSet yp ym)) (p : lowerSet yp ym)
    (C : PerfectMatching V) {ent ext : V} (hent : ent = yp ∧ ext = ym ∨ ent = ym ∧ ext = yp)
    (hCp : C.mate p = ent) (hCq : C.mate (Cm.mate p) = ext)
    (hC : ∀ v, v ≠ p → v ≠ Cm.mate p → C.mate v = Cm.mate v) :
    (¬(Rm.toGraph ⊔ Cm.toGraph).Reachable p a → cycleCount R C + 1 = cycleCount Rm Cm) ∧
      ((Rm.toGraph ⊔ Cm.toGraph).Reachable p a → ∀ r : lowerSet yp ym, (r : V) = R.mate ent →
        ((cutGraph Rm Cm a b p).Reachable p r → cycleCount R C = cycleCount Rm Cm + 1) ∧
        (¬(cutGraph Rm Cm a b p).Reachable p r → cycleCount R C = cycleCount Rm Cm)) ∧
      ((Rm.toGraph ⊔ Cm.toGraph).Reachable p a →
        ((cutGraph Rm Cm a b p).Reachable p a ↔ ¬(cutGraph Rm Cm a b p).Reachable p b)) := by
  set q := Cm.mate p with hq
  have memL : ∀ v : (lowerSet yp ym), (v : V) ≠ yp ∧ (v : V) ≠ ym := fun v ↦ mem_lowerSet.mp v.2
  have notL : ∀ v : V, v ∉ (lowerSet yp ym) → v = yp ∨ v = ym := by
    intro v hv
    by_contra h
    push Not at h
    exact hv (mem_lowerSet.mpr h)
  have hentL : ent ≠ yp → ent = ym := fun h ↦ by rcases hent with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all
  have hent' : ent ∉ (lowerSet yp ym) ∧ ext ∉ (lowerSet yp ym) ∧ ent ≠ ext := by
    rcases hent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun h ↦ (mem_lowerSet.mp h).1 rfl, fun h ↦ (mem_lowerSet.mp h).2 rfl, hy⟩
    · exact ⟨fun h ↦ (mem_lowerSet.mp h).2 rfl, fun h ↦ (mem_lowerSet.mp h).1 rfl, hy.symm⟩
  clear hentL
  have neL : ∀ v : (lowerSet yp ym), (v : V) ≠ ent ∧ (v : V) ≠ ext := fun v ↦
    ⟨fun h ↦ hent'.1 (h ▸ v.2), fun h ↦ hent'.2.1 (h ▸ v.2)⟩
  have hRa' : R.mate a = yp := by rw [← hRa, mate_mate]
  have hRb' : R.mate b = ym := by rw [← hRb, mate_mate]
  have hRba : Rm.mate b = a := by rw [← hRab, mate_mate]
  have hab : a ≠ b := fun h ↦
    hy (hRa'.symm.trans ((congrArg (fun z : lowerSet yp ym ↦ R.mate z) h).trans hRb'))
  have hpq : p ≠ q := (Cm.mate_ne p).symm
  have hqp : Cm.mate q = p := Cm.mate_mate p
  have hCent : C.mate ent = p := by rw [← hCp, mate_mate]
  have hCext : C.mate ext = q := by rw [← hCq, mate_mate]
  let C0 : PerfectMatching V := Equiv.swap ent (q : V) • C
  have hC0 : ∀ v, C0.mate v = Equiv.swap ent (q : V) (C.mate (Equiv.swap ent (q : V) v)) := by
    intro v
    rw [smul_mate, Equiv.swap_inv]
  have hqent : (q : V) ≠ ent := (neL q).1
  have hqext : (q : V) ≠ ext := (neL q).2
  have hpent : (p : V) ≠ ent := (neL p).1
  have hpext : (p : V) ≠ ext := (neL p).2
  have C0p : C0.mate p = q := by
    rw [hC0, Equiv.swap_apply_of_ne_of_ne hpent (fun h ↦ hpq (Subtype.ext h)), hCp,
      Equiv.swap_apply_left]
  have C0q : C0.mate q = p := by rw [← C0p, mate_mate]
  have C0ent : C0.mate ent = ext := by
    rw [hC0, Equiv.swap_apply_left, hCq, Equiv.swap_apply_of_ne_of_ne hent'.2.2.symm hqext.symm]
  have C0ext : C0.mate ext = ent := by rw [← C0ent, mate_mate]
  have C0o : ∀ v : V, v ≠ p → v ≠ q → v ≠ ent → v ≠ ext → C0.mate v = C.mate v := by
    intro v h1 h2 h3 h4
    rw [hC0, Equiv.swap_apply_of_ne_of_ne h3 h2]
    refine Equiv.swap_apply_of_ne_of_ne (fun h ↦ h1 ?_) (fun h ↦ h4 ?_)
    · rw [← C.mate_mate v, h, hCent]
    · rw [← C.mate_mate v, h, hCq]
  have C0L : ∀ v : (lowerSet yp ym), v ≠ p → v ≠ q → C0.mate v = Cm.mate v := fun v h1 h2 ↦ by
    rw [C0o v (fun h ↦ h1 (Subtype.ext h)) (fun h ↦ h2 (Subtype.ext h)) (neL v).1 (neL v).2,
      hC v h1 h2]
  have RL : ∀ v : (lowerSet yp ym), v ≠ a → v ≠ b → R.mate v = Rm.mate v :=
    fun v h1 h2 ↦ (hRm v h1 h2).symm
  have hD := fourSet_closed C0 p ent
  have memD : ∀ v, v ∈ fourSet C0 p ent ↔ v = p ∨ v = q ∨ v = ent ∨ v = ext := by
    intro v
    rw [mem_fourSet, C0p, C0ent]
  have hsw := two_switch (R := R) (C := C0) (p := p) (e := ent) C hpent (by rwa [C0ent]) hCp
    (by rw [C0p, C0ent, hCq]) (fun v hv ↦ by
      rw [memD] at hv
      push Not at hv
      exact (C0o v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2).symm)
  have hdich := fun h ↦ switchCut_reachable_iff (R := R) (C := C0) (p := p) (e := ent) hpent
    (by rwa [C0ent]) h
  rw [C0ent] at hdich
  let π : V → (lowerSet yp ym) := fun v ↦
    if h : v ∈ (lowerSet yp ym) then ⟨v, h⟩ else if v = yp then a else b
  have πL : ∀ v : (lowerSet yp ym), π v = v := fun v ↦ by simp [π, v.2]
  have πyp : π yp = a := by
    have : yp ∉ (lowerSet yp ym) := fun h ↦ (mem_lowerSet.mp h).1 rfl
    simp [π, this]
  have πym : π ym = b := by
    have : ym ∉ (lowerSet yp ym) := fun h ↦ (mem_lowerSet.mp h).2 rfl
    simp [π, this, hy.symm]
  have πR : ∀ v, v ∉ (lowerSet yp ym) → (π v : V) = R.mate v := by
    intro v hv
    rcases notL v hv with rfl | rfl
    · rw [πyp, hRa]
    · rw [πym, hRb]
  have Gm_ab : (Rm.toGraph ⊔ Cm.toGraph).Reachable a b := (adj_mate_left Rm Cm a).reachable.trans
    (by rw [hRab])
  have C0yp : C0.mate yp = ym := by
    rcases hent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C0ent
    · exact C0ext
  have G_ab : (R.toGraph ⊔ C0.toGraph).Reachable a b := by
    have h1 : (R.toGraph ⊔ C0.toGraph).Adj a yp := Or.inl hRa'
    have h2 : (R.toGraph ⊔ C0.toGraph).Adj yp ym := Or.inr C0yp
    have h3 : (R.toGraph ⊔ C0.toGraph).Adj ym b := Or.inl hRb
    exact h1.reachable.trans (h2.reachable.trans h3.reachable)
  have hfix : ∀ (G : SimpleGraph V) (G' : SimpleGraph (lowerSet yp ym)),
      (∀ (v : lowerSet yp ym) (w : V), G.Adj v w → G'.Reachable v (π w)) →
      (∀ v w : V, v ∉ (lowerSet yp ym) → w ∉ (lowerSet yp ym) → G.Adj v w →
        G'.Reachable (π v) (π w)) →
      ∀ v w, G.Adj v w → G'.Reachable (π v) (π w) := by
    intro G G' hL1 hL2 v w hvw
    by_cases hv : v ∈ (lowerSet yp ym)
    · have := hL1 ⟨v, hv⟩ w hvw
      rwa [← πL ⟨v, hv⟩] at this
    · by_cases hw : w ∈ (lowerSet yp ym)
      · have := hL1 ⟨w, hw⟩ v hvw.symm
        rw [← πL ⟨w, hw⟩] at this
        exact this.symm
      · exact hL2 v w hv hw hvw
  have h3 : ∀ v, (R.toGraph ⊔ C0.toGraph).Reachable v (π v) := by
    intro v
    by_cases hv : v ∈ (lowerSet yp ym)
    · rw [show π v = ⟨v, hv⟩ from πL ⟨v, hv⟩]
    · rw [πR v hv]
      exact (adj_mate_left R C0 v).reachable
  have h3H : ∀ v, (switchCut R C0 p ent).Reachable v (π v) := by
    intro v
    by_cases hv : v ∈ (lowerSet yp ym)
    · rw [show π v = ⟨v, hv⟩ from πL ⟨v, hv⟩]
    · rw [πR v hv]
      exact SimpleGraph.Adj.reachable (Or.inl rfl)
  have h1G := hfix (R.toGraph ⊔ C0.toGraph) (Rm.toGraph ⊔ Cm.toGraph)
    (fun v w hvw ↦ by
      rcases hvw with hvw | hvw
      · change R.mate v = w at hvw
        by_cases hva : v = a
        · subst hva
          rw [← hvw, hRa', πyp]
        by_cases hvb : v = b
        · subst hvb
          rw [← hvw, hRb', πym]
        rw [← hvw, RL v hva hvb, πL]
        exact (adj_mate_left Rm Cm v).reachable
      · change C0.mate v = w at hvw
        by_cases hvp : v = p
        · subst hvp
          rw [← hvw, C0p, πL]
          exact (adj_mate_right Rm Cm v).reachable
        by_cases hvq : v = q
        · subst hvq
          rw [← hvw, C0q, πL, ← hqp]
          exact (adj_mate_right Rm Cm _).reachable
        rw [← hvw, C0L v hvp hvq, πL]
        exact (adj_mate_right Rm Cm v).reachable)
    (fun v w hv hw hvw ↦ by
      have hne := hvw.ne
      rcases notL v hv with rfl | rfl <;> rcases notL w hw with rfl | rfl
      · exact absurd rfl hne
      · rw [πyp, πym]
        exact Gm_ab
      · rw [πyp, πym]
        exact Gm_ab.symm
      · exact absurd rfl hne)
  have h2G : ∀ v w : (lowerSet yp ym), (Rm.toGraph ⊔ Cm.toGraph).Adj v w →
      (R.toGraph ⊔ C0.toGraph).Reachable v w := by
    intro v w hvw
    rcases hvw with hvw | hvw
    · change Rm.mate v = w at hvw
      by_cases hva : v = a
      · subst hva
        rw [← hvw, hRab]
        exact G_ab
      by_cases hvb : v = b
      · subst hvb
        rw [← hvw, hRba]
        exact G_ab.symm
      rw [← hvw, ← RL v hva hvb]
      exact (adj_mate_left R C0 v).reachable
    · change Cm.mate v = w at hvw
      by_cases hvp : v = p
      · subst hvp
        rw [← hvw, ← C0p]
        exact (adj_mate_right R C0 _).reachable
      by_cases hvq : v = q
      · subst hvq
        rw [← hvw, hqp, ← C0q]
        exact (adj_mate_right R C0 _).reachable
      rw [← hvw, ← C0L v hvp hvq]
      exact (adj_mate_right R C0 v).reachable
  have h1H := hfix (switchCut R C0 p ent) (cutGraph Rm Cm a b p)
    (fun v w hvw ↦ by
      rcases hvw with hvw | ⟨hvw, hvD⟩
      · change R.mate v = w at hvw
        by_cases hva : v = a
        · subst hva
          rw [← hvw, hRa', πyp]
        by_cases hvb : v = b
        · subst hvb
          rw [← hvw, hRb', πym]
        rw [← hvw, RL v hva hvb, πL]
        exact SimpleGraph.Adj.reachable
          (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨rfl, sym2_ne_of_ne hva hvb⟩))
      · rw [memD] at hvD
        push Not at hvD
        have hvp : v ≠ p := fun h ↦ hvD.1 (congrArg Subtype.val h)
        have hvq : v ≠ q := fun h ↦ hvD.2.1 (congrArg Subtype.val h)
        rw [← hvw, C0L v hvp hvq, πL]
        exact SimpleGraph.Adj.reachable
          (Or.inr (SimpleGraph.deleteEdges_adj.mpr ⟨rfl, sym2_ne_of_ne hvp hvq⟩)))
    (fun v w hv hw hvw ↦ by
      exfalso
      rcases hvw with hvw | ⟨-, hvD⟩
      · change R.mate v = w at hvw
        rcases notL v hv with rfl | rfl
        · exact hw (hvw ▸ hRa ▸ a.2)
        · exact hw (hvw ▸ hRb ▸ b.2)
      · rw [memD] at hvD
        rcases notL v hv with rfl | rfl <;> rcases hent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp at hvD)
  have h2H : ∀ v w : (lowerSet yp ym), (cutGraph Rm Cm a b p).Adj v w →
      (switchCut R C0 p ent).Reachable v w := by
    intro v w hvw
    rcases hvw with hvw0 | hvw0 <;> obtain ⟨hvw, hs⟩ := SimpleGraph.deleteEdges_adj.mp hvw0 <;>
      clear hvw0
    · change Rm.mate v = w at hvw
      have hva : v ≠ a := by
        rintro rfl
        exact hs (by rw [← hvw, hRab]; exact Set.mem_singleton _)
      have hvb : v ≠ b := by
        rintro rfl
        exact hs (by rw [← hvw, hRba, Set.mem_singleton_iff, Sym2.eq_swap])
      rw [← hvw, ← RL v hva hvb]
      exact SimpleGraph.Adj.reachable (Or.inl rfl)
    · change Cm.mate v = w at hvw
      have hvp : v ≠ p := by
        rintro rfl
        exact hs (by rw [← hvw]; exact Set.mem_singleton _)
      have hvq : v ≠ q := by
        rintro rfl
        exact hs (by rw [← hvw, hqp, Set.mem_singleton_iff, Sym2.eq_swap])
      rw [← hvw, ← C0L v hvp hvq]
      refine SimpleGraph.Adj.reachable (Or.inr ⟨rfl, ?_⟩)
      rw [memD]
      push Not
      exact ⟨fun h ↦ hvp (Subtype.ext h), fun h ↦ hvq (Subtype.ext h), (neL v).1, (neL v).2⟩
  have hκ : cycleCount R C0 = cycleCount Rm Cm :=
    card_connectedComponent_eq_of_retract π Subtype.val h1G h2G h3
      (fun w ↦ by rw [πL])
  have hGr := reachable_iff_of_retract π Subtype.val h1G h2G h3
  have hHr := reachable_iff_of_retract π Subtype.val h1H h2H h3H
  have πent : π ent = a ∨ π ent = b := by
    rcases hent with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl πyp
    · exact Or.inr πym
  have hGp : (R.toGraph ⊔ C0.toGraph).Reachable p ent ↔
      (Rm.toGraph ⊔ Cm.toGraph).Reachable p a := by
    rw [hGr, πL]
    rcases πent with h | h <;> rw [h]
    exact ⟨fun h' ↦ h'.trans Gm_ab.symm, fun h' ↦ h'.trans Gm_ab⟩
  have πr : ∀ r : (lowerSet yp ym), (r : V) = R.mate ent → π ent = r := by
    intro r hr
    apply Subtype.ext
    rw [πR ent hent'.1, hr]
  refine ⟨fun hn ↦ ?_, fun hr r hrr ↦ ?_, fun hr ↦ ?_⟩
  · rcases hsw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [← hκ, h]
    · exact absurd (hGp.mp h) hn
    · exact absurd (hGp.mp h) hn
  · have hHp : (switchCut R C0 p ent).Reachable p ent ↔ (cutGraph Rm Cm a b p).Reachable p r := by
      rw [hHr, πL, πr r hrr]
    rcases hsw with ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · exact absurd (hGp.mpr hr) h
    · exact ⟨fun _ ↦ by rw [h2, hκ], fun h ↦ absurd (hHp.mp h1) h⟩
    · exact ⟨fun h ↦ absurd (hHp.mpr h) h1, fun _ ↦ by rw [h2, hκ]⟩
  · have hd := hdich (hGp.mpr hr)
    rw [hHr, hHr, πL] at hd
    rcases hent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [πyp, πym] at hd
    · rw [πyp, πym] at hd
      exact ⟨fun h1 h2 ↦ hd.mp h2 h1, fun h1 ↦ by_contra fun h2 ↦ h1 (hd.mpr h2)⟩

/-- **Lemma 5, last sentence.** `results/hybrid-joint-incoherence.md`. If `R⁻ ∪ C⁻` is one
cycle, then for every slot `f = {p, C⁻ p}` exactly one of the two signs of `y` gives a
Hamiltonian `R ∪ C`. Here `C₁` enters `y` at `y₊` and `C₂` enters it at `y₋`. -/
theorem insertion_ham_iff (hy : yp ≠ ym) (R : PerfectMatching V) (a b : lowerSet yp ym)
    (hRa : R.mate yp = a) (hRb : R.mate ym = b)
    (Rm : PerfectMatching (lowerSet yp ym)) (hRab : Rm.mate a = b)
    (hRm : ∀ v, v ≠ a → v ≠ b → (Rm.mate v : V) = R.mate v)
    (Cm : PerfectMatching (lowerSet yp ym)) (p : lowerSet yp ym) (C₁ C₂ : PerfectMatching V)
    (h1p : C₁.mate p = yp) (h1q : C₁.mate (Cm.mate p) = ym)
    (h1 : ∀ v, v ≠ p → v ≠ Cm.mate p → C₁.mate v = Cm.mate v)
    (h2p : C₂.mate p = ym) (h2q : C₂.mate (Cm.mate p) = yp)
    (h2 : ∀ v, v ≠ p → v ≠ Cm.mate p → C₂.mate v = Cm.mate v)
    (hH : Ham Rm Cm) : Ham R C₁ ↔ ¬Ham R C₂ := by
  have hκ := (ham_iff_cycleCount_eq_one Rm Cm).mp hH
  have hr : (Rm.toGraph ⊔ Cm.toGraph).Reachable p a := hH.preconnected p a
  obtain ⟨-, h1', h3⟩ := insertion_cycleCount hy R a b hRa hRb Rm hRab hRm Cm p C₁
    (Or.inl ⟨rfl, rfl⟩) h1p h1q h1
  obtain ⟨-, h2', -⟩ := insertion_cycleCount hy R a b hRa hRb Rm hRab hRm Cm p C₂
    (Or.inr ⟨rfl, rfl⟩) h2p h2q h2
  have e1 := h1' hr a hRa.symm
  have e2 := h2' hr b hRb.symm
  have hd := h3 hr
  rw [ham_iff_cycleCount_eq_one, ham_iff_cycleCount_eq_one]
  by_cases ha : (cutGraph Rm Cm a b p).Reachable p a
  · rw [e1.1 ha, e2.2 (hd.mp ha), hκ]
    simp
  · have hb : (cutGraph Rm Cm a b p).Reachable p b := by
      by_contra hb
      exact ha (hd.mpr hb)
    rw [e1.2 ha, e2.1 hb, hκ]
    simp

end Insertion

end PerfectMatching

end Pairing
