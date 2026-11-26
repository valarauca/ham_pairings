import Repair.SqrtObstructions.CertLength

/-!
# Proposition NC: what an `o(√m)` proof must find near hybrids

Source: `results/sqrt-m-obstructions.md` §1.5, Proposition NC, with the corrections of
`results/review-sqrt-m-obstructions.md` §4. Put `n = 2m - 1`, prime, `G0` the default gadget and
`T(n)` the factor tail, the restriction of `F_{s0}` to `U = V_m ∖ G0`.

A hybrid is a tail `H` with `T(n) ∖ H = E′` and `H ∖ T(n) = R′`, `|E′| = |R′| = d′`. Since
`T(n)` consists of all `F_{s0}`-edges inside `U`, `H ∖ T(n) = H ∖ F_{s0}`
(`card_sdiff_factorTail`), so `R′ ∩ F_{s0} = ∅` holds for every tail and
`d′ = tailDist F_{s0} H`. For a zero state `P` with `|H ∖ P| ≤ K` and `k = |P ∖ F_{s0}|`:

* `nearHybrid_kept` (i) : `|P ∩ R′| ≥ d′ - K`.
* `nearHybrid_defects` (ii) : `d′ - K ≤ k ≤ K + d′ + 3`.
* `nearHybrid_certLength` (iii) : if `L(P) ≤ L`, then `n - 1 ≤ 2k((2k + 2)L - 1)`, and so
  `n - 1 ≤ 2(K + d′ + 3)((2(K + d′ + 3) + 2)L - 1)`.
* `nearHybrid_majority` : the review's correction of "most of the generic defects". `P` keeps more
  than half of `R′` once `2K < d′`, that is `δ < ε/2` at `d′ = ε√m`, `K = δ√m`.
* `exists_nearHybrid` : the necessary condition itself. If `N_m ≤ K` for `G0`, every tail `H` has
  a zero state with all of the above.

The review notes that the bound on `L(P)` is a constant, `(1 - o(1))/(2(ε + δ)²)`, which is
vacuous once `ε + δ ≥ 1/√2`. The finite statements here carry no asymptotics.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangle inequality for defects through a tail (`sqrt-m-obstructions.md` §1.5, proof of
Proposition NC (ii)): `|defect Q P| ≤ 2 |T ∖ P| + 2 |T ∖ Q| + |V ∖ U|` for a tail `T` of `U`. -/
theorem card_defect_le_tailDist_add (Q P : PerfectMatching V) {U : Finset V}
    (T : PerfectMatching U) :
    (defect Q P).card ≤ 2 * tailDist P T + 2 * tailDist Q T + Uᶜ.card := by
  rw [two_mul_tailDist, two_mul_tailDist]
  calc (defect Q P).card
      ≤ ((Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u).map
            (Function.Embedding.subtype _) ∪
          (Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ Q.mate u).map
            (Function.Embedding.subtype _) ∪ Uᶜ).card := by
        refine Finset.card_le_card fun w hw ↦ ?_
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_compl]
        by_cases h : w ∈ U
        · by_cases hP : (T.mate ⟨w, h⟩ : V) = P.mate w
          · refine Or.inl (Or.inr (Finset.mem_map.mpr ⟨⟨w, h⟩, ?_, rfl⟩))
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, fun h' ↦ mem_defect.mp hw (hP.symm.trans h')⟩
          · exact Or.inl (Or.inl (Finset.mem_map.mpr
              ⟨⟨w, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, rfl⟩))
        · exact Or.inr h
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans ?_) _)
        rw [Finset.card_map, Finset.card_map]

/-- The edges of a tail `H` that lie outside `Q` and inside `P`. For `Q = F_{s0}` these are the
generic defects `R′` of the hybrid `H` that `P` keeps, `P ∩ R′` (`sqrt-m-obstructions.md` §1.5,
Proposition NC). -/
def keptEdges (Q P : PerfectMatching V) {U : Finset V} (H : PerfectMatching U) :
    Finset (Sym2 V) :=
  (tailEdges H).filter fun e ↦ e ∉ Q.toGraph.edgeSet ∧ e ∈ P.toGraph.edgeSet

omit [Fintype V] in
/-- `|H ∖ Q| ≤ |P ∩ (H ∖ Q)| + |H ∖ P|` (`sqrt-m-obstructions.md` §1.5, Proposition NC (i)). -/
theorem tailDist_le_card_keptEdges_add (Q P : PerfectMatching V) {U : Finset V}
    (H : PerfectMatching U) : tailDist Q H ≤ (keptEdges Q P H).card + tailDist P H := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (tailEdges H).filter fun e ↦ e ∉ Q.toGraph.edgeSet) (p := fun e ↦ e ∈ P.toGraph.edgeSet)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hsub : ((tailEdges H).filter fun e ↦ e ∉ Q.toGraph.edgeSet ∧ e ∉ P.toGraph.edgeSet) ⊆
      (tailEdges H).filter fun e ↦ e ∉ P.toGraph.edgeSet :=
    fun e he ↦ by
      rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, he.2.2⟩
  have h2 := Finset.card_le_card hsub
  rw [tailDist, keptEdges, tailDist]
  omega

/-- The kept defects are edges of `P` outside `Q` (`sqrt-m-obstructions.md` §1.5,
Proposition NC (ii)): `|P ∩ (H ∖ Q)| ≤ |P ∖ Q|`. -/
theorem card_keptEdges_le (Q P : PerfectMatching V) {U : Finset V} (H : PerfectMatching U) :
    (keptEdges Q P H).card ≤ (edgesOutside Q P).card := by
  refine Finset.card_le_card fun e he ↦ ?_
  have h := (Finset.mem_filter.mp he).2
  exact mem_edgesOutside.mpr ⟨h.2, h.1⟩

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `H ∖ T(n) = H ∖ F_{s0}` for every tail `H` of `G0`, so `|R′| = tailDist F_{s0} H` and
`R′ ∩ F_{s0} = ∅` holds automatically (`sqrt-m-obstructions.md` §1.5, Proposition NC). -/
theorem card_sdiff_factorTail (hm : 5 ≤ m)
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) :
    (tailEdges H \ tailEdges (FactorCap.factorTail m hm)).card =
      tailDist (factor m (FactorCap.capCenter m)) H := by
  rw [tailDist, Finset.sdiff_eq_filter]
  congr 1
  refine Finset.filter_congr fun e he ↦ ?_
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp he
  rw [SimpleGraph.mem_edgeSet, toGraph_adj]
  constructor
  · intro h hF
    refine h (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩)
    rw [FactorCap.factorTail_mate, hF]
  · intro h hT
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hT
    rw [FactorCap.factorTail_mate] at hv
    rcases Sym2.eq_iff.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, h2] at h
      exact h rfl
    · rw [← h2, ← h1, mate_mate] at h
      exact h rfl

/-- **Proposition NC (i)** (`sqrt-m-obstructions.md` §1.5). A perfect matching `P` within `K`
of the hybrid `H` keeps at least `d′ - K` of its generic defects `R′ = H ∖ F_{s0}`, where
`d′ = |R′|`: `d′ ≤ |P ∩ R′| + K`. -/
theorem nearHybrid_kept
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
    (P : PerfectMatching (Vertex m)) {K : ℕ} (hK : tailDist P H ≤ K) :
    tailDist (factor m (FactorCap.capCenter m)) H ≤
      (keptEdges (factor m (FactorCap.capCenter m)) P H).card + K :=
  (tailDist_le_card_keptEdges_add _ P H).trans (Nat.add_le_add_left hK _)

/-- **Proposition NC (ii)** (`sqrt-m-obstructions.md` §1.5). If `|H ∖ P| ≤ K` and
`d′ = |H ∖ F_{s0}|`, then `k = |P ∖ F_{s0}|` satisfies `d′ - K ≤ k ≤ K + d′ + 3`. -/
theorem nearHybrid_defects (hm : 5 ≤ m)
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
    (P : PerfectMatching (Vertex m)) {K : ℕ} (hK : tailDist P H ≤ K) :
    tailDist (factor m (FactorCap.capCenter m)) H ≤
        (edgesOutside (factor m (FactorCap.capCenter m)) P).card + K ∧
      (edgesOutside (factor m (FactorCap.capCenter m)) P).card ≤
        K + tailDist (factor m (FactorCap.capCenter m)) H + 3 := by
  refine ⟨(nearHybrid_kept H P hK).trans (Nat.add_le_add_right (card_keptEdges_le _ P H) _),
    ?_⟩
  have h1 := two_mul_card_edgesOutside (factor m (FactorCap.capCenter m)) P
  have h2 := card_defect_le_tailDist_add (factor m (FactorCap.capCenter m)) P H
  rw [compl_compl, card_gadget hm] at h2
  omega

/-- **Proposition NC, majority form** (`review-sqrt-m-obstructions.md` §4, correcting "most of
the generic defects" in `sqrt-m-obstructions.md` §1.5). If `2K < d′`, a perfect matching within
`K` of the hybrid `H` keeps more than half of its `d′` generic defects. -/
theorem nearHybrid_majority
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
    (P : PerfectMatching (Vertex m)) {K : ℕ} (hK : tailDist P H ≤ K)
    (hKd : 2 * K < tailDist (factor m (FactorCap.capCenter m)) H) :
    tailDist (factor m (FactorCap.capCenter m)) H <
      2 * (keptEdges (factor m (FactorCap.capCenter m)) P H).card := by
  have h := nearHybrid_kept H P hK
  omega

/-- **Proposition NC (iii)** (`sqrt-m-obstructions.md` §1.5, by Theorem C′). Let `n = 2m - 1`
be prime and `P` a zero state within `K` of the hybrid `H`, with `d′ = |H ∖ F_{s0}|` and
`k = |P ∖ F_{s0}|`. If `L(P) ≤ L`, then `n - 1 ≤ 2k((2k + 2)L - 1)` and
`n - 1 ≤ 2(K + d′ + 3)((2(K + d′ + 3) + 2)L - 1)`. -/
theorem nearHybrid_certLength (hp : (2 * m - 1).Prime) (hm : 5 ≤ m)
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
    {P : PerfectMatching (Vertex m)} (hP : IsZeroState (factor m) P) {K L : ℕ}
    (hK : tailDist P H ≤ K)
    (hcert : ∀ t ≠ FactorCap.capCenter m, ∃ y r, 1 ≤ r ∧ r ≤ L ∧ (certPerm P t ^ r) y = y) :
    2 * m - 2 ≤ 2 * (edgesOutside (factor m (FactorCap.capCenter m)) P).card *
        ((2 * (edgesOutside (factor m (FactorCap.capCenter m)) P).card + 2) * L - 1) ∧
      2 * m - 2 ≤ 2 * (K + tailDist (factor m (FactorCap.capCenter m)) H + 3) *
        ((2 * (K + tailDist (factor m (FactorCap.capCenter m)) H + 3) + 2) * L - 1) := by
  have h := certLength_bound_of_isZeroState hp hP _ hcert
  have hk := (nearHybrid_defects hm H P hK).2
  exact ⟨h, h.trans (Nat.mul_le_mul (by omega)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right L (by omega)) 1))⟩

/-- **Proposition NC** (`sqrt-m-obstructions.md` §1.5 and Status, with
`review-sqrt-m-obstructions.md` §4). Let `n = 2m - 1` be prime and suppose `N_m ≤ K` for the
gadget `G0`. Then every tail `H`, in particular every hybrid with `d′ = |H ∖ T(n)|` generic
defects, is within `K` of a zero state `P` with `k = |P ∖ F_{s0}|` such that
`d′ ≤ |P ∩ R′| + K`, `d′ ≤ k + K`, `k ≤ K + d′ + 3`, and `n - 1 ≤ 2k((2k + 2)L - 1)` whenever
`L(P) ≤ L`. So an `o(√m)` bound must produce zero states that are `Θ(√m)`-defect perturbations
of `F_{s0}` near hybrids with `d′ = Θ(√m)`. -/
theorem exists_nearHybrid (hp : (2 * m - 1).Prime) (hm : 5 ≤ m) {K : ℕ}
    (hN : RepairBound m (FactorCap.gadget m) K)
    (H : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) :
    ∃ P : ZeroState m, tailDist P.1 H ≤ K ∧
      tailDist (factor m (FactorCap.capCenter m)) H ≤
        (keptEdges (factor m (FactorCap.capCenter m)) P.1 H).card + K ∧
      tailDist (factor m (FactorCap.capCenter m)) H ≤
        (edgesOutside (factor m (FactorCap.capCenter m)) P.1).card + K ∧
      (edgesOutside (factor m (FactorCap.capCenter m)) P.1).card ≤
        K + tailDist (factor m (FactorCap.capCenter m)) H + 3 ∧
      ∀ L, (∀ t ≠ FactorCap.capCenter m, ∃ y r, 1 ≤ r ∧ r ≤ L ∧ (certPerm P.1 t ^ r) y = y) →
        2 * m - 2 ≤ 2 * (edgesOutside (factor m (FactorCap.capCenter m)) P.1).card *
          ((2 * (edgesOutside (factor m (FactorCap.capCenter m)) P.1).card + 2) * L - 1) := by
  obtain ⟨P, hK⟩ := hN H
  exact ⟨P, hK, nearHybrid_kept H P.1 hK, (nearHybrid_defects hm H P.1 hK).1,
    (nearHybrid_defects hm H P.1 hK).2,
    fun L hcert ↦ (nearHybrid_certLength hp hm H P.2 hK hcert).1⟩

end RoundRobin.Canonical

end Pairing
