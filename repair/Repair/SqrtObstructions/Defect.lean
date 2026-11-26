import Repair.DensityFloor

/-!
# Defect counts against a tail

Vertex-level facts used by the hole lemma (NG-A(b)) and by Theorem C′ (NG-B(b)) of
`results/sqrt-m-obstructions.md`. For perfect matchings `Q, P` of `V`, `defect Q P` is the set of
vertices that `P` and `Q` pair differently, and `|defect Q P| = 2 |P ∖ Q|`.

* `two_mul_tailDist_le` : `2 |T ∖ Q| ≤ 2 |T ∖ P| + |defect Q P|` for a tail `T`.
* `card_defect_le_of_extends` : if `Q` extends the tail `T` of `U`, then
  `|defect Q P| ≤ 2 |T ∖ P| + |V ∖ U|`.
* `card_defect_smul` : relabelling both matchings by `σ` keeps `|defect Q P|`.
* `exists_extends` : every tail extends to a perfect matching of `V` when `|V|` is even.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangle inequality for tail distance (`sqrt-m-obstructions.md` §1.2, proof of NG-A(b)):
`2 |T ∖ Q| ≤ 2 |T ∖ P| + |defect Q P|`. -/
theorem two_mul_tailDist_le (P Q : PerfectMatching V) {U : Finset V} (T : PerfectMatching U) :
    2 * tailDist Q T ≤ 2 * tailDist P T + (defect Q P).card := by
  rw [two_mul_tailDist, two_mul_tailDist]
  calc (Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ Q.mate u).card
      ≤ ((Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u) ∪
          Finset.univ.filter fun u : U ↦ P.mate u ≠ Q.mate u).card := by
        refine Finset.card_le_card fun u hu ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hu ⊢
        by_contra h
        push Not at h
        exact hu (h.1.trans h.2)
    _ ≤ (Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u).card +
          (Finset.univ.filter fun u : U ↦ P.mate u ≠ Q.mate u).card :=
        Finset.card_union_le _ _
    _ ≤ (Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u).card + (defect Q P).card := by
        refine Nat.add_le_add_left (Finset.card_le_card_of_injOn (fun u : U ↦ (u : V))
          (fun u hu ↦ ?_) (fun u _ w _ h ↦ Subtype.ext h)) _
        rw [Finset.mem_coe, Finset.mem_filter] at hu
        exact mem_defect.mpr hu.2

/-- A perfect matching `Q` of `V` extending the tail `T` of `U` differs from `P` on at most
`2 |T ∖ P| + |V ∖ U|` vertices (`sqrt-m-obstructions.md` §1.2, proof of NG-A(b)). -/
theorem card_defect_le_of_extends (Q : PerfectMatching V) {U : Finset V} (T : PerfectMatching U)
    (hQ : ∀ u : U, Q.mate u = T.mate u) (P : PerfectMatching V) :
    (defect Q P).card ≤ 2 * tailDist P T + Uᶜ.card := by
  rw [two_mul_tailDist]
  calc (defect Q P).card
      ≤ ((Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u).map
          (Function.Embedding.subtype _) ∪ Uᶜ).card := by
        refine Finset.card_le_card fun w hw ↦ ?_
        rw [Finset.mem_union, Finset.mem_compl]
        by_cases h : w ∈ U
        · refine Or.inl (Finset.mem_map.mpr ⟨⟨w, h⟩, ?_, rfl⟩)
          rw [Finset.mem_filter, ← hQ ⟨w, h⟩]
          exact ⟨Finset.mem_univ _, fun h' ↦ mem_defect.mp hw h'.symm⟩
        · exact Or.inr h
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans ?_
        rw [Finset.card_map]

/-- Relabelling both matchings by `σ` keeps the size of their defect
(`sqrt-m-obstructions.md` §1.2, proof of NG-A(b)). -/
theorem card_defect_smul (σ : Equiv.Perm V) (Q P : PerfectMatching V) :
    (defect (σ • Q) (σ • P)).card = (defect Q P).card := by
  refine Finset.card_equiv (σ⁻¹ : Equiv.Perm V) fun w ↦ ?_
  simp only [mem_defect, smul_mate, ne_eq, EmbeddingLike.apply_eq_iff_eq]

omit [DecidableEq V] in
/-- Every tail `T` of `U ⊆ V` extends to a perfect matching of `V` when `|V|` is even
(`sqrt-m-obstructions.md` §1.2, proof of NG-A(b)). -/
theorem exists_extends (hV : Even (Fintype.card V)) {U : Finset V} (T : PerfectMatching U) :
    ∃ Q : PerfectMatching V, ∀ u : U, Q.mate u = T.mate u := by
  classical
  obtain ⟨Q, -, hQE⟩ := exists_edgesOff_eq hV (isPartialMatching_tailEdges T)
  rw [uncovered_tailEdges] at hQE
  refine ⟨Q, fun u ↦ ?_⟩
  have hmem : s((u : V), Q.mate u) ∈ tailEdges T :=
    hQE ▸ mem_edgesOff.mpr ⟨u, by simp, rfl⟩
  obtain ⟨u', -, he⟩ := Finset.mem_image.mp hmem
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl : u' = u := Subtype.ext h1
    exact h2.symm
  · have h3 : T.mate u' = u := Subtype.ext h2
    obtain rfl : u' = T.mate u := by rw [← h3, mate_mate]
    exact h1.symm

end PerfectMatching

end Pairing
