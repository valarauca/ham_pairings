import Repair.LowerBound.ZeroCore

/-!
# A zero state near a tail agrees with it off one tail edge

Source: `results/struct-lb-extend.md` §1, the reduction of COD-186 Corollary 3 at `K = 1`
(organize-archive b5cb45e).

Let `T` be a tail, a perfect matching of `V_m ∖ G0`, cut out of a perfect matching `Q` of `V_m`.
If `|T ∖ P| ≤ 1`, then `P` agrees with `Q` at every tail vertex off one edge `{u, Q u}` of `T`.

* `exists_agree_of_tailDist_le_one` : the edge `{u, Q u}`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching LowerBound

variable {m : ℕ} [NeZero m]

/-- **The reduction at `K = 1`** (`results/struct-lb-extend.md` §1, COD-186 Corollary 3,
organize-archive b5cb45e). If the tail `T` is `Q` on `V_m ∖ G0` and `|T ∖ P| ≤ 1`, then some tail
vertex `u` has `P v = Q v` for every tail vertex `v ∉ {u, Q u}`. -/
theorem exists_agree_of_tailDist_le_one
    {T : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m))}
    {Q : PerfectMatching (Vertex m)} (hTQ : ∀ u, (T.mate u : Vertex m) = Q.mate u)
    {P : PerfectMatching (Vertex m)} (h : tailDist P T ≤ 1) :
    ∃ u : Vertex m, u ∉ FactorCap.gadget m ∧ ∀ v, v ∉ FactorCap.gadget m → v ≠ u →
      v ≠ Q.mate u → P.mate v = Q.mate v := by
  have h2 := two_mul_tailDist P T
  set D := Finset.univ.filter fun u : ((FactorCap.gadget m)ᶜ : Finset (Vertex m)) ↦
    (T.mate u : Vertex m) ≠ P.mate u with hD
  have hcard : D.card ≤ 2 := by omega
  have hmem : ∀ u, u ∈ D ↔ (T.mate u : Vertex m) ≠ P.mate u := by
    intro u
    simp [hD]
  by_cases hne : D.Nonempty
  · obtain ⟨w, hw⟩ := hne
    refine ⟨w, Finset.mem_compl.mp w.2, fun v hv hvw hvm ↦ ?_⟩
    by_contra hcon
    set v' : ((FactorCap.gadget m)ᶜ : Finset (Vertex m)) := ⟨v, Finset.mem_compl.mpr hv⟩
    have hv' : v' ∈ D := by
      rw [hmem, hTQ]
      exact Ne.symm hcon
    have hw' : T.mate w ∈ D := by
      rw [hmem, mate_mate]
      intro h
      apply (hmem w).mp hw
      rw [h, mate_mate]
    have h3 : 2 < D.card := by
      rw [Finset.two_lt_card]
      refine ⟨w, hw, T.mate w, hw', v', hv', fun h ↦ T.mate_ne w h.symm, fun h ↦ hvw ?_,
        fun h ↦ hvm ?_⟩
      · exact (congrArg Subtype.val h).symm
      · rw [← hTQ]
        exact (congrArg Subtype.val h).symm
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨none, fun h ↦ ?_, fun v hv _ _ ↦ ?_⟩
    · obtain ⟨j, hj⟩ := (mem_gadget_iff none).mp h
      simp at hj
    · have h1 : (⟨v, Finset.mem_compl.mpr hv⟩ :
          ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) ∉ D := by
        rw [hne]
        exact Finset.notMem_empty _
      rw [hmem, not_not, hTQ] at h1
      exact h1.symm

end RoundRobin.Canonical

end Pairing
