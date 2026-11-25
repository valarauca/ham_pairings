import Repair.Forcing

/-!
# Hamiltonian completions and the partial-core bound (COD-181)

This file formalizes Lemma 3 and Theorem 4 of the COD-168 write-up.

* `card_ham_le` (Lemma 3, upper bound) : for a perfect matching `M` of a type with `2r`
  elements, at most `2^(r-1) (r-1)!` perfect matchings `X` make `X ∪ M` one cycle. The proof
  fixes a vertex `w`, splits by the partner `x = X w`, and contracts the edge `wx` with
  `ham_glue_iff`.
* `twentyfour_mul_le` : `24 · 2^j j! ≤ 11 (2j + 1)!!` for `j ≥ 3`, so two leftover factors
  cost at most `11/12` of the completions once `r = j + 1 ≥ 4`.
* `doubleFactorial_le_pow_mul` : `(2(r + s) - 1)!! ≤ (2(r + s))^s (2r - 1)!!`, that is
  `c_s(m) ≤ (2m)^s`.
* `RoundRobin.Canonical.doubleFactorial_le_zeroCount_add` (Theorem 4) : if a partial matching
  `A` of `V_m` with `s < m` edges blocks every `F_t` with `t ∉ T`, and `r = m - s`, then
  `(2r - 1)!! ≤ Z_m + |T| 2^(r-1) (r-1)!`.
-/

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Lemma 3 (COD-168), upper bound. For a perfect matching `M` of a type with `2r` elements, at
most `2^(r-1) (r-1)!` perfect matchings `X` make `X ∪ M` one cycle. -/
theorem card_ham_le {r : ℕ} (hW : Fintype.card W = 2 * r) (M : PerfectMatching W) :
    (Finset.univ.filter fun X : PerfectMatching W ↦ Ham X M).card ≤
      2 ^ (r - 1) * (r - 1).factorial := by
  induction r generalizing W with
  | zero =>
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, card_eq_doubleFactorial hW]
    simp
  | succ r ih =>
    rcases r with _ | r
    · refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_univ, card_eq_doubleFactorial hW]
      simp
    obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    have hfib : ∀ x ∈ (Finset.univ.erase w).erase (M.mate w),
        (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card ≤
          2 ^ r * r.factorial := by
      intro x hx
      have hxM : x ≠ M.mate w := (Finset.mem_erase.mp hx).1
      have hxw : x ≠ w := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      rcases (Finset.univ.filter fun X : PerfectMatching W ↦
        X.mate w = x ∧ Ham X M).eq_empty_or_nonempty with h | ⟨X₀, hX₀⟩
      · rw [h, Finset.card_empty]
        exact Nat.zero_le _
      have hX₀w : X₀.mate w = x := (Finset.mem_filter.mp hX₀).2.1
      have hX₀x : X₀.mate x = w := by rw [← hX₀w, mate_mate]
      have hmemA : ∀ v, v ∈ (Finset.univ.erase w).erase x ↔ v ≠ x ∧ v ≠ w := fun v ↦ by
        simp
      have hA : ∀ v ∈ (Finset.univ.erase w).erase x, X₀.mate v ∈ (Finset.univ.erase w).erase x := by
        intro v hv
        rw [hmemA] at hv ⊢
        refine ⟨fun h ↦ hv.2 ?_, fun h ↦ hv.1 ?_⟩
        · rw [← X₀.mate_mate v, h, hX₀x]
        · rw [← X₀.mate_mate v, h, hX₀w]
      have hAcard : Fintype.card ((Finset.univ.erase w).erase x) = 2 * (r + 1) := by
        rw [Fintype.card_coe,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxw, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hW]
        omega
      have hC : ¬HasClosedCycle X₀ M ((Finset.univ.erase w).erase x) := by
        rintro ⟨C, ⟨v, hv⟩, hdisj, -, hMC⟩
        have hout : ∀ u ∈ C, u = x ∨ u = w := by
          intro u hu
          have h := Finset.disjoint_left.mp hdisj hu
          rw [hmemA] at h
          tauto
        rcases hout v hv with rfl | rfl
        · rcases hout _ (hMC _ hv) with h | h
          · exact M.mate_ne _ h
          · exact hxM (by rw [← h, mate_mate])
        · rcases hout _ (hMC _ hv) with h | h
          · exact hxM h.symm
          · exact M.mate_ne _ h
      calc (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card
          ≤ ((Finset.univ.filter fun Y : PerfectMatching ((Finset.univ.erase w).erase x) ↦
              Ham Y (contract X₀ M _ hA)).image (glue X₀ _ hA)).card := by
            refine Finset.card_le_card fun X hX ↦ ?_
            obtain ⟨hXw, hXM⟩ := (Finset.mem_filter.mp hX).2
            have hagree : ∀ v ∉ (Finset.univ.erase w).erase x, X.mate v = X₀.mate v := by
              intro v hv
              rw [hmemA, not_and_or, not_not, not_not] at hv
              rcases hv with rfl | rfl
              · rw [hX₀x, ← hXw, mate_mate]
              · rw [hXw, hX₀w]
            have hg := glue_restrict_of_agree X₀ _ hA hagree
            refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hg⟩
            rw [← ham_glue_iff X₀ M _ hA hC, hg]
            exact hXM
        _ ≤ (Finset.univ.filter fun Y : PerfectMatching ((Finset.univ.erase w).erase x) ↦
              Ham Y (contract X₀ M _ hA)).card := Finset.card_image_le
        _ ≤ 2 ^ (r + 1 - 1) * (r + 1 - 1).factorial := ih hAcard _
        _ = 2 ^ r * r.factorial := by simp
    have hcard : ((Finset.univ.erase w).erase (M.mate w)).card = 2 * r + 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨M.mate_ne w, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hW]
      omega
    calc (Finset.univ.filter fun X : PerfectMatching W ↦ Ham X M).card
        ≤ (((Finset.univ.erase w).erase (M.mate w)).biUnion fun x ↦
            Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card := by
          refine Finset.card_le_card fun X hX ↦ ?_
          have hXM := (Finset.mem_filter.mp hX).2
          refine Finset.mem_biUnion.mpr ⟨X.mate w, Finset.mem_erase.mpr ⟨fun h ↦ ?_,
            Finset.mem_erase.mpr ⟨X.mate_ne w, Finset.mem_univ _⟩⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hXM⟩⟩
          obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := ({w, M.mate w} : Finset W)) (t := Finset.univ)
            (by rw [Finset.card_univ, hW]; exact Finset.card_le_two.trans_lt (by omega))
          refine not_ham_of_closed (u := w) (w := u) X M (({w, M.mate w} : Finset W) : Set W)
            (fun v hv ↦ ?_) (fun v hv ↦ ?_) (by simp) (by simpa using hu) hXM
          · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hv ⊢
            rcases hv with rfl | rfl
            · exact Or.inr h
            · exact Or.inl (by rw [← h, mate_mate])
          · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hv ⊢
            rcases hv with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl (mate_mate _ _)
      _ ≤ ∑ x ∈ (Finset.univ.erase w).erase (M.mate w),
            (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ (Finset.univ.erase w).erase (M.mate w), 2 ^ r * r.factorial :=
          Finset.sum_le_sum hfib
      _ = 2 ^ (r + 1 + 1 - 1) * (r + 1 + 1 - 1).factorial := by
          rw [Finset.sum_const, smul_eq_mul, hcard, show r + 1 + 1 - 1 = r + 1 by omega,
            Nat.factorial_succ, pow_succ]
          ring

end PerfectMatching

/-- `24 · 2^j j! ≤ 11 (2j + 1)!!` for `j ≥ 3`. With `r = j + 1 ≥ 4` this says that two
leftover factors, each with at most `2^(r-1) (r-1)!` Hamiltonian completions, cost at most
`11/12` of the `(2r - 1)!!` completions. -/
theorem twentyfour_mul_le {j : ℕ} (hj : 3 ≤ j) :
    24 * (2 ^ j * j.factorial) ≤ 11 * Nat.doubleFactorial (2 * j + 1) := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, Nat.doubleFactorial_add_two,
      Nat.factorial_succ, pow_succ]
    calc 24 * (2 ^ j * 2 * ((j + 1) * j.factorial))
        = 24 * (2 ^ j * j.factorial) * (2 * j + 2) := by ring
      _ ≤ 11 * Nat.doubleFactorial (2 * j + 1) * (2 * j + 3) := Nat.mul_le_mul ih (by omega)
      _ = 11 * ((2 * j + 1 + 2) * Nat.doubleFactorial (2 * j + 1)) := by ring

/-- `(2(r + s) - 1)!! ≤ (2(r + s))^s (2r - 1)!!`. For `m = r + s` this is `c_s(m) ≤ (2m)^s`,
where `(2m - 1)!! = c_s(m) (2r - 1)!!`. -/
theorem doubleFactorial_le_pow_mul (r s : ℕ) :
    Nat.doubleFactorial (2 * (r + s) - 1) ≤
      (2 * (r + s)) ^ s * Nat.doubleFactorial (2 * r - 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (r + (s + 1)) - 1 = 2 * (r + s) + 1 by omega, Nat.doubleFactorial_add_one]
    calc (2 * (r + s) + 1) * Nat.doubleFactorial (2 * (r + s) - 1)
        ≤ (2 * (r + (s + 1))) * ((2 * (r + s)) ^ s * Nat.doubleFactorial (2 * r - 1)) :=
          Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (r + (s + 1))) * ((2 * (r + (s + 1))) ^ s * Nat.doubleFactorial (2 * r - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) s))
      _ = (2 * (r + (s + 1))) ^ (s + 1) * Nat.doubleFactorial (2 * r - 1) := by ring

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- Theorem 4 (COD-168), the partial-core bound. Let `A` be a partial matching of `V_m` with
`s < m` edges and put `r = m - s`. If `A ∪ F_t` has a closed alternating cycle for every `t ∉ T`,
then at least `(2r - 1)!! - |T| 2^(r-1) (r-1)!` zero states contain `A`, so
`(2r - 1)!! ≤ Z_m + |T| 2^(r-1) (r-1)!`. -/
theorem doubleFactorial_le_zeroCount_add {A : Finset (Sym2 (Vertex m))}
    (hA : IsPartialMatching A) (hs : A.card < m) (T : Finset (ZMod (2 * m - 1)))
    (hT : ∀ t ∉ T, Blocks A (factor m t)) :
    Nat.doubleFactorial (2 * (m - A.card) - 1) ≤
      zeroCount m + T.card * (2 ^ (m - A.card - 1) * (m - A.card - 1).factorial) := by
  classical
  have hV : Even (Fintype.card (Vertex m)) := by
    rw [card_vertex]
    exact even_two_mul m
  obtain ⟨P, hU, hPA⟩ := exists_edgesOff_eq hV hA
  have hWcard : (uncovered A).card = 2 * (m - A.card) := by
    have h := two_mul_card_eq hV hA
    have h' := (uncovered A).card_le_univ
    rw [Finset.card_compl, card_vertex] at h
    rw [card_vertex] at h'
    omega
  have hW0 : (uncovered A).Nonempty := by
    rw [← Finset.card_pos, hWcard]
    omega
  have hWc : Fintype.card (uncovered A) = 2 * (m - A.card) := by
    rw [Fintype.card_coe, hWcard]
  set B := T.biUnion fun t ↦ Finset.univ.filter fun X : PerfectMatching (uncovered A) ↦
    Ham X (contract P (factor m t) (uncovered A) hU)
  have hB : B.card ≤ T.card * (2 ^ (m - A.card - 1) * (m - A.card - 1).factorial) := by
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun t _ ↦ card_ham_le hWc _).trans ?_)
    rw [Finset.sum_const, smul_eq_mul]
  have havoid : ∀ X ∉ B, AvoidsContexts (factor m) P (uncovered A) hU X := by
    intro X hX t
    by_cases ht : t ∈ T
    · exact Or.inr fun hham ↦ hX (Finset.mem_biUnion.mpr
        ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hham⟩⟩)
    · exact Or.inl (hasClosedCycle_of_blocks (hPA ▸ edgesOff_subset_edgeSet P _) (hT t ht))
  have hZ : Nat.card {X : PerfectMatching (uncovered A) //
      AvoidsContexts (factor m) P (uncovered A) hU X} ≤ zeroCount m := by
    rw [← Nat.card_congr (zeroStateEquiv (factor m) P (uncovered A) hU hW0), zeroCount,
      ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective (fun Z ↦ ⟨Z.1, Z.2.2⟩)
      fun Z₁ Z₂ h ↦ Subtype.ext (Subtype.mk.inj h)
  have hcompl : (Finset.univ \ B).card ≤ Nat.card {X : PerfectMatching (uncovered A) //
      AvoidsContexts (factor m) P (uncovered A) hU X} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.card_le_card fun X hX ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, havoid X (Finset.mem_sdiff.mp hX).2⟩
  have hsd := Finset.card_univ_sdiff B
  rw [card_eq_doubleFactorial hWc] at hsd
  have hBle : B.card ≤ Fintype.card (PerfectMatching (uncovered A)) := B.card_le_univ
  rw [card_eq_doubleFactorial hWc] at hBle
  omega

end RoundRobin.Canonical

end Pairing
