import Suppression.Density

/-!
# The layered tail count (COD-173)

Fix a six-vertex gadget `G ⊆ V_m`, put `U = V_m ∖ G` and `M = m - 3`. A perfect matching `P`
of `V_m` has layer `s(P)` when it has `2 s(P)` edges between `G` and `U`, and then its core,
the edges of `P` inside `U`, has `M - s(P)` edges.

* `avoidCount j a = D(j, a)` : the number of perfect matchings of `2j` points that avoid `a`
  fixed disjoint pairs. `card_avoiding` proves that it counts them on every vertex type.
* `ballCount M K s = b_K(s) = ∑_{j = s..K} C(M - s, j - s) D(j, j - s)`.
* `card_tailDist_le_eq_ballCount` (Lemma 1.1) : exactly `b_K(s)` perfect matchings `T` of `U`
  have `|T ∖ P| ≤ K`, when `2s` vertices of `U` have their `P`-partner outside `U`.
  `RoundRobin.Canonical.card_ball_eq` states it on `V_m` with `s = s(P)`.
* `ballCount_succ_le`, `ballCount_antitone` (Lemma 1.2) : `b_K(0) ≥ b_K(1) ≥ b_K(2) ≥ b_K(3)`.
* `RoundRobin.Canonical.layered_count` (Theorem 1) : if `N_m ≤ K`, then
  `(2m - 7)!! ≤ ∑_{s ≤ 3} Z_{m,s}(G) b_K(s)`, with `Z_{m,s}(G) = layerCount m G s`.
* `RoundRobin.Canonical.doubleFactorial_le_zeroCount_mul_ballCount` (Corollary 1.3) : if
  `N_m ≤ K`, then `(2m - 7)!! ≤ Z_m b_K(0)`.
-/

namespace Pairing

/-- `D(j, a)`, the number of perfect matchings of `2j` points that avoid `a` fixed disjoint
pairs, by `D(j, 0) = (2j - 1)!!` and `D(j, a + 1) = D(j, a) - D(j - 1, a)`. -/
def avoidCount : ℕ → ℕ → ℕ
  | j, 0 => Nat.doubleFactorial (2 * j - 1)
  | j, a + 1 => avoidCount j a - avoidCount (j - 1) a

/-- `D(j + 1, a) ≤ D(j, a) + D(j + 1, a + 1)`. -/
theorem avoidCount_le_add (j a : ℕ) :
    avoidCount (j + 1) a ≤ avoidCount j a + avoidCount (j + 1) (a + 1) := by
  rw [avoidCount, Nat.add_sub_cancel]
  omega

/-- `b_K(s) = ∑_{j = s..K} C(M - s, j - s) D(j, j - s)`, the number of tails within `K` edges
of a zero state of layer `s`, for `M = m - 3`. -/
def ballCount (M K s : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc s K, (M - s).choose (j - s) * avoidCount j (j - s)

/-- `b_K(s) = ∑_{i < K + 1 - s} C(M - s, i) D(s + i, i)`. -/
theorem ballCount_eq_sum_range (M K s : ℕ) :
    ballCount M K s =
      ∑ i ∈ Finset.range (K + 1 - s), (M - s).choose i * avoidCount (s + i) i := by
  rw [ballCount, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp

/-- Lemma 1.2 (COD-167), one step: `b_K(s + 1) ≤ b_K(s)` for `s + 1 ≤ M`. -/
theorem ballCount_succ_le {M K s : ℕ} (h : s + 1 ≤ M) :
    ballCount M K (s + 1) ≤ ballCount M K s := by
  rw [ballCount_eq_sum_range, ballCount_eq_sum_range]
  obtain ⟨N, hN⟩ : ∃ N, M - s = N + 1 := ⟨M - s - 1, by omega⟩
  rw [hN, show M - (s + 1) = N by omega]
  rcases Nat.lt_or_ge K s with hK | hK
  · rw [show K + 1 - (s + 1) = 0 by omega]
    simp
  obtain ⟨L, hL⟩ : ∃ L, K + 1 - s = L + 1 := ⟨K - s, by omega⟩
  rw [hL, show K + 1 - (s + 1) = L by omega]
  calc ∑ i ∈ Finset.range L, N.choose i * avoidCount (s + 1 + i) i
      ≤ ∑ i ∈ Finset.range L, (N.choose i * avoidCount (s + i + 1) (i + 1) +
          N.choose i * avoidCount (s + i) i) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [← Nat.mul_add, show s + 1 + i = s + i + 1 by omega, add_comm (avoidCount _ (i + 1))]
        exact Nat.mul_le_mul_left _ (avoidCount_le_add (s + i) i)
    _ ≤ ∑ i ∈ Finset.range L, N.choose i * avoidCount (s + i + 1) (i + 1) +
          ∑ i ∈ Finset.range (L + 1), N.choose i * avoidCount (s + i) i := by
        rw [Finset.sum_add_distrib]
        exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset
          (Finset.range_subset_range.mpr (Nat.le_succ L))) _
    _ = ∑ i ∈ Finset.range (L + 1), (N + 1).choose i * avoidCount (s + i) i := by
        rw [Finset.sum_range_succ' _ L, Finset.sum_range_succ' _ L]
        simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right,
          ← add_assoc]

/-- `b_K(s) ≤ b_K(0)` for `s ≤ M`. -/
theorem ballCount_le_zero {M K s : ℕ} (h : s ≤ M) : ballCount M K s ≤ ballCount M K 0 := by
  induction s with
  | zero => exact le_rfl
  | succ s ih => exact (ballCount_succ_le h).trans (ih (by omega))

/-- Lemma 1.2 (COD-167): `b_K(0) ≥ b_K(1) ≥ b_K(2) ≥ b_K(3)` for `3 ≤ M`. -/
theorem ballCount_antitone {M K : ℕ} (h : 3 ≤ M) :
    ballCount M K 3 ≤ ballCount M K 2 ∧ ballCount M K 2 ≤ ballCount M K 1 ∧
      ballCount M K 1 ≤ ballCount M K 0 :=
  ⟨ballCount_succ_le h, ballCount_succ_le (by omega), ballCount_succ_le (by omega)⟩

namespace PerfectMatching

section Avoid

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The perfect matchings `X` of `W` that share no edge with `Q` at a vertex of `A`. -/
def avoiding (Q : PerfectMatching W) (A : Finset W) : Finset (PerfectMatching W) :=
  Finset.univ.filter fun X ↦ ∀ w ∈ A, X.mate w ≠ Q.mate w

/-- `X` avoids `Q` on `A` iff `X.mate w ≠ Q.mate w` for every `w ∈ A`. -/
theorem mem_avoiding {Q X : PerfectMatching W} {A : Finset W} :
    X ∈ avoiding Q A ↔ ∀ w ∈ A, X.mate w ≠ Q.mate w := by
  simp [avoiding]

/-- If `A` is a union of `a` edges of `Q` and `|W| = 2j`, then exactly `D(j, a)` perfect
matchings of `W` share no edge with `Q` inside `A`. -/
theorem card_avoiding {j a : ℕ} (Q : PerfectMatching W) (A : Finset W)
    (hA : ∀ w ∈ A, Q.mate w ∈ A) (hW : Fintype.card W = 2 * j) (hAa : A.card = 2 * a) :
    (avoiding Q A).card = avoidCount j a := by
  induction a generalizing W j with
  | zero =>
    obtain rfl : A = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [avoidCount, ← card_eq_doubleFactorial hW, ← Finset.card_univ]
    congr 1
    ext X
    simp [avoiding]
  | succ a ih =>
    obtain ⟨v, hv⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    have hvv : Q.mate v ≠ v := Q.mate_ne v
    have hne : ∀ w, w ≠ v → w ≠ Q.mate v → Q.mate w ≠ v ∧ Q.mate w ≠ Q.mate v := by
      intro w h1 h2
      refine ⟨fun h ↦ h2 ?_, fun h ↦ h1 (Q.mate.injective h)⟩
      rw [← h, mate_mate]
    set A' := (A.erase v).erase (Q.mate v) with hA'def
    have hmemA' : ∀ w, w ∈ A' ↔ w ≠ Q.mate v ∧ w ≠ v ∧ w ∈ A := by
      intro w
      simp [hA'def, Finset.mem_erase]
    have hA' : ∀ w ∈ A', Q.mate w ∈ A' := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := (hmemA' w).mp hw
      obtain ⟨h4, h5⟩ := hne w h2 h1
      exact (hmemA' _).mpr ⟨h5, h4, hA w h3⟩
    have hA'a : A'.card = 2 * a := by
      rw [hA'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvv, hA v hv⟩),
        Finset.card_erase_of_mem hv, hAa]
      omega
    set B : Finset W := ({v, Q.mate v} : Finset W)ᶜ with hBdef
    have hmemB : ∀ w, w ∈ B ↔ w ≠ v ∧ w ≠ Q.mate v := by
      intro w
      simp [hBdef]
    have hB : ∀ w ∈ B, Q.mate w ∈ B := by
      intro w hw
      obtain ⟨h1, h2⟩ := (hmemB w).mp hw
      obtain ⟨h4, h5⟩ := hne w h1 h2
      exact (hmemB _).mpr ⟨h4, h5⟩
    have hBj : Fintype.card B = 2 * (j - 1) := by
      have := A.card_le_univ
      rw [Fintype.card_coe, hBdef, Finset.card_compl, Finset.card_pair hvv.symm, hW]
      omega
    set A'' : Finset B := A'.subtype (· ∈ B) with hA''def
    have hA'' : ∀ w ∈ A'', (restrict Q B hB).mate w ∈ A'' := by
      intro w hw
      rw [Finset.mem_subtype] at hw ⊢
      exact hA' _ hw
    have hA''a : A''.card = 2 * a := by
      rw [hA''def, Finset.card_subtype, Finset.filter_true_of_mem, hA'a]
      intro w hw
      obtain ⟨h1, h2, -⟩ := (hmemA' w).mp hw
      exact (hmemB w).mpr ⟨h2, h1⟩
    have hsplit : (avoiding Q A').card =
        ((avoiding Q A').filter fun X ↦ X.mate v = Q.mate v).card + (avoiding Q A).card := by
      rw [← Finset.card_filter_add_card_filter_not (s := avoiding Q A')
        (fun X ↦ X.mate v = Q.mate v)]
      congr 2
      ext X
      simp only [Finset.mem_filter, mem_avoiding]
      constructor
      · rintro ⟨h, hXv⟩ w hw
        by_cases hw1 : w = v
        · rw [hw1]
          exact hXv
        by_cases hw2 : w = Q.mate v
        · rw [hw2, mate_mate]
          intro h'
          apply hXv
          have h'' := congrArg X.mate h'
          rw [mate_mate] at h''
          exact h''.symm
        exact h w ((hmemA' w).mpr ⟨hw2, hw1, hw⟩)
      · intro h
        exact ⟨fun w hw ↦ h w ((hmemA' w).mp hw).2.2, h v hv⟩
    have hglue : ((avoiding Q A').filter fun X ↦ X.mate v = Q.mate v).card =
        (avoiding (restrict Q B hB) A'').card := by
      symm
      refine Finset.card_bij (fun Y _ ↦ glue Q B hB Y) (fun Y hY ↦ ?_)
        (fun Y₁ _ Y₂ _ h ↦ ?_) (fun X hX ↦ ?_)
      · rw [mem_avoiding] at hY
        refine Finset.mem_filter.mpr ⟨mem_avoiding.mpr fun w hw ↦ ?_,
          glue_mate_of_notMem Q B hB Y (by simp [hmemB])⟩
        have hwB : w ∈ B := by
          obtain ⟨h1, h2, -⟩ := (hmemA' w).mp hw
          exact (hmemB w).mpr ⟨h2, h1⟩
        rw [glue_mate_of_mem Q B hB Y hwB]
        intro h
        exact hY ⟨w, hwB⟩ (Finset.mem_subtype.mpr hw) (Subtype.ext h)
      · refine PerfectMatching.ext (Equiv.ext fun b ↦ Subtype.ext ?_)
        rw [← glue_mate_coe Q B hB Y₁, ← glue_mate_coe Q B hB Y₂, h]
      · obtain ⟨hXA, hXv⟩ := Finset.mem_filter.mp hX
        have hagree : ∀ w ∉ B, X.mate w = Q.mate w := by
          intro w hw
          rw [hmemB, not_and_or, not_not, not_not] at hw
          rcases hw with rfl | rfl
          · exact hXv
          · rw [mate_mate, ← hXv, mate_mate]
        refine ⟨restrict X B (mate_mem_of_agree Q B hB hagree), mem_avoiding.mpr fun w hw h ↦ ?_,
          glue_restrict_of_agree Q B hB hagree⟩
        exact mem_avoiding.mp hXA w (Finset.mem_subtype.mp hw) (congrArg Subtype.val h)
    rw [ih Q A' hA' hW hA'a, hglue, ih (restrict Q B hB) A'' hA'' hBj hA''a] at hsplit
    rw [avoidCount]
    omega

/-- If `B` is a union of `n` edges of `Q`, exactly `C(n, i)` unions of `i` edges of `Q` lie
inside `B`. -/
theorem card_closed_subset (Q : PerfectMatching W) {B : Finset W} (hB : ∀ w ∈ B, Q.mate w ∈ B)
    {n : ℕ} (hBn : B.card = 2 * n) (i : ℕ) :
    (B.powerset.filter fun D ↦ (∀ w ∈ D, Q.mate w ∈ D) ∧ D.card = 2 * i).card = n.choose i := by
  have hQ : (B.image fun w ↦ s(w, Q.mate w)).card = n := by
    have h := two_mul_card_image_mate Q B hB
    omega
  rw [← hQ, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun D _ ↦ D.image fun w ↦ s(w, Q.mate w)) (fun D hD ↦ ?_)
    (fun D₁ hD₁ D₂ hD₂ h ↦ ?_) (fun S hS ↦ ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD
    refine Finset.mem_powersetCard.mpr ⟨Finset.image_subset_image hD.1, ?_⟩
    have h := two_mul_card_image_mate Q D hD.2.1
    omega
  · have h₁ := (Finset.mem_filter.mp hD₁).2.1
    have h₂ := (Finset.mem_filter.mp hD₂).2.1
    ext w
    constructor
    · intro hw
      exact mem_of_mem_image_mate Q h₂ (h ▸ Finset.mem_image_of_mem _ hw)
    · intro hw
      exact mem_of_mem_image_mate Q h₁ (h.symm ▸ Finset.mem_image_of_mem _ hw)
  · obtain ⟨hSB, hSi⟩ := Finset.mem_powersetCard.mp hS
    set D := B.filter fun w ↦ s(w, Q.mate w) ∈ S with hDdef
    have hD : ∀ w ∈ D, Q.mate w ∈ D := by
      intro w hw
      rw [hDdef, Finset.mem_filter] at hw ⊢
      exact ⟨hB w hw.1, by rw [mate_mate, Sym2.eq_swap]; exact hw.2⟩
    have himg : (D.image fun w ↦ s(w, Q.mate w)) = S := by
      ext e
      constructor
      · intro he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hw).2
      · intro he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hSB he)
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, he⟩)
    refine ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hD, ?_⟩,
      himg⟩
    have h := two_mul_card_image_mate Q D hD
    rw [himg, hSi] at h
    omega

end Avoid

section Ball

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Lemma 1.1 (COD-167), the exact ball. Let `P` be a perfect matching of `V` and `|U| = 2M`,
and let `2s` vertices of `U` have their `P`-partner outside `U`, so that the core of `P`, its
edges inside `U`, has `M - s` edges. Then exactly `b_K(s)` perfect matchings `T` of `U` have
`|T ∖ P| ≤ K`. -/
theorem card_tailDist_le_eq_ballCount (P : PerfectMatching V) {U : Finset V} {M s : ℕ}
    (hU : U.card = 2 * M) (hF : (Finset.univ.filter fun u : U ↦ P.mate u ∉ U).card = 2 * s)
    (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T ≤ K).card =
      ballCount M K s := by
  obtain ⟨P', hP'⟩ := exists_extend_restrict P U ⟨M, by omega⟩
  set F := Finset.univ.filter fun u : U ↦ P.mate u ∉ U with hFdef
  have hmemF : ∀ u, u ∈ F ↔ P.mate u ∉ U := fun u ↦ by simp [hFdef]
  have hF' : ∀ u ∈ F, P'.mate u ∈ F := by
    intro u hu
    rw [hmemF] at hu ⊢
    intro h
    have h' := hP' _ h
    rw [mate_mate] at h'
    apply hu
    rw [h', mate_mate]
    exact (P'.mate u).2
  set Δ : PerfectMatching U → Finset U :=
    fun T ↦ Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u with hΔdef
  have hmemΔ : ∀ T u, u ∈ Δ T ↔ (T.mate u : V) ≠ P.mate u := fun T u ↦ by simp [hΔdef]
  have hΔcard : ∀ T, (Δ T).card = 2 * tailDist P T := fun T ↦ (two_mul_tailDist P T).symm
  have hFΔ : ∀ T, F ⊆ Δ T := by
    intro T u hu
    rw [hmemF] at hu
    rw [hmemΔ]
    intro h
    exact hu (h ▸ (T.mate u).2)
  have hsΔ : ∀ T : PerfectMatching U, s ≤ tailDist P T := by
    intro T
    have h := Finset.card_le_card (hFΔ T)
    rw [hΔcard, hF] at h
    omega
  have hΔT : ∀ T, ∀ u ∈ Δ T, T.mate u ∈ Δ T := by
    intro T u hu
    rw [hmemΔ] at hu ⊢
    intro h
    apply hu
    simp only [mate_mate] at h
    have h' := congrArg P.mate h
    simp only [mate_mate] at h'
    exact h'.symm
  have hΔP' : ∀ T, ∀ u ∈ Δ T, P'.mate u ∈ Δ T := by
    intro T u hu
    by_cases huF : u ∈ F
    · exact hFΔ T (hF' u huF)
    rw [hmemF, not_not] at huF
    rw [hmemΔ] at hu ⊢
    have h1 := hP' u huF
    intro h
    rw [h1, mate_mate] at h
    have h2 := congrArg T.mate (Subtype.ext h : T.mate (P'.mate u) = u)
    rw [mate_mate] at h2
    apply hu
    rw [← h2, h1]
  have hfib : ∀ D : Finset U, ∀ hD : ∀ u ∈ D, P'.mate u ∈ D, F ⊆ D → ∀ j, D.card = 2 * j →
      (Finset.univ.filter fun T : PerfectMatching U ↦ Δ T = D).card = avoidCount j (j - s) := by
    intro D hD hFD j hDj
    have hsj : s ≤ j := by
      have := Finset.card_le_card hFD
      omega
    set A := (D \ F).subtype (· ∈ D) with hAdef
    have hA : ∀ w ∈ A, (restrict P' D hD).mate w ∈ A := by
      intro w hw
      rw [hAdef, Finset.mem_subtype, Finset.mem_sdiff] at hw ⊢
      change P'.mate (w : U) ∈ D ∧ P'.mate (w : U) ∉ F
      exact ⟨hD _ hw.1, fun h ↦ hw.2 (by simpa using hF' _ h)⟩
    have hAcard : A.card = 2 * (j - s) := by
      rw [hAdef, Finset.card_subtype,
        Finset.filter_true_of_mem fun w hw ↦ (Finset.mem_sdiff.mp hw).1,
        Finset.card_sdiff_of_subset hFD, hDj, hF]
      omega
    rw [← card_avoiding (restrict P' D hD) A hA (by rw [Fintype.card_coe, hDj]) hAcard]
    symm
    refine Finset.card_bij (fun X _ ↦ glue P' D hD X) (fun X hX ↦ ?_)
      (fun X₁ _ X₂ _ h ↦ ?_) (fun T hT ↦ ?_)
    · rw [mem_avoiding] at hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext u
      constructor
      · intro hu
        by_contra huD
        rw [hmemΔ, glue_mate_of_notMem P' D hD X huD] at hu
        have huF : u ∉ F := fun h ↦ huD (hFD h)
        rw [hmemF, not_not] at huF
        exact hu (hP' u huF)
      · intro huD
        by_cases huF : u ∈ F
        · exact hFΔ _ huF
        rw [hmemΔ, glue_mate_of_mem P' D hD X huD]
        intro h
        rw [hmemF, not_not] at huF
        refine hX ⟨u, huD⟩ (Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨huD, ?_⟩))
          (Subtype.ext (Subtype.ext ?_))
        · rw [hmemF, not_not]
          exact huF
        · rw [h, ← hP' u huF]
          rfl
    · refine PerfectMatching.ext (Equiv.ext fun b ↦ Subtype.ext ?_)
      rw [← glue_mate_coe P' D hD X₁, ← glue_mate_coe P' D hD X₂, h]
    · have hTD : Δ T = D := (Finset.mem_filter.mp hT).2
      have hagree : ∀ u ∉ D, T.mate u = P'.mate u := by
        intro u huD
        have h1 : u ∉ Δ T := hTD ▸ huD
        rw [hmemΔ, not_not] at h1
        have huF : u ∉ F := fun h ↦ huD (hFD h)
        rw [hmemF, not_not] at huF
        exact Subtype.ext (h1.trans (hP' u huF).symm)
      refine ⟨restrict T D (mate_mem_of_agree P' D hD hagree), mem_avoiding.mpr fun w hw h ↦ ?_,
        glue_restrict_of_agree P' D hD hagree⟩
      rw [hAdef, Finset.mem_subtype, Finset.mem_sdiff, hmemF, not_not] at hw
      have hwΔ : (w : U) ∈ Δ T := hTD ▸ hw.1
      rw [hmemΔ] at hwΔ
      apply hwΔ
      rw [← hP' _ hw.2]
      exact congrArg (fun x : D ↦ ((x : U) : V)) h
  have hcount : ∀ j, s ≤ j → (Finset.univ.filter fun D : Finset U ↦
      (∀ u ∈ D, P'.mate u ∈ D) ∧ F ⊆ D ∧ D.card = 2 * j).card = (M - s).choose (j - s) := by
    intro j hsj
    have hFc : ∀ u ∈ Fᶜ, P'.mate u ∈ Fᶜ := by
      intro u hu
      rw [Finset.mem_compl] at hu ⊢
      intro h
      exact hu (by simpa using hF' _ h)
    have hFcard : Fᶜ.card = 2 * (M - s) := by
      have := F.card_le_univ
      rw [Fintype.card_coe, hU, hF] at this
      rw [Finset.card_compl, Fintype.card_coe, hU, hF]
      omega
    rw [← card_closed_subset P' hFc hFcard (j - s)]
    refine Finset.card_bij (fun D _ ↦ D \ F) (fun D hD ↦ ?_) (fun D₁ hD₁ D₂ hD₂ h ↦ ?_)
      (fun E hE ↦ ?_)
    · obtain ⟨hcl, hFD, hcard⟩ := (Finset.mem_filter.mp hD).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun u hu ↦
        Finset.mem_compl.mpr (Finset.mem_sdiff.mp hu).2, fun u hu ↦ ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hu
        exact Finset.mem_sdiff.mpr ⟨hcl u h1, fun h ↦ h2 (by simpa using hF' _ h)⟩
      · rw [Finset.card_sdiff_of_subset hFD, hcard, hF]
        omega
    · rw [← Finset.sdiff_union_of_subset (Finset.mem_filter.mp hD₁).2.2.1,
        ← Finset.sdiff_union_of_subset (Finset.mem_filter.mp hD₂).2.2.1]
      exact congrArg (· ∪ F) h
    · obtain ⟨hsub, hcl, hcard⟩ := Finset.mem_filter.mp hE
      have hdisj : Disjoint E F := Finset.disjoint_left.mpr fun u hu huF ↦
        Finset.mem_compl.mp (Finset.mem_powerset.mp hsub hu) huF
      refine ⟨E ∪ F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu ↦ ?_,
        Finset.subset_union_right, ?_⟩, Finset.union_sdiff_cancel_right hdisj⟩
      · rcases Finset.mem_union.mp hu with h | h
        · exact Finset.mem_union_left _ (hcl u h)
        · exact Finset.mem_union_right _ (hF' u h)
      · rw [Finset.card_union_of_disjoint hdisj, hcard, hF]
        omega
  have hj : ∀ j, s ≤ j → (Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T = j).card =
      (M - s).choose (j - s) * avoidCount j (j - s) := by
    intro j hsj
    have hmaps : ∀ T ∈ Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T = j,
        Δ T ∈ Finset.univ.filter fun D : Finset U ↦
          (∀ u ∈ D, P'.mate u ∈ D) ∧ F ⊆ D ∧ D.card = 2 * j := by
      intro T hT
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hΔP' T, hFΔ T, ?_⟩
      rw [hΔcard, (Finset.mem_filter.mp hT).2]
    rw [Finset.card_eq_sum_card_fiberwise hmaps, ← hcount j hsj]
    refine Finset.sum_const_nat fun D hD ↦ ?_
    obtain ⟨hcl, hFD, hcard⟩ := (Finset.mem_filter.mp hD).2
    rw [← hfib D hcl hFD j hcard, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun T _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    have := hΔcard T
    rw [h, hcard] at this
    omega
  have hmapsK : ∀ T ∈ Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T ≤ K,
      tailDist P T ∈ Finset.Icc s K := fun T hT ↦
    Finset.mem_Icc.mpr ⟨hsΔ T, (Finset.mem_filter.mp hT).2⟩
  rw [ballCount, Finset.card_eq_sum_card_fiberwise hmapsK]
  refine Finset.sum_congr rfl fun j hj' ↦ ?_
  obtain ⟨hsj, hjK⟩ := Finset.mem_Icc.mp hj'
  rw [← hj j hsj, Finset.filter_filter]
  congr 1
  exact Finset.filter_congr fun T _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hjK, h⟩⟩

omit [Fintype V] in
/-- The layer `s(P)` of a perfect matching `P` of `V` relative to the gadget `G ⊆ V`: `P` has
`2 s(P)` edges between `G` and `V ∖ G`. -/
def layer (G : Finset V) (P : PerfectMatching V) : ℕ :=
  (G.filter fun v ↦ P.mate v ∉ G).card / 2

omit [Fintype V] in
/-- For `|G|` even, `P` has exactly `2 s(P)` edges between `G` and `V ∖ G`. -/
theorem two_mul_layer [Finite V] (G : Finset V) (P : PerfectMatching V) (hG : Even G.card) :
    2 * layer G P = (G.filter fun v ↦ P.mate v ∉ G).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := G) (fun v ↦ P.mate v ∈ G)
  have h2 := two_mul_card_image_mate P (G.filter fun v ↦ P.mate v ∈ G) fun v hv ↦ by
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨hv.2, by rw [mate_mate]; exact hv.1⟩
  obtain ⟨k, hk⟩ := hG
  rw [layer]
  omega

/-- The vertices of `V ∖ G` whose `P`-partner lies in `G` are as many as the edges of `P` between
`G` and `V ∖ G`. -/
theorem card_compl_matched (G : Finset V) (P : PerfectMatching V) :
    (Finset.univ.filter fun u : (Gᶜ : Finset V) ↦ P.mate u ∉ Gᶜ).card =
      (G.filter fun v ↦ P.mate v ∉ G).card := by
  refine Finset.card_bij (fun u _ ↦ P.mate u) (fun u hu ↦ ?_)
    (fun u₁ _ u₂ _ h ↦ Subtype.ext (P.mate.injective h)) (fun v hv ↦ ?_)
  · rw [Finset.mem_filter, Finset.mem_compl, not_not] at hu
    rw [Finset.mem_filter, mate_mate]
    exact ⟨hu.2, Finset.mem_compl.mp u.2⟩
  · rw [Finset.mem_filter] at hv
    refine ⟨⟨P.mate v, Finset.mem_compl.mpr hv.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      mate_mate P v⟩
    change P.mate (P.mate v) ∉ Gᶜ
    rw [mate_mate, Finset.mem_compl, not_not]
    exact hv.1

/-- `s(P) ≤ M` when `|V ∖ G| = 2M`. -/
theorem layer_le (G : Finset V) (P : PerfectMatching V) {M : ℕ} (hU : Gᶜ.card = 2 * M) :
    layer G P ≤ M := by
  have h := (Finset.univ.filter fun u : (Gᶜ : Finset V) ↦ P.mate u ∉ Gᶜ).card_le_univ
  rw [card_compl_matched, Fintype.card_coe, hU] at h
  rw [layer]
  omega

/-- Lemma 1.1 (COD-167) for a gadget `G` with `|G|` even and `|V ∖ G| = 2M`: exactly
`b_K(s(P))` perfect matchings `T` of `V ∖ G` have `|T ∖ P| ≤ K`. -/
theorem card_tailDist_le_eq_ballCount_layer (P : PerfectMatching V) {G : Finset V} {M : ℕ}
    (hU : Gᶜ.card = 2 * M) (hG : Even G.card) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset V) ↦ tailDist P T ≤ K).card =
      ballCount M K (layer G P) :=
  card_tailDist_le_eq_ballCount P hU (by rw [card_compl_matched, two_mul_layer G P hG]) K

end Ball

end PerfectMatching

/-- Covering sum: if every `a` is within `K` of some `b`, then
`|α| ≤ ∑_b #{a | d a b ≤ K}`. -/
theorem card_le_sum_of_cover {α β : Type*} [Fintype α] [Fintype β] (d : α → β → ℕ) (K : ℕ)
    (hcover : ∀ a, ∃ b, d a b ≤ K) :
    Fintype.card α ≤ ∑ b, (Finset.univ.filter fun a ↦ d a b ≤ K).card := by
  classical
  calc Fintype.card α = (Finset.univ : Finset α).card := rfl
    _ ≤ (Finset.univ.biUnion fun b ↦ Finset.univ.filter fun a ↦ d a b ≤ K).card := by
      refine Finset.card_le_card fun a _ ↦ ?_
      obtain ⟨b, hb⟩ := hcover a
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, by simpa using hb⟩
    _ ≤ ∑ b, (Finset.univ.filter fun a ↦ d a b ≤ K).card := Finset.card_biUnion_le

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `Z_{m,s}(G)`, the number of zero states of layer `s` relative to the gadget `G`. -/
def layerCount (m : ℕ) [NeZero m] (G : Finset (Vertex m)) (s : ℕ) : ℕ :=
  (Finset.univ.filter fun P : ZeroState m ↦ layer G P.1 = s).card

omit [NeZero m] in
/-- A perfect matching of `V_m` has layer at most `3` relative to a six-vertex gadget. -/
theorem layer_le_three {G : Finset (Vertex m)} (hG : G.card = 6) (P : PerfectMatching (Vertex m)) :
    layer G P ≤ 3 := by
  have h := G.card_filter_le fun v ↦ P.mate v ∉ G
  rw [layer]
  omega

/-- Lemma 1.1 (COD-167) on `V_m`: for a six-vertex gadget `G`, exactly `b_K(s(P))` tails are
within `K` edges of the perfect matching `P`. -/
theorem card_ball_eq {G : Finset (Vertex m)} (hG : G.card = 6) (P : PerfectMatching (Vertex m))
    (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
      tailDist P T ≤ K).card = ballCount (m - 3) K (layer G P) :=
  card_tailDist_le_eq_ballCount_layer P (card_compl_gadget hG).2 (by rw [hG]; exact ⟨3, rfl⟩) K

/-- If `N_m ≤ K`, then `(2m - 7)!! ≤ ∑_P b_K(s(P))` over the zero states `P`. -/
theorem doubleFactorial_le_sum_ballCount {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ}
    (hK : RepairBound m G K) :
    Nat.doubleFactorial (2 * m - 7) ≤ ∑ P : ZeroState m, ballCount (m - 3) K (layer G P.1) := by
  rw [← card_tail hG]
  refine (card_le_sum_of_cover
    (fun (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (P : ZeroState m) ↦ tailDist P.1 T)
    K hK).trans_eq (Finset.sum_congr rfl fun P _ ↦ card_ball_eq hG P.1 K)

/-- Theorem 1 (COD-167), the layered tail count, for every `m` and `K`. If every tail is within
`K` edges of a zero state, then `(2m - 7)!! ≤ ∑_{s ≤ 3} Z_{m,s}(G) b_K(s)`. -/
theorem layered_count {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ}
    (hK : RepairBound m G K) :
    Nat.doubleFactorial (2 * m - 7) ≤
      ∑ s ∈ Finset.range 4, layerCount m G s * ballCount (m - 3) K s := by
  refine (doubleFactorial_le_sum_ballCount hG hK).trans_eq ?_
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range 4)
    (g := fun P : ZeroState m ↦ layer G P.1)
    fun P _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (layer_le_three hG P.1))]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [layerCount]
  exact Finset.sum_const_nat fun P hP ↦ by rw [(Finset.mem_filter.mp hP).2]

/-- Corollary 1.3 (COD-167), for every `m` and `K`. If every tail is within `K` edges of a zero
state, then `(2m - 7)!! ≤ Z_m b_K(0)`. -/
theorem doubleFactorial_le_zeroCount_mul_ballCount {G : Finset (Vertex m)} (hG : G.card = 6)
    {K : ℕ} (hK : RepairBound m G K) :
    Nat.doubleFactorial (2 * m - 7) ≤ zeroCount m * ballCount (m - 3) K 0 := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  calc Nat.doubleFactorial (2 * m - 7)
      ≤ ∑ P : ZeroState m, ballCount (m - 3) K (layer G P.1) :=
        doubleFactorial_le_sum_ballCount hG hK
    _ ≤ ∑ _P : ZeroState m, ballCount (m - 3) K 0 :=
        Finset.sum_le_sum fun P _ ↦ ballCount_le_zero (layer_le G P.1 hU)
    _ = zeroCount m * ballCount (m - 3) K 0 := by simp [zeroCount]

end RoundRobin.Canonical

end Pairing
