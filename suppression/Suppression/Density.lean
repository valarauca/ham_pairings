import Mathlib.Basic.Real.Basic
import Suppression.Canonical

/-!
# A uniform repair bound forces polynomial zero-state density (COD-155)

Fix a six-vertex gadget `G ⊆ V_m` and put `U = V_m ∖ G`, so `|U| = 2m - 6`. A tail is a perfect
matching `T` of `U`, and `tailDist P T = |T ∖ P|` counts the edges of `T` that are not edges of
the perfect matching `P` of `V_m`. `RepairBound m G K` says that every tail lies within `K`
edges of some zero state, which is `N_m ≤ K`.

* `card_le_card_mul_of_cover` : if every `a` is within `K` of some `b`, then
  `|α| ≤ |β| · max_b #{a | d a b ≤ K}`.
* `card_defect_le` : for a perfect matching `Q` of a type with `2n` elements, at most
  `∑_{j ≤ K} C(n, j)(2j - 1)!!` perfect matchings `T` differ from `Q` on at most `2K`
  vertices.
* `card_tailDist_le` : for a perfect matching `P` of `V` and `|U| = 2n`, at most
  `∑_{j ≤ K} C(n, j)(2j - 1)!!` perfect matchings `T` of `U` have `|T ∖ P| ≤ K`.
* `sum_choose_mul_doubleFactorial_le` : `∑_{j ≤ K} C(n, j)(2j - 1)!! ≤ (K + 1)(2N)^K` for
  `0 < N` and `n ≤ N`.
* `RoundRobin.Canonical.card_tail` : there are `(2m - 7)!!` tails.
* `RoundRobin.Canonical.repair_count` : if `N_m ≤ K`, then
  `(2m - 7)!! ≤ Z_m ∑_{j ≤ K} C(m - 3, j)(2j - 1)!! ≤ Z_m (K + 1)(2m)^K`.
* `RoundRobin.Canonical.density_ge` : if `N_m ≤ K`, then
  `q_m = Z_m / (2m - 1)!! ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`.
-/

namespace Pairing

/-- Covering count: if every `a` is within `K` of some `b`, and each `b` has at most `M` such
`a`, then `|α| ≤ |β| · M`. -/
theorem card_le_card_mul_of_cover {α β : Type*} [Fintype α] [Fintype β]
    (d : α → β → ℕ) (K M : ℕ) (hcover : ∀ a, ∃ b, d a b ≤ K)
    (hball : ∀ b, (Finset.univ.filter fun a ↦ d a b ≤ K).card ≤ M) :
    Fintype.card α ≤ Fintype.card β * M := by
  classical
  calc Fintype.card α = (Finset.univ : Finset α).card := rfl
    _ ≤ (Finset.univ.biUnion fun b ↦ Finset.univ.filter fun a ↦ d a b ≤ K).card := by
      refine Finset.card_le_card fun a _ ↦ ?_
      obtain ⟨b, hb⟩ := hcover a
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, by simpa using hb⟩
    _ ≤ ∑ b, (Finset.univ.filter fun a ↦ d a b ≤ K).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : β, M := Finset.sum_le_sum fun b _ ↦ hball b
    _ = Fintype.card β * M := by simp

/-- `(2j - 1)!! ≤ 2^j j!`. -/
theorem doubleFactorial_two_mul_sub_one_le (j : ℕ) :
    Nat.doubleFactorial (2 * j - 1) ≤ 2 ^ j * j.factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.doubleFactorial_add_one, pow_succ,
      Nat.factorial_succ]
    calc (2 * j + 1) * Nat.doubleFactorial (2 * j - 1) ≤ (2 * j + 2) * (2 ^ j * j.factorial) :=
          Nat.mul_le_mul (by omega) ih
      _ = 2 ^ j * 2 * ((j + 1) * j.factorial) := by ring

/-- `C(n, j)(2j - 1)!! ≤ (2n)^j`. -/
theorem choose_mul_doubleFactorial_le (n j : ℕ) :
    n.choose j * Nat.doubleFactorial (2 * j - 1) ≤ (2 * n) ^ j := by
  calc n.choose j * Nat.doubleFactorial (2 * j - 1) ≤ n.choose j * (2 ^ j * j.factorial) :=
        Nat.mul_le_mul_left _ (doubleFactorial_two_mul_sub_one_le j)
    _ = 2 ^ j * n.descFactorial j := by rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
    _ ≤ 2 ^ j * n ^ j := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow n j)
    _ = (2 * n) ^ j := (mul_pow 2 n j).symm

/-- `∑_{j ≤ K} C(n, j)(2j - 1)!! ≤ (K + 1)(2N)^K` for `0 < N` and `n ≤ N`. -/
theorem sum_choose_mul_doubleFactorial_le {n N : ℕ} (hn : n ≤ N) (hN : 0 < N) (K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), n.choose j * Nat.doubleFactorial (2 * j - 1) ≤
      (K + 1) * (2 * N) ^ K := by
  calc ∑ j ∈ Finset.range (K + 1), n.choose j * Nat.doubleFactorial (2 * j - 1)
      ≤ ∑ _j ∈ Finset.range (K + 1), (2 * N) ^ K := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        calc n.choose j * Nat.doubleFactorial (2 * j - 1) ≤ (2 * n) ^ j :=
              choose_mul_doubleFactorial_le n j
          _ ≤ (2 * N) ^ j := Nat.pow_le_pow_left (by omega) j
          _ ≤ (2 * N) ^ K :=
              Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = (K + 1) * (2 * N) ^ K := by simp

namespace PerfectMatching

section Defect

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The vertices where `T` and `Q` disagree, the vertices of the edges of `T ∖ Q`. -/
def defect (Q T : PerfectMatching W) : Finset W :=
  Finset.univ.filter fun w ↦ T.mate w ≠ Q.mate w

/-- `w` is in the defect iff `T` and `Q` pair it differently. -/
theorem mem_defect {Q T : PerfectMatching W} {w : W} : w ∈ defect Q T ↔ T.mate w ≠ Q.mate w := by
  simp [defect]

/-- The defect is closed under `T`. -/
theorem mate_mem_defect (Q T : PerfectMatching W) {w : W} (hw : w ∈ defect Q T) :
    T.mate w ∈ defect Q T := by
  rw [mem_defect] at hw ⊢
  intro h
  apply hw
  have h' := congrArg Q.mate h
  simp only [mate_mate] at h'
  exact h'.symm

/-- The defect is closed under `Q`. -/
theorem mate_mem_defect_ref (Q T : PerfectMatching W) {w : W} (hw : w ∈ defect Q T) :
    Q.mate w ∈ defect Q T := by
  rw [mem_defect] at hw ⊢
  intro h
  apply hw
  have h' := congrArg T.mate h
  simp only [mate_mate] at h'
  exact h'.symm

omit [Fintype W] in
/-- A `Q`-closed set has twice as many vertices as `Q`-edges. -/
theorem two_mul_card_image_mate [Finite W] (Q : PerfectMatching W) (A : Finset W)
    (hA : ∀ w ∈ A, Q.mate w ∈ A) : 2 * (A.image fun w ↦ s(w, Q.mate w)).card = A.card := by
  have := Fintype.ofFinite W
  have hAc : ∀ w ∈ Aᶜ, Q.mate w ∈ Aᶜ := fun w hw ↦
    Finset.mem_compl.mpr fun h ↦ Finset.mem_compl.mp hw ((mate_mem_iff Q A hA w).mp h)
  have h := two_mul_card_edgesOff Q Aᶜ hAc
  rwa [edgesOff, compl_compl] at h

omit [Fintype W] in
/-- A `Q`-closed set contains `w` if its `Q`-edges contain the `Q`-edge at `w`. -/
theorem mem_of_mem_image_mate (Q : PerfectMatching W) {A : Finset W}
    (hA : ∀ w ∈ A, Q.mate w ∈ A) {w : W} (h : s(w, Q.mate w) ∈ A.image fun v ↦ s(v, Q.mate v)) :
    w ∈ A := by
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
  rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨_, rfl⟩
  · exact hv
  · exact hA v hv

/-- At most `|PM(D)|` matchings `T` have defect `D`, since `T` equals `Q` off `D`. -/
theorem card_defect_eq_le (Q : PerfectMatching W) (D : Finset W) :
    (Finset.univ.filter fun T : PerfectMatching W ↦ defect Q T = D).card ≤
      Fintype.card (PerfectMatching D) := by
  rw [← Fintype.card_subtype]
  have hD : ∀ T : {T : PerfectMatching W // defect Q T = D}, ∀ w ∈ D, T.1.mate w ∈ D := by
    rintro ⟨T, rfl⟩ w hw
    exact mate_mem_defect Q T hw
  refine Fintype.card_le_of_injective (fun T ↦ restrict T.1 D (hD T)) ?_
  rintro ⟨T₁, h₁⟩ ⟨T₂, h₂⟩ h
  refine Subtype.ext (PerfectMatching.ext (Equiv.ext fun w ↦ ?_))
  by_cases hw : w ∈ D
  · exact congrArg (fun X : PerfectMatching D ↦ (X.mate ⟨w, hw⟩ : W)) h
  · rw [← h₁, mem_defect, not_not] at hw
    have hw₂ : w ∉ defect Q T₂ := h₂ ▸ h₁ ▸ fun h' ↦ (mem_defect.mp h') hw
    rw [mem_defect, not_not] at hw₂
    rw [hw, hw₂]

/-- A perfect matching `Q` of a type with `2n` elements has at most `C(n, j)` `Q`-closed sets
of size `2j`. -/
theorem card_closed_le (Q : PerfectMatching W) {n : ℕ} (hW : Fintype.card W = 2 * n) (j : ℕ) :
    (Finset.univ.filter fun D : Finset W ↦ (∀ w ∈ D, Q.mate w ∈ D) ∧ D.card = 2 * j).card ≤
      n.choose j := by
  have hQ : (Finset.univ.image fun w ↦ s(w, Q.mate w)).card = n := by
    have h := two_mul_card_image_mate Q Finset.univ fun w _ ↦ Finset.mem_univ _
    rw [Finset.card_univ, hW] at h
    omega
  rw [← hQ, ← Finset.card_powersetCard]
  refine Finset.card_le_card_of_injOn (fun D ↦ D.image fun w ↦ s(w, Q.mate w)) ?_ ?_
  · intro D hD
    obtain ⟨hcl, hcard⟩ := (Finset.mem_filter.mp hD).2
    refine Finset.mem_powersetCard.mpr ⟨Finset.image_subset_image (Finset.subset_univ D), ?_⟩
    have h := two_mul_card_image_mate Q D hcl
    dsimp only
    omega
  · intro D₁ hD₁ D₂ hD₂ h
    have h₁ := (Finset.mem_filter.mp hD₁).2.1
    have h₂ := (Finset.mem_filter.mp hD₂).2.1
    dsimp only at h
    ext w
    constructor
    · intro hw
      exact mem_of_mem_image_mate Q h₂ (h ▸ Finset.mem_image_of_mem _ hw)
    · intro hw
      exact mem_of_mem_image_mate Q h₁ (h.symm ▸ Finset.mem_image_of_mem _ hw)

/-- At most `C(n, j)(2j - 1)!!` perfect matchings differ from `Q` on exactly `2j` vertices. -/
theorem card_defect_card_eq_le (Q : PerfectMatching W) {n : ℕ} (hW : Fintype.card W = 2 * n)
    (j : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j).card ≤
      n.choose j * Nat.doubleFactorial (2 * j - 1) := by
  set 𝒞 := Finset.univ.filter fun D : Finset W ↦ (∀ w ∈ D, Q.mate w ∈ D) ∧ D.card = 2 * j
  have hmaps : ((Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j) :
      Set (PerfectMatching W)).MapsTo (defect Q) 𝒞 := by
    intro T hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun w hw ↦ mate_mem_defect_ref Q T hw, (Finset.mem_filter.mp hT).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ D ∈ 𝒞, ({T ∈ Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j |
        defect Q T = D}).card
      ≤ ∑ _D ∈ 𝒞, Nat.doubleFactorial (2 * j - 1) := by
        refine Finset.sum_le_sum fun D hD ↦ ?_
        have hcard : Fintype.card D = 2 * j := by
          rw [Fintype.card_coe]
          exact (Finset.mem_filter.mp hD).2.2
        calc ({T ∈ Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j |
              defect Q T = D}).card
            ≤ (Finset.univ.filter fun T : PerfectMatching W ↦ defect Q T = D).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
          _ ≤ Fintype.card (PerfectMatching D) := card_defect_eq_le Q D
          _ = Nat.doubleFactorial (2 * j - 1) := card_eq_doubleFactorial hcard
    _ = 𝒞.card * Nat.doubleFactorial (2 * j - 1) := by simp
    _ ≤ n.choose j * Nat.doubleFactorial (2 * j - 1) :=
        Nat.mul_le_mul_right _ (card_closed_le Q hW j)

/-- At most `∑_{j ≤ K} C(n, j)(2j - 1)!!` perfect matchings differ from `Q` on at most `2K`
vertices. -/
theorem card_defect_le (Q : PerfectMatching W) {n : ℕ} (hW : Fintype.card W = 2 * n) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card ≤ 2 * K).card ≤
      ∑ j ∈ Finset.range (K + 1), n.choose j * Nat.doubleFactorial (2 * j - 1) := by
  calc (Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card ≤ 2 * K).card
      ≤ ((Finset.range (K + 1)).biUnion fun j ↦
          Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j).card := by
        refine Finset.card_le_card fun T hT ↦ ?_
        have h := two_mul_card_image_mate Q (defect Q T) fun w hw ↦ mate_mem_defect_ref Q T hw
        have hK := (Finset.mem_filter.mp hT).2
        refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩⟩
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          (Finset.univ.filter fun T : PerfectMatching W ↦ (defect Q T).card = 2 * j).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (K + 1), n.choose j * Nat.doubleFactorial (2 * j - 1) :=
        Finset.sum_le_sum fun j _ ↦ card_defect_card_eq_le Q hW j

end Defect

section Tail

variable {V : Type*} [DecidableEq V]

/-- The edges of a perfect matching `T` of `U ⊆ V`, as edges of `V`. -/
def tailEdges {U : Finset V} (T : PerfectMatching U) : Finset (Sym2 V) :=
  Finset.univ.image fun u : U ↦ s((u : V), (T.mate u : V))

/-- `|T ∖ P|`, the number of edges of the perfect matching `T` of `U ⊆ V` that are not edges of
the perfect matching `P` of `V`. -/
def tailDist (P : PerfectMatching V) {U : Finset V} (T : PerfectMatching U) : ℕ :=
  ((tailEdges T).filter fun e ↦ e ∉ P.toGraph.edgeSet).card

/-- `2|T ∖ P|` is the number of vertices of `U` that `T` and `P` pair differently. -/
theorem two_mul_tailDist (P : PerfectMatching V) {U : Finset V} (T : PerfectMatching U) :
    2 * tailDist P T = (Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u).card := by
  set D := Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u
  have hD : ∀ u ∈ D, T.mate u ∈ D := by
    intro u hu
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    intro h
    apply hu
    simp only [mate_mate] at h
    have h' := congrArg P.mate h
    simp only [mate_mate] at h'
    exact h'.symm
  have himg : (tailEdges T).filter (fun e ↦ e ∉ P.toGraph.edgeSet) =
      (D.image fun u ↦ s(u, T.mate u)).image (Sym2.map Subtype.val) := by
    rw [tailEdges, Finset.filter_image, Finset.image_image]
    refine congrArg₂ Finset.image rfl (Finset.filter_congr fun u _ ↦ ?_)
    rw [SimpleGraph.mem_edgeSet, toGraph_adj, ne_comm]
  rw [tailDist, himg, Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
    two_mul_card_image_mate T D hD]

omit [DecidableEq V] in
/-- Some perfect matching `P'` of `U` agrees with `P` on every edge of `P` inside `U`. -/
theorem exists_extend_restrict (P : PerfectMatching V) (U : Finset V) (hU : Even U.card) :
    ∃ P' : PerfectMatching U, ∀ u : U, P.mate u ∈ U → (P'.mate u : V) = P.mate u := by
  classical
  set E : Finset (Sym2 U) :=
    Finset.univ.filter fun e ↦ Sym2.map Subtype.val e ∈ P.toGraph.edgeSet
  have hmem : ∀ a b : U, s(a, b) ∈ E ↔ P.mate a = b := fun a b ↦ by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.map_mk,
      SimpleGraph.mem_edgeSet, toGraph_adj]
  have hE : IsPartialMatching E := by
    refine ⟨fun e he hd ↦ ?_, fun e he f hf v hve hvf ↦ ?_⟩
    · induction e using Sym2.ind with
      | h a b =>
      obtain rfl := Sym2.mk_isDiag_iff.mp hd
      exact P.mate_ne a ((hmem a a).mp he)
    · obtain ⟨x, rfl⟩ : ∃ x, s(v, x) = e := ⟨_, Sym2.other_spec hve⟩
      obtain ⟨y, rfl⟩ : ∃ y, s(v, y) = f := ⟨_, Sym2.other_spec hvf⟩
      rw [Sym2.congr_right]
      exact Subtype.ext (((hmem v x).mp he).symm.trans ((hmem v y).mp hf))
  obtain ⟨P', -, hPE⟩ := exists_edgesOff_eq (by rwa [Fintype.card_coe]) hE
  refine ⟨P', fun u hu ↦ ?_⟩
  have hin : s(u, ⟨P.mate u, hu⟩) ∈ E := (hmem _ _).mpr rfl
  have hu' : u ∉ uncovered E := fun h ↦ mem_uncovered.mp h _ hin (Sym2.mem_mk_left _ _)
  have hin' : s(u, P'.mate u) ∈ E := by
    rw [← hPE]
    exact mem_edgesOff.mpr ⟨u, hu', rfl⟩
  have h := hE.2 _ hin' _ hin u (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
  rw [Sym2.congr_right] at h
  rw [h]

/-- For a perfect matching `P` of `V` and `U ⊆ V` with `|U| = 2n`, at most
`∑_{j ≤ K} C(n, j)(2j - 1)!!` perfect matchings `T` of `U` have `|T ∖ P| ≤ K`. -/
theorem card_tailDist_le (P : PerfectMatching V) {U : Finset V} {n : ℕ} (hU : U.card = 2 * n)
    (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T ≤ K).card ≤
      ∑ j ∈ Finset.range (K + 1), n.choose j * Nat.doubleFactorial (2 * j - 1) := by
  obtain ⟨P', hP'⟩ := exists_extend_restrict P U ⟨n, by omega⟩
  refine le_trans (Finset.card_le_card fun T hT ↦ ?_)
    (card_defect_le P' (by rw [Fintype.card_coe, hU]) K)
  have hT := (Finset.mem_filter.mp hT).2
  have hsub : defect P' T ⊆ Finset.univ.filter fun u : U ↦ (T.mate u : V) ≠ P.mate u := by
    intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h ↦ mem_defect.mp hu (Subtype.ext ?_)⟩
    rw [hP' u (h ▸ (T.mate u).2), h]
  have hcard := (Finset.card_le_card hsub).trans_eq (two_mul_tailDist P T).symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

end Tail

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

/-- `N_m ≤ K` for the gadget `G`: every tail, a perfect matching `T` of `U = V_m ∖ G`, has a
zero state `P` with `|T ∖ P| ≤ K`. -/
def RepairBound (m : ℕ) [NeZero m] (G : Finset (Vertex m)) (K : ℕ) : Prop :=
  ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), ∃ P : ZeroState m, tailDist P.1 T ≤ K

variable {m : ℕ} [NeZero m]

/-- A six-vertex gadget `G ⊆ V_m` forces `3 ≤ m` and `|V_m ∖ G| = 2(m - 3)`. -/
theorem card_compl_gadget {G : Finset (Vertex m)} (hG : G.card = 6) :
    3 ≤ m ∧ Gᶜ.card = 2 * (m - 3) := by
  have h := G.card_le_univ
  rw [card_vertex, hG] at h
  rw [Finset.card_compl, card_vertex, hG]
  omega

/-- There are `(2m - 7)!!` tails, the perfect matchings of `U = V_m ∖ G`. -/
theorem card_tail {G : Finset (Vertex m)} (hG : G.card = 6) :
    Fintype.card (PerfectMatching (Gᶜ : Finset (Vertex m))) =
      Nat.doubleFactorial (2 * m - 7) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  rw [card_eq_doubleFactorial (n := m - 3) (by rw [Fintype.card_coe, hU])]
  congr 1
  omega

/-- The COD-155 counting lemma, for every `m` and `K`. If every tail is within `K` edges of a
zero state, then `(2m - 7)!! ≤ Z_m ∑_{j ≤ K} C(m - 3, j)(2j - 1)!! ≤ Z_m (K + 1)(2m)^K`. -/
theorem repair_count {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ}
    (hK : RepairBound m G K) :
    Nat.doubleFactorial (2 * m - 7) ≤ zeroCount m *
        ∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) ∧
      zeroCount m *
          ∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) ≤
        zeroCount m * ((K + 1) * (2 * m) ^ K) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  refine ⟨?_, Nat.mul_le_mul_left _
    (sum_choose_mul_doubleFactorial_le (Nat.sub_le m 3) (NeZero.pos m) K)⟩
  rw [← card_tail hG]
  exact card_le_card_mul_of_cover
    (fun (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (P : ZeroState m) ↦ tailDist P.1 T)
    K _ hK fun P ↦ card_tailDist_le P.1 hU K

/-- `(2m - 1)!! = (2m - 1)(2m - 3)(2m - 5)(2m - 7)!!` for `3 ≤ m`. -/
theorem doubleFactorial_two_mul_sub_one_eq (h : 3 ≤ m) :
    Nat.doubleFactorial (2 * m - 1) =
      (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * Nat.doubleFactorial (2 * m - 7) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : 2 * (3 + k) - 1 = 2 * k + 1 + 2 + 2 := by omega
  have e3 : 2 * (3 + k) - 3 = 2 * k + 1 + 2 := by omega
  have e5 : 2 * (3 + k) - 5 = 2 * k + 1 := by omega
  have e7 : 2 * (3 + k) - 7 = 2 * k - 1 := by omega
  rw [e1, e3, e5, e7, Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two,
    Nat.doubleFactorial_add_one]
  ring

/-- If `N_m ≤ K`, then `(2m - 1)!! ≤ Z_m (2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K`. -/
theorem doubleFactorial_le_zeroCount_mul {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ}
    (hK : RepairBound m G K) :
    Nat.doubleFactorial (2 * m - 1) ≤
      zeroCount m * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  obtain ⟨h1, h2⟩ := repair_count hG hK
  rw [doubleFactorial_two_mul_sub_one_eq h3]
  calc (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * Nat.doubleFactorial (2 * m - 7)
      ≤ (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (zeroCount m * ((K + 1) * (2 * m) ^ K)) :=
        Nat.mul_le_mul_left _ (h1.trans h2)
    _ = zeroCount m * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K) := by
        ring

/-- The density form of the counting lemma. If `N_m ≤ K`, then
`q_m = Z_m / (2m - 1)!! ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`. -/
theorem density_ge {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ} (hK : RepairBound m G K) :
    1 / ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K : ℝ) ≤
      (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  have h := doubleFactorial_le_zeroCount_mul hG hK
  have hcast : (((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K : ℕ) : ℝ) =
      (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_sub (show 3 ≤ 2 * m by omega),
      Nat.cast_sub (show 5 ≤ 2 * m by omega)]
    ring
  have hpos : 0 < (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K :=
    Nat.pos_of_ne_zero (by simp; omega)
  rw [div_le_div_iff₀ (hcast ▸ Nat.cast_pos.mpr hpos)
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)), one_mul, ← hcast]
  exact_mod_cast h

end RoundRobin.Canonical

end Pairing
