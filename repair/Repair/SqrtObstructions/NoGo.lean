import Repair.SqrtObstructions.ClassCount
import Repair.SqrtObstructions.Hole
import Repair.SqrtObstructions.CertLength

/-!
# NG-A(c) and (d): relativization barriers for `N_m ≤ K`

Source: `results/sqrt-m-obstructions.md` §0 (event families, robustness, Lemma R) and §1.2,
Theorem NG-A(c), (d) and the instance table, in the corrected form of
`results/review-sqrt-m-obstructions.md` §1.2 to §1.4 and §8. The review verifies (c) and (d) only
as relativization statements: they bar arguments whose derivation is valid for every family in
`𝔈_m`. The statements here make that family quantifier explicit. They say nothing about
arguments that use the true family beyond the stated hypotheses.

A hypothesis is a predicate `H` on event families. Fix a six-vertex gadget `G` and a profile
radius `K′`. `H` is `δ`-robust at radius `K′` (`IsRobust`) if it holds for every `𝓐′ ∈ 𝔈_m` with
`U(Y′ ≠ Y) ≤ δ` whose radius-`K′` coverage sets `Z(𝓐′) ∩ B_{K′}(T)` differ from those of `Z` on at
most `δ W` tails, `W = (2m - 7)!!`. The review asks for the profile clause per radius, which is
why `K′` is a parameter.

* `abs_prob_profile_sub_le_ne` : Lemma R for any two families,
  `|U(Y′ ∈ E) - U(Y ∈ E)| ≤ U(Y′ ≠ Y)`.
* `isRobust_law`, `isRobust_coverage` : law-level facts and radius-`K′` profile counts that hold
  for the true family with slack `δ` are `δ`-robust. So the robust class is not empty. Not every
  law-level statement is robust: the review (§1.3) notes that `E(X′)_k` can move by `(n)_k δ_K`,
  so a moment bound is covered only when its slack absorbs that.
* `hole_isRobust` : the hole family of NG-A(b) satisfies every `δ`-robust hypothesis once
  `δ ≥ δ_K = |Aut(𝓕)| (K + 4)(2m)^(K + 3)/(2m - 1)!!` and
  `δ W ≥ |Aut(𝓕)| ∑_{j ≤ K + K′ + 3} C(m - 3, j)(2j - 1)!!`. At `K′ = K` this is the review's
  `δ = max(δ_K, |G| β_{2K+3}(M)/W)`.
* `ngA_relativized` : for `𝒵 ⊆ Z`, `Aut(𝓕)`-invariant, and a tail with `ρ_𝒵(T0) > K`, some
  `𝓐′ ∈ 𝔈_m` satisfies `𝒵 ⊆ Z(𝓐′)` and every such hypothesis, and has `N(𝓐′) > K`.
* `ngA_c` (NG-A(c)) : if `|𝒵| (K + 1)(2m)^K < (2m - 7)!!`, no derivation valid for every
  `𝓐′ ∈ 𝔈_m` from `𝒵 ⊆ Z(𝓐′)` and a `δ`-robust hypothesis proves `N(𝓐′) ≤ K`.
* `ngA_d` (NG-A(d)) : the same with `𝒵 = ∅`, with no density hypothesis.
* `certTwoClass`, `ngA_c_certTwo` : the corrected instance of row 1 of the table,
  `𝒵 = Z ∩ Z_2(e)`, the zero states all but `e` of whose factors have a cycle with at most two
  `P`-edges. Its density bound (locality Theorem 4) is not formalized, so it is a hypothesis.

The asymptotic readings (`δ_K = e^(-(1 - o(1)) m ln m)` at `K = O(√m)`, the threshold
`(a - ε)√m`, and "they cannot reprove P1") are arithmetic on these finite statements and are not
formalized. The source's `δ_K` uses `A_K(m)`, while `prob_holeSet_le` loses a factor of order
`(2m)^3`.
-/

namespace Pairing

namespace Obstruction

open ChainRule

variable {Ω ι : Type*}

/-- **Lemma R** for any two families (`sqrt-m-obstructions.md` §0): every event `E` on profiles has
`|U(Y′ ∈ E) - U(Y ∈ E)| ≤ U(Y′ ≠ Y)`. -/
theorem abs_prob_profile_sub_le_ne [Fintype Ω] {P : Ω → ℝ} (hP : IsProb P) (A A' : ι → Set Ω)
    (E : Set (ι → Prop)) :
    |prob P {ω | (fun t ↦ ω ∈ A' t) ∈ E} - prob P {ω | (fun t ↦ ω ∈ A t) ∈ E}| ≤
      prob P {ω | (fun t ↦ ω ∈ A' t) ≠ fun t ↦ ω ∈ A t} := by
  set R := {ω | (fun t ↦ ω ∈ A' t) ≠ fun t ↦ ω ∈ A t} with hR
  have hd : {ω | (fun t ↦ ω ∈ A' t) ∈ E} \ R = {ω | (fun t ↦ ω ∈ A t) ∈ E} \ R := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hR, not_not]
    constructor
    · rintro ⟨h, hω⟩
      exact ⟨hω ▸ h, hω⟩
    · rintro ⟨h, hω⟩
      exact ⟨hω ▸ h, hω⟩
  rw [prob_eq_inter_add_diff P _ R, prob_eq_inter_add_diff P {ω | (fun t ↦ ω ∈ A t) ∈ E} R, hd,
    abs_le]
  have h1 := prob_mono hP (Set.inter_subset_left : R ∩ {ω | (fun t ↦ ω ∈ A' t) ∈ E} ⊆ R)
  have h2 := prob_mono hP (Set.inter_subset_left : R ∩ {ω | (fun t ↦ ω ∈ A t) ∈ E} ⊆ R)
  have h3 := prob_nonneg hP (R ∩ {ω | (fun t ↦ ω ∈ A' t) ∈ E})
  have h4 := prob_nonneg hP (R ∩ {ω | (fun t ↦ ω ∈ A t) ∈ E})
  constructor <;> linarith

end Obstruction

namespace RoundRobin.Canonical

open PerfectMatching Obstruction ChainRule

variable {m : ℕ} [NeZero m]

/-- `N(𝓐) ≤ K` for the gadget `G`: every tail is within `K` of a zero state of the family `𝓐`
(`sqrt-m-obstructions.md` §0). -/
def FamilyRepairBound (A : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m)))
    (G : Finset (Vertex m)) (K : ℕ) : Prop :=
  ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), ∃ P ∈ zeroSet A, tailDist P T ≤ K

/-- `U(Y′ ≠ Y)`, the uniform mass on which the profiles of two families differ
(`sqrt-m-obstructions.md` §0). -/
noncomputable def profileDist (A A' : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) : ℝ :=
  prob (unifWeight m) {P | (fun t ↦ P ∈ A' t) ≠ fun t ↦ P ∈ A t}

/-- The radius-`K′` coverage set `Z(𝓐) ∩ B_{K′}(T)` of a tail (`sqrt-m-obstructions.md` §0). -/
def coverage (A : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) {G : Finset (Vertex m)}
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (K' : ℕ) : Set (PerfectMatching (Vertex m)) :=
  {P | P ∈ zeroSet A ∧ tailDist P T ≤ K'}

open Classical in
/-- The tails whose radius-`K′` coverage set differs between two families
(`sqrt-m-obstructions.md` §0, per radius as `review-sqrt-m-obstructions.md` §1.3 asks). -/
noncomputable def coverChange (G : Finset (Vertex m))
    (A A' : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) (K' : ℕ) :
    Finset (PerfectMatching (Gᶜ : Finset (Vertex m))) :=
  Finset.univ.filter fun T ↦ coverage A' T K' ≠ coverage A T K'

/-- A hypothesis `H` on event families is `δ`-robust at profile radius `K′`
(`sqrt-m-obstructions.md` §0, with the per-radius profile clause of
`review-sqrt-m-obstructions.md` §1.3): it holds for every `𝓐′ ∈ 𝔈_m` with `U(Y′ ≠ Y) ≤ δ` whose
radius-`K′` coverage sets differ from those of `Z` on at most `δ (2m - 7)!!` tails. -/
def IsRobust (G : Finset (Vertex m)) (δ : ℝ) (K' : ℕ)
    (H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop) : Prop :=
  ∀ A', IsEquivFamily A' → profileDist (hamFamily m) A' ≤ δ →
    ((coverChange G (hamFamily m) A' K').card : ℝ) ≤ δ * Nat.doubleFactorial (2 * m - 7) → H A'

/-- **Law-level facts are robust** (`sqrt-m-obstructions.md` §0, Lemma R). If
`|U(Y ∈ E) - c| + δ ≤ ε` for the true family, the hypothesis `|U(Y′ ∈ E) - c| ≤ ε` is
`δ`-robust. -/
theorem isRobust_law (G : Finset (Vertex m)) (K' : ℕ) (E : Set (ZMod (2 * m - 1) → Prop))
    {c ε δ : ℝ}
    (h : |prob (unifWeight m) {P | (fun t ↦ P ∈ hamFamily m t) ∈ E} - c| + δ ≤ ε) :
    IsRobust G δ K' fun A' ↦ |prob (unifWeight m) {P | (fun t ↦ P ∈ A' t) ∈ E} - c| ≤ ε := by
  intro A' _ hδ _
  have hR := abs_prob_profile_sub_le_ne (isProb_unifWeight m) (hamFamily m) A' E
  have htri := abs_sub_le (prob (unifWeight m) {P | (fun t ↦ P ∈ A' t) ∈ E})
    (prob (unifWeight m) {P | (fun t ↦ P ∈ hamFamily m t) ∈ E}) c
  rw [profileDist] at hδ
  linarith

open Classical in
/-- **Profile averages are robust** (`sqrt-m-obstructions.md` §0). For any property `Q` of
coverage sets, if at least `(c + δ) W` tails have `Q (Z ∩ B_{K′}(T))`, the hypothesis "at least
`c W` tails have `Q (Z(𝓐′) ∩ B_{K′}(T))`" is `δ`-robust, `W = (2m - 7)!!`. -/
theorem isRobust_coverage (G : Finset (Vertex m)) (K' : ℕ)
    (Q : Set (PerfectMatching (Vertex m)) → Prop) {c δ : ℝ}
    (h : (c + δ) * Nat.doubleFactorial (2 * m - 7) ≤
      ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage (hamFamily m) T K')).card : ℝ)) :
    IsRobust G δ K' fun A' ↦ c * Nat.doubleFactorial (2 * m - 7) ≤
      ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage A' T K')).card : ℝ) := by
  intro A' _ _ hch
  have hsub : (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage (hamFamily m) T K')) ⊆
      (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage A' T K')) ∪ coverChange G (hamFamily m) A' K' := by
    intro T hT
    have hQ := (Finset.mem_filter.mp hT).2
    by_cases hT' : coverage A' T K' = coverage (hamFamily m) T K'
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT' ▸ hQ⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' : ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage (hamFamily m) T K')).card : ℝ) ≤
      ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        Q (coverage A' T K')).card : ℝ) + ((coverChange G (hamFamily m) A' K').card : ℝ) := by
    exact_mod_cast hc
  nlinarith

/-- **NG-A(b), coverage profile at radius `K′`** (`sqrt-m-obstructions.md` §1.2, proof of NG-A(b),
per radius as `review-sqrt-m-obstructions.md` §1.3 asks). At most
`|Aut(𝓕)| ∑_{j ≤ K + K′ + 3} C(m - 3, j)(2j - 1)!!` tails `T` have a member of
`⋃_g g • B_K(T0)` within `K′`. -/
theorem card_coverage_change_le_of_radius {G : Finset (Vertex m)} (hG : G.card = 6)
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K K' : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ ballOrbit T0 K, tailDist P T ≤ K').card ≤
      Nat.card (autGroup m) *
        ∑ j ∈ Finset.range (K + K' + 3 + 1),
          (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  obtain ⟨Q, hQ⟩ := exists_extends (by rw [card_vertex]; exact even_two_mul m) T0
  calc (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ ballOrbit T0 K, tailDist P T ≤ K').card
      ≤ ((autFinset m).biUnion fun g ↦
          Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
            tailDist (g • Q) T ≤ K + K' + 3).card := by
        refine Finset.card_le_card fun T hT ↦ ?_
        obtain ⟨P, ⟨g, hg, hd0⟩, hd⟩ := (Finset.mem_filter.mp hT).2
        refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        have h1 := two_mul_tailDist_le P (g • Q) T
        have h2 := card_defect_le_of_extends Q T0 hQ (g⁻¹ • P)
        rw [compl_compl, hG] at h2
        have h3 := card_defect_smul g Q (g⁻¹ • P)
        rw [smul_inv_smul] at h3
        omega
    _ ≤ ∑ g ∈ autFinset m, (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
          tailDist (g • Q) T ≤ K + K' + 3).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ autFinset m,
          ∑ j ∈ Finset.range (K + K' + 3 + 1),
            (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) :=
        Finset.sum_le_sum fun g _ ↦ card_tailDist_le (g • Q) hU (K + K' + 3)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, card_autFinset]

/-- **The hole family satisfies every robust hypothesis** (`sqrt-m-obstructions.md` §1.2,
NG-A(b) to (c), with `review-sqrt-m-obstructions.md` §1.2). Let `𝒵` be an `Aut(𝓕)`-invariant set
of zero states, `T0` a tail and `𝓐′` the hole family `A_t ∪ Rem`. If
`δ ≥ |Aut(𝓕)| (K + 4)(2m)^(K + 3)/(2m - 1)!!` and
`δ (2m - 7)!! ≥ |Aut(𝓕)| ∑_{j ≤ K + K′ + 3} C(m - 3, j)(2j - 1)!!`, then every `δ`-robust
hypothesis at radius `K′` holds for `𝓐′`. -/
theorem hole_isRobust {G : Finset (Vertex m)} (hG : G.card = 6)
    {𝒵 : Set (PerfectMatching (Vertex m))} (h𝒵 : 𝒵 ⊆ zeroSet (hamFamily m))
    (h𝒵G : ∀ g ∈ autGroup m, ∀ P, g • P ∈ 𝒵 ↔ P ∈ 𝒵)
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) {K K' : ℕ} (hT0 : ∀ P ∈ 𝒵, K < tailDist P T0)
    {δ : ℝ}
    (hδ1 : (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
      Nat.doubleFactorial (2 * m - 1) ≤ δ)
    (hδ2 : ((Nat.card (autGroup m) * ∑ j ∈ Finset.range (K + K' + 3 + 1),
      (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) : ℕ) : ℝ) ≤
        δ * Nat.doubleFactorial (2 * m - 7))
    {H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop}
    (hH : IsRobust G δ K' H) : H (holeFamily (hamFamily m) (holeSet 𝒵 T0 K)) := by
  obtain ⟨hequiv, hZ, -, -⟩ := hole h𝒵 h𝒵G hT0
  refine hH _ hequiv ?_ ?_
  · exact (prob_profile_ne_le (isProb_unifWeight m) (hamFamily m) (holeSet 𝒵 T0 K)).trans
      ((prob_holeSet_le hG 𝒵 T0 K).trans hδ1)
  · refine le_trans ?_ hδ2
    refine Nat.cast_le.mpr ((Finset.card_le_card fun T hT ↦ ?_).trans
      (card_coverage_change_le_of_radius hG T0 K K'))
    have hne := (Finset.mem_filter.mp hT).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hfar
    push Not at hfar
    refine hne ?_
    ext P
    simp only [coverage, Set.mem_ofPred_eq, hZ, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨h, -⟩, hd⟩
      exact ⟨h, hd⟩
    · rintro ⟨h, hd⟩
      exact ⟨⟨h, fun hR ↦ absurd hd (not_le.mpr (hfar P hR.2))⟩, hd⟩

/-- **NG-A(b) to (c), relativized** (`sqrt-m-obstructions.md` §1.2, in the form of
`review-sqrt-m-obstructions.md` §8). Let `𝒵` be an `Aut(𝓕)`-invariant set of zero states and
`T0` a tail with `ρ_𝒵(T0) > K`. For `δ` as in `hole_isRobust` and every `δ`-robust hypothesis
`H` at radius `K′`, some `𝓐′ ∈ 𝔈_m` has `𝒵 ⊆ Z(𝓐′)`, satisfies `H`, and has `N(𝓐′) > K`. -/
theorem ngA_relativized {G : Finset (Vertex m)} (hG : G.card = 6)
    {𝒵 : Set (PerfectMatching (Vertex m))} (h𝒵 : 𝒵 ⊆ zeroSet (hamFamily m))
    (h𝒵G : ∀ g ∈ autGroup m, ∀ P, g • P ∈ 𝒵 ↔ P ∈ 𝒵)
    {T0 : PerfectMatching (Gᶜ : Finset (Vertex m))} {K K' : ℕ}
    (hT0 : ∀ P ∈ 𝒵, K < tailDist P T0) {δ : ℝ}
    (hδ1 : (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
      Nat.doubleFactorial (2 * m - 1) ≤ δ)
    (hδ2 : ((Nat.card (autGroup m) * ∑ j ∈ Finset.range (K + K' + 3 + 1),
      (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) : ℕ) : ℝ) ≤
        δ * Nat.doubleFactorial (2 * m - 7))
    {H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop}
    (hH : IsRobust G δ K' H) :
    ∃ A', IsEquivFamily A' ∧ 𝒵 ⊆ zeroSet A' ∧ H A' ∧ ¬FamilyRepairBound A' G K := by
  obtain ⟨hequiv, -, hsub, hfar⟩ := hole h𝒵 h𝒵G hT0
  refine ⟨_, hequiv, hsub, hole_isRobust hG h𝒵 h𝒵G T0 hT0 hδ1 hδ2 hH, fun hN ↦ ?_⟩
  obtain ⟨P, hP, hd⟩ := hN T0
  exact absurd hd (not_le.mpr (hfar P hP))

/-- **NG-A(c), relativization form** (`sqrt-m-obstructions.md` §1.2, NG-A(c), as corrected in
`review-sqrt-m-obstructions.md` §1.2 and §8). Let `𝒵` be an `Aut(𝓕)`-invariant finite set of
zero states with `|𝒵| (K + 1)(2m)^K < (2m - 7)!!`, the finite form of NG-A(a). Let `δ` satisfy the
two bounds of `hole_isRobust` and `H` be `δ`-robust at radius `K′`. Then no derivation valid for
every `𝓐′ ∈ 𝔈_m` from `𝒵 ⊆ Z(𝓐′)` and `H(𝓐′)` concludes `N(𝓐′) ≤ K`. -/
theorem ngA_c {G : Finset (Vertex m)} (hG : G.card = 6)
    {𝒵 : Finset (PerfectMatching (Vertex m))} (h𝒵 : ↑𝒵 ⊆ zeroSet (hamFamily m))
    (h𝒵G : ∀ g ∈ autGroup m, ∀ P, g • P ∈ 𝒵 ↔ P ∈ 𝒵) {K K' : ℕ}
    (hdens : 𝒵.card * ((K + 1) * (2 * m) ^ K) < Nat.doubleFactorial (2 * m - 7)) {δ : ℝ}
    (hδ1 : (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
      Nat.doubleFactorial (2 * m - 1) ≤ δ)
    (hδ2 : ((Nat.card (autGroup m) * ∑ j ∈ Finset.range (K + K' + 3 + 1),
      (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) : ℕ) : ℝ) ≤
        δ * Nat.doubleFactorial (2 * m - 7))
    {H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop}
    (hH : IsRobust G δ K' H) :
    ¬∀ A', IsEquivFamily A' → ↑𝒵 ⊆ zeroSet A' → H A' → FamilyRepairBound A' G K := by
  intro hall
  obtain ⟨T0, hT0⟩ : ∃ T0 : PerfectMatching (Gᶜ : Finset (Vertex m)),
      ∀ P ∈ 𝒵, K < tailDist P T0 := by
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := class_count hG hno
    omega
  obtain ⟨A', hA', hsub, hHA, hN⟩ := ngA_relativized hG (𝒵 := ↑𝒵) h𝒵 h𝒵G
    (T0 := T0) hT0 hδ1 hδ2 hH
  exact hN (hall A' hA' hsub hHA)

/-- **NG-A(d), relativization form** (`sqrt-m-obstructions.md` §1.2, NG-A(d), as corrected in
`review-sqrt-m-obstructions.md` §1.2 and §8). For `δ` satisfying the two bounds of
`hole_isRobust` and `H` `δ`-robust at radius `K′`, no derivation valid for every `𝓐′ ∈ 𝔈_m` from
`H(𝓐′)` alone concludes `N(𝓐′) ≤ K`. -/
theorem ngA_d {G : Finset (Vertex m)} (hG : G.card = 6) {K K' : ℕ} {δ : ℝ}
    (hδ1 : (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
      Nat.doubleFactorial (2 * m - 1) ≤ δ)
    (hδ2 : ((Nat.card (autGroup m) * ∑ j ∈ Finset.range (K + K' + 3 + 1),
      (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) : ℕ) : ℝ) ≤
        δ * Nat.doubleFactorial (2 * m - 7))
    {H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop}
    (hH : IsRobust G δ K' H) :
    ¬∀ A', IsEquivFamily A' → H A' → FamilyRepairBound A' G K := by
  intro hall
  refine ngA_c hG (𝒵 := ∅) (by simp) (by simp) ?_ hδ1 hδ2 hH fun A' hA' _ hHA ↦ hall A' hA' hHA
  rw [Finset.card_empty, zero_mul]
  exact Nat.doubleFactorial_pos _

/-- `F_t` has a cycle with at most two edges of `P` in `P ∪ F_t`: a common edge (`σ_t y = y`) or a
`4`-cycle (`σ_t^2 y = y`) (`sqrt-m-obstructions.md` §1.2, the class `Z_2(θm)`). -/
def ShortCert (P : PerfectMatching (Vertex m)) (t : ZMod (2 * m - 1)) : Prop :=
  ∃ y, certPerm P t y = y ∨ (certPerm P t ^ 2) y = y

instance (P : PerfectMatching (Vertex m)) (t : ZMod (2 * m - 1)) : Decidable (ShortCert P t) :=
  inferInstanceAs (Decidable (∃ y, certPerm P t y = y ∨ (certPerm P t ^ 2) y = y))

/-- The class `Z ∩ Z_2(e)` of row 1 of the NG-A instance table, as corrected in
`review-sqrt-m-obstructions.md` §1.4: zero states for which at most `e` factors lack a cycle with
at most two edges of `P`. -/
def certTwoClass (m : ℕ) [NeZero m] (e : ℕ) : Finset (PerfectMatching (Vertex m)) :=
  Finset.univ.filter fun P ↦ IsZeroState (factor m) P ∧
    (Finset.univ.filter fun t ↦ ¬ShortCert P t).card ≤ e

/-- An automorphism conjugates `σ_t`: `σ_{π t}(g • P) = g σ_t(P) g⁻¹` when `g • F_t = F_{π t}`
(`sqrt-m-obstructions.md` §0, the group `G` acting on certificates). -/
theorem certPerm_smul (P : PerfectMatching (Vertex m)) {g : Equiv.Perm (Vertex m)}
    {t t' : ZMod (2 * m - 1)} (h : g • factor m t = factor m t') :
    certPerm (g • P) t' = g * certPerm P t * g⁻¹ := by
  rw [certPerm, certPerm, ← h]
  show g * P.mate * g⁻¹ * (g * (factor m t).mate * g⁻¹) = _
  group

/-- Short certificates are carried by automorphisms (`sqrt-m-obstructions.md` §1.2, `Z_2(θm)` is
`G`-invariant). -/
theorem shortCert_smul_iff (P : PerfectMatching (Vertex m)) {g : Equiv.Perm (Vertex m)}
    {t t' : ZMod (2 * m - 1)} (h : g • factor m t = factor m t') :
    ShortCert (g • P) t' ↔ ShortCert P t := by
  rw [ShortCert, ShortCert, certPerm_smul P h, conj_pow]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨g⁻¹ y, ?_⟩
    simp only [Equiv.Perm.mul_apply] at hy
    rcases hy with hy | hy
    · exact Or.inl (by rw [← Equiv.Perm.eq_inv_iff_eq] at hy; exact hy)
    · exact Or.inr (by rw [← Equiv.Perm.eq_inv_iff_eq] at hy; exact hy)
  · rintro ⟨y, hy⟩
    refine ⟨g y, ?_⟩
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases hy with hy | hy
    · exact Or.inl (by rw [hy])
    · exact Or.inr (by rw [hy])

/-- `Z ∩ Z_2(e)` is `Aut(𝓕)`-invariant (`sqrt-m-obstructions.md` §1.2, instance table, row 1,
with `review-sqrt-m-obstructions.md` §1.4). -/
theorem smul_mem_certTwoClass_iff (e : ℕ) {g : Equiv.Perm (Vertex m)} (hg : g ∈ autGroup m)
    (P : PerfectMatching (Vertex m)) : g • P ∈ certTwoClass m e ↔ P ∈ certTwoClass m e := by
  obtain ⟨π, hπ⟩ := IsAut.exists_perm hg
  have hcard : (Finset.univ.filter fun t ↦ ¬ShortCert P t).card =
      (Finset.univ.filter fun t ↦ ¬ShortCert (g • P) t).card :=
    Finset.card_equiv π fun t ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, shortCert_smul_iff P (hπ t)]
  simp only [certTwoClass, Finset.mem_filter, Finset.mem_univ, true_and, ← hcard]
  rw [← mem_zeroSet_hamFamily, ← mem_zeroSet_hamFamily,
    isEquivFamily_hamFamily.smul_mem_zeroSet_iff hg]

/-- **NG-A(c) for `𝒵 = Z ∩ Z_2(e)`** (`sqrt-m-obstructions.md` §1.2, instance table row 1, as
corrected in `review-sqrt-m-obstructions.md` §1.4: the class is `Z ∩ Z_2(θm)`, not `Z_2(θm)`).
If `|Z ∩ Z_2(e)| (K + 1)(2m)^K < (2m - 7)!!` (for `e = θm` and `K ≤ (½√(1 - 2θ) - ε)√m` this is
locality Theorem 4, not formalized here), then for `δ` and `H` as in `ngA_c` no derivation valid
for every `𝓐′ ∈ 𝔈_m` that keeps every zero state certified by `2`- and `4`-cycles off `e`
factors proves `N(𝓐′) ≤ K`. -/
theorem ngA_c_certTwo {G : Finset (Vertex m)} (hG : G.card = 6) (e : ℕ) {K K' : ℕ}
    (hdens : (certTwoClass m e).card * ((K + 1) * (2 * m) ^ K) < Nat.doubleFactorial (2 * m - 7))
    {δ : ℝ}
    (hδ1 : (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
      Nat.doubleFactorial (2 * m - 1) ≤ δ)
    (hδ2 : ((Nat.card (autGroup m) * ∑ j ∈ Finset.range (K + K' + 3 + 1),
      (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) : ℕ) : ℝ) ≤
        δ * Nat.doubleFactorial (2 * m - 7))
    {H : (ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) → Prop}
    (hH : IsRobust G δ K' H) :
    ¬∀ A', IsEquivFamily A' → ↑(certTwoClass m e) ⊆ zeroSet A' → H A' →
      FamilyRepairBound A' G K :=
  ngA_c hG (fun _ hP ↦ (Finset.mem_filter.mp hP).2.1)
    (fun _ hg _ ↦ smul_mem_certTwoClass_iff e hg _) hdens hδ1 hδ2 hH

end RoundRobin.Canonical

end Pairing
