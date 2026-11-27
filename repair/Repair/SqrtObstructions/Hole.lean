import Repair.Automorphism
import Repair.SqrtObstructions.Defect

/-!
# NG-A(b), the hole lemma

Source: `results/sqrt-m-obstructions.md` §0 (event families `𝔈_m`, Lemma R) and §1.2,
Theorem NG-A(b). Put `n = 2m - 1` and let `G = Aut(𝓕)` (`autGroup m`), which is
`AGL(1, ℤ/n)` for `n ≥ 7` (`range_affinePerm`).

An event family is `A : ℤ/n → Set PM(V_m)`. Its zero set is `Z(𝓐) = {P | ∀ t, P ∉ A_t}`. It lies
in `𝔈_m` (`IsEquivFamily`) when `g • A_t = A_{g(t)}` for every `g ∈ G`, where `g • F_t = F_{g(t)}`.
The true family is `A_t = {P | P ∪ F_t is one cycle}` (`hamEvent`), and its zero set is the set
of zero states.

Abstract part (namespace `Obstruction`).
* `zeroSet_holeFamily` : with `A′_t = A_t ∪ R`, `Z(𝓐′) = Z(𝓐) ∖ R`.
* `abs_prob_profile_sub_le` (Lemma R, first claim) : for every event `E` on profiles,
  `|U(Y′ ∈ E) - U(Y ∈ E)| ≤ U(R)`, and `prob_profile_ne_le` : `U(Y′ ≠ Y) ≤ U(R)`.

Round-robin part.
* `ballOrbit T0 K = ⋃_{g ∈ G} g • B_K(T0)` and `holeSet 𝒵 T0 K = (Z ∖ 𝒵) ∩ ballOrbit T0 K`,
  the set `Rem` of the source.
* `hole` (NG-A(b)) : for `𝒵 ⊆ Z` that is `G`-invariant and a tail `T0` with `ρ_𝒵(T0) > K`, the
  family `A′_t = A_t ∪ Rem` lies in `𝔈_m`, `Z(𝓐′) = Z ∖ Rem`, `𝒵 ⊆ Z(𝓐′)`, and every zero state of
  `𝓐′` is more than `K` from `T0`, so `N_m(𝓐′) > K`.
* `card_ball_tail_le` : `|B_K(T0)| ≤ ∑_{j ≤ K + 3} C(m, j)(2j - 1)!! ≤ (K + 4)(2m)^(K + 3)`.
* `prob_holeSet_le`, `abs_prob_profile_hole_le` : `U(Y′ ≠ Y) ≤ U(Rem) ≤ δ_K` with
  `δ_K = |G| (K + 4)(2m)^(K + 3) / (2m - 1)!!`.
* `coverage_eq_of_far`, `card_coverage_change_le` : the coverage profile
  `T ↦ Z(𝓐′) ∩ B_K(T)` equals `T ↦ Z ∩ B_K(T)` except on at most `|G| β_{2K+3}(M)` tails.

The source bounds `|B_K(T0)|` by `A_K(m) ≤ (K + 1)(2K + 1)(2K + 3)(2K + 5)(2m)^K` and cites
`card_ball_eq`. That lemma counts the dual ball, the tails near a fixed matching. Here the ball of
matchings near a tail is bounded directly through `card_defect_le`, which costs a polynomial
factor of order `(2m)^3` in `δ_K`. NG-A(c) and (d) are not formalized.
-/

namespace Pairing

namespace Obstruction

open ChainRule

variable {Ω ι : Type*}

/-- The zero set `Z(𝓐) = {ω | ∀ t, ω ∉ A_t}` of an event family (`sqrt-m-obstructions.md` §0). -/
def zeroSet (A : ι → Set Ω) : Set Ω :=
  {ω | ∀ t, ω ∉ A t}

/-- The hole family `A′_t = A_t ∪ R` of NG-A(b) (`sqrt-m-obstructions.md` §1.2). -/
def holeFamily (A : ι → Set Ω) (R : Set Ω) (t : ι) : Set Ω :=
  A t ∪ R

/-- Off `R` the hole family agrees with `A` (`sqrt-m-obstructions.md` §1.2, NG-A(b)). -/
theorem mem_holeFamily_iff_of_notMem {A : ι → Set Ω} {R : Set Ω} {ω : Ω} (h : ω ∉ R) (t : ι) :
    ω ∈ holeFamily A R t ↔ ω ∈ A t := by
  simp [holeFamily, h]

/-- Off `R` the profile `Y′(ω) = (ω ∈ A′_t)_t` equals `Y(ω)` (`sqrt-m-obstructions.md` §0,
Lemma R). -/
theorem profile_eq_of_notMem {A : ι → Set Ω} {R : Set Ω} {ω : Ω} (h : ω ∉ R) :
    (fun t ↦ ω ∈ holeFamily A R t) = fun t ↦ ω ∈ A t :=
  funext fun t ↦ propext (mem_holeFamily_iff_of_notMem h t)

/-- `Z(𝓐′) = Z(𝓐) ∖ R` for `A′_t = A_t ∪ R` (`sqrt-m-obstructions.md` §1.2, NG-A(b)). -/
theorem zeroSet_holeFamily [Nonempty ι] (A : ι → Set Ω) (R : Set Ω) :
    zeroSet (holeFamily A R) = zeroSet A \ R := by
  ext ω
  simp only [zeroSet, holeFamily, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, not_or]
  constructor
  · intro h
    exact ⟨fun t ↦ (h t).1, (h (Classical.arbitrary ι)).2⟩
  · rintro ⟨h1, h2⟩ t
    exact ⟨h1 t, h2⟩

/-- **Lemma R**, first claim (`sqrt-m-obstructions.md` §0). If `Y′` and `Y` agree off `R`, then
`|U(Y′ ∈ E) - U(Y ∈ E)| ≤ U(R)` for every event `E` on profiles. -/
theorem abs_prob_profile_sub_le [Fintype Ω] {P : Ω → ℝ} (hP : IsProb P) (A : ι → Set Ω)
    (R : Set Ω) (E : Set (ι → Prop)) :
    |prob P {ω | (fun t ↦ ω ∈ holeFamily A R t) ∈ E} - prob P {ω | (fun t ↦ ω ∈ A t) ∈ E}| ≤
      prob P R := by
  have hd : {ω | (fun t ↦ ω ∈ holeFamily A R t) ∈ E} \ R = {ω | (fun t ↦ ω ∈ A t) ∈ E} \ R := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hR⟩
      exact ⟨by rwa [profile_eq_of_notMem hR] at h, hR⟩
    · rintro ⟨h, hR⟩
      exact ⟨by rwa [profile_eq_of_notMem hR], hR⟩
  rw [prob_eq_inter_add_diff P _ R, prob_eq_inter_add_diff P {ω | (fun t ↦ ω ∈ A t) ∈ E} R, hd,
    abs_le]
  have h1 := prob_mono hP (Set.inter_subset_left : R ∩ {ω | (fun t ↦ ω ∈ holeFamily A R t) ∈ E} ⊆ R)
  have h2 := prob_mono hP (Set.inter_subset_left : R ∩ {ω | (fun t ↦ ω ∈ A t) ∈ E} ⊆ R)
  have h3 := prob_nonneg hP (R ∩ {ω | (fun t ↦ ω ∈ holeFamily A R t) ∈ E})
  have h4 := prob_nonneg hP (R ∩ {ω | (fun t ↦ ω ∈ A t) ∈ E})
  constructor <;> linarith

/-- **Lemma R** (`sqrt-m-obstructions.md` §0): `U(Y′ ≠ Y) ≤ U(R)` for `A′_t = A_t ∪ R`. -/
theorem prob_profile_ne_le [Fintype Ω] {P : Ω → ℝ} (hP : IsProb P) (A : ι → Set Ω) (R : Set Ω) :
    prob P {ω | (fun t ↦ ω ∈ holeFamily A R t) ≠ fun t ↦ ω ∈ A t} ≤ prob P R :=
  prob_mono hP fun _ hω ↦ by_contra fun hR ↦ hω (profile_eq_of_notMem hR)

end Obstruction

namespace RoundRobin.Canonical

open PerfectMatching Obstruction ChainRule

variable {m : ℕ} [NeZero m]

@[deprecated hamEvent (since := "2026-11-26")]
alias hamFamily := hamEvent

/-- The zero set of the true family `hamEvent` is the set of zero states
(`sqrt-m-obstructions.md` §0). -/
theorem mem_zeroSet_hamEvent {P : PerfectMatching (Vertex m)} :
    P ∈ zeroSet (hamEvent m) ↔ IsZeroState (factor m) P :=
  Iff.rfl

@[deprecated mem_zeroSet_hamEvent (since := "2026-11-26")]
alias mem_zeroSet_hamFamily := mem_zeroSet_hamEvent

/-- Membership in `𝔈_m` (`sqrt-m-obstructions.md` §0): `g • A_t = A_{g(t)}` for every
`g ∈ Aut(𝓕)`, where `g • F_t = F_{g(t)}`. -/
def IsEquivFamily (A : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))) : Prop :=
  ∀ g ∈ autGroup m, ∀ t s, g • factor m t = factor m s → ∀ P, g • P ∈ A s ↔ P ∈ A t

/-- The true family lies in `𝔈_m` (`sqrt-m-obstructions.md` §0). -/
theorem isEquivFamily_hamEvent : IsEquivFamily (hamEvent m) := by
  intro g _ t s h P
  simp only [hamEvent, Set.mem_ofPred_eq]
  rw [← h, ham_smul]

@[deprecated isEquivFamily_hamEvent (since := "2026-11-26")]
alias isEquivFamily_hamFamily := isEquivFamily_hamEvent

/-- The zero set of a family in `𝔈_m` is `Aut(𝓕)`-invariant (`sqrt-m-obstructions.md` §1.2). -/
theorem IsEquivFamily.smul_mem_zeroSet_iff {A : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))}
    (hA : IsEquivFamily A) {g : Equiv.Perm (Vertex m)} (hg : g ∈ autGroup m)
    (P : PerfectMatching (Vertex m)) : g • P ∈ zeroSet A ↔ P ∈ zeroSet A := by
  obtain ⟨π, hπ⟩ := IsAut.exists_perm hg
  constructor
  · intro h t ht
    exact h (π t) ((hA g hg t (π t) (hπ t) P).mpr ht)
  · intro h s hs
    exact h _ ((hA g hg (π.symm s) s (by rw [hπ, Equiv.apply_symm_apply]) P).mp hs)

/-- Adding an `Aut(𝓕)`-invariant set `R` to every event keeps the family in `𝔈_m`
(`sqrt-m-obstructions.md` §1.2, proof of NG-A(b)). -/
theorem IsEquivFamily.hole {A : ZMod (2 * m - 1) → Set (PerfectMatching (Vertex m))}
    (hA : IsEquivFamily A) {R : Set (PerfectMatching (Vertex m))}
    (hR : ∀ g ∈ autGroup m, ∀ P, g • P ∈ R ↔ P ∈ R) : IsEquivFamily (holeFamily A R) := by
  intro g hg t s h P
  simp only [holeFamily, Set.mem_union, hA g hg t s h P, hR g hg P]

/-- `⋃_{g ∈ Aut(𝓕)} g • B_K(T0)`, the perfect matchings within `K` of some image of the tail
`T0` (`sqrt-m-obstructions.md` §1.2, NG-A(b)). -/
def ballOrbit {G : Finset (Vertex m)} (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) :
    Set (PerfectMatching (Vertex m)) :=
  {P | ∃ g, IsAut m g ∧ tailDist (g⁻¹ • P) T0 ≤ K}

instance {G : Finset (Vertex m)} (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) :
    DecidablePred (· ∈ ballOrbit T0 K) :=
  fun P ↦ inferInstanceAs (Decidable (∃ g, IsAut m g ∧ tailDist (g⁻¹ • P) T0 ≤ K))

/-- `ballOrbit T0 K` is `Aut(𝓕)`-invariant (`sqrt-m-obstructions.md` §1.2, NG-A(b)). -/
theorem smul_mem_ballOrbit_iff {G : Finset (Vertex m)}
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) {h : Equiv.Perm (Vertex m)}
    (hh : h ∈ autGroup m) (P : PerfectMatching (Vertex m)) :
    h • P ∈ ballOrbit T0 K ↔ P ∈ ballOrbit T0 K := by
  constructor
  · rintro ⟨g, hg, hd⟩
    refine ⟨h⁻¹ * g, (mul_mem (inv_mem hh) (show g ∈ autGroup m from hg) : _), ?_⟩
    rwa [mul_inv_rev, inv_inv, mul_smul]
  · rintro ⟨g, hg, hd⟩
    refine ⟨h * g, (mul_mem hh (show g ∈ autGroup m from hg) : _), ?_⟩
    rwa [mul_inv_rev, mul_smul, inv_smul_smul]

/-- The set `Rem = (Z ∖ 𝒵) ∩ ⋃_{g ∈ G} g • B_K(T0)` of NG-A(b) (`sqrt-m-obstructions.md` §1.2). -/
def holeSet (𝒵 : Set (PerfectMatching (Vertex m))) {G : Finset (Vertex m)}
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) : Set (PerfectMatching (Vertex m)) :=
  zeroSet (hamEvent m) ∩ 𝒵ᶜ ∩ ballOrbit T0 K

/-- `Rem` is `Aut(𝓕)`-invariant when `𝒵` is (`sqrt-m-obstructions.md` §1.2, NG-A(b)). -/
theorem smul_mem_holeSet_iff {𝒵 : Set (PerfectMatching (Vertex m))}
    (h𝒵G : ∀ g ∈ autGroup m, ∀ P, g • P ∈ 𝒵 ↔ P ∈ 𝒵) {G : Finset (Vertex m)}
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) {g : Equiv.Perm (Vertex m)}
    (hg : g ∈ autGroup m) (P : PerfectMatching (Vertex m)) :
    g • P ∈ holeSet 𝒵 T0 K ↔ P ∈ holeSet 𝒵 T0 K := by
  simp only [holeSet, Set.mem_inter_iff, Set.mem_compl_iff,
    isEquivFamily_hamEvent.smul_mem_zeroSet_iff hg, h𝒵G g hg, smul_mem_ballOrbit_iff T0 K hg]

/-- **NG-A(b), the hole lemma** (`sqrt-m-obstructions.md` §1.2). Let `𝒵` be an
`Aut(𝓕)`-invariant set of zero states and `T0` a tail with `ρ_𝒵(T0) > K`. Put
`A′_t = A_t ∪ Rem` with `Rem = holeSet 𝒵 T0 K`. Then `𝓐′ ∈ 𝔈_m`, `Z(𝓐′) = Z ∖ Rem`,
`𝒵 ⊆ Z(𝓐′)`, and every zero state of `𝓐′` is more than `K` edges from `T0`, so
`N_m(𝓐′) ≥ ρ_{Z(𝓐′)}(T0) > K`. -/
theorem hole {𝒵 : Set (PerfectMatching (Vertex m))} (h𝒵 : 𝒵 ⊆ zeroSet (hamEvent m))
    (h𝒵G : ∀ g ∈ autGroup m, ∀ P, g • P ∈ 𝒵 ↔ P ∈ 𝒵) {G : Finset (Vertex m)}
    {T0 : PerfectMatching (Gᶜ : Finset (Vertex m))} {K : ℕ}
    (hT0 : ∀ P ∈ 𝒵, K < tailDist P T0) :
    IsEquivFamily (holeFamily (hamEvent m) (holeSet 𝒵 T0 K)) ∧
      zeroSet (holeFamily (hamEvent m) (holeSet 𝒵 T0 K)) =
        zeroSet (hamEvent m) \ holeSet 𝒵 T0 K ∧
      𝒵 ⊆ zeroSet (holeFamily (hamEvent m) (holeSet 𝒵 T0 K)) ∧
      ∀ P ∈ zeroSet (holeFamily (hamEvent m) (holeSet 𝒵 T0 K)), K < tailDist P T0 := by
  have hZ := zeroSet_holeFamily (hamEvent m) (holeSet 𝒵 T0 K)
  refine ⟨isEquivFamily_hamEvent.hole fun g hg P ↦ smul_mem_holeSet_iff h𝒵G T0 K hg P, hZ,
    fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  · rw [hZ]
    exact ⟨h𝒵 hP, fun h ↦ h.1.2 hP⟩
  · rw [hZ] at hP
    by_contra hd
    have hball : P ∈ ballOrbit T0 K := ⟨1, (one_mem (autGroup m) : _), by simpa using hd⟩
    by_cases hP𝒵 : P ∈ 𝒵
    · exact hd (hT0 P hP𝒵)
    · exact hP.2 ⟨⟨hP.1, hP𝒵⟩, hball⟩

/-- `|B_K(T0)| ≤ ∑_{j ≤ K + 3} C(m, j)(2j - 1)!!` for a tail `T0` of a six-vertex gadget
(`sqrt-m-obstructions.md` §0 and §1.2, the bound `δ_K` of NG-A(b)). -/
theorem card_ball_tail_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) :
    (Finset.univ.filter fun P : PerfectMatching (Vertex m) ↦ tailDist P T0 ≤ K).card ≤
      ∑ j ∈ Finset.range (K + 3 + 1), m.choose j * Nat.doubleFactorial (2 * j - 1) := by
  obtain ⟨Q, hQ⟩ := exists_extends (by rw [card_vertex]; exact even_two_mul m) T0
  refine le_trans (Finset.card_le_card fun P hP ↦ ?_) (card_defect_le Q (card_vertex m) (K + 3))
  have hd := (Finset.mem_filter.mp hP).2
  have h := card_defect_le_of_extends Q T0 hQ P
  rw [compl_compl, hG] at h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

/-- `Aut(𝓕)` as a finset of permutations. -/
def autFinset (m : ℕ) [NeZero m] : Finset (Equiv.Perm (Vertex m)) :=
  Finset.univ.filter (IsAut m)

/-- `|autFinset m| = |Aut(𝓕)|`. -/
theorem card_autFinset : (autFinset m).card = Nat.card (autGroup m) := by
  rw [autFinset, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

/-- `|⋃_{g ∈ G} g • B_K(T0)| ≤ |G| ∑_{j ≤ K + 3} C(m, j)(2j - 1)!!` (`sqrt-m-obstructions.md`
§1.2, NG-A(b)). -/
theorem card_ballOrbit_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) :
    (Finset.univ.filter (· ∈ ballOrbit T0 K)).card ≤
      Nat.card (autGroup m) *
        ∑ j ∈ Finset.range (K + 3 + 1), m.choose j * Nat.doubleFactorial (2 * j - 1) := by
  calc (Finset.univ.filter (· ∈ ballOrbit T0 K)).card
      ≤ ((autFinset m).biUnion fun g ↦
          Finset.univ.filter fun P : PerfectMatching (Vertex m) ↦
            tailDist (g⁻¹ • P) T0 ≤ K).card := by
        refine Finset.card_le_card fun P hP ↦ ?_
        obtain ⟨g, hg, hd⟩ := (Finset.mem_filter.mp hP).2
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩
    _ ≤ ∑ g ∈ autFinset m, (Finset.univ.filter fun P : PerfectMatching (Vertex m) ↦
          tailDist (g⁻¹ • P) T0 ≤ K).card :=
        Finset.card_biUnion_le
    _ = ∑ _g ∈ autFinset m, (Finset.univ.filter fun P : PerfectMatching (Vertex m) ↦
          tailDist P T0 ≤ K).card := by
        refine Finset.sum_congr rfl fun g _ ↦ Finset.card_equiv (MulAction.toPerm g⁻¹) fun P ↦ ?_
        simp
    _ ≤ ∑ _g ∈ autFinset m,
          ∑ j ∈ Finset.range (K + 3 + 1), m.choose j * Nat.doubleFactorial (2 * j - 1) :=
        Finset.sum_le_sum fun _ _ ↦ card_ball_tail_le hG T0 K
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, card_autFinset]

/-- **NG-A(b)**, the size of the hole (`sqrt-m-obstructions.md` §1.2). Under the uniform law,
`U(Rem) ≤ δ_K = |Aut(𝓕)| (K + 4)(2m)^(K + 3) / (2m - 1)!!`. -/
theorem prob_holeSet_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (𝒵 : Set (PerfectMatching (Vertex m))) (T0 : PerfectMatching (Gᶜ : Finset (Vertex m)))
    (K : ℕ) :
    prob (unifWeight m) (holeSet 𝒵 T0 K) ≤
      (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
        Nat.doubleFactorial (2 * m - 1) := by
  refine (prob_mono (isProb_unifWeight m) (Set.inter_subset_right :
    holeSet 𝒵 T0 K ⊆ ballOrbit T0 K)).trans ?_
  rw [prob_unifWeight, card_eq_doubleFactorial (card_vertex m)]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h := (card_ballOrbit_le hG T0 K).trans (Nat.mul_le_mul_left _
    (sum_choose_mul_doubleFactorial_le (le_refl m) (NeZero.pos m) (K + 3)))
  rw [show K + 3 + 1 = K + 4 by ring] at h
  exact_mod_cast h

/-- **NG-A(b) with Lemma R** (`sqrt-m-obstructions.md` §0, §1.2). For the hole family, every
event `E` on profiles has `|U(Y′ ∈ E) - U(Y ∈ E)| ≤ δ_K`, with
`δ_K = |Aut(𝓕)| (K + 4)(2m)^(K + 3) / (2m - 1)!!`. -/
theorem abs_prob_profile_hole_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (𝒵 : Set (PerfectMatching (Vertex m))) (T0 : PerfectMatching (Gᶜ : Finset (Vertex m)))
    (K : ℕ) (E : Set (ZMod (2 * m - 1) → Prop)) :
    |prob (unifWeight m) {P | (fun t ↦ P ∈ holeFamily (hamEvent m) (holeSet 𝒵 T0 K) t) ∈ E} -
        prob (unifWeight m) {P | (fun t ↦ P ∈ hamEvent m t) ∈ E}| ≤
      (Nat.card (autGroup m) * ((K + 4) * (2 * m) ^ (K + 3)) : ℝ) /
        Nat.doubleFactorial (2 * m - 1) :=
  (abs_prob_profile_sub_le (isProb_unifWeight m) _ _ E).trans (prob_holeSet_le hG 𝒵 T0 K)

/-- **NG-A(b)**, coverage profile (`sqrt-m-obstructions.md` §1.2). If no member of `Rem` lies
within `K` of the tail `T`, then `Z(𝓐′) ∩ B_K(T) = Z ∩ B_K(T)`. -/
theorem coverage_eq_of_far {𝒵 : Set (PerfectMatching (Vertex m))} {G : Finset (Vertex m)}
    (T0 T : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ)
    (hT : ∀ P ∈ holeSet 𝒵 T0 K, K < tailDist P T) :
    {P | P ∈ zeroSet (holeFamily (hamEvent m) (holeSet 𝒵 T0 K)) ∧ tailDist P T ≤ K} =
      {P | P ∈ zeroSet (hamEvent m) ∧ tailDist P T ≤ K} := by
  ext P
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, zeroSet_holeFamily, Set.mem_sdiff]
  constructor
  · rintro ⟨⟨h, -⟩, hd⟩
    exact ⟨h, hd⟩
  · rintro ⟨h, hd⟩
    exact ⟨⟨h, fun hR ↦ absurd hd (not_le.mpr (hT P hR))⟩, hd⟩

/-- **NG-A(b)**, coverage profile count (`sqrt-m-obstructions.md` §1.2). At most
`|Aut(𝓕)| ∑_{j ≤ 2K + 3} C(m - 3, j)(2j - 1)!!` tails `T` have a member of `⋃_g g • B_K(T0)`
within `K`. Off these tails `coverage_eq_of_far` applies. -/
theorem card_coverage_change_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (T0 : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ ballOrbit T0 K, tailDist P T ≤ K).card ≤
      Nat.card (autGroup m) *
        ∑ j ∈ Finset.range (2 * K + 3 + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  obtain ⟨Q, hQ⟩ := exists_extends (by rw [card_vertex]; exact even_two_mul m) T0
  calc (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ ballOrbit T0 K, tailDist P T ≤ K).card
      ≤ ((autFinset m).biUnion fun g ↦
          Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
            tailDist (g • Q) T ≤ 2 * K + 3).card := by
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
          tailDist (g • Q) T ≤ 2 * K + 3).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ autFinset m,
          ∑ j ∈ Finset.range (2 * K + 3 + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) :=
        Finset.sum_le_sum fun g _ ↦ card_tailDist_le (g • Q) hU (2 * K + 3)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, card_autFinset]

end RoundRobin.Canonical

end Pairing
