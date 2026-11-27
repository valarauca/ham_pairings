import Repair.SqrtObstructions.ClassCount

/-!
# Repair bounds for an arbitrary family of perfect matchings (COD-272)

Source: `results/random-family-lb-extend.md` §1.1 and §5 items G1 and G2, and
`results/random-family-lb-contra.md` §1.4 and §5 (organize-archive fc1a04f), checked in
`results/random-family-lb-factcheck-extend.md` and `-contra.md` (2f3e50f).

A family is `M : ι → PerfectMatching (Vertex m)`. Its zero states `Z(M)` are the perfect matchings
`P` with `¬Ham P (M t)` for every `t`. For a class `𝒵` and a six-vertex gadget `G`,
`RepairBoundFor 𝒵 G K` says that every tail is within `K` edges of a member of `𝒵`. With
`𝒵 = Z(M)` this is `N(M, G) ≤ K`. Put `S_K(m) = ∑_{j ≤ K} C(m - 3, j)(2j - 1)!!`.

* `RandomFamily.zeroStates M` : the finset `Z(M)`.
* `RandomFamily.RepairBoundFor 𝒵 G K` : `N(𝒵, G) ≤ K`.
* `RandomFamily.repairBoundFor_zeroStates_factor_iff` : for the round-robin family `F_t` it is
  `RepairBound m G K`.
* `RandomFamily.doubleFactorial_le_card_mul` (Lemma 1(b)) : if `N(𝒵, G) ≤ K`, then
  `(2m - 1)!! ≤ |𝒵| (2m - 1)(2m - 3)(2m - 5) S_K(m)`.
* `RandomFamily.doubleFactorial_le_card_zeroStates_mul` : the same for `𝒵 = Z(M)`.
* `RandomFamily.zeroStates_density_ge` (Lemma 1(c)) : if `N(M, G) ≤ K`, then
  `|Z(M)| / (2m - 1)!! ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`.
-/

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The zero states `Z(M)` of a family `M` (`random-family-lb-extend.md` §0, fc1a04f): the
perfect matchings `P` with `¬Ham P (M t)` for every `t`. -/
def zeroStates {ι : Type*} [Fintype ι] (M : ι → PerfectMatching (Vertex m)) :
    Finset (PerfectMatching (Vertex m)) :=
  Finset.univ.filter (IsZeroState M)

/-- `P ∈ Z(M)` iff `P` is a zero state of `M`. -/
theorem mem_zeroStates {ι : Type*} [Fintype ι] {M : ι → PerfectMatching (Vertex m)}
    {P : PerfectMatching (Vertex m)} : P ∈ zeroStates M ↔ IsZeroState M P := by
  simp [zeroStates]

/-- `N(𝒵, G) ≤ K` for a class `𝒵` and a gadget `G` (`random-family-lb-extend.md` §5 item G1,
fc1a04f): every tail, a perfect matching `T` of `V_m ∖ G`, has some `P ∈ 𝒵` with
`|T ∖ P| ≤ K`. -/
def RepairBoundFor (𝒵 : Finset (PerfectMatching (Vertex m))) (G : Finset (Vertex m)) (K : ℕ) :
    Prop :=
  ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), ∃ P ∈ 𝒵, tailDist P T ≤ K

/-- `RepairBound m G K` is the round-robin instance of `RepairBoundFor`: it is
`RepairBoundFor (Z(F)) G K` for the canonical factors `F_t` (`random-family-lb-extend.md` §1.1,
fc1a04f). -/
theorem repairBoundFor_zeroStates_factor_iff (G : Finset (Vertex m)) (K : ℕ) :
    RepairBoundFor (zeroStates (factor m)) G K ↔ RepairBound m G K :=
  ⟨fun h T ↦ let ⟨P, hP, hd⟩ := h T; ⟨⟨P, mem_zeroStates.mp hP⟩, hd⟩,
    fun h T ↦ let ⟨P, hd⟩ := h T; ⟨P.1, mem_zeroStates.mpr P.2, hd⟩⟩

/-- `S_K(m) = ∑_{j ≤ K} C(m - 3, j)(2j - 1)!!`, the ball bound of the counting lemma
(`random-family-lb-extend.md` §0, fc1a04f). -/
def ballBound (m K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1)

/-- `S_K(m) ≤ (K + 1)(2m)^K` (`random-family-lb-extend.md` §0 item L4, fc1a04f). -/
theorem ballBound_le (K : ℕ) : ballBound m K ≤ (K + 1) * (2 * m) ^ K :=
  sum_choose_mul_doubleFactorial_le (Nat.sub_le m 3) (NeZero.pos m) K

/-- Lemma 1(b) of `random-family-lb-extend.md` §1.1 (fc1a04f), from `class_count`. If
`N(𝒵, G) ≤ K` for a six-vertex gadget `G`, then
`(2m - 1)!! ≤ |𝒵| (2m - 1)(2m - 3)(2m - 5) S_K(m)`. -/
theorem doubleFactorial_le_card_mul {𝒵 : Finset (PerfectMatching (Vertex m))}
    {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ} (hK : RepairBoundFor 𝒵 G K) :
    Nat.doubleFactorial (2 * m - 1) ≤
      𝒵.card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  rw [doubleFactorial_two_mul_sub_one_eq h3]
  calc (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * Nat.doubleFactorial (2 * m - 7)
      ≤ (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (𝒵.card * ballBound m K) :=
        Nat.mul_le_mul_left _ (class_count hG hK).1
    _ = 𝒵.card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) := by ring

/-- The family form of the counting lemma (`random-family-lb-extend.md` §1.1, Lemma 1(b),
fc1a04f). If `N(M, G) ≤ K` for a family `M` and a six-vertex gadget `G`, then
`(2m - 1)!! ≤ |Z(M)| (2m - 1)(2m - 3)(2m - 5) S_K(m)`. -/
theorem doubleFactorial_le_card_zeroStates_mul {ι : Type*} [Fintype ι]
    (M : ι → PerfectMatching (Vertex m)) {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ}
    (hK : RepairBoundFor (zeroStates M) G K) :
    Nat.doubleFactorial (2 * m - 1) ≤
      (zeroStates M).card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) :=
  doubleFactorial_le_card_mul hG hK

/-- Lemma 1(c) of `random-family-lb-extend.md` §1.1 (fc1a04f), from `class_density_ge`. If
`N(M, G) ≤ K` for a family `M` and a six-vertex gadget `G`, then
`q(M) = |Z(M)| / (2m - 1)!! ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`. -/
theorem zeroStates_density_ge {ι : Type*} [Fintype ι] (M : ι → PerfectMatching (Vertex m))
    {G : Finset (Vertex m)} (hG : G.card = 6) {K : ℕ} (hK : RepairBoundFor (zeroStates M) G K) :
    1 / ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K : ℝ) ≤
      ((zeroStates M).card : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) :=
  class_density_ge hG hK

end RoundRobin.Canonical.RandomFamily

end Pairing
