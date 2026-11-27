import Clifford.QuadraticForm
import Repair.RoundRobinSpan

/-!
# Hamiltonian cliques and perfect 1-factorizations at even `m` (COD-293)

Corollary C of `results/outside-applications-extend.md` §2 and Theorem Q of
`results/p1f-spin-extend.md` §1.2 (organize-archive d6e5620). Let `F : ι → 𝓜(V)` be a Hamiltonian
clique, `F_s ∪ F_t` one cycle exactly for `s ≠ t`, on `|V| = 2m` vertices with `m ≥ 4`. It has
`C(|ι|, 2)` Hamiltonian pairs, so the Hamiltonian-pair quadratic form (`hamQuad`,
`sum_rowW_ne_zero_of_odd`, ham-spin spin-q 87df892) gives `Σ_t φ(F_t) ≠ 0` when `C(|ι|, 2)` is
odd. The clique lemmas (`finrank_fpSpan_eq_card_iff`, ham_pairings main bf1e85b) then give
`dim R(F) = |ι|`.

* `card_hamPairs_of_clique` : a clique has `C(|ι|, 2)` Hamiltonian pairs under any linear order.
* `fpSum_ne_zero_of_clique`, `finrank_fpSpan_of_clique` : Corollary C, `dim R(F) = |ι|` when
  `C(|ι|, 2)` is odd, that is `|ι| ≡ 2, 3 (mod 4)`.
* `odd_choose_two_two_mul_sub_one` : `C(2m - 1, 2) = (2m - 1)(m - 1)` is odd for even `m`.
* `finrank_fpSpan_of_p1f` : a clique of `2m - 1` matchings, such as a perfect 1-factorization,
  has `dim R(F) = 2m - 1` at even `m ≥ 4`.
* `RoundRobin.Canonical.finrank_rrSpan_of_prime_of_even` : the check against
  `finrank_rrSpan_of_four_le` (ham_pairings main bf1e85b) at prime `2m - 1` and even `m`.
-/

namespace Pairing.PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- A Hamiltonian clique, `F_s ∪ F_t` one cycle iff `s ≠ t` (`Ham`, ham-spin e88ff2d), has
`C(|ι|, 2)` Hamiltonian pairs `s < t`, for any linear order on `ι`. -/
theorem card_hamPairs_of_clique [LinearOrder ι] {F : ι → PerfectMatching V}
    (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    #{p ∈ (univ : Finset ι) ×ˢ univ | p.1 < p.2 ∧ Ham (F p.1) (F p.2)} =
      (Fintype.card ι).choose 2 := by
  have h := Finset.card_product_filter_lt (s := (univ : Finset ι))
  rw [Finset.card_univ] at h
  rw [← h]
  congr 1
  refine Finset.filter_congr fun p _ ↦ ?_
  rw [hF]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.ne⟩⟩

/-- Corollary C of `results/outside-applications-extend.md` (organize-archive d6e5620), first
half. A Hamiltonian clique on `|V| = 2m`, `m ≥ 4`, with `C(|ι|, 2)` odd has `Σ_t φ(F_t) ≠ 0`
(`fpSum`; `sum_rowW_ne_zero_of_odd`, ham-spin spin-q 87df892). -/
theorem fpSum_ne_zero_of_clique {m : ℕ} (hV : Fintype.card V = 2 * m) (hm : 4 ≤ m)
    {F : ι → PerfectMatching V} (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hodd : Odd ((Fintype.card ι).choose 2)) : fpSum F ≠ 0 := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact sum_rowW_ne_zero_of_odd hV hm univ F (by rwa [card_hamPairs_of_clique hF])

/-- Corollary C of `results/outside-applications-extend.md` (organize-archive d6e5620). A
Hamiltonian clique on `|V| = 2m`, `m ≥ 4`, with `C(|ι|, 2)` odd has independent fingerprints,
`dim R(F) = |ι|` (`fpSpan`, ham-spin e88ff2d; `finrank_fpSpan_eq_card_iff`). -/
theorem finrank_fpSpan_of_clique {m : ℕ} (hV : Fintype.card V = 2 * m) (hm : 4 ≤ m)
    {F : ι → PerfectMatching V} (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hodd : Odd ((Fintype.card ι).choose 2)) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι := by
  have hne : Nonempty ι := by
    refine Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h ↦ ?_)
    simp [h] at hodd
  exact (finrank_fpSpan_eq_card_iff hF).mpr (fpSum_ne_zero_of_clique hV hm hF hodd)

/-- `C(2m - 1, 2) = (2m - 1)(m - 1)` is odd for even `m ≥ 1`. -/
theorem odd_choose_two_two_mul_sub_one {m : ℕ} (hm : 1 ≤ m) (heven : Even m) :
    Odd ((2 * m - 1).choose 2) := by
  obtain ⟨k, rfl⟩ := heven
  have h1 : 2 * (k + k) - 1 - 1 = 2 * (2 * k - 1) := by omega
  have h2 : (2 * (k + k) - 1).choose 2 = (2 * (k + k) - 1) * (2 * k - 1) := by
    rw [Nat.choose_two_right, h1]
    exact Nat.div_eq_of_eq_mul_left two_pos (by ring)
  rw [h2]
  exact Nat.odd_mul.mpr ⟨⟨2 * k - 1, by omega⟩, ⟨k - 1, by omega⟩⟩

/-- Theorem Q of `results/p1f-spin-extend.md` and Corollary C of
`results/outside-applications-extend.md` (organize-archive d6e5620). On `|V| = 2m` with `m` even
and `m ≥ 4`, a family of `2m - 1` pairwise Hamiltonian distinct matchings, for example a perfect
1-factorization, has `dim R(F) = 2m - 1` (`fpSpan`, `Ham`, ham-spin e88ff2d). -/
theorem finrank_fpSpan_of_p1f {m : ℕ} (hV : Fintype.card V = 2 * m) (hm : 4 ≤ m)
    (heven : Even m) {F : ι → PerfectMatching V} (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hι : Fintype.card ι = 2 * m - 1) : Module.finrank F₂ (fpSpan F) = 2 * m - 1 := by
  rw [← hι]
  refine finrank_fpSpan_of_clique hV hm hF ?_
  rw [hι]
  exact odd_choose_two_two_mul_sub_one (by omega) heven

end Pairing.PerfectMatching

namespace Pairing.RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `dim R_rr = 2m - 1` at prime `2m - 1` and even `m ≥ 4` (`rrSpan`, `factor`, ham-spin
e88ff2d), from `finrank_fpSpan_of_p1f` and the clique `ham_factor_iff_ne`. This rederives the
even prime cases of `finrank_rrSpan_of_four_le` (ham_pairings main bf1e85b) without the ladders. -/
theorem finrank_rrSpan_of_prime_of_even (hp : (2 * m - 1).Prime) (hm : 4 ≤ m) (heven : Even m) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 1 :=
  finrank_fpSpan_of_p1f (card_vertex m) hm heven (ham_factor_iff_ne hp) (ZMod.card _)

end Pairing.RoundRobin.Canonical
