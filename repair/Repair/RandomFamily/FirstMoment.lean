import Repair.DensityGlue
import Repair.RandomFamily.RepairBound

/-!
# The first moment of the zero-state count over all families (COD-272)

Source: `results/random-family-lb-extend.md` §1.2 (Lemma 2) and §5 items G3 and G4, and
`results/random-family-lb-contra.md` §1.1 and §1.2 (organize-archive fc1a04f), checked in
`results/random-family-lb-factcheck-extend.md` and `-contra.md` (2f3e50f). Put
`N = (2m - 1)!!`, the number of perfect matchings of `V_m`, and `D = 2^(m-1)(m-1)!`.

* `RandomFamily.card_ham_left` : every `P` has exactly `D` partners `X` with `Ham P X`, by
  `card_ham_eq` and `ham_comm`.
* `RandomFamily.card_not_ham` : so exactly `N - D` perfect matchings `X` have `¬Ham P X`.
* `RandomFamily.sum_card_zeroStates` : `∑_M |Z(M)| = N (N - D)^n` over all families
  `M : ι → PerfectMatching (Vertex m)`, with `n = |ι|`. Dividing by `N^(n+1)` gives
  `E q(M) = (1 - p)^n` for i.i.d. uniform `M_t`.
-/

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `#{X : Ham P X} = 2^(m-1)(m-1)!` for every perfect matching `P` of `V_m`
(`random-family-lb-extend.md` §1.2, Lemma 2, fc1a04f), from `card_ham_eq` and `ham_comm`. -/
theorem card_ham_left (P : PerfectMatching (Vertex m)) :
    (Finset.univ.filter fun X : PerfectMatching (Vertex m) ↦ Ham P X).card =
      2 ^ (m - 1) * (m - 1).factorial := by
  rw [Finset.filter_congr fun X _ ↦ ham_comm P X]
  exact card_ham_eq (NeZero.pos m) (card_vertex m) P

/-- `D = 2^(m-1)(m-1)! ≤ (2m - 1)!! = N`, so `p = D / N ≤ 1`. -/
theorem ham_count_le : 2 ^ (m - 1) * (m - 1).factorial ≤ Nat.doubleFactorial (2 * m - 1) := by
  rw [← card_ham_left (factor m 0), ← card_eq_doubleFactorial (card_vertex m)]
  exact Finset.card_filter_le _ _

/-- `#{X : ¬Ham P X} = (2m - 1)!! - 2^(m-1)(m-1)!` for every perfect matching `P` of `V_m`
(`random-family-lb-extend.md` §5 item G3, fc1a04f). -/
theorem card_not_ham (P : PerfectMatching (Vertex m)) :
    (Finset.univ.filter fun X : PerfectMatching (Vertex m) ↦ ¬Ham P X).card =
      Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun X ↦ Ham P X
  rw [card_ham_left, Finset.card_univ, card_eq_doubleFactorial (card_vertex m)] at h
  omega

/-- For a fixed `P`, exactly `(N - D)^n` families `M` have `P ∈ Z(M)`, since the condition
`¬Ham P (M t)` is a product over the coordinates (`random-family-lb-extend.md` §1.2, fc1a04f). -/
theorem card_isZeroState (ι : Type*) [Fintype ι] [DecidableEq ι] (P : PerfectMatching (Vertex m)) :
    (Finset.univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ IsZeroState M P).card =
      (Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial) ^ Fintype.card ι := by
  have h : (Finset.univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ IsZeroState M P) =
      Fintype.piFinset fun _ ↦ Finset.univ.filter fun X ↦ ¬Ham P X := by
    ext M
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    rfl
  rw [h, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, card_not_ham]

/-- Lemma 2 of `random-family-lb-extend.md` §1.2 (fc1a04f), the counting identity
`∑_M |Z(M)| = N (N - D)^n` over all families `M : ι → PerfectMatching (Vertex m)`, where
`N = (2m - 1)!!`, `D = 2^(m-1)(m-1)!` and `n = |ι|`. -/
theorem sum_card_zeroStates (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card =
      Nat.doubleFactorial (2 * m - 1) *
        (Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial) ^ Fintype.card ι := by
  calc ∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card
      = ∑ M : ι → PerfectMatching (Vertex m), ∑ P : PerfectMatching (Vertex m),
          if IsZeroState M P then 1 else 0 := by
        simp only [zeroStates, Finset.card_filter]
    _ = ∑ P : PerfectMatching (Vertex m), ∑ M : ι → PerfectMatching (Vertex m),
          if IsZeroState M P then 1 else 0 := Finset.sum_comm
    _ = ∑ P : PerfectMatching (Vertex m),
          (Finset.univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ IsZeroState M P).card := by
        simp only [Finset.card_filter]
    _ = Nat.doubleFactorial (2 * m - 1) *
          (Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial) ^
            Fintype.card ι := by
        rw [Finset.sum_congr rfl fun P _ ↦ card_isZeroState ι P, Finset.sum_const,
          Finset.card_univ, card_eq_doubleFactorial (card_vertex m), smul_eq_mul]

end RoundRobin.Canonical.RandomFamily

end Pairing
