import Mathlib.Analysis.Real.Sqrt
import Repair.SumCover

/-!
# The `O(√m)` repair bound (COD-165)

A six-vertex gadget is a set `G ⊆ V_m` with `|G| = 6`, and a tail for `G` is a partial matching
`T` of `V_m` with `uncovered T = G`, that is a perfect matching of `V_m \ G`.

* `L_eq_ceil_sqrt` : `SumCover.L q = ⌈√q⌉` for `q ≥ 1`.
* `exists_zeroForcing_core` : for `2m - 1 ≥ 257` some zero-forcing core has at most
  `4 ⌈√(2m - 1)⌉ - 3` edges, fewer than `m`.
* `repair_bound` : for `m ≥ 6`, every gadget and every tail `T`, some canonical zero state misses
  at most `min (m - 3) (8 ⌈√(2m - 1)⌉)` edges of `T`. So
  `N_m(G) ≤ min {m - 3, 8 ⌈√(2m - 1)⌉}`. For `m ≤ 128` this is the trivial bound from
  `nonempty_zeroState`, and for `m ≥ 129` it comes from the sum-cover core and `exists_repair`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- `SumCover.L q = Nat.sqrt (q - 1) + 1` is `⌈√q⌉` for `q ≥ 1`. -/
theorem L_eq_ceil_sqrt {q : ℕ} (hq : 1 ≤ q) : SumCover.L q = ⌈Real.sqrt q⌉₊ := by
  obtain ⟨h1, h2⟩ := SumCover.L_spec hq
  have hL := SumCover.L_pos (q := q)
  symm
  rw [Nat.ceil_eq_iff hL.ne']
  constructor
  · rw [Real.lt_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast (by rw [sq]; exact h1 : (SumCover.L q - 1) ^ 2 < q)
  · rw [Real.sqrt_le_left (Nat.cast_nonneg _)]
    exact_mod_cast (by rw [sq]; exact h2 : q ≤ SumCover.L q ^ 2)

/-- The real number `2m - 1` is the cast of the natural `2m - 1`, for `m ≥ 1`. -/
theorem cast_two_mul_sub_one (m : ℕ) [NeZero m] : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
  have := NeZero.pos m
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

variable {m : ℕ} [NeZero m]

/-- The sum-cover core as a zero-forcing core. For `q = 2m - 1 ≥ 257` some partial matching `A`
of `V_m` has `|A| ≤ 4 ⌈√(2m - 1)⌉ - 3` and `|A| < m`, and every perfect matching that contains
it is a canonical zero state. -/
theorem exists_zeroForcing_core (hq : 257 ≤ 2 * m - 1) :
    ∃ A : Finset (Sym2 (Vertex m)), IsPartialMatching A ∧
      A.card ≤ 4 * ⌈Real.sqrt (2 * m - 1)⌉₊ - 3 ∧ A.card < m ∧ IsZeroForcing (factor m) A := by
  obtain ⟨A, hA, hAcard, hAm, hB⟩ := SumCover.exists_sumCover_core hq
  have hV : Even (Fintype.card (Vertex m)) := by
    rw [card_vertex]
    exact even_two_mul m
  refine ⟨A, hA, ?_, hAm,
    isZeroForcing_of_blocks (uncovered_nonempty hV hA (by rw [card_vertex]; omega)) hB⟩
  rwa [← cast_two_mul_sub_one, ← L_eq_ceil_sqrt (by omega)]

/-- **COD-165.** For `m ≥ 6`, every six-vertex gadget `G` and every tail `T`, a perfect matching
of `V_m \ G`, some canonical zero state `P` misses at most `min (m - 3) (8 ⌈√(2m - 1)⌉)` edges
of `T`. That is, `N_m(G) ≤ min {m - 3, 8 ⌈√(2m - 1)⌉}`. -/
theorem repair_bound (hm : 6 ≤ m) (G : Finset (Vertex m)) (hG : G.card = 6)
    (T : Finset (Sym2 (Vertex m))) (hT : IsPartialMatching T) (hTG : uncovered T = G) :
    ∃ P : ZeroState m, (T.filter fun e ↦ e ∉ P.1.toGraph.edgeSet).card ≤
      min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊) := by
  have hV : Even (Fintype.card (Vertex m)) := by
    rw [card_vertex]
    exact even_two_mul m
  have hTcard : T.card = m - 3 := by
    have h := two_mul_card_eq hV hT
    rw [Finset.card_compl, card_vertex, hTG, hG] at h
    omega
  rw [← cast_two_mul_sub_one, ← L_eq_ceil_sqrt (by omega)]
  have hL := SumCover.L_spec (q := 2 * m - 1) (by omega)
  rcases Nat.lt_or_ge (2 * m - 1) 257 with hq | hq
  · obtain ⟨P⟩ := nonempty_zeroState hm
    refine ⟨P, le_min ((Finset.card_filter_le _ _).trans hTcard.le)
      ((Finset.card_filter_le _ _).trans ?_)⟩
    rw [hTcard]
    by_contra! h
    have h1 : 2 * m ≤ SumCover.L (2 * m - 1) * SumCover.L (2 * m - 1) + 1 := by omega
    have h2 : 8 * SumCover.L (2 * m - 1) + 4 ≤ m := by omega
    have h3 : m ≤ 128 := by omega
    nlinarith [Nat.mul_le_mul h2 h2, Nat.mul_le_mul_left m h3]
  · obtain ⟨A, hA, hAcard, hAm, hB⟩ := SumCover.exists_sumCover_core hq
    obtain ⟨P, hP, hcard⟩ := exists_zeroState_repair hV hA
      (isZeroForcing_of_blocks (uncovered_nonempty hV hA (by rw [card_vertex]; omega)) hB) hT
    exact ⟨⟨P, hP⟩, le_min ((Finset.card_filter_le _ _).trans hTcard.le)
      (hcard.trans (by omega))⟩

end RoundRobin.Canonical

end Pairing
