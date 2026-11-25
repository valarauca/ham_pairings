import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Repair.SqrtBound
import Suppression.Density

/-!
# The repair-based density floor (COD-181)

`repair_bound` (COD-165) bounds `N_m(G)` for tails given as partial matchings `T` of `V_m` with
`uncovered T = G`. `density_ge` (COD-155) takes `RepairBound m G K`, whose tails are perfect
matchings of `V_m ∖ G`. This file bridges the two forms of a tail and composes the theorems.

* `isPartialMatching_tailEdges`, `uncovered_tailEdges` : the edges of a perfect matching of
  `U ⊆ V` form a partial matching of `V` that leaves exactly `V ∖ U` uncovered.
* `RoundRobin.Canonical.repairBound` : for `m ≥ 6` and every six-vertex gadget `G`,
  `RepairBound m G (min (m - 3) (8 ⌈√(2m - 1)⌉))`.
* `RoundRobin.Canonical.density_ge_repair` : for every `m ≥ 6`,
  `q_m ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)` with `K = min (m - 3) (8 ⌈√(2m - 1)⌉)`.
* `RoundRobin.Canonical.doubleFactorial_le_zeroCount_mul_pow_repair` : for every `m ≥ 6`,
  `(2m - 1)!! ≤ Z_m (2m)^(8 ⌈√(2m - 1)⌉ + 4)`.
* `RoundRobin.Canonical.density_ge_repair_rpow` : for every `m ≥ 6`,
  `q_m ≥ (2m)^-(8 ⌈√(2m - 1)⌉ + 4)`.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The edges of a perfect matching `T` of `U ⊆ V` form a partial matching of `V`. -/
theorem isPartialMatching_tailEdges {U : Finset V} (T : PerfectMatching U) :
    IsPartialMatching (tailEdges T) := by
  refine ⟨fun e he ↦ ?_, fun e he f hf x hxe hxf ↦ ?_⟩
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp he
    exact fun h ↦ T.mate_ne u (Subtype.ext (Sym2.mk_isDiag_iff.mp h).symm)
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hf
    rcases Sym2.mem_iff.mp hxe with rfl | rfl <;> rcases Sym2.mem_iff.mp hxf with h | h
    · rw [Subtype.ext h]
    · rw [Subtype.ext h, mate_mate, Sym2.eq_swap]
    · rw [← Subtype.ext h, mate_mate, Sym2.eq_swap]
    · rw [T.mate.injective (Subtype.ext h)]

/-- A perfect matching `T` of `U ⊆ V` leaves exactly `V ∖ U` uncovered. -/
theorem uncovered_tailEdges {U : Finset V} (T : PerfectMatching U) :
    uncovered (tailEdges T) = Uᶜ := by
  ext v
  rw [mem_uncovered, Finset.mem_compl]
  constructor
  · intro h hv
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ ⟨v, hv⟩)) (Sym2.mem_mk_left _ _)
  · rintro hv e he hve
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp he
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact hv u.2
    · exact hv (T.mate u).2

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- COD-165 in the form of COD-155. For `m ≥ 6` and every six-vertex gadget `G`, every tail, a
perfect matching of `V_m ∖ G`, is within `min (m - 3) (8 ⌈√(2m - 1)⌉)` edges of a zero state. -/
theorem repairBound (hm : 6 ≤ m) {G : Finset (Vertex m)} (hG : G.card = 6) :
    RepairBound m G (min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊)) := fun T ↦
  repair_bound hm G hG (tailEdges T) (isPartialMatching_tailEdges T)
    (by rw [uncovered_tailEdges, compl_compl])

/-- `V_m` has a six-vertex gadget for `m ≥ 3`. -/
theorem exists_gadget (hm : 3 ≤ m) : ∃ G : Finset (Vertex m), G.card = 6 := by
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Vertex m)))
    (n := 6) (by rw [Finset.card_univ, card_vertex]; omega)
  exact ⟨G, hG⟩

/-- The repair-based density floor (COD-181 (A)). For every `m ≥ 6`, with
`K = min (m - 3) (8 ⌈√(2m - 1)⌉)`, `q_m ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`. -/
theorem density_ge_repair (hm : 6 ≤ m) :
    1 / ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) *
        ((min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊) : ℕ) + 1) *
        (2 * m) ^ min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊) : ℝ) ≤
      (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  obtain ⟨G, hG⟩ := exists_gadget (m := m) (by omega)
  exact density_ge hG (repairBound hm hG)

/-- The repair-based floor in natural numbers. For every `m ≥ 6`,
`(2m - 1)!! ≤ Z_m (2m)^(8 ⌈√(2m - 1)⌉ + 4)`. -/
theorem doubleFactorial_le_zeroCount_mul_pow_repair (hm : 6 ≤ m) :
    Nat.doubleFactorial (2 * m - 1) ≤
      zeroCount m * (2 * m) ^ (8 * ⌈Real.sqrt (2 * m - 1)⌉₊ + 4) := by
  obtain ⟨G, hG⟩ := exists_gadget (m := m) (by omega)
  refine (doubleFactorial_le_zeroCount_mul hG (repairBound hm hG)).trans
    (Nat.mul_le_mul_left _ ?_)
  calc (2 * m - 1) * (2 * m - 3) * (2 * m - 5) *
        (min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊) + 1) *
        (2 * m) ^ min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊)
      ≤ (2 * m) * (2 * m) * (2 * m) * (2 * m) *
          (2 * m) ^ (8 * ⌈Real.sqrt (2 * m - 1)⌉₊) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
          (by omega)) (by omega)) (Nat.pow_le_pow_right (by omega) (min_le_right _ _))
    _ = (2 * m) ^ (8 * ⌈Real.sqrt (2 * m - 1)⌉₊ + 4) := by ring

/-- The repair-based density floor in closed form (COD-181 (A)). For every `m ≥ 6`,
`q_m ≥ (2m)^-(8 ⌈√(2m - 1)⌉ + 4)`. -/
theorem density_ge_repair_rpow (hm : 6 ≤ m) :
    (2 * m : ℝ) ^ (-(8 * ⌈Real.sqrt (2 * m - 1)⌉₊ + 4 : ℝ)) ≤
      (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  have h := doubleFactorial_le_zeroCount_mul_pow_repair hm
  have h2m : (0 : ℝ) < 2 * m := by
    have : (6 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [show (8 * ⌈Real.sqrt (2 * m - 1)⌉₊ + 4 : ℝ) =
      ((8 * ⌈Real.sqrt (2 * m - 1)⌉₊ + 4 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg h2m.le, Real.rpow_natCast, ← one_div,
    div_le_div_iff₀ (by positivity) (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)), one_mul]
  exact_mod_cast h

end RoundRobin.Canonical

end Pairing
