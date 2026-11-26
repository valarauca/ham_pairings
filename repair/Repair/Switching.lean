import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Repair.CycleStep

/-!
# Detailed balance of the 2-switch chain (COD-146)

This file formalizes the first equality of Identity A of the switching spike
(`results/switching-j0-spike.md`, ce14dda), the double counting of 2-switches between the zero
set `Z = L_0` and the level `L_1 = {X = 1}`.

* `PerfectMatching.IsSwitch P Q` : `P` and `Q` disagree at exactly four vertices. Then
  `P ∪ Q` on those four vertices is a 4-cycle, so `Q` comes from `P` by removing two `P`-edges
  and adding one of their two other rematchings. This is the move of the kernel `K` of §1, and the
  relation is symmetric (`PerfectMatching.isSwitch_comm`), which is the reversibility of `K` for
  the uniform law.
* `switchOut m P = D_out(P)`, the number of 2-switches from `P` into `L_1`, and
  `switchIn m Q = D_in(Q)`, the number of 2-switches from `Q` into `Z`.
* `sum_switchOut_eq_sum_switchIn` : `∑_{P ∈ Z} D_out(P) = ∑_{Q ∈ L_1} D_in(Q)`.
* `hamLaw_one_mul_meanSwitchIn` (Identity A, first equality, multiplied form) :
  `P_1 E[D_in | L_1] = P_0 E[D_out | Z]`.
* `hamLaw_one_div_hamLaw_zero` (Identity A, first equality) :
  `P_1 / P_0 = E[D_out | Z] / E[D_in | L_1]` when `P_0 > 0` and `E[D_in | L_1] > 0`.

The second equality of Identity A, `E[D_out | Z] / E[D_in | L_1] = 2 P_Z(c = 1) / P_{L_1}(c = 0)`,
rests on Lemma 1 of the spike (the effect of one switch on the cycles of `P ∪ F_t`, from
Theorem 11.1 of the archive). It is not formalized here.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Q` is a 2-switch of `P`: the two matchings disagree at exactly four vertices
(`results/switching-j0-spike.md` §1, the moves of the 2-switch kernel `K`). -/
def IsSwitch (P Q : PerfectMatching V) : Prop :=
  (univ.filter fun v ↦ P.mate v ≠ Q.mate v).card = 4

instance (P Q : PerfectMatching V) : Decidable (IsSwitch P Q) :=
  inferInstanceAs (Decidable (_ = 4))

/-- The 2-switch relation is symmetric, so the kernel `K` is symmetric and the uniform law is
reversible for it (`results/switching-j0-spike.md` §1). -/
theorem isSwitch_comm (P Q : PerfectMatching V) : IsSwitch P Q ↔ IsSwitch Q P := by
  unfold IsSwitch
  rw [filter_congr fun v _ ↦ ne_comm]

end PerfectMatching

namespace RoundRobin.Canonical

open Finset PerfectMatching

/-- `D_out(P)`, the number of 2-switches from `P` that land in `L_1 = {X = 1}`
(`results/switching-j0-spike.md`, Identity A). -/
def switchOut (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) : ℕ :=
  (univ.filter fun Q ↦ IsSwitch P Q ∧ hamCount m Q = 1).card

/-- `D_in(Q)`, the number of 2-switches from `Q` that land in `Z = {X = 0}`
(`results/switching-j0-spike.md`, Identity A). -/
def switchIn (m : ℕ) [NeZero m] (Q : PerfectMatching (Vertex m)) : ℕ :=
  (univ.filter fun P ↦ IsSwitch Q P ∧ hamCount m P = 0).card

/-- `E[D_out | Z]`, `0` when `Z` is empty (`results/switching-j0-spike.md`, Identity A). -/
noncomputable def meanSwitchOut (m : ℕ) [NeZero m] : ℝ :=
  (∑ P ∈ univ.filter fun P ↦ hamCount m P = 0, (switchOut m P : ℝ)) /
    (univ.filter fun P : PerfectMatching (Vertex m) ↦ hamCount m P = 0).card

/-- `E[D_in | L_1]`, `0` when `L_1` is empty (`results/switching-j0-spike.md`, Identity A). -/
noncomputable def meanSwitchIn (m : ℕ) [NeZero m] : ℝ :=
  (∑ Q ∈ univ.filter fun Q ↦ hamCount m Q = 1, (switchIn m Q : ℝ)) /
    (univ.filter fun Q : PerfectMatching (Vertex m) ↦ hamCount m Q = 1).card

/-- Double counting of the 2-switches between `Z` and `L_1` (`results/switching-j0-spike.md`,
proof of Identity A): `∑_{P ∈ Z} D_out(P) = ∑_{Q ∈ L_1} D_in(Q)`. -/
theorem sum_switchOut_eq_sum_switchIn (m : ℕ) [NeZero m] :
    ∑ P ∈ univ.filter (fun P ↦ hamCount m P = 0), switchOut m P =
      ∑ Q ∈ univ.filter (fun Q ↦ hamCount m Q = 1), switchIn m Q := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow IsSwitch
    (s := univ.filter fun P : PerfectMatching (Vertex m) ↦ hamCount m P = 0)
    (t := univ.filter fun Q : PerfectMatching (Vertex m) ↦ hamCount m Q = 1)
  refine (sum_congr rfl fun P _ ↦ ?_).trans (h.trans (sum_congr rfl fun Q _ ↦ ?_))
  · rw [switchOut, bipartiteAbove, filter_filter]
    congr 1
    exact filter_congr fun Q _ ↦ and_comm
  · rw [switchIn, bipartiteBelow, filter_filter]
    congr 1
    exact filter_congr fun P _ ↦ by rw [isSwitch_comm, and_comm]

/-- `(|S| / N) · (∑_S f / |S|) = ∑_S f / N`, also when `S` is empty
(`results/switching-j0-spike.md`, Identity A). -/
theorem card_div_mul_sum_div {α : Type*} (S : Finset α) (f : α → ℝ) (N : ℝ) :
    (S.card : ℝ) / N * ((∑ x ∈ S, f x) / S.card) = (∑ x ∈ S, f x) / N := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
  rw [div_mul_div_comm, mul_comm (S.card : ℝ), mul_div_mul_right _ _ this]

/-- Identity A of `results/switching-j0-spike.md`, first equality in multiplied form
(detailed balance of the 2-switch chain): `P_1 E[D_in | L_1] = P_0 E[D_out | Z]`. -/
theorem hamLaw_one_mul_meanSwitchIn (m : ℕ) [NeZero m] :
    hamLaw m 1 * meanSwitchIn m = hamLaw m 0 * meanSwitchOut m := by
  rw [hamLaw, hamLaw, meanSwitchIn, meanSwitchOut, card_div_mul_sum_div, card_div_mul_sum_div]
  congr 1
  exact_mod_cast (sum_switchOut_eq_sum_switchIn m).symm

/-- Identity A of `results/switching-j0-spike.md`, first equality:
`P_1 / P_0 = E[D_out | Z] / E[D_in | L_1]` when `P_0 > 0` and `E[D_in | L_1] > 0`. -/
theorem hamLaw_one_div_hamLaw_zero {m : ℕ} [NeZero m] (h0 : hamLaw m 0 ≠ 0)
    (hin : meanSwitchIn m ≠ 0) :
    hamLaw m 1 / hamLaw m 0 = meanSwitchOut m / meanSwitchIn m := by
  rw [div_eq_div_iff h0 hin, hamLaw_one_mul_meanSwitchIn, mul_comm]

end RoundRobin.Canonical

end Pairing
