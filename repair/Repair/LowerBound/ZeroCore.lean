import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Repair.Cover.NCycle
import Repair.FactorCap.Tail
import Repair.LowerBound.Arc

/-!
# `N_m ≥ 1` for every `m ≥ 6`: the zero core of the factor tail is bad

Source: `results/struct-lb-contra.md` Theorem 1 and `results/struct-lb-extend.md` Theorem A, with
the corrections of `results/struct-lb-factcheck-contra.md` §1 and §4 and
`results/struct-lb-factcheck-extend.md` §2 (organize-archive b5cb45e). The scripts are
`scripts/struct-lb-c-cert.py` and `scripts/struct-lb-e-k1.out` (b5cb45e).

Put `n = 2m - 1`, `s0 = 7/2` and `T(n) = F_{s0} ∖ {16, 25, 34}`. A perfect matching `P` at
distance `0` from `T(n)` is `T(n) ∪ R` for a matching `R` of the gadget `G0 = {1, …, 6}`. The
claim is that some round-robin factor `F_t` makes `P ∪ F_t` one cycle, for every `R` and every
odd `n ≥ 11`.

**The walk.** By Theorem S (`RoundRobin.ham_factor_iff_sameCycle`), `P ∪ F_t` is one cycle iff
`σ = F̃_t P̃` is an `n`-cycle. Put `d = 2t - 7`. Off `G0`, `σ y = y + d`. In the coordinate
`y = s0 + v d` the map `σ` is the translation `v ↦ v + 1`, with a jump at each gadget point.
The gadget point `k` sits at a position `q` with `q D ≡ 2k - 7 (mod n)`, where `D = 2d`.
`sameCycle_of_arcs` turns the cyclic order of the six positions into a finite check on `Fin 6`.

**The four factors.** `D = 1, -1, 4, 8`, that is the multipliers `μ = D⁻¹ = 1, -1, 4⁻¹, 8⁻¹` of
the source, a four-element subfamily of the six units `±1, ±4⁻¹, ±8⁻¹` of contra Theorem 1. For
`D = ±1` the positions are `±(2k - 7)` at every `n`. For `D = 4, 8` they are linear in `b`, where
`n = 8b + c`, and the residue `c` fixes the cyclic order (`ordFour`, `ordEight`).
`coverGoal_table` checks that the four orders cover all fifteen `R`, in each residue class.
The contra's remark that a `K = 1` proof must use the `1/8`-cells is wrong
(`struct-lb-factcheck-contra.md` §4, item 8). The corrected statement there is that among the
multipliers `±(2^k)⁻¹` only `±8⁻¹` closes the cover with no residue split, and that is why
`D = 8` is used here.

* `ham_of_chart` : the walk, for one factor and one cyclic order of the gadget.
* `exists_ham_of_agree` : for every odd `n ≥ 11` and every `P` that agrees with `F_{s0}` off
  `G0`, some `P ∪ F_t` is one cycle.
* `one_le_tailDist_factorTail` : every zero state differs from `T(n)` in at least one edge,
  `ρ(T(n)) ≥ 1`.
* `not_repairBound_zero` : `N_m ≥ 1` for every `m ≥ 6`, as `¬ RepairBound m G0 0`.
-/

namespace Pairing

namespace LowerBound

open Equiv PerfectMatching RoundRobin

variable {n : ℕ}

/-- The gadget vertex `j + 1` of `G0 = {1, …, 6}`, as a point of `ℤ/n`
(`results/struct-lb-contra.md` §1, organize-archive b5cb45e). -/
def gadgetPt (n : ℕ) (j : Fin 6) : ZMod n :=
  (((j : ℕ) + 1 : ℕ) : ZMod n)

/-- The six gadget points are distinct for `n > 6` (`results/struct-lb-contra.md` §1,
organize-archive b5cb45e). -/
theorem gadgetPt_injective (hn : 6 < n) : Function.Injective (gadgetPt n) := by
  intro a b h
  rw [gadgetPt, gadgetPt, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h
  exact Fin.ext (by omega)

/-- `F_{s0}` swaps the gadget points `j + 1` and `6 - j`, which is `7 - (j + 1)`
(`results/struct-lb-contra.md` §1, organize-archive b5cb45e). -/
theorem gadgetPt_rev (j : Fin 6) : gadgetPt n (Fin.rev j) = 7 - gadgetPt n j := by
  fin_cases j <;> simp [gadgetPt] <;> norm_num

/-- An integer that vanishes mod `n` and has absolute value below `n` is zero
(`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem eq_zero_of_intCast_eq_zero {z : ℤ} (hz : (z : ZMod n) = 0) (hlt : |z| < n) : z = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp hz) hlt

/-- The centre `s0 = 7/2` is not a gadget point for `n ≥ 11` (`results/struct-lb-contra.md` §1,
organize-archive b5cb45e). -/
theorem ne_gadgetPt_of_two_mul (h11 : 11 ≤ n) {s0 : ZMod n} (hs0 : 2 * s0 = 7) (j : Fin 6) :
    s0 ≠ gadgetPt n j := by
  intro h
  have hz : ((2 * (j : ℤ) - 5 : ℤ) : ZMod n) = 0 := by
    rw [h, gadgetPt] at hs0
    push_cast at hs0 ⊢
    linear_combination hs0
  have := eq_zero_of_intCast_eq_zero hz (by rw [abs_lt]; constructor <;> omega)
  omega

/-- **The gadget part of `P`** (`results/struct-lb-contra.md` §1, organize-archive b5cb45e). If
`P` agrees with `F_{s0}` off `G0`, then `P` maps `G0` to itself, by a fixed-point-free involution
`r` of the six indices. -/
theorem exists_gadget_mate (hn : Odd n) (h11 : 11 ≤ n) {s0 : ZMod n} (hs0 : 2 * s0 = 7)
    {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → P.mate v = (factor hn s0).mate v) :
    ∃ r : Fin 6 → Fin 6, (∀ j, P.mate (some (gadgetPt n j)) = some (gadgetPt n (r j))) ∧
      (∀ j, r (r j) = j) ∧ ∀ j, r j ≠ j := by
  have hnone : P.mate none = some s0 := by
    rw [hP none (fun j h ↦ by simp at h), factor_mate, mateFn_none]
  have hex : ∀ j, ∃ k, P.mate (some (gadgetPt n j)) = some (gadgetPt n k) := by
    intro j
    rcases hw : P.mate (some (gadgetPt n j)) with _ | y
    · exfalso
      have h1 : P.mate none = some (gadgetPt n j) := by rw [← hw, mate_mate]
      rw [hnone, Option.some_inj] at h1
      exact ne_gadgetPt_of_two_mul h11 hs0 j h1
    · by_contra hcon
      have hy : ∀ k, some y ≠ some (gadgetPt n k) := fun k h ↦ hcon ⟨k, h⟩
      have h1 := hP (some y) hy
      have h2 : P.mate (some y) = some (gadgetPt n j) := by rw [← hw, mate_mate]
      by_cases hys : y = s0
      · rw [hys, factor_mate, mateFn_self] at h1
        rw [hys, h1] at h2
        simp at h2
      · rw [factor_mate, mateFn_of_ne _ _ hys, h2, Option.some_inj, hs0] at h1
        apply hy (Fin.rev j)
        rw [gadgetPt_rev, h1]
        ring_nf
  choose r hr using hex
  refine ⟨r, hr, fun j ↦ ?_, fun j h ↦ ?_⟩
  · have h1 := P.mate_mate (some (gadgetPt n j))
    rw [hr, hr, Option.some_inj] at h1
    exact gadgetPt_injective (by omega) h1
  · have h1 := P.mate_ne (some (gadgetPt n j))
    rw [hr, h] at h1
    exact h1 rfl

/-- The arc map `i ↦ ρ (i + 1)` of `sameCycle_of_arcs`, for the cyclic order `ord` of the gadget
points and the gadget matching `r`. Here `ρ i = ord⁻¹ (rev (r (ord i)))`, because
`F̃_{s0} P̃` sends the gadget point `k` to `7 - r k` (`results/struct-lb-contra.md` Theorem 1,
organize-archive b5cb45e). -/
def arcStep (ord ordInv r : Fin 6 → Fin 6) (i : Fin 6) : Fin 6 :=
  ordInv (Fin.rev (r (ord (i + 1))))

/-- The cyclic order `ord` covers `r`: the arc map runs through all six arcs. This is "`R` is one
cycle with the cell context" of `results/struct-lb-contra.md` §1 (organize-archive b5cb45e). -/
def Covers (ord ordInv r : Fin 6 → Fin 6) : Prop :=
  ∀ j, ∃ k : Fin 6, (arcStep ord ordInv r)^[k] 0 = j

instance (ord ordInv r : Fin 6 → Fin 6) : Decidable (Covers ord ordInv r) :=
  inferInstanceAs (Decidable (∀ _j, ∃ _k : Fin 6, _))

/-- **One factor, one cyclic order** (`results/struct-lb-contra.md` Theorem 1 and
`results/struct-lb-extend.md` Theorem A, organize-archive b5cb45e). Let `P` agree with `F_{s0}`
off `G0`, with gadget matching `r`. Let `2(2t - 7) = D` with `D` a unit. Let `q` be strictly
increasing with `q 5 < q 0 + n`, and `q i D = 2 ord(i) - 5 + n w(i)`, so that the gadget point
`ord(i) + 1` sits at position `q i`. If the order `ord` covers `r`, then `P ∪ F_t` is one
cycle. -/
theorem ham_of_chart (hn : Odd n) [NeZero n] {s0 t : ZMod n} (hs0 : 2 * s0 = 7)
    {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → P.mate v = (factor hn s0).mate v)
    {r : Fin 6 → Fin 6} (hr : ∀ j, P.mate (some (gadgetPt n j)) = some (gadgetPt n (r j)))
    {D : ℤ} (hD : IsUnit (D : ZMod n)) (ht : 2 * (2 * t - 7) = D)
    {q w : Fin 6 → ℤ} (hq : StrictMono q) (hqn : q 5 < q 0 + n)
    {ord ordInv : Fin 6 → Fin 6} (hord' : ∀ j, ord (ordInv j) = j)
    (hpos : ∀ i, q i * D = 2 * ((ord i : ℕ) : ℤ) - 5 + n * w i)
    (hcov : Covers ord ordInv r) : Ham P (factor hn t) := by
  rw [ham_factor_iff_sameCycle]
  intro x y
  have hdu : IsUnit (2 * t - 7) := isUnit_of_mul_isUnit_right (ht ▸ hD)
  obtain ⟨u, hu⟩ : ∃ u, u * (2 * t - 7) = 1 := ⟨_, hdu.val_inv_mul⟩
  set e : ℤ → ZMod n := fun v ↦ s0 + v * (2 * t - 7) with he
  have hgad : ∀ i, e (q i) = gadgetPt n (ord i) := by
    intro i
    apply (isUnit_two hn).mul_left_cancel
    have hp := congrArg (fun z : ℤ ↦ (z : ZMod n)) (hpos i)
    push_cast [ZMod.natCast_self] at hp
    rw [← ht] at hp
    simp only [he, gadgetPt]
    push_cast
    linear_combination hp + hs0
  have hpin : ∀ y : ZMod n, P.mate (some y) = (factor hn s0).mate (some y) →
      pinned P y = 2 * s0 - y := by
    intro y hy
    rw [← pinned_factor hn s0 y]
    simp only [pinned, Function.Involutive.coe_toPerm, pinnedFn, hy]
  refine sameCycle_of_arcs (r := 5) _ e ?_ ?_ ?_ q hq hqn
    (fun i ↦ ordInv (Fin.rev (r (ord i)))) ?_ ?_ (fun j ↦ ?_) x y
  · intro v k
    simp only [he]
    push_cast [ZMod.natCast_self]
    ring
  · intro z
    refine ⟨(((z - s0) * u : ZMod n).val : ℤ), ?_⟩
    simp only [he, Int.cast_natCast, ZMod.natCast_zmod_val]
    linear_combination (z - s0) * hu
  · intro v v' h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [he] at h
    push_cast
    linear_combination u * h + ((v' : ZMod n) - v) * hu
  · intro v hv
    have hng : ∀ j, some (e v) ≠ some (gadgetPt n j) := by
      intro j h
      apply hv (ordInv j)
      rw [hgad, hord', Option.some_inj.mp h]
    rw [Perm.mul_apply, hpin _ (hP _ hng), pinned_factor]
    simp only [he]
    push_cast
    linear_combination -hs0
  · intro i
    have hshift : e (q (ordInv (Fin.rev (r (ord i)))) + 1) =
        e (q (ordInv (Fin.rev (r (ord i))))) + (2 * t - 7) := by
      simp only [he]
      push_cast
      ring
    rw [hshift, hgad, hgad, hord', gadgetPt_rev, Perm.mul_apply,
      pinned_apply_of_mate_eq_some P (hr _), pinned_factor]
    ring
  · obtain ⟨k, hk⟩ := hcov j
    exact ⟨k, hk⟩

/-- Some `t` has `2(2t - 7) = D`, since `2` is a unit for odd `n` (`results/struct-lb-contra.md`
Theorem 1, organize-archive b5cb45e: the factor `t = s0 + D/4` of multiplier `μ = D⁻¹`). -/
theorem exists_two_mul_two_mul_sub (hn : Odd n) (D : ZMod n) :
    ∃ t : ZMod n, 2 * (2 * t - 7) = D := by
  obtain ⟨u, hu⟩ : ∃ u : ZMod n, u * 2 = 1 := ⟨_, (isUnit_two hn).val_inv_mul⟩
  refine ⟨(D * u + 7) * u, ?_⟩
  linear_combination (D * (2 * u + 1) + 14) * hu

/-- The cyclic order of the gadget for `D = 1`: positions `-5, -3, -1, 1, 3, 5` hold the gadget
points `1, …, 6` (`results/struct-lb-contra.md` Theorem 1, `μ = 1`, organize-archive b5cb45e). -/
def ordOne : Fin 6 → Fin 6 :=
  ![0, 1, 2, 3, 4, 5]

/-- The cyclic order of the gadget for `D = -1`: positions `-5, …, 5` hold the gadget points
`6, …, 1` (`results/struct-lb-contra.md` Theorem 1, `μ = -1`, organize-archive b5cb45e). -/
def ordNegOne : Fin 6 → Fin 6 :=
  ![5, 4, 3, 2, 1, 0]

/-- The cyclic order of the gadget for `D = 4` and `n = 8b + 2c + 1`
(`results/struct-lb-contra.md` Theorem 1, `μ = 4⁻¹`, organize-archive b5cb45e). -/
def ordFour (c : Fin 4) : Fin 6 → Fin 6 :=
  ![![1, 3, 5, 0, 2, 4], ![0, 2, 4, 1, 3, 5], ![1, 3, 5, 0, 2, 4], ![0, 2, 4, 1, 3, 5]] c

/-- The inverse of `ordFour c` (`results/struct-lb-contra.md` Theorem 1, organize-archive
b5cb45e). -/
def ordFourInv (c : Fin 4) : Fin 6 → Fin 6 :=
  ![![3, 0, 4, 1, 5, 2], ![0, 3, 1, 4, 2, 5], ![3, 0, 4, 1, 5, 2], ![0, 3, 1, 4, 2, 5]] c

/-- The cyclic order of the gadget for `D = 8` and `n = 8b + 2c + 1`
(`results/struct-lb-contra.md` Theorem 1, `μ = 8⁻¹`, organize-archive b5cb45e). -/
def ordEight (c : Fin 4) : Fin 6 → Fin 6 :=
  ![![0, 4, 3, 2, 1, 5], ![3, 0, 4, 1, 5, 2], ![2, 1, 5, 0, 4, 3], ![1, 5, 2, 3, 0, 4]] c

/-- The inverse of `ordEight c` (`results/struct-lb-contra.md` Theorem 1, organize-archive
b5cb45e). -/
def ordEightInv (c : Fin 4) : Fin 6 → Fin 6 :=
  ![![0, 4, 3, 2, 1, 5], ![1, 3, 5, 0, 2, 4], ![3, 1, 0, 5, 4, 2], ![4, 0, 2, 3, 5, 1]] c

/-- In the class `n = 8b + 2c + 1`, one of the four factors `D = 1, -1, 4, 8` covers `r`
(`results/struct-lb-contra.md` Theorem 1, its 6 × 15 table, organize-archive b5cb45e). -/
def CoverGoal (c : Fin 4) (r : Fin 6 → Fin 6) : Prop :=
  Covers ordOne ordOne r ∨ Covers ordNegOne ordNegOne r ∨ Covers (ordFour c) (ordFourInv c) r ∨
    Covers (ordEight c) (ordEightInv c) r

instance (c : Fin 4) (r : Fin 6 → Fin 6) : Decidable (CoverGoal c r) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

set_option synthInstance.maxSize 100000 in
/-- **The finite table** (`results/struct-lb-contra.md` Theorem 1, its 6 × 15 table, and
`scripts/struct-lb-c-cert.py` check L0, organize-archive b5cb45e). In every class of `n` mod 8,
each of the fifteen fixed-point-free involutions `r` of `Fin 6` is covered by one of the four
factors. The hypotheses enumerate the involutions: `a_i ≠ i` and `a_i = j ↔ a_j = i`. -/
theorem coverGoal_table : ∀ c : Fin 4, ∀ a0 : Fin 6, a0 ≠ 0 → ∀ a1 : Fin 6, a1 ≠ 1 →
    (a0 = 1 ↔ a1 = 0) → ∀ a2 : Fin 6, a2 ≠ 2 → (a0 = 2 ↔ a2 = 0) → (a1 = 2 ↔ a2 = 1) →
    ∀ a3 : Fin 6, a3 ≠ 3 → (a0 = 3 ↔ a3 = 0) → (a1 = 3 ↔ a3 = 1) → (a2 = 3 ↔ a3 = 2) →
    ∀ a4 : Fin 6, a4 ≠ 4 → (a0 = 4 ↔ a4 = 0) → (a1 = 4 ↔ a4 = 1) → (a2 = 4 ↔ a4 = 2) →
    (a3 = 4 ↔ a4 = 3) → ∀ a5 : Fin 6, a5 ≠ 5 → (a0 = 5 ↔ a5 = 0) → (a1 = 5 ↔ a5 = 1) →
    (a2 = 5 ↔ a5 = 2) → (a3 = 5 ↔ a5 = 3) → (a4 = 5 ↔ a5 = 4) →
    CoverGoal c ![a0, a1, a2, a3, a4, a5] := by
  decide

/-- Every fixed-point-free involution `r` of `Fin 6` is covered by one of the four factors, in
every class `c` (`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem coverGoal_of_involution (c : Fin 4) {r : Fin 6 → Fin 6} (h1 : ∀ j, r (r j) = j)
    (h2 : ∀ j, r j ≠ j) : CoverGoal c r := by
  have hi : ∀ i j, r i = j ↔ r j = i :=
    fun i j ↦ ⟨fun h ↦ by rw [← h, h1], fun h ↦ by rw [← h, h1]⟩
  have hr : ![r 0, r 1, r 2, r 3, r 4, r 5] = r := by
    funext i
    fin_cases i <;> rfl
  rw [← hr]
  exact coverGoal_table c _ (h2 0) _ (h2 1) (hi 0 1) _ (h2 2) (hi 0 2) (hi 1 2) _ (h2 3) (hi 0 3)
    (hi 1 3) (hi 2 3) _ (h2 4) (hi 0 4) (hi 1 4) (hi 2 4) (hi 3 4) _ (h2 5) (hi 0 5) (hi 1 5)
    (hi 2 5) (hi 3 5) (hi 4 5)

/-- `4` is a unit for odd `n`. -/
theorem isUnit_four (hn : Odd n) : IsUnit (4 : ZMod n) := by
  have h := (isUnit_two hn).mul (isUnit_two hn)
  norm_num at h
  exact h

/-- `8` is a unit for odd `n`. -/
theorem isUnit_eight (hn : Odd n) : IsUnit (8 : ZMod n) := by
  have h := (isUnit_four hn).mul (isUnit_two hn)
  norm_num at h
  exact h

section Charts

variable (hn : Odd n) [NeZero n] {s0 : ZMod n} (hs0 : 2 * s0 = 7)
  {P : PerfectMatching (Option (ZMod n))}
  (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → P.mate v = (factor hn s0).mate v)
  {r : Fin 6 → Fin 6} (hr : ∀ j, P.mate (some (gadgetPt n j)) = some (gadgetPt n (r j)))
include hs0 hP hr

/-- The factor `D = 1`, multiplier `μ = 1`, at every odd `n ≥ 11`
(`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem exists_ham_one (h11 : 11 ≤ n) (hcov : Covers ordOne ordOne r) :
    ∃ t, Ham P (factor hn t) := by
  obtain ⟨t, ht⟩ := exists_two_mul_two_mul_sub hn ((1 : ℤ) : ZMod n)
  refine ⟨t, ham_of_chart hn hs0 hP hr (D := 1) (by simp) ht
    (q := ![-5, -3, -1, 1, 3, 5]) (w := 0) ?_ (by simp; omega) (ordInv := ordOne)
    (fun j ↦ by fin_cases j <;> rfl) (fun i ↦ by fin_cases i <;> simp [ordOne]) hcov⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp

/-- The factor `D = -1`, multiplier `μ = -1`, at every odd `n ≥ 11`
(`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem exists_ham_negOne (h11 : 11 ≤ n) (hcov : Covers ordNegOne ordNegOne r) :
    ∃ t, Ham P (factor hn t) := by
  obtain ⟨t, ht⟩ := exists_two_mul_two_mul_sub hn ((-1 : ℤ) : ZMod n)
  refine ⟨t, ham_of_chart hn hs0 hP hr (D := -1) (by simp) ht
    (q := ![-5, -3, -1, 1, 3, 5]) (w := 0) ?_ (by simp; omega) (ordInv := ordNegOne)
    (fun j ↦ by fin_cases j <;> rfl) (fun i ↦ by fin_cases i <;> simp [ordNegOne]) hcov⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp

/-- Positions of the gadget for `D = 4` in the class `n = 8b + 2c + 1`: the point `ordFour c i`
sits at `-2b + β`, `2b + β` (`results/struct-lb-contra.md` Theorem 1, `μ = 4⁻¹`, organize-archive
b5cb45e). -/
def posFour (c : Fin 4) (b : ℤ) (i : Fin 6) : ℤ :=
  ![-2, -2, -2, 2, 2, 2] i * b +
    ![![-1, 0, 1, -1, 0, 1], ![-2, -1, 0, 0, 1, 2], ![-2, -1, 0, 0, 1, 2],
      ![-3, -2, -1, 1, 2, 3]] c i

/-- Positions of the gadget for `D = 8` in the class `n = 8b + 2c + 1`
(`results/struct-lb-contra.md` Theorem 1, `μ = 8⁻¹`, organize-archive b5cb45e). -/
def posEight (c : Fin 4) (b : ℤ) (i : Fin 6) : ℤ :=
  ![![-3, -3, -1, 1, 3, 3], ![-3, -1, -1, 1, 1, 3], ![-3, -1, -1, 1, 1, 3],
      ![-3, -3, -1, 1, 3, 3]] c i * b +
    ![![-1, 0, 0, 0, 0, 1], ![-1, -1, 0, 0, 1, 1], ![-2, -1, 0, 0, 1, 2],
      ![-3, -2, -1, 1, 2, 3]] c i

/-- The factor `D = 4`, multiplier `μ = 4⁻¹`, in the class `n = 8b + 2c + 1` with `b ≥ 1`
(`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem exists_ham_four {b : ℕ} {c : Fin 4} (hb : n = 8 * b + (2 * c + 1)) (hb1 : 1 ≤ b)
    (hcov : Covers (ordFour c) (ordFourInv c) r) : ∃ t, Ham P (factor hn t) := by
  obtain ⟨t, ht⟩ := exists_two_mul_two_mul_sub hn ((4 : ℤ) : ZMod n)
  refine ⟨t, ham_of_chart hn hs0 hP hr (D := 4) (by simpa using isUnit_four hn) ht
    (q := posFour c b) (w := ![-1, -1, -1, 1, 1, 1]) ?_ ?_ (ordInv := ordFourInv c) ?_ ?_ hcov⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases c <;> fin_cases i <;> simp [posFour] <;> omega
  · fin_cases c <;> simp [posFour] at hb ⊢ <;> omega
  · fin_cases c <;> decide
  · intro i
    fin_cases c <;> fin_cases i <;> simp [posFour, ordFour] at hb ⊢ <;> omega

/-- The factor `D = 8`, multiplier `μ = 8⁻¹`, in the class `n = 8b + 2c + 1` with `b ≥ 1`
(`results/struct-lb-contra.md` Theorem 1, organize-archive b5cb45e). -/
theorem exists_ham_eight {b : ℕ} {c : Fin 4} (hb : n = 8 * b + (2 * c + 1)) (hb1 : 1 ≤ b)
    (hcov : Covers (ordEight c) (ordEightInv c) r) : ∃ t, Ham P (factor hn t) := by
  obtain ⟨t, ht⟩ := exists_two_mul_two_mul_sub hn ((8 : ℤ) : ZMod n)
  refine ⟨t, ham_of_chart hn hs0 hP hr (D := 8) (by simpa using isUnit_eight hn) ht
    (q := posEight c b)
    (w := ![![-3, -3, -1, 1, 3, 3], ![-3, -1, -1, 1, 1, 3], ![-3, -1, -1, 1, 1, 3],
      ![-3, -3, -1, 1, 3, 3]] c) ?_ ?_ (ordInv := ordEightInv c) ?_ ?_ hcov⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases c <;> fin_cases i <;> simp [posEight] <;> omega
  · fin_cases c <;> simp [posEight] at hb ⊢ <;> omega
  · fin_cases c <;> decide
  · intro i
    fin_cases c <;> fin_cases i <;> simp [posEight, ordEight] at hb ⊢ <;> omega

end Charts

/-- **Theorem 1 of `results/struct-lb-contra.md`, in walk form** (Theorem A of
`results/struct-lb-extend.md`, organize-archive b5cb45e). For every odd `n ≥ 11`, with
`2 s0 = 7`, every perfect matching `P` of `ℤ/n ∪ {∞}` that agrees with `F_{s0}` off the gadget
`G0` has some round-robin factor `F_t` with `P ∪ F_t` one cycle. The factor is one of the four
with `μ = 1, -1, 4⁻¹, 8⁻¹`. -/
theorem exists_ham_of_agree (hn : Odd n) [NeZero n] (h11 : 11 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → P.mate v = (factor hn s0).mate v) :
    ∃ t, Ham P (factor hn t) := by
  obtain ⟨r, hr, hr1, hr2⟩ := exists_gadget_mate hn h11 hs0 hP
  obtain ⟨k, hk⟩ := hn
  obtain ⟨c, hc⟩ : ∃ c : Fin 4, (c : ℕ) = k % 4 := ⟨⟨k % 4, Nat.mod_lt _ (by omega)⟩, rfl⟩
  have hb : n = 8 * (k / 4) + (2 * c + 1) := by omega
  have hb1 : 1 ≤ k / 4 := by omega
  rcases coverGoal_of_involution c hr1 hr2 with h | h | h | h
  · exact exists_ham_one _ hs0 hP hr h11 h
  · exact exists_ham_negOne _ hs0 hP hr h11 h
  · exact exists_ham_four _ hs0 hP hr hb hb1 h
  · exact exists_ham_eight _ hs0 hP hr hb hb1 h

end LowerBound

namespace RoundRobin.Canonical

open PerfectMatching LowerBound

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
/-- The default gadget `G0` is the set of the six points `gadgetPt (2m - 1) j`
(`results/struct-lb-contra.md` §1, organize-archive b5cb45e). -/
theorem mem_gadget_iff (v : Vertex m) :
    v ∈ FactorCap.gadget m ↔ ∃ j, v = some (gadgetPt (2 * m - 1) j) := by
  constructor
  · intro hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_Icc] at hk
    exact ⟨⟨k - 1, by omega⟩, by simp [gadgetPt, Nat.sub_add_cancel hk.1]⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨(j : ℕ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩

/-- **`ρ(T(n)) ≥ 1`** (`results/struct-lb-contra.md` Theorem 1 and `results/struct-lb-extend.md`
Theorem A, organize-archive b5cb45e). For every `m ≥ 6`, every zero state differs from the
factor tail `T(n)` in at least one edge. -/
theorem one_le_tailDist_factorTail (hm : 6 ≤ m) (P : ZeroState m) :
    1 ≤ tailDist P.1 (FactorCap.factorTail m (by omega)) := by
  by_contra h0
  have h2 := two_mul_tailDist P.1 (FactorCap.factorTail m (by omega))
  have hcard : (Finset.univ.filter fun u : ((FactorCap.gadget m)ᶜ : Finset (Vertex m)) ↦
      ((FactorCap.factorTail m (by omega)).mate u : Vertex m) ≠ P.1.mate u).card = 0 := by
    omega
  have hempty := Finset.card_eq_zero.mp hcard
  have hP : ∀ v, (∀ j, v ≠ some (gadgetPt (2 * m - 1) j)) →
      P.1.mate v = (RoundRobin.factor (modulus_odd m) (FactorCap.capCenter m)).mate v := by
    intro v hv
    have hvc : v ∈ (FactorCap.gadget m)ᶜ :=
      Finset.mem_compl.mpr fun h ↦ by
        obtain ⟨j, hj⟩ := (mem_gadget_iff v).mp h
        exact hv j hj
    have h1 := Finset.filter_eq_empty_iff.mp hempty (Finset.mem_univ ⟨v, hvc⟩)
    rw [not_not, FactorCap.factorTail_mate] at h1
    exact h1.symm
  obtain ⟨t, ht⟩ := exists_ham_of_agree (modulus_odd m) (by omega)
    FactorCap.two_mul_capCenter hP
  exact P.2 t ht

/-- **`N_m ≥ 1` for every `m ≥ 6`** (`results/struct-lb-contra.md` Theorem 1 and
`results/struct-lb-extend.md` Theorem A, organize-archive b5cb45e). No zero state lies at distance
`0` from the factor tail `T(n)`, so `RepairBound m G0 0` fails. -/
theorem not_repairBound_zero (hm : 6 ≤ m) : ¬RepairBound m (FactorCap.gadget m) 0 := by
  intro h
  obtain ⟨P, hP⟩ := h (FactorCap.factorTail m (by omega))
  have := one_le_tailDist_factorTail hm P
  omega

end RoundRobin.Canonical

end Pairing
