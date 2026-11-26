import Mathlib.Analysis.Real.Pi.Wallis
import Repair.PartialCore
import Repair.ZeroState
import Suppression.VMinus

/-!
# The √m glue for the density reductions

This file turns the reductions of `Reweighted.lean` and `VMinus.lean` (COD-198) into end-to-end
statements about `q_m` with explicit `√m` rates. Notation is that of the frontier
(`results/frontier-2026-11-25.md` §1): `A_t = hamEvent m t`, `p = U(A_t)`, `μ_m = ∑_t U(A_t)`,
`n = 2m - 1` and `q_m = hamLaw m 0`.

* `PerfectMatching.le_card_ham`, `PerfectMatching.card_ham_eq` (Lemma 3 of COD-168, exact form) :
  for a perfect matching `M` of a type with `2r ≥ 2` elements, exactly `2^(r-1) (r-1)!` perfect
  matchings `X` make `X ∪ M` one cycle. The upper bound is `PerfectMatching.card_ham_le`.
* `RoundRobin.Canonical.prob_hamEvent_eq` : `p = 2^(m-1) (m-1)! / (2m - 1)!!`.
* `RoundRobin.Canonical.sum_prob_hamEvent` : `μ_m = n p`.
* `RoundRobin.Canonical.mul_sq_sum_prob_hamEvent` : `(2m)² μ_m² = (2m - 1)² (2m + 1) W_m`, with
  `W_m` the Wallis product of Mathlib.
* `RoundRobin.Canonical.sum_prob_hamEvent_le`, `RoundRobin.Canonical.sub_le_sum_prob_hamEvent` :
  `√(πm) - √π / (2√m) ≤ μ_m ≤ √(πm)` for every `m ≥ 1`, the frontier's
  `μ_m = √(πm) + O(m^(-1/2))` with explicit error.
* `RoundRobin.Canonical.sqrt_mul_sqrt_le_sum_prob_hamEvent` : `(√π / 2) √m ≤ μ_m ≤ √π √m`.
* `RoundRobin.Canonical.hamLaw_zero_pos`, `RoundRobin.Canonical.prob_avoid_hamEvent_pos` :
  `0 < q_m` for every `m ≥ 6`.
* `RoundRobin.Canonical.exp_neg_sqrt_le_hamLaw_zero` (COD-168 from (V−_M)) : if
  `c M_T ≤ V_T` for every `T ≠ ℤ_n`, then `q_m ≥ exp(-(√π / c) √m)`.
* `RoundRobin.Canonical.exp_neg_sqrt_sub_le_hamLaw_zero` (COD-168 from windowed (V−_M)).
* `RoundRobin.Canonical.exp_neg_sqrt_le_hamLaw_zero_of_le_palmGap` (COD-168 from the lower-side
  Lemma A on one path) : if `(1 + Δ_k)(1 - f_k) ≥ c > 0` at every step of one ordering of `ℤ_n`,
  then `q_m ≥ exp(-(√π / c) √m)`.
* `RoundRobin.Canonical.exp_neg_sqrt_sub_le_hamLaw_zero_of_le_palmGap` (COD-168 from the lower
  interval Palm lemma on a window) : `q_m ≥ exp(-(√π / (c (1 - δ))) √m - 2δ - G)`.
* `RoundRobin.Canonical.hamLaw_zero_le_exp_neg_sqrt` (COD-174 from (V+_B)) : (V+_B) on the window
  `⌊δ / p⌋ ≤ |T|`, `N_T ≥ K + 1` with constant `κ`, and the named hypothesis `Var X ≤ A μ_m`,
  give `q_m ≤ exp(-(√π / (2κ)) √m + (8 A δ + K (K + 1) / 2) / κ)`.
-/

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- On a type of even size, any two distinct vertices `w ≠ x` are partners in some perfect
matching. -/
theorem exists_mate_eq (hW : Even (Fintype.card W)) {w x : W} (hwx : w ≠ x) :
    ∃ X : PerfectMatching W, X.mate w = x := by
  classical
  obtain ⟨P⟩ := nonempty_of_even_card hW
  refine ⟨Equiv.swap x (P.mate w) • P, ?_⟩
  rw [smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hwx (P.mate_ne w).symm,
    Equiv.swap_apply_right]

/-- Lemma 3 (COD-168, `results/cod-168-density-lower-bound.md`), lower bound. For a perfect
matching `M` of a type with `2(r + 1)` elements, at least `2^r r!` perfect matchings `X` make
`X ∪ M` one cycle. As in `card_ham_le`, the proof fixes a vertex `w`, splits by the partner
`x = X w`, and contracts the edge `wx` with `ham_glue_iff`. -/
theorem le_card_ham {r : ℕ} (hW : Fintype.card W = 2 * (r + 1)) (M : PerfectMatching W) :
    2 ^ r * r.factorial ≤ (Finset.univ.filter fun X : PerfectMatching W ↦ Ham X M).card := by
  induction r generalizing W with
  | zero =>
    obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    have h2 : ∀ u v : W, u = v ∨ M.mate u = v := by
      intro u v
      by_contra h
      push Not at h
      have hc := Finset.card_le_univ ({u, v, M.mate u} : Finset W)
      rw [Finset.card_insert_of_notMem (by simp [h.1, (M.mate_ne u).symm]),
        Finset.card_pair h.2.symm, hW] at hc
      omega
    have hM : Ham M M := by
      change (M.toGraph ⊔ M.toGraph).Connected
      have : Nonempty W := ⟨w⟩
      refine ⟨fun u v ↦ ?_⟩
      rcases h2 u v with rfl | h
      · exact SimpleGraph.Reachable.refl _
      · exact h ▸ (adj_mate_left M M u).reachable
    simp only [pow_zero, Nat.factorial_zero, mul_one]
    exact Finset.card_pos.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩⟩
  | succ r ih =>
    obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    have hfib : ∀ x ∈ (Finset.univ.erase w).erase (M.mate w), 2 ^ r * r.factorial ≤
        (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card := by
      intro x hx
      have hxM : x ≠ M.mate w := (Finset.mem_erase.mp hx).1
      have hxw : x ≠ w := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      obtain ⟨X₀, hX₀w⟩ := exists_mate_eq ⟨r + 2, by omega⟩ hxw.symm
      have hX₀x : X₀.mate x = w := by rw [← hX₀w, mate_mate]
      have hmemA : ∀ v, v ∈ (Finset.univ.erase w).erase x ↔ v ≠ x ∧ v ≠ w := fun v ↦ by
        simp
      have hA : ∀ v ∈ (Finset.univ.erase w).erase x,
          X₀.mate v ∈ (Finset.univ.erase w).erase x := by
        intro v hv
        rw [hmemA] at hv ⊢
        refine ⟨fun h ↦ hv.2 ?_, fun h ↦ hv.1 ?_⟩
        · rw [← X₀.mate_mate v, h, hX₀x]
        · rw [← X₀.mate_mate v, h, hX₀w]
      have hAcard : Fintype.card ((Finset.univ.erase w).erase x) = 2 * (r + 1) := by
        rw [Fintype.card_coe,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxw, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hW]
        omega
      have hC : ¬HasClosedCycle X₀ M ((Finset.univ.erase w).erase x) := by
        rintro ⟨C, ⟨v, hv⟩, hdisj, -, hMC⟩
        have hout : ∀ u ∈ C, u = x ∨ u = w := by
          intro u hu
          have h := Finset.disjoint_left.mp hdisj hu
          rw [hmemA] at h
          tauto
        rcases hout v hv with rfl | rfl
        · rcases hout _ (hMC _ hv) with h | h
          · exact M.mate_ne _ h
          · exact hxM (by rw [← h, mate_mate])
        · rcases hout _ (hMC _ hv) with h | h
          · exact hxM h.symm
          · exact M.mate_ne _ h
      calc 2 ^ r * r.factorial
          ≤ (Finset.univ.filter fun Y : PerfectMatching ((Finset.univ.erase w).erase x) ↦
              Ham Y (contract X₀ M _ hA)).card := ih hAcard _
        _ = ((Finset.univ.filter fun Y : PerfectMatching ((Finset.univ.erase w).erase x) ↦
              Ham Y (contract X₀ M _ hA)).image (glue X₀ _ hA)).card :=
            (Finset.card_image_of_injective _
              fun Y Y' h ↦ (glueEquiv X₀ _ hA).injective (Subtype.ext h)).symm
        _ ≤ (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card := by
            refine Finset.card_le_card fun X hX ↦ ?_
            obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
            have hwA : w ∉ (Finset.univ.erase w).erase x := fun h ↦ ((hmemA w).mp h).2 rfl
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · rw [glue_mate_of_notMem X₀ _ hA Y hwA, hX₀w]
            · exact (ham_glue_iff X₀ M _ hA hC Y).mpr (Finset.mem_filter.mp hY).2
    have hcard : ((Finset.univ.erase w).erase (M.mate w)).card = 2 * r + 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨M.mate_ne w, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hW]
      omega
    calc 2 ^ (r + 1) * (r + 1).factorial
        = ∑ _x ∈ (Finset.univ.erase w).erase (M.mate w), 2 ^ r * r.factorial := by
          rw [Finset.sum_const, smul_eq_mul, hcard, Nat.factorial_succ, pow_succ]
          ring
      _ ≤ ∑ x ∈ (Finset.univ.erase w).erase (M.mate w),
            (Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card :=
          Finset.sum_le_sum hfib
      _ = (((Finset.univ.erase w).erase (M.mate w)).biUnion fun x ↦
            Finset.univ.filter fun X : PerfectMatching W ↦ X.mate w = x ∧ Ham X M).card :=
          (Finset.card_biUnion fun x _ y _ hxy ↦
            Finset.disjoint_filter.mpr fun X _ h1 h2 ↦ hxy (h1.1.symm.trans h2.1)).symm
      _ ≤ (Finset.univ.filter fun X : PerfectMatching W ↦ Ham X M).card := by
          refine Finset.card_le_card fun X hX ↦ ?_
          obtain ⟨x, -, hX⟩ := Finset.mem_biUnion.mp hX
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.2⟩

/-- Lemma 3 (COD-168, `results/cod-168-density-lower-bound.md`), exact form. For a perfect
matching `M` of a type with `2r` elements, `r ≥ 1`, exactly `2^(r-1) (r-1)!` perfect matchings `X`
make `X ∪ M` one cycle. -/
theorem card_ham_eq {r : ℕ} (hr : 0 < r) (hW : Fintype.card W = 2 * r) (M : PerfectMatching W) :
    (Finset.univ.filter fun X : PerfectMatching W ↦ Ham X M).card =
      2 ^ (r - 1) * (r - 1).factorial :=
  le_antisymm (card_ham_le hW M) (le_card_ham (by rw [hW, Nat.sub_add_cancel hr]) M)

end PerfectMatching

namespace RoundRobin.Canonical

open Finset ChainRule PerfectMatching Real

/-- Lemma 3 of COD-168 on `V_m`: exactly `2^(m-1) (m-1)!` perfect matchings `P` make `P ∪ F_t`
one cycle, so `|A_t| = 2^(m-1) (m-1)!` (frontier `results/frontier-2026-11-25.md` §1). -/
theorem card_ham_factor (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) :
    (Finset.univ.filter fun P ↦ Ham P (factor m t)).card = 2 ^ (m - 1) * (m - 1).factorial :=
  card_ham_eq (NeZero.pos m) (card_vertex m) (factor m t)

/-- The closed form of `p` (frontier `results/frontier-2026-11-25.md` §1, COD-168 Lemma 3):
`p = U(A_t) = 2^(m-1) (m-1)! / (2m - 1)!!`, the probability that `P ∪ F_t` is one cycle for a
uniform perfect matching `P` of `V_m`. -/
theorem prob_hamEvent_eq (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) :
    prob (unifWeight m) (hamEvent m t) =
      (2 ^ (m - 1) * (m - 1).factorial : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  classical
  rw [prob_unifWeight, card_eq_doubleFactorial (card_vertex m)]
  have h := card_ham_factor m t
  congr 1
  rw [show (2 ^ (m - 1) * (m - 1).factorial : ℝ) = ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) by
    push_cast; ring, ← h]
  congr 2
  exact filter_congr fun P _ ↦ Iff.rfl

/-- `p > 0`, from the closed form `p = 2^(m-1) (m-1)! / (2m - 1)!!` (frontier §1). -/
theorem prob_hamEvent_pos (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) :
    0 < prob (unifWeight m) (hamEvent m t) := by
  rw [prob_hamEvent_eq]
  exact div_pos (by positivity) (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))

/-- `μ_m = n p` with `n = 2m - 1` (frontier `results/frontier-2026-11-25.md` §1). -/
theorem sum_prob_hamEvent (m : ℕ) [NeZero m] :
    ∑ t, prob (unifWeight m) (hamEvent m t) =
      (2 * m - 1 : ℝ) * prob (unifWeight m) (hamEvent m 0) := by
  have hm := NeZero.pos m
  rw [sum_congr rfl fun t _ ↦ prob_hamEvent m t, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `μ_m` through the Wallis product `W_m` of Mathlib:
`(2m)² μ_m² = (2m - 1)² (2m + 1) W_m` (frontier `results/frontier-2026-11-25.md` §1). -/
theorem mul_sq_sum_prob_hamEvent (m : ℕ) [NeZero m] :
    (2 * m : ℝ) ^ 2 * (∑ t, prob (unifWeight m) (hamEvent m t)) ^ 2 =
      (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * Wallis.W m := by
  rw [sum_prob_hamEvent, prob_hamEvent_eq, Wallis.W_eq_factorial_ratio]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  have hD : ((2 * (k + 1)).factorial : ℝ) =
      2 ^ (k + 1) * (k + 1).factorial * Nat.doubleFactorial (2 * k + 1) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Nat.doubleFactorial_two_mul] at h
    exact_mod_cast h
  have hF : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  have hpos : (0 : ℝ) < Nat.doubleFactorial (2 * k + 1) :=
    Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  have hkf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega, hD, hF]
  field_simp
  push_cast
  ring

/-- The upper half of `μ_m = √(πm) + O(m^(-1/2))` (frontier `results/frontier-2026-11-25.md` §1):
`μ_m ≤ √(πm)` for every `m ≥ 1`, from `W_m ≤ π / 2`. -/
theorem sum_prob_hamEvent_le (m : ℕ) [NeZero m] :
    ∑ t, prob (unifWeight m) (hamEvent m t) ≤ Real.sqrt (π * m) := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
  have hμ : 0 ≤ ∑ t, prob (unifWeight m) (hamEvent m t) :=
    sum_nonneg fun t _ ↦ prob_nonneg (isProb_unifWeight m) _
  have h := mul_sq_sum_prob_hamEvent m
  have hW := Wallis.W_le m
  have hpi := pi_pos
  rw [le_sqrt hμ (by positivity)]
  have h1 : (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * Wallis.W m ≤
      (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * (π / 2) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have h2 : (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * (π / 2) ≤ (2 * m : ℝ) ^ 2 * (π * m) := by
    have : (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) ≤ 8 * m ^ 3 := by nlinarith
    nlinarith
  have h3 : (2 * m : ℝ) ^ 2 * (∑ t, prob (unifWeight m) (hamEvent m t)) ^ 2 ≤
      (2 * m : ℝ) ^ 2 * (π * m) := by
    linarith
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- The lower half of `μ_m = √(πm) + O(m^(-1/2))` (frontier `results/frontier-2026-11-25.md` §1):
`(1 - 1 / (2m)) √(πm) ≤ μ_m` for every `m ≥ 1`, from `W_m ≥ (2m + 1) / (2m + 2) · π / 2`. -/
theorem one_sub_mul_sqrt_le_sum_prob_hamEvent (m : ℕ) [NeZero m] :
    (1 - 1 / (2 * m)) * Real.sqrt (π * m) ≤ ∑ t, prob (unifWeight m) (hamEvent m t) := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
  have hμ : 0 ≤ ∑ t, prob (unifWeight m) (hamEvent m t) :=
    sum_nonneg fun t _ ↦ prob_nonneg (isProb_unifWeight m) _
  have h := mul_sq_sum_prob_hamEvent m
  have hW := Wallis.le_W m
  have hpi := pi_pos
  have ha : 0 ≤ 1 - 1 / (2 * m : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hsq : ((1 - 1 / (2 * m)) * Real.sqrt (π * m)) ^ 2 =
      (2 * m - 1 : ℝ) ^ 2 * (π * m) / (2 * m) ^ 2 := by
    rw [mul_pow, sq_sqrt (by positivity)]
    field_simp
  have h1 : (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * ((2 * m + 1) / (2 * m + 2) * (π / 2)) ≤
      (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * Wallis.W m :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have h2 : (2 * m - 1 : ℝ) ^ 2 * (π * m) ≤
      (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * ((2 * m + 1) / (2 * m + 2) * (π / 2)) := by
    have e : (2 * m - 1 : ℝ) ^ 2 * (2 * m + 1) * ((2 * m + 1) / (2 * m + 2) * (π / 2)) =
        (2 * m - 1 : ℝ) ^ 2 * π * ((2 * m + 1) ^ 2 / (4 * (m + 1))) := by
      field_simp
      ring
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hpi.le) (by positivity)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : ((1 - 1 / (2 * m)) * Real.sqrt (π * m)) ^ 2 ≤
      (∑ t, prob (unifWeight m) (hamEvent m t)) ^ 2 := by
    rw [hsq, div_le_iff₀ (by positivity), mul_comm _ ((2 * m : ℝ) ^ 2), h]
    linarith
  rw [← sqrt_sq (mul_nonneg ha (sqrt_nonneg _)), ← sqrt_sq hμ]
  exact sqrt_le_sqrt h3

/-- `μ_m = √(πm) + O(m^(-1/2))` with explicit error (frontier `results/frontier-2026-11-25.md`
§1): `√(πm) - √π / (2√m) ≤ μ_m ≤ √(πm)` for every `m ≥ 1`. -/
theorem sub_le_sum_prob_hamEvent (m : ℕ) [NeZero m] :
    Real.sqrt (π * m) - Real.sqrt π / (2 * Real.sqrt m) ≤
        ∑ t, prob (unifWeight m) (hamEvent m t) ∧
      ∑ t, prob (unifWeight m) (hamEvent m t) ≤ Real.sqrt (π * m) := by
  refine ⟨le_trans (le_of_eq ?_) (one_sub_mul_sqrt_le_sum_prob_hamEvent m),
    sum_prob_hamEvent_le m⟩
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hs : (0 : ℝ) < Real.sqrt m := sqrt_pos.mpr hm
  have hss : Real.sqrt m * Real.sqrt m = m := mul_self_sqrt hm.le
  have e : 1 / (2 * (m : ℝ)) * (Real.sqrt π * Real.sqrt m) = Real.sqrt π / (2 * Real.sqrt m) := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * Real.sqrt π) * hss
  rw [sqrt_mul pi_pos.le, ← e]
  ring

/-- `μ_m = Θ(√m)` with explicit constants (frontier `results/frontier-2026-11-25.md` §1):
`(√π / 2) √m ≤ μ_m ≤ √π √m` for every `m ≥ 1`. -/
theorem sqrt_mul_sqrt_le_sum_prob_hamEvent (m : ℕ) [NeZero m] :
    Real.sqrt π / 2 * Real.sqrt m ≤ ∑ t, prob (unifWeight m) (hamEvent m t) ∧
      ∑ t, prob (unifWeight m) (hamEvent m t) ≤ Real.sqrt π * Real.sqrt m := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
  have h1 := one_sub_mul_sqrt_le_sum_prob_hamEvent m
  have h2 := sum_prob_hamEvent_le m
  rw [sqrt_mul pi_pos.le] at h1 h2
  refine ⟨le_trans ?_ h1, h2⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ two_pos, mul_comm _ (2 : ℝ), ← mul_assoc]
  refine le_mul_of_one_le_left (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) ?_
  rw [mul_sub, mul_one, mul_one_div, show (2 : ℝ) / (2 * m) = 1 / m by field_simp]
  have : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hm
  linarith

/-- `0 < q_m` for every `m ≥ 6` (frontier `results/frontier-2026-11-25.md` §1, P3), since a zero
state exists (`nonempty_zeroState`). -/
theorem hamLaw_zero_pos {m : ℕ} [NeZero m] (hm : 6 ≤ m) : 0 < hamLaw m 0 := by
  rw [hamLaw_zero]
  exact div_pos (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (nonempty_zeroState hm)))
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))

/-- `0 < q = U(Z_{ℤ_n})` for every `m ≥ 6`, the standing hypothesis `q > 0` of COD-198
(`results/cod-198-attempt.md`) for the round-robin events. -/
theorem prob_avoid_hamEvent_pos {m : ℕ} [NeZero m] (hm : 6 ≤ m) :
    0 < prob (unifWeight m) (avoid (hamEvent m) univ) := by
  rw [prob_avoid_hamEvent]
  exact hamLaw_zero_pos hm

/-- `p ≤ 1 / 2` for every `m ≥ 6` (frontier `results/frontier-2026-11-25.md` §1), from
`n p = μ_m ≤ √(πm)`. -/
theorem prob_hamEvent_le_half {m : ℕ} [NeZero m] (hm : 6 ≤ m) (t : ZMod (2 * m - 1)) :
    prob (unifWeight m) (hamEvent m t) ≤ 1 / 2 := by
  have hm' : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have h := sum_prob_hamEvent_le m
  rw [sum_prob_hamEvent, ← prob_hamEvent m t] at h
  have hs : Real.sqrt (π * m) ≤ (2 * m - 1) / 2 := by
    rw [sqrt_le_left (by linarith)]
    nlinarith [pi_le_four]
  rw [le_div_iff₀ two_pos]
  nlinarith

/-- COD-168 (`q_m ≥ e^(-C√m)`) from (V−_M), end to end, through Corollary 4(iv) of COD-198
(`results/cod-198-attempt.md`, `exp_neg_div_le_prob_avoid_of_le_condVar`) and
`μ_m ≤ √π √m` (frontier `results/frontier-2026-11-25.md` §1). If `c > 0` and (V−_M)
`c M_T ≤ V_T` holds for every avoidance set `T ≠ ℤ_n`, then `q_m ≥ exp(-C √m)` with
`C = √π / c`. This holds for every `m ≥ 1`. -/
theorem exp_neg_sqrt_le_hamLaw_zero {m : ℕ} [NeZero m] {c : ℝ} (hc : 0 < c)
    (hV : ∀ T : Finset (ZMod (2 * m - 1)), T ≠ univ →
      c * condMean (unifWeight m) (hamEvent m) T ≤ condVar (unifWeight m) (hamEvent m) T) :
    Real.exp (-(Real.sqrt π / c * Real.sqrt m)) ≤ hamLaw m 0 := by
  rw [← prob_avoid_hamEvent]
  refine le_trans (exp_le_exp.mpr ?_)
    (exp_neg_div_le_prob_avoid_of_le_condVar (isProb_unifWeight m) hc hV)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (sqrt_mul_sqrt_le_sum_prob_hamEvent m).2 hc.le

/-- COD-168 (`q_m ≥ e^(-C√m)`) from (V−_M) on a window, end to end, through Corollary 4(ii),
(iii) of COD-198 (`results/cod-198-attempt.md`, `neg_log_le_div_add_of_le_condVar_condMean`).
Let `m ≥ 6`, `c > 0` and `0 ≤ δ ≤ 1 / 4`. If (V−_M) `c M_T ≤ V_T` holds for every `T ≠ ℤ_n` with
`⌊δ / p⌋ ≤ |T|`, then `q_m ≥ exp(-(√π / c) √m - 8δ)`. -/
theorem exp_neg_sqrt_sub_le_hamLaw_zero {m : ℕ} [NeZero m] (hm : 6 ≤ m) {c δ : ℝ} (hc : 0 < c)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hV : ∀ T : Finset (ZMod (2 * m - 1)), ⌊δ / prob (unifWeight m) (hamEvent m 0)⌋₊ ≤ T.card →
      T ≠ univ →
      c * condMean (unifWeight m) (hamEvent m) T ≤ condVar (unifWeight m) (hamEvent m) T) :
    Real.exp (-(Real.sqrt π / c * Real.sqrt m) - 8 * δ) ≤ hamLaw m 0 := by
  set p := prob (unifWeight m) (hamEvent m 0) with hpdef
  set μ := ∑ t, prob (unifWeight m) (hamEvent m t) with hμdef
  have hq := prob_avoid_hamEvent_pos hm
  have hp : ∀ t, prob (unifWeight m) (hamEvent m t) ≤ p := fun t ↦ (prob_hamEvent m t).le
  have hp0 : 0 < p := prob_hamEvent_pos m 0
  have hp2 : p ≤ 1 / 2 := prob_hamEvent_le_half hm 0
  have hbd := sqrt_mul_sqrt_le_sum_prob_hamEvent m
  have hpi : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 from sqrt_one.symm]
    exact sqrt_le_sqrt (by linarith [one_le_pi_div_two])
  have hsm : 1 ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 from sqrt_one.symm]
    exact sqrt_le_sqrt (Nat.one_le_cast.mpr (NeZero.pos m))
  have hμ1 : 1 / 2 ≤ μ := by nlinarith [hbd.1]
  have h := neg_log_le_div_add_of_le_condVar_condMean (isProb_unifWeight m) hq hp hp0 hδ0
    (by linarith) (by linarith) hc hV
  have hden : μ / 8 ≤ (1 - δ - p) * (μ - δ) := by nlinarith
  have hC : μ * δ / ((1 - δ - p) * (μ - δ)) ≤ 8 * δ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hμc : μ / c ≤ Real.sqrt π / c * Real.sqrt m := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hbd.2 hc.le
  rw [← prob_avoid_hamEvent]
  calc Real.exp (-(Real.sqrt π / c * Real.sqrt m) - 8 * δ)
      ≤ Real.exp (Real.log (prob (unifWeight m) (avoid (hamEvent m) univ))) :=
        exp_le_exp.mpr (by linarith)
    _ = prob (unifWeight m) (avoid (hamEvent m) univ) := exp_log hq

/-- COD-168 (`q_m ≥ e^(-C√m)`) from the lower-side Lemma A on one path, end to end, through
`exp_neg_div_le_prob_avoid_of_le_palmGap` (`results/two-sided-corner-spike.md` Proposition 4,
`results/soft-floor-spike.md` §7 step 2) and `μ_m ≤ √π √m` (frontier
`results/frontier-2026-11-25.md` §1). If `c > 0` and `(1 + Δ_k)(1 - f_k) ≥ c` at every step of
one ordering `σ` of `ℤ_n`, for instance the interval ordering, then `q_m ≥ exp(-(√π / c) √m)`,
the bound of `exp_neg_sqrt_le_hamLaw_zero`. This holds for every `m ≥ 1`. -/
theorem exp_neg_sqrt_le_hamLaw_zero_of_le_palmGap {m : ℕ} [NeZero m] {c : ℝ} (hc : 0 < c)
    {n : ℕ} (σ : Fin n ≃ ZMod (2 * m - 1))
    (h : ∀ k : Fin n,
      c ≤ (1 + palmGap (unifWeight m) (hamEvent m) (pre σ k) (σ k)) *
        (1 - condProb (unifWeight m) (hamEvent m) (pre σ k) (σ k))) :
    Real.exp (-(Real.sqrt π / c * Real.sqrt m)) ≤ hamLaw m 0 := by
  rw [← prob_avoid_hamEvent]
  refine le_trans (exp_le_exp.mpr ?_)
    (exp_neg_div_le_prob_avoid_of_le_palmGap (isProb_unifWeight m) hc σ h)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (sqrt_mul_sqrt_le_sum_prob_hamEvent m).2 hc.le

/-- COD-168 (`q_m ≥ e^(-C√m)`) from the lower interval Palm lemma on a window, end to end,
through `neg_log_le_div_add_of_le_palmGap_of_le` (`results/two-sided-corner-spike.md` §7 item 2
and Proposition 4) and `μ_m ≤ √π √m` (frontier `results/frontier-2026-11-25.md` §1). Let `m ≥ 6`,
`c > 0` and `0 ≤ δ ≤ 1 / 2`. If `(1 + Δ_k)(1 - f_k) ≥ c` at every step `k` of one ordering `σ`
of `ℤ_n` with `⌊δ / p⌋ ≤ k` and `k + K < n`, and the last `K` steps cost
`log U(Z_{T_{n-K}}) - log q_m ≤ G`, then `q_m ≥ exp(-(√π / (c (1 - δ))) √m - 2δ - G)`. With
`K = 0` one may take `G = 0`. -/
theorem exp_neg_sqrt_sub_le_hamLaw_zero_of_le_palmGap {m : ℕ} [NeZero m] (hm : 6 ≤ m)
    {c δ G : ℝ} {K n : ℕ} (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (σ : Fin n ≃ ZMod (2 * m - 1))
    (h : ∀ k : Fin n, ⌊δ / prob (unifWeight m) (hamEvent m 0)⌋₊ ≤ (k : ℕ) → (k : ℕ) + K < n →
      c ≤ (1 + palmGap (unifWeight m) (hamEvent m) (pre σ k) (σ k)) *
        (1 - condProb (unifWeight m) (hamEvent m) (pre σ k) (σ k)))
    (hG : Real.log (prob (unifWeight m) (avoid (hamEvent m) (pre σ (n - K)))) -
      Real.log (hamLaw m 0) ≤ G) :
    Real.exp (-(Real.sqrt π / (c * (1 - δ)) * Real.sqrt m) - 2 * δ - G) ≤ hamLaw m 0 := by
  set p := prob (unifWeight m) (hamEvent m 0) with hpdef
  have hq := prob_avoid_hamEvent_pos hm
  have hp : ∀ t, prob (unifWeight m) (hamEvent m t) ≤ p := fun t ↦ (prob_hamEvent m t).le
  have hp0 : 0 < p := prob_hamEvent_pos m 0
  have hδ1 : 0 < 1 - δ := by linarith
  rw [← prob_avoid_hamEvent] at hG ⊢
  have h1 := neg_log_le_div_add_of_le_palmGap_of_le (isProb_unifWeight m) hq hc hp hp0 hδ0
    (by linarith) σ h hG
  have h2 : -Real.log (1 - δ) ≤ 2 * δ := by
    have h3 := one_sub_inv_le_log_of_pos hδ1
    have h4 : (1 - δ)⁻¹ ≤ 1 + 2 * δ := by
      rw [inv_eq_one_div, div_le_iff₀ hδ1]
      nlinarith
    linarith
  have h3 : (∑ t, prob (unifWeight m) (hamEvent m t)) / (c * (1 - δ)) ≤
      Real.sqrt π / (c * (1 - δ)) * Real.sqrt m := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (sqrt_mul_sqrt_le_sum_prob_hamEvent m).2 (mul_pos hc hδ1).le
  calc Real.exp (-(Real.sqrt π / (c * (1 - δ)) * Real.sqrt m) - 2 * δ - G)
      ≤ Real.exp (Real.log (prob (unifWeight m) (avoid (hamEvent m) univ))) :=
        exp_le_exp.mpr (by linarith)
    _ = prob (unifWeight m) (avoid (hamEvent m) univ) := exp_log hq

/-- COD-174 (`q_m ≤ e^(-c√m)`) from (V+_B), end to end, through Corollary 4(i), (iii) of COD-198
(`results/cod-198-attempt.md`, `div_le_neg_log_of_condVar_le_bernVarSum`) and
`μ_m ≥ (√π / 2) √m` (frontier `results/frontier-2026-11-25.md` §1). Let `m ≥ 6`, `κ > 0`,
`K ∈ ℕ` and `0 ≤ δ ≤ 1 / 4`. Assume (V+_B) `V_T ≤ κ B_T` for every `T` with `⌊δ / p⌋ ≤ |T|` and
`N_T ≥ K + 1`, and the named hypothesis `Var X ≤ A μ_m` (`hVar`, not proved here). Then
`q_m ≤ exp(-c √m + C')` with `c = √π / (2κ)` and `C' = (8 A δ + K (K + 1) / 2) / κ`. With `δ = 0`
the window is every `T` with `N_T ≥ K + 1`, `C'` does not involve `A`, and `hVar` holds with
`A = Var X / μ_m`. -/
theorem hamLaw_zero_le_exp_neg_sqrt {m : ℕ} [NeZero m] (hm : 6 ≤ m) {κ A δ : ℝ} {K : ℕ}
    (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hVar : condVar (unifWeight m) (hamEvent m) ∅ ≤
      A * ∑ t, prob (unifWeight m) (hamEvent m t))
    (hV : ∀ T : Finset (ZMod (2 * m - 1)), ⌊δ / prob (unifWeight m) (hamEvent m 0)⌋₊ ≤ T.card →
      K < Tᶜ.card →
      condVar (unifWeight m) (hamEvent m) T ≤ κ * bernVarSum (unifWeight m) (hamEvent m) T) :
    hamLaw m 0 ≤
      Real.exp (-(Real.sqrt π / (2 * κ) * Real.sqrt m) + (8 * A * δ + K * (K + 1) / 2) / κ) := by
  set p := prob (unifWeight m) (hamEvent m 0) with hpdef
  set μ := ∑ t, prob (unifWeight m) (hamEvent m t) with hμdef
  set V := condVar (unifWeight m) (hamEvent m) ∅ with hVdef
  have hq := prob_avoid_hamEvent_pos hm
  have hp : ∀ t, prob (unifWeight m) (hamEvent m t) ≤ p := fun t ↦ (prob_hamEvent m t).le
  have hp0 : 0 < p := prob_hamEvent_pos m 0
  have hp2 : p ≤ 1 / 2 := prob_hamEvent_le_half hm 0
  have hbd := sqrt_mul_sqrt_le_sum_prob_hamEvent m
  have hpi : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 from sqrt_one.symm]
    exact sqrt_le_sqrt (by linarith [one_le_pi_div_two])
  have hsm : 1 ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 from sqrt_one.symm]
    exact sqrt_le_sqrt (Nat.one_le_cast.mpr (NeZero.pos m))
  have hμ1 : 1 / 2 ≤ μ := by nlinarith [hbd.1]
  have hV0 : 0 ≤ V := condVar_nonneg (isProb_unifWeight m) ∅
  have hA : 0 ≤ A := by
    by_contra hA
    push Not at hA
    nlinarith
  have h := div_le_neg_log_of_condVar_le_bernVarSum (isProb_unifWeight m) hq hp hp0 hδ0
    (by linarith) (by linarith) hκ hV
  have hden : μ / 8 ≤ (1 - δ - p) * (μ - δ) := by nlinarith
  have hC : V * δ / ((1 - δ - p) * (μ - δ)) ≤ 8 * A * δ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hVar hδ0, mul_nonneg hA hδ0]
  have h2 : (Real.sqrt π / 2 * Real.sqrt m - 8 * A * δ - K * (K + 1) / 2) / κ ≤
      -Real.log (prob (unifWeight m) (avoid (hamEvent m) univ)) :=
    le_trans (div_le_div_of_nonneg_right (by linarith [hbd.1]) hκ.le) h
  have e : -(Real.sqrt π / (2 * κ) * Real.sqrt m) + (8 * A * δ + K * (K + 1) / 2) / κ =
      -((Real.sqrt π / 2 * Real.sqrt m - 8 * A * δ - K * (K + 1) / 2) / κ) := by
    field_simp
    ring
  rw [← prob_avoid_hamEvent, e]
  calc prob (unifWeight m) (avoid (hamEvent m) univ)
      = Real.exp (Real.log (prob (unifWeight m) (avoid (hamEvent m) univ))) := (exp_log hq).symm
    _ ≤ _ := exp_le_exp.mpr (by linarith)

end RoundRobin.Canonical

end Pairing
