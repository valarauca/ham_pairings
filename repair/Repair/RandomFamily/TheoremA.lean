import Mathlib.Analysis.Complex.ExponentialBounds
import Repair.RandomFamily.FirstMoment

/-!
# Theorem A: almost every family has repair radius of order `√m / log m` (COD-272)

Source: `results/random-family-lb-extend.md` §1.3 (Theorem A, Corollary A1) and §5 items G5 to G7,
and `results/random-family-lb-contra.md` §1.3 and §1.6 (Theorem A′) (organize-archive fc1a04f),
checked in `results/random-family-lb-factcheck-extend.md` and `-contra.md` (2f3e50f).

Families `M : ι → PerfectMatching (Vertex m)` carry the counting measure, which is the law of
`n = |ι|` i.i.d. uniform perfect matchings. Put `N = (2m - 1)!!`, `D = 2^(m-1)(m-1)!`,
`p = D / N`, `μ = n p`, `D3 = (2m - 1)(2m - 3)(2m - 5)` and `S_K(m)` as in `RepairBound.lean`.
`badFamilies ι m K` is the set of families with `N(M, G) ≤ K` at some six-vertex gadget `G`.
Markov's inequality is done by counting.

* `RandomFamily.card_badFamilies_le` : `#bad ≤ (N - D)^n D3 S_K(m)` in `ℕ`.
* `RandomFamily.card_badFamilies_le_beta` (Theorem A, finite form) :
  `#bad ≤ #families · β_K(m)` with `β_K(m) = (1 - p)^n D3 S_K(m)`, for `m ≥ 3`.
* `RandomFamily.one_sub_pHam_pow_le` : `(1 - p)^n ≤ e^(-np)`.
* `RandomFamily.card_badFamilies_le_exp` : `#bad ≤ #families · e^(-np)(K + 1)(2m)^(K+3)`.
* `RandomFamily.mul_pHam_eq_sum`, `RandomFamily.sub_le_mul_pHam`,
  `RandomFamily.one_sub_pHam_pow_le_sqrt` : at `n = 2m - 1`, `μ = ∑_t U(A_t)`, so
  `√(πm) - √π / (2√m) ≤ μ ≤ √(πm)` by `sub_le_sum_prob_hamEvent`, and
  `(1 - p)^(2m-1) ≤ e^(-μ) ≤ e^(-(√(πm) - √π / (2√m)))`.
* `RandomFamily.corollaryA1` (Corollary A1) : at `n = 2m - 1`, for `θ ≥ 0` and
  `(K + 4) log(2m) ≤ (1 - θ)μ`, at most a fraction `e^(-θμ)` of the families have
  `N(M, G) ≤ K` at some gadget.
* `RandomFamily.corollaryA1_floor` : the same at `K = ⌊(1 - θ)μ / log(2m)⌋ - 4`, which is
  Corollary A1 as stated in the extend.
* `RandomFamily.corollaryA1_sqrt` : the same with `μ` replaced by `√(πm) - √π / (2√m)`, for
  `0 ≤ θ ≤ 1`.
-/

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching Real ChainRule

open Classical in
/-- The families `M` with `N(M, G) ≤ K` at some six-vertex gadget `G`, the event of Theorem A
(`random-family-lb-extend.md` §1.3, fc1a04f). -/
noncomputable def badFamilies (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m]
    (K : ℕ) : Finset (ι → PerfectMatching (Vertex m)) :=
  Finset.univ.filter fun M ↦
    ∃ G : Finset (Vertex m), G.card = 6 ∧ RepairBoundFor (zeroStates M) G K

/-- `p = 2^(m-1)(m-1)! / (2m - 1)!!`, the probability that `P ∪ X` is one cycle for a fixed `P`
and a uniform `X` (`random-family-lb-extend.md` §0, fc1a04f). It is `Pairing.hamProb m` of
`Repair.HybridPair.CommonEdge`, restated here so that this file does not import it. -/
noncomputable def pHam (m : ℕ) : ℝ :=
  (2 ^ (m - 1) * (m - 1).factorial : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ)

variable {m : ℕ} [NeZero m]

/-- `M` is bad iff `N(M, G) ≤ K` at some six-vertex gadget `G`. -/
theorem mem_badFamilies {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
    {M : ι → PerfectMatching (Vertex m)} :
    M ∈ badFamilies ι m K ↔
      ∃ G : Finset (Vertex m), G.card = 6 ∧ RepairBoundFor (zeroStates M) G K := by
  simp [badFamilies]

/-- Theorem A in `ℕ`, with Markov done by counting (`random-family-lb-extend.md` §1.3 and §5 item
G5, fc1a04f). The number of families `M : ι → PerfectMatching (Vertex m)` with `N(M, G) ≤ K` at
some six-vertex gadget `G` is at most `(N - D)^n (2m - 1)(2m - 3)(2m - 5) S_K(m)`, where
`N = (2m - 1)!!`, `D = 2^(m-1)(m-1)!` and `n = |ι|`. -/
theorem card_badFamilies_le (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℕ) :
    (badFamilies ι m K).card ≤
      (Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial) ^ Fintype.card ι *
        ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) := by
  have h : (badFamilies ι m K).card * Nat.doubleFactorial (2 * m - 1) ≤
      (Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial) ^ Fintype.card ι *
        ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) *
          Nat.doubleFactorial (2 * m - 1) := by
    calc (badFamilies ι m K).card * Nat.doubleFactorial (2 * m - 1)
        = (badFamilies ι m K).card • Nat.doubleFactorial (2 * m - 1) := (smul_eq_mul _ _).symm
      _ ≤ ∑ M ∈ badFamilies ι m K, (zeroStates M).card *
            ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) :=
          Finset.card_nsmul_le_sum _ _ _ fun M hM ↦ by
            obtain ⟨G, hG, hK⟩ := mem_badFamilies.mp hM
            exact doubleFactorial_le_card_mul hG hK
      _ ≤ ∑ M, (zeroStates M).card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = (∑ M, (zeroStates M).card) *
            ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * ballBound m K) :=
          (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [sum_card_zeroStates]; ring
  exact Nat.le_of_mul_le_mul_right h (Nat.doubleFactorial_pos _)

omit [NeZero m] in
/-- `0 ≤ p`. -/
theorem pHam_nonneg : 0 ≤ pHam m := by
  unfold pHam
  positivity

/-- `p ≤ 1`, since `D ≤ N`. -/
theorem pHam_le_one : pHam m ≤ 1 := by
  unfold pHam
  rw [div_le_one (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))]
  exact_mod_cast ham_count_le

/-- **Theorem A**, finite form (`random-family-lb-extend.md` §1.3, fc1a04f;
`random-family-lb-contra.md` §1.6, Theorem A′). For `m ≥ 3`, the number of families
`M : ι → PerfectMatching (Vertex m)` with `N(M, G) ≤ K` at some six-vertex gadget `G` is at most
the number of families times `β_K(m) = (1 - p)^n (2m - 1)(2m - 3)(2m - 5) S_K(m)`, with
`n = |ι|`. -/
theorem card_badFamilies_le_beta (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℕ) :
    ((badFamilies ι m K).card : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        ((1 - pHam m) ^ Fintype.card ι * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5)) *
          ballBound m K) := by
  have hN : (0 : ℝ) < Nat.doubleFactorial (2 * m - 1) :=
    Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  have e1 : ((Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) =
      Nat.doubleFactorial (2 * m - 1) * (1 - pHam m) := by
    rw [Nat.cast_sub ham_count_le, pHam, mul_sub, mul_one, mul_div_cancel₀ _ hN.ne']
    push_cast
    ring
  have e2 : (((2 * m - 1) * (2 * m - 3) * (2 * m - 5) : ℕ) : ℝ) =
      (2 * m - 1) * (2 * m - 3) * (2 * m - 5) := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_sub (show 3 ≤ 2 * m by omega),
      Nat.cast_sub (show 5 ≤ 2 * m by omega)]
    ring
  have h : ((badFamilies ι m K).card : ℝ) ≤
      ((Nat.doubleFactorial (2 * m - 1) - 2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ^
          Fintype.card ι *
        ((((2 * m - 1) * (2 * m - 3) * (2 * m - 5) : ℕ) : ℝ) * ballBound m K) := by
    exact_mod_cast card_badFamilies_le ι K
  rw [e1, e2, mul_pow] at h
  rw [Fintype.card_fun, Nat.cast_pow, card_eq_doubleFactorial (card_vertex m)]
  calc ((badFamilies ι m K).card : ℝ) ≤ _ := h
    _ = _ := by ring

/-- `(1 - p)^n ≤ e^(-np)` (`random-family-lb-extend.md` §5 item G6, fc1a04f), from
`1 - x ≤ e^(-x)`. -/
theorem one_sub_pHam_pow_le (n : ℕ) : (1 - pHam m) ^ n ≤ exp (-(n * pHam m)) := by
  calc (1 - pHam m) ^ n ≤ exp (-pHam m) ^ n :=
        pow_le_pow_left₀ (sub_nonneg.mpr pHam_le_one)
          (by linarith [add_one_le_exp (-pHam m)]) n
    _ = exp (-(n * pHam m)) := by
        rw [← exp_nat_mul]
        ring_nf

/-- Theorem A, exponential form (`random-family-lb-extend.md` §1.3, fc1a04f). For `m ≥ 3`, at
most a fraction `e^(-np)(K + 1)(2m)^(K+3)` of the families `M : ι → PerfectMatching (Vertex m)`
have `N(M, G) ≤ K` at some six-vertex gadget `G`, with `n = |ι|`. -/
theorem card_badFamilies_le_exp (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℕ) :
    ((badFamilies ι m K).card : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        (exp (-(Fintype.card ι * pHam m)) * (K + 1) * (2 * m) ^ (K + 3)) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) ≤ 2 * m - 1 := by linarith
  have h3 : (0 : ℝ) ≤ 2 * m - 3 := by linarith
  have h5 : (0 : ℝ) ≤ 2 * m - 5 := by linarith
  have hD3n : (0 : ℝ) ≤ (2 * m - 1) * (2 * m - 3) * (2 * m - 5) :=
    mul_nonneg (mul_nonneg h1 h3) h5
  have hD3 : (2 * m - 1) * (2 * m - 3) * (2 * m - 5) ≤ ((2 * m) ^ 3 : ℝ) := by
    calc (2 * m - 1) * (2 * m - 3) * (2 * m - 5) ≤ (2 * m : ℝ) * (2 * m) * (2 * m) :=
          mul_le_mul (mul_le_mul (by linarith) (by linarith) h3 (by linarith)) (by linarith) h5
            (by positivity)
      _ = (2 * m) ^ 3 := by ring
  have hS : (ballBound m K : ℝ) ≤ (K + 1) * (2 * m) ^ K := by exact_mod_cast ballBound_le K
  refine (card_badFamilies_le_beta hm ι K).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  calc (1 - pHam m) ^ Fintype.card ι * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5)) *
        (ballBound m K : ℝ)
      ≤ exp (-(Fintype.card ι * pHam m)) * (2 * m) ^ 3 * ((K + 1) * (2 * m) ^ K) :=
        mul_le_mul (mul_le_mul (one_sub_pHam_pow_le _) hD3 hD3n (exp_pos _).le) hS
          (Nat.cast_nonneg _) (by positivity)
    _ = exp (-(Fintype.card ι * pHam m)) * (K + 1) * (2 * m) ^ (K + 3) := by ring

/-- At `n = 2m - 1`, `μ = n p` is the round-robin sum `∑_t U(A_t)` (`random-family-lb-contra.md`
§1.3, fc1a04f), by `sum_prob_hamEvent` and `prob_hamEvent_eq`. -/
theorem mul_pHam_eq_sum :
    (2 * m - 1 : ℝ) * pHam m = ∑ t, prob (unifWeight m) (hamEvent m t) := by
  rw [sum_prob_hamEvent, prob_hamEvent_eq, pHam]

/-- `√(πm) - √π / (2√m) ≤ μ ≤ √(πm)` for `μ = (2m - 1)p` (`random-family-lb-contra.md` §1.3,
fc1a04f), from `sub_le_sum_prob_hamEvent`. -/
theorem sub_le_mul_pHam :
    √(π * m) - √π / (2 * √m) ≤ (2 * m - 1 : ℝ) * pHam m ∧
      (2 * m - 1 : ℝ) * pHam m ≤ √(π * m) := by
  rw [mul_pHam_eq_sum]
  exact sub_le_sum_prob_hamEvent m

/-- `(1 - p)^(2m-1) ≤ e^(-μ) ≤ e^(-(√(πm) - √π / (2√m)))` for `μ = (2m - 1)p`
(`random-family-lb-extend.md` §5 item G6, fc1a04f). -/
theorem one_sub_pHam_pow_le_sqrt :
    (1 - pHam m) ^ (2 * m - 1) ≤ exp (-((2 * m - 1 : ℝ) * pHam m)) ∧
      exp (-((2 * m - 1 : ℝ) * pHam m)) ≤ exp (-(√(π * m) - √π / (2 * √m))) := by
  refine ⟨?_, exp_le_exp.mpr (neg_le_neg sub_le_mul_pHam.1)⟩
  have h := one_sub_pHam_pow_le (m := m) (2 * m - 1)
  rwa [Nat.cast_sub (by have := NeZero.pos m; omega), Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] at h

/-- **Corollary A1** (`random-family-lb-extend.md` §1.3, fc1a04f), at `n = |ι| = 2m - 1` and
`μ = (2m - 1)p`. For `m ≥ 3`, `θ ≥ 0` and `K` with `(K + 4) log(2m) ≤ (1 - θ)μ`, at most a
fraction `e^(-θμ)` of the families `M : ι → PerfectMatching (Vertex m)` have `N(M, G) ≤ K` at
some six-vertex gadget `G`. -/
theorem corollaryA1 (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ}
    (hK : (K + 4) * log (2 * m) ≤ (1 - θ) * ((2 * m - 1) * pHam m)) :
    ((badFamilies ι m K).card : ℝ) / Fintype.card (ι → PerfectMatching (Vertex m)) ≤
      exp (-(θ * ((2 * m - 1) * pHam m))) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : (Fintype.card ι : ℝ) = 2 * m - 1 := by
    rw [hι, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hμ0 : 0 ≤ (2 * m - 1 : ℝ) * pHam m := mul_nonneg (by linarith) pHam_nonneg
  have hμ1 : (2 * m - 1 : ℝ) * pHam m ≤ 2 * m - 1 :=
    mul_le_of_le_one_right (by linarith) pHam_le_one
  have hlog : 1 ≤ log (2 * m) := by
    rw [le_log_iff_exp_le (by positivity)]
    have := exp_one_lt_d9
    norm_num at this
    linarith
  have hK1 : (K + 1 : ℝ) ≤ 2 * m := by
    have h1 : (K + 4 : ℝ) ≤ (K + 4) * log (2 * m) := le_mul_of_one_le_right (by positivity) hlog
    have h2 : (1 - θ) * ((2 * m - 1) * pHam m) ≤ (2 * m - 1) * pHam m := by nlinarith
    linarith
  have hpow : (K + 1 : ℝ) * (2 * m) ^ (K + 3) ≤ exp ((1 - θ) * ((2 * m - 1) * pHam m)) := by
    calc (K + 1 : ℝ) * (2 * m) ^ (K + 3) ≤ (2 * m) * (2 * m) ^ (K + 3) :=
          mul_le_mul_of_nonneg_right hK1 (by positivity)
      _ = exp (log (2 * m)) ^ (K + 4) := by rw [exp_log (by positivity)]; ring
      _ = exp ((K + 4) * log (2 * m)) := by rw [← exp_nat_mul]; push_cast; ring_nf
      _ ≤ exp ((1 - θ) * ((2 * m - 1) * pHam m)) := exp_le_exp.mpr hK
  have hC : (0 : ℝ) < Fintype.card (ι → PerfectMatching (Vertex m)) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨fun _ ↦ factor m 0⟩)
  rw [div_le_iff₀ hC]
  have h := card_badFamilies_le_exp hm ι K
  rw [hn] at h
  calc ((badFamilies ι m K).card : ℝ)
      ≤ Fintype.card (ι → PerfectMatching (Vertex m)) *
          (exp (-((2 * m - 1) * pHam m)) * ((K + 1) * (2 * m) ^ (K + 3))) := by
        rw [← mul_assoc (exp _)]
        exact h
    _ ≤ Fintype.card (ι → PerfectMatching (Vertex m)) *
          (exp (-((2 * m - 1) * pHam m)) * exp ((1 - θ) * ((2 * m - 1) * pHam m))) := by
        gcongr
    _ = exp (-(θ * ((2 * m - 1) * pHam m))) * Fintype.card (ι → PerfectMatching (Vertex m)) := by
        rw [← exp_add]
        ring_nf

/-- **Corollary A1** with the floor, as stated in `random-family-lb-extend.md` §1.3 (fc1a04f),
at `n = |ι| = 2m - 1` and `μ = (2m - 1)p`. For `m ≥ 3` and `θ ≥ 0`, put
`K₀ = ⌊(1 - θ)μ / log(2m)⌋`. If `K₀ ≥ 4`, at most a fraction `e^(-θμ)` of the families have
`N(M, G) ≤ K₀ - 4` at some six-vertex gadget, so with probability at least `1 - e^(-θμ)` every
gadget has `N(M, G) ≥ K₀ - 3`. -/
theorem corollaryA1_floor (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (h4 : 4 ≤ ⌊(1 - θ) * ((2 * m - 1) * pHam m) / log (2 * m)⌋₊) :
    ((badFamilies ι m (⌊(1 - θ) * ((2 * m - 1) * pHam m) / log (2 * m)⌋₊ - 4)).card : ℝ) /
        Fintype.card (ι → PerfectMatching (Vertex m)) ≤
      exp (-(θ * ((2 * m - 1) * pHam m))) := by
  refine corollaryA1 hm ι hι hθ ?_
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < log (2 * m) := log_pos (by linarith)
  have hx : 0 ≤ (1 - θ) * ((2 * m - 1) * pHam m) / log (2 * m) := by
    by_contra h
    rw [Nat.floor_of_nonpos (not_le.mp h).le] at h4
    omega
  rw [Nat.cast_sub h4, Nat.cast_ofNat, sub_add_cancel]
  calc (⌊(1 - θ) * ((2 * m - 1) * pHam m) / log (2 * m)⌋₊ : ℝ) * log (2 * m)
      ≤ (1 - θ) * ((2 * m - 1) * pHam m) / log (2 * m) * log (2 * m) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hx) hlog.le
    _ = (1 - θ) * ((2 * m - 1) * pHam m) := div_mul_cancel₀ _ hlog.ne'

/-- **Corollary A1** in `√m` form (`random-family-lb-extend.md` §1.3, fc1a04f), at
`n = |ι| = 2m - 1`, with `L = √(πm) - √π / (2√m) ≤ μ`. For `m ≥ 3`, `0 ≤ θ ≤ 1` and `K` with
`(K + 4) log(2m) ≤ (1 - θ)L`, at most a fraction `e^(-θL)` of the families have `N(M, G) ≤ K`
at some six-vertex gadget. -/
theorem corollaryA1_sqrt (hm : 3 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {K : ℕ}
    (hK : (K + 4) * log (2 * m) ≤ (1 - θ) * (√(π * m) - √π / (2 * √m))) :
    ((badFamilies ι m K).card : ℝ) / Fintype.card (ι → PerfectMatching (Vertex m)) ≤
      exp (-(θ * (√(π * m) - √π / (2 * √m)))) := by
  have hL := (sub_le_mul_pHam (m := m)).1
  refine (corollaryA1 hm ι hι hθ0
    (hK.trans (mul_le_mul_of_nonneg_left hL (by linarith)))).trans ?_
  exact exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hL hθ0))

end RoundRobin.Canonical.RandomFamily

end Pairing
