import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Suppression.HamCount

/-!
# Chain-rule reductions for `q = U(no A_t)` (COD-190, COD-196)

Let `P` be a probability weight on a finite set `Ω` (`IsProb P`, `Prob.lean`), with law `U`, and let
`A : ι → Set Ω` be events indexed by a finite set `ι` with `n = |ι|`. For `T ⊆ ι` put
`Z_T = ⋂_{s ∈ T} A_sᶜ` (`avoid A T`), `f_t(T) = U(A_t | Z_T)` (`condProb`),
`g_T(s, t) = U(A_s A_t | Z_T) / (f_s(T) f_t(T))` (`pairRatio`, set to `1` when
`f_s(T) f_t(T) = 0`), `Cov_T(s, t) = U(A_s A_t | Z_T) - f_s(T) f_t(T)` (`condCov`) and
`q = U(Z_ι)`. Conditional probabilities given a null event are `0`. An ordering is an
equivalence `σ : Fin n ≃ ι`, with prefixes `T_k = {σ 0, …, σ (k - 1)}` (`pre σ k`).

From `cod-190-delta-proof-attempt.md` (COD-190):

* `condProb_insert` (Lemma 2) : `f_t(T ∪ v) = f_t(T) (1 - f_v g_T(t, v)) / (1 - f_v)` for
  `f_v(T) < 1`, and `condProb_insert_mul`, its multiplied-out form with no hypothesis.
* `prob_avoid_univ` (chain rule) : `q = ∏_k (1 - f_{σ k}(T_k))` for every ordering `σ`.
* `condProb_le_mul_pow`, `condProb_le_mul` (Proposition 3(1)) : if `U(A_t) ≤ p`, `ε ≥ 0`,
  `b > 1`, `b p < 1`, `(★) n ε b p / (1 - b p) ≤ log b` and `g_T ≥ 1 - ε`, then
  `f_t(T) ≤ min(b p, p β^|T|)` with `β = 1 + ε b p / (1 - b p)`. `prod_le_prob_avoid`,
  `neg_log_prob_avoid_le` and `pow_le_prob_avoid` give the bounds on `q` and `-log q`.
* `mul_pow_le_condProb_of_mem_Icc`, `pow_mul_le_condProb_of_mem_Icc`,
  `prob_avoid_le_pow_of_mem_Icc`, `prob_avoid_le_exp_of_mem_Icc` (Proposition 3(2)) : if also
  `p' ≤ U(A_t)`, `g_T ≤ 1 + ε'`, `ε' ≥ 0` and `ε' b p < 1 - b p`, then `f_t(T) ≥ α p'` and
  `q ≤ (1 - α p')^n ≤ e^(-α n p')`. The paper's common probability `U(A_t) = p` is the case
  `p' = p` (`mul_pow_le_condProb`, `pow_mul_le_condProb`, `prob_avoid_le_pow`,
  `prob_avoid_le_exp`).

From `conditional-pair-bound-attempt.md`:

* `condProb_pre_le_mul`, `pow_le_prob_avoid_of_pre` (Proposition 4(1)) : the prefix-dropped
  form, with `(★_J) exp(n ε b p / (1 - b p)) ≤ (1 - J p) b` and the union-bound start
  `one_sub_sum_le_prob_avoid`.
* `mul_le_condProb_pre_of_mem_Icc`, `prob_avoid_le_pow_of_pre_of_mem_Icc` (Proposition 4(2)) :
  the lower bound for `p' ≤ U(A_t) ≤ p`, with the Bonferroni start `sub_sum_le_prob_inter_avoid`
  (through `mul_le_condProb_of_le`, which needs only `U(A_t) ≥ p'`) and any `R` with
  `U(A_x A_y) ≤ R p'²`. `mul_le_condProb_pre` and `prob_avoid_le_pow_of_pre` are the case
  `p' = p`.

From `cod-196-averaged-pinning.md` (COD-196):

* `condProb_insert_sub` (Proposition 6) : `f_t(T ∪ s) - f_t(T) = -Cov_T(s, t) / (1 - f_s(T))`.
* `chainAvg` is `E_π ∑_k G(T_k, π_k)` for a uniformly random ordering, computed level by
  level, and `chainAvg_eq_sum_equiv` identifies it with the average over all `n!` orderings.
* `levelAvg_outAvg_succ`, `chainAvg_condProb`, `sum_equiv_condProb` (Proposition 6) : for
  `q > 0`, `m̄_{i+1} = m̄_i - E Δ_T / (n - i - 1)` and `E_π ∑_k f_k = μ - ∑_{i ≤ n - 2} E Δ_T`.
* `chainAvg_le_neg_log`, `neg_log_le_chainAvg`, `sum_equiv_le_neg_log_le` (Proposition 6) :
  `E_π ∑_k f_k ≤ -log q ≤ E_π ∑_k f_k / (1 - f_k)`.
* `sq_div_le_binMI`, `sum_abs_sub_le_binMI` (Lemma 3) : the chi-square lower bound on binary
  mutual information `binMI` and its summed form.
* `abs_chainAvg_sub_le`, `div_le_neg_log_prob_avoid`, `neg_log_prob_avoid_le_div`
  (Theorem 7 under (B′)) : with (A) `f ≤ φ < 1` and (B′)
  `∑_{s ≠ t ∉ T} |Cov_T(s, t)| ≤ 2 √J M_T + 4 J` for `N_T ≥ K + 2`,
  `(μ - η) / (1 + θ) ≤ -log q`, and `-log q ≤ (μ + η) / ((1 - φ)(1 - θ))` when `θ < 1`.
* `div_le_neg_log_prob_avoid_of_pairInfo`, `neg_log_prob_avoid_le_div_of_pairInfo`
  (Theorem 7) : the same under (B) `J_T ≤ J`, through Lemma 3 (`sum_abs_condCov_le`).

For the round-robin events (`hamEvent m t = {P | P ∪ F_t is one cycle}` under the uniform law
`unifWeight m` of `HamCount.lean`): `prob_hamEvent` (the common probability `p`) and
`prob_avoid_hamEvent` (`q = hamLaw m 0 = q_m`).
-/

namespace Pairing

namespace ChainRule

open Finset

variable {Ω ι : Type*}

/-- `Z_T = ⋂_{s ∈ T} A_sᶜ`, the event that no `A_s` with `s ∈ T` occurs. -/
def avoid (A : ι → Set Ω) (T : Finset ι) : Set Ω :=
  {ω | ∀ s ∈ T, ω ∉ A s}

/-- `f_t(T) = U(A_t | Z_T)`, which is `0` when `U(Z_T) = 0`. -/
noncomputable def condProb [Fintype Ω] (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (t : ι) : ℝ :=
  prob P (A t ∩ avoid A T) / prob P (avoid A T)

/-- `U(A_s A_t | Z_T)`, which is `0` when `U(Z_T) = 0`. -/
noncomputable def condPair [Fintype Ω] (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s t : ι) : ℝ :=
  prob P (A s ∩ A t ∩ avoid A T) / prob P (avoid A T)

/-- The conditional pair ratio `g_T(s, t) = U(A_s A_t | Z_T) / (f_s(T) f_t(T))`, set to `1` when
`f_s(T) f_t(T) = 0` as in the papers. -/
noncomputable def pairRatio [Fintype Ω] (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s t : ι) : ℝ :=
  if condProb P A T s * condProb P A T t = 0 then 1
  else condPair P A T s t / (condProb P A T s * condProb P A T t)

/-- `Cov_T(s, t) = U(A_s A_t | Z_T) - f_s(T) f_t(T)`. -/
noncomputable def condCov [Fintype Ω] (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s t : ι) : ℝ :=
  condPair P A T s t - condProb P A T s * condProb P A T t

/-- `T_k = {σ 0, …, σ (k - 1)}`, the first `k` elements of the ordering `σ`. -/
def pre {n : ℕ} (σ : Fin n ≃ ι) (k : ℕ) : Finset ι :=
  (univ.filter fun j : Fin n ↦ (j : ℕ) < k).map σ.toEmbedding

/-- `x ∈ T_k` exactly when `x` sits at a position `< k` of the ordering `σ`. -/
theorem mem_pre {n : ℕ} {σ : Fin n ≃ ι} {k : ℕ} {x : ι} : x ∈ pre σ k ↔ (σ.symm x : ℕ) < k := by
  simp [pre, mem_map_equiv]

/-- `T_0 = ∅`. -/
theorem pre_zero {n : ℕ} (σ : Fin n ≃ ι) : pre σ 0 = ∅ := by
  ext x
  simp [mem_pre]

/-- `σ j ∉ T_k` for `k ≤ j`. -/
theorem notMem_pre {n : ℕ} (σ : Fin n ≃ ι) {k : ℕ} {j : Fin n} (hk : k ≤ j) : σ j ∉ pre σ k := by
  simp [mem_pre, hk]

/-- `T_n = ι` for an ordering `σ : Fin n ≃ ι`. -/
theorem pre_eq_univ [Fintype ι] {n : ℕ} (σ : Fin n ≃ ι) : pre σ n = univ := by
  ext x
  simp [mem_pre]

/-- `Z_∅` is the whole space. -/
theorem avoid_empty (A : ι → Set Ω) : avoid A ∅ = Set.univ := by
  ext
  simp [avoid]

/-- `T ⊆ T'` gives `Z_{T'} ⊆ Z_T`. -/
theorem avoid_anti {A : ι → Set Ω} {T T' : Finset ι} (h : T ⊆ T') : avoid A T' ⊆ avoid A T :=
  fun _ hω s hs ↦ hω s (h hs)

/-- `A_t ∩ Z_T = ∅` for `t ∈ T`. -/
theorem inter_avoid_eq_empty {A : ι → Set Ω} {T : Finset ι} {t : ι} (ht : t ∈ T) :
    A t ∩ avoid A T = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun h1 h2 ↦ h2 t ht h1

section DecidableEq

variable [DecidableEq ι]

/-- `Z_{T ∪ v} = Z_T ∖ A_v`. -/
theorem avoid_insert (A : ι → Set Ω) (T : Finset ι) (v : ι) :
    avoid A (insert v T) = avoid A T \ A v := by
  ext ω
  simp [avoid, and_comm]

/-- `T_{k+1} = T_k ∪ {σ k}`. -/
theorem pre_succ {n : ℕ} (σ : Fin n ≃ ι) {k : ℕ} (hk : k < n) :
    pre σ (k + 1) = insert (σ ⟨k, hk⟩) (pre σ k) := by
  ext x
  rw [mem_insert, mem_pre, mem_pre]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl ((Equiv.symm_apply_eq σ).mp (Fin.ext h))
  · rintro (rfl | h)
    · simp
    · omega

end DecidableEq

variable [Fintype Ω] {P : Ω → ℝ} {A : ι → Set Ω}

/-- `f_t(T) ≥ 0`. -/
theorem condProb_nonneg (hP : IsProb P) (T : Finset ι) (t : ι) : 0 ≤ condProb P A T t :=
  div_nonneg (prob_nonneg hP _) (prob_nonneg hP _)

/-- `f_t(T) ≤ 1`. -/
theorem condProb_le_one (hP : IsProb P) (T : Finset ι) (t : ι) : condProb P A T t ≤ 1 :=
  div_le_one_of_le₀ (prob_mono hP Set.inter_subset_right) (prob_nonneg hP _)

/-- `U(A_s A_t | Z_T) ≥ 0`. -/
theorem condPair_nonneg (hP : IsProb P) (T : Finset ι) (s t : ι) : 0 ≤ condPair P A T s t :=
  div_nonneg (prob_nonneg hP _) (prob_nonneg hP _)

/-- `U(A_s A_t | Z_T)` is symmetric in `s` and `t`. -/
theorem condPair_comm (T : Finset ι) (s t : ι) : condPair P A T s t = condPair P A T t s := by
  rw [condPair, condPair, Set.inter_comm (A s)]

/-- `U(A_s A_t | Z_T) ≤ f_s(T)`. -/
theorem condPair_le_left (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condPair P A T s t ≤ condProb P A T s :=
  div_le_div_of_nonneg_right (prob_mono hP (Set.inter_subset_inter_left _
    Set.inter_subset_left)) (prob_nonneg hP _)

/-- `U(A_s A_t | Z_T) ≤ f_t(T)`. -/
theorem condPair_le_right (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condPair P A T s t ≤ condProb P A T t :=
  condPair_comm (P := P) (A := A) T s t ▸ condPair_le_left hP T t s

/-- `f_t(T) = 0` for `t ∈ T`. -/
theorem condProb_of_mem {T : Finset ι} {t : ι} (ht : t ∈ T) : condProb P A T t = 0 := by
  simp [condProb, inter_avoid_eq_empty ht, prob]

/-- `f_t(∅) = U(A_t)`. -/
theorem condProb_empty (hP : IsProb P) (t : ι) : condProb P A ∅ t = prob P (A t) := by
  rw [condProb, avoid_empty, Set.inter_univ, prob_univ hP, div_one]

/-- `f_t(T) U(Z_T) = U(A_t ∩ Z_T)`, also when `U(Z_T) = 0`. -/
theorem condProb_mul_prob (hP : IsProb P) (T : Finset ι) (t : ι) :
    condProb P A T t * prob P (avoid A T) = prob P (A t ∩ avoid A T) := by
  by_cases hz : prob P (avoid A T) = 0
  · rw [hz, mul_zero, prob_eq_zero_of_subset hP Set.inter_subset_right hz]
  · exact div_mul_cancel₀ _ hz

/-- `U(A_s A_t | Z_T) U(Z_T) = U(A_s A_t ∩ Z_T)`, also when `U(Z_T) = 0`. -/
theorem condPair_mul_prob (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condPair P A T s t * prob P (avoid A T) = prob P (A s ∩ A t ∩ avoid A T) := by
  by_cases hz : prob P (avoid A T) = 0
  · rw [hz, mul_zero, prob_eq_zero_of_subset hP Set.inter_subset_right hz]
  · exact div_mul_cancel₀ _ hz

/-- `f_s(T) f_t(T) g_T(s, t) = U(A_s A_t | Z_T)`, also where `f_s(T) f_t(T) = 0`. -/
theorem condProb_mul_pairRatio (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condProb P A T s * condProb P A T t * pairRatio P A T s t = condPair P A T s t := by
  rw [pairRatio]
  split_ifs with h
  · rw [h, zero_mul]
    rcases mul_eq_zero.mp h with h | h
    · exact le_antisymm (condPair_nonneg hP T s t) ((condPair_le_left hP T s t).trans h.le)
    · exact le_antisymm (condPair_nonneg hP T s t) ((condPair_le_right hP T s t).trans h.le)
  · exact mul_div_cancel₀ _ h

/-- `g_T(s, t) ≥ 1 - ε` gives `U(A_s A_t | Z_T) ≥ (1 - ε) f_s(T) f_t(T)`. -/
theorem le_condPair_of_le_pairRatio (hP : IsProb P) {T : Finset ι} {s t : ι} {ε : ℝ}
    (h : 1 - ε ≤ pairRatio P A T s t) :
    (1 - ε) * (condProb P A T s * condProb P A T t) ≤ condPair P A T s t := by
  rw [← condProb_mul_pairRatio hP, mul_comm]
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (condProb_nonneg hP T s) (condProb_nonneg hP T t))

/-- `g_T(s, t) ≤ 1 + ε'` gives `U(A_s A_t | Z_T) ≤ (1 + ε') f_s(T) f_t(T)`. -/
theorem condPair_le_of_pairRatio_le (hP : IsProb P) {T : Finset ι} {s t : ι} {ε : ℝ}
    (h : pairRatio P A T s t ≤ 1 + ε) :
    condPair P A T s t ≤ (1 + ε) * (condProb P A T s * condProb P A T t) := by
  rw [← condProb_mul_pairRatio hP, mul_comm (1 + ε)]
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (condProb_nonneg hP T s) (condProb_nonneg hP T t))

/-- `U(A_t ∩ Z_T) ≤ f_t(T)`. -/
theorem prob_inter_avoid_le_condProb (hP : IsProb P) (T : Finset ι) (t : ι) :
    prob P (A t ∩ avoid A T) ≤ condProb P A T t := by
  by_cases hz : prob P (avoid A T) = 0
  · rw [prob_eq_zero_of_subset hP Set.inter_subset_right hz]
    exact condProb_nonneg hP T t
  · exact le_div_self (prob_nonneg hP _) (lt_of_le_of_ne (prob_nonneg hP _) (Ne.symm hz))
      (prob_le_one hP _)

variable [DecidableEq ι]

/-- `U(Z_{T ∪ v}) = U(Z_T) - U(A_v ∩ Z_T)`. -/
theorem prob_avoid_insert_eq_sub (A : ι → Set Ω) (T : Finset ι) (v : ι) :
    prob P (avoid A (insert v T)) = prob P (avoid A T) - prob P (A v ∩ avoid A T) := by
  rw [prob_eq_inter_add_diff P (avoid A T) (A v), avoid_insert]
  ring

/-- `U(A_t ∩ Z_{T ∪ v}) = U(A_t ∩ Z_T) - U(A_t A_v ∩ Z_T)`. -/
theorem prob_inter_avoid_insert_eq_sub (A : ι → Set Ω) (T : Finset ι) (t v : ι) :
    prob P (A t ∩ avoid A (insert v T)) =
      prob P (A t ∩ avoid A T) - prob P (A t ∩ A v ∩ avoid A T) := by
  rw [prob_eq_inter_add_diff P (A t ∩ avoid A T) (A v), avoid_insert, Set.inter_sdiff_assoc,
    show A v ∩ (A t ∩ avoid A T) = A t ∩ A v ∩ avoid A T by
      rw [← Set.inter_assoc, Set.inter_comm (A v)]]
  ring

/-- `U(Z_{T ∪ v}) = U(Z_T) (1 - f_v(T))`, the one-step chain rule. -/
theorem prob_avoid_insert (hP : IsProb P) (T : Finset ι) (v : ι) :
    prob P (avoid A (insert v T)) = prob P (avoid A T) * (1 - condProb P A T v) := by
  rw [prob_avoid_insert_eq_sub, mul_sub, mul_one, mul_comm, condProb_mul_prob hP]

/-- The multiplied-out form of Lemma 2 of COD-190 (`cod-190-delta-proof-attempt.md`),
`f_t(T ∪ v) (1 - f_v(T)) = f_t(T) - U(A_t A_v | Z_T)`, with no hypothesis. -/
theorem condProb_insert_mul (hP : IsProb P) (T : Finset ι) (t v : ι) :
    condProb P A (insert v T) t * (1 - condProb P A T v) =
      condProb P A T t - condPair P A T t v := by
  by_cases hz : prob P (avoid A T) = 0
  · have h1 : prob P (avoid A (insert v T)) = 0 :=
      prob_eq_zero_of_subset hP (avoid_anti (subset_insert v T)) hz
    simp [condProb, condPair, hz, h1]
  refine mul_right_cancel₀ hz ?_
  rw [mul_assoc, mul_comm (1 - _), ← prob_avoid_insert hP, condProb_mul_prob hP,
    prob_inter_avoid_insert_eq_sub, sub_mul, condProb_mul_prob hP, condPair_mul_prob hP]

/-- Lemma 2 of COD-190 (`cod-190-delta-proof-attempt.md`), the telescoping identity: if
`f_v(T) < 1`, then `f_t(T ∪ v) = f_t(T) (1 - f_v(T) g_T(t, v)) / (1 - f_v(T))`. -/
theorem condProb_insert (hP : IsProb P) (T : Finset ι) (t v : ι) (hv : condProb P A T v < 1) :
    condProb P A (insert v T) t =
      condProb P A T t * (1 - condProb P A T v * pairRatio P A T t v) /
        (1 - condProb P A T v) := by
  rw [eq_div_iff (sub_pos.mpr hv).ne', condProb_insert_mul hP, ← condProb_mul_pairRatio hP]
  ring

omit [DecidableEq ι] in
/-- `|T_k| = k` for `k ≤ n`. -/
theorem card_pre {n : ℕ} (σ : Fin n ≃ ι) {k : ℕ} (hk : k ≤ n) : (pre σ k).card = k := by
  classical
  induction k with
  | zero => simp [pre_zero]
  | succ k ih =>
    rw [pre_succ σ (by omega), card_insert_of_notMem (by simp [mem_pre]), ih (by omega)]

omit [DecidableEq ι] in
/-- The chain rule along an ordering, `U(Z_{T_k}) = ∏_{j < k} (1 - f_{σ j}(T_j))`. -/
theorem prob_avoid_pre (hP : IsProb P) {n : ℕ} (σ : Fin n ≃ ι) {k : ℕ} (hk : k ≤ n) :
    prob P (avoid A (pre σ k)) =
      ∏ j ∈ univ.filter (fun j : Fin n ↦ (j : ℕ) < k), (1 - condProb P A (pre σ j) (σ j)) := by
  classical
  induction k with
  | zero => simp [pre_zero, avoid_empty, prob_univ hP]
  | succ k ih =>
    have hk' : k < n := by omega
    rw [pre_succ σ hk', prob_avoid_insert hP, ih (by omega),
      show univ.filter (fun j : Fin n ↦ (j : ℕ) < k + 1) =
        insert ⟨k, hk'⟩ (univ.filter fun j : Fin n ↦ (j : ℕ) < k) by
          ext j
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          omega,
      prod_insert (by simp)]
    ring

omit [DecidableEq ι] in
/-- The chain rule of COD-190 (Proposition 3, proof), `q = U(Z_ι) = ∏_k (1 - f_{t_k}(T_{k-1}))`
for every ordering `σ` of `ι`. -/
theorem prob_avoid_univ [Fintype ι] (hP : IsProb P) {n : ℕ} (σ : Fin n ≃ ι) :
    prob P (avoid A univ) = ∏ k : Fin n, (1 - condProb P A (pre σ k) (σ k)) := by
  classical
  have h := prob_avoid_pre hP σ (A := A) (le_refl n)
  rw [pre_eq_univ] at h
  rw [h]
  exact prod_congr (filter_true_of_mem fun j _ ↦ j.isLt) fun _ _ ↦ rfl

omit [DecidableEq ι] in
/-- The union bound, `U(Z_T) ≥ 1 - ∑_{u ∈ T} U(A_u)`. -/
theorem one_sub_sum_le_prob_avoid (hP : IsProb P) (T : Finset ι) :
    1 - ∑ u ∈ T, prob P (A u) ≤ prob P (avoid A T) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [avoid_empty, prob_univ hP]
  | insert v T hv ih =>
    rw [sum_insert hv, prob_avoid_insert_eq_sub]
    linarith [prob_mono hP (Set.inter_subset_left (s := A v) (t := avoid A T))]

omit [DecidableEq ι] in
/-- The Bonferroni bound, `U(A_t ∩ Z_T) ≥ U(A_t) - ∑_{u ∈ T} U(A_t A_u)`. -/
theorem sub_sum_le_prob_inter_avoid (hP : IsProb P) (T : Finset ι) (t : ι) :
    prob P (A t) - ∑ u ∈ T, prob P (A t ∩ A u) ≤ prob P (A t ∩ avoid A T) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [avoid_empty]
  | insert v T hv ih =>
    rw [sum_insert hv, prob_inter_avoid_insert_eq_sub]
    linarith [prob_mono hP (Set.inter_subset_left (s := A t ∩ A v) (t := avoid A T))]

omit [DecidableEq ι] in
/-- If `U(A_u) ≤ p` for all `u` and `|T| p < 1`, then `f_t(T) ≤ p / (1 - |T| p)`. -/
theorem condProb_le_div (hP : IsProb P) {p : ℝ} (hp : ∀ u, prob P (A u) ≤ p) (hp0 : 0 ≤ p)
    {T : Finset ι} (hT : T.card * p < 1) (t : ι) :
    condProb P A T t ≤ p / (1 - T.card * p) := by
  classical
  have h1 : 1 - T.card * p ≤ prob P (avoid A T) := by
    refine le_trans ?_ (one_sub_sum_le_prob_avoid hP T)
    have := sum_le_sum fun u (_ : u ∈ T) ↦ hp u
    rw [sum_const, nsmul_eq_mul] at this
    linarith
  exact (div_le_div_of_nonneg_right (prob_mono hP Set.inter_subset_left)
    (prob_nonneg hP _)).trans (div_le_div₀ hp0 (hp t) (by linarith) h1)

omit [DecidableEq ι] in
/-- If `U(A_u) ≥ p` for all `u`, `U(A_x A_y) ≤ R p²` for `x ≠ y`, and `t ∉ T`, then
`f_t(T) ≥ p (1 - |T| p R)`. -/
theorem mul_le_condProb_of_le (hP : IsProb P) {p R : ℝ} (hp : ∀ u, p ≤ prob P (A u))
    (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p ^ 2) {T : Finset ι} {t : ι} (ht : t ∉ T) :
    p * (1 - T.card * p * R) ≤ condProb P A T t := by
  classical
  refine le_trans ?_ ((sub_sum_le_prob_inter_avoid hP T t).trans
    (prob_inter_avoid_le_condProb hP T t))
  have := sum_le_sum fun u (hu : u ∈ T) ↦ hR t u fun h ↦ ht (h ▸ hu)
  rw [sum_const, nsmul_eq_mul] at this
  nlinarith [hp t]

omit [DecidableEq ι] in
/-- If `U(A_u) = p` for all `u`, `U(A_x A_y) ≤ R p²` for `x ≠ y`, and `t ∉ T`, then
`f_t(T) ≥ p (1 - |T| p R)`. The lower bound `U(A_u) ≥ p` suffices (`mul_le_condProb_of_le`). -/
theorem mul_le_condProb (hP : IsProb P) {p R : ℝ} (hp : ∀ u, prob P (A u) = p)
    (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p ^ 2) {T : Finset ι} {t : ι} (ht : t ∉ T) :
    p * (1 - T.card * p * R) ≤ condProb P A T t :=
  mul_le_condProb_of_le hP (fun u ↦ (hp u).ge) hR ht

/-- One upward step of the induction in Proposition 3(1) of COD-190: if
`F (1 - a) ≤ y - (1 - ε) a y` with `0 ≤ y`, `a ≤ c < 1` and `ε ≥ 0`, then
`F ≤ y (1 + ε c / (1 - c))`. -/
theorem step_upper {F y a c ε : ℝ} (hy : 0 ≤ y) (hac : a ≤ c) (hc : c < 1)
    (hε : 0 ≤ ε) (h : F * (1 - a) ≤ y - (1 - ε) * (a * y)) : F ≤ y * (1 + ε * c / (1 - c)) := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - c := by linarith
  have key : F * (1 - c) * (1 - a) ≤ y * (1 - c + ε * c) * (1 - a) := by
    nlinarith [mul_nonneg (mul_nonneg hy hε) (sub_nonneg.2 hac), mul_le_mul_of_nonneg_right h h2.le]
  have key' := le_of_mul_le_mul_right key h1
  rw [show y * (1 + ε * c / (1 - c)) = y * (1 - c + ε * c) / (1 - c) by field_simp,
    le_div_iff₀ h2]
  exact key'

/-- One downward step of the induction in Proposition 3(2) of COD-190: if
`F (1 - a) ≥ y - (1 + ε) a y` with `0 ≤ y`, `a ≤ c < 1` and `ε ≥ 0`, then
`F ≥ y (1 - ε c / (1 - c))`. -/
theorem step_lower {F y a c ε : ℝ} (hy : 0 ≤ y) (hac : a ≤ c) (hc : c < 1)
    (hε : 0 ≤ ε) (h : y - (1 + ε) * (a * y) ≤ F * (1 - a)) : y * (1 - ε * c / (1 - c)) ≤ F := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - c := by linarith
  have key : y * (1 - c - ε * c) * (1 - a) ≤ F * (1 - c) * (1 - a) := by
    nlinarith [mul_nonneg (mul_nonneg hy hε) (sub_nonneg.2 hac), mul_le_mul_of_nonneg_right h h2.le]
  have key' := le_of_mul_le_mul_right key h1
  rw [show y * (1 - ε * c / (1 - c)) = y * (1 - c - ε * c) / (1 - c) by field_simp,
    div_le_iff₀ h2]
  exact key'

/-- `(1 + x)^k ≤ e^(n x)` for `x ≥ 0` and `k ≤ n`. -/
theorem one_add_pow_le_exp {x : ℝ} {k n : ℕ} (hx : 0 ≤ x) (hk : k ≤ n) :
    (1 + x) ^ k ≤ Real.exp (n * x) :=
  calc (1 + x) ^ k ≤ Real.exp x ^ k :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k
    _ = Real.exp (k * x) := (Real.exp_nat_mul x k).symm
    _ ≤ Real.exp (n * x) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hx)

/-- `(1 + x)^k ≤ b` for `x ≥ 0`, `k ≤ n` and `n x ≤ log b`, the use of `(★)`. -/
theorem one_add_pow_le {x b : ℝ} {k n : ℕ} (hx : 0 ≤ x) (hk : k ≤ n) (hb : 0 < b)
    (h : n * x ≤ Real.log b) : (1 + x) ^ k ≤ b :=
  (one_add_pow_le_exp hx hk).trans (by rwa [← Real.exp_log hb, Real.exp_le_exp])

/-- `p β^k ≤ b p` for `k ≤ n` under `(★) n ε b p / (1 - b p) ≤ log b`, with
`β = 1 + ε b p / (1 - b p)`, `p, ε ≥ 0`, `b > 1` and `b p < 1`. -/
theorem mul_pow_le_of_star {p ε b : ℝ} {k n : ℕ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (hb : 1 < b)
    (hbp : b * p < 1) (hk : k ≤ n) (hstar : n * ε * b * p / (1 - b * p) ≤ Real.log b) :
    p * (1 + ε * b * p / (1 - b * p)) ^ k ≤ b * p :=
  (mul_le_mul_of_nonneg_left (one_add_pow_le (div_nonneg (by positivity) (by linarith)) hk
    (by linarith) ((le_of_eq (by ring)).trans hstar)) hp).trans_eq (mul_comm p b)

/-- `γ = 1 - ε' b p / (1 - b p) ∈ [0, 1]` for `ε', b, p ≥ 0`, `b p < 1` and `ε' b p < 1 - b p`. -/
theorem one_sub_div_mem_Icc {ε' b p : ℝ} (hε' : 0 ≤ ε') (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hbp : b * p < 1) (hε'b : ε' * b * p < 1 - b * p) :
    1 - ε' * b * p / (1 - b * p) ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : 0 < 1 - b * p := by linarith
  refine ⟨?_, sub_le_self _ (div_nonneg (by positivity) hc.le)⟩
  rw [sub_nonneg, div_le_one hc]
  linarith

section Prop3

variable [Fintype ι] {p ε b : ℝ}

omit [DecidableEq ι] in
/-- Proposition 3(1) of COD-190 (`cod-190-delta-proof-attempt.md`), the refined bound. Let
`n = |ι|`, `U(A_t) ≤ p` for all `t`, `ε ≥ 0`, `b > 1`, `b p < 1` and
`(★) n ε b p / (1 - b p) ≤ log b`. If `g_T(s, t) ≥ 1 - ε` for every `T` and every pair
`s ≠ t` outside `T`, then `f_t(T) ≤ p β^|T|` for `t ∉ T`, with `β = 1 + ε b p / (1 - b p)`. -/
theorem condProb_le_mul_pow (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (T : Finset ι) {t : ι} (ht : t ∉ T) :
    condProb P A T t ≤ p * (1 + ε * b * p / (1 - b * p)) ^ T.card := by
  classical
  have hp0 : 0 ≤ p := (prob_nonneg hP _).trans (hp t)
  have hc : 0 < 1 - b * p := by linarith
  have hx : 0 ≤ ε * b * p / (1 - b * p) := div_nonneg (by positivity) hc.le
  have hpow : ∀ S : Finset ι, p * (1 + ε * b * p / (1 - b * p)) ^ S.card ≤ b * p := fun S ↦
    mul_pow_le_of_star hp0 hε hb hbp (card_le_univ S) hstar
  induction T using Finset.induction_on generalizing t with
  | empty => simpa [condProb_empty hP] using hp t
  | insert v T hv ih =>
    rw [mem_insert, not_or] at ht
    have hv' := (ih hv).trans (hpow T)
    have h := condProb_insert_mul hP (A := A) T t v
    rw [condPair_comm] at h
    have h' := le_condPair_of_le_pairRatio hP (hg T v t hv ht.2 (Ne.symm ht.1))
    have hstep := step_upper (condProb_nonneg hP T t) hv' hbp hε
      (F := condProb P A (insert v T) t) (by linarith)
    calc condProb P A (insert v T) t ≤ condProb P A T t * (1 + ε * (b * p) / (1 - b * p)) := hstep
      _ ≤ p * (1 + ε * b * p / (1 - b * p)) ^ T.card * (1 + ε * b * p / (1 - b * p)) := by
          rw [← mul_assoc ε b p]
          exact mul_le_mul_of_nonneg_right (ih ht.2) (by linarith)
      _ = _ := by rw [card_insert_of_notMem hv, pow_succ, mul_assoc]

omit [DecidableEq ι] in
/-- Proposition 3(1) of COD-190 (`cod-190-delta-proof-attempt.md`). Under the hypotheses of
`condProb_le_mul_pow`, `f_t(T) ≤ b p` for every `T` and `t`. -/
theorem condProb_le_mul (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (T : Finset ι) (t : ι) : condProb P A T t ≤ b * p := by
  classical
  have hp0 : 0 ≤ p := (prob_nonneg hP _).trans (hp t)
  by_cases ht : t ∈ T
  · rw [condProb_of_mem ht]
    positivity
  exact (condProb_le_mul_pow hP hp hε hb hbp hstar hg T ht).trans
    (mul_pow_le_of_star hp0 hε hb hbp (card_le_univ T) hstar)

omit [DecidableEq ι] in
/-- Proposition 3(1) of COD-190 (`cod-190-delta-proof-attempt.md`), the bound on `q`. Under the
hypotheses of `condProb_le_mul_pow`, `q = U(Z_ι) ≥ ∏_{k < n} (1 - min(b p, p β^k))`, so in
particular `q ≥ (1 - b p)^n`. -/
theorem prod_le_prob_avoid (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t) :
    ∏ k ∈ range (Fintype.card ι),
        (1 - min (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ k)) ≤ prob P (avoid A univ) := by
  classical
  set σ := (Fintype.equivFin ι).symm
  rw [prob_avoid_univ hP σ, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_le_prod₀ (fun k _ ↦ ?_) fun k _ ↦ ?_
  · linarith [min_le_left (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ (k : ℕ))]
  · have h := condProb_le_mul_pow hP hp hε hb hbp hstar hg (pre σ k) (notMem_pre σ le_rfl)
    rw [card_pre σ k.isLt.le] at h
    linarith [le_min (condProb_le_mul hP hp hε hb hbp hstar hg (pre σ k) (σ k)) h]

omit [DecidableEq ι] in
/-- Proposition 3(1) of COD-190 (`cod-190-delta-proof-attempt.md`). Under the hypotheses of
`condProb_le_mul_pow`, `q ≥ (1 - b p)^n`. -/
theorem pow_le_prob_avoid (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t) :
    (1 - b * p) ^ Fintype.card ι ≤ prob P (avoid A univ) := by
  classical
  refine le_trans ?_ (prod_le_prob_avoid hP hp hε hb hbp hstar hg)
  rw [← card_range (Fintype.card ι), ← prod_const, card_range]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ by linarith) fun k _ ↦ by
    linarith [min_le_left (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ k)]

omit [DecidableEq ι] in
/-- Proposition 3(1) of COD-190 (`cod-190-delta-proof-attempt.md`), the log form. Under the
hypotheses of `condProb_le_mul_pow`, `-log q ≤ ∑_{k < n} -log(1 - min(b p, p β^k))`. -/
theorem neg_log_prob_avoid_le (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t) :
    -Real.log (prob P (avoid A univ)) ≤ ∑ k ∈ range (Fintype.card ι),
      -Real.log (1 - min (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ k)) := by
  classical
  have hpos : ∀ k ∈ range (Fintype.card ι),
      0 < 1 - min (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ k) := fun k _ ↦ by
    linarith [min_le_left (b * p) (p * (1 + ε * b * p / (1 - b * p)) ^ k)]
  rw [sum_neg_distrib, neg_le_neg_iff, ← Real.log_prod fun k hk ↦ (hpos k hk).ne']
  exact Real.log_le_log (prod_pos hpos) (prod_le_prob_avoid hP hp hε hb hbp hstar hg)

variable {ε' p' : ℝ}

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), the refined bound, for
`p' ≤ U(A_t) ≤ p`. Assume the hypotheses of `condProb_le_mul_pow`. If moreover `U(A_t) ≥ p'` for
all `t`, and `g_T(s, t) ≤ 1 + ε'` for every `T` and every pair `s ≠ t` outside `T`, with
`ε' ≥ 0` and `ε' b p < 1 - b p`, then `f_t(T) ≥ p' γ^|T|` for `t ∉ T`, with
`γ = 1 - ε' b p / (1 - b p)`. -/
theorem mul_pow_le_condProb_of_mem_Icc (hP : IsProb P) (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε')
    (T : Finset ι) {t : ι} (ht : t ∉ T) :
    p' * (1 - ε' * b * p / (1 - b * p)) ^ T.card ≤ condProb P A T t := by
  classical
  have hp' : ∀ t, prob P (A t) ≤ p := fun t ↦ (hp t).2
  have hc : 0 < 1 - b * p := by linarith
  have hγ : 0 ≤ 1 - ε' * b * p / (1 - b * p) := by
    rw [sub_nonneg, div_le_one hc]
    linarith
  induction T using Finset.induction_on generalizing t with
  | empty => simpa [condProb_empty hP] using (hp t).1
  | insert v T hv ih =>
    rw [mem_insert, not_or] at ht
    have hv' := condProb_le_mul hP hp' hε hb hbp hstar hg T v
    have h := condProb_insert_mul hP (A := A) T t v
    rw [condPair_comm] at h
    have h' := condPair_le_of_pairRatio_le hP (hg' T v t hv ht.2 (Ne.symm ht.1))
    have hstep := step_lower (condProb_nonneg hP T t) hv' hbp hε'
      (F := condProb P A (insert v T) t) (by linarith)
    calc p' * (1 - ε' * b * p / (1 - b * p)) ^ (insert v T).card =
          p' * (1 - ε' * b * p / (1 - b * p)) ^ T.card * (1 - ε' * b * p / (1 - b * p)) := by
          rw [card_insert_of_notMem hv, pow_succ]
          ring
      _ ≤ condProb P A T t * (1 - ε' * (b * p) / (1 - b * p)) := by
          rw [← mul_assoc ε' b p]
          exact mul_le_mul_of_nonneg_right (ih ht.2) hγ
      _ ≤ _ := hstep

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), the refined bound. Assume
the hypotheses of `condProb_le_mul_pow` with `U(A_t) = p` for all `t`. If moreover
`g_T(s, t) ≤ 1 + ε'` for every `T` and every pair `s ≠ t` outside `T`, with `ε' ≥ 0` and
`ε' b p < 1 - b p`, then `f_t(T) ≥ p γ^|T|` for `t ∉ T`, with `γ = 1 - ε' b p / (1 - b p)`.
`mul_pow_le_condProb_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem mul_pow_le_condProb (hP : IsProb P) (hp : ∀ t, prob P (A t) = p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε')
    (T : Finset ι) {t : ι} (ht : t ∉ T) :
    p * (1 - ε' * b * p / (1 - b * p)) ^ T.card ≤ condProb P A T t :=
  mul_pow_le_condProb_of_mem_Icc hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hε hb hbp hstar hg hε' hε'b
    hg' T ht

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), for `p' ≤ U(A_t) ≤ p`.
Under the hypotheses of `mul_pow_le_condProb_of_mem_Icc`, `f_t(T) ≥ α p'` for `t ∉ T`, with
`α = (1 - ε' b p / (1 - b p))^(n - 1)`. -/
theorem pow_mul_le_condProb_of_mem_Icc (hP : IsProb P) (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε')
    (T : Finset ι) {t : ι} (ht : t ∉ T) :
    (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) * p' ≤ condProb P A T t := by
  classical
  have hγ := one_sub_div_mem_Icc hε' (by linarith) ((prob_nonneg hP _).trans (hp t).2) hbp hε'b
  rcases lt_or_ge p' 0 with hp0 | hp0
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ.1 _) hp0.le).trans
      (condProb_nonneg hP T t)
  have hT := card_lt_univ_of_notMem ht
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγ.1 hγ.2 (by omega)) hp0).trans
    (mul_pow_le_condProb_of_mem_Icc hP hp hε hb hbp hstar hg hε' hε'b hg' T ht)

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`). Under the hypotheses of
`mul_pow_le_condProb`, `f_t(T) ≥ α p` for `t ∉ T`, with `α = (1 - ε' b p / (1 - b p))^(n - 1)`.
`pow_mul_le_condProb_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem pow_mul_le_condProb (hP : IsProb P) (hp : ∀ t, prob P (A t) = p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε')
    (T : Finset ι) {t : ι} (ht : t ∉ T) :
    (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) * p ≤ condProb P A T t :=
  pow_mul_le_condProb_of_mem_Icc hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hε hb hbp hstar hg hε' hε'b
    hg' T ht

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), for `p' ≤ U(A_t) ≤ p`.
Under the hypotheses of `mul_pow_le_condProb_of_mem_Icc`, `q ≤ (1 - α p')^n` with
`α = (1 - ε' b p / (1 - b p))^(n - 1)`. -/
theorem prob_avoid_le_pow_of_mem_Icc (hP : IsProb P) (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      (1 - (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) * p') ^ Fintype.card ι := by
  classical
  set σ := (Fintype.equivFin ι).symm
  rw [prob_avoid_univ hP σ]
  calc ∏ k : Fin (Fintype.card ι), (1 - condProb P A (pre σ k) (σ k)) ≤
        ∏ _k : Fin (Fintype.card ι),
          (1 - (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) * p') :=
        Finset.prod_le_prod₀ (fun k _ ↦ sub_nonneg.mpr (condProb_le_one hP _ _)) fun k _ ↦
          sub_le_sub_left (pow_mul_le_condProb_of_mem_Icc hP hp hε hb hbp hstar hg hε' hε'b hg' _
            (notMem_pre σ le_rfl)) 1
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`). Under the hypotheses of
`mul_pow_le_condProb`, `q ≤ (1 - α p)^n` with `α = (1 - ε' b p / (1 - b p))^(n - 1)`.
`prob_avoid_le_pow_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem prob_avoid_le_pow (hP : IsProb P) (hp : ∀ t, prob P (A t) = p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      (1 - (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) * p) ^ Fintype.card ι :=
  prob_avoid_le_pow_of_mem_Icc hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hε hb hbp hstar hg hε' hε'b hg'

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), the exponential form, for
`p' ≤ U(A_t) ≤ p`. Under the hypotheses of `mul_pow_le_condProb_of_mem_Icc`, `q ≤ e^(-α n p')`. -/
theorem prob_avoid_le_exp_of_mem_Icc (hP : IsProb P) (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      Real.exp (-((1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) *
        (Fintype.card ι * p'))) := by
  classical
  refine (prob_avoid_le_pow_of_mem_Icc hP hp hε hb hbp hstar hg hε' hε'b hg').trans ?_
  set α := (1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨t⟩⟩
  · simp
  have hp0 : 0 ≤ p := (prob_nonneg hP _).trans (hp t).2
  have hγ := one_sub_div_mem_Icc hε' (by linarith) hp0 hbp hε'b
  have hα0 : 0 ≤ α := pow_nonneg hγ.1 _
  have hα1 : α ≤ 1 := pow_le_one₀ hγ.1 hγ.2
  have hpp : p' ≤ p := (hp t).1.trans (hp t).2
  have hαp : α * p' ≤ 1 := by
    rcases le_or_gt 0 p' with hp'0 | hp'0
    · nlinarith
    · nlinarith
  calc (1 - α * p') ^ Fintype.card ι ≤ Real.exp (-(α * p')) ^ Fintype.card ι :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
    _ = _ := by
        rw [← Real.exp_nat_mul]
        ring_nf

omit [DecidableEq ι] in
/-- Proposition 3(2) of COD-190 (`cod-190-delta-proof-attempt.md`), the exponential form. Under
the hypotheses of `mul_pow_le_condProb`, `q ≤ e^(-α μ)` with `μ = n p`.
`prob_avoid_le_exp_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem prob_avoid_le_exp (hP : IsProb P) (hp : ∀ t, prob P (A t) = p) (hε : 0 ≤ ε)
    (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Fintype.card ι * ε * b * p / (1 - b * p) ≤ Real.log b)
    (hg : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → 1 - ε ≤ pairRatio P A T s t)
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ T s t, s ∉ T → t ∉ T → s ≠ t → pairRatio P A T s t ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      Real.exp (-((1 - ε' * b * p / (1 - b * p)) ^ (Fintype.card ι - 1) *
        (Fintype.card ι * p))) :=
  prob_avoid_le_exp_of_mem_Icc hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hε hb hbp hstar hg hε' hε'b hg'

end Prop3

section Prop4

variable {n : ℕ} (σ : Fin n ≃ ι) {p ε b : ℝ} {J : ℕ}

omit [DecidableEq ι] in
/-- Proposition 4(1) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`),
small prefixes dropped. Fix an ordering `σ` of `ι` (so `n = |ι|`), `J` with `J p < 1`,
`U(A_t) ≤ p` for all `t`, `ε ≥ 0`, `b > 1`, `b p < 1` and
`(★_J) exp(n ε b p / (1 - b p)) ≤ (1 - J p) b`. If `g_{T_j}(σ j, σ k) ≥ 1 - ε` whenever
`J ≤ j < k`, then `f_{σ k}(T_k) ≤ b p` for every `k`. Indices are `0`-based, so the paper's
`J < j < k` reads `J ≤ j < k` here. -/
theorem condProb_pre_le_mul (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p) (hJp : J * p < 1)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k))
    (k : Fin n) : condProb P A (pre σ k) (σ k) ≤ b * p := by
  classical
  have hp0 : 0 ≤ p := (prob_nonneg hP _).trans (hp (σ k))
  have hc : 0 < 1 - b * p := by linarith
  have hx : 0 ≤ ε * b * p / (1 - b * p) := div_nonneg (by positivity) hc.le
  have hJ1 : 1 ≤ (1 - J * p) * b :=
    (Real.one_le_exp (div_nonneg (by positivity) hc.le)).trans hstar
  have hbase : p / (1 - J * p) ≤ b * p := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  suffices h : ∀ k : ℕ, ∀ hk : k < n, condProb P A (pre σ k) (σ ⟨k, hk⟩) ≤ b * p from
    h k k.isLt
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  by_cases hkJ : k ≤ J
  · have hkJ' : (k : ℝ) ≤ J := by exact_mod_cast hkJ
    have h := condProb_le_div hP hp hp0 (T := pre σ k) (by rw [card_pre σ hk.le]; nlinarith)
      (σ ⟨k, hk⟩)
    rw [card_pre σ hk.le] at h
    exact h.trans ((div_le_div_of_nonneg_left hp0 (by linarith) (by nlinarith)).trans hbase)
  rw [not_le] at hkJ
  have hinner : ∀ d, J + d ≤ k → condProb P A (pre σ (J + d)) (σ ⟨k, hk⟩) ≤
      p / (1 - J * p) * (1 + ε * b * p / (1 - b * p)) ^ d := by
    intro d
    induction d with
    | zero =>
      intro _
      have h := condProb_le_div hP hp hp0 (T := pre σ J)
        (by rw [card_pre σ (by omega)]; exact hJp) (σ ⟨k, hk⟩)
      rw [card_pre σ (by omega)] at h
      simpa using h
    | succ d ihd =>
      intro hd
      have hjn : J + d < n := by omega
      have hj := ih (J + d) (by omega) hjn
      have h := condProb_insert_mul hP (A := A) (pre σ (J + d)) (σ ⟨k, hk⟩) (σ ⟨J + d, hjn⟩)
      rw [condPair_comm, ← pre_succ σ hjn] at h
      have h' : (1 - ε) * (condProb P A (pre σ (J + d)) (σ ⟨J + d, hjn⟩) *
          condProb P A (pre σ (J + d)) (σ ⟨k, hk⟩)) ≤
          condPair P A (pre σ (J + d)) (σ ⟨J + d, hjn⟩) (σ ⟨k, hk⟩) :=
        le_condPair_of_le_pairRatio hP
          (hg ⟨J + d, hjn⟩ ⟨k, hk⟩ (by simp) (Fin.mk_lt_mk.mpr (by omega)))
      have hstep := step_upper (condProb_nonneg hP _ _) hj hbp hε
        (F := condProb P A (pre σ (J + d + 1)) (σ ⟨k, hk⟩)) (by linarith)
      calc condProb P A (pre σ (J + (d + 1))) (σ ⟨k, hk⟩) ≤
            condProb P A (pre σ (J + d)) (σ ⟨k, hk⟩) * (1 + ε * (b * p) / (1 - b * p)) := hstep
        _ ≤ p / (1 - J * p) * (1 + ε * b * p / (1 - b * p)) ^ d *
              (1 + ε * b * p / (1 - b * p)) := by
            rw [← mul_assoc ε b p]
            exact mul_le_mul_of_nonneg_right (ihd (by omega)) (by linarith)
        _ = _ := by rw [pow_succ, mul_assoc]
  have h1 := hinner (k - J) (by omega)
  rw [show J + (k - J) = k by omega] at h1
  calc condProb P A (pre σ k) (σ ⟨k, hk⟩) ≤
        p / (1 - J * p) * (1 + ε * b * p / (1 - b * p)) ^ (k - J) := h1
    _ ≤ p / (1 - J * p) * Real.exp (n * (ε * b * p / (1 - b * p))) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le_exp hx (by omega))
          (div_nonneg hp0 (by linarith))
    _ ≤ p / (1 - J * p) * ((1 - J * p) * b) :=
        mul_le_mul_of_nonneg_left ((le_of_eq (by ring_nf)).trans hstar)
          (div_nonneg hp0 (by linarith))
    _ = b * p * ((1 - J * p) / (1 - J * p)) := by ring
    _ = b * p := by rw [div_self (by linarith : (0 : ℝ) < 1 - J * p).ne', mul_one]

omit [DecidableEq ι] in
/-- Proposition 4(1) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`).
Under the hypotheses of `condProb_pre_le_mul`, `q ≥ (1 - b p)^n`. -/
theorem pow_le_prob_avoid_of_pre [Fintype ι] (hP : IsProb P) (hp : ∀ t, prob P (A t) ≤ p)
    (hJp : J * p < 1) (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k)) :
    (1 - b * p) ^ n ≤ prob P (avoid A univ) := by
  classical
  rw [prob_avoid_univ hP σ]
  calc (1 - b * p) ^ n = ∏ _k : Fin n, (1 - b * p) := by
        rw [prod_const, card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ by linarith) fun k _ ↦
        sub_le_sub_left (condProb_pre_le_mul σ hP hp hJp hε hb hbp hstar hg k) 1

variable {R ε' p' : ℝ}

omit [DecidableEq ι] in
/-- Proposition 4(2) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`),
for `p' ≤ U(A_t) ≤ p`. Assume the hypotheses of `condProb_pre_le_mul`, `U(A_t) ≥ p'` for all `t`,
`R ≥ 0` with `U(A_x A_y) ≤ R p'²` for `x ≠ y`, and `g_{T_j}(σ j, σ k) ≤ 1 + ε'` whenever
`J ≤ j < k`, with `ε' ≥ 0` and `ε' b p < 1 - b p`. Then `f_{σ k}(T_k) ≥ α_J p'` for every `k`,
with `α_J = (1 - J p' R) (1 - ε' b p / (1 - b p))^(n - 1)`. -/
theorem mul_le_condProb_pre_of_mem_Icc (hP : IsProb P) (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p)
    (hR0 : 0 ≤ R) (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p' ^ 2) (hJp : J * p < 1)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k))
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → pairRatio P A (pre σ j) (σ j) (σ k) ≤ 1 + ε')
    (k : Fin n) :
    (1 - J * p' * R) * (1 - ε' * b * p / (1 - b * p)) ^ (n - 1) * p' ≤
      condProb P A (pre σ k) (σ k) := by
  classical
  have hp' : ∀ t, prob P (A t) ≤ p := fun t ↦ (hp t).2
  have hpl : ∀ t, p' ≤ prob P (A t) := fun t ↦ (hp t).1
  set γ := 1 - ε' * b * p / (1 - b * p) with hγ_def
  obtain ⟨hγ, hγ1⟩ := one_sub_div_mem_Icc hε' (by linarith) ((prob_nonneg hP _).trans (hp' (σ k)))
    hbp hε'b
  have hf0 := condProb_nonneg hP (A := A) (pre σ k) (σ k)
  rcases lt_or_ge p' 0 with hp0 | hp0
  · refine le_trans (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ?_ (pow_nonneg hγ _)) hp0.le) hf0
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) J) hR0]
  by_cases hc0 : 1 - J * p' * R < 0
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0.le
      (pow_nonneg hγ _)) hp0) hf0
  rw [not_lt] at hc0
  have hpR : 0 ≤ p' * R := mul_nonneg hp0 hR0
  by_cases hkJ : (k : ℕ) ≤ J
  · have hkJ' : ((k : ℕ) : ℝ) ≤ J := by exact_mod_cast hkJ
    have h := mul_le_condProb_of_le hP hpl hR (notMem_pre σ (k := k) le_rfl)
    rw [card_pre σ k.isLt.le] at h
    refine le_trans ?_ h
    have h1 : (1 - J * p' * R) * γ ^ (n - 1) ≤ 1 - J * p' * R :=
      mul_le_of_le_one_right hc0 (pow_le_one₀ hγ hγ1)
    have h2 := mul_le_mul_of_nonneg_right h1 hp0
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkJ' hpR) hp0
    linarith
  rw [not_le] at hkJ
  have hinner : ∀ d, J + d ≤ k →
      (1 - J * p' * R) * p' * γ ^ d ≤ condProb P A (pre σ (J + d)) (σ k) := by
    intro d
    induction d with
    | zero =>
      intro _
      have h := mul_le_condProb_of_le hP hpl hR (notMem_pre σ (k := J) (j := k) (by omega))
      rw [card_pre σ (by omega)] at h
      simpa [mul_comm] using h
    | succ d ihd =>
      intro hd
      have hjn : J + d < n := by omega
      have hj := condProb_pre_le_mul σ hP hp' hJp hε hb hbp hstar hg ⟨J + d, hjn⟩
      have h := condProb_insert_mul hP (A := A) (pre σ (J + d)) (σ k) (σ ⟨J + d, hjn⟩)
      rw [condPair_comm, ← pre_succ σ hjn] at h
      have h' : condPair P A (pre σ (J + d)) (σ ⟨J + d, hjn⟩) (σ k) ≤
          (1 + ε') * (condProb P A (pre σ (J + d)) (σ ⟨J + d, hjn⟩) *
            condProb P A (pre σ (J + d)) (σ k)) :=
        condPair_le_of_pairRatio_le hP
          (hg' ⟨J + d, hjn⟩ k (by simp) (Fin.mk_lt_mk.mpr (by omega) |>.trans_eq rfl))
      have hstep := step_lower (condProb_nonneg hP _ _) hj hbp hε'
        (F := condProb P A (pre σ (J + d + 1)) (σ k)) (by linarith)
      calc (1 - J * p' * R) * p' * γ ^ (d + 1) = (1 - J * p' * R) * p' * γ ^ d * γ := by
            rw [pow_succ]
            ring
        _ ≤ condProb P A (pre σ (J + d)) (σ k) * (1 - ε' * (b * p) / (1 - b * p)) := by
            rw [← mul_assoc ε' b p]
            exact mul_le_mul_of_nonneg_right (ihd (by omega)) hγ
        _ ≤ _ := hstep
  have h1 := hinner (k - J) (by omega)
  rw [show J + ((k : ℕ) - J) = k by omega] at h1
  refine le_trans ?_ h1
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγ hγ1 (by omega))
    (mul_nonneg hc0 hp0)

omit [DecidableEq ι] in
/-- Proposition 4(2) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`).
Assume the hypotheses of `condProb_pre_le_mul` with `U(A_t) = p` for all `t`, let `R ≥ 0` satisfy
`U(A_x A_y) ≤ R p²` for `x ≠ y` (the paper's `R̄`, or any upper bound for it), and suppose
`g_{T_j}(σ j, σ k) ≤ 1 + ε'` whenever `J ≤ j < k`, with `ε' ≥ 0` and `ε' b p < 1 - b p`. Then
`f_{σ k}(T_k) ≥ α_J p` for every `k`, with `α_J = (1 - J p R) (1 - ε' b p / (1 - b p))^(n - 1)`.
`mul_le_condProb_pre_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem mul_le_condProb_pre (hP : IsProb P) (hp : ∀ t, prob P (A t) = p) (hR0 : 0 ≤ R)
    (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p ^ 2) (hJp : J * p < 1)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k))
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → pairRatio P A (pre σ j) (σ j) (σ k) ≤ 1 + ε')
    (k : Fin n) :
    (1 - J * p * R) * (1 - ε' * b * p / (1 - b * p)) ^ (n - 1) * p ≤
      condProb P A (pre σ k) (σ k) :=
  mul_le_condProb_pre_of_mem_Icc σ hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hR0 hR hJp hε hb hbp hstar
    hg hε' hε'b hg' k

omit [DecidableEq ι] in
/-- Proposition 4(2) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`),
for `p' ≤ U(A_t) ≤ p`. Under the hypotheses of `mul_le_condProb_pre_of_mem_Icc`,
`q ≤ (1 - α_J p')^n`. -/
theorem prob_avoid_le_pow_of_pre_of_mem_Icc [Fintype ι] (hP : IsProb P)
    (hp : ∀ t, prob P (A t) ∈ Set.Icc p' p) (hR0 : 0 ≤ R)
    (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p' ^ 2) (hJp : J * p < 1)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k))
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → pairRatio P A (pre σ j) (σ j) (σ k) ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      (1 - (1 - J * p' * R) * (1 - ε' * b * p / (1 - b * p)) ^ (n - 1) * p') ^ n := by
  classical
  rw [prob_avoid_univ hP σ]
  calc ∏ k : Fin n, (1 - condProb P A (pre σ k) (σ k)) ≤
        ∏ _k : Fin n, (1 - (1 - J * p' * R) * (1 - ε' * b * p / (1 - b * p)) ^ (n - 1) * p') :=
        Finset.prod_le_prod₀ (fun k _ ↦ sub_nonneg.mpr (condProb_le_one hP _ _)) fun k _ ↦
          sub_le_sub_left (mul_le_condProb_pre_of_mem_Icc σ hP hp hR0 hR hJp hε hb hbp hstar hg
            hε' hε'b hg' k) 1
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]

omit [DecidableEq ι] in
/-- Proposition 4(2) of the conditional pair bound attempt (`conditional-pair-bound-attempt.md`).
Under the hypotheses of `mul_le_condProb_pre`, `q ≤ (1 - α_J p)^n`.
`prob_avoid_le_pow_of_pre_of_mem_Icc` needs only `p' ≤ U(A_t) ≤ p`. -/
theorem prob_avoid_le_pow_of_pre [Fintype ι] (hP : IsProb P) (hp : ∀ t, prob P (A t) = p)
    (hR0 : 0 ≤ R) (hR : ∀ x y, x ≠ y → prob P (A x ∩ A y) ≤ R * p ^ 2) (hJp : J * p < 1)
    (hε : 0 ≤ ε) (hb : 1 < b) (hbp : b * p < 1)
    (hstar : Real.exp (n * ε * b * p / (1 - b * p)) ≤ (1 - J * p) * b)
    (hg : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → 1 - ε ≤ pairRatio P A (pre σ j) (σ j) (σ k))
    (hε' : 0 ≤ ε') (hε'b : ε' * b * p < 1 - b * p)
    (hg' : ∀ j k : Fin n, J ≤ (j : ℕ) → j < k → pairRatio P A (pre σ j) (σ j) (σ k) ≤ 1 + ε') :
    prob P (avoid A univ) ≤
      (1 - (1 - J * p * R) * (1 - ε' * b * p / (1 - b * p)) ^ (n - 1) * p) ^ n :=
  prob_avoid_le_pow_of_pre_of_mem_Icc σ hP (fun t ↦ ⟨(hp t).ge, (hp t).le⟩) hR0 hR hJp hε hb hbp
    hstar hg hε' hε'b hg'

end Prop4


section Averaged

variable [Fintype ι]

/-- `M_T = ∑_{t ∉ T} f_t(T) = E[X | Z_T]`. -/
noncomputable def condMean (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  ∑ t ∈ Tᶜ, condProb P A T t

/-- `R_T(s) = ∑_{t ∉ T ∪ s} Cov_T(s, t)`. -/
noncomputable def covSum (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s : ι) : ℝ :=
  ∑ t ∈ (insert s T)ᶜ, condCov P A T s t

/-- `Δ_T = (1 / N_T) ∑_{s ∉ T} R_T(s) / (1 - f_s(T))`, with `N_T = |ι ∖ T|`. -/
noncomputable def drift (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  (∑ s ∈ Tᶜ, covSum P A T s / (1 - condProb P A T s)) / Tᶜ.card

/-- `E_{|T| = i} F(T)`, the average of `F` over the `i`-subsets of `ι`. -/
noncomputable def levelAvg (F : Finset ι → ℝ) (i : ℕ) : ℝ :=
  (∑ T ∈ powersetCard i univ, F T) / (Fintype.card ι).choose i

/-- `(1 / N_T) ∑_{s ∉ T} G(T, s)`, the average of `G(T, ·)` outside `T`. -/
noncomputable def outAvg (G : Finset ι → ι → ℝ) (T : Finset ι) : ℝ :=
  (∑ s ∈ Tᶜ, G T s) / Tᶜ.card

/-- `E_π ∑_k G(T_k, π_k)` for a uniformly random ordering `π` of `ι`, written level by level:
`T_k` is a uniform `k`-subset and `π_k` is uniform outside it. `chainAvg_eq_sum_equiv` shows that
this is the average of `∑_k G(T_k, π_k)` over all orderings `π : Fin n ≃ ι`. -/
noncomputable def chainAvg (G : Finset ι → ι → ℝ) : ℝ :=
  ∑ i ∈ range (Fintype.card ι), levelAvg (outAvg G) i

/-- `N_T = n - i` for `|T| = i`. -/
theorem card_compl_of_mem_powersetCard {T : Finset ι} {i : ℕ} (hT : T ∈ powersetCard i univ) :
    (Tᶜ.card : ℝ) = Fintype.card ι - i := by
  have h := (mem_powersetCard.mp hT).2
  have hi : i ≤ Fintype.card ι := h ▸ card_le_univ T
  rw [card_compl, h, Nat.cast_sub hi]

/-- `M_T ≥ 0`. -/
theorem condMean_nonneg (hP : IsProb P) (T : Finset ι) : 0 ≤ condMean P A T :=
  sum_nonneg fun t _ ↦ condProb_nonneg hP T t

omit [DecidableEq ι] in
/-- `C(n, i) > 0` for `i ≤ n`. -/
theorem choose_pos_real {i : ℕ} (hi : i ≤ Fintype.card ι) :
    (0 : ℝ) < (Fintype.card ι).choose i := by
  exact_mod_cast Nat.choose_pos hi

omit [DecidableEq ι] in
/-- `E_{|T| = i}` only sees `i`-sets. -/
theorem levelAvg_congr {F G : Finset ι → ℝ} {i : ℕ} (h : ∀ T, T.card = i → F T = G T) :
    levelAvg F i = levelAvg G i := by
  rw [levelAvg, levelAvg, sum_congr rfl fun T hT ↦ h T (mem_powersetCard.mp hT).2]

omit [DecidableEq ι] in
/-- `E_{|T| = i}` is monotone. -/
theorem levelAvg_mono {F G : Finset ι → ℝ} {i : ℕ} (h : ∀ T, T.card = i → F T ≤ G T) :
    levelAvg F i ≤ levelAvg G i :=
  div_le_div_of_nonneg_right (sum_le_sum fun T hT ↦ h T (mem_powersetCard.mp hT).2)
    (Nat.cast_nonneg _)

omit [DecidableEq ι] in
/-- `E_{|T| = i} (a F + b) = a E_{|T| = i} F + b` for `i ≤ n`. -/
theorem levelAvg_affine (F : Finset ι → ℝ) (a b : ℝ) {i : ℕ} (hi : i ≤ Fintype.card ι) :
    levelAvg (fun T ↦ a * F T + b) i = a * levelAvg F i + b := by
  have hc := (choose_pos_real hi).ne'
  rw [levelAvg, levelAvg, sum_add_distrib, ← mul_sum, sum_const, card_powersetCard, card_univ,
    nsmul_eq_mul]
  field_simp

omit [DecidableEq ι] in
/-- `|E_{|T| = i} F| ≤ E_{|T| = i} |F|`. -/
theorem abs_levelAvg_le (F : Finset ι → ℝ) (i : ℕ) :
    |levelAvg F i| ≤ levelAvg (fun T ↦ |F T|) i := by
  rw [levelAvg, levelAvg, abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- Double counting of the pairs `(T, s)` with `|T| = i` and `s ∉ T` against the pairs
`(T', s)` with `|T'| = i + 1` and `s ∈ T'`. -/
theorem sum_powersetCard_sum_compl (G : Finset ι → ι → ℝ) (i : ℕ) :
    ∑ T ∈ powersetCard i univ, ∑ s ∈ Tᶜ, G (insert s T) s =
      ∑ T ∈ powersetCard (i + 1) univ, ∑ s ∈ T, G T s := by
  rw [← sum_finset_product' ((powersetCard i univ ×ˢ univ).filter fun x ↦ x.2 ∉ x.1) _ _
      (fun x ↦ by simp) (f := fun T s ↦ G (insert s T) s),
    ← sum_finset_product' ((powersetCard (i + 1) univ ×ˢ univ).filter fun x ↦ x.2 ∈ x.1) _ _
      (fun x ↦ by simp) (f := fun T s ↦ G T s)]
  refine sum_nbij' (fun x ↦ (insert x.2 x.1, x.2)) (fun x ↦ (x.1.erase x.2, x.2)) ?_ ?_ ?_ ?_
    fun _ _ ↦ rfl
  · intro x hx
    simp only [mem_filter, mem_product, mem_powersetCard, subset_univ, true_and, mem_univ,
      and_true] at hx ⊢
    exact ⟨by rw [card_insert_of_notMem hx.2, hx.1], mem_insert_self _ _⟩
  · intro x hx
    simp only [mem_filter, mem_product, mem_powersetCard, subset_univ, true_and, mem_univ,
      and_true] at hx ⊢
    exact ⟨by rw [card_erase_of_mem hx.2, hx.1, Nat.add_sub_cancel], notMem_erase _ _⟩
  · intro x hx
    simp only [mem_filter, mem_product, mem_univ, and_true] at hx
    simp [erase_insert hx.2]
  · intro x hx
    simp only [mem_filter, mem_product, mem_univ, and_true] at hx
    simp [insert_erase hx.2]

/-- `E_{i+1} F - E_i F = E_{|T| = i} (1 / N_T) ∑_{s ∉ T} (F(T ∪ s) - F(T))`: a uniform `i`-set with
a uniform point outside it added is a uniform `(i + 1)`-set. -/
theorem levelAvg_succ_sub (F : Finset ι → ℝ) {i : ℕ} (hi : i < Fintype.card ι) :
    levelAvg F (i + 1) - levelAvg F i =
      levelAvg (fun T ↦ (∑ s ∈ Tᶜ, (F (insert s T) - F T)) / Tᶜ.card) i := by
  have hni : (0 : ℝ) < Fintype.card ι - i := by
    have : (i : ℝ) < Fintype.card ι := by exact_mod_cast hi
    linarith
  have hc := choose_pos_real hi.le
  have hc' := choose_pos_real (Nat.succ_le_of_lt hi)
  have hcc : (((Fintype.card ι).choose (i + 1) : ℕ) : ℝ) * (i + 1) =
      ((Fintype.card ι).choose i : ℕ) * (Fintype.card ι - i) := by
    have := Nat.choose_succ_right_eq (Fintype.card ι) i
    rw [← Nat.cast_sub hi.le]
    exact_mod_cast this
  have h1 : ∑ T ∈ powersetCard i univ, (∑ s ∈ Tᶜ, (F (insert s T) - F T)) / Tᶜ.card =
      (∑ T ∈ powersetCard i univ, ∑ s ∈ Tᶜ, F (insert s T)) / (Fintype.card ι - i) -
        ∑ T ∈ powersetCard i univ, F T := by
    rw [sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun T hT ↦ ?_
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_compl_of_mem_powersetCard hT]
    field_simp
  have h2 : ∑ T ∈ powersetCard i univ, ∑ s ∈ Tᶜ, F (insert s T) =
      (i + 1) * ∑ T ∈ powersetCard (i + 1) univ, F T := by
    rw [sum_powersetCard_sum_compl (fun T _ ↦ F T), mul_sum]
    refine sum_congr rfl fun T hT ↦ ?_
    rw [sum_const, nsmul_eq_mul, (mem_powersetCard.mp hT).2]
    push_cast
    ring
  have h3 : (i + 1) / ((Fintype.card ι - i) * ((Fintype.card ι).choose i : ℕ)) =
      (1 : ℝ) / ((Fintype.card ι).choose (i + 1) : ℕ) := by
    rw [div_eq_div_iff (mul_pos hni hc).ne' hc'.ne']
    linarith
  rw [levelAvg, levelAvg, levelAvg, h1, h2, sub_div, div_div, mul_comm (i + 1 : ℝ),
    mul_div_assoc, h3]
  ring

omit [DecidableEq ι] in
/-- `E_{|T| = 0} F = F(∅)`. -/
theorem levelAvg_zero (F : Finset ι → ℝ) : levelAvg F 0 = F ∅ := by
  simp [levelAvg]

omit [DecidableEq ι] in
/-- `E_{|T| = n} F = F(ι)`. -/
theorem levelAvg_card (F : Finset ι → ℝ) : levelAvg F (Fintype.card ι) = F univ := by
  rw [levelAvg, ← card_univ, powersetCard_self, sum_singleton, Nat.choose_self, Nat.cast_one,
    div_one]

omit [DecidableEq ι] in
/-- If `q > 0`, then `f_s(T) < 1` for all `T` and `s`. -/
theorem condProb_lt_one (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) (T : Finset ι)
    (s : ι) : condProb P A T s < 1 := by
  classical
  have h := prob_avoid_insert hP (A := A) T s
  have h1 : 0 < prob P (avoid A (insert s T)) :=
    hq.trans_le (prob_mono hP (avoid_anti (subset_univ _)))
  rw [h] at h1
  have h2 := pos_of_mul_pos_right h1 (prob_nonneg hP _)
  linarith

omit [Fintype ι] in
/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the additive form of Lemma 2 of
COD-190: if `f_s(T) ≠ 1`, then `f_t(T ∪ s) - f_t(T) = -Cov_T(s, t) / (1 - f_s(T))`. -/
theorem condProb_insert_sub (hP : IsProb P) (T : Finset ι) (s t : ι)
    (hs : condProb P A T s ≠ 1) :
    condProb P A (insert s T) t - condProb P A T t =
      -condCov P A T s t / (1 - condProb P A T s) := by
  have h := condProb_insert_mul hP (A := A) T t s
  have hs' : 1 - condProb P A T s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [eq_div_iff hs', sub_mul, h, condCov, condPair_comm]
  ring

/-- Proposition 6 of COD-196, proof: `M_{T ∪ s} = M_T - f_s(T) - R_T(s) / (1 - f_s(T))` for
`s ∉ T` with `f_s(T) ≠ 1`. -/
theorem condMean_insert (hP : IsProb P) {T : Finset ι} {s : ι} (hsT : s ∉ T)
    (hs : condProb P A T s ≠ 1) :
    condMean P A (insert s T) =
      condMean P A T - condProb P A T s - covSum P A T s / (1 - condProb P A T s) := by
  have hcomp : (insert s T)ᶜ = Tᶜ.erase s := compl_insert
  have h1 : condMean P A (insert s T) = ∑ t ∈ (insert s T)ᶜ,
      (condProb P A T t - condCov P A T s t / (1 - condProb P A T s)) :=
    sum_congr rfl fun t _ ↦ by
      have h := condProb_insert_sub hP T s t hs
      rw [neg_div] at h
      linarith
  rw [h1, sum_sub_distrib, ← sum_div, ← covSum, condMean, hcomp,
    ← add_sum_erase _ _ (mem_compl.mpr hsT)]
  ring

/-- `m̄_i = E_{|T| = i} f̄_T`, with `f̄_T = M_T / N_T`. -/
theorem outAvg_condProb (T : Finset ι) :
    outAvg (condProb P A) T = condMean P A T / Tᶜ.card :=
  rfl

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the level recursion: if `q > 0`
and `i + 1 < n`, then `m̄_{i+1} = m̄_i - E_{|T| = i} Δ_T / (n - i - 1)`, where
`m̄_i = E_{|T| = i} f̄_T`. -/
theorem levelAvg_outAvg_succ (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {i : ℕ}
    (hi : i + 1 < Fintype.card ι) :
    levelAvg (outAvg (condProb P A)) (i + 1) =
      levelAvg (outAvg (condProb P A)) i - levelAvg (drift P A) i / (Fintype.card ι - i - 1) := by
  have hni : (1 : ℝ) < Fintype.card ι - i := by
    have : ((i + 1 : ℕ) : ℝ) < Fintype.card ι := by exact_mod_cast hi
    push_cast at this
    linarith
  have h := levelAvg_succ_sub (outAvg (condProb P A)) (i := i) (by omega)
  have key : levelAvg (fun T ↦ (∑ s ∈ Tᶜ, (outAvg (condProb P A) (insert s T) -
      outAvg (condProb P A) T)) / Tᶜ.card) i =
      (-1 / (Fintype.card ι - i - 1)) * levelAvg (drift P A) i + 0 := by
    rw [← levelAvg_affine _ _ _ (by omega)]
    refine levelAvg_congr fun T hT ↦ ?_
    have hN : (Tᶜ.card : ℝ) = Fintype.card ι - i :=
      card_compl_of_mem_powersetCard (mem_powersetCard.mpr ⟨subset_univ T, hT⟩)
    have hsum : ∑ s ∈ Tᶜ, (outAvg (condProb P A) (insert s T) - outAvg (condProb P A) T) =
        ∑ s ∈ Tᶜ, ((condMean P A T - condProb P A T s -
          covSum P A T s / (1 - condProb P A T s)) / (Fintype.card ι - i - 1) -
            condMean P A T / (Fintype.card ι - i)) := by
      refine sum_congr rfl fun s hs ↦ ?_
      have hsT := mem_compl.mp hs
      have hN' : ((insert s T)ᶜ.card : ℝ) = Fintype.card ι - i - 1 := by
        rw [card_compl, card_insert_of_notMem hsT, hT, Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [outAvg_condProb, outAvg_condProb, hN', hN,
        condMean_insert hP hsT (condProb_lt_one hP hq T s).ne]
    rw [hsum, hN, drift, hN, sum_sub_distrib, ← sum_div, sum_sub_distrib, sum_sub_distrib,
      sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, hN,
      show ∑ s ∈ Tᶜ, condProb P A T s = condMean P A T from rfl]
    have h1 : (Fintype.card ι : ℝ) - i - 1 ≠ 0 := by linarith
    have h2 : (Fintype.card ι : ℝ) - i ≠ 0 := by linarith
    field_simp
    ring
  have e : levelAvg (drift P A) i / (Fintype.card ι - i - 1) =
      -((-1 / (Fintype.card ι - i - 1)) * levelAvg (drift P A) i) := by ring
  linarith

/-- If `(n - i - 1) (a_{i+1} - a_i) = -d_i` for `i + 1 < n`, then
`∑_{i < n} a_i = n a_0 - ∑_{i < n - 1} d_i`. -/
theorem sum_range_of_rec {n : ℕ} (a d : ℕ → ℝ)
    (h : ∀ i, i + 1 < n → a (i + 1) = a i - d i / (n - i - 1)) :
    ∑ i ∈ range n, a i = n * a 0 - ∑ i ∈ range (n - 1), d i := by
  have key : ∀ k, k + 1 ≤ n →
      ∑ i ∈ range k, a i + (n - k) * a k = n * a 0 - ∑ i ∈ range k, d i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hnk : (n : ℝ) - k - 1 ≠ 0 := by
        have : ((k + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
        push_cast at this
        linarith
      have e : ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * a (k + 1) = (n - k - 1) * a k - d k := by
        rw [h k (by omega)]
        push_cast
        field_simp
        ring
      rw [sum_range_succ, sum_range_succ, e]
      linarith [ih (by omega)]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  have h := key (n - 1) (by omega)
  rw [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel, one_mul, ← sum_range_succ,
    Nat.sub_add_cancel hn] at h
  exact h

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the averaged chain identity: if
`q > 0`, then `E_π ∑_k f_k = ∑_{i < n} m̄_i = μ - ∑_{i ≤ n - 2} E_{|T| = i} Δ_T`, with
`μ = ∑_t U(A_t)`. -/
theorem chainAvg_condProb (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    chainAvg (condProb P A) =
      ∑ t, prob P (A t) - ∑ i ∈ range (Fintype.card ι - 1), levelAvg (drift P A) i := by
  rw [chainAvg, sum_range_of_rec _ _ fun i hi ↦ levelAvg_outAvg_succ hP hq hi, levelAvg_zero,
    outAvg_condProb, condMean, compl_empty, card_univ]
  congr 1
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  · rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
    exact sum_congr rfl fun t _ ↦ condProb_empty hP t

/-- `-log U(Z_{T ∪ s}) + log U(Z_T) = -log(1 - f_s(T))` when `q > 0`. -/
theorem neg_log_avoid_insert (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) (T : Finset ι)
    (s : ι) :
    -Real.log (prob P (avoid A (insert s T))) - -Real.log (prob P (avoid A T)) =
      -Real.log (1 - condProb P A T s) := by
  have h1 : 0 < prob P (avoid A T) := hq.trans_le (prob_mono hP (avoid_anti (subset_univ _)))
  have h2 : 0 < 1 - condProb P A T s := sub_pos.mpr (condProb_lt_one hP hq T s)
  rw [prob_avoid_insert hP, Real.log_mul h1.ne' h2.ne']
  ring

/-- `-log q = ∑_{i < n} E_{|T| = i} (1 / N_T) ∑_{s ∉ T} -log(1 - f_s(T))`, the averaged form of
the chain rule. -/
theorem neg_log_prob_avoid_eq_chainAvg (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    -Real.log (prob P (avoid A univ)) =
      chainAvg (fun T s ↦ -Real.log (1 - condProb P A T s)) := by
  set L : Finset ι → ℝ := fun T ↦ -Real.log (prob P (avoid A T))
  have h := sum_range_sub (fun i ↦ levelAvg L i) (Fintype.card ι)
  simp only [levelAvg_card, levelAvg_zero, L, avoid_empty, prob_univ hP, Real.log_one,
    neg_zero, sub_zero] at h
  rw [← h, chainAvg]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [levelAvg_succ_sub _ (mem_range.mp hi)]
  exact levelAvg_congr fun T _ ↦ by
    rw [outAvg]
    congr 1
    exact sum_congr rfl fun s _ ↦ neg_log_avoid_insert hP hq T s

/-- `E_π ∑_k G(T_k, π_k)` is monotone in `G` on the pairs `s ∉ T`. -/
theorem chainAvg_mono {G H : Finset ι → ι → ℝ} (h : ∀ T s, s ∉ T → G T s ≤ H T s) :
    chainAvg G ≤ chainAvg H :=
  sum_le_sum fun _ _ ↦ levelAvg_mono fun T _ ↦ div_le_div_of_nonneg_right
    (sum_le_sum fun s hs ↦ h T s (mem_compl.mp hs)) (Nat.cast_nonneg _)

/-- `E_π ∑_k G(T_k, π_k) c = c E_π ∑_k G(T_k, π_k)`. -/
theorem chainAvg_mul_const (G : Finset ι → ι → ℝ) (c : ℝ) :
    chainAvg (fun T s ↦ G T s * c) = chainAvg G * c := by
  simp only [chainAvg, levelAvg, outAvg, ← sum_mul, mul_div_right_comm _ c]

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the sandwich: if `q > 0`, then
`E_π ∑_k f_k ≤ -log q ≤ E_π ∑_k f_k / (1 - f_k)`. -/
theorem chainAvg_le_neg_log (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    chainAvg (condProb P A) ≤ -Real.log (prob P (avoid A univ)) := by
  rw [neg_log_prob_avoid_eq_chainAvg hP hq]
  refine chainAvg_mono fun T s _ ↦ ?_
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr (condProb_lt_one hP hq T s))
  linarith

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the sandwich: if `q > 0`, then
`-log q ≤ E_π ∑_k f_k / (1 - f_k)`. -/
theorem neg_log_le_chainAvg (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    -Real.log (prob P (avoid A univ)) ≤
      chainAvg (fun T s ↦ condProb P A T s / (1 - condProb P A T s)) := by
  rw [neg_log_prob_avoid_eq_chainAvg hP hq]
  refine chainAvg_mono fun T s _ ↦ ?_
  have h1 := sub_pos.mpr (condProb_lt_one hP hq T s)
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  rw [show condProb P A T s / (1 - condProb P A T s) = (1 - condProb P A T s)⁻¹ - 1 by
    field_simp
    ring]
  exact h

end Averaged

section Theorem7

/-- `∑_{i < n - 1} g(n - i) = ∑_{j < n - 1} g(j + 2)`. -/
theorem sum_range_reflect_two (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n - 1), g (n - i) = ∑ j ∈ range (n - 1), g (j + 2) := by
  rw [← sum_range_reflect (fun j ↦ g (j + 2))]
  exact sum_congr rfl fun j hj ↦ congrArg g (by have := mem_range.mp hj; omega)

/-- `∑_{j < m} 1 / (j + 2) ≤ log(m + 1)`. -/
theorem sum_inv_add_two_le_log (m : ℕ) :
    ∑ j ∈ range m, 1 / ((j : ℝ) + 2) ≤ Real.log (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := Real.one_sub_inv_le_log_of_pos (x := ((m : ℝ) + 2) / (m + 1)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h
    have e : 1 - ((m : ℝ) + 1) / (m + 2) = 1 / (m + 2) := by
      field_simp
      ring
    push_cast
    rw [show (m : ℝ) + 1 + 1 = m + 2 by ring]
    linarith

/-- `∑_{j < K} (j + 1) = K (K + 1) / 2`. -/
theorem sum_range_add_one (K : ℕ) : ∑ j ∈ range K, ((j : ℝ) + 1) = K * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The level corrections of Theorem 7 of COD-196 sum to at most `4 J log n + K (K + 1) φ / 2`. -/
theorem sum_corr_le (n K : ℕ) {J φ : ℝ} (hJ : 0 ≤ J) (hφ : 0 ≤ φ) :
    ∑ i ∈ range (n - 1), (4 * J / ((n - i : ℕ) : ℝ) +
      if n - i ≤ K + 1 then (((n - i : ℕ) : ℝ) - 1) * φ else 0) ≤
        4 * J * Real.log n + K * (K + 1) * φ / 2 := by
  rw [sum_range_reflect_two (fun N ↦ 4 * J / (N : ℝ) + if N ≤ K + 1 then ((N : ℝ) - 1) * φ else 0),
    sum_add_distrib]
  refine add_le_add ?_ ?_
  · have h : ∑ j ∈ range (n - 1), 4 * J / ((j + 2 : ℕ) : ℝ) =
        4 * J * ∑ j ∈ range (n - 1), 1 / ((j : ℝ) + 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      push_cast
      ring
    rw [h]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have := sum_inv_add_two_le_log (n - 1)
      rwa [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at this
  · have h : ∑ j ∈ range (n - 1), (if j + 2 ≤ K + 1 then (((j + 2 : ℕ) : ℝ) - 1) * φ else 0) =
        (∑ j ∈ (range (n - 1)).filter (fun j ↦ j < K), ((j : ℝ) + 1)) * φ := by
      rw [sum_mul, sum_filter]
      refine sum_congr rfl fun j _ ↦ ?_
      split_ifs with h1 h2 h2
      · push_cast
        ring
      · omega
      · omega
      · rfl
    have h2 : ∑ j ∈ (range (n - 1)).filter (fun j ↦ j < K), ((j : ℝ) + 1) ≤
        ∑ j ∈ range K, ((j : ℝ) + 1) :=
      sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ by simp only [mem_filter, mem_range] at hj ⊢; omega) fun _ _ _ ↦ by positivity
    rw [sum_range_add_one] at h2
    rw [h]
    calc (∑ j ∈ (range (n - 1)).filter (fun j ↦ j < K), ((j : ℝ) + 1)) * φ ≤
          K * (K + 1) / 2 * φ := mul_le_mul_of_nonneg_right h2 hφ
      _ = K * (K + 1) * φ / 2 := by ring

variable [Fintype ι]

omit [DecidableEq ι] in
/-- `E_{|T| = i} F ≥ 0` for `F ≥ 0`. -/
theorem levelAvg_nonneg {F : Finset ι → ℝ} (h : ∀ T, 0 ≤ F T) (i : ℕ) : 0 ≤ levelAvg F i :=
  div_nonneg (sum_nonneg fun T _ ↦ h T) (Nat.cast_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
/-- Under hypothesis (A) of Theorem 7 of COD-196, `|Cov_T(s, t)| ≤ φ` for `s ∉ T`. -/
theorem abs_condCov_le (hP : IsProb P) {φ : ℝ} (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    {T : Finset ι} {s t : ι} (hs : s ∉ T) : |condCov P A T s t| ≤ φ := by
  have h1 := condPair_le_left hP (A := A) T s t
  have h2 := condPair_nonneg hP (A := A) T s t
  have h3 := hA T s hs
  have h4 := condProb_nonneg hP (A := A) T s
  have h5 := condProb_nonneg hP (A := A) T t
  have h6 := condProb_le_one hP (A := A) T t
  rw [condCov, abs_sub_le_iff]
  constructor <;> nlinarith

omit [DecidableEq ι] in
/-- Under hypothesis (A) of Theorem 7 of COD-196, `q ≥ (1 - φ)^n > 0`. -/
theorem prob_avoid_pos (hP : IsProb P) {φ : ℝ} (hφ1 : φ < 1)
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ) : 0 < prob P (avoid A univ) := by
  classical
  rw [prob_avoid_univ hP (Fintype.equivFin ι).symm]
  exact prod_pos fun k _ ↦ by linarith [hA _ _ (notMem_pre (Fintype.equivFin ι).symm (k := k)
    le_rfl)]

/-- The core estimate of Theorem 7 of COD-196 (`cod-196-averaged-pinning.md`) under hypothesis
(B′). Assume (A) `f_t(T) ≤ φ < 1` for every `T` and `t ∉ T`, and (B′)
`∑_{s ≠ t ∉ T} |Cov_T(s, t)| ≤ 2 √J M_T + 4 J` for every `T` with `N_T ≥ K + 2`, the bound that
the paper derives from (B) through Lemma 3. Then, with `S = E_π ∑_k f_k`, `μ = ∑_t U(A_t)`,
`θ = 2 √J / (1 - φ)` and `η = (4 J log n + K (K + 1) φ / 2) / (1 - φ)`, `|S - μ| ≤ θ S + η`. -/
theorem abs_chainAvg_sub_le (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    |chainAvg (condProb P A) - ∑ t, prob P (A t)| ≤
      2 * √J / (1 - φ) * chainAvg (condProb P A) +
        (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ) := by
  have hq := prob_avoid_pos hP hφ1 hA
  have h1φ : 0 < 1 - φ := by linarith
  have hθ : 0 ≤ 2 * √J / (1 - φ) := div_nonneg (by positivity) h1φ.le
  have hid := chainAvg_condProb hP hq
  have hT : ∀ i, i + 1 < Fintype.card ι → ∀ T : Finset ι, T.card = i →
      |drift P A T| ≤ 2 * √J / (1 - φ) * outAvg (condProb P A) T +
        (4 * J / ((Fintype.card ι - i : ℕ) : ℝ) + if Fintype.card ι - i ≤ K + 1 then
          (((Fintype.card ι - i : ℕ) : ℝ) - 1) * φ else 0) / (1 - φ) := by
    intro i hi T hTc
    have hN : Tᶜ.card = Fintype.card ι - i := by rw [card_compl, hTc]
    have hNpos : (0 : ℝ) < Tᶜ.card := by exact_mod_cast (by omega : 0 < Tᶜ.card)
    have hs : ∀ s ∈ Tᶜ, |covSum P A T s / (1 - condProb P A T s)| ≤
        (∑ t ∈ Tᶜ.erase s, |condCov P A T s t|) / (1 - φ) := fun s hs ↦ by
      have hfs := hA T s (mem_compl.mp hs)
      have hfs1 : 0 < 1 - condProb P A T s := by linarith
      rw [abs_div, abs_of_pos hfs1, covSum, compl_insert]
      exact div_le_div₀ (sum_nonneg fun _ _ ↦ abs_nonneg _) (abs_sum_le_sum_abs _ _) h1φ
        (by linarith)
    have hdrift : |drift P A T| ≤
        (∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t|) / ((1 - φ) * Tᶜ.card) :=
      calc |drift P A T| =
            |∑ s ∈ Tᶜ, covSum P A T s / (1 - condProb P A T s)| / Tᶜ.card := by
            rw [drift, abs_div, Nat.abs_cast]
        _ ≤ (∑ s ∈ Tᶜ, (∑ t ∈ Tᶜ.erase s, |condCov P A T s t|) / (1 - φ)) / Tᶜ.card :=
            div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hs))
              hNpos.le
        _ = _ := by rw [← sum_div, div_div]
    have hM : 0 ≤ outAvg (condProb P A) T :=
      div_nonneg (condMean_nonneg hP T) (Nat.cast_nonneg _)
    rw [← hN]
    by_cases hK : K + 2 ≤ Tᶜ.card
    · have hite : 0 ≤ if Tᶜ.card ≤ K + 1 then ((Tᶜ.card : ℝ) - 1) * φ else 0 := by
        split_ifs
        · omega
        · exact le_rfl
      refine hdrift.trans ?_
      rw [div_le_iff₀ (mul_pos h1φ hNpos)]
      have hB' := hB T hK
      have e : 2 * √J / (1 - φ) * outAvg (condProb P A) T * ((1 - φ) * Tᶜ.card) =
          2 * √J * condMean P A T := by
        rw [outAvg_condProb]
        field_simp
      have e2 : (4 * J / Tᶜ.card + if Tᶜ.card ≤ K + 1 then ((Tᶜ.card : ℝ) - 1) * φ else 0) /
          (1 - φ) * ((1 - φ) * Tᶜ.card) = 4 * J + (if Tᶜ.card ≤ K + 1 then
            ((Tᶜ.card : ℝ) - 1) * φ else 0) * Tᶜ.card := by
        field_simp
      rw [add_mul, e, e2]
      nlinarith
    · rw [not_le] at hK
      have hC : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
          Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ := by
        calc ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
              ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, φ :=
            sum_le_sum fun s hs ↦ sum_le_sum fun t _ ↦ abs_condCov_le hP hA (mem_compl.mp hs)
          _ = Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ := by
            rw [sum_congr rfl fun s hs ↦ by rw [sum_const, card_erase_of_mem hs], sum_const,
              nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub (by omega)]
            push_cast
            ring
      refine hdrift.trans ?_
      rw [show (if Tᶜ.card ≤ K + 1 then ((Tᶜ.card : ℝ) - 1) * φ else 0) =
        ((Tᶜ.card : ℝ) - 1) * φ from ite_eq_left (by omega), div_le_iff₀ (mul_pos h1φ hNpos)]
      have e2 : (4 * J / Tᶜ.card + ((Tᶜ.card : ℝ) - 1) * φ) / (1 - φ) * ((1 - φ) * Tᶜ.card) =
          4 * J + ((Tᶜ.card : ℝ) - 1) * φ * Tᶜ.card := by
        field_simp
      rw [add_mul, e2]
      have : 0 ≤ 2 * √J / (1 - φ) * outAvg (condProb P A) T * ((1 - φ) * Tᶜ.card) := by
        positivity
      nlinarith
  calc |chainAvg (condProb P A) - ∑ t, prob P (A t)| =
        |∑ i ∈ range (Fintype.card ι - 1), levelAvg (drift P A) i| := by
        rw [hid, sub_sub_cancel_left, abs_neg]
    _ ≤ ∑ i ∈ range (Fintype.card ι - 1), levelAvg (fun T ↦ |drift P A T|) i :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ abs_levelAvg_le _ _)
    _ ≤ ∑ i ∈ range (Fintype.card ι - 1), (2 * √J / (1 - φ) *
          levelAvg (outAvg (condProb P A)) i + (4 * J / ((Fintype.card ι - i : ℕ) : ℝ) +
            if Fintype.card ι - i ≤ K + 1 then (((Fintype.card ι - i : ℕ) : ℝ) - 1) * φ
              else 0) / (1 - φ)) := by
        refine sum_le_sum fun i hi ↦ ?_
        have hi' := mem_range.mp hi
        rw [← levelAvg_affine _ _ _ (by omega)]
        exact levelAvg_mono fun T hT' ↦ hT i (by omega) T hT'
    _ = 2 * √J / (1 - φ) * ∑ i ∈ range (Fintype.card ι - 1),
          levelAvg (outAvg (condProb P A)) i + (∑ i ∈ range (Fintype.card ι - 1),
            (4 * J / ((Fintype.card ι - i : ℕ) : ℝ) + if Fintype.card ι - i ≤ K + 1 then
              (((Fintype.card ι - i : ℕ) : ℝ) - 1) * φ else 0)) / (1 - φ) := by
        rw [sum_add_distrib, mul_sum, sum_div]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ hθ)
          (div_le_div_of_nonneg_right (sum_corr_le _ _ hJ hφ0) h1φ.le)
        exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le _ 1))
          fun i _ _ ↦ levelAvg_nonneg
            (fun T ↦ div_nonneg (condMean_nonneg hP T) (Nat.cast_nonneg _)) i

/-- Theorem 7(i) of COD-196 (`cod-196-averaged-pinning.md`) under hypothesis (B′) of
`abs_chainAvg_sub_le`: `-log q ≥ (μ - η) / (1 + θ)`. -/
theorem div_le_neg_log_prob_avoid (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    (∑ t, prob P (A t) - (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ)) /
        (1 + 2 * √J / (1 - φ)) ≤ -Real.log (prob P (avoid A univ)) := by
  have hq := prob_avoid_pos hP hφ1 hA
  have h1φ : 0 < 1 - φ := by linarith
  have hθ : 0 ≤ 2 * √J / (1 - φ) := div_nonneg (by positivity) h1φ.le
  have hcore := (abs_le.mp (abs_chainAvg_sub_le hP hφ0 hφ1 hJ hA hB)).1
  have hS := chainAvg_le_neg_log hP hq
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Theorem 7(ii) of COD-196 (`cod-196-averaged-pinning.md`) under hypothesis (B′) of
`abs_chainAvg_sub_le`: if `θ < 1`, then `-log q ≤ (μ + η) / ((1 - φ)(1 - θ))`. -/
theorem neg_log_prob_avoid_le_div (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J)
    (hθ1 : 2 * √J / (1 - φ) < 1) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t) + (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) /
        (1 - φ)) / ((1 - φ) * (1 - 2 * √J / (1 - φ))) := by
  have hq := prob_avoid_pos hP hφ1 hA
  have h1φ : 0 < 1 - φ := by linarith
  have hcore := (abs_le.mp (abs_chainAvg_sub_le hP hφ0 hφ1 hJ hA hB)).2
  have h1 : -Real.log (prob P (avoid A univ)) ≤ chainAvg (condProb P A) * (1 / (1 - φ)) := by
    refine (neg_log_le_chainAvg hP hq).trans ?_
    rw [← chainAvg_mul_const]
    refine chainAvg_mono fun T s hs ↦ ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (condProb_nonneg hP T s) h1φ
      (by linarith [hA T s hs])
  refine h1.trans ?_
  rw [le_div_iff₀ (mul_pos h1φ (by linarith)), mul_one_div, div_mul_eq_mul_div,
    div_le_iff₀ h1φ]
  nlinarith

end Theorem7

section Lemma3

/-- `u log u - u + 1 ≥ (u - 1)² / 2` on `[0, 1]`. -/
theorem sq_div_two_le_klFun {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u - 1) ^ 2 / 2 ≤ u * Real.log u - u + 1 := by
  rcases hu0.eq_or_lt with rfl | hu0
  · norm_num
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x ↦ x * Real.log x - x + 1 - (x - 1) ^ 2 / 2)
      (Real.log x + 1 - x) x := fun x hx ↦ by
    convert ((((Real.hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id' x)).add_const 1).sub
      ((((hasDerivAt_id' x).sub_const 1).pow 2).div_const 2)) using 1
    push_cast
    ring
  have hanti : AntitoneOn (fun x ↦ x * Real.log x - x + 1 - (x - 1) ^ 2 / 2) (Set.Ioc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
      (fun x hx ↦ (hd x hx.1).continuousAt.continuousWithinAt) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ioc] at hx
      exact (hd x hx.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc] at hx
      rw [(hd x hx.1).deriv]
      linarith [Real.log_le_sub_one_of_pos hx.1]
  have h := hanti ⟨hu0, hu1⟩ ⟨one_pos, le_rfl⟩ hu1
  norm_num at h
  linarith

/-- `u log u - u + 1 ≥ (u - 1)² / (2 u)` for `u ≥ 1`. -/
theorem sq_div_le_klFun {u : ℝ} (hu : 1 ≤ u) :
    (u - 1) ^ 2 / (2 * u) ≤ u * Real.log u - u + 1 := by
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun x ↦ x * Real.log x - x + 1 - (x / 2 - 1 + x⁻¹ / 2))
        (Real.log x - 1 / 2 + (x ^ 2)⁻¹ / 2) x := fun x hx ↦ by
    convert ((((Real.hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id' x)).add_const 1).sub
      ((((hasDerivAt_id' x).div_const 2).sub_const 1).add
        ((hasDerivAt_inv hx.ne').div_const 2))) using 1
    ring
  have hmono : MonotoneOn (fun x ↦ x * Real.log x - x + 1 - (x / 2 - 1 + x⁻¹ / 2))
      (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun x hx ↦ (hd x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ici] at hx
      exact (hd x (one_pos.trans hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := one_pos.trans hx
      rw [(hd x hx0).deriv]
      have h := Real.one_sub_inv_le_log_of_pos (pow_pos hx0 2)
      rw [Real.log_pow] at h
      push_cast at h
      linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) hu hu
  norm_num at h
  have hu0 : 0 < u := one_pos.trans_le hu
  have e : (u - 1) ^ 2 / (2 * u) = u / 2 - 1 + u⁻¹ / 2 := by
    field_simp
    ring
  linarith

/-- `x log(x / y) - x + y ≥ (x - y)² / (2 max(x, y))` for `x ≥ 0` and `y > 0`. -/
theorem sq_div_max_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    (x - y) ^ 2 / (2 * max x y) ≤ x * Real.log (x / y) - x + y := by
  have hu : 0 ≤ x / y := div_nonneg hx hy.le
  have key : x * Real.log (x / y) - x + y = y * (x / y * Real.log (x / y) - x / y + 1) := by
    field_simp
  rw [key]
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    calc (x - y) ^ 2 / (2 * y) = y * ((x / y - 1) ^ 2 / 2) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_div_two_le_klFun hu ((div_le_one hy).mpr h)) hy.le
  · have hx' : 0 < x := hy.trans_le h
    rw [max_eq_left h]
    calc (x - y) ^ 2 / (2 * x) = y * ((x / y - 1) ^ 2 / (2 * (x / y))) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_div_le_klFun ((one_le_div hy).mpr h)) hy.le

/-- `x log(x / y) - x + y ≥ 0` for `x, y ≥ 0` with `x = 0` when `y = 0`. -/
theorem klTerm_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y = 0 → x = 0) :
    0 ≤ x * Real.log (x / y) - x + y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [hxy rfl]
  · exact (div_nonneg (sq_nonneg _) (mul_pos two_pos (lt_max_of_lt_right hy)).le).trans
      (sq_div_max_le hx hy)

/-- The mutual information `I(Y_s; Y_t)` of two binary variables with `P(Y_s = 1) = a`,
`P(Y_t = 1) = b` and `P(Y_s = Y_t = 1) = c`, that is
`∑_{x, y} P(x, y) log(P(x, y) / (P(x) P(y)))` with `0 log 0 = 0`. -/
noncomputable def binMI (a b c : ℝ) : ℝ :=
  c * Real.log (c / (a * b)) + (a - c) * Real.log ((a - c) / (a * (1 - b))) +
    (b - c) * Real.log ((b - c) / ((1 - a) * b)) +
      (1 - a - b + c) * Real.log ((1 - a - b + c) / ((1 - a) * (1 - b)))

/-- `(a, b, c)` describes a joint law of two binary variables, `0 ≤ c ≤ a, b` and
`a + b - c ≤ 1`. -/
structure IsBinLaw (a b c : ℝ) : Prop where
  nonneg : 0 ≤ c
  le_left : c ≤ a
  le_right : c ≤ b
  add_le : a + b - c ≤ 1

/-- `I = ∑_{x, y} (P(x, y) log(P(x, y) / Q(x, y)) - P(x, y) + Q(x, y))` with
`Q(x, y) = P(x) P(y)`, since both laws have total mass `1`. -/
theorem binMI_eq (a b c : ℝ) :
    binMI a b c = (c * Real.log (c / (a * b)) - c + a * b) +
      ((a - c) * Real.log ((a - c) / (a * (1 - b))) - (a - c) + a * (1 - b)) +
      ((b - c) * Real.log ((b - c) / ((1 - a) * b)) - (b - c) + (1 - a) * b) +
      ((1 - a - b + c) * Real.log ((1 - a - b + c) / ((1 - a) * (1 - b))) -
        (1 - a - b + c) + (1 - a) * (1 - b)) := by
  rw [binMI]
  ring

/-- The `(1, 1)` cell bounds the mutual information below,
`I ≥ c log(c / (a b)) - c + a b`. -/
theorem binMI_ge {a b c : ℝ} (h : IsBinLaw a b c) :
    c * Real.log (c / (a * b)) - c + a * b ≤ binMI a b c := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have h2' := klTerm_nonneg (x := a - c) (y := a * (1 - b)) (by linarith)
    (mul_nonneg (by linarith) (by linarith)) fun h ↦ by
      rcases mul_eq_zero.mp h with h | h <;> linarith
  have h3' := klTerm_nonneg (x := b - c) (y := (1 - a) * b) (by linarith)
    (mul_nonneg (by linarith) (by linarith)) fun h ↦ by
      rcases mul_eq_zero.mp h with h | h <;> linarith
  have h4' := klTerm_nonneg (x := 1 - a - b + c) (y := (1 - a) * (1 - b)) (by linarith)
    (mul_nonneg (by linarith) (by linarith)) fun h ↦ by
      rcases mul_eq_zero.mp h with h | h <;> linarith
  rw [binMI_eq]
  linarith

/-- `I(Y_s; Y_t) ≥ 0`. -/
theorem binMI_nonneg {a b c : ℝ} (h : IsBinLaw a b c) : 0 ≤ binMI a b c := by
  refine le_trans ?_ (binMI_ge h)
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact klTerm_nonneg h0 (mul_nonneg (by linarith) (by linarith)) fun h ↦ by
    rcases mul_eq_zero.mp h with h | h <;> linarith

/-- Lemma 3 of COD-196 (`cod-196-averaged-pinning.md`), the chi-square lower bound on binary
mutual information: for a joint law with `a, b > 0`,
`I(Y_s; Y_t) ≥ (c - a b)² / (2 max(c, a b))`. -/
theorem sq_div_le_binMI {a b c : ℝ} (h : IsBinLaw a b c) (ha : 0 < a) (hb : 0 < b) :
    (c - a * b) ^ 2 / (2 * max c (a * b)) ≤ binMI a b c :=
  (sq_div_max_le h.nonneg (mul_pos ha hb)).trans (binMI_ge h)

/-- The per-pair form of Lemma 3 of COD-196: `|c - a b| ≤ 2 √(a b) √I + 4 I`. -/
theorem abs_sub_le_binMI {a b c : ℝ} (h : IsBinLaw a b c) :
    |c - a * b| ≤ 2 * √(a * b) * √(binMI a b c) + 4 * binMI a b c := by
  have hI := binMI_nonneg h
  have ha : 0 ≤ a := h.nonneg.trans h.le_left
  have hb : 0 ≤ b := h.nonneg.trans h.le_right
  rcases ha.eq_or_lt with rfl | ha
  · have : c = 0 := le_antisymm h.le_left h.nonneg
    subst this
    simp only [zero_mul, sub_zero, abs_zero]
    exact add_nonneg (by positivity) (by linarith)
  rcases hb.eq_or_lt with rfl | hb
  · have : c = 0 := le_antisymm h.le_right h.nonneg
    subst this
    simp only [mul_zero, sub_zero, abs_zero]
    exact add_nonneg (by positivity) (by linarith)
  have hw : 0 < a * b := mul_pos ha hb
  have hq := sq_div_le_binMI h ha hb
  have hs : 0 ≤ 2 * √(a * b) * √(binMI a b c) := by positivity
  rcases le_or_gt c (2 * (a * b)) with hc | hc
  · have hmax : 2 * max c (a * b) ≤ 4 * (a * b) := by
      rw [show 4 * (a * b) = 2 * (2 * (a * b)) by ring]
      exact mul_le_mul_of_nonneg_left (max_le hc (by linarith)) zero_le_two
    have h1 : (c - a * b) ^ 2 / (4 * (a * b)) ≤ binMI a b c :=
      (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos two_pos (lt_max_of_lt_right hw)) hmax).trans
        hq
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : |c - a * b| ≤ √(4 * (a * b) * binMI a b c) := Real.abs_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two] at h2
    linarith
  · have hmax : max c (a * b) = c := max_eq_left (by linarith)
    rw [hmax] at hq
    have hc0 : 0 < c := by linarith
    have h1 : (c - a * b) / 4 ≤ (c - a * b) ^ 2 / (2 * c) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    rw [abs_of_pos (by linarith)]
    linarith

/-- Lemma 3 of COD-196 (`cod-196-averaged-pinning.md`), the summed form: for a finite family of
joint laws of binary pairs, `∑ |c - a b| ≤ 2 (∑ a b)^(1/2) (∑ I)^(1/2) + 4 ∑ I`. -/
theorem sum_abs_sub_le_binMI {κ : Type*} (s : Finset κ) (a b c : κ → ℝ)
    (h : ∀ k ∈ s, IsBinLaw (a k) (b k) (c k)) :
    ∑ k ∈ s, |c k - a k * b k| ≤
      2 * √(∑ k ∈ s, a k * b k) * √(∑ k ∈ s, binMI (a k) (b k) (c k)) +
        4 * ∑ k ∈ s, binMI (a k) (b k) (c k) := by
  have hw : ∀ k ∈ s, 0 ≤ a k * b k := fun k hk ↦
    mul_nonneg ((h k hk).nonneg.trans (h k hk).le_left) ((h k hk).nonneg.trans (h k hk).le_right)
  have hI : ∀ k ∈ s, 0 ≤ binMI (a k) (b k) (c k) := fun k hk ↦ binMI_nonneg (h k hk)
  have hcs : ∑ k ∈ s, √(a k * b k) * √(binMI (a k) (b k) (c k)) ≤
      √(∑ k ∈ s, a k * b k) * √(∑ k ∈ s, binMI (a k) (b k) (c k)) := by
    have h1 := sum_mul_sq_le_sq_mul_sq s (fun k ↦ √(a k * b k))
      (fun k ↦ √(binMI (a k) (b k) (c k)))
    rw [sum_congr rfl fun k hk ↦ Real.sq_sqrt (hw k hk),
      sum_congr rfl fun k hk ↦ Real.sq_sqrt (hI k hk)] at h1
    rw [← Real.sqrt_mul (sum_nonneg hw)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  calc ∑ k ∈ s, |c k - a k * b k| ≤
        ∑ k ∈ s, (2 * √(a k * b k) * √(binMI (a k) (b k) (c k)) +
          4 * binMI (a k) (b k) (c k)) :=
        sum_le_sum fun k hk ↦ abs_sub_le_binMI (h k hk)
    _ = 2 * ∑ k ∈ s, √(a k * b k) * √(binMI (a k) (b k) (c k)) +
          4 * ∑ k ∈ s, binMI (a k) (b k) (c k) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
        simp only [mul_assoc]
    _ ≤ _ := by linarith

end Lemma3

section Theorem7B

variable [Fintype ι]

omit [Fintype ι] [DecidableEq ι] in
/-- `f_s(T) + f_t(T) - U(A_s A_t | Z_T) ≤ 1`. -/
theorem condProb_add_condProb_sub_condPair_le_one (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condProb P A T s + condProb P A T t - condPair P A T s t ≤ 1 := by
  by_cases hz : prob P (avoid A T) = 0
  · simp [condProb, condPair, hz]
  have hz' : 0 < prob P (avoid A T) := lt_of_le_of_ne (prob_nonneg hP _) (Ne.symm hz)
  have h : prob P (A s ∩ avoid A T) + prob P (A t ∩ avoid A T) ≤
      prob P (avoid A T) + prob P (A s ∩ A t ∩ avoid A T) := by
    simp only [prob, ← sum_add_distrib]
    refine sum_le_sum fun ω _ ↦ ?_
    have := hP.nonneg ω
    by_cases h1 : ω ∈ A s <;> by_cases h2 : ω ∈ A t <;> by_cases h3 : ω ∈ avoid A T <;>
      simp [Set.indicator, h1, h2, h3, this]
  rw [condProb, condProb, condPair, ← add_div, ← sub_div, div_le_one hz']
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Under `ν_T`, the indicators of `A_s` and `A_t` form a joint law of two binary variables. -/
theorem isBinLaw_cond (hP : IsProb P) (T : Finset ι) (s t : ι) :
    IsBinLaw (condProb P A T s) (condProb P A T t) (condPair P A T s t) :=
  ⟨condPair_nonneg hP T s t, condPair_le_left hP T s t, condPair_le_right hP T s t,
    condProb_add_condProb_sub_condPair_le_one hP T s t⟩

/-- `J_T = ∑_{s ≠ t ∉ T} I_{ν_T}(Y_s; Y_t)`, summed over ordered pairs. -/
noncomputable def pairInfo (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, binMI (condProb P A T s) (condProb P A T t) (condPair P A T s t)

/-- Lemma 3 of COD-196 (`cod-196-averaged-pinning.md`) applied to `ν_T`, as in the proof of
Theorem 7: `∑_{s ≠ t ∉ T} |Cov_T(s, t)| ≤ 2 M_T √J_T + 4 J_T`. -/
theorem sum_abs_condCov_le (hP : IsProb P) (T : Finset ι) :
    ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
      2 * √(pairInfo P A T) * condMean P A T + 4 * pairInfo P A T := by
  have h := sum_abs_sub_le_binMI (Tᶜ.sigma fun s ↦ Tᶜ.erase s)
    (fun x ↦ condProb P A T x.1) (fun x ↦ condProb P A T x.2)
    (fun x ↦ condPair P A T x.1 x.2) fun x _ ↦ isBinLaw_cond hP T x.1 x.2
  simp only [sum_sigma] at h
  have hM0 := condMean_nonneg hP (A := A) T
  have hM : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, condProb P A T s * condProb P A T t ≤
      condMean P A T ^ 2 := by
    calc ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, condProb P A T s * condProb P A T t =
          ∑ s ∈ Tᶜ, condProb P A T s * (condMean P A T - condProb P A T s) :=
          sum_congr rfl fun s hs ↦ by rw [← mul_sum, sum_erase_eq_sub hs, condMean]
      _ ≤ ∑ s ∈ Tᶜ, condProb P A T s * condMean P A T :=
          sum_le_sum fun s _ ↦ by nlinarith [condProb_nonneg hP (A := A) T s]
      _ = condMean P A T ^ 2 := by rw [← sum_mul, ← condMean, sq]
  have hsq : √(∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, condProb P A T s * condProb P A T t) ≤
      condMean P A T := by
    rw [← Real.sqrt_sq hM0]
    exact Real.sqrt_le_sqrt hM
  have hJ := Real.sqrt_nonneg (pairInfo P A T)
  have h' : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
      2 * √(∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, condProb P A T s * condProb P A T t) *
        √(pairInfo P A T) + 4 * pairInfo P A T := h
  nlinarith [mul_le_mul_of_nonneg_right hsq hJ]

/-- Hypothesis (B) of Theorem 7 of COD-196 gives hypothesis (B′) of
`abs_chainAvg_sub_le`, through Lemma 3. -/
theorem hB'_of_pairInfo (hP : IsProb P) {J : ℝ} {K : ℕ}
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card → pairInfo P A T ≤ J) (T : Finset ι)
    (hT : K + 2 ≤ Tᶜ.card) :
    ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J := by
  have hM0 := condMean_nonneg hP (A := A) T
  have h1 := Real.sqrt_le_sqrt (hB T hT)
  refine (sum_abs_condCov_le hP T).trans ?_
  nlinarith [hB T hT]

/-- Theorem 7(i) of COD-196 (`cod-196-averaged-pinning.md`). Assume (A) `f_t(T) ≤ φ < 1` for
every `T` and `t ∉ T`, and (B) `J_T ≤ J` for every `T` with `N_T ≥ K + 2`, where
`J_T = ∑_{s ≠ t ∉ T} I_{ν_T}(Y_s; Y_t)`. With `μ = ∑_t U(A_t)`, `θ = 2 √J / (1 - φ)` and
`η = (4 J log n + K (K + 1) φ / 2) / (1 - φ)`, `-log q ≥ (μ - η) / (1 + θ)`. -/
theorem div_le_neg_log_prob_avoid_of_pairInfo (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card → pairInfo P A T ≤ J) :
    (∑ t, prob P (A t) - (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) / (1 - φ)) /
        (1 + 2 * √J / (1 - φ)) ≤ -Real.log (prob P (avoid A univ)) :=
  div_le_neg_log_prob_avoid hP hφ0 hφ1 hJ hA (hB'_of_pairInfo hP hB)

/-- Theorem 7(ii) of COD-196 (`cod-196-averaged-pinning.md`). Under the hypotheses of
`div_le_neg_log_prob_avoid_of_pairInfo`, if `θ < 1`, then
`-log q ≤ (μ + η) / ((1 - φ)(1 - θ))`. -/
theorem neg_log_prob_avoid_le_div_of_pairInfo (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card → pairInfo P A T ≤ J)
    (hθ1 : 2 * √J / (1 - φ) < 1) :
    -Real.log (prob P (avoid A univ)) ≤
      (∑ t, prob P (A t) + (4 * J * Real.log (Fintype.card ι) + K * (K + 1) * φ / 2) /
        (1 - φ)) / ((1 - φ) * (1 - 2 * √J / (1 - φ))) :=
  neg_log_prob_avoid_le_div hP hφ0 hφ1 hJ hA (hB'_of_pairInfo hP hB) hθ1

end Theorem7B

section Orderings

variable [Fintype ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Relabelling an ordering by a permutation `τ` relabels its prefixes. -/
theorem pre_trans {n : ℕ} (σ : Fin n ≃ ι) (τ : Equiv.Perm ι) (k : ℕ) :
    pre (σ.trans τ) k = (pre σ k).map τ.toEmbedding := by
  ext x
  rw [mem_pre, mem_map_equiv, mem_pre]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The permutations of `ι` act transitively on the pairs `(T, s)` with `|T| = k` and
`s ∉ T`. -/
theorem exists_perm_map_eq {k : ℕ} {T T' : Finset ι} {s s' : ι} (hT : T.card = k)
    (hT' : T'.card = k) (hs : s ∉ T) (hs' : s' ∉ T') :
    ∃ τ : Equiv.Perm ι, T.map τ.toEmbedding = T' ∧ τ s = s' := by
  classical
  have := Set.powersetCard.isPretransitive (α := ι) (n := k + 1)
  obtain ⟨τ₁, h₁⟩ := MulAction.exists_smul_eq (Equiv.Perm ι)
    (⟨insert s T, by rw [Set.powersetCard.mem_iff, card_insert_of_notMem hs, hT]⟩ :
      Set.powersetCard ι (k + 1))
    ⟨insert s' T', by rw [Set.powersetCard.mem_iff, card_insert_of_notMem hs', hT']⟩
  have h₂ : (insert s T).image τ₁ = insert s' T' := by
    have := congrArg Subtype.val h₁
    simpa [Set.powersetCard.coe_smul, Finset.smul_finset_def] using this
  have hmem : τ₁ s ∈ insert s' T' := h₂ ▸ mem_image_of_mem τ₁ (mem_insert_self s T)
  set τ := τ₁.trans (Equiv.swap (τ₁ s) s') with hτ
  have hτs : τ s = s' := by simp [τ]
  refine ⟨τ, ?_, hτs⟩
  have h₃ : (insert s T).map τ.toEmbedding = insert s' T' := by
    refine eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · rw [mem_map_equiv] at hy
      have hy' : τ₁ (τ.symm y) ∈ insert s' T' := h₂ ▸ mem_image_of_mem τ₁ hy
      have e : τ₁ (τ.symm y) = Equiv.swap (τ₁ s) s' y := by simp [τ, Equiv.symm_swap]
      rw [e] at hy'
      rcases eq_or_ne y (τ₁ s) with rfl | h1
      · exact hmem
      rcases eq_or_ne y s' with rfl | h2
      · exact mem_insert_self _ _
      rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hy'
    · rw [card_map, card_insert_of_notMem hs, card_insert_of_notMem hs', hT, hT']
  rw [map_insert, Equiv.coe_toEmbedding, hτs] at h₃
  have hs'' : s' ∉ T.map τ.toEmbedding := by
    rw [mem_map_equiv, ← hτs, Equiv.symm_apply_apply]
    exact hs
  rw [← erase_insert hs'', h₃, erase_insert hs']

/-- For `k < n`, the average over all orderings `σ : Fin n ≃ ι` of `G(T_k, σ k)` is
`E_{|T| = k} (1 / N_T) ∑_{s ∉ T} G(T, s)`: the prefix `T_k` of a uniformly random ordering is a
uniform `k`-set, and `σ k` is uniform outside it. -/
theorem sum_equiv_div_factorial (G : Finset ι → ι → ℝ) (k : Fin (Fintype.card ι)) :
    (∑ σ : Fin (Fintype.card ι) ≃ ι, G (pre σ k) (σ k)) / (Fintype.card ι).factorial =
      levelAvg (outAvg G) k := by
  set Pk := (powersetCard (k : ℕ) univ ×ˢ (univ : Finset ι)).filter fun x ↦ x.2 ∉ x.1
    with hPk
  have hmemPk : ∀ x : Finset ι × ι, x ∈ Pk ↔ x.1 ∈ powersetCard (k : ℕ) univ ∧ x.2 ∈ x.1ᶜ :=
    fun x ↦ by simp [Pk]
  set f : (Fin (Fintype.card ι) ≃ ι) → Finset ι × ι := fun σ ↦ (pre σ k, σ k) with hf_def
  have hf : ∀ σ ∈ (univ : Finset (Fin (Fintype.card ι) ≃ ι)), f σ ∈ Pk := fun σ _ ↦ by
    rw [hmemPk, mem_powersetCard, mem_compl]
    exact ⟨⟨subset_univ _, card_pre σ k.isLt.le⟩, notMem_pre σ le_rfl⟩
  set c : Finset ι × ι → ℕ := fun x ↦ (univ.filter fun σ ↦ f σ = x).card with hc_def
  have hinv : ∀ (τ : Equiv.Perm ι) x, c (x.1.map τ.toEmbedding, τ x.2) = c x := by
    intro τ x
    refine card_nbij' (fun σ ↦ σ.trans τ.symm) (fun σ ↦ σ.trans τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_coe, mem_filter, mem_univ, true_and, f, Prod.ext_iff] at hσ ⊢
      rw [pre_trans, hσ.1]
      refine ⟨?_, by simp [hσ.2]⟩
      ext y
      simp [mem_map_equiv]
    · intro σ hσ
      simp only [mem_coe, mem_filter, mem_univ, true_and, f, Prod.ext_iff] at hσ ⊢
      rw [pre_trans, hσ.1]
      exact ⟨rfl, by simp [hσ.2]⟩
    · intro σ _
      ext
      simp
    · intro σ _
      ext
      simp
  set e₀ := (Fintype.equivFin ι).symm
  have hconst : ∀ x ∈ Pk, c x = c (f e₀) := by
    intro x hx
    rw [hmemPk, mem_powersetCard, mem_compl] at hx
    obtain ⟨τ, h1, h2⟩ := exists_perm_map_eq (card_pre e₀ k.isLt.le) hx.1.2
      (notMem_pre e₀ (k := k) (j := k) le_rfl) hx.2
    rw [← hinv τ (f e₀)]
    exact congrArg c (Prod.ext h1 h2).symm
  have hcard : (Fintype.card ι).factorial = ∑ x ∈ Pk, c x := by
    have h1 : (univ : Finset (Fin (Fintype.card ι) ≃ ι)).card = (Fintype.card ι).factorial := by
      rw [card_univ, Fintype.card_equiv e₀, Fintype.card_fin]
    rw [← h1]
    exact card_eq_sum_card_fiberwise fun σ hσ ↦ hf σ (mem_coe.mp hσ)
  have hsumG : ∑ σ : Fin (Fintype.card ι) ≃ ι, G (pre σ k) (σ k) =
      c (f e₀) * ∑ x ∈ Pk, G x.1 x.2 := by
    rw [← sum_fiberwise_of_maps_to' hf (fun x ↦ G x.1 x.2), mul_sum]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [sum_const, nsmul_eq_mul, ← hconst x hx]
  have hPkG : ∑ x ∈ Pk, G x.1 x.2 = ∑ T ∈ powersetCard (k : ℕ) univ, ∑ s ∈ Tᶜ, G T s :=
    sum_finset_product' Pk _ _ hmemPk
  have hPk1 : ((∑ x ∈ Pk, c x : ℕ) : ℝ) = c (f e₀) *
      (((Fintype.card ι).choose k : ℕ) * (Fintype.card ι - k)) := by
    rw [Nat.cast_sum, sum_congr rfl fun x hx ↦ by rw [hconst x hx], sum_const, nsmul_eq_mul,
      mul_comm]
    congr 1
    have h := sum_finset_product' Pk _ _ hmemPk (f := fun _ _ ↦ (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one] at h
    rw [sum_congr rfl fun T hT ↦ card_compl_of_mem_powersetCard hT, sum_const,
      card_powersetCard, card_univ, nsmul_eq_mul] at h
    exact h
  have hc0 : (c (f e₀) : ℝ) ≠ 0 := by
    intro h0
    have := hPk1
    rw [h0, zero_mul, ← hcard] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) this
  have hk : (k : ℕ) < Fintype.card ι := k.isLt
  have hni : (0 : ℝ) < Fintype.card ι - k := by
    have : ((k : ℕ) : ℝ) < Fintype.card ι := by exact_mod_cast hk
    linarith
  have hch := choose_pos_real hk.le
  have hL : levelAvg (outAvg G) k = (∑ T ∈ powersetCard (k : ℕ) univ, ∑ s ∈ Tᶜ, G T s) /
      (((Fintype.card ι).choose k : ℕ) * (Fintype.card ι - k)) := by
    simp only [levelAvg, outAvg]
    rw [mul_comm (((Fintype.card ι).choose k : ℕ) : ℝ), ← div_div]
    congr 1
    rw [sum_div]
    exact sum_congr rfl fun T hT ↦ by rw [card_compl_of_mem_powersetCard hT]
  rw [hL, hcard, hPk1, hsumG, hPkG, mul_div_mul_left _ _ hc0]

/-- `chainAvg G` is the average of `∑_k G(T_k, σ k)` over all `n!` orderings `σ : Fin n ≃ ι`,
which is the expectation `E_π ∑_k G(T_k, π_k)` of Proposition 6 of COD-196
(`cod-196-averaged-pinning.md`) for a uniformly random ordering `π`. -/
theorem chainAvg_eq_sum_equiv (G : Finset ι → ι → ℝ) :
    chainAvg G = (∑ σ : Fin (Fintype.card ι) ≃ ι, ∑ k : Fin (Fintype.card ι),
      G (pre σ k) (σ k)) / (Fintype.card ι).factorial := by
  rw [sum_comm, sum_div, chainAvg, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun k _ ↦ (sum_equiv_div_factorial G k).symm

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the averaged chain identity over
uniformly random orderings: if `q > 0`, then the average of `∑_k f_{σ k}(T_k)` over all `n!`
orderings `σ` is `μ - ∑_{i ≤ n - 2} E_{|T| = i} Δ_T`, with `μ = ∑_t U(A_t)`. -/
theorem sum_equiv_condProb (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    (∑ σ : Fin (Fintype.card ι) ≃ ι, ∑ k : Fin (Fintype.card ι),
      condProb P A (pre σ k) (σ k)) / (Fintype.card ι).factorial =
      ∑ t, prob P (A t) - ∑ i ∈ range (Fintype.card ι - 1), levelAvg (drift P A) i := by
  rw [← chainAvg_eq_sum_equiv, chainAvg_condProb hP hq]

/-- Proposition 6 of COD-196 (`cod-196-averaged-pinning.md`), the sandwich over uniformly random
orderings: if `q > 0`, then `E_π ∑_k f_k ≤ -log q ≤ E_π ∑_k f_k / (1 - f_k)`, where `E_π` is the
average over all `n!` orderings and `f_k = f_{π k}(T_k)`. -/
theorem sum_equiv_le_neg_log_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    (∑ σ : Fin (Fintype.card ι) ≃ ι, ∑ k : Fin (Fintype.card ι),
        condProb P A (pre σ k) (σ k)) / (Fintype.card ι).factorial ≤
        -Real.log (prob P (avoid A univ)) ∧
      -Real.log (prob P (avoid A univ)) ≤
        (∑ σ : Fin (Fintype.card ι) ≃ ι, ∑ k : Fin (Fintype.card ι),
          condProb P A (pre σ k) (σ k) / (1 - condProb P A (pre σ k) (σ k))) /
            (Fintype.card ι).factorial := by
  rw [← chainAvg_eq_sum_equiv, ← chainAvg_eq_sum_equiv (fun T s ↦
    condProb P A T s / (1 - condProb P A T s))]
  exact ⟨chainAvg_le_neg_log hP hq, neg_log_le_chainAvg hP hq⟩

end Orderings

end ChainRule

namespace RoundRobin.Canonical

open Finset ChainRule PerfectMatching

/-- The round-robin event `A_t = {P | P ∪ F_t is one cycle}`. -/
def hamEvent (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) : Set (PerfectMatching (Vertex m)) :=
  {P | Ham P (factor m t)}

/-- The round-robin instance: `U(A_t) = U(A_0)` for every `t`, the common probability `p`. -/
theorem prob_hamEvent (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) :
    prob (unifWeight m) (hamEvent m t) = prob (unifWeight m) (hamEvent m 0) := by
  classical
  rw [prob_unifWeight, prob_unifWeight]
  have h := card_ham_and_eq m (fun _ ↦ True) t
  simp only [and_true] at h
  congr 2
  convert h using 2 <;> exact filter_congr fun P _ ↦ Iff.rfl

/-- The round-robin instance: `q_m = U(Z_{Z_n}) = P(X = 0)`, so the bounds on
`prob P (avoid A univ)` in this file are bounds on `q_m = hamLaw m 0`. -/
theorem prob_avoid_hamEvent (m : ℕ) [NeZero m] :
    prob (unifWeight m) (avoid (hamEvent m) univ) = hamLaw m 0 := by
  rw [hamLaw_eq_lawOf, lawOf]
  congr 1
  ext P
  simp [avoid, hamEvent, hamCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

end RoundRobin.Canonical

end Pairing
