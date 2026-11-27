import Mathlib.Algebra.Order.Chebyshev
import Suppression.ChainRule

/-!
# The re-weighted ordering of the chain rule (COD-198, COD-215)

Notation is that of `ChainRule.lean`: `P` is a probability weight on a finite set `Ω`,
`A : ι → Set Ω` are events indexed by a finite set `ι` with `n = |ι|`, `Z_T = avoid A T`,
`f_s(T) = condProb P A T s`, `M_T = condMean P A T`, `Cov_T(s, t) = condCov P A T s t`,
`μ = ∑_t U(A_t)` and `q = U(Z_ι)`.
Here `X = #{t : ω ∈ A_t}` (`eventCount`), and

* `V_T = Var(X | Z_T)` (`condVar`), `B_T = ∑_{s ∉ T} f_s(T)(1 - f_s(T))` (`bernVarSum`),
* `D_T = N_T - M_T = ∑_{s ∉ T} (1 - f_s(T))` (`condSlack`),
* `L_T = ∑_{s ∉ T} -(1 - f_s(T)) log(1 - f_s(T))` (`entSum`).

The Markov chain on subsets that moves from `T` to `T ∪ s` with probability `w(T, s)` has
`E[∑_{k ≤ n} G(T_{k-1}, s_k) | T_0 = T]` given by the first-step recursion `kerExp w G n T`.
With the uniform step law `1 / N_T` this is `chainAvg`, the average over all orderings
(`kerExp_uniform`). The chain of COD-198 is `w = reweight P A`, `w_T(s) = (1 - f_s(T)) / D_T`.
Standing hypothesis, as in the paper: `q > 0`.

From `cod-198-attempt.md` (COD-198):

* `kerExp_reweight_condVar`, `kerExp_reweight_entSum` (Theorem 3(a), (b)) :
  `E_w ∑_k V_{T_{k-1}} / D_{T_{k-1}} = μ` and `E_w ∑_k L_{T_{k-1}} / D_{T_{k-1}} = -log q`.
* `kerExp_bernVarSum_le_neg_log`, `neg_log_le_kerExp_condMean`, `kerExp_reweight_condProb`,
  `kerExp_reweight_condProb_div` (Theorem 3(c)).
* `inf'_mul_le_neg_log`, `neg_log_le_sup'_mul` (Theorem 3(d)) :
  `μ min_T (L_T / V_T) ≤ -log q ≤ μ max_T (L_T / V_T)`, and `mul_le_neg_log_of_mul_condVar_le`,
  `neg_log_le_mul_of_entSum_le`, the same as bounds `a V_T ≤ L_T ≤ b V_T`.
* `sub_sum_sub_le_mul_neg_log`, `div_le_neg_log_of_condVar_le`,
  `div_le_neg_log_of_condVar_le_bernVarSum`, `div_le_neg_log_of_condVar_le_of_pairRatio`
  (Corollary 4(i), (iii), with the two free ends of Lemma B of the survey) : `(V+)` or `(V+_B)`
  on `⌊δ / p⌋ ≤ |T|`, `N_T ≥ K + 1` gives `-log q ≥ (μ - C_δ - K (K + 1) / 2) / κ` with an explicit
  `C_δ`. The Kim–Wormald pair-ratio bound `U(A_s A_t) ≤ R p²` is the named hypothesis `hR`.
* `condVar_le_of_sum_abs_condCov_le`, `le_condVar_of_sum_abs_condCov_le`,
  `abs_condVar_sub_le_and_div_le` (Corollary 5) : the variance comparison that gives Theorem 7 of
  COD-196 through Theorem 3. The theorem through Theorem 3 is
  `div_le_neg_log_prob_avoid_of_reweight_harmonic` in `VMinus.lean`. Its `log n` form is
  `div_le_neg_log_prob_avoid` in `ChainRule.lean`, proved through Proposition 6.

From `v-plus-strategy-survey.md`:

* `condMean_sub_condMean_insert` (Lemma A) : `M_T - M_{T ∪ s} = f_s(T) (1 + Δ_s(T))`, with
  `Δ_s(T) = E[X'_s | Z_T ∩ A_s] - E[X'_s | Z_{T ∪ s}]` (`palmGap`).
* `sum_condProb_mul_one_add_palmGap`, `sum_condProb_le_neg_log`, `mul_le_neg_log_of_palmGap_le`,
  `condMean_le_of_exists_palmGap_le`, `sub_le_mul_neg_log_of_exists_palmGap_le`,
  `div_le_neg_log_of_exists_palmGap_le`, `exists_palmGap_le_of_condVar_le` (Lemma A and (H3)).
* `one_add_palmGap_le`, `condVar_le_card_mul`, `bernVarSum_le_condSlack`,
  `condVar_div_condSlack_le`, `sum_prob_sub_condMean_le`, `sum_prob_sub_condMean_le_of_pairRatio`
  (Lemma B).
-/

namespace Pairing

namespace ChainRule

open Finset

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

section Variance

/-- `X(ω) = #{t : ω ∈ A_t}`, the number of events that occur, as a real number. -/
noncomputable def eventCount (A : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ t, (A t).indicator (1 : Ω → ℝ) ω

/-- `V_T = Var(X | Z_T) = E[(X - M_T)² | Z_T]`, which is `0` when `U(Z_T) = 0`. `V_∅ = Var X`. -/
noncomputable def condVar (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  (∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2) / prob P (avoid A T)

/-- `B_T = ∑_{s ∉ T} f_s(T) (1 - f_s(T))`, the sum of the conditional Bernoulli variances. -/
noncomputable def bernVarSum (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  ∑ s ∈ Tᶜ, condProb P A T s * (1 - condProb P A T s)

/-- `∑_ω 1_S(ω) P(ω) 1_B(ω) = U(B ∩ S)`. -/
theorem sum_indicator_mul_indicator (P : Ω → ℝ) (S B : Set Ω) :
    ∑ ω, S.indicator P ω * B.indicator (1 : Ω → ℝ) ω = prob P (B ∩ S) := by
  rw [prob]
  refine sum_congr rfl fun ω _ ↦ ?_
  by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ B <;> simp [Set.indicator, h1, h2]

omit [Fintype Ω] in
/-- On `Z_T`, `X = X_{T^c} = ∑_{t ∉ T} 1_{A_t}`. -/
theorem eventCount_of_mem_avoid {T : Finset ι} {ω : Ω} (hω : ω ∈ avoid A T) :
    eventCount A ω = ∑ t ∈ Tᶜ, (A t).indicator (1 : Ω → ℝ) ω := by
  rw [eventCount, ← sum_add_sum_compl T,
    sum_eq_zero fun t ht ↦ Set.indicator_of_notMem (hω t ht) _, zero_add]

/-- `E[X 1_{Z_T}] = M_T U(Z_T)`. -/
theorem sum_avoid_mul_eventCount (hP : IsProb P) (T : Finset ι) :
    ∑ ω, (avoid A T).indicator P ω * eventCount A ω = condMean P A T * prob P (avoid A T) := by
  simp only [eventCount, mul_sum]
  rw [sum_comm, sum_congr rfl fun t _ ↦ by rw [sum_indicator_mul_indicator,
    ← condProb_mul_prob hP], condMean, sum_mul, ← sum_add_sum_compl T,
    sum_eq_zero fun t ht ↦ by rw [condProb_of_mem ht, zero_mul], zero_add]

omit [Fintype ι] [DecidableEq ι] in
/-- `E[(1_{A_s} - f_s(T)) (1_{A_t} - f_t(T)) 1_{Z_T}] = Cov_T(s, t) U(Z_T)`. -/
theorem sum_avoid_mul_centered (hP : IsProb P) (T : Finset ι) (s t : ι) :
    ∑ ω, (avoid A T).indicator P ω * (((A s).indicator (1 : Ω → ℝ) ω - condProb P A T s) *
      ((A t).indicator (1 : Ω → ℝ) ω - condProb P A T t)) =
      condCov P A T s t * prob P (avoid A T) := by
  have h1 : ∀ ω, (avoid A T).indicator P ω * (((A s).indicator (1 : Ω → ℝ) ω -
      condProb P A T s) * ((A t).indicator (1 : Ω → ℝ) ω - condProb P A T t)) =
      (A s ∩ A t ∩ avoid A T).indicator P ω -
        condProb P A T t * (A s ∩ avoid A T).indicator P ω -
        condProb P A T s * (A t ∩ avoid A T).indicator P ω +
        condProb P A T s * condProb P A T t * (avoid A T).indicator P ω := by
    intro ω
    by_cases h0 : ω ∈ avoid A T <;> by_cases hs : ω ∈ A s <;> by_cases ht : ω ∈ A t <;>
      simp [Set.indicator, h0, hs, ht] <;> ring
  have e1 := condPair_mul_prob hP (A := A) T s t
  have e2 := condProb_mul_prob hP (A := A) T s
  have e3 := condProb_mul_prob hP (A := A) T t
  simp only [h1, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp only [prob] at e1 e2 e3 ⊢
  rw [condCov]
  linear_combination -e1 + condProb P A T t * e2 + condProb P A T s * e3

omit [Fintype ι] [DecidableEq ι] in
/-- `Cov_T(s, s) = f_s(T) (1 - f_s(T))`. -/
theorem condCov_self (T : Finset ι) (s : ι) :
    condCov P A T s s = condProb P A T s * (1 - condProb P A T s) := by
  simp only [condCov, condPair, condProb, Set.inter_self]
  ring

/-- `V_T = ∑_{s, t ∉ T} Cov_T(s, t)`, the variance of `X_{T^c}` under `ν_T`. -/
theorem condVar_eq_sum_condCov (hP : IsProb P) (T : Finset ι) :
    condVar P A T = ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ, condCov P A T s t := by
  by_cases hz : prob P (avoid A T) = 0
  · have h : ∀ s t, condCov P A T s t = 0 := fun s t ↦ by
      simp [condCov, condPair, condProb, hz]
    simp [condVar, hz, h]
  have key : ∀ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 =
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ, (avoid A T).indicator P ω *
        (((A s).indicator (1 : Ω → ℝ) ω - condProb P A T s) *
          ((A t).indicator (1 : Ω → ℝ) ω - condProb P A T t)) := by
    intro ω
    by_cases h0 : ω ∈ avoid A T
    · rw [eventCount_of_mem_avoid h0, condMean, ← sum_sub_distrib, sq, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun s _ ↦ by rw [mul_sum]
    · simp [Set.indicator_of_notMem h0]
  rw [condVar, div_eq_iff hz, sum_congr rfl fun ω _ ↦ key ω, sum_comm, sum_mul]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [sum_comm, sum_mul]
  exact sum_congr rfl fun t _ ↦ sum_avoid_mul_centered hP T s t

/-- `V_T = B_T + ∑_{s ≠ t ∉ T} Cov_T(s, t)`. -/
theorem condVar_eq_bernVarSum_add (hP : IsProb P) (T : Finset ι) :
    condVar P A T = bernVarSum P A T + ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, condCov P A T s t := by
  rw [condVar_eq_sum_condCov hP, bernVarSum, ← sum_add_distrib]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [← add_sum_erase _ _ hs, condCov_self]

/-- `V_T ≥ 0`. -/
theorem condVar_nonneg (hP : IsProb P) (T : Finset ι) : 0 ≤ condVar P A T :=
  div_nonneg (sum_nonneg fun ω _ ↦ mul_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω)
    (sq_nonneg _)) (prob_nonneg hP _)

/-- `B_T ≥ 0`. -/
theorem bernVarSum_nonneg (hP : IsProb P) (T : Finset ι) : 0 ≤ bernVarSum P A T :=
  sum_nonneg fun s _ ↦ mul_nonneg (condProb_nonneg hP T s) (sub_nonneg.2 (condProb_le_one hP T s))

/-- `E[(X - M_T)² 1_{Z_T}] ≤ E[(X - a)² 1_{Z_T}]` for every `a`. -/
theorem sum_avoid_sq_le (hP : IsProb P) (T : Finset ι) (a : ℝ) :
    ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 ≤
      ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - a) ^ 2 := by
  have h0 := sum_avoid_mul_eventCount hP (A := A) T
  have hU : ∑ ω, (avoid A T).indicator P ω = prob P (avoid A T) := rfl
  have e : ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - a) ^ 2 -
      ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 =
      (condMean P A T - a) * (2 * ∑ ω, (avoid A T).indicator P ω * eventCount A ω -
        (condMean P A T + a) * ∑ ω, (avoid A T).indicator P ω) := by
    rw [← sum_sub_distrib, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun ω _ ↦ by ring
  rw [h0, hU] at e
  have e2 : (condMean P A T - a) * (2 * (condMean P A T * prob P (avoid A T)) -
      (condMean P A T + a) * prob P (avoid A T)) =
      (condMean P A T - a) ^ 2 * prob P (avoid A T) := by ring
  linarith [mul_nonneg (sq_nonneg (condMean P A T - a)) (prob_nonneg hP (avoid A T))]

/-- `V_T U(Z_T) ≤ Var X`. -/
theorem condVar_mul_prob_le (hP : IsProb P) (T : Finset ι) :
    condVar P A T * prob P (avoid A T) ≤ condVar P A ∅ := by
  by_cases hz : prob P (avoid A T) = 0
  · rw [hz, mul_zero]
    exact condVar_nonneg hP ∅
  rw [condVar, div_mul_cancel₀ _ hz, condVar, avoid_empty, prob_univ hP, div_one]
  refine (sum_avoid_sq_le hP T (condMean P A ∅)).trans (sum_le_sum fun ω _ ↦ ?_)
  by_cases h : ω ∈ avoid A T
  · simp [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, zero_mul, Set.indicator_of_mem (Set.mem_univ ω)]
    exact mul_nonneg (hP.nonneg ω) (sq_nonneg _)

/-- Lemma B(i) of the (V+) survey (`v-plus-strategy-survey.md`), by Cauchy–Schwarz:
`V_T ≤ N_T B_T`. -/
theorem condVar_le_card_mul (hP : IsProb P) (T : Finset ι) :
    condVar P A T ≤ Tᶜ.card * bernVarSum P A T := by
  by_cases hz : prob P (avoid A T) = 0
  · rw [condVar, hz, div_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (bernVarSum_nonneg hP T)
  have hU : 0 < prob P (avoid A T) := lt_of_le_of_ne (prob_nonneg hP _) (Ne.symm hz)
  rw [condVar, div_le_iff₀ hU]
  calc ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 ≤
        ∑ ω, (avoid A T).indicator P ω * (Tᶜ.card *
          ∑ s ∈ Tᶜ, ((A s).indicator (1 : Ω → ℝ) ω - condProb P A T s) ^ 2) := by
        refine sum_le_sum fun ω _ ↦ ?_
        by_cases h0 : ω ∈ avoid A T
        · rw [eventCount_of_mem_avoid h0, condMean, ← sum_sub_distrib]
          exact mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq
            (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω)
        · simp [Set.indicator_of_notMem h0]
    _ = Tᶜ.card * ∑ s ∈ Tᶜ, ∑ ω, (avoid A T).indicator P ω *
          (((A s).indicator (1 : Ω → ℝ) ω - condProb P A T s) *
            ((A s).indicator (1 : Ω → ℝ) ω - condProb P A T s)) := by
        simp only [mul_sum, sq]
        rw [sum_comm]
        exact sum_congr rfl fun s _ ↦ sum_congr rfl fun ω _ ↦ by ring
    _ = Tᶜ.card * bernVarSum P A T * prob P (avoid A T) := by
        rw [bernVarSum, mul_assoc, sum_mul]
        congr 1
        exact sum_congr rfl fun s _ ↦ by rw [sum_avoid_mul_centered hP, condCov_self]

end Variance

section Kernel

/-- `E[∑_{j < k} G(T_j, s_{j+1}) | T_0 = T]` for the Markov chain on the subsets of `ι` that moves
from `T` to `T ∪ {s}`, `s ∉ T`, with probability `w(T, s)`, run for `k` steps. It is the first-step
recursion `E_{k+1}(T) = ∑_{s ∉ T} w(T, s) (G(T, s) + E_k(T ∪ s))`, `E_0 = 0`. -/
noncomputable def kerExp (w G : Finset ι → ι → ℝ) : ℕ → Finset ι → ℝ
  | 0, _ => 0
  | k + 1, T => ∑ s ∈ Tᶜ, w T s * (G T s + kerExp w G k (insert s T))

/-- Two rewards with the same one-step conditional expectations have the same expected sum. -/
theorem kerExp_congr {w G H : Finset ι → ι → ℝ}
    (h : ∀ T : Finset ι, ∑ s ∈ Tᶜ, w T s * G T s = ∑ s ∈ Tᶜ, w T s * H T s) (k : ℕ)
    (T : Finset ι) : kerExp w G k T = kerExp w H k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    simp only [kerExp, mul_add, sum_add_distrib, h T, ih]

/-- If the step law has total mass `1` at every `T ≠ ι`, and `∑_{s ∉ T} w(T, s) G(T, s) = c(T)`,
then the reward `G` may be replaced by its conditional expectation `c`. -/
theorem kerExp_eq_of_sum {w G : Finset ι → ι → ℝ} {c : Finset ι → ℝ}
    (hw : ∀ T : Finset ι, T ≠ univ → ∑ s ∈ Tᶜ, w T s = 1)
    (hG : ∀ T : Finset ι, T ≠ univ → ∑ s ∈ Tᶜ, w T s * G T s = c T) (k : ℕ) (T : Finset ι) :
    kerExp w G k T = kerExp w (fun T _ ↦ c T) k T := by
  refine kerExp_congr (fun T ↦ ?_) k T
  by_cases hT : T = univ
  · simp [hT]
  · rw [hG T hT, ← sum_mul, hw T hT, one_mul]

/-- The telescoping sum along the chain:
`E[∑_k (F(T_{k-1}) - F(T_k)) | T_0 = T] = F(T) - F(ι)` for `k = N_T` steps. -/
theorem kerExp_sub {w : Finset ι → ι → ℝ} (hw : ∀ T : Finset ι, T ≠ univ → ∑ s ∈ Tᶜ, w T s = 1)
    (F : Finset ι → ℝ) (k : ℕ) (T : Finset ι) (hk : Tᶜ.card = k) :
    kerExp w (fun T s ↦ F T - F (insert s T)) k T = F T - F univ := by
  induction k generalizing T with
  | zero =>
    rw [card_eq_zero, compl_eq_empty_iff] at hk
    simp [kerExp, hk]
  | succ k ih =>
    have hT : T ≠ univ := fun h ↦ by simp [h] at hk
    rw [kerExp]
    rw [sum_congr rfl fun s hs ↦ by
      rw [ih (insert s T) (by rw [compl_insert, card_erase_of_mem hs, hk]; rfl)]]
    rw [sum_congr rfl fun s _ ↦ show w T s * (F T - F (insert s T) + (F (insert s T) - F univ)) =
      w T s * (F T - F univ) by ring, ← sum_mul, hw T hT, one_mul]

/-- The chain meets each level once: `E[∑_k h(|T_{k-1}|) | T_0 = T] = ∑_{j < k} h(|T| + j)` for
`k = N_T` steps. -/
theorem kerExp_card {w : Finset ι → ι → ℝ} (hw : ∀ T : Finset ι, T ≠ univ → ∑ s ∈ Tᶜ, w T s = 1)
    (h : ℕ → ℝ) (k : ℕ) (T : Finset ι) (hk : Tᶜ.card = k) :
    kerExp w (fun T _ ↦ h T.card) k T = ∑ j ∈ range k, h (T.card + j) := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    have hT : T ≠ univ := fun h ↦ by simp [h] at hk
    rw [kerExp]
    rw [sum_congr rfl fun s hs ↦ by
      rw [ih (insert s T) (by rw [compl_insert, card_erase_of_mem hs, hk]; rfl),
        card_insert_of_notMem (mem_compl.mp hs)]]
    rw [← sum_mul, hw T hT, one_mul, sum_range_succ', add_zero, add_comm]
    exact congrArg₂ _ (sum_congr rfl fun j _ ↦ by rw [add_assoc, add_comm 1 j]) rfl

/-- `E[∑_k (G + H)] = E[∑_k G] + E[∑_k H]`. -/
theorem kerExp_add (w G H : Finset ι → ι → ℝ) (k : ℕ) (T : Finset ι) :
    kerExp w (fun T s ↦ G T s + H T s) k T = kerExp w G k T + kerExp w H k T := by
  induction k generalizing T with
  | zero => simp [kerExp]
  | succ k ih =>
    simp only [kerExp, ih, ← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by ring

/-- `E[∑_k a G] = a E[∑_k G]`. -/
theorem kerExp_const_mul (w G : Finset ι → ι → ℝ) (a : ℝ) (k : ℕ) (T : Finset ι) :
    kerExp w (fun T s ↦ a * G T s) k T = a * kerExp w G k T := by
  induction k generalizing T with
  | zero => simp [kerExp]
  | succ k ih =>
    simp only [kerExp, ih, mul_sum]
    exact sum_congr rfl fun s _ ↦ by ring

/-- `E[∑_k G]` is monotone in `G` on the pairs `s ∉ T` when `w ≥ 0`. -/
theorem kerExp_mono {w G H : Finset ι → ι → ℝ} (hw : ∀ T s, s ∉ T → 0 ≤ w T s)
    (h : ∀ T s, s ∉ T → G T s ≤ H T s) (k : ℕ) (T : Finset ι) :
    kerExp w G k T ≤ kerExp w H k T := by
  induction k generalizing T with
  | zero => exact le_rfl
  | succ k ih =>
    refine sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left
      (add_le_add (h T s (mem_compl.mp hs)) (ih _)) (hw T s (mem_compl.mp hs))

/-- `E[∑_k G] ≥ 0` for `G ≥ 0` on the pairs `s ∉ T` when `w ≥ 0`. -/
theorem kerExp_nonneg {w G : Finset ι → ι → ℝ} (hw : ∀ T s, s ∉ T → 0 ≤ w T s)
    (h : ∀ T s, s ∉ T → 0 ≤ G T s) (k : ℕ) (T : Finset ι) : 0 ≤ kerExp w G k T := by
  have h0 : kerExp w (fun _ _ ↦ (0 : ℝ)) k T = 0 := by
    simpa using kerExp_const_mul w (fun _ _ ↦ (0 : ℝ)) 0 k T
  exact h0 ▸ kerExp_mono hw h k T

omit [DecidableEq ι] in
/-- `E_{|T| = i} (F + H) = E_{|T| = i} F + E_{|T| = i} H`. -/
theorem levelAvg_add (F H : Finset ι → ℝ) (i : ℕ) :
    levelAvg (fun T ↦ F T + H T) i = levelAvg F i + levelAvg H i := by
  simp only [levelAvg, sum_add_distrib, add_div]

omit [DecidableEq ι] in
/-- `E_{|T| = i} (F - H) = E_{|T| = i} F - E_{|T| = i} H`. -/
theorem levelAvg_sub (F H : Finset ι → ℝ) (i : ℕ) :
    levelAvg (fun T ↦ F T - H T) i = levelAvg F i - levelAvg H i := by
  simp only [levelAvg, sum_sub_distrib, sub_div]

/-- For `i < n`, `E_{|T| = i} (1 / N_T) ∑_{s ∉ T} F(T ∪ s) = E_{|T| = i + 1} F`: a uniform `i`-set
with a uniform point outside it added is a uniform `(i + 1)`-set. -/
theorem levelAvg_outAvg_insert (F : Finset ι → ℝ) {i : ℕ} (hi : i < Fintype.card ι) :
    levelAvg (fun T ↦ (∑ s ∈ Tᶜ, F (insert s T)) / Tᶜ.card) i = levelAvg F (i + 1) := by
  have h := levelAvg_succ_sub F hi
  have e : levelAvg (fun T ↦ (∑ s ∈ Tᶜ, (F (insert s T) - F T)) / Tᶜ.card) i =
      levelAvg (fun T ↦ (∑ s ∈ Tᶜ, F (insert s T)) / Tᶜ.card - F T) i :=
    levelAvg_congr fun T hT ↦ by
      have hN : (Tᶜ.card : ℝ) ≠ 0 := by
        have : 0 < Tᶜ.card := by
          rw [card_compl, hT]
          omega
        exact_mod_cast this.ne'
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hN]
  rw [e, levelAvg_sub] at h
  linarith

/-- With the uniform step law `w_T(s) = 1 / N_T`, the chain is a uniformly random ordering, and
`kerExp` is `chainAvg`, the average of `∑_k G(T_k, π_k)` over all `n!` orderings
(`chainAvg_eq_sum_equiv`). -/
theorem kerExp_uniform (G : Finset ι → ι → ℝ) :
    kerExp (fun T _ ↦ 1 / (Tᶜ.card : ℝ)) G (Fintype.card ι) ∅ = chainAvg G := by
  have key : ∀ k i, i + k = Fintype.card ι →
      levelAvg (fun T ↦ kerExp (fun T _ ↦ 1 / (Tᶜ.card : ℝ)) G k T) i =
        ∑ j ∈ range k, levelAvg (outAvg G) (i + j) := by
    intro k
    induction k with
    | zero => exact fun i _ ↦ by simp [kerExp, levelAvg]
    | succ k ih =>
      intro i hik
      have e : ∀ T : Finset ι, kerExp (fun T _ ↦ 1 / (Tᶜ.card : ℝ)) G (k + 1) T =
          outAvg G T + (∑ s ∈ Tᶜ, kerExp (fun T _ ↦ 1 / (Tᶜ.card : ℝ)) G k (insert s T)) /
            Tᶜ.card := by
        intro T
        rw [kerExp, outAvg, ← add_div, ← sum_add_distrib, sum_div]
        exact sum_congr rfl fun s _ ↦ by ring
      simp only [e]
      rw [levelAvg_add, levelAvg_outAvg_insert
        (fun T ↦ kerExp (fun T _ ↦ 1 / (Tᶜ.card : ℝ)) G k T) (i := i) (by omega),
        ih (i + 1) (by omega), sum_range_succ', add_zero]
      have e2 : ∑ j ∈ range k, levelAvg (outAvg G) (i + 1 + j) =
          ∑ j ∈ range k, levelAvg (outAvg G) (i + (j + 1)) :=
        sum_congr rfl fun j _ ↦ by rw [add_assoc, add_comm 1 j]
      rw [e2]
      ring
  have h := key (Fintype.card ι) 0 (zero_add _)
  simp only [levelAvg_zero, zero_add] at h
  rw [h, chainAvg]

end Kernel

section Theorem3

/-- `D_T = ∑_{s ∉ T} (1 - f_s(T))`, which is `N_T - M_T` (`condSlack_eq`). -/
noncomputable def condSlack (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  ∑ s ∈ Tᶜ, (1 - condProb P A T s)

/-- `L_T = ∑_{s ∉ T} ψ(f_s(T))`, with `ψ(f) = -(1 - f) log(1 - f)`. -/
noncomputable def entSum (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) : ℝ :=
  ∑ s ∈ Tᶜ, -(1 - condProb P A T s) * Real.log (1 - condProb P A T s)

/-- The step law of Theorem 3 of COD-198 (`cod-198-attempt.md`): from `T`, add `s ∉ T` with
probability `w_T(s) = (1 - f_s(T)) / D_T`. -/
noncomputable def reweight (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s : ι) : ℝ :=
  (1 - condProb P A T s) / condSlack P A T

/-- `D_T = N_T - M_T`. -/
theorem condSlack_eq (T : Finset ι) : condSlack P A T = Tᶜ.card - condMean P A T := by
  rw [condSlack, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, condMean]

/-- `D_T ≥ 0`. -/
theorem condSlack_nonneg (hP : IsProb P) (T : Finset ι) : 0 ≤ condSlack P A T :=
  sum_nonneg fun s _ ↦ sub_nonneg.2 (condProb_le_one hP T s)

/-- If `q > 0`, then `D_T > 0` for `T ≠ ι`. -/
theorem condSlack_pos (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {T : Finset ι}
    (hT : T ≠ univ) : 0 < condSlack P A T :=
  sum_pos (fun s _ ↦ sub_pos.2 (condProb_lt_one hP hq T s))
    (by rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]; exact hT)

/-- `w_T(s) ≥ 0`. -/
theorem reweight_nonneg (hP : IsProb P) (T : Finset ι) (s : ι) : 0 ≤ reweight P A T s :=
  div_nonneg (sub_nonneg.2 (condProb_le_one hP T s)) (condSlack_nonneg hP T)

/-- If `q > 0`, then `w_T` is a probability on `ι ∖ T` for every `T ≠ ι`. -/
theorem sum_reweight (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {T : Finset ι}
    (hT : T ≠ univ) : ∑ s ∈ Tᶜ, reweight P A T s = 1 := by
  simp only [reweight, ← sum_div]
  exact div_self (condSlack_pos hP hq hT).ne'

/-- `M_∅ = μ`. -/
theorem condMean_empty (hP : IsProb P) : condMean P A ∅ = ∑ t, prob P (A t) := by
  rw [condMean, compl_empty]
  exact sum_congr rfl fun t _ ↦ condProb_empty hP t

/-- `M_ι = 0`. -/
theorem condMean_univ : condMean P A univ = 0 := by
  rw [condMean, compl_univ, sum_empty]

/-- Theorem 3(a) of COD-198 (`cod-198-attempt.md`), proof: for `s ∉ T`,
`(1 - f_s(T)) (M_T - M_{T ∪ s}) = f_s(T) (1 - f_s(T)) + R_T(s)`, with no hypothesis on `f_s`. -/
theorem one_sub_condProb_mul_condMean_sub (hP : IsProb P) {T : Finset ι} {s : ι} (hsT : s ∉ T) :
    (1 - condProb P A T s) * (condMean P A T - condMean P A (insert s T)) =
      condProb P A T s * (1 - condProb P A T s) + covSum P A T s := by
  have h1 : (1 - condProb P A T s) * condMean P A (insert s T) =
      ∑ t ∈ (insert s T)ᶜ, (condProb P A T t - condPair P A T s t) := by
    rw [condMean, mul_sum]
    exact sum_congr rfl fun t _ ↦ by rw [mul_comm, condProb_insert_mul hP, condPair_comm]
  have h2 : condMean P A T = condProb P A T s + ∑ t ∈ (insert s T)ᶜ, condProb P A T t := by
    rw [condMean, compl_insert, add_sum_erase _ _ (mem_compl.mpr hsT)]
  have h3 : ∑ t ∈ (insert s T)ᶜ, ((1 - condProb P A T s) * condProb P A T t -
      (condProb P A T t - condPair P A T s t)) = covSum P A T s :=
    sum_congr rfl fun t _ ↦ by rw [condCov]; ring
  rw [sum_sub_distrib, ← mul_sum] at h3
  rw [mul_sub, h1, h2]
  linear_combination h3

/-- Theorem 3(a) of COD-198 (`cod-198-attempt.md`), the one-step drift
`E_w[M_{T ∪ s} | T] = M_T - V_T / D_T`, in the form
`∑_{s ∉ T} w_T(s) (M_T - M_{T ∪ s}) = V_T / D_T`. -/
theorem sum_reweight_mul_condMean_sub (hP : IsProb P) (T : Finset ι) :
    ∑ s ∈ Tᶜ, reweight P A T s * (condMean P A T - condMean P A (insert s T)) =
      condVar P A T / condSlack P A T := by
  rw [condVar_eq_bernVarSum_add hP, bernVarSum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [reweight, div_mul_eq_mul_div, one_sub_condProb_mul_condMean_sub hP (mem_compl.mp hs),
    covSum, compl_insert]

/-- Theorem 3(a) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then along the `(1 - f)`-weighted
ordering, `E_w ∑_{k=1}^n V_{T_{k-1}} / D_{T_{k-1}} = μ`. -/
theorem kerExp_reweight_condVar (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    kerExp (reweight P A) (fun T _ ↦ condVar P A T / condSlack P A T) (Fintype.card ι) ∅ =
      ∑ t, prob P (A t) := by
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  have h1 := kerExp_eq_of_sum hw
    (G := fun T s ↦ condMean P A T - condMean P A (insert s T))
    (c := fun T ↦ condVar P A T / condSlack P A T)
    (fun T _ ↦ sum_reweight_mul_condMean_sub hP T) (Fintype.card ι) ∅
  rw [← h1, kerExp_sub hw _ _ _ (by rw [compl_empty, card_univ]), condMean_univ, sub_zero,
    condMean_empty hP]

/-- `∑_{s ∉ T} w_T(s) (-log(1 - f_s(T))) = L_T / D_T`. -/
theorem sum_reweight_mul_neg_log (T : Finset ι) :
    ∑ s ∈ Tᶜ, reweight P A T s * -Real.log (1 - condProb P A T s) =
      entSum P A T / condSlack P A T := by
  rw [entSum, sum_div]
  exact sum_congr rfl fun s _ ↦ by rw [reweight]; ring

/-- Theorem 3(b) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then along the `(1 - f)`-weighted
ordering, `E_w ∑_{k=1}^n L_{T_{k-1}} / D_{T_{k-1}} = -log q`. -/
theorem kerExp_reweight_entSum (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    kerExp (reweight P A) (fun T _ ↦ entSum P A T / condSlack P A T) (Fintype.card ι) ∅ =
      -Real.log (prob P (avoid A univ)) := by
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  have h1 := kerExp_eq_of_sum hw
    (G := fun T s ↦ Real.log (prob P (avoid A T)) - Real.log (prob P (avoid A (insert s T))))
    (c := fun T ↦ entSum P A T / condSlack P A T)
    (fun T _ ↦ by
      rw [← sum_reweight_mul_neg_log]
      refine sum_congr rfl fun s _ ↦ ?_
      have := neg_log_avoid_insert hP hq T s
      congr 1
      linarith) (Fintype.card ι) ∅
  rw [← h1, kerExp_sub hw _ _ _ (by rw [compl_empty, card_univ]), avoid_empty, prob_univ hP,
    Real.log_one, zero_sub]

/-- `f (1 - f) ≤ -(1 - f) log(1 - f)` for `0 ≤ f ≤ 1`. -/
theorem mul_one_sub_le_neg_mul_log {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    f * (1 - f) ≤ -(1 - f) * Real.log (1 - f) := by
  rcases h1.lt_or_eq with h1 | rfl
  · have hx : 0 < 1 - f := by linarith
    have h := Real.log_le_sub_one_of_pos hx
    nlinarith [mul_le_mul_of_nonneg_left h hx.le]
  · simp

/-- `-(1 - f) log(1 - f) ≤ f` for `0 ≤ f ≤ 1`. -/
theorem neg_mul_log_le {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    -(1 - f) * Real.log (1 - f) ≤ f := by
  rcases h1.lt_or_eq with h1 | rfl
  · have hx : 0 < 1 - f := by linarith
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at h
    have e : (1 - f) * ((1 - f)⁻¹ - 1) = f := by
      rw [mul_sub, mul_inv_cancel₀ hx.ne', mul_one]
      ring
    nlinarith [mul_le_mul_of_nonneg_left h hx.le]
  · simp

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`), proof: `B_T ≤ L_T`. -/
theorem bernVarSum_le_entSum (hP : IsProb P) (T : Finset ι) : bernVarSum P A T ≤ entSum P A T :=
  sum_le_sum fun s _ ↦ mul_one_sub_le_neg_mul_log (condProb_nonneg hP T s)
    (condProb_le_one hP T s)

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`), proof: `L_T ≤ M_T`. -/
theorem entSum_le_condMean (hP : IsProb P) (T : Finset ι) : entSum P A T ≤ condMean P A T :=
  sum_le_sum fun s _ ↦ neg_mul_log_le (condProb_nonneg hP T s) (condProb_le_one hP T s)

/-- `L_T ≥ 0`. -/
theorem entSum_nonneg (hP : IsProb P) (T : Finset ι) : 0 ≤ entSum P A T :=
  (bernVarSum_nonneg hP T).trans (bernVarSum_le_entSum hP T)

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then
`E_w ∑_k B_{T_{k-1}} / D_{T_{k-1}} ≤ -log q`. -/
theorem kerExp_bernVarSum_le_neg_log (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    kerExp (reweight P A) (fun T _ ↦ bernVarSum P A T / condSlack P A T) (Fintype.card ι) ∅ ≤
      -Real.log (prob P (avoid A univ)) := by
  rw [← kerExp_reweight_entSum hP hq]
  exact kerExp_mono (fun T s _ ↦ reweight_nonneg hP T s) (fun T _ _ ↦
    div_le_div_of_nonneg_right (bernVarSum_le_entSum hP T) (condSlack_nonneg hP T)) _ _

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then
`-log q ≤ E_w ∑_k M_{T_{k-1}} / D_{T_{k-1}}`. -/
theorem neg_log_le_kerExp_condMean (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    -Real.log (prob P (avoid A univ)) ≤
      kerExp (reweight P A) (fun T _ ↦ condMean P A T / condSlack P A T) (Fintype.card ι) ∅ := by
  rw [← kerExp_reweight_entSum hP hq]
  exact kerExp_mono (fun T s _ ↦ reweight_nonneg hP T s) (fun T _ _ ↦
    div_le_div_of_nonneg_right (entSum_le_condMean hP T) (condSlack_nonneg hP T)) _ _

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then
`E_w ∑_k f_k = E_w ∑_k B_{T_{k-1}} / D_{T_{k-1}}`, with `f_k = f_{s_k}(T_{k-1})`. -/
theorem kerExp_reweight_condProb (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    kerExp (reweight P A) (fun T s ↦ condProb P A T s) (Fintype.card ι) ∅ =
      kerExp (reweight P A) (fun T _ ↦ bernVarSum P A T / condSlack P A T) (Fintype.card ι) ∅ :=
  kerExp_eq_of_sum (fun T hT ↦ sum_reweight hP hq hT) (fun T _ ↦ by
    rw [bernVarSum, sum_div]
    exact sum_congr rfl fun s _ ↦ by rw [reweight]; ring) _ _

/-- Theorem 3(c) of COD-198 (`cod-198-attempt.md`): if `q > 0`, then
`E_w ∑_k f_k / (1 - f_k) = E_w ∑_k M_{T_{k-1}} / D_{T_{k-1}}`. -/
theorem kerExp_reweight_condProb_div (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) :
    kerExp (reweight P A) (fun T s ↦ condProb P A T s / (1 - condProb P A T s))
        (Fintype.card ι) ∅ =
      kerExp (reweight P A) (fun T _ ↦ condMean P A T / condSlack P A T) (Fintype.card ι) ∅ :=
  kerExp_eq_of_sum (fun T hT ↦ sum_reweight hP hq hT) (fun T _ ↦ by
    rw [condMean, sum_div]
    refine sum_congr rfl fun s _ ↦ ?_
    have h := (sub_pos.2 (condProb_lt_one hP hq T s)).ne'
    rw [reweight, div_mul_div_comm, mul_comm (1 - condProb P A T s), mul_div_mul_right _ _ h]) _ _

/-- Theorem 3(d) of COD-198 (`cod-198-attempt.md`), lower half: if `q > 0` and `a V_T ≤ L_T` for
every `T ≠ ι`, then `a μ ≤ -log q`. With `a = min_T L_T / V_T` over the `T` with `V_T > 0` this is
`μ min_T (L_T / V_T) ≤ -log q`. -/
theorem mul_le_neg_log_of_mul_condVar_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {a : ℝ}
    (h : ∀ T : Finset ι, T ≠ univ → a * condVar P A T ≤ entSum P A T) :
    a * ∑ t, prob P (A t) ≤ -Real.log (prob P (avoid A univ)) := by
  rw [← kerExp_reweight_condVar hP hq, ← kerExp_reweight_entSum hP hq, ← kerExp_const_mul]
  refine kerExp_mono (fun T s _ ↦ reweight_nonneg hP T s) (fun T s hs ↦ ?_) _ _
  show a * (condVar P A T / condSlack P A T) ≤ entSum P A T / condSlack P A T
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h T fun hT ↦ hs (hT ▸ mem_univ s)) (condSlack_nonneg hP T)

/-- Theorem 3(d) of COD-198 (`cod-198-attempt.md`), upper half: if `q > 0` and `L_T ≤ b V_T` for
every `T ≠ ι`, then `-log q ≤ b μ`. With `b = max_T L_T / V_T` this is
`-log q ≤ μ max_T (L_T / V_T)`. The hypothesis fails when `V_T = 0 < L_T`, where the paper reads
`L_T / V_T = +∞`. -/
theorem neg_log_le_mul_of_entSum_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {b : ℝ}
    (h : ∀ T : Finset ι, T ≠ univ → entSum P A T ≤ b * condVar P A T) :
    -Real.log (prob P (avoid A univ)) ≤ b * ∑ t, prob P (A t) := by
  rw [← kerExp_reweight_condVar hP hq, ← kerExp_reweight_entSum hP hq, ← kerExp_const_mul]
  refine kerExp_mono (fun T s _ ↦ reweight_nonneg hP T s) (fun T s hs ↦ ?_) _ _
  show entSum P A T / condSlack P A T ≤ b * (condVar P A T / condSlack P A T)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h T fun hT ↦ hs (hT ▸ mem_univ s)) (condSlack_nonneg hP T)

/-- Theorem 3(d) of COD-198 (`cod-198-attempt.md`), lower half, as stated: if `q > 0`, then
`μ min_T (L_T / V_T) ≤ -log q`, with the minimum over the `T ≠ ι` with `V_T > 0`, assumed to
exist. -/
theorem inf'_mul_le_neg_log (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    (hS : ((univ : Finset (Finset ι)).filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T).Nonempty) :
    ((univ.filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T).inf' hS
      fun T ↦ entSum P A T / condVar P A T) * ∑ t, prob P (A t) ≤
        -Real.log (prob P (avoid A univ)) := by
  refine mul_le_neg_log_of_mul_condVar_le hP hq fun T hT ↦ ?_
  rcases (condVar_nonneg hP (A := A) T).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact entSum_nonneg hP T
  · have hmem : T ∈ (univ : Finset (Finset ι)).filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T :=
      mem_filter.mpr ⟨mem_univ _, hT, h⟩
    have := inf'_le (fun T ↦ entSum P A T / condVar P A T) hmem
    rwa [le_div_iff₀ h] at this

/-- Theorem 3(d) of COD-198 (`cod-198-attempt.md`), upper half, as stated: if `q > 0`, then
`-log q ≤ μ max_T (L_T / V_T)`, with the maximum over the `T ≠ ι` with `V_T > 0`, assumed to exist.
The paper reads `L_T / V_T = +∞` when `V_T = 0 < L_T`, which makes the bound vacuous, so here
`L_T = 0` is assumed wherever `V_T = 0`. -/
theorem neg_log_le_sup'_mul (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    (hS : ((univ : Finset (Finset ι)).filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T).Nonempty)
    (h0 : ∀ T : Finset ι, T ≠ univ → condVar P A T = 0 → entSum P A T = 0) :
    -Real.log (prob P (avoid A univ)) ≤
      ((univ.filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T).sup' hS
        fun T ↦ entSum P A T / condVar P A T) * ∑ t, prob P (A t) := by
  refine neg_log_le_mul_of_entSum_le hP hq fun T hT ↦ ?_
  rcases (condVar_nonneg hP (A := A) T).eq_or_lt with h | h
  · rw [← h, mul_zero, h0 T hT h.symm]
  · have hmem : T ∈ (univ : Finset (Finset ι)).filter fun T ↦ T ≠ univ ∧ 0 < condVar P A T :=
      mem_filter.mpr ⟨mem_univ _, hT, h⟩
    have := le_sup' (fun T ↦ entSum P A T / condVar P A T) hmem
    rwa [div_le_iff₀ h] at this

end Theorem3

section LemmaAB

/-- `U(A_t | Z_T ∩ A_s)`, which is `0` when `U(Z_T ∩ A_s) = 0`. -/
noncomputable def palmProb (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s t : ι) : ℝ :=
  prob P (A s ∩ A t ∩ avoid A T) / prob P (A s ∩ avoid A T)

/-- `Δ_s(T) = E[X'_s | Z_T ∩ A_s] - E[X'_s | Z_{T ∪ s}]`, with `X'_s = X - 1_{A_s}`, from Section 4
of the (V+) survey (`v-plus-strategy-survey.md`). On `Z_T ∩ A_s` and on `Z_{T ∪ s}`,
`X'_s = ∑_{t ∉ T ∪ s} 1_{A_t}`, so `Δ_s(T) = ∑_{t ∉ T ∪ s} U(A_t | Z_T ∩ A_s) - M_{T ∪ s}`. -/
noncomputable def palmGap (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (s : ι) : ℝ :=
  ∑ t ∈ (insert s T)ᶜ, palmProb P A T s t - condMean P A (insert s T)

omit [Fintype ι] [DecidableEq ι] in
/-- `f_s(T) U(A_t | Z_T ∩ A_s) = U(A_s A_t | Z_T)`, also when `U(Z_T ∩ A_s) = 0`. -/
theorem condProb_mul_palmProb (hP : IsProb P) (T : Finset ι) (s t : ι) :
    condProb P A T s * palmProb P A T s t = condPair P A T s t := by
  by_cases h : prob P (A s ∩ avoid A T) = 0
  · have h' : prob P (A s ∩ A t ∩ avoid A T) = 0 :=
      prob_eq_zero_of_subset hP (Set.inter_subset_inter_left _ Set.inter_subset_left) h
    simp [palmProb, condPair, h, h']
  · rw [condProb, palmProb, condPair, div_mul_div_comm, mul_comm (prob P (A s ∩ avoid A T)),
      mul_div_mul_right _ _ h]

omit [Fintype ι] [DecidableEq ι] in
/-- `U(A_t | Z_T ∩ A_s) ≤ 1`. -/
theorem palmProb_le_one (hP : IsProb P) (T : Finset ι) (s t : ι) : palmProb P A T s t ≤ 1 :=
  div_le_one_of_le₀ (prob_mono hP (Set.inter_subset_inter_left _ Set.inter_subset_left))
    (prob_nonneg hP _)

/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`): for `s ∉ T`,
`M_T - M_{T ∪ s} = f_s(T) (1 + Δ_s(T))`, with no hypothesis on `f_s(T)`. -/
theorem condMean_sub_condMean_insert (hP : IsProb P) {T : Finset ι} {s : ι} (hsT : s ∉ T) :
    condMean P A T - condMean P A (insert s T) = condProb P A T s * (1 + palmGap P A T s) := by
  have h2 : condMean P A T = condProb P A T s + ∑ t ∈ (insert s T)ᶜ, condProb P A T t := by
    rw [condMean, compl_insert, add_sum_erase _ _ (mem_compl.mpr hsT)]
  have h3 : ∀ t, condProb P A T t = condProb P A T s * palmProb P A T s t +
      condProb P A (insert s T) t * (1 - condProb P A T s) := fun t ↦ by
    rw [condProb_insert_mul hP, condProb_mul_palmProb hP, condPair_comm]
    ring
  have hM : ∑ t ∈ (insert s T)ᶜ, condProb P A (insert s T) t = condMean P A (insert s T) := rfl
  rw [h2, sum_congr rfl fun t _ ↦ h3 t, sum_add_distrib, ← mul_sum, ← sum_mul, hM, palmGap]
  ring

/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`): along every ordering `σ`,
`μ = ∑_k f_k (1 + Δ_k)`, with `f_k = f_{σ k}(T_k)` and `Δ_k = Δ_{σ k}(T_k)`. -/
theorem sum_condProb_mul_one_add_palmGap (hP : IsProb P) {n : ℕ} (σ : Fin n ≃ ι) :
    ∑ k : Fin n, condProb P A (pre σ k) (σ k) * (1 + palmGap P A (pre σ k) (σ k)) =
      ∑ t, prob P (A t) := by
  have h := sum_range_sub' (fun k ↦ condMean P A (pre σ k)) n
  rw [pre_zero, pre_eq_univ, condMean_univ, sub_zero, condMean_empty hP] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [pre_succ σ k.isLt, condMean_sub_condMean_insert hP (notMem_pre σ le_rfl)]

omit [DecidableEq ι] in
/-- The chain rule in log form along an ordering `σ`: if `q > 0`, then
`-log q = ∑_k -log(1 - f_k)`. -/
theorem neg_log_prob_avoid_eq_sum (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {n : ℕ}
    (σ : Fin n ≃ ι) :
    -Real.log (prob P (avoid A univ)) =
      ∑ k : Fin n, -Real.log (1 - condProb P A (pre σ k) (σ k)) := by
  rw [prob_avoid_univ hP σ,
    Real.log_prod fun k _ ↦ (sub_pos.2 (condProb_lt_one hP hq _ _)).ne', ← sum_neg_distrib]

omit [DecidableEq ι] in
/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`): if `q > 0`, then
`-log q ≥ ∑_k f_k` along every ordering `σ`. -/
theorem sum_condProb_le_neg_log (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {n : ℕ}
    (σ : Fin n ≃ ι) :
    ∑ k : Fin n, condProb P A (pre σ k) (σ k) ≤ -Real.log (prob P (avoid A univ)) := by
  rw [neg_log_prob_avoid_eq_sum hP hq σ]
  refine sum_le_sum fun k _ ↦ ?_
  linarith [Real.log_le_sub_one_of_pos (sub_pos.2 (condProb_lt_one hP hq (A := A) (pre σ k) (σ k)))]

/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`): if `q > 0`, `κ ≥ 0`, and
`Δ_k ≤ κ - 1` at every step of an ordering `σ`, then `μ ≤ κ (-log q)`, that is
`-log q ≥ μ / κ`. -/
theorem mul_le_neg_log_of_palmGap_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {κ : ℝ}
    (hκ : 0 ≤ κ) {n : ℕ} (σ : Fin n ≃ ι)
    (h : ∀ k : Fin n, palmGap P A (pre σ k) (σ k) ≤ κ - 1) :
    ∑ t, prob P (A t) ≤ κ * -Real.log (prob P (avoid A univ)) := by
  rw [← sum_condProb_mul_one_add_palmGap hP σ, neg_log_prob_avoid_eq_sum hP hq σ, mul_sum]
  refine sum_le_sum fun k _ ↦ ?_
  have h0 := condProb_nonneg hP (A := A) (pre σ k) (σ k)
  have h1 := Real.log_le_sub_one_of_pos (sub_pos.2 (condProb_lt_one hP hq (A := A) (pre σ k) (σ k)))
  have h2 : condProb P A (pre σ k) (σ k) ≤ -Real.log (1 - condProb P A (pre σ k) (σ k)) := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (h k) h0, mul_le_mul_of_nonneg_left h2 hκ]

/-- `M_T ≤ N_T`. -/
theorem condMean_le_card (hP : IsProb P) (T : Finset ι) : condMean P A T ≤ Tᶜ.card :=
  calc condMean P A T ≤ ∑ t ∈ Tᶜ, (1 : ℝ) := sum_le_sum fun t _ ↦ condProb_le_one hP T t
    _ = Tᶜ.card := by simp

/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`) along an adaptive ordering. Assume
`q > 0`, `κ ≥ 0` and (H3) on the window `k₀ ≤ |T|`, `N_T ≥ K + 1`: some `s ∉ T` has
`Δ_s(T) ≤ κ - 1`. Then every `T` with `k₀ ≤ |T|` has `M_T ≤ κ (log U(Z_T) - log q) + K`. -/
theorem condMean_le_of_exists_palmGap_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {κ : ℝ} (hκ : 0 ≤ κ) {k₀ K : ℕ}
    (hH3 : ∀ T : Finset ι, k₀ ≤ T.card → K < Tᶜ.card → ∃ s ∉ T, palmGap P A T s ≤ κ - 1)
    (T : Finset ι) (hT : k₀ ≤ T.card) :
    condMean P A T ≤
      κ * (Real.log (prob P (avoid A T)) - Real.log (prob P (avoid A univ))) + K := by
  have base : ∀ T : Finset ι, Tᶜ.card ≤ K → condMean P A T ≤
      κ * (Real.log (prob P (avoid A T)) - Real.log (prob P (avoid A univ))) + K := by
    intro T hK
    have h1 := condMean_le_card hP (A := A) T
    have h2 : Real.log (prob P (avoid A univ)) ≤ Real.log (prob P (avoid A T)) :=
      Real.log_le_log hq (prob_mono hP (avoid_anti (subset_univ T)))
    have h3 : ((Tᶜ.card : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [mul_nonneg hκ (sub_nonneg.2 h2)]
  have key : ∀ N : ℕ, ∀ T : Finset ι, Tᶜ.card = N → k₀ ≤ T.card → condMean P A T ≤
      κ * (Real.log (prob P (avoid A T)) - Real.log (prob P (avoid A univ))) + K := by
    intro N
    induction N with
    | zero => exact fun T hN _ ↦ base T (by omega)
    | succ N ih =>
      intro T hN hT
      by_cases hK : K < N + 1
      · obtain ⟨s, hs, hΔ⟩ := hH3 T hT (hN ▸ hK)
        have hN' : (insert s T)ᶜ.card = N := by
          rw [compl_insert, card_erase_of_mem (mem_compl.mpr hs), hN]
          rfl
        have hT' : k₀ ≤ (insert s T).card := by
          rw [card_insert_of_notMem hs]
          omega
        have ih' := ih (insert s T) hN' hT'
        have hA := condMean_sub_condMean_insert hP (A := A) hs
        have hlog := neg_log_avoid_insert hP hq (A := A) T s
        have h0 := condProb_nonneg hP (A := A) T s
        have h1 := Real.log_le_sub_one_of_pos (sub_pos.2 (condProb_lt_one hP hq (A := A) T s))
        have h2 : condProb P A T s ≤ -Real.log (1 - condProb P A T s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hΔ h0, mul_le_mul_of_nonneg_left h2 hκ]
      · exact base T (by omega)
  exact key _ T rfl hT

/-- Lemmas A and B of the (V+) survey (`v-plus-strategy-survey.md`), general form. Assume
`q > 0`, `κ ≥ 0`, `k₀ ≤ n`, (H3) on the window `k₀ ≤ |T|`, `N_T ≥ K + 1` (some `s ∉ T` has
`Δ_s(T) ≤ κ - 1`), and `μ - M_T ≤ E` for every `T` with `|T| = k₀`. Then
`μ - E - K ≤ κ (-log q)`. The top levels `N_T ≤ K` cost `M_T ≤ N_T ≤ K`. -/
theorem sub_le_mul_neg_log_of_exists_palmGap_le (hP : IsProb P)
    (hq : 0 < prob P (avoid A univ)) {κ : ℝ} (hκ : 0 ≤ κ) {k₀ K : ℕ}
    (hH3 : ∀ T : Finset ι, k₀ ≤ T.card → K < Tᶜ.card → ∃ s ∉ T, palmGap P A T s ≤ κ - 1)
    (hk₀ : k₀ ≤ Fintype.card ι) {E : ℝ}
    (hE : ∀ T : Finset ι, T.card = k₀ → ∑ t, prob P (A t) - condMean P A T ≤ E) :
    ∑ t, prob P (A t) - E - K ≤ κ * -Real.log (prob P (avoid A univ)) := by
  obtain ⟨T, hT⟩ := powersetCard_nonempty.mpr (show k₀ ≤ (univ : Finset ι).card by
    rwa [card_univ])
  have hTc := (mem_powersetCard.mp hT).2
  have h1 := condMean_le_of_exists_palmGap_le hP hq hκ hH3 T hTc.ge
  have h2 := hE T hTc
  have h3 : Real.log (prob P (avoid A T)) ≤ 0 :=
    Real.log_nonpos (prob_nonneg hP _) (prob_le_one hP _)
  rw [mul_sub] at h1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hκ h3]

/-- Lemma B(i) of the (V+) survey (`v-plus-strategy-survey.md`): `1 + Δ_s(T) ≤ N_T` for
`s ∉ T`. -/
theorem one_add_palmGap_le (hP : IsProb P) {T : Finset ι} {s : ι} (hsT : s ∉ T) :
    1 + palmGap P A T s ≤ Tᶜ.card := by
  have h1 : ∑ t ∈ (insert s T)ᶜ, palmProb P A T s t ≤ (insert s T)ᶜ.card := by
    simpa using sum_le_sum fun t (_ : t ∈ (insert s T)ᶜ) ↦ palmProb_le_one hP (A := A) T s t
  have h2 := condMean_nonneg hP (A := A) (insert s T)
  have h3 : ((insert s T)ᶜ.card : ℝ) = Tᶜ.card - 1 := by
    rw [compl_insert, card_erase_of_mem (mem_compl.mpr hsT),
      Nat.cast_sub (card_pos.mpr ⟨s, mem_compl.mpr hsT⟩), Nat.cast_one]
  rw [palmGap]
  linarith

/-- Lemma B(i) of the (V+) survey (`v-plus-strategy-survey.md`): `B_T ≤ D_T`. -/
theorem bernVarSum_le_condSlack (hP : IsProb P) (T : Finset ι) :
    bernVarSum P A T ≤ condSlack P A T :=
  sum_le_sum fun s _ ↦ by
    nlinarith [condProb_nonneg hP (A := A) T s, condProb_le_one hP (A := A) T s]

/-- Lemma B(i) of the (V+) survey (`v-plus-strategy-survey.md`): if `D_T > 0`, then
`V_T / D_T ≤ N_T`, so the levels `N_T ≤ K` add at most `K (K + 1) / 2` in Theorem 3(a) of
COD-198. -/
theorem condVar_div_condSlack_le (hP : IsProb P) {T : Finset ι} (hD : 0 < condSlack P A T) :
    condVar P A T / condSlack P A T ≤ Tᶜ.card := by
  rw [div_le_iff₀ hD]
  exact (condVar_le_card_mul hP T).trans
    (mul_le_mul_of_nonneg_left (bernVarSum_le_condSlack hP T) (Nat.cast_nonneg _))

/-- Lemma B(ii) of the (V+) survey (`v-plus-strategy-survey.md`), general form:
`μ - M_T ≤ ∑_{u ∈ T} ∑_t U(A_t A_u) = ∑_{u ∈ T} E[X 1_{A_u}]`. -/
theorem sum_prob_sub_condMean_le (hP : IsProb P) (T : Finset ι) :
    ∑ t, prob P (A t) - condMean P A T ≤ ∑ u ∈ T, ∑ t, prob P (A t ∩ A u) := by
  have hM : condMean P A T = ∑ t, condProb P A T t := by
    rw [condMean, ← sum_add_sum_compl T, sum_eq_zero fun t ht ↦ condProb_of_mem ht, zero_add]
  have h := sum_le_sum fun t (_ : t ∈ univ) ↦
    (sub_sum_le_prob_inter_avoid hP (A := A) T t).trans (prob_inter_avoid_le_condProb hP T t)
  rw [sum_sub_distrib] at h
  rw [hM, sum_comm]
  linarith

/-- Lemma B(ii) of the (V+) survey (`v-plus-strategy-survey.md`): with `U(A_t) ≤ p` and the
Kim–Wormald pair-ratio bound `U(A_s A_t) ≤ R p²` for `s ≠ t` (the hypothesis `hR`, which is not
proved here), `μ - M_T ≤ |T| p (1 + (n - 1) p R)`, the survey's `|T| p E_{Q_0}[X]`. -/
theorem sum_prob_sub_condMean_le_of_pairRatio (hP : IsProb P) {p R : ℝ}
    (hp : ∀ t, prob P (A t) ≤ p) (hR : ∀ s t, s ≠ t → prob P (A s ∩ A t) ≤ R * p ^ 2)
    (T : Finset ι) :
    ∑ t, prob P (A t) - condMean P A T ≤
      T.card * p * (1 + (Fintype.card ι - 1) * p * R) := by
  refine (sum_prob_sub_condMean_le hP T).trans ?_
  have h : ∀ u, ∑ t, prob P (A t ∩ A u) ≤ p * (1 + (Fintype.card ι - 1) * p * R) := fun u ↦ by
    rw [← add_sum_erase _ _ (mem_univ u), Set.inter_self]
    have h1 := sum_le_sum fun t (ht : t ∈ univ.erase u) ↦ hR t u (ne_of_mem_erase ht)
    rw [sum_const, card_erase_of_mem (mem_univ u), card_univ, nsmul_eq_mul,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨u⟩), Nat.cast_one] at h1
    nlinarith [hp u]
  calc ∑ u ∈ T, ∑ t, prob P (A t ∩ A u) ≤ ∑ u ∈ T, p * (1 + (Fintype.card ι - 1) * p * R) :=
        sum_le_sum fun u _ ↦ h u
    _ = _ := by
        rw [sum_const, nsmul_eq_mul]
        ring

/-- Lemmas A and B of the (V+) survey (`v-plus-strategy-survey.md`), the stated form. Assume
`q > 0`, `κ > 0`, `U(A_t) = p > 0`, `δ ≥ 0`, the Kim–Wormald pair-ratio bound
`U(A_s A_t) ≤ R p²` for `s ≠ t` with `R ≥ 0` (the hypothesis `hR`, which is not proved here), and
(H3) on the window `⌊δ / p⌋ ≤ |T|`, `N_T ≥ K + 1`: some `s ∉ T` has `Δ_s(T) ≤ κ - 1`. Then
`-log q ≥ ((1 - δ R) μ - δ - K (K + 1) / 2) / κ`. The survey's window `δ / p ≤ k ≤ n - K` for the
step `k` from `T_{k-1}` contains this one. -/
theorem div_le_neg_log_of_exists_palmGap_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {κ p δ R : ℝ} {K : ℕ} (hκ : 0 < κ) (hp : ∀ t, prob P (A t) = p) (hp0 : 0 < p) (hδ : 0 ≤ δ)
    (hR0 : 0 ≤ R) (hR : ∀ s t, s ≠ t → prob P (A s ∩ A t) ≤ R * p ^ 2)
    (hH3 : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → K < Tᶜ.card →
      ∃ s ∉ T, palmGap P A T s ≤ κ - 1) :
    ((1 - δ * R) * ∑ t, prob P (A t) - δ - K * (K + 1) / 2) / κ ≤
      -Real.log (prob P (avoid A univ)) := by
  have hμ : ∑ t, prob P (A t) = Fintype.card ι * p := by
    rw [sum_congr rfl fun t _ ↦ hp t, sum_const, card_univ, nsmul_eq_mul]
  have hq0 : 0 ≤ -Real.log (prob P (avoid A univ)) :=
    neg_nonneg.2 (Real.log_nonpos (prob_nonneg hP _) (prob_le_one hP _))
  have hKK : (K : ℝ) ≤ K * (K + 1) / 2 := by
    rcases Nat.eq_zero_or_pos K with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ K := by exact_mod_cast h
      nlinarith
  have hfl : (⌊δ / p⌋₊ : ℝ) * p ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ hp0.le)
    rwa [le_div_iff₀ hp0] at this
  rw [div_le_iff₀ hκ]
  by_cases hk : ⌊δ / p⌋₊ ≤ Fintype.card ι
  · have h := sub_le_mul_neg_log_of_exists_palmGap_le hP hq hκ.le hH3 hk
      (E := δ * (1 + (∑ t, prob P (A t)) * R)) fun T hT ↦ by
        refine (sum_prob_sub_condMean_le_of_pairRatio hP (fun t ↦ (hp t).le) hR T).trans ?_
        rw [hT, hμ]
        have h1 : (Fintype.card ι - 1 : ℝ) * p * R ≤ Fintype.card ι * p * R := by nlinarith
        have h3 : 0 ≤ (Fintype.card ι : ℝ) * p * R :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hp0.le) hR0
        have h4 : 0 ≤ (⌊δ / p⌋₊ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0.le
        rcases le_or_gt 0 (1 + (Fintype.card ι - 1 : ℝ) * p * R) with h2 | h2
        · calc (⌊δ / p⌋₊ : ℝ) * p * (1 + (Fintype.card ι - 1) * p * R) ≤
                δ * (1 + (Fintype.card ι - 1) * p * R) := mul_le_mul_of_nonneg_right hfl h2
            _ ≤ δ * (1 + Fintype.card ι * p * R) := by nlinarith
        · nlinarith [mul_nonneg hδ (add_nonneg zero_le_one h3)]
    nlinarith
  · have hn : (Fintype.card ι : ℝ) < ⌊δ / p⌋₊ := by exact_mod_cast not_le.mp hk
    have h1 : (∑ t, prob P (A t)) < δ := by
      rw [hμ]
      nlinarith
    have h2 : 0 ≤ ∑ t, prob P (A t) := sum_nonneg fun t _ ↦ prob_nonneg hP _
    nlinarith [mul_nonneg (mul_nonneg hδ hR0) h2, mul_nonneg hκ.le hq0]

/-- `V_T - B_T = ∑_{s ∉ T} f_s(T) (1 - f_s(T)) Δ_s(T)` (Section 4 of the (V+) survey,
`v-plus-strategy-survey.md`). -/
theorem condVar_sub_bernVarSum (hP : IsProb P) (T : Finset ι) :
    condVar P A T - bernVarSum P A T =
      ∑ s ∈ Tᶜ, condProb P A T s * (1 - condProb P A T s) * palmGap P A T s := by
  rw [condVar_eq_bernVarSum_add hP, add_sub_cancel_left]
  refine sum_congr rfl fun s hs ↦ ?_
  have h1 := one_sub_condProb_mul_condMean_sub hP (A := A) (mem_compl.mp hs)
  rw [condMean_sub_condMean_insert hP (mem_compl.mp hs), covSum, compl_insert] at h1
  linear_combination -h1

/-- Lemma A of the (V+) survey (`v-plus-strategy-survey.md`): (V+_B) implies (H3). If
`V_T ≤ κ B_T` and `B_T > 0`, then some `s ∉ T` has `Δ_s(T) ≤ κ - 1`, because the minimum of
`Δ_s(T)` is at most its `f (1 - f)`-weighted average `(V_T - B_T) / B_T`. The survey states this
without `B_T > 0`. At `B_T = 0` with `q > 0`, every `f_s(T)` is `0`, so `Δ_s(T) = 0` and (H3) fails
for `κ < 1`. -/
theorem exists_palmGap_le_of_condVar_le (hP : IsProb P) {T : Finset ι} {κ : ℝ}
    (hV : condVar P A T ≤ κ * bernVarSum P A T) (hB : 0 < bernVarSum P A T) :
    ∃ s ∉ T, palmGap P A T s ≤ κ - 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hpos⟩ : ∃ s ∈ Tᶜ, 0 < condProb P A T s * (1 - condProb P A T s) := by
    by_contra h
    push Not at h
    exact absurd (sum_nonpos h) (not_le.mpr hB)
  have hlt : ∑ s ∈ Tᶜ, condProb P A T s * (1 - condProb P A T s) * (κ - 1) <
      ∑ s ∈ Tᶜ, condProb P A T s * (1 - condProb P A T s) * palmGap P A T s :=
    sum_lt_sum (fun s hs ↦ mul_le_mul_of_nonneg_left (hcon s (mem_compl.mp hs)).le
      (mul_nonneg (condProb_nonneg hP T s) (sub_nonneg.2 (condProb_le_one hP T s))))
      ⟨s, hs, mul_lt_mul_of_pos_left (hcon s (mem_compl.mp hs)) hpos⟩
  rw [← sum_mul, ← bernVarSum, ← condVar_sub_bernVarSum hP] at hlt
  nlinarith

end LemmaAB

section Corollary4

/-- `∑_{i < n} g(n - i) = ∑_{j < n} g(j + 1)`. -/
theorem sum_range_reflect_one (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, g (n - i) = ∑ j ∈ range n, g (j + 1) := by
  rw [← sum_range_reflect (fun j ↦ g (j + 1))]
  exact sum_congr rfl fun j hj ↦ congrArg g (by have := mem_range.mp hj; omega)

/-- `∑_{j < n, j + 1 ≤ K} (j + 1) ≤ K (K + 1) / 2`. -/
theorem sum_range_ite_le (n K : ℕ) :
    ∑ j ∈ range n, (if j + 1 ≤ K then ((j + 1 : ℕ) : ℝ) else 0) ≤ K * (K + 1) / 2 := by
  rw [← sum_filter, ← sum_range_add_one]
  push_cast
  exact sum_le_sum_of_subset_of_nonneg
    (fun j hj ↦ by simp only [mem_filter, mem_range] at hj ⊢; omega) fun _ _ _ ↦ by positivity

/-- Corollary 4 of COD-198 (`cod-198-attempt.md`) with both free ends of Lemma B of the (V+) survey
(`v-plus-strategy-survey.md`), general form. Assume `q > 0`, `κ ≥ 0`, `V_T / D_T ≤ c(|T|)` for
`|T| < k₀`, and (V+) `V_T ≤ κ L_T` for every `T` with `k₀ ≤ |T|` and `N_T ≥ K + 1`. Then
`μ - ∑_{k < min(k₀, n)} c(k) - K (K + 1) / 2 ≤ κ (-log q)`. -/
theorem sub_sum_sub_le_mul_neg_log (hP : IsProb P) (hq : 0 < prob P (avoid A univ)) {κ : ℝ}
    (hκ : 0 ≤ κ) {k₀ K : ℕ} {c : ℕ → ℝ}
    (hlow : ∀ T : Finset ι, T.card < k₀ → T ≠ univ → condVar P A T / condSlack P A T ≤ c T.card)
    (hV : ∀ T : Finset ι, k₀ ≤ T.card → K < Tᶜ.card → condVar P A T ≤ κ * entSum P A T) :
    ∑ t, prob P (A t) - ∑ k ∈ range (min k₀ (Fintype.card ι)), c k - K * (K + 1) / 2 ≤
      κ * -Real.log (prob P (avoid A univ)) := by
  have hw := fun T (hT : T ≠ univ) ↦ sum_reweight hP hq (A := A) hT
  set h : ℕ → ℝ := fun i ↦ (if i < k₀ then c i else 0) +
    if Fintype.card ι - i ≤ K then ((Fintype.card ι - i : ℕ) : ℝ) else 0 with hh
  have hpt : ∀ T : Finset ι, ∀ s, s ∉ T → condVar P A T / condSlack P A T ≤
      h T.card + κ * (entSum P A T / condSlack P A T) := by
    intro T s hs
    have hT : T ≠ univ := fun e ↦ hs (e ▸ mem_univ s)
    have hD := condSlack_pos hP hq (A := A) hT
    have hL : 0 ≤ κ * (entSum P A T / condSlack P A T) :=
      mul_nonneg hκ (div_nonneg (entSum_nonneg hP T) hD.le)
    have hN : Tᶜ.card = Fintype.card ι - T.card := card_compl T
    have h2 : 0 ≤ if Fintype.card ι - T.card ≤ K then
        ((Fintype.card ι - T.card : ℕ) : ℝ) else 0 := by
      split_ifs <;> positivity
    simp only [hh]
    by_cases h1 : T.card < k₀
    · simp only [h1, ↓reduceIte]
      linarith [hlow T h1 hT]
    simp only [h1, ↓reduceIte, zero_add]
    by_cases hK : K < Tᶜ.card
    · have h3 : condVar P A T / condSlack P A T ≤ κ * (entSum P A T / condSlack P A T) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hV T (not_lt.mp h1) hK) hD.le
      linarith
    · have hK' : Fintype.card ι - T.card ≤ K := by omega
      simp only [hK', ↓reduceIte]
      rw [← hN]
      linarith [condVar_div_condSlack_le hP hD]
  have hmono := kerExp_mono (w := reweight P A) (fun T s _ ↦ reweight_nonneg hP T s) hpt
    (Fintype.card ι) ∅
  rw [kerExp_reweight_condVar hP hq, kerExp_add, kerExp_const_mul,
    kerExp_card hw h _ ∅ (by rw [compl_empty, card_univ]), kerExp_reweight_entSum hP hq,
    card_empty] at hmono
  simp only [zero_add, hh, sum_add_distrib] at hmono
  have e1 : ∑ i ∈ range (Fintype.card ι), (if i < k₀ then c i else 0) =
      ∑ k ∈ range (min k₀ (Fintype.card ι)), c k := by
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range, lt_min_iff]
    omega
  have e2 : ∑ i ∈ range (Fintype.card ι), (if Fintype.card ι - i ≤ K then
      ((Fintype.card ι - i : ℕ) : ℝ) else 0) =
      ∑ j ∈ range (Fintype.card ι), (if j + 1 ≤ K then ((j + 1 : ℕ) : ℝ) else 0) :=
    sum_range_reflect_one (fun N ↦ if N ≤ K then (N : ℝ) else 0) _
  have e3 := sum_range_ite_le (Fintype.card ι) K
  rw [e1, e2] at hmono
  linarith

/-- Corollary 4(i) of COD-198 (`cod-198-attempt.md`), with the upper free end of Lemma B of the
(V+) survey (`v-plus-strategy-survey.md`). Assume `q > 0`, `κ > 0`, `U(A_t) ≤ p` with `p > 0`,
`δ ≥ 0`, `δ + p < 1`, `δ < μ`, and (V+) `V_T ≤ κ L_T` for every `T` with `⌊δ / p⌋ ≤ |T|` and
`N_T ≥ K + 1`. `K = 0` is the paper's range `⌊δ / p⌋ ≤ |T| ≤ n - 1`. Then
`-log q ≥ (μ - C_δ - K (K + 1) / 2) / κ` with `C_δ = Var X δ / ((1 - δ - p)(μ - δ))`. The paper
writes `C_δ = (1 + o(1)) / (1 - δ)`, using `Var X ≤ μ + O(1)` from the Kim–Wormald pair-ratio bound
(see `div_le_neg_log_of_condVar_le_of_pairRatio`, where that bound is a hypothesis). -/
theorem div_le_neg_log_of_condVar_le (hP : IsProb P) (hq : 0 < prob P (avoid A univ))
    {p δ κ : ℝ} {K : ℕ} (hp : ∀ t, prob P (A t) ≤ p) (hp0 : 0 < p) (hδ0 : 0 ≤ δ)
    (hδp : δ + p < 1) (hμ : δ < ∑ t, prob P (A t)) (hκ : 0 < κ)
    (hV : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → K < Tᶜ.card → condVar P A T ≤ κ * entSum P A T) :
    (∑ t, prob P (A t) - condVar P A ∅ * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) -
      K * (K + 1) / 2) / κ ≤ -Real.log (prob P (avoid A univ)) := by
  have hVar := condVar_nonneg hP (A := A) ∅
  have ha : 0 < 1 - δ - p := by linarith
  have hδ1 : 0 < 1 - δ := by linarith
  have hfl : (⌊δ / p⌋₊ : ℝ) * p ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ0 hp0.le)
    rwa [le_div_iff₀ hp0] at this
  have hμn : ∑ t, prob P (A t) ≤ Fintype.card ι * p :=
    calc ∑ t, prob P (A t) ≤ ∑ _t : ι, p := sum_le_sum fun t _ ↦ hp t
      _ = Fintype.card ι * p := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hk₀n : (⌊δ / p⌋₊ : ℝ) < Fintype.card ι := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h hp0.le]
  have hk₀n' : ⌊δ / p⌋₊ < Fintype.card ι := by exact_mod_cast hk₀n
  have hlow : ∀ T : Finset ι, T.card < ⌊δ / p⌋₊ → T ≠ univ →
      condVar P A T / condSlack P A T ≤
        condVar P A ∅ / ((1 - δ - p) * ((Fintype.card ι : ℝ) - T.card)) := by
    intro T hT hTu
    have hTp : (T.card : ℝ) * p ≤ δ := by
      have : (T.card : ℝ) ≤ ⌊δ / p⌋₊ := by exact_mod_cast hT.le
      nlinarith
    have hU : 1 - δ ≤ prob P (avoid A T) := by
      have h1 := one_sub_sum_le_prob_avoid hP (A := A) T
      have h2 : ∑ u ∈ T, prob P (A u) ≤ T.card * p :=
        calc ∑ u ∈ T, prob P (A u) ≤ ∑ _u ∈ T, p := sum_le_sum fun u _ ↦ hp u
          _ = T.card * p := by rw [sum_const, nsmul_eq_mul]
      linarith
    have hVT : condVar P A T * (1 - δ) ≤ condVar P A ∅ :=
      (mul_le_mul_of_nonneg_left hU (condVar_nonneg hP T)).trans (condVar_mul_prob_le hP T)
    have hf : ∀ s, condProb P A T s ≤ p / (1 - δ) := fun s ↦
      (condProb_le_div hP hp hp0.le (by linarith) s).trans
        (div_le_div_of_nonneg_left hp0.le hδ1 (by linarith))
    have hN : (Tᶜ.card : ℝ) = Fintype.card ι - T.card := by
      rw [card_compl, Nat.cast_sub (card_le_univ T)]
    have hNpos : (0 : ℝ) < Tᶜ.card := by
      have : 0 < Tᶜ.card :=
        card_pos.mpr (by rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]; exact hTu)
      exact_mod_cast this
    have hD : Tᶜ.card * (1 - δ - p) ≤ condSlack P A T * (1 - δ) := by
      have h1 : ∑ s ∈ Tᶜ, (1 - p / (1 - δ)) ≤ condSlack P A T :=
        sum_le_sum fun s _ ↦ by linarith [hf s]
      rw [sum_const, nsmul_eq_mul] at h1
      have e : (1 - p / (1 - δ)) * (1 - δ) = 1 - δ - p := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hδ1.ne']
      nlinarith [mul_le_mul_of_nonneg_right h1 hδ1.le]
    have hDpos : 0 < condSlack P A T := by nlinarith [mul_pos hNpos ha]
    rw [← hN, div_le_div_iff₀ hDpos (mul_pos ha hNpos)]
    nlinarith [mul_le_mul_of_nonneg_left hD (condVar_nonneg hP (A := A) T),
      mul_le_mul_of_nonneg_left hVT hDpos.le]
  have hgen := sub_sum_sub_le_mul_neg_log hP hq hκ.le (k₀ := ⌊δ / p⌋₊) (K := K)
    (c := fun k ↦ condVar P A ∅ / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k))) hlow hV
  rw [min_eq_left hk₀n'.le] at hgen
  have hsum : ∑ k ∈ range ⌊δ / p⌋₊,
      condVar P A ∅ / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k)) ≤
      condVar P A ∅ * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) := by
    have hnk : (0 : ℝ) < Fintype.card ι - ⌊δ / p⌋₊ := by linarith
    have h1 : ∀ k ∈ range ⌊δ / p⌋₊,
        condVar P A ∅ / ((1 - δ - p) * ((Fintype.card ι : ℝ) - k)) ≤
          condVar P A ∅ / ((1 - δ - p) * ((Fintype.card ι : ℝ) - ⌊δ / p⌋₊)) := fun k hk ↦ by
      have : (k : ℝ) < ⌊δ / p⌋₊ := by exact_mod_cast mem_range.mp hk
      exact div_le_div_of_nonneg_left hVar (mul_pos ha hnk)
        (mul_le_mul_of_nonneg_left (by linarith) ha.le)
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [card_range, nsmul_eq_mul, mul_div_assoc',
      div_le_div_iff₀ (mul_pos ha hnk) (mul_pos ha (by linarith))]
    have hkey : (⌊δ / p⌋₊ : ℝ) * ∑ t, prob P (A t) ≤ δ * Fintype.card ι := by
      nlinarith [mul_le_mul_of_nonneg_left hμn (Nat.cast_nonneg ⌊δ / p⌋₊),
        mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (Fintype.card ι))]
    nlinarith [mul_nonneg (mul_nonneg hVar ha.le) (sub_nonneg.2 hkey)]
  rw [div_le_iff₀ hκ]
  linarith

/-- Corollary 4(iii) of COD-198 (`cod-198-attempt.md`): the clean form (V+_B) `V_T ≤ κ B_T` on
the window `⌊δ / p⌋ ≤ |T|`, `N_T ≥ K + 1` implies (V+) there, since `B_T ≤ L_T`, and so gives the
bound of `div_le_neg_log_of_condVar_le`. -/
theorem div_le_neg_log_of_condVar_le_bernVarSum (hP : IsProb P)
    (hq : 0 < prob P (avoid A univ)) {p δ κ : ℝ} {K : ℕ} (hp : ∀ t, prob P (A t) ≤ p)
    (hp0 : 0 < p) (hδ0 : 0 ≤ δ) (hδp : δ + p < 1) (hμ : δ < ∑ t, prob P (A t)) (hκ : 0 < κ)
    (hV : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → K < Tᶜ.card →
      condVar P A T ≤ κ * bernVarSum P A T) :
    (∑ t, prob P (A t) - condVar P A ∅ * δ / ((1 - δ - p) * (∑ t, prob P (A t) - δ)) -
      K * (K + 1) / 2) / κ ≤ -Real.log (prob P (avoid A univ)) :=
  div_le_neg_log_of_condVar_le hP hq hp hp0 hδ0 hδp hμ hκ fun T h1 h2 ↦
    (hV T h1 h2).trans (mul_le_mul_of_nonneg_left (bernVarSum_le_entSum hP T) hκ.le)

/-- The variance bound in the proof of Corollary 4 of COD-198 (`cod-198-attempt.md`): with
`U(A_t) = p` and the Kim–Wormald pair-ratio bound `U(A_s A_t) ≤ R p²` for `s ≠ t` (the hypothesis
`hR`, which is not proved here), `Var X ≤ μ + n (n - 1) p² (R - 1)`. -/
theorem condVar_empty_le_of_pairRatio (hP : IsProb P) {p R : ℝ} (hp : ∀ t, prob P (A t) = p)
    (hR : ∀ s t, s ≠ t → prob P (A s ∩ A t) ≤ R * p ^ 2) :
    condVar P A ∅ ≤
      ∑ t, prob P (A t) + Fintype.card ι * (Fintype.card ι - 1) * p ^ 2 * (R - 1) := by
  have hf : ∀ t, condProb P A ∅ t = p := fun t ↦ by rw [condProb_empty hP, hp]
  have hc : ∀ s t, s ≠ t → condCov P A ∅ s t ≤ (R - 1) * p ^ 2 := fun s t hst ↦ by
    have : condPair P A ∅ s t = prob P (A s ∩ A t) := by
      rw [condPair, avoid_empty, Set.inter_univ, prob_univ hP, div_one]
    rw [condCov, this, hf, hf]
    nlinarith [hR s t hst]
  rw [condVar_eq_bernVarSum_add hP, bernVarSum, compl_empty]
  have h1 : ∑ s, condProb P A ∅ s * (1 - condProb P A ∅ s) ≤ ∑ t, prob P (A t) :=
    sum_le_sum fun s _ ↦ by rw [hf, hp]; nlinarith [sq_nonneg p]
  have h2 : ∑ s, ∑ t ∈ univ.erase s, condCov P A ∅ s t ≤
      Fintype.card ι * (Fintype.card ι - 1) * p ^ 2 * (R - 1) := by
    calc ∑ s, ∑ t ∈ univ.erase s, condCov P A ∅ s t ≤
          ∑ s : ι, ∑ _t ∈ univ.erase s, (R - 1) * p ^ 2 :=
          sum_le_sum fun s _ ↦ sum_le_sum fun t ht ↦ hc s t (ne_of_mem_erase ht).symm
      _ = _ := by
          simp only [sum_const, card_erase_of_mem, mem_univ, card_univ, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
          · simp [h]
          · rw [Nat.cast_sub h]
            push_cast
            ring
  linarith

/-- Corollary 4(i) of COD-198 (`cod-198-attempt.md`) with the Kim–Wormald input made explicit.
Under the hypotheses of `div_le_neg_log_of_condVar_le` with `U(A_t) = p`, and the Kim–Wormald
pair-ratio bound `U(A_s A_t) ≤ R p²` for `s ≠ t` (the hypothesis `hR`, which is not proved here),
`-log q ≥ (μ - C_δ - K (K + 1) / 2) / κ` with
`C_δ = (μ + n (n - 1) p² (R - 1)) δ / ((1 - δ - p)(μ - δ))`. When `n (n - 1) p² (R - 1) = O(1)`,
`μ → ∞` and `p → 0`, `C_δ → δ / (1 - δ)`, within the paper's `C_δ = (1 + o(1)) / (1 - δ)`. -/
theorem div_le_neg_log_of_condVar_le_of_pairRatio (hP : IsProb P)
    (hq : 0 < prob P (avoid A univ)) {p δ κ R : ℝ} {K : ℕ} (hp : ∀ t, prob P (A t) = p)
    (hR : ∀ s t, s ≠ t → prob P (A s ∩ A t) ≤ R * p ^ 2) (hp0 : 0 < p) (hδ0 : 0 ≤ δ)
    (hδp : δ + p < 1) (hμ : δ < ∑ t, prob P (A t)) (hκ : 0 < κ)
    (hV : ∀ T : Finset ι, ⌊δ / p⌋₊ ≤ T.card → K < Tᶜ.card → condVar P A T ≤ κ * entSum P A T) :
    (∑ t, prob P (A t) - (∑ t, prob P (A t) +
      Fintype.card ι * (Fintype.card ι - 1) * p ^ 2 * (R - 1)) * δ /
        ((1 - δ - p) * (∑ t, prob P (A t) - δ)) - K * (K + 1) / 2) / κ ≤
      -Real.log (prob P (avoid A univ)) := by
  refine le_trans ?_ (div_le_neg_log_of_condVar_le hP hq (fun t ↦ (hp t).le) hp0 hδ0 hδp hμ hκ hV)
  refine div_le_div_of_nonneg_right ?_ hκ.le
  have hden : 0 ≤ (1 - δ - p) * (∑ t, prob P (A t) - δ) :=
    mul_nonneg (by linarith) (by linarith)
  have := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (condVar_empty_le_of_pairRatio hP hp hR) hδ0) hden
  linarith

end Corollary4

section Corollary5

/-- `|V_T - B_T| ≤ ∑_{s ≠ t ∉ T} |Cov_T(s, t)|`. -/
theorem abs_condVar_sub_bernVarSum_le (hP : IsProb P) (T : Finset ι) :
    |condVar P A T - bernVarSum P A T| ≤ ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| := by
  rw [condVar_eq_bernVarSum_add hP, add_sub_cancel_left]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ abs_sum_le_sum_abs _ _)

/-- Under hypothesis (A) `f_t(T) ≤ φ` of Theorem 7 of COD-196, `B_T ≥ (1 - φ) M_T`. -/
theorem mul_condMean_le_bernVarSum (hP : IsProb P) {φ : ℝ}
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ) (T : Finset ι) :
    (1 - φ) * condMean P A T ≤ bernVarSum P A T := by
  rw [condMean, mul_sum]
  exact sum_le_sum fun s hs ↦ by
    have := hA T s (mem_compl.mp hs)
    nlinarith [condProb_nonneg hP (A := A) T s]

/-- Under hypothesis (A) `f_t(T) ≤ φ` of Theorem 7 of COD-196, `D_T ≥ (1 - φ) N_T`. -/
theorem mul_card_le_condSlack {φ : ℝ} (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (T : Finset ι) : (1 - φ) * Tᶜ.card ≤ condSlack P A T :=
  calc (1 - φ) * Tᶜ.card = ∑ _s ∈ Tᶜ, (1 - φ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ condSlack P A T := sum_le_sum fun s hs ↦ by linarith [hA T s (mem_compl.mp hs)]

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`): under (A) `f ≤ φ < 1` and the bound
`∑_{s ≠ t ∉ T} |Cov_T(s, t)| ≤ 2 √J M_T + 4 J`, which Lemma 3 of COD-196 derives from (B)
(`hB'_of_pairInfo`), `V_T ≤ (1 + θ) B_T + 4 J` with `θ = 2 √J / (1 - φ)`. This is (V+_B) up to the
additive `4 J`. -/
theorem condVar_le_of_sum_abs_condCov_le (hP : IsProb P) {φ J : ℝ} (hφ1 : φ < 1)
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ) {T : Finset ι}
    (hB : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    condVar P A T ≤ (1 + 2 * √J / (1 - φ)) * bernVarSum P A T + 4 * J := by
  have h1 := (abs_le.mp (abs_condVar_sub_bernVarSum_le hP (A := A) T)).2
  have h2 := mul_condMean_le_bernVarSum hP hA T
  have h1φ : 0 < 1 - φ := by linarith
  have hM : 2 * √J * condMean P A T ≤ 2 * √J / (1 - φ) * bernVarSum P A T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1φ]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * √J)]
  linarith

/-- Corollary 5 of COD-198 (`cod-198-attempt.md`): under the hypotheses of
`condVar_le_of_sum_abs_condCov_le`, `V_T ≥ (1 - φ)(1 - θ) M_T - 4 J`. This is (V−_M) up to the
additive `4 J`. -/
theorem le_condVar_of_sum_abs_condCov_le (hP : IsProb P) {φ J : ℝ} (hφ1 : φ < 1)
    (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ) {T : Finset ι}
    (hB : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J) :
    (1 - φ) * (1 - 2 * √J / (1 - φ)) * condMean P A T - 4 * J ≤ condVar P A T := by
  have h1 := (abs_le.mp (abs_condVar_sub_bernVarSum_le hP (A := A) T)).1
  have h2 := mul_condMean_le_bernVarSum hP hA T
  have h1φ : 0 < 1 - φ := by linarith
  have e : (1 - φ) * (1 - 2 * √J / (1 - φ)) = 1 - φ - 2 * √J := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ h1φ.ne']
  rw [e]
  linarith

/-- The error allowance of Corollary 5 of COD-198 at level `|T| = i`, for `n = |ι|`:
`(4 J / N + [N ≤ K + 1] (N - 1) φ) / (1 - φ)` with `N = n - i ≥ 2`, and `0` at `N ≤ 1`. -/
noncomputable def corrLevel (n K : ℕ) (J φ : ℝ) (i : ℕ) : ℝ :=
  if i + 1 < n then (4 * J / ((n - i : ℕ) : ℝ) +
    if n - i ≤ K + 1 then (((n - i : ℕ) : ℝ) - 1) * φ else 0) / (1 - φ) else 0

/-- The allowances of Corollary 5 sum to at most `η = (4 J log n + K (K + 1) φ / 2) / (1 - φ)`. -/
theorem sum_corrLevel_le (n K : ℕ) {J φ : ℝ} (hJ : 0 ≤ J) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    ∑ i ∈ range n, corrLevel n K J φ i ≤
      (4 * J * Real.log n + K * (K + 1) * φ / 2) / (1 - φ) := by
  have e : ∑ i ∈ range n, corrLevel n K J φ i = (∑ i ∈ range (n - 1), (4 * J /
      ((n - i : ℕ) : ℝ) + if n - i ≤ K + 1 then (((n - i : ℕ) : ℝ) - 1) * φ else 0)) /
        (1 - φ) := by
    rw [sum_div]
    simp only [corrLevel]
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [e]
  exact div_le_div_of_nonneg_right (sum_corr_le n K hJ hφ0) (by linarith)

/-- The errors of Corollary 5 of COD-198 (`cod-198-attempt.md`): under (A) `f ≤ φ < 1` with
`φ ≥ 0` and (B′) for `N_T ≥ K + 2`, every `T ≠ ι` has `|V_T - B_T| ≤ 2 √J M_T + e_T`, with
`e_T = 4 J` for `N_T ≥ K + 2` and `e_T = N_T (N_T - 1) φ` otherwise, and `e_T / D_T` is at most
the allowance `corrLevel` at level `|T|`. -/
theorem abs_condVar_sub_le_and_div_le (hP : IsProb P) {φ J : ℝ} {K : ℕ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ < 1) (hJ : 0 ≤ J) (hA : ∀ T t, t ∉ T → condProb P A T t ≤ φ)
    (hB : ∀ T : Finset ι, K + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤ 2 * √J * condMean P A T + 4 * J)
    {T : Finset ι} (hT : T ≠ univ) :
    |condVar P A T - bernVarSum P A T| ≤ 2 * √J * condMean P A T +
        (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) ∧
      (if K + 2 ≤ Tᶜ.card then 4 * J else Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ) /
        condSlack P A T ≤ corrLevel (Fintype.card ι) K J φ T.card := by
  have h1φ : 0 < 1 - φ := by linarith
  have hNpos : 0 < Tᶜ.card :=
    card_pos.mpr (by rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]; exact hT)
  have hNr : (1 : ℝ) ≤ Tᶜ.card := by exact_mod_cast hNpos
  have hD : (1 - φ) * Tᶜ.card ≤ condSlack P A T := mul_card_le_condSlack hA T
  have hDpos : 0 < condSlack P A T := lt_of_lt_of_le (by positivity) hD
  have hM := condMean_nonneg hP (A := A) T
  have hN : Fintype.card ι - T.card = Tᶜ.card := (card_compl T).symm
  have hlev : T.card + 1 < Fintype.card ι ↔ 2 ≤ Tᶜ.card := by
    have := card_le_univ T
    omega
  by_cases hK : K + 2 ≤ Tᶜ.card
  · simp only [hK, ↓reduceIte]
    refine ⟨(abs_condVar_sub_bernVarSum_le hP T).trans (hB T hK), ?_⟩
    have h2 : T.card + 1 < Fintype.card ι := hlev.mpr (by omega)
    have h3 : ¬ Tᶜ.card ≤ K + 1 := by omega
    rw [corrLevel, hN]
    simp only [h2, h3, ↓reduceIte, add_zero]
    rw [div_div, mul_comm (Tᶜ.card : ℝ)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hD
  · simp only [hK, ↓reduceIte]
    have hC : ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
        Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ := by
      calc ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
            ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, φ :=
          sum_le_sum fun s hs ↦ sum_le_sum fun t _ ↦ abs_condCov_le hP hA (mem_compl.mp hs)
        _ = Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ := by
          rw [sum_congr rfl fun s hs ↦ by rw [sum_const, card_erase_of_mem hs], sum_const,
            nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hNpos]
          push_cast
          ring
    refine ⟨(abs_condVar_sub_bernVarSum_le hP T).trans (by nlinarith [Real.sqrt_nonneg J]), ?_⟩
    have hfrac : Tᶜ.card * ((Tᶜ.card : ℝ) - 1) * φ / condSlack P A T ≤
        ((Tᶜ.card : ℝ) - 1) * φ / (1 - φ) := by
      rw [div_le_div_iff₀ hDpos h1φ]
      have h0 : 0 ≤ ((Tᶜ.card : ℝ) - 1) * φ := mul_nonneg (by linarith) hφ0
      nlinarith [mul_le_mul_of_nonneg_left hD h0]
    rw [corrLevel]
    by_cases h2 : 2 ≤ Tᶜ.card
    · have h4 : T.card + 1 < Fintype.card ι := hlev.mpr h2
      have h5 : Tᶜ.card ≤ K + 1 := by omega
      rw [hN]
      simp only [h4, h5, ↓reduceIte]
      refine hfrac.trans (div_le_div_of_nonneg_right ?_ h1φ.le)
      have : 0 ≤ 4 * J / (Tᶜ.card : ℝ) := by positivity
      linarith
    · have h4 : ¬ T.card + 1 < Fintype.card ι := fun h ↦ h2 (hlev.mp h)
      simp only [h4, ↓reduceIte]
      have h1 : (Tᶜ.card : ℝ) = 1 := by exact_mod_cast (by omega : Tᶜ.card = 1)
      rw [h1]
      simp

end Corollary5

end ChainRule

end Pairing
