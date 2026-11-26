import Suppression.Reweighted
import Repair.Barrier.LevelWeight

/-!
# Contamination by zero states (vplusb-contra Lemma C1, Proposition C2, Theorem C3)

Source: `results/vplusb-contra.md` (2e62e83) §1 to §4. Notation is that of `Reweighted.lean`:
`P` is a probability weight on a finite set `Ω`, `A : ι → Set Ω` are events, `Z_T = avoid A T`,
`f_s(T) = condProb`, `M_T = condMean`, `V_T = condVar`, `B_T = bernVarSum`,
`U(A_s A_t | Z_T) = condPair`, `g_T(s, t) = pairRatio` (so the relative pair correlation is
`ρ_T(s, t) = g_T(s, t) - 1`), `X = eventCount A` and `q = U(Z_ι) = U(X = 0)`. Everything holds for
every law, as in the source.

Lemma C1 (§2).
* `sum_avoid_mul_sq_sub` : `E[(X - a)² 1_{Z_T}] = (V_T + (M_T - a)²) U(Z_T)`.
* `lowerTail_div_le_condVar_div` (Cantelli) : `ν_T(X ≤ M_T - a) ≤ V_T / (V_T + a²)` for `a > 0`.
* `lowerTail_div_le_of_condVar_le` : `V_T ≤ κ B_T` gives `ν_T(X ≤ M_T - a) ≤ κ M_T / (κ M_T + a²)`.
* `prob_avoid_univ_div_le_condVar_div`, `prob_avoid_univ_div_le_of_condVar_le` : with
  `ν_T(X = 0) = q / U(Z_T)`, `q / U(Z_T) ≤ V_T / (V_T + M_T²)` when `M_T > 0`, and
  `V_T ≤ κ B_T` gives `q / U(Z_T) ≤ κ / (κ + M_T)` for every `T` and `κ > 0`. The source assumes
  `N_T ≥ 1`, which is not needed.

Proposition C2 (§3). For a probability weight `Q` carried by zero states (`Q ω ≠ 0 → ω ∈ Z_ι`)
and `0 ≤ ε < 1`, the contaminated law is `contam P Q ε = (1 - ε) P + ε Q`. Conditioning on `Z_T`
turns it into `(1 - θ_T) ν_T + θ_T Q` with `θ_T = ε / ((1 - ε) U(Z_T) + ε)` (`mixTheta`), the
identity of §1 (`mixTheta_div_one_sub`). The source states C2 for a law `μ` on the free
coordinates and `μ_θ = (1 - θ) μ + θ δ_0`. The forms here are that statement applied to
`μ = ν_T`, for every `T` at once, and with any `Q` on zero states in place of `δ_0` (the spread
version of the Remark after C3).
* `condProb_contam`, `condPair_contam`, `condMean_contam` : `f′ = (1 - θ) f`, the same for pair
  probabilities and for `M`.
* `pairRatio_contam` : `ρ′ = (ρ + θ) / (1 - θ)` whenever `f_s f_t ≠ 0`.
* `condVar_contam` : `V′ = (1 - θ) V + θ (1 - θ) M²`. `bernVarSum_contam` :
  `B′ = (1 - θ)(B + θ S₂)` with `S₂ = ∑_{s ∉ T} f_s(T)²`.
* `condVar_div_bernVarSum_contam` : `V′ / B′ = (V + θ M²) / (B + θ S₂)`, and
  `div_le_condVar_div_bernVarSum_contam` : `V′ / B′ ≥ θ M / (1 + θ)`.
* `interRatio_contam` : at `T = ∅`, `R′_S = R_S / (1 - ε)^(|S| - 1)` for nonempty `S`.
* `condVar_le_iff` (C2(b), the exact split of (V+_B)) : for `0 < q < U(Z_T)`, with
  `θ₀ = q / U(Z_T)` and the `+` quantities taken under `posPart P A = U(· | X ≥ 1)`,
  `V_T ≤ κ B_T` if and only if `θ₀ (M_+² - κ S₂₊) ≤ κ B_+ - V_+`.
  `posPart_contam_zeroPart` : `U = (1 - q) U(· | X ≥ 1) + q U(· | X = 0)`.

Theorem C3 (§4), its two barred forms of (V+_B):
* `lt_condVar_contam` : if `0 ≤ κ` and `κ (1 + θ_T) < θ_T M_T^U`, the contaminated law has
  `V′_T > κ B′_T`.
* `lt_condVar_contam_of_le` : in particular when `(1 - ε) U(Z_T) ≤ ε` and `3 κ < M_T^U`.

The relative third cumulant expansion `κ̃′_3 ≈ κ̃_3 - θ` of C2(a) is an expansion to first order
and is not formalized.
-/

namespace Pairing

namespace Barrier

open Finset ChainRule

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {P : Ω → ℝ} {A : ι → Set Ω}

section LemmaC1

/-- `E[(X - a)² 1_{Z_T}] = (V_T + (M_T - a)²) U(Z_T)` when `U(Z_T) ≠ 0`
(`results/vplusb-contra.md` (2e62e83), proof of Lemma C1 and Proposition C2). -/
theorem sum_avoid_mul_sq_sub (hP : IsProb P) (T : Finset ι) (hu : prob P (avoid A T) ≠ 0)
    (a : ℝ) :
    ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - a) ^ 2 =
      (condVar P A T + (condMean P A T - a) ^ 2) * prob P (avoid A T) := by
  have h0 := sum_avoid_mul_eventCount hP (A := A) T
  have hU : ∑ ω, (avoid A T).indicator P ω = prob P (avoid A T) := rfl
  have hV : ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 =
      condVar P A T * prob P (avoid A T) := by
    rw [condVar, div_mul_cancel₀ _ hu]
  have e : ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - a) ^ 2 =
      ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - condMean P A T) ^ 2 +
        2 * (condMean P A T - a) * ∑ ω, (avoid A T).indicator P ω * eventCount A ω -
        (condMean P A T - a) * (condMean P A T + a) * ∑ ω, (avoid A T).indicator P ω := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun ω _ ↦ by ring
  rw [e, h0, hU, hV]
  ring

/-- Cantelli's inequality under `ν_T` (`results/vplusb-contra.md` (2e62e83), proof of
Lemma C1): `ν_T(X ≤ M_T - a) ≤ V_T / (V_T + a²)` for `a > 0`. -/
theorem lowerTail_div_le_condVar_div (hP : IsProb P) (T : Finset ι) {a : ℝ} (ha : 0 < a) :
    prob P ({ω | eventCount A ω ≤ condMean P A T - a} ∩ avoid A T) / prob P (avoid A T) ≤
      condVar P A T / (condVar P A T + a ^ 2) := by
  set E := {ω | eventCount A ω ≤ condMean P A T - a} ∩ avoid A T
  set V := condVar P A T
  set u := prob P (avoid A T)
  have hV := condVar_nonneg hP (A := A) T
  have hVa : 0 < V + a ^ 2 := by positivity
  rcases eq_or_lt_of_le (prob_nonneg hP (avoid A T)) with hu | hu
  · have hu0 : u = 0 := hu.symm
    rw [hu0, div_zero]
    exact div_nonneg hV hVa.le
  set t := V / a
  have ht : 0 ≤ t := div_nonneg hV ha.le
  have key : (a + t) ^ 2 * prob P E ≤ (V + t ^ 2) * u := by
    have hsum := sum_avoid_mul_sq_sub hP (A := A) T hu.ne' (condMean P A T + t)
    rw [show condMean P A T - (condMean P A T + t) = -t by ring, neg_sq] at hsum
    rw [← hsum, prob, mul_sum]
    refine sum_le_sum fun ω _ ↦ ?_
    by_cases hE : ω ∈ E
    · have h1 : ω ∈ avoid A T := hE.2
      have h2 : eventCount A ω ≤ condMean P A T - a := hE.1
      rw [Set.indicator_of_mem hE, Set.indicator_of_mem h1, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (hP.nonneg ω)
      nlinarith
    · rw [Set.indicator_of_notMem hE, mul_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω) (sq_nonneg _)
  have e1 : (a + t) ^ 2 = (a ^ 2 + V) ^ 2 / a ^ 2 := by
    rw [show t = V / a from rfl]
    field_simp
  have e2 : V + t ^ 2 = V * (a ^ 2 + V) / a ^ 2 := by
    rw [show t = V / a from rfl]
    field_simp
  rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (by positivity)] at key
  rw [div_le_div_iff₀ hu hVa]
  have hpE := prob_nonneg hP E
  nlinarith

/-- `B_T ≤ M_T` (`results/vplusb-contra.md` (2e62e83), proof of Lemma C1). -/
theorem bernVarSum_le_condMean (hP : IsProb P) (T : Finset ι) :
    bernVarSum P A T ≤ condMean P A T :=
  (bernVarSum_le_entSum hP T).trans (entSum_le_condMean hP T)

/-- Lemma C1 of `results/vplusb-contra.md` (2e62e83), lower-tail form: if `κ ≥ 0` and
`V_T ≤ κ B_T`, then `ν_T(X ≤ M_T - a) ≤ κ M_T / (κ M_T + a²)` for `a > 0`. -/
theorem lowerTail_div_le_of_condVar_le (hP : IsProb P) (T : Finset ι) {κ a : ℝ} (hκ : 0 ≤ κ)
    (ha : 0 < a) (hVB : condVar P A T ≤ κ * bernVarSum P A T) :
    prob P ({ω | eventCount A ω ≤ condMean P A T - a} ∩ avoid A T) / prob P (avoid A T) ≤
      κ * condMean P A T / (κ * condMean P A T + a ^ 2) := by
  refine (lowerTail_div_le_condVar_div hP T ha).trans ?_
  have hV := condVar_nonneg hP (A := A) T
  have hVM : condVar P A T ≤ κ * condMean P A T :=
    hVB.trans (mul_le_mul_of_nonneg_left (bernVarSum_le_condMean hP T) hκ)
  rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_pos_of_pos ha])]
  nlinarith [sq_pos_of_pos ha]

omit [Fintype Ω] [DecidableEq ι] in
/-- `X = 0` on `Z_ι` (`results/vplusb-contra.md` (2e62e83), Lemma C1, reading
`ν_T(X = 0) = q / U(Z_T)`). -/
theorem eventCount_of_mem_avoid_univ {ω : Ω} (h : ω ∈ avoid A univ) : eventCount A ω = 0 := by
  classical
  rw [eventCount_of_mem_avoid h, compl_univ, sum_empty]

/-- Lemma C1 of `results/vplusb-contra.md` (2e62e83), first inequality:
`ν_T(X = 0) = q / U(Z_T) ≤ V_T / (V_T + M_T²)` when `M_T > 0`. -/
theorem prob_avoid_univ_div_le_condVar_div (hP : IsProb P) (T : Finset ι)
    (hM : 0 < condMean P A T) :
    prob P (avoid A univ) / prob P (avoid A T) ≤
      condVar P A T / (condVar P A T + condMean P A T ^ 2) := by
  have hsub : avoid A univ ⊆
      {ω | eventCount A ω ≤ condMean P A T - condMean P A T} ∩ avoid A T := by
    intro ω hω
    refine ⟨?_, avoid_anti (subset_univ T) hω⟩
    change eventCount A ω ≤ condMean P A T - condMean P A T
    rw [eventCount_of_mem_avoid_univ hω, sub_self]
  exact le_trans (div_le_div_of_nonneg_right (prob_mono hP hsub) (prob_nonneg hP _))
    (lowerTail_div_le_condVar_div hP T hM)

/-- Lemma C1 of `results/vplusb-contra.md` (2e62e83): for every law, every `T` and `κ > 0`,
`V_T ≤ κ B_T` gives `ν_T(X = 0) = q / U(Z_T) ≤ κ / (κ + M_T)`. -/
theorem prob_avoid_univ_div_le_of_condVar_le (hP : IsProb P) (T : Finset ι) {κ : ℝ}
    (hκ : 0 < κ) (hVB : condVar P A T ≤ κ * bernVarSum P A T) :
    prob P (avoid A univ) / prob P (avoid A T) ≤ κ / (κ + condMean P A T) := by
  have hM0 := condMean_nonneg hP (A := A) T
  rcases eq_or_lt_of_le hM0 with hM | hM
  · rw [← hM, add_zero, div_self hκ.ne']
    exact div_le_one_of_le₀ (prob_mono hP (avoid_anti (subset_univ T))) (prob_nonneg hP _)
  refine (prob_avoid_univ_div_le_condVar_div hP T hM).trans ?_
  have hV := condVar_nonneg hP (A := A) T
  have hVM : condVar P A T ≤ κ * condMean P A T :=
    hVB.trans (mul_le_mul_of_nonneg_left (bernVarSum_le_condMean hP T) hκ.le)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hM hM]

end LemmaC1

section PropositionC2

/-- The contaminated law `(1 - ε) P + ε Q` of `results/vplusb-contra.md` (2e62e83) §1 and
Proposition C2. -/
def contam (P Q : Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  (1 - ε) * P ω + ε * Q ω

/-- The mixing weight `θ_T = ε / ((1 - ε) U(Z_T) + ε)` of `Q` in the contaminated law conditioned
on `Z_T` (`results/vplusb-contra.md` (2e62e83) §1 and Theorem C3). -/
noncomputable def mixTheta (P : Ω → ℝ) (A : ι → Set Ω) (T : Finset ι) (ε : ℝ) : ℝ :=
  ε / ((1 - ε) * prob P (avoid A T) + ε)

omit [Fintype ι] [DecidableEq ι] in
/-- The identity of `results/vplusb-contra.md` (2e62e83) §1:
`θ_T / (1 - θ_T) = ε / ((1 - ε) U(Z_T))`. -/
theorem mixTheta_div_one_sub (T : Finset ι) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hu : 0 < prob P (avoid A T)) :
    mixTheta P A T ε / (1 - mixTheta P A T ε) = ε / ((1 - ε) * prob P (avoid A T)) := by
  have hD : (1 - ε) * prob P (avoid A T) + ε ≠ 0 := by
    have := mul_pos (by linarith : (0 : ℝ) < 1 - ε) hu
    linarith
  rw [mixTheta, one_sub_div hD, div_div_div_cancel_right₀ hD]
  congr 1
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `U′(S) = (1 - ε) U(S) + ε Q(S)` (`results/vplusb-contra.md` (2e62e83), proof of
Proposition C2). -/
theorem prob_contam (P Q : Ω → ℝ) (ε : ℝ) (S : Set Ω) :
    prob (contam P Q ε) S = (1 - ε) * prob P S + ε * prob Q S := by
  rw [prob, prob, prob, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ ↦ ?_
  by_cases h : ω ∈ S <;> simp [Set.indicator, h, contam]

variable {Q : Ω → ℝ}

omit [DecidableEq ι] in
/-- A weight carried by `Z_ι` gives `Z_T` mass `1` (`results/vplusb-contra.md` (2e62e83) §1). -/
theorem prob_avoid_of_supp (hQ : IsProb Q) (hQZ : ∀ ω, Q ω ≠ 0 → ω ∈ avoid A univ)
    (T : Finset ι) : prob Q (avoid A T) = 1 := by
  rw [← hQ.sum_eq_one, prob]
  refine sum_congr rfl fun ω _ ↦ ?_
  by_cases h : Q ω = 0
  · simp [Set.indicator, h]
  · exact Set.indicator_of_mem (avoid_anti (subset_univ T) (hQZ ω h)) Q

omit [DecidableEq ι] in
/-- A weight carried by `Z_ι` gives no mass to `A_s` (`results/vplusb-contra.md` (2e62e83) §1). -/
theorem prob_eq_zero_of_supp (hQZ : ∀ ω, Q ω ≠ 0 → ω ∈ avoid A univ) {S : Set Ω} {s : ι}
    (hS : S ⊆ A s) : prob Q S = 0 := by
  rw [prob]
  refine sum_eq_zero fun ω _ ↦ ?_
  by_cases h : Q ω = 0
  · simp [Set.indicator, h]
  · exact Set.indicator_of_notMem (fun hω ↦ hQZ ω h s (mem_univ s) (hS hω)) Q

variable (hP : IsProb P) (hQ : IsProb Q) (hQZ : ∀ ω, Q ω ≠ 0 → ω ∈ avoid A univ) {ε : ℝ}
  (hε0 : 0 ≤ ε) (hε1 : ε < 1) {T : Finset ι} (hu : 0 < prob P (avoid A T))
include hP hQ hQZ hε0 hε1 hu

omit hP hε0 hε1 hu in
omit [DecidableEq ι] in
/-- `U′(Z_T) = (1 - ε) U(Z_T) + ε > 0` (`results/vplusb-contra.md` (2e62e83) §1). -/
theorem prob_avoid_contam :
    prob (contam P Q ε) (avoid A T) = (1 - ε) * prob P (avoid A T) + ε := by
  rw [prob_contam, prob_avoid_of_supp hQ hQZ, mul_one]

omit hP hQ hQZ in
omit [Fintype ι] [DecidableEq ι] in
/-- `(1 - ε) U(Z_T) + ε > 0` (`results/vplusb-contra.md` (2e62e83) §1). -/
theorem mixDen_pos : 0 < (1 - ε) * prob P (avoid A T) + ε := by
  have := mul_pos (by linarith : (0 : ℝ) < 1 - ε) hu
  linarith

omit hP hQ hQZ in
omit [Fintype ι] [DecidableEq ι] in
/-- `0 ≤ θ_T < 1` (`results/vplusb-contra.md` (2e62e83) §1). -/
theorem mixTheta_mem : 0 ≤ mixTheta P A T ε ∧ mixTheta P A T ε < 1 := by
  have hD := mixDen_pos hε0 hε1 hu
  have := mul_pos (by linarith : (0 : ℝ) < 1 - ε) hu
  refine ⟨div_nonneg hε0 hD.le, (div_lt_one hD).2 (by linarith)⟩

omit hP hQ hQZ in
omit [Fintype ι] [DecidableEq ι] in
/-- `(1 - ε) / ((1 - ε) U(Z_T) + ε) = (1 - θ_T) / U(Z_T)` (`results/vplusb-contra.md` (2e62e83),
proof of Proposition C2). -/
theorem one_sub_mixTheta :
    (1 - ε) / ((1 - ε) * prob P (avoid A T) + ε) = (1 - mixTheta P A T ε) / prob P (avoid A T) := by
  have hD := (mixDen_pos hε0 hε1 hu).ne'
  rw [mixTheta, one_sub_div hD]
  field_simp
  ring

omit hP in
omit [DecidableEq ι] in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83): `f′_s(T) = (1 - θ_T) f_s(T)`. -/
theorem condProb_contam (s : ι) :
    condProb (contam P Q ε) A T s = (1 - mixTheta P A T ε) * condProb P A T s := by
  rw [condProb, prob_contam, prob_eq_zero_of_supp hQZ Set.inter_subset_left,
    prob_avoid_contam hQ hQZ, condProb, mul_zero, add_zero, mul_div_right_comm,
    one_sub_mixTheta hε0 hε1 hu]
  ring

omit hP in
omit [DecidableEq ι] in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83): `U′(A_s A_t | Z_T)` is
`(1 - θ_T) U(A_s A_t | Z_T)`. -/
theorem condPair_contam (s t : ι) :
    condPair (contam P Q ε) A T s t = (1 - mixTheta P A T ε) * condPair P A T s t := by
  rw [condPair, prob_contam,
    prob_eq_zero_of_supp hQZ (Set.inter_subset_left.trans Set.inter_subset_left),
    prob_avoid_contam hQ hQZ, condPair, mul_zero, add_zero, mul_div_right_comm,
    one_sub_mixTheta hε0 hε1 hu]
  ring

omit hP in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83): `M′_T = (1 - θ_T) M_T`. -/
theorem condMean_contam :
    condMean (contam P Q ε) A T = (1 - mixTheta P A T ε) * condMean P A T := by
  rw [condMean, condMean, mul_sum]
  exact sum_congr rfl fun s _ ↦ condProb_contam hQ hQZ hε0 hε1 hu s

omit hP in
omit [DecidableEq ι] in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83): the relative pair correlation
becomes `ρ′ = (ρ + θ_T) / (1 - θ_T)` whenever `f_s(T) f_t(T) ≠ 0`. -/
theorem pairRatio_contam {s t : ι} (hf : condProb P A T s * condProb P A T t ≠ 0) :
    pairRatio (contam P Q ε) A T s t - 1 =
      (pairRatio P A T s t - 1 + mixTheta P A T ε) / (1 - mixTheta P A T ε) := by
  have hθ := (mixTheta_mem hε0 hε1 hu (P := P) (A := A)).2
  have h1 : 1 - mixTheta P A T ε ≠ 0 := by linarith
  have hf' : condProb (contam P Q ε) A T s * condProb (contam P Q ε) A T t ≠ 0 := by
    rw [condProb_contam hQ hQZ hε0 hε1 hu, condProb_contam hQ hQZ hε0 hε1 hu]
    exact mul_ne_zero (mul_ne_zero h1 (left_ne_zero_of_mul hf))
      (mul_ne_zero h1 (right_ne_zero_of_mul hf))
  rw [pairRatio, ite_eq_right hf', pairRatio, ite_eq_right hf, condPair_contam hQ hQZ hε0 hε1 hu,
    condProb_contam hQ hQZ hε0 hε1 hu, condProb_contam hQ hQZ hε0 hε1 hu]
  field_simp
  ring

/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83):
`V′_T = (1 - θ_T) V_T + θ_T (1 - θ_T) M_T²`. -/
theorem condVar_contam :
    condVar (contam P Q ε) A T =
      (1 - mixTheta P A T ε) * condVar P A T +
        mixTheta P A T ε * (1 - mixTheta P A T ε) * condMean P A T ^ 2 := by
  set θ := mixTheta P A T ε
  set M' := condMean (contam P Q ε) A T
  have hD := (mixDen_pos hε0 hε1 hu).ne'
  have hM' : M' = (1 - θ) * condMean P A T := condMean_contam hQ hQZ hε0 hε1 hu
  have hQs : ∑ ω, (avoid A T).indicator Q ω * (eventCount A ω - M') ^ 2 = M' ^ 2 := by
    rw [← mul_one (M' ^ 2), ← hQ.sum_eq_one, mul_sum]
    refine sum_congr rfl fun ω _ ↦ ?_
    by_cases h : Q ω = 0
    · simp [Set.indicator, h]
    · have h0 := hQZ ω h
      rw [Set.indicator_of_mem (avoid_anti (subset_univ T) h0),
        eventCount_of_mem_avoid_univ h0, zero_sub, neg_sq, mul_comm]
  have hsplit : ∑ ω, (avoid A T).indicator (contam P Q ε) ω * (eventCount A ω - M') ^ 2 =
      (1 - ε) * ∑ ω, (avoid A T).indicator P ω * (eventCount A ω - M') ^ 2 +
        ε * ∑ ω, (avoid A T).indicator Q ω * (eventCount A ω - M') ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ ↦ ?_
    by_cases h : ω ∈ avoid A T
    · simp only [Set.indicator, h, ↓reduceIte, contam]
      ring
    · simp [Set.indicator, h]
  rw [condVar, hsplit, hQs, sum_avoid_mul_sq_sub hP T hu.ne', prob_avoid_contam hQ hQZ,
    hM']
  have e1 : (1 - ε) * prob P (avoid A T) / ((1 - ε) * prob P (avoid A T) + ε) = 1 - θ := by
    rw [mul_div_right_comm, one_sub_mixTheta hε0 hε1 hu, div_mul_cancel₀ _ hu.ne']
  have e2 : ε / ((1 - ε) * prob P (avoid A T) + ε) = θ := rfl
  have e3 : ((1 - ε) * ((condVar P A T + (condMean P A T - (1 - θ) * condMean P A T) ^ 2) *
      prob P (avoid A T)) + ε * ((1 - θ) * condMean P A T) ^ 2) /
        ((1 - ε) * prob P (avoid A T) + ε) =
      (1 - ε) * prob P (avoid A T) / ((1 - ε) * prob P (avoid A T) + ε) *
        (condVar P A T + (condMean P A T - (1 - θ) * condMean P A T) ^ 2) +
      ε / ((1 - ε) * prob P (avoid A T) + ε) * ((1 - θ) * condMean P A T) ^ 2 := by
    ring
  rw [e3, e1, e2]
  ring

omit hP in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83):
`B′_T = (1 - θ_T)(B_T + θ_T S₂)` with `S₂ = ∑_{s ∉ T} f_s(T)²`. -/
theorem bernVarSum_contam :
    bernVarSum (contam P Q ε) A T =
      (1 - mixTheta P A T ε) *
        (bernVarSum P A T + mixTheta P A T ε * ∑ s ∈ Tᶜ, condProb P A T s ^ 2) := by
  have e : ∀ s, condProb (contam P Q ε) A T s * (1 - condProb (contam P Q ε) A T s) =
      (1 - mixTheta P A T ε) * (condProb P A T s * (1 - condProb P A T s) +
        mixTheta P A T ε * condProb P A T s ^ 2) := fun s ↦ by
    rw [condProb_contam hQ hQZ hε0 hε1 hu]
    ring
  rw [bernVarSum, bernVarSum, sum_congr rfl fun s _ ↦ e s, ← mul_sum, sum_add_distrib, ← mul_sum]

/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83):
`V′_T / B′_T = (V_T + θ_T M_T²) / (B_T + θ_T S₂)`. -/
theorem condVar_div_bernVarSum_contam :
    condVar (contam P Q ε) A T / bernVarSum (contam P Q ε) A T =
      (condVar P A T + mixTheta P A T ε * condMean P A T ^ 2) /
        (bernVarSum P A T + mixTheta P A T ε * ∑ s ∈ Tᶜ, condProb P A T s ^ 2) := by
  have hθ := (mixTheta_mem hε0 hε1 hu (P := P) (A := A)).2
  rw [condVar_contam hP hQ hQZ hε0 hε1 hu, bernVarSum_contam hQ hQZ hε0 hε1 hu,
    show (1 - mixTheta P A T ε) * condVar P A T +
      mixTheta P A T ε * (1 - mixTheta P A T ε) * condMean P A T ^ 2 =
        (1 - mixTheta P A T ε) * (condVar P A T + mixTheta P A T ε * condMean P A T ^ 2) by ring,
    mul_div_mul_left _ _ (by linarith)]

omit hQ hQZ hε0 hε1 hu in
/-- `S₂ = ∑_{s ∉ T} f_s(T)² ≤ M_T` (`results/vplusb-contra.md` (2e62e83), proof of
Proposition C2(a)). -/
theorem sum_condProb_sq_le_condMean : ∑ s ∈ Tᶜ, condProb P A T s ^ 2 ≤ condMean P A T := by
  rw [condMean]
  refine sum_le_sum fun s _ ↦ ?_
  have h0 := condProb_nonneg hP (A := A) T s
  have h1 := condProb_le_one hP (A := A) T s
  nlinarith

omit hP hQ hQZ hε0 hε1 hu in
/-- `M_T > 0` gives `S₂ = ∑_{s ∉ T} f_s(T)² > 0` (`results/vplusb-contra.md` (2e62e83), proof of
Proposition C2(a)). -/
theorem sum_condProb_sq_pos (hM : 0 < condMean P A T) : 0 < ∑ s ∈ Tᶜ, condProb P A T s ^ 2 := by
  obtain ⟨s, hs, hfs⟩ : ∃ s ∈ Tᶜ, condProb P A T s ≠ 0 := by
    by_contra hc
    push Not at hc
    have : condMean P A T = 0 := sum_eq_zero fun s hs ↦ hc s hs
    linarith
  exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfs)))
    (single_le_sum (f := fun s ↦ condProb P A T s ^ 2) (fun _ _ ↦ sq_nonneg _) hs)

omit hP hQ hQZ hε0 hε1 hu in
omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The inequality `(V + θ M²) / (B + θ S₂) ≥ θ M / (1 + θ)` for `V ≥ 0`, `0 ≤ B ≤ M`,
`0 ≤ S₂ ≤ M`, `θ ≥ 0`, with `S₂ > 0` when `θ M > 0` (`results/vplusb-contra.md` (2e62e83), proof of
Proposition C2(a)). -/
theorem mul_div_one_add_le_div {V B M S θ : ℝ} (hV : 0 ≤ V) (hB : 0 ≤ B) (hBM : B ≤ M)
    (hS0 : 0 ≤ S) (hS : S ≤ M) (hθ : 0 ≤ θ) (hSpos : 0 < θ * M → 0 < S) :
    θ * M / (1 + θ) ≤ (V + θ * M ^ 2) / (B + θ * S) := by
  have hM : 0 ≤ M := hB.trans hBM
  rcases eq_or_lt_of_le (mul_nonneg hθ hM) with h0 | h0
  · rw [← h0, zero_div]
    exact div_nonneg (add_nonneg hV (mul_nonneg hθ (sq_nonneg M))) (add_nonneg hB
      (mul_nonneg hθ hS0))
  have hθ0 : 0 < θ := pos_of_mul_pos_left h0 hM
  have hS2 := hSpos h0
  rw [div_le_div_iff₀ (by linarith) (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hBM h0.le, mul_le_mul_of_nonneg_left hS
    (mul_nonneg (mul_nonneg hθ0.le hθ0.le) hM), mul_nonneg hV (by linarith : (0 : ℝ) ≤ 1 + θ)]

/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83):
`V′_T / B′_T ≥ θ_T M_T / (1 + θ_T)`. -/
theorem div_le_condVar_div_bernVarSum_contam :
    mixTheta P A T ε * condMean P A T / (1 + mixTheta P A T ε) ≤
      condVar (contam P Q ε) A T / bernVarSum (contam P Q ε) A T := by
  rw [condVar_div_bernVarSum_contam hP hQ hQZ hε0 hε1 hu]
  have hθ := mixTheta_mem hε0 hε1 hu (P := P) (A := A)
  exact mul_div_one_add_le_div (condVar_nonneg hP T) (bernVarSum_nonneg hP T)
    (bernVarSum_le_condMean hP T) (sum_nonneg fun s _ ↦ sq_nonneg _)
    (sum_condProb_sq_le_condMean hP) hθ.1
    fun h ↦ sum_condProb_sq_pos (pos_of_mul_pos_right h hθ.1)

/-- Theorem C3 of `results/vplusb-contra.md` (2e62e83), the (V+_B) bar: if `0 ≤ κ` and
`κ (1 + θ_T) < θ_T M_T^U`, then the contaminated law violates (V+_B) with constant `κ` at `T`,
`V′_T > κ B′_T`. -/
theorem lt_condVar_contam {κ : ℝ} (hκ : 0 ≤ κ)
    (h : κ * (1 + mixTheta P A T ε) < mixTheta P A T ε * condMean P A T) :
    κ * bernVarSum (contam P Q ε) A T < condVar (contam P Q ε) A T := by
  have hθ := mixTheta_mem hε0 hε1 hu (P := P) (A := A)
  have hθ0 : 0 < mixTheta P A T ε * condMean P A T :=
    lt_of_le_of_lt (mul_nonneg hκ (by linarith [hθ.1])) h
  have hM := condMean_nonneg hP (A := A) T
  have hθp : 0 < mixTheta P A T ε := pos_of_mul_pos_left hθ0 hM
  have hMp : 0 < condMean P A T := pos_of_mul_pos_right hθ0 hθ.1
  have hB : 0 < bernVarSum (contam P Q ε) A T := by
    rw [bernVarSum_contam hQ hQZ hε0 hε1 hu]
    exact mul_pos (by linarith [hθ.2]) (add_pos_of_nonneg_of_pos (bernVarSum_nonneg hP T)
      (mul_pos hθp (sum_condProb_sq_pos hMp)))
  have h1 := div_le_condVar_div_bernVarSum_contam hP hQ hQZ hε0 hε1 hu
  have h2 : κ < mixTheta P A T ε * condMean P A T / (1 + mixTheta P A T ε) := by
    rw [lt_div_iff₀ (by linarith)]
    exact h
  rw [← lt_div_iff₀ hB]
  linarith

/-- Theorem C3 of `results/vplusb-contra.md` (2e62e83), the particular case: if `0 ≤ κ`,
`0 < ε`, `(1 - ε) U(Z_T) ≤ ε` (so `θ_T ≥ 1/2`) and `3 κ < M_T^U`, the contaminated law has
`V′_T > κ B′_T`. -/
theorem lt_condVar_contam_of_le {κ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hsmall : (1 - ε) * prob P (avoid A T) ≤ ε) (hM : 3 * κ < condMean P A T) :
    κ * bernVarSum (contam P Q ε) A T < condVar (contam P Q ε) A T := by
  refine lt_condVar_contam hP hQ hQZ hε0 hε1 hu hκ ?_
  have hD := mixDen_pos hε0 hε1 hu (P := P) (A := A)
  have hθ : 1 / 2 ≤ mixTheta P A T ε := by
    rw [mixTheta, le_div_iff₀ hD]
    linarith
  have hθ1 := (mixTheta_mem hε0 hε1 hu (P := P) (A := A)).2
  nlinarith

end PropositionC2

section Split

/-- `U(· | X ≥ 1)`, the weight `1_{Z_ιᶜ} U / (1 - q)` of `results/vplusb-contra.md` (2e62e83),
Proposition C2(b). -/
noncomputable def posPart (P : Ω → ℝ) (A : ι → Set Ω) (ω : Ω) : ℝ :=
  (avoid A univ)ᶜ.indicator P ω / (1 - prob P (avoid A univ))

/-- `U(· | X = 0)`, the weight `1_{Z_ι} U / q` of `results/vplusb-contra.md` (2e62e83),
Proposition C2(b). -/
noncomputable def zeroPart (P : Ω → ℝ) (A : ι → Set Ω) (ω : Ω) : ℝ :=
  (avoid A univ).indicator P ω / prob P (avoid A univ)

omit [DecidableEq ι] in
/-- `U = (1 - q) U(· | X ≥ 1) + q U(· | X = 0)` for `0 < q < 1` (`results/vplusb-contra.md`
(2e62e83), Proposition C2(b)). -/
theorem posPart_contam_zeroPart (hq0 : 0 < prob P (avoid A univ))
    (hq1 : prob P (avoid A univ) < 1) :
    contam (posPart P A) (zeroPart P A) (prob P (avoid A univ)) = P := by
  funext ω
  have h1 : 1 - prob P (avoid A univ) ≠ 0 := by linarith
  rw [contam, posPart, zeroPart, mul_div_cancel₀ _ h1, mul_div_cancel₀ _ hq0.ne']
  by_cases h : ω ∈ avoid A univ <;> simp [Set.indicator, h]

omit [DecidableEq ι] in
/-- `U(· | X ≥ 1)` is a probability weight for `q < 1` (`results/vplusb-contra.md` (2e62e83),
Proposition C2(b)). -/
theorem isProb_posPart (hP : IsProb P) (hq1 : prob P (avoid A univ) < 1) :
    IsProb (posPart P A) where
  nonneg ω := div_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω) (by linarith)
  sum_eq_one := by
    have h := prob_eq_inter_add_diff P Set.univ (avoid A univ)
    rw [prob_univ hP, Set.inter_univ, ← Set.compl_eq_univ_sdiff] at h
    simp only [posPart]
    rw [← sum_div, div_eq_one_iff_eq (by linarith)]
    change prob P (avoid A univ)ᶜ = _
    linarith

omit [DecidableEq ι] in
/-- `U(· | X = 0)` is a probability weight for `q > 0` (`results/vplusb-contra.md` (2e62e83),
Proposition C2(b)). -/
theorem isProb_zeroPart (hP : IsProb P) (hq0 : 0 < prob P (avoid A univ)) :
    IsProb (zeroPart P A) where
  nonneg ω := div_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω) hq0.le
  sum_eq_one := by
    simp only [zeroPart]
    rw [← sum_div, div_eq_one_iff_eq hq0.ne']
    rfl

omit [DecidableEq ι] in
/-- `U(· | X = 0)` is carried by `Z_ι` (`results/vplusb-contra.md` (2e62e83),
Proposition C2(b)). -/
theorem zeroPart_supp (ω : Ω) (h : zeroPart P A ω ≠ 0) : ω ∈ avoid A univ := by
  by_contra hω
  exact h (by simp [zeroPart, Set.indicator, hω])

omit [DecidableEq ι] in
/-- `θ_T = q / U(Z_T)` for the split `U = (1 - q) U(· | X ≥ 1) + q U(· | X = 0)`
(`results/vplusb-contra.md` (2e62e83), Proposition C2(b)). -/
theorem mixTheta_posPart (hP : IsProb P) (hq0 : 0 < prob P (avoid A univ))
    (hq1 : prob P (avoid A univ) < 1) (T : Finset ι) :
    mixTheta (posPart P A) A T (prob P (avoid A univ)) =
      prob P (avoid A univ) / prob P (avoid A T) := by
  have h := prob_contam (posPart P A) (zeroPart P A) (prob P (avoid A univ)) (avoid A T)
  rw [posPart_contam_zeroPart hq0 hq1,
    prob_avoid_of_supp (isProb_zeroPart hP hq0) zeroPart_supp, mul_one] at h
  rw [mixTheta, ← h]

omit [DecidableEq ι] in
/-- `U(Z_T ∩ {X ≥ 1}) > 0` when `q < U(Z_T)` (`results/vplusb-contra.md` (2e62e83),
Proposition C2(b)). -/
theorem prob_avoid_posPart_pos (hP : IsProb P) (hq0 : 0 < prob P (avoid A univ))
    (hq1 : prob P (avoid A univ) < 1) {T : Finset ι}
    (hqT : prob P (avoid A univ) < prob P (avoid A T)) : 0 < prob (posPart P A) (avoid A T) := by
  have h := prob_contam (posPart P A) (zeroPart P A) (prob P (avoid A univ)) (avoid A T)
  rw [posPart_contam_zeroPart hq0 hq1,
    prob_avoid_of_supp (isProb_zeroPart hP hq0) zeroPart_supp, mul_one] at h
  by_contra hc
  push Not at hc
  nlinarith

/-- Proposition C2(b) of `results/vplusb-contra.md` (2e62e83), the exact split of (V+_B). Let
`0 < q < U(Z_T)` and `q < 1`, `θ₀ = q / U(Z_T) = ν_T(X = 0)`, and write `V_+`, `B_+`, `M_+`,
`S₂₊` for the quantities of `ν_T(· | X ≥ 1)`. Then `V_T ≤ κ B_T` if and only if
`θ₀ (M_+² - κ S₂₊) ≤ κ B_+ - V_+`. -/
theorem condVar_le_iff (hP : IsProb P) (hq0 : 0 < prob P (avoid A univ))
    (hq1 : prob P (avoid A univ) < 1) {T : Finset ι}
    (hqT : prob P (avoid A univ) < prob P (avoid A T)) (κ : ℝ) :
    condVar P A T ≤ κ * bernVarSum P A T ↔
      prob P (avoid A univ) / prob P (avoid A T) *
          (condMean (posPart P A) A T ^ 2 -
            κ * ∑ s ∈ Tᶜ, condProb (posPart P A) A T s ^ 2) ≤
        κ * bernVarSum (posPart P A) A T - condVar (posPart P A) A T := by
  have hP' := isProb_posPart hP hq1 (A := A)
  have hQ := isProb_zeroPart hP hq0 (A := A)
  have hu := prob_avoid_posPart_pos hP hq0 hq1 hqT
  have hV := condVar_contam hP' hQ zeroPart_supp hq0.le hq1 hu
  have hB := bernVarSum_contam hQ zeroPart_supp hq0.le hq1 hu
  have hθ := mixTheta_mem hq0.le hq1 hu (P := posPart P A) (A := A)
  rw [posPart_contam_zeroPart hq0 hq1, mixTheta_posPart hP hq0 hq1] at hV hB
  rw [mixTheta_posPart hP hq0 hq1] at hθ
  rw [hV, hB]
  set θ := prob P (avoid A univ) / prob P (avoid A T)
  have h1 : 0 < 1 - θ := by linarith [hθ.2]
  constructor
  · intro h
    have h' : (1 - θ) * (condVar (posPart P A) A T + θ * condMean (posPart P A) A T ^ 2) ≤
        (1 - θ) * (κ * (bernVarSum (posPart P A) A T +
          θ * ∑ s ∈ Tᶜ, condProb (posPart P A) A T s ^ 2)) := by
      linarith
    have := le_of_mul_le_mul_left h' h1
    linarith
  · intro h
    have h' : condVar (posPart P A) A T + θ * condMean (posPart P A) A T ^ 2 ≤
        κ * (bernVarSum (posPart P A) A T + θ * ∑ s ∈ Tᶜ, condProb (posPart P A) A T s ^ 2) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h' h1.le]

end Split

section Intersections

variable {Q : Ω → ℝ}

omit [DecidableEq ι] in
/-- Proposition C2(a) of `results/vplusb-contra.md` (2e62e83) at `T = ∅` (Theorem C3 item 1):
every relative joint moment scales as `R′_S = R_S / (1 - ε)^(|S| - 1)` for nonempty `S`. -/
theorem interRatio_contam (hQZ : ∀ ω, Q ω ≠ 0 → ω ∈ avoid A univ) {ε : ℝ} (hε1 : ε < 1)
    {S : Finset ι} (hS : S.Nonempty) :
    interRatio (contam P Q ε) A S = interRatio P A S / (1 - ε) ^ (S.card - 1) := by
  have h1 : 1 - ε ≠ 0 := by linarith
  obtain ⟨t₀, ht₀⟩ := hS
  have hI : prob Q (interSet A S) = 0 :=
    prob_eq_zero_of_supp hQZ (s := t₀) fun ω hω ↦ hω t₀ ht₀
  have hA : ∀ t, prob Q (A t) = 0 := fun t ↦ prob_eq_zero_of_supp hQZ (s := t) subset_rfl
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by have := card_pos.mpr ⟨t₀, ht₀⟩; omega⟩
  rw [interRatio, interRatio, prob_contam, hI, mul_zero, add_zero,
    prod_congr rfl fun t _ ↦ by rw [prob_contam, hA, mul_zero, add_zero], prod_mul_distrib,
    prod_const, hk, Nat.add_sub_cancel, pow_succ]
  by_cases hpr : ∏ t ∈ S, prob P (A t) = 0
  · simp [hpr]
  · field_simp

end Intersections

end Barrier

end Pairing
