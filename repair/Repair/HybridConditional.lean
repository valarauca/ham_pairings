import Mathlib.Data.Nat.Choose.Vandermonde
import Repair.CumulantTail
import Suppression.Density
import Suppression.Prob
import Suppression.Tilt

/-!
# The hybrid-tail route: the conditional theorem (`hybrid-assembly.md`)

Formal parts of `results/hybrid-assembly.md` (COD-232) beyond the probability core of
`CumulantTail.lean`. Notation is that of the note: `M = m - 3` kept factor edges, `d'` the size of
the defect set `E'`, `N = 3 + j0 + j1` and `X` the number of Hamiltonian factors of `P_Λ`, with
`X ≤ n - 1`.

The pattern law `Λ_(j0, j1)` and the random hybrid `H` are not built here. Each pattern enters as
an abstract finite probability space `(Ω j0 j1, P j0 j1)` carrying the count `X j0 j1` and the event
`B j0 j1 = {E' ∈ 𝔅}`. Proposition 2 (the union over repair patterns) and Lemma 5 (the per-pattern
mean) are the hypotheses `hunion` and `hmean` of the assembly theorems, and (H-JI) is the structure
`HJI`.

* `patternCount M d K` : `Π_K = ∑_(j0 + j1 ≤ K) C(M, j0) C(d', j1) (2N - 1)!!`.
* `patternCount_eq`, `patternCount_le` (Lemma 3) : `Π_K = ∑_(j ≤ K) C(M + d', j) (2j + 5)!!
  ≤ (K + 1)(2K + 5)³ (2(M + d'))^K`.
* `condLaw P B X` : the law of `X` under `P(· | Bᶜ)`, the law `Λ^𝔅` of §2.
  `le_partialMean_condLaw` is the last step of the proof of Lemma 5,
  `E[X | Bᶜ] ≥ E X - (n - 1) P(B)`.
* `HJI` : the hypothesis (H-JI) of §2, for every pattern `j0 + j1 ≤ K`.
* `prob_le_of_hji` (Theorem 1, finite form) : Proposition 2, Lemma 5 and (H-JI) give
  `P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + Π_K (4e H k / μ_*)^k` with `μ_* = πδ(n - 1) / (80√d')`, and
  `prob_le_of_hji'` replaces `Π_K` by the bound of Lemma 3.
* `prob_zero_le_exp_of_tiltVar_le` (proof of Theorem 1') : (H-T) on one pattern gives
  `P_Λ(X = 0) ≤ exp(-μ_Λ / κ_T)`, through `Tilt.le_exp_neg_div_of_le_fano`.
* `prob_le_of_tilt` (Theorem 1', finite form) : Proposition 2 with `𝔅 = ∅`, Lemma 5 and (H-T) give
  `P_H(ρ(H) ≤ K) ≤ Π_K exp(-πδ(n - 1) / (40√d' κ_T))`.
-/

namespace Pairing

namespace HybridConditional

open Finset Nat SizeBias ChainRule CumulantTail

section PatternCount

/-- `(2j + 5)!! = (2j + 5)(2j + 3)(2j + 1)(2j - 1)!!`. -/
theorem doubleFactorial_two_mul_add_five (j : ℕ) :
    (2 * j + 5).doubleFactorial =
      (2 * j + 5) * (2 * j + 3) * (2 * j + 1) * (2 * j - 1).doubleFactorial := by
  rw [show 2 * j + 5 = 2 * j + 3 + 2 by omega, doubleFactorial_add_two,
    show 2 * j + 3 = 2 * j + 1 + 2 by omega, doubleFactorial_add_two]
  rcases j with _ | j
  · rfl
  · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega, doubleFactorial_add_two,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    ring

/-- The pattern count `Π_K = ∑_(j0 + j1 ≤ K) C(M, j0) C(d', j1) (2N - 1)!!` with
`N = 3 + j0 + j1` (`hybrid-assembly.md`, Proposition 2 and Lemma 3). -/
def patternCount (M d K : ℕ) : ℕ :=
  ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
    M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial

/-- Lemma 3 of `hybrid-assembly.md`, the Vandermonde step:
`Π_K = ∑_(j ≤ K) C(M + d', j) (2j + 5)!!`. -/
theorem patternCount_eq (M d K : ℕ) :
    patternCount M d K = ∑ j ∈ range (K + 1), (M + d).choose j * (2 * j + 5).doubleFactorial := by
  refine sum_congr rfl fun j _ ↦ ?_
  rw [Nat.add_choose_eq, sum_mul]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [show 2 * (3 + x.1 + x.2) - 1 = 2 * j + 5 by have := mem_antidiagonal.mp hx; omega]

/-- Lemma 3 of `hybrid-assembly.md` (pattern count). For `M + d' ≥ 1`,
`Π_K ≤ (K + 1)(2K + 5)³ (2(M + d'))^K`. -/
theorem patternCount_le {M d : ℕ} (hMd : 0 < M + d) (K : ℕ) :
    patternCount M d K ≤ (K + 1) * (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K := by
  rw [patternCount_eq]
  calc ∑ j ∈ range (K + 1), (M + d).choose j * (2 * j + 5).doubleFactorial
      ≤ ∑ _j ∈ range (K + 1), (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K := by
        refine sum_le_sum fun j hj ↦ ?_
        have hjK := Nat.lt_succ_iff.mp (mem_range.mp hj)
        rw [doubleFactorial_two_mul_add_five]
        calc (M + d).choose j * ((2 * j + 5) * (2 * j + 3) * (2 * j + 1) *
              (2 * j - 1).doubleFactorial)
            = ((2 * j + 5) * (2 * j + 3) * (2 * j + 1)) *
                ((M + d).choose j * (2 * j - 1).doubleFactorial) := by ring
          _ ≤ ((2 * K + 5) * (2 * K + 5) * (2 * K + 5)) * (2 * (M + d)) ^ K :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
                ((choose_mul_doubleFactorial_le (M + d) j).trans
                  (Nat.pow_le_pow_right (by omega) hjK))
          _ = (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K := by ring
    _ = (K + 1) * (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K := by
        rw [sum_const, card_range, smul_eq_mul, mul_assoc]

end PatternCount

section CondLaw

variable {Ω : Type*} [Fintype Ω]

/-- The law `j ↦ P(X = j, Bᶜ) / P(Bᶜ)` of `X` under `P(· | Bᶜ)`. With `B = {E' ∈ 𝔅}` it is the
law of `X` under `Λ^𝔅` (`hybrid-assembly.md`, §2). -/
noncomputable def condLaw (P : Ω → ℝ) (B : Set Ω) (X : Ω → ℕ) (j : ℕ) : ℝ :=
  lawOf (Bᶜ.indicator P) X j / prob P Bᶜ

/-- `∑_ω 1_(Bᶜ)(ω) P ω = P(Bᶜ)`. -/
theorem sum_indicator_eq_prob (P : Ω → ℝ) (B : Set Ω) : ∑ ω, Bᶜ.indicator P ω = prob P Bᶜ :=
  rfl

/-- The law of `X ≤ N` under `P(· | Bᶜ)` is a law on `[0, N]` when `P(Bᶜ) > 0`. -/
theorem isLaw_condLaw {P : Ω → ℝ} (hP : IsProb P) {B : Set Ω} (hB : 0 < prob P Bᶜ) {X : Ω → ℕ}
    {N : ℕ} (hX : ∀ ω, X ω ≤ N) : IsLaw (condLaw P B X) N where
  nonneg j := div_nonneg (by
    rw [lawOf_eq_sum]
    exact sum_nonneg fun ω _ ↦ Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω) hB.le
  eq_zero j hj := by
    rw [condLaw, lawOf_eq_sum, sum_eq_zero fun ω hω ↦ absurd (mem_filter.mp hω).2
      (by have := hX ω; omega), zero_div]
  sum_eq_one := by
    have h := sum_mul_lawOf (Bᶜ.indicator P) hX fun _ ↦ 1
    simp only [mul_one] at h
    simp only [condLaw, div_eq_mul_inv]
    rw [← sum_mul, ← h, sum_indicator_eq_prob, mul_inv_cancel₀ hB.ne']

/-- `P(Bᶜ) = 1 - P(B)`. -/
theorem prob_compl_eq {P : Ω → ℝ} (hP : IsProb P) (B : Set Ω) : prob P Bᶜ = 1 - prob P B := by
  rw [← hP.sum_eq_one, prob, prob, eq_sub_iff_add_eq, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ ↦ by rw [add_comm, Set.indicator_self_add_compl_apply]

/-- The mean of `X` under `P(· | Bᶜ)`: `E[X | Bᶜ] = ∑_ω 1_(Bᶜ)(ω) P ω X ω / P(Bᶜ)`. -/
theorem partialMean_condLaw (P : Ω → ℝ) (B : Set Ω) {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) :
    partialMean (condLaw P B X) N = (∑ ω, Bᶜ.indicator P ω * X ω) / prob P Bᶜ := by
  rw [sum_mul_lawOf (Bᶜ.indicator P) hX fun j ↦ (j : ℝ), partialMean, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [condLaw, div_eq_mul_inv]
  ring

/-- `E X = ∑_ω P ω X ω` is the mean of the law of `X`. -/
theorem partialMean_lawOf (P : Ω → ℝ) {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) :
    partialMean (lawOf P X) N = ∑ ω, P ω * X ω := by
  rw [sum_mul_lawOf P hX fun j ↦ (j : ℝ), partialMean]
  exact sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The last step of the proof of Lemma 5 of `hybrid-assembly.md`. If `X ≤ N` and `P(Bᶜ) > 0`,
then `E[X | Bᶜ] ≥ E X - N P(B)`. -/
theorem le_partialMean_condLaw {P : Ω → ℝ} (hP : IsProb P) {B : Set Ω} (hB : 0 < prob P Bᶜ)
    {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) :
    ∑ ω, P ω * X ω - N * prob P B ≤ partialMean (condLaw P B X) N := by
  have hS : 0 ≤ ∑ ω, Bᶜ.indicator P ω * X ω :=
    sum_nonneg fun ω _ ↦ mul_nonneg (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω)
      (Nat.cast_nonneg _)
  have hsplit : ∑ ω, P ω * X ω =
      ∑ ω, B.indicator P ω * X ω + ∑ ω, Bᶜ.indicator P ω * X ω := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun ω _ ↦ by rw [← add_mul, Set.indicator_self_add_compl_apply]
  have hbad : ∑ ω, B.indicator P ω * X ω ≤ N * prob P B := by
    rw [prob, mul_sum]
    exact sum_le_sum fun ω _ ↦ by
      rw [mul_comm (N : ℝ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hX ω)
        (Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω)
  rw [partialMean_condLaw P B hX]
  calc ∑ ω, P ω * X ω - N * prob P B ≤ ∑ ω, Bᶜ.indicator P ω * X ω := by linarith
    _ ≤ (∑ ω, Bᶜ.indicator P ω * X ω) / prob P Bᶜ := le_div_self hS hB (prob_le_one hP _)

/-- `P(X = j, Bᶜ) ≤ P(X = j | Bᶜ)`, the step from `P_Λ(X = 0, E' ∉ 𝔅)` to `P_(Λ^𝔅)(X = 0)` in
Theorem 1 of `hybrid-assembly.md`. -/
theorem lawOf_indicator_le_condLaw {P : Ω → ℝ} (hP : IsProb P) {B : Set Ω} (hB : 0 < prob P Bᶜ)
    (X : Ω → ℕ) (j : ℕ) : lawOf (Bᶜ.indicator P) X j ≤ condLaw P B X j := by
  refine le_div_self ?_ hB (prob_le_one hP _)
  rw [lawOf_eq_sum]
  exact sum_nonneg fun ω _ ↦ Set.indicator_nonneg (fun ω _ ↦ hP.nonneg ω) ω

end CondLaw

section Assembly

variable {Ω : ℕ → ℕ → Type*} [∀ a b, Fintype (Ω a b)]

/-- The hypothesis (H-JI) of `hybrid-assembly.md` §2 (joint incoherence of contexts, averaged over
the defect set), for the patterns `j0 + j1 ≤ K`. Pattern `(j0, j1)` is the finite probability
space `(Ω j0 j1, P j0 j1)` of the law `Λ_(j0, j1)`, with the count `X j0 j1` of Hamiltonian factors
and the event `B j0 j1 = {E' ∈ 𝔅}` of the exceptional family. With `μ = E_(Λ^𝔅) X` the mean of
the law `condLaw` of `X` under `Λ^𝔅 = Λ( · | E' ∉ 𝔅)`, it asks `P(E' ∈ 𝔅) ≤ πδ / (80√d')`,
`H μ ≥ 8k`, and `|κ^f_j(X; Λ^𝔅)| ≤ j! H μ (H μ / (8k))^((j - 2)/2)` for `2 ≤ j ≤ 2k`. `𝔅 = ∅`
is the case `B j0 j1 = ∅`. -/
structure HJI (P : ∀ a b, Ω a b → ℝ) (X : ∀ a b, Ω a b → ℕ) (B : ∀ a b, Set (Ω a b))
    (N d K k : ℕ) (δ H : ℝ) : Prop where
  prob_bad_le : ∀ a b, a + b ≤ K → prob (P a b) (B a b) ≤ Real.pi * δ / (80 * Real.sqrt d)
  le_mean : ∀ a b, a + b ≤ K → 8 * k ≤ H * partialMean (condLaw (P a b) (B a b) (X a b)) N
  factCumulant_le : ∀ a b, a + b ≤ K → ∀ j, 2 ≤ j → j ≤ 2 * k →
    |factCumulant (condLaw (P a b) (B a b) (X a b)) N j| ≤
      j ! * H * partialMean (condLaw (P a b) (B a b) (X a b)) N *
        Real.sqrt (H * partialMean (condLaw (P a b) (B a b) (X a b)) N / (8 * k)) ^ (j - 2)

/-- `πδ / (80√d') < 1` for `δ ≤ 1` and `d' ≥ 1`. -/
theorem pi_mul_div_lt_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    Real.pi * δ / (80 * Real.sqrt d) < 1 := by
  have hs : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  rw [div_lt_one (by positivity)]
  nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The per-pattern bound of Theorem 1 of `hybrid-assembly.md`. Under (H-JI) and the mean bound
of Lemma 5, `P_Λ(X = 0, E' ∉ 𝔅) ≤ (4e H k / μ_*)^k` with `μ_* = πδ(n - 1) / (80√d')`, for every
pattern `j0 + j1 ≤ K`. -/
theorem lawOf_zero_le_of_hji {P : ∀ a b, Ω a b → ℝ} {X : ∀ a b, Ω a b → ℕ}
    {B : ∀ a b, Set (Ω a b)} {N d K k : ℕ} {δ H : ℝ} (hP : ∀ a b, IsProb (P a b))
    (hX : ∀ a b ω, X a b ω ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hN : 0 < N) (hji : HJI P X B N d K k δ H)
    (hmean : ∀ a b, a + b ≤ K → Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b ω * X a b ω)
    {a b : ℕ} (hab : a + b ≤ K) :
    lawOf ((B a b)ᶜ.indicator (P a b)) (X a b) 0 ≤
      (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ := hji.prob_bad_le a b hab
  have hB : 0 < prob (P a b) (B a b)ᶜ := by
    rw [prob_compl_eq (hP a b)]
    linarith [pi_mul_div_lt_one hδ hδ1 hd]
  have hlaw := isLaw_condLaw (hP a b) hB (hX a b)
  have hμs : 0 < Real.pi * δ * N / (80 * Real.sqrt d) := by positivity
  have hμ : Real.pi * δ * N / (80 * Real.sqrt d) ≤
      partialMean (condLaw (P a b) (B a b) (X a b)) N := by
    refine le_trans ?_ (le_partialMean_condLaw (hP a b) hB (hX a b))
    have h1 := hmean a b hab
    have h2 : (N : ℝ) * prob (P a b) (B a b) ≤ N * (Real.pi * δ / (80 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hβ hNr.le
    have h3 : Real.pi * δ * N / (40 * Real.sqrt d) - N * (Real.pi * δ / (80 * Real.sqrt d)) =
        Real.pi * δ * N / (80 * Real.sqrt d) := by
      field_simp
      ring
    linarith
  have h8 := prob_zero_le_of_factCumulant hlaw hH hk (hμs.trans_le hμ) (hji.le_mean a b hab)
    (hji.factCumulant_le a b hab)
  refine (lawOf_indicator_le_condLaw (hP a b) hB (X a b) 0).trans (h8.trans ?_)
  exact pow_le_pow_left₀ (div_nonneg (by positivity) (hμs.trans_le hμ).le)
    (div_le_div_of_nonneg_left (by positivity) hμs hμ) k

/-- Theorem 1 of `hybrid-assembly.md`, finite form, conditional on Proposition 2 and Lemma 5.
Let pattern `(j0, j1)` carry the law `Λ_(j0, j1)` as in `HJI`, with `X ≤ n - 1 = N`. Suppose the
union over repair patterns (Proposition 2, `hunion`),
`P_H(ρ(H) ≤ K) ≤ P(E' ∈ 𝔅) + ∑_(j0 + j1 ≤ K) C(M, j0) C(d', j1) (2N - 1)!! P_Λ(X = 0, E' ∉ 𝔅)`,
the mean bound of Lemma 5 (`hmean`), `μ_Λ ≥ πδ(n - 1) / (40√d')`, `P(E' ∈ 𝔅) ≤ πδ / (80√d')`
under `H` (`hpB`), and (H-JI). Then
`P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + Π_K (4e H k / μ_*)^k` with `μ_* = πδ(n - 1) / (80√d')`. -/
theorem prob_le_of_hji {P : ∀ a b, Ω a b → ℝ} {X : ∀ a b, Ω a b → ℕ} {B : ∀ a b, Set (Ω a b)}
    {N M d K k : ℕ} {δ H PH pB : ℝ} (hP : ∀ a b, IsProb (P a b)) (hX : ∀ a b ω, X a b ω ≤ N)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hH : 1 ≤ H) (hk : 1 ≤ k) (hN : 0 < N)
    (hji : HJI P X B N d K k δ H)
    (hmean : ∀ a b, a + b ≤ K → Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b ω * X a b ω)
    (hpB : pB ≤ Real.pi * δ / (80 * Real.sqrt d))
    (hunion : PH ≤ pB + ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
      ((M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial : ℕ) : ℝ) *
        lawOf ((B x.1 x.2)ᶜ.indicator (P x.1 x.2)) (X x.1 x.2) 0) :
    PH ≤ Real.pi * δ / (80 * Real.sqrt d) + patternCount M d K *
      (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  refine hunion.trans (add_le_add hpB ?_)
  rw [patternCount, cast_sum, sum_mul]
  refine sum_le_sum fun j _ ↦ ?_
  rw [cast_sum, sum_mul]
  refine sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left
    (lawOf_zero_le_of_hji hP hX hδ hδ1 hd hH hk hN hji hmean ?_) (Nat.cast_nonneg _)
  have := mem_antidiagonal.mp hx
  have := mem_range.mp ‹j ∈ range (K + 1)›
  omega

/-- Theorem 1 of `hybrid-assembly.md`, finite form with the pattern count of Lemma 3:
`P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + (K + 1)(2K + 5)³ (2(M + d'))^K (4e H k / μ_*)^k`. -/
theorem prob_le_of_hji' {P : ∀ a b, Ω a b → ℝ} {X : ∀ a b, Ω a b → ℕ} {B : ∀ a b, Set (Ω a b)}
    {N M d K k : ℕ} {δ H PH pB : ℝ} (hP : ∀ a b, IsProb (P a b)) (hX : ∀ a b ω, X a b ω ≤ N)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hH : 1 ≤ H) (hk : 1 ≤ k) (hN : 0 < N)
    (hji : HJI P X B N d K k δ H)
    (hmean : ∀ a b, a + b ≤ K → Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b ω * X a b ω)
    (hpB : pB ≤ Real.pi * δ / (80 * Real.sqrt d))
    (hunion : PH ≤ pB + ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
      ((M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial : ℕ) : ℝ) *
        lawOf ((B x.1 x.2)ᶜ.indicator (P x.1 x.2)) (X x.1 x.2) 0) :
    PH ≤ Real.pi * δ / (80 * Real.sqrt d) + (K + 1) * (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K *
      (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  refine (prob_le_of_hji hP hX hδ hδ1 hd hH hk hN hji hmean hpB hunion).trans ?_
  gcongr
  exact_mod_cast patternCount_le (by omega) K

end Assembly

section Tilted

/-- The per-pattern step of Theorem 1' of `hybrid-assembly.md`. If the tilted laws satisfy
(H-T), `Var_w X ≤ κ_T E_w X` for every `w ∈ (0, 1]` with `κ_T > 0`, then
`P(X = 0) ≤ exp(-μ / κ_T)`. It is `Tilt.le_exp_neg_div_of_le_fano` at `δ = 1 - κ_T`. -/
theorem prob_zero_le_exp_of_tiltVar_le {p : ℕ → ℝ} {N : ℕ} (hp : IsLaw p N) {κ : ℝ} (hκ : 0 < κ)
    (hT : ∀ w ∈ Set.Ioc (0 : ℝ) 1, Tilt.tiltVar p N w ≤ κ * Tilt.tiltMean p N w) :
    p 0 ≤ Real.exp (-(partialMean p N / κ)) := by
  have h := Tilt.le_exp_neg_div_of_le_fano hp (δ := 1 - κ) (by linarith) fun w hw ↦ by
    have hm : 0 ≤ Tilt.tiltMean p N w := div_nonneg
      (sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (by positivity) (hp.nonneg j))
        (pow_nonneg hw.1.le j)) (Tilt.genFun_pos_of_pos hp hw.1).le
    rw [Tilt.fano, sub_le_sub_iff_left]
    rcases hm.eq_or_lt with h | h
    · rw [← h, div_zero]
      exact hκ.le
    · rw [div_le_iff₀ h]
      exact hT w hw
  rwa [sub_sub_cancel] at h

variable {Ω : ℕ → ℕ → Type*} [∀ a b, Fintype (Ω a b)]

/-- Theorem 1' of `hybrid-assembly.md`, finite form, conditional on Proposition 2 (with
`𝔅 = ∅`) and Lemma 5. If every pattern `j0 + j1 ≤ K` has mean `μ_Λ ≥ πδ(n - 1) / (40√d')` and
satisfies (H-T), `Var_w X ≤ κ_T E_w X` for `w ∈ (0, 1]`, then
`P_H(ρ(H) ≤ K) ≤ Π_K exp(-πδ(n - 1) / (40√d' κ_T))`. -/
theorem prob_le_of_tilt {P : ∀ a b, Ω a b → ℝ} {X : ∀ a b, Ω a b → ℕ} {N M d K : ℕ} {δ κ PH : ℝ}
    (hP : ∀ a b, IsProb (P a b)) (hX : ∀ a b ω, X a b ω ≤ N) (hκ : 0 < κ)
    (hT : ∀ a b, a + b ≤ K → ∀ w ∈ Set.Ioc (0 : ℝ) 1,
      Tilt.tiltVar (lawOf (P a b) (X a b)) N w ≤ κ * Tilt.tiltMean (lawOf (P a b) (X a b)) N w)
    (hmean : ∀ a b, a + b ≤ K → Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b ω * X a b ω)
    (hunion : PH ≤ ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
      ((M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial : ℕ) : ℝ) *
        lawOf (P x.1 x.2) (X x.1 x.2) 0) :
    PH ≤ patternCount M d K * Real.exp (-(Real.pi * δ * N / (40 * Real.sqrt d) / κ)) := by
  refine hunion.trans ?_
  rw [patternCount, cast_sum, sum_mul]
  refine sum_le_sum fun j hj ↦ ?_
  rw [cast_sum, sum_mul]
  refine sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hab : x.1 + x.2 ≤ K := by
    have := mem_antidiagonal.mp hx
    have := mem_range.mp hj
    omega
  have hlaw := isLaw_lawOf (hP x.1 x.2) (hX x.1 x.2)
  refine (prob_zero_le_exp_of_tiltVar_le hlaw hκ (hT x.1 x.2 hab)).trans ?_
  rw [partialMean_lawOf _ (hX x.1 x.2), Real.exp_le_exp, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (hmean x.1 x.2 hab) hκ.le

end Tilted

section Asymptotic

/-- `d' = ⌈ε√m⌉`, the size of the defect set in Theorem 1 of `hybrid-assembly.md`. -/
noncomputable def defectSize (ε : ℝ) (m : ℕ) : ℕ :=
  ⌈ε * Real.sqrt m⌉₊

/-- `K = ⌊(1 - δ)d'⌋`, the repair radius in Theorem 1 of `hybrid-assembly.md`. -/
noncomputable def radius (ε δ : ℝ) (m : ℕ) : ℕ :=
  ⌊(1 - δ) * defectSize ε m⌋₊

/-- `k = ⌈4(1 + η)K⌉`, the half order of the moments in Theorem 1 of `hybrid-assembly.md`. -/
noncomputable def halfOrder (ε δ η : ℝ) (m : ℕ) : ℕ :=
  ⌈4 * (1 + η) * radius ε δ m⌉₊

/-- `(1 - δ)ε√m ≤ K + 1`, the last line of the proof of Theorem 1 of `hybrid-assembly.md`. -/
theorem le_radius_add_one {ε δ : ℝ} (hδ1 : δ ≤ 1) (m : ℕ) :
    (1 - δ) * ε * Real.sqrt m ≤ radius ε δ m + 1 := by
  have h1 := Nat.le_ceil (ε * Real.sqrt m)
  have h2 := Nat.lt_floor_add_one ((1 - δ) * defectSize ε m)
  have h3 : (1 - δ) * (ε * Real.sqrt m) ≤ (1 - δ) * defectSize ε m :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  rw [radius]
  linarith

/-- The arithmetic of the proof of Theorem 1 of `hybrid-assembly.md`. If `K ≥ 1`, `0 < x ≤ 1`,
`(1 + η)K ≤ βk`, `0 < Y ≤ 4m`, `log x ≤ c - β log m`, and
`19 + log 4 + (1 + η)c / β ≤ (η / 2) log m`, then `(K + 1)(2K + 5)³ Y^K x^k ≤ m^(-ηK/2)`. -/
theorem tail_product_le {K k : ℕ} {η β x Y c m : ℝ} (hη : 0 < η) (hβ : 0 < β) (hK : 1 ≤ K)
    (hm : 0 < m) (hY : 0 < Y) (hYm : Y ≤ 4 * m) (hx : 0 < x) (hx1 : x ≤ 1)
    (hk : (1 + η) * K ≤ β * k) (hlog : Real.log x ≤ c - β * Real.log m)
    (hm0 : 19 + Real.log 4 + (1 + η) * c / β ≤ η / 2 * Real.log m) :
    (K + 1) * (2 * K + 5) ^ 3 * Y ^ K * x ^ k ≤ m ^ (-(η * K / 2)) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpos : 0 < (K + 1 : ℝ) * (2 * K + 5) ^ 3 * Y ^ K * x ^ k := by positivity
  rw [Real.rpow_def_of_pos hm, ← Real.exp_log hpos, Real.exp_le_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  have h1 : Real.log (K + 1) ≤ K := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 1 by positivity)]
  have h2 : Real.log (2 * K + 5) ≤ 2 * K + 4 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * K + 5 by positivity)]
  have h3 : Real.log Y ≤ Real.log 4 + Real.log m := by
    rw [← Real.log_mul (by norm_num) hm.ne']
    exact Real.log_le_log hY hYm
  have hlx : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have h4 : (k : ℝ) * Real.log x ≤ (1 + η) * K / β * Real.log x := by
    refine mul_le_mul_of_nonpos_right ?_ hlx
    rw [div_le_iff₀ hβ]
    linarith
  have h5 : (1 + η) * K / β * Real.log x ≤ (1 + η) * K / β * (c - β * Real.log m) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h6 : (1 + η) * K / β * (c - β * Real.log m) =
      K * ((1 + η) * c / β) - (1 + η) * K * Real.log m := by
    field_simp
  have h7 := mul_le_mul_of_nonneg_left hm0 (by positivity : (0 : ℝ) ≤ K)
  have h8 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ K)
  nlinarith

/-- Theorem 1 of `hybrid-assembly.md`, the arithmetic. Fix `ε, η > 0`, `δ ∈ (0, 1)` and `H ≥ 1`,
and put `d' = ⌈ε√m⌉`, `K = ⌊(1 - δ)d'⌋`, `k = ⌈4(1 + η)K⌉`, `M = m - 3`, `n - 1 = 2m - 2` and
`μ_* = πδ(n - 1) / (80√d')`. There is `m₀` such that every `m ≥ m₀` has `m ≥ 3`,
`d', K, k ≥ 1`, `(K + 1)(2K + 5)³ (2(M + d'))^K (4e H k / μ_*)^k ≤ m^(-ηK/2)` and
`πδ / (80√d') + m^(-ηK/2) < 1`. -/
theorem exists_tail_le {ε δ η H : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hH : 1 ≤ H) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      3 ≤ m ∧ 1 ≤ defectSize ε m ∧ 1 ≤ radius ε δ m ∧ 1 ≤ halfOrder ε δ η m ∧
      (radius ε δ m + 1) * (2 * radius ε δ m + 5) ^ 3 *
          (2 * ((m - 3 : ℕ) + defectSize ε m)) ^ radius ε δ m *
          (4 * Real.exp 1 * H * halfOrder ε δ η m /
            (Real.pi * δ * (2 * m - 2 : ℕ) / (80 * Real.sqrt (defectSize ε m)))) ^
            halfOrder ε δ η m ≤ (m : ℝ) ^ (-(η * radius ε δ m / 2)) ∧
      Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
        (m : ℝ) ^ (-(η * radius ε δ m / 2)) < 1 := by
  set C1 : ℝ := 3200 * Real.exp 1 * H * (1 + η) * ε * Real.sqrt (2 * ε) / (Real.pi * δ) with hC1
  have hC1pos : 0 < C1 := by positivity
  set c : ℝ := |Real.log C1| with hcdef
  have hc : 0 ≤ c := abs_nonneg _
  set L : ℝ := 2 * (19 + Real.log 4 + (1 + η) * c / (1 / 4)) / η with hLdef
  set S0 : ℝ := max (max (1 / ε) (1 / ((1 - δ) * ε))) (max (2 * ε) (C1 ^ 2)) with hS0def
  refine ⟨⌈max (max (S0 ^ 2) 3) (Real.exp L)⌉₊, fun m hm ↦ ?_⟩
  have hmT : max (max (S0 ^ 2) 3) (Real.exp L) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hS0m : S0 ^ 2 ≤ (m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmT
  have h3m : (3 : ℝ) ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmT
  have hLm : Real.exp L ≤ m := le_trans (le_max_right _ _) hmT
  have hm3 : 3 ≤ m := by exact_mod_cast h3m
  have hmpos : (0 : ℝ) < m := by linarith
  have h1ε : 0 ≤ 1 / ε := by positivity
  have hS0 : 0 ≤ S0 := h1ε.trans ((le_max_left _ _).trans (le_max_left _ _))
  set s := Real.sqrt m with hsdef
  have hs : S0 ≤ s := (Real.le_sqrt hS0 hmpos.le).mpr hS0m
  have hspos : 0 < s := Real.sqrt_pos.mpr hmpos
  have hss : s ^ 2 = m := Real.sq_sqrt hmpos.le
  have hεs : 1 ≤ ε * s := by
    have h : 1 / ε ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    rw [div_le_iff₀ hε] at h
    linarith
  have hδε : 0 < (1 - δ) * ε := mul_pos (by linarith) hε
  have hδεs : 1 ≤ (1 - δ) * ε * s := by
    have h : 1 / ((1 - δ) * ε) ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    rw [div_le_iff₀ hδε] at h
    linarith
  have h2ε : 2 * ε ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hC1s : C1 ^ 2 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  set t := Real.sqrt s with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hspos
  have htt : t ^ 2 = s := Real.sq_sqrt hspos.le
  have hC1t : C1 ≤ t := (Real.le_sqrt hC1pos.le hspos.le).mpr hC1s
  set d := defectSize ε m with hddef
  have hd1 : ε * s ≤ d := Nat.le_ceil _
  have hd2 : (d : ℝ) < ε * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hd : 1 ≤ d := by exact_mod_cast hεs.trans hd1
  have hd2' : (d : ℝ) ≤ 2 * ε * s := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdm : (d : ℝ) ≤ m :=
    calc (d : ℝ) ≤ 2 * ε * s := hd2'
      _ ≤ s * s := mul_le_mul_of_nonneg_right h2ε hspos.le
      _ = m := by rw [← hss]; ring
  set K := radius ε δ m with hKdef
  have hK1 : (K : ℝ) ≤ (1 - δ) * d := Nat.floor_le (by positivity)
  have hδd : (1 : ℝ) ≤ (1 - δ) * d := by
    have h := mul_le_mul_of_nonneg_left hd1 (by linarith : (0 : ℝ) ≤ 1 - δ)
    linarith
  have hK : 1 ≤ K := Nat.le_floor (by push_cast; exact hδd)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKd : (K : ℝ) ≤ d := hK1.trans (by linarith [mul_nonneg hδ.le hdpos.le])
  have hηK : 0 ≤ η * K := mul_nonneg hη.le (Nat.cast_nonneg K)
  set k := halfOrder ε δ η m with hkdef
  have hk1 : 4 * (1 + η) * K ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < 4 * (1 + η) * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hk3 : (k : ℝ) ≤ 10 * (1 + η) * ε * s := by
    have e1 : (1 : ℝ) ≤ (1 + η) * K := by linarith
    have e2 : (1 + η) * (K : ℝ) ≤ (1 + η) * (2 * ε * s) :=
      mul_le_mul_of_nonneg_left (hKd.trans hd2') (by positivity)
    linarith
  have hN : (((2 * m - 2 : ℕ)) : ℝ) = 2 * m - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hNm : (m : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := by
    rw [hN]
    linarith
  have hsd : Real.sqrt d ≤ Real.sqrt (2 * ε) * t := by
    rw [htdef, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  set x := 4 * Real.exp 1 * H * k /
    (Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ) / (80 * Real.sqrt d)) with hxdef
  have hxpos : 0 < x := by
    rw [hxdef]
    have : (0 : ℝ) < ((2 * m - 2 : ℕ) : ℝ) := hmpos.trans_le hNm
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hx : x ≤ C1 / t := by
    rw [hxdef, div_div_eq_mul_div]
    calc 4 * Real.exp 1 * H * k * (80 * Real.sqrt d) / (Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ))
        ≤ 4 * Real.exp 1 * H * (10 * (1 + η) * ε * s) * (80 * (Real.sqrt (2 * ε) * t)) /
            (Real.pi * δ * m) := by
          gcongr
      _ = C1 / t := by
          rw [hC1, ← hss, ← htt]
          field_simp
          ring
  have hx1 : x ≤ 1 := hx.trans ((div_le_one htpos).mpr hC1t)
  have hlogt : Real.log t = Real.log m / 4 := by
    rw [htdef, Real.log_sqrt hspos.le, hsdef, Real.log_sqrt hmpos.le]
    ring
  have hlog : Real.log x ≤ c - 1 / 4 * Real.log m := by
    have h := Real.log_le_log hxpos hx
    rw [Real.log_div hC1pos.ne' htpos.ne', hlogt] at h
    linarith [le_abs_self (Real.log C1)]
  have hLlog : L ≤ Real.log m := (Real.le_log_iff_exp_le hmpos).mpr hLm
  have hm0 : 19 + Real.log 4 + (1 + η) * c / (1 / 4) ≤ η / 2 * Real.log m := by
    have h := mul_le_mul_of_nonneg_left hLlog (by positivity : (0 : ℝ) ≤ η / 2)
    rw [hLdef] at h
    field_simp at h ⊢
    linarith
  have hM : (((m - 3 : ℕ)) : ℝ) = m - 3 := by
    rw [Nat.cast_sub hm3]
    push_cast
    ring
  have hY : 0 < 2 * (((m - 3 : ℕ) : ℝ) + d) := by positivity
  have hYm : 2 * (((m - 3 : ℕ) : ℝ) + d) ≤ 4 * m := by
    rw [hM]
    linarith
  have htail := tail_product_le (K := K) (k := k) hη (by norm_num : (0 : ℝ) < 1 / 4) hK hmpos hY
    hYm hxpos hx1 (by linarith) hlog hm0
  refine ⟨hm3, hd, hK, hk, htail, ?_⟩
  have hβ : Real.pi * δ / (80 * Real.sqrt d) ≤ 1 / 20 := by
    have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
    rw [div_le_iff₀ (by positivity)]
    have hπδ : Real.pi * δ ≤ 4 * 1 :=
      mul_le_mul Real.pi_le_four hδ1.le hδ.le (by norm_num)
    linarith
  have h19 : 19 ≤ η / 2 * Real.log m := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : 0 ≤ (1 + η) * c / (1 / 4) := by positivity
    linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hpow : (m : ℝ) ^ (-(η * K / 2)) ≤ Real.exp (-19) := by
    rw [Real.rpow_def_of_pos hmpos, Real.exp_le_exp]
    have h := mul_nonneg (mul_nonneg hη.le hlogm) (sub_nonneg.mpr hK')
    linarith
  have he : Real.exp (-19) ≤ 1 / 20 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 19) (by norm_num)]
    linarith [Real.add_one_le_exp (19 : ℝ)]
  linarith

universe u in
/-- Theorem 1 of `hybrid-assembly.md`, conditional on Proposition 2 and Lemma 5. Fix `ε, η > 0`,
`δ ∈ (0, 1)` and `H ≥ 1`, and put `d' = ⌈ε√m⌉`, `K = ⌊(1 - δ)d'⌋` and `k = ⌈4(1 + η)K⌉`. There is
`m₀` such that for every `m ≥ m₀` the bound `πδ / (80√d') + m^(-ηK/2)` is below `1`, and the
following holds for every family of pattern spaces at `m`, with `X ≤ n - 1 = 2m - 2`. If (H-JI)
holds, the mean bound of Lemma 5 holds, `P(E' ∈ 𝔅) = pB ≤ πδ / (80√d')` under `H`, and the union
of Proposition 2 bounds `P_H = P_H(ρ(H) ≤ K)`, then `P_H ≤ πδ / (80√d') + m^(-ηK/2)`. Since then
`P_H(ρ(H) ≤ K) < 1`, some tail has `ρ > K`, and `N_m ≥ K + 1 ≥ (1 - δ)ε√m` by
`le_radius_add_one`. -/
theorem hybrid_theorem1 {ε δ η H : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hH : 1 ≤ H) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
        (m : ℝ) ^ (-(η * radius ε δ m / 2)) < 1 ∧
      ∀ (Ω : ℕ → ℕ → Type u) [∀ a b, Fintype (Ω a b)] (P : ∀ a b, Ω a b → ℝ)
        (X : ∀ a b, Ω a b → ℕ) (B : ∀ a b, Set (Ω a b)) (PH pB : ℝ),
        (∀ a b, IsProb (P a b)) → (∀ a b ω, X a b ω ≤ 2 * m - 2) →
        HJI P X B (2 * m - 2) (defectSize ε m) (radius ε δ m) (halfOrder ε δ η m) δ H →
        (∀ a b, a + b ≤ radius ε δ m → Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ) /
          (40 * Real.sqrt (defectSize ε m)) ≤ ∑ ω, P a b ω * X a b ω) →
        pB ≤ Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) →
        PH ≤ pB + ∑ j ∈ range (radius ε δ m + 1), ∑ x ∈ antidiagonal j,
          (((m - 3).choose x.1 * (defectSize ε m).choose x.2 *
            (2 * (3 + x.1 + x.2) - 1).doubleFactorial : ℕ) : ℝ) *
            lawOf ((B x.1 x.2)ᶜ.indicator (P x.1 x.2)) (X x.1 x.2) 0 →
        PH ≤ Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
          (m : ℝ) ^ (-(η * radius ε δ m / 2)) := by
  obtain ⟨m₀, hm₀⟩ := exists_tail_le hε hδ hδ1 hη hH
  refine ⟨m₀, fun m hm ↦ ?_⟩
  obtain ⟨hm3, hd, hK, hk, htail, hlt⟩ := hm₀ m hm
  refine ⟨hlt, fun Ω _ P X B PH pB hP hX hji hmean hpB hunion ↦ ?_⟩
  refine (prob_le_of_hji' hP hX hδ hδ1.le hd hH hk (by omega) hji hmean hpB hunion).trans ?_
  gcongr

end Asymptotic

end HybridConditional

end Pairing
