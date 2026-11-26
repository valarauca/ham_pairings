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

end HybridConditional

end Pairing
