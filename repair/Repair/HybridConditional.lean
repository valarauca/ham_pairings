import Mathlib.Data.Nat.Choose.Vandermonde
import Repair.CumulantTail
import Suppression.Density
import Suppression.Prob
import Suppression.Tilt

/-!
# The hybrid-tail route: the conditional theorem (`hybrid-assembly.md`, `hji-pro.md`)

Formal parts of `results/hybrid-assembly.md` (COD-232) beyond the probability core of
`CumulantTail.lean`, with the hypothesis in the corrected form of `results/hji-pro.md`. Notation
is that of the notes: `M = m - 3` kept factor edges, `d'` the size of the defect set `E'`,
`N = 3 + j0 + j1` and `X` the number of Hamiltonian factors, with `X ≤ n - 1`.

`hji-pro.md` Proposition A shows that (H-JI) as stated in `hybrid-assembly.md` §2 fails for the
law `Λ`, whose rematchings carry false defects (`F_0`-edges). The hypothesis used here is the
correction of `hji-pro.md` Lemma A′ and §8: (H-JI*), the moment form, for the true-defect laws
`Λ⁰_(j0, j1, F)`, with `H` allowed to grow up to `m^(1/4 - θ)` and `k = ⌈(1 + η)K / θ⌉`
(Proposition C). The cumulant form still implies it, by Proposition 8.

The laws `Λ⁰` and the random hybrid `H` are not built here. Each true-defect pattern
`(j0, j1, F)` enters as an abstract finite probability space `(Ω j0 j1 F, P j0 j1 F)` carrying the
count `X` and the event `B = {E' ∈ 𝔅}`. The union of Lemma A′ and the mean bound (Lemma 5 of
`hybrid-assembly.md`, not yet re-derived for `Λ⁰`) are the hypotheses `hunion` and `hmean`.

* `patternCount M d K` : `Π_K = ∑_(j0 + j1 ≤ K) C(M, j0) C(d', j1) (2N - 1)!!`.
* `patternCount_eq`, `patternCount_le` (Lemma 3) : `Π_K = ∑_(j ≤ K) C(M + d', j) (2j + 5)!!
  ≤ (K + 1)(2K + 5)³ (2(M + d'))^K`.
* `trueWeight`, `sum_trueWeight_le` (Lemma A′) : the union over true-defect patterns costs
  `∑_(j0 + j1 ≤ K) ∑_F C(M, j0) C(d', j1) (2(N - |F|) - 1)!! ≤ 2^(K + 3) Π_K`.
* `condLaw P B X` : the law of `X` under `P(· | Bᶜ)`, the law `Λ^𝔅` of §2.
  `le_partialMean_condLaw` is the last step of the proof of Lemma 5,
  `E[X | Bᶜ] ≥ E X - (n - 1) P(B)`.
* `HJIStar` : the corrected hypothesis, (H-JI*) for `Λ⁰`, and `hjiStar_of_factCumulant` : the
  factorial-cumulant form implies it.
* `prob_le_of_hjiStar`, `prob_le_of_hjiStar'` (Theorem 1, finite form) : the union, the mean
  bound and (H-JI*) for `Λ⁰` give
  `P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + 2^(K + 3) Π_K (4e H k / μ_*)^k` with
  `μ_* = πδ(n - 1) / (80√d')`.
* `exists_tail_le`, `hybrid_theorem1` (Theorem 1 with Proposition C) : with `d' = ⌈ε√m⌉`,
  `K = ⌊(1 - δ)d'⌋`, `H = m^(1/4 - θ)` and `k = ⌈(1 + η)K / θ⌉`, for `m ≥ m₀`,
  `P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + m^(-ηK/2) < 1`, and `le_radius_add_one` gives
  `K + 1 ≥ (1 - δ)ε√m`.
* `prob_zero_le_exp_of_tiltVar_le` (proof of Theorem 1') : (H-T) on one pattern gives
  `P_Λ(X = 0) ≤ exp(-μ_Λ / κ_T)`, through `Tilt.le_exp_neg_div_of_le_fano`.
* `prob_le_of_tilt` (Theorem 1', finite form) : Proposition 2 with `𝔅 = ∅`, Lemma 5 and (H-T) give
  `P_H(ρ(H) ≤ K) ≤ Π_K exp(-πδ(n - 1) / (40√d' κ_T))`. Proposition 2 over `Λ` remains a valid
  union, and `hji-pro.md` does not treat (H-T).
-/

namespace Pairing

namespace HybridConditional

open Finset Nat SizeBias ChainRule CumulantTail

section PatternCount

/-- `(2j + 5)!! = (2j + 5)(2j + 3)(2j + 1)(2j - 1)!!`. Used for Lemma 3 of `hybrid-assembly.md`. -/
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

/-- `∑_ω 1_(Bᶜ)(ω) P ω = P(Bᶜ)`. Used for the law `Λ^𝔅` of `hybrid-assembly.md` §2. -/
theorem sum_indicator_eq_prob (P : Ω → ℝ) (B : Set Ω) : ∑ ω, Bᶜ.indicator P ω = prob P Bᶜ :=
  rfl

/-- The law of `X ≤ N` under `P(· | Bᶜ)` is a law on `[0, N]` when `P(Bᶜ) > 0`.
Used for the law `Λ^𝔅` of `hybrid-assembly.md` §2. -/
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

/-- `P(Bᶜ) = 1 - P(B)`. Used for the law `Λ^𝔅` of `hybrid-assembly.md` §2. -/
theorem prob_compl_eq {P : Ω → ℝ} (hP : IsProb P) (B : Set Ω) : prob P Bᶜ = 1 - prob P B := by
  rw [← hP.sum_eq_one, prob, prob, eq_sub_iff_add_eq, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ ↦ by rw [add_comm, Set.indicator_self_add_compl_apply]

/-- The mean of `X` under `P(· | Bᶜ)`: `E[X | Bᶜ] = ∑_ω 1_(Bᶜ)(ω) P ω X ω / P(Bᶜ)`.
Used for Lemma 5 of `hybrid-assembly.md`. -/
theorem partialMean_condLaw (P : Ω → ℝ) (B : Set Ω) {X : Ω → ℕ} {N : ℕ} (hX : ∀ ω, X ω ≤ N) :
    partialMean (condLaw P B X) N = (∑ ω, Bᶜ.indicator P ω * X ω) / prob P Bᶜ := by
  rw [sum_mul_lawOf (Bᶜ.indicator P) hX fun j ↦ (j : ℝ), partialMean, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [condLaw, div_eq_mul_inv]
  ring

/-- `E X = ∑_ω P ω X ω` is the mean of the law of `X`.
Used for Theorem 1' of `hybrid-assembly.md`. -/
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

section TrueDefect

/-- `(2i - 1)!! ≤ (2j - 1)!!` for `i ≤ j`.
Used for the union of `hji-pro.md` Lemma A′ against Lemma 3 of `hybrid-assembly.md`. -/
theorem doubleFactorial_two_mul_sub_one_mono {i j : ℕ} (h : i ≤ j) :
    (2 * i - 1).doubleFactorial ≤ (2 * j - 1).doubleFactorial := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    refine ih.trans ?_
    rcases j with _ | j
    · exact le_rfl
    · rw [show 2 * (j + 1 + 1) - 1 = 2 * (j + 1) - 1 + 2 by omega, doubleFactorial_add_two]
      exact Nat.le_mul_of_pos_left _ (by omega)

/-- The weight `C(M, j0) C(d', j1) (2(N - |F|) - 1)!!` of the true-defect pattern `(j0, j1, F)`,
with `N = 3 + j0 + j1` and `F` a set of `F_0`-edges of `Q` (gadget edges and `E'`-pairs inside
`U_1`, at most `3 + j1` of them). It is the union of Lemma A′ of `hji-pro.md`, the corrected
Proposition 2 of `hybrid-assembly.md`. -/
def trueWeight (M d a b : ℕ) (F : Finset (Fin (3 + b))) : ℕ :=
  M.choose a * d.choose b * (2 * (3 + a + b - F.card) - 1).doubleFactorial

/-- The union cost of Lemma A′ of `hji-pro.md` against Lemma 3 of `hybrid-assembly.md`:
`∑_(j0 + j1 ≤ K) ∑_F C(M, j0) C(d', j1) (2(N - |F|) - 1)!! ≤ 2^(K + 3) Π_K`. -/
theorem sum_trueWeight_le (M d K : ℕ) :
    ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j, ∑ F : Finset (Fin (3 + x.2)),
      trueWeight M d x.1 x.2 F ≤ 2 ^ (K + 3) * patternCount M d K := by
  rw [patternCount, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun x hx ↦ ?_
  have hb : x.2 ≤ K := by
    have := mem_antidiagonal.mp hx
    have := mem_range.mp hj
    omega
  calc ∑ F : Finset (Fin (3 + x.2)), trueWeight M d x.1 x.2 F
      ≤ ∑ _F : Finset (Fin (3 + x.2)),
          M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial :=
        sum_le_sum fun F _ ↦ Nat.mul_le_mul_left _
          (doubleFactorial_two_mul_sub_one_mono (by omega))
    _ = 2 ^ (3 + x.2) *
          (M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial) := by
        rw [sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
    _ ≤ 2 ^ (K + 3) *
          (M.choose x.1 * d.choose x.2 * (2 * (3 + x.1 + x.2) - 1).doubleFactorial) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

end TrueDefect

section Assembly

variable {Ω : ℕ → ∀ b : ℕ, Finset (Fin (3 + b)) → Type*} [∀ a b F, Fintype (Ω a b F)]

/-- `πδ / (80√d') < 1` for `δ ≤ 1` and `d' ≥ 1` (`hybrid-assembly.md`, §2). -/
theorem pi_mul_div_lt_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    Real.pi * δ / (80 * Real.sqrt d) < 1 := by
  have hs : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  rw [div_lt_one (by positivity)]
  nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The hypothesis of the hybrid-tail route in its corrected form, (H-JI*) for the true-defect
laws `Λ⁰` (`hji-pro.md`, Lemma A′ and §8 item 1, replacing (H-JI) of `hybrid-assembly.md` §2,
which `hji-pro.md` Proposition A refutes for `Λ`). The pattern `(j0, j1, F)` is the finite
probability space `(Ω j0 j1 F, P j0 j1 F)` of `Λ⁰_(j0, j1, F)`, with the count `X` of Hamiltonian
factors and the event `B = {E' ∈ 𝔅}`. With `μ = E_(Λ⁰^𝔅) X` the mean of `condLaw`, the law of
`X` under `Λ⁰^𝔅 = Λ⁰( · | E' ∉ 𝔅)`, it asks `P(E' ∈ 𝔅) ≤ πδ / (80√d')` and
`E_(Λ⁰^𝔅)(X - μ)^(2k) ≤ (4e H k μ)^k` for every pattern with `j0 + j1 ≤ K`. `H` may depend on
`m`, up to `H = m^(1/4 - θ)` (`hji-pro.md`, Proposition C). The factorial-cumulant form implies it
(`hjiStar_of_factCumulant`). -/
structure HJIStar (P : ∀ a b F, Ω a b F → ℝ) (X : ∀ a b F, Ω a b F → ℕ)
    (B : ∀ a b F, Set (Ω a b F)) (N d K k : ℕ) (δ H : ℝ) : Prop where
  prob_bad_le : ∀ a b F, a + b ≤ K →
    prob (P a b F) (B a b F) ≤ Real.pi * δ / (80 * Real.sqrt d)
  centralMoment_le : ∀ a b F, a + b ≤ K →
    centralMoment (condLaw (P a b F) (B a b F) (X a b F)) N (2 * k) ≤
      (4 * Real.exp 1 * H * k * partialMean (condLaw (P a b F) (B a b F) (X a b F)) N) ^ k

/-- The factorial-cumulant form of the corrected hypothesis implies (H-JI*) for `Λ⁰`, by
Proposition 8 of `hybrid-assembly.md`. If every pattern has `μ > 0`, `H μ ≥ 8k` and
`|κ^f_j(X; Λ⁰^𝔅)| ≤ j! H μ (H μ / (8k))^((j - 2)/2)` for `2 ≤ j ≤ 2k`, with `H ≥ 1`, and
`P(E' ∈ 𝔅) ≤ πδ / (80√d')`, then `HJIStar` holds. -/
theorem hjiStar_of_factCumulant {P : ∀ a b F, Ω a b F → ℝ} {X : ∀ a b F, Ω a b F → ℕ}
    {B : ∀ a b F, Set (Ω a b F)} {N d K k : ℕ} {δ H : ℝ} (hP : ∀ a b F, IsProb (P a b F))
    (hX : ∀ a b F ω, X a b F ω ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hH : 1 ≤ H)
    (hk : 1 ≤ k)
    (hbad : ∀ a b F, a + b ≤ K → prob (P a b F) (B a b F) ≤ Real.pi * δ / (80 * Real.sqrt d))
    (hpos : ∀ a b F, a + b ≤ K → 0 < partialMean (condLaw (P a b F) (B a b F) (X a b F)) N)
    (hHμ : ∀ a b F, a + b ≤ K →
      8 * k ≤ H * partialMean (condLaw (P a b F) (B a b F) (X a b F)) N)
    (hκ : ∀ a b F, a + b ≤ K → ∀ j, 2 ≤ j → j ≤ 2 * k →
      |factCumulant (condLaw (P a b F) (B a b F) (X a b F)) N j| ≤
        j ! * H * partialMean (condLaw (P a b F) (B a b F) (X a b F)) N *
          Real.sqrt (H * partialMean (condLaw (P a b F) (B a b F) (X a b F)) N / (8 * k)) ^
            (j - 2)) :
    HJIStar P X B N d K k δ H where
  prob_bad_le := hbad
  centralMoment_le a b F hab := by
    have hB : 0 < prob (P a b F) (B a b F)ᶜ := by
      rw [prob_compl_eq (hP a b F)]
      linarith [pi_mul_div_lt_one hδ hδ1 hd, hbad a b F hab]
    exact centralMoment_le_of_factCumulant (isLaw_condLaw (hP a b F) hB (hX a b F)) hH hk
      (hpos a b F hab) (hHμ a b F hab) (hκ a b F hab)

/-- The per-pattern bound of Theorem 1 of `hybrid-assembly.md`, for the true-defect laws of
`hji-pro.md`. Under (H-JI*) for `Λ⁰` with `H ≥ 0` and the mean bound
`μ_(Λ⁰) ≥ πδ(n - 1) / (40√d')` (Lemma 5 of `hybrid-assembly.md`, to be re-derived for `Λ⁰`),
`P_(Λ⁰)(X = 0, E' ∉ 𝔅) ≤ (4e H k / μ_*)^k` with `μ_* = πδ(n - 1) / (80√d')`. -/
theorem lawOf_zero_le_of_hjiStar {P : ∀ a b F, Ω a b F → ℝ} {X : ∀ a b F, Ω a b F → ℕ}
    {B : ∀ a b F, Set (Ω a b F)} {N d K k : ℕ} {δ H : ℝ} (hP : ∀ a b F, IsProb (P a b F))
    (hX : ∀ a b F ω, X a b F ω ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hH : 0 ≤ H)
    (hN : 0 < N) (hji : HJIStar P X B N d K k δ H)
    (hmean : ∀ a b F, a + b ≤ K →
      Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b F ω * X a b F ω)
    {a b : ℕ} {F : Finset (Fin (3 + b))} (hab : a + b ≤ K) :
    lawOf ((B a b F)ᶜ.indicator (P a b F)) (X a b F) 0 ≤
      (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ := hji.prob_bad_le a b F hab
  have hB : 0 < prob (P a b F) (B a b F)ᶜ := by
    rw [prob_compl_eq (hP a b F)]
    linarith [pi_mul_div_lt_one hδ hδ1 hd]
  have hlaw := isLaw_condLaw (hP a b F) hB (hX a b F)
  have hμs : 0 < Real.pi * δ * N / (80 * Real.sqrt d) := by positivity
  have hμ : Real.pi * δ * N / (80 * Real.sqrt d) ≤
      partialMean (condLaw (P a b F) (B a b F) (X a b F)) N := by
    refine le_trans ?_ (le_partialMean_condLaw (hP a b F) hB (hX a b F))
    have h1 := hmean a b F hab
    have h2 : (N : ℝ) * prob (P a b F) (B a b F) ≤ N * (Real.pi * δ / (80 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hβ hNr.le
    have h3 : Real.pi * δ * N / (40 * Real.sqrt d) - N * (Real.pi * δ / (80 * Real.sqrt d)) =
        Real.pi * δ * N / (80 * Real.sqrt d) := by
      field_simp
      ring
    linarith
  have hC : 0 ≤ 4 * Real.exp 1 * H * k :=
    mul_nonneg (mul_nonneg (by positivity) hH) (Nat.cast_nonneg k)
  have h8 := prob_zero_le_of_centralMoment_le hlaw (hμs.trans_le hμ)
    (hji.centralMoment_le a b F hab)
  refine (lawOf_indicator_le_condLaw (hP a b F) hB (X a b F) 0).trans (h8.trans ?_)
  exact pow_le_pow_left₀ (div_nonneg hC (hμs.trans_le hμ).le)
    (div_le_div_of_nonneg_left hC hμs hμ) k

/-- Theorem 1 of `hybrid-assembly.md` in the corrected form of `hji-pro.md`, finite form,
conditional on the union of Lemma A′ and the mean bound. Let pattern `(j0, j1, F)` carry `Λ⁰` as
in `HJIStar`, with `X ≤ n - 1 = N`. Suppose the union over true-defect patterns (`hunion`),
`P_H(ρ(H) ≤ K) ≤ P(E' ∈ 𝔅) + ∑_(j0 + j1 ≤ K) ∑_F C(M, j0) C(d', j1) (2(N - |F|) - 1)!!
P_(Λ⁰)(X = 0, E' ∉ 𝔅)` for the hybrid conditioned on `R' ∩ F_0 = ∅`, the mean bound
`μ_(Λ⁰) ≥ πδ(n - 1) / (40√d')` (`hmean`), `P(E' ∈ 𝔅) ≤ πδ / (80√d')` under `H` (`hpB`), and
(H-JI*) for `Λ⁰` with `H ≥ 0`. Then
`P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + 2^(K + 3) Π_K (4e H k / μ_*)^k` with
`μ_* = πδ(n - 1) / (80√d')`. -/
theorem prob_le_of_hjiStar {P : ∀ a b F, Ω a b F → ℝ} {X : ∀ a b F, Ω a b F → ℕ}
    {B : ∀ a b F, Set (Ω a b F)} {N M d K k : ℕ} {δ H PH pB : ℝ}
    (hP : ∀ a b F, IsProb (P a b F)) (hX : ∀ a b F ω, X a b F ω ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 1 ≤ d) (hH : 0 ≤ H) (hN : 0 < N) (hji : HJIStar P X B N d K k δ H)
    (hmean : ∀ a b F, a + b ≤ K →
      Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b F ω * X a b F ω)
    (hpB : pB ≤ Real.pi * δ / (80 * Real.sqrt d))
    (hunion : PH ≤ pB + ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
      ∑ F : Finset (Fin (3 + x.2)), (trueWeight M d x.1 x.2 F : ℝ) *
        lawOf ((B x.1 x.2 F)ᶜ.indicator (P x.1 x.2 F)) (X x.1 x.2 F) 0) :
    PH ≤ Real.pi * δ / (80 * Real.sqrt d) + 2 ^ (K + 3) * patternCount M d K *
      (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  set T := (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k with hT
  have hT0 : 0 ≤ T := pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hH)
    (Nat.cast_nonneg k)) (by positivity)) k
  refine hunion.trans (add_le_add hpB ?_)
  calc ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j, ∑ F : Finset (Fin (3 + x.2)),
        (trueWeight M d x.1 x.2 F : ℝ) *
          lawOf ((B x.1 x.2 F)ᶜ.indicator (P x.1 x.2 F)) (X x.1 x.2 F) 0
      ≤ ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j, ∑ F : Finset (Fin (3 + x.2)),
          (trueWeight M d x.1 x.2 F : ℝ) * T := by
        refine sum_le_sum fun j hj ↦ sum_le_sum fun x hx ↦ sum_le_sum fun F _ ↦ ?_
        refine mul_le_mul_of_nonneg_left (lawOf_zero_le_of_hjiStar hP hX hδ hδ1 hd hH hN hji
          hmean ?_) (Nat.cast_nonneg _)
        have := mem_antidiagonal.mp hx
        have := mem_range.mp hj
        omega
    _ = ((∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j, ∑ F : Finset (Fin (3 + x.2)),
          trueWeight M d x.1 x.2 F : ℕ) : ℝ) * T := by
        push_cast
        simp only [sum_mul]
    _ ≤ ((2 ^ (K + 3) * patternCount M d K : ℕ) : ℝ) * T :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast sum_trueWeight_le M d K) hT0
    _ = 2 ^ (K + 3) * patternCount M d K * T := by push_cast; ring

/-- The corrected Theorem 1 of `hybrid-assembly.md` in finite form, with the pattern count of
Lemma 3: `P_H(ρ(H) ≤ K) ≤ πδ / (80√d') + 2^(K + 3) (K + 1)(2K + 5)³ (2(M + d'))^K
(4e H k / μ_*)^k`, under the hypotheses of `prob_le_of_hjiStar`. -/
theorem prob_le_of_hjiStar' {P : ∀ a b F, Ω a b F → ℝ} {X : ∀ a b F, Ω a b F → ℕ}
    {B : ∀ a b F, Set (Ω a b F)} {N M d K k : ℕ} {δ H PH pB : ℝ}
    (hP : ∀ a b F, IsProb (P a b F)) (hX : ∀ a b F ω, X a b F ω ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 1 ≤ d) (hH : 0 ≤ H) (hN : 0 < N) (hji : HJIStar P X B N d K k δ H)
    (hmean : ∀ a b F, a + b ≤ K →
      Real.pi * δ * N / (40 * Real.sqrt d) ≤ ∑ ω, P a b F ω * X a b F ω)
    (hpB : pB ≤ Real.pi * δ / (80 * Real.sqrt d))
    (hunion : PH ≤ pB + ∑ j ∈ range (K + 1), ∑ x ∈ antidiagonal j,
      ∑ F : Finset (Fin (3 + x.2)), (trueWeight M d x.1 x.2 F : ℝ) *
        lawOf ((B x.1 x.2 F)ᶜ.indicator (P x.1 x.2 F)) (X x.1 x.2 F) 0) :
    PH ≤ Real.pi * δ / (80 * Real.sqrt d) +
      2 ^ (K + 3) * (K + 1) * (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K *
        (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k := by
  refine (prob_le_of_hjiStar hP hX hδ hδ1 hd hH hN hji hmean hpB hunion).trans ?_
  have hT0 : 0 ≤ (4 * Real.exp 1 * H * k / (Real.pi * δ * N / (80 * Real.sqrt d))) ^ k :=
    pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hH) (Nat.cast_nonneg k))
      (by positivity)) k
  have hc : (patternCount M d K : ℝ) ≤ (K + 1) * (2 * K + 5) ^ 3 * (2 * (M + d)) ^ K := by
    exact_mod_cast patternCount_le (by omega) K
  have h2 : (0 : ℝ) ≤ 2 ^ (K + 3) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc h2) hT0
  linarith

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

/-- `k = ⌈(1 + η)K / θ⌉`, the half order of the moments in the corrected Theorem 1
(`hji-pro.md`, Proposition C, which is Corollary 1.2 of `hybrid-assembly.md` at `α = 1/2`). -/
noncomputable def halfOrder (ε δ η θ : ℝ) (m : ℕ) : ℕ :=
  ⌈(1 + η) * radius ε δ m / θ⌉₊

/-- `(1 - δ)ε√m ≤ K + 1`, the last line of the proof of Theorem 1 of `hybrid-assembly.md`. -/
theorem le_radius_add_one {ε δ : ℝ} (hδ1 : δ ≤ 1) (m : ℕ) :
    (1 - δ) * ε * Real.sqrt m ≤ radius ε δ m + 1 := by
  have h1 := Nat.le_ceil (ε * Real.sqrt m)
  have h2 := Nat.lt_floor_add_one ((1 - δ) * defectSize ε m)
  have h3 : (1 - δ) * (ε * Real.sqrt m) ≤ (1 - δ) * defectSize ε m :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  rw [radius]
  linarith

/-- The arithmetic of the proof of Theorem 1 of `hybrid-assembly.md`, with the union cost
`2^(K + 3)` of `hji-pro.md` Lemma A′. If `K ≥ 1`, `0 < x ≤ 1`, `(1 + η)K ≤ βk`, `0 < Y ≤ 4m`,
`log x ≤ c - β log m` and `23 + log 4 + (1 + η)c / β ≤ (η / 2) log m`, then
`2^(K + 3) (K + 1)(2K + 5)³ Y^K x^k ≤ m^(-ηK/2)`. -/
theorem tail_product_le {K k : ℕ} {η β x Y c m : ℝ} (hη : 0 < η) (hβ : 0 < β) (hK : 1 ≤ K)
    (hm : 0 < m) (hY : 0 < Y) (hYm : Y ≤ 4 * m) (hx : 0 < x) (hx1 : x ≤ 1)
    (hk : (1 + η) * K ≤ β * k) (hlog : Real.log x ≤ c - β * Real.log m)
    (hm0 : 23 + Real.log 4 + (1 + η) * c / β ≤ η / 2 * Real.log m) :
    2 ^ (K + 3) * (K + 1) * (2 * K + 5) ^ 3 * Y ^ K * x ^ k ≤ m ^ (-(η * K / 2)) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpos : 0 < (2 : ℝ) ^ (K + 3) * (K + 1) * (2 * K + 5) ^ 3 * Y ^ K * x ^ k := by positivity
  rw [Real.rpow_def_of_pos hm, ← Real.exp_log hpos, Real.exp_le_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have h0 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h0' : ((K + 3 : ℕ) : ℝ) * Real.log 2 ≤ 4 * K := by
    have := mul_le_mul_of_nonneg_left h0 (by positivity : (0 : ℝ) ≤ ((K + 3 : ℕ) : ℝ))
    push_cast at this ⊢
    linarith
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

/-- The arithmetic of Theorem 1 of `hybrid-assembly.md` in the corrected form of `hji-pro.md`
(Proposition C). Fix `ε, η > 0`, `δ ∈ (0, 1)` and `θ ∈ (0, 1/4)`, and put `d' = ⌈ε√m⌉`,
`K = ⌊(1 - δ)d'⌋`, `k = ⌈(1 + η)K / θ⌉`, `H = m^(1/4 - θ)`, `M = m - 3`, `n - 1 = 2m - 2` and
`μ_* = πδ(n - 1) / (80√d')`. There is `m₀` such that every `m ≥ m₀` has `m ≥ 3`,
`d', K, k ≥ 1`, `2^(K + 3) (K + 1)(2K + 5)³ (2(M + d'))^K (4e H k / μ_*)^k ≤ m^(-ηK/2)` and
`πδ / (80√d') + m^(-ηK/2) < 1`. -/
theorem exists_tail_le {ε δ η θ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hθ : 0 < θ) (hθ4 : θ < 1 / 4) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      3 ≤ m ∧ 1 ≤ defectSize ε m ∧ 1 ≤ radius ε δ m ∧ 1 ≤ halfOrder ε δ η θ m ∧
      2 ^ (radius ε δ m + 3) * (radius ε δ m + 1) * (2 * radius ε δ m + 5) ^ 3 *
          (2 * ((m - 3 : ℕ) + defectSize ε m)) ^ radius ε δ m *
          (4 * Real.exp 1 * (m : ℝ) ^ (1 / 4 - θ) * halfOrder ε δ η θ m /
            (Real.pi * δ * (2 * m - 2 : ℕ) / (80 * Real.sqrt (defectSize ε m)))) ^
            halfOrder ε δ η θ m ≤ (m : ℝ) ^ (-(η * radius ε δ m / 2)) ∧
      Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
        (m : ℝ) ^ (-(η * radius ε δ m / 2)) < 1 := by
  set C1 : ℝ := 1280 * Real.exp 1 * (1 + η) * ε * Real.sqrt (2 * ε) / (θ * Real.pi * δ)
    with hC1
  have hC1pos : 0 < C1 := by positivity
  set c : ℝ := |Real.log C1| with hcdef
  have hc : 0 ≤ c := abs_nonneg _
  set L : ℝ := max (c / θ) (2 * (23 + Real.log 4 + (1 + η) * c / θ) / η) with hLdef
  set S0 : ℝ := max (max (1 / ε) (1 / ((1 - δ) * ε))) (2 * ε) with hS0def
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
  have h2ε : 2 * ε ≤ s := le_trans (le_max_right _ _) hs
  set t := Real.sqrt s with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hspos
  set d := defectSize ε m with hddef
  have hd1 : ε * s ≤ d := Nat.le_ceil _
  have hd2 : (d : ℝ) < ε * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hd : 1 ≤ d := by exact_mod_cast hεs.trans hd1
  have hd2' : (d : ℝ) ≤ 2 * ε * s := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set K := radius ε δ m with hKdef
  have hK1 : (K : ℝ) ≤ (1 - δ) * d := Nat.floor_le (by positivity)
  have hδd : (1 : ℝ) ≤ (1 - δ) * d := by
    have h : 1 / ((1 - δ) * ε) ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    rw [div_le_iff₀ hδε] at h
    have h' := mul_le_mul_of_nonneg_left hd1 (by linarith : (0 : ℝ) ≤ 1 - δ)
    linarith
  have hK : 1 ≤ K := Nat.le_floor (by push_cast; exact hδd)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKd : (K : ℝ) ≤ d := hK1.trans (by linarith [mul_nonneg hδ.le hdpos.le])
  have hηK : 0 ≤ η * K := mul_nonneg hη.le (Nat.cast_nonneg K)
  set k := halfOrder ε δ η θ m with hkdef
  have hk1 : (1 + η) * K / θ ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 + η) * K / θ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hηK1 : (1 : ℝ) ≤ (1 + η) * K := by linarith
  have hθK : (1 : ℝ) ≤ (1 + η) * K / θ := by
    rw [le_div_iff₀ hθ]
    linarith
  have hk : 1 ≤ k := by exact_mod_cast hθK.trans hk1
  have hkθ : (1 + η) * K ≤ θ * k := by
    rw [div_le_iff₀ hθ] at hk1
    linarith
  have hk3 : (k : ℝ) ≤ 4 * (1 + η) * ε * s / θ := by
    have e2 : (1 + η) * (K : ℝ) ≤ (1 + η) * (2 * ε * s) :=
      mul_le_mul_of_nonneg_left (hKd.trans hd2') (by positivity)
    have e3 : 2 * ((1 + η) * K / θ) ≤ 2 * ((1 + η) * (2 * ε * s) / θ) := by
      gcongr
    have e4 : 2 * ((1 + η) * (2 * ε * s) / θ) = 4 * (1 + η) * ε * s / θ := by ring
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
  set Hm : ℝ := (m : ℝ) ^ (1 / 4 - θ) with hHm
  have hHpos : 0 < Hm := Real.rpow_pos_of_pos hmpos _
  set x := 4 * Real.exp 1 * Hm * k /
    (Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ) / (80 * Real.sqrt d)) with hxdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hxpos : 0 < x := by
    rw [hxdef]
    have : (0 : ℝ) < ((2 * m - 2 : ℕ) : ℝ) := hmpos.trans_le hNm
    positivity
  have hx : x ≤ C1 * Hm * s * t / m := by
    rw [hxdef, div_div_eq_mul_div]
    calc 4 * Real.exp 1 * Hm * k * (80 * Real.sqrt d) / (Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ))
        ≤ 4 * Real.exp 1 * Hm * (4 * (1 + η) * ε * s / θ) * (80 * (Real.sqrt (2 * ε) * t)) /
            (Real.pi * δ * m) := by
          gcongr
      _ = C1 * Hm * s * t / m := by
          rw [hC1]
          field_simp
          ring
  have hlogt : Real.log t = Real.log m / 4 := by
    rw [htdef, Real.log_sqrt hspos.le, hsdef, Real.log_sqrt hmpos.le]
    ring
  have hlogs : Real.log s = Real.log m / 2 := by
    rw [hsdef, Real.log_sqrt hmpos.le]
  have hlogH : Real.log Hm = (1 / 4 - θ) * Real.log m := Real.log_rpow hmpos _
  have hlog : Real.log x ≤ c - θ * Real.log m := by
    have h := Real.log_le_log hxpos hx
    rw [Real.log_div (by positivity) hmpos.ne', Real.log_mul (by positivity) htpos.ne',
      Real.log_mul (by positivity) hspos.ne', Real.log_mul hC1pos.ne' hHpos.ne', hlogt, hlogs,
      hlogH] at h
    linarith [le_abs_self (Real.log C1)]
  have hLlog : L ≤ Real.log m := (Real.le_log_iff_exp_le hmpos).mpr hLm
  have hcθ : c ≤ θ * Real.log m := by
    have h := (le_max_left _ _).trans hLlog
    rw [div_le_iff₀ hθ] at h
    linarith
  have hx1 : x ≤ 1 := (Real.log_nonpos_iff hxpos.le).mp (by linarith)
  have hm0 : 23 + Real.log 4 + (1 + η) * c / θ ≤ η / 2 * Real.log m := by
    have h := (le_max_right _ _).trans hLlog
    rw [div_le_iff₀ hη] at h
    linarith
  have hM : (((m - 3 : ℕ)) : ℝ) = m - 3 := by
    rw [Nat.cast_sub hm3]
    push_cast
    ring
  have hdm : (d : ℝ) ≤ m :=
    calc (d : ℝ) ≤ 2 * ε * s := hd2'
      _ ≤ s * s := mul_le_mul_of_nonneg_right h2ε hspos.le
      _ = m := by rw [← hss]; ring
  have hY : 0 < 2 * (((m - 3 : ℕ) : ℝ) + d) := by positivity
  have hYm : 2 * (((m - 3 : ℕ) : ℝ) + d) ≤ 4 * m := by
    rw [hM]
    linarith
  have htail := tail_product_le (K := K) (k := k) hη hθ hK hmpos hY hYm hxpos hx1 hkθ hlog hm0
  refine ⟨hm3, hd, hK, hk, htail, ?_⟩
  have hβ : Real.pi * δ / (80 * Real.sqrt d) ≤ 1 / 20 := by
    have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
    rw [div_le_iff₀ (by positivity)]
    have hπδ : Real.pi * δ ≤ 4 * 1 :=
      mul_le_mul Real.pi_le_four hδ1.le hδ.le (by norm_num)
    linarith
  have h19 : 19 ≤ η / 2 * Real.log m := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : 0 ≤ (1 + η) * c / θ := by positivity
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
/-- Theorem 1 of `hybrid-assembly.md` in the corrected form of `hji-pro.md` (Lemma A′ and
Proposition C), conditional on the union of Lemma A′ and the mean bound of Lemma 5 for `Λ⁰`.
Fix `ε, η > 0`, `δ ∈ (0, 1)` and `θ ∈ (0, 1/4)`, and put `d' = ⌈ε√m⌉`, `K = ⌊(1 - δ)d'⌋`,
`k = ⌈(1 + η)K / θ⌉` and `H = m^(1/4 - θ)`. There is `m₀` such that for every `m ≥ m₀` the
bound `πδ / (80√d') + m^(-ηK/2)` is below `1`, and the following holds for every family of
true-defect pattern spaces at `m`, with `X ≤ n - 1 = 2m - 2`. If (H-JI*) holds for `Λ⁰` with
`H = m^(1/4 - θ)`, `μ_(Λ⁰) ≥ πδ(n - 1) / (40√d')`, `P(E' ∈ 𝔅) = pB ≤ πδ / (80√d')` under `H`,
and the union of Lemma A′ bounds `P_H = P_H(ρ(H) ≤ K)` for the hybrid conditioned on
`R' ∩ F_0 = ∅`, then `P_H ≤ πδ / (80√d') + m^(-ηK/2) < 1`. So some tail has `ρ > K`, and
`N_m ≥ K + 1 ≥ (1 - δ)ε√m` by `le_radius_add_one`. Any fixed `H ≥ 1` is covered, since
(H-JI*) at `H` implies it at every larger `H`. -/
theorem hybrid_theorem1 {ε δ η θ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hθ : 0 < θ) (hθ4 : θ < 1 / 4) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
        (m : ℝ) ^ (-(η * radius ε δ m / 2)) < 1 ∧
      ∀ (Ω : ℕ → ∀ b : ℕ, Finset (Fin (3 + b)) → Type u) [∀ a b F, Fintype (Ω a b F)]
        (P : ∀ a b F, Ω a b F → ℝ) (X : ∀ a b F, Ω a b F → ℕ) (B : ∀ a b F, Set (Ω a b F))
        (PH pB : ℝ), (∀ a b F, IsProb (P a b F)) → (∀ a b F ω, X a b F ω ≤ 2 * m - 2) →
        HJIStar P X B (2 * m - 2) (defectSize ε m) (radius ε δ m) (halfOrder ε δ η θ m) δ
          ((m : ℝ) ^ (1 / 4 - θ)) →
        (∀ a b F, a + b ≤ radius ε δ m → Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ) /
          (40 * Real.sqrt (defectSize ε m)) ≤ ∑ ω, P a b F ω * X a b F ω) →
        pB ≤ Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) →
        PH ≤ pB + ∑ j ∈ range (radius ε δ m + 1), ∑ x ∈ antidiagonal j,
          ∑ F : Finset (Fin (3 + x.2)), (trueWeight (m - 3) (defectSize ε m) x.1 x.2 F : ℝ) *
            lawOf ((B x.1 x.2 F)ᶜ.indicator (P x.1 x.2 F)) (X x.1 x.2 F) 0 →
        PH ≤ Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
          (m : ℝ) ^ (-(η * radius ε δ m / 2)) := by
  obtain ⟨m₀, hm₀⟩ := exists_tail_le hε hδ hδ1 hη hθ hθ4
  refine ⟨m₀, fun m hm ↦ ?_⟩
  obtain ⟨hm3, hd, hK, hk, htail, hlt⟩ := hm₀ m hm
  refine ⟨hlt, fun Ω _ P X B PH pB hP hX hji hmean hpB hunion ↦ ?_⟩
  refine (prob_le_of_hjiStar' hP hX hδ hδ1.le hd (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    (by omega) hji hmean hpB hunion).trans ?_
  gcongr

end Asymptotic

end HybridConditional

end Pairing
