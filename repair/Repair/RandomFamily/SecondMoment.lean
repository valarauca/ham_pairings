import Repair.RandomFamily.TheoremAPrime
import Repair.RandomFamily.PairRatio

/-!
# The second moment of the zero-state count over all families (COD-288)

Source: `results/q-second-moment-extend.md` §2 (Lemma 0, Lemma 1) and §8 (C1), and
`results/q-second-moment-contra.md` §1 (organize-archive af8925f), checked in
`results/q-second-moment-factcheck-extend.md`, rows L0, L1 and C1 (af8925f). Families
`M : ι → PerfectMatching (Vertex m)` carry the counting measure, `n = |ι|`, `N = (2m - 1)!!`,
`D = 2^(m-1)(m-1)!` and `J(P, Q) = jointCount P Q`.

* `card_not_ham_two_add` : `#{X : ¬Ham P X ∧ ¬Ham Q X} + 2D = N + J(P, Q)`.
* `sum_card_zeroStates_sq` : `∑_M |Z(M)|² = ∑_(P,Q) #{X : ¬Ham P X ∧ ¬Ham Q X}^n`, the second
  moment identity, so `∑_M |Z(M)|² = ∑_(P,Q) (N - 2D + J(P, Q))^n`.
* `sum_jointCount` : `∑_Q J(P, Q) = D²`, so `E δ = 0`.
* `sq_sum_card_zeroStates_le` : Cauchy–Schwarz, `(∑_M |Z(M)|)² ≤ #{M : Z(M) ≠ ∅} ∑_M |Z(M)|²`.
* `pow_sub_sub_le` : Lemma 1, `x^n - 1 - n(x - 1) ≤ C(n, 2)(x - 1)² max(1, x)^(n-2)` for
  `x ≥ 0`.
* `card_emptyFamilies_le` : C1 in the form `#{M : Z(M) = ∅} ≤ #families · R` with
  `R = N^(-2) ∑_(P,Q) (x^n - 1 - n(x - 1))`, `x = (N - 2D + J)N/(N - D)² = 1 + aδ`. This is
  Lemma 0 and `P(Z = ∅) ≤ R/(1 + R) ≤ R`.
-/

open Finset

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- Inclusion–exclusion for one coordinate (`q-second-moment-extend.md` §2, Lemma 0, af8925f):
`#{X : ¬Ham P X ∧ ¬Ham Q X} + 2D = N + J(P, Q)`. -/
theorem card_not_ham_two_add (P Q : PerfectMatching (Vertex m)) :
    #{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} +
        2 * (2 ^ (m - 1) * (m - 1).factorial) =
      Nat.doubleFactorial (2 * m - 1) + jointCount P Q := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (PerfectMatching (Vertex m)))) fun X ↦ Ham P X ∨ Ham Q X
  have h2 := Finset.card_union_add_card_inter (univ.filter fun X ↦ Ham P X)
    (univ.filter fun X ↦ Ham Q X)
  rw [← Finset.filter_or, ← Finset.filter_and, card_ham_left, card_ham_left] at h2
  have hJ : jointCount P Q = #{X | Ham P X ∧ Ham Q X} := by
    unfold jointCount
    congr 1
    ext X
    simp [ham_comm]
  simp only [not_or] at h1
  rw [Finset.card_univ, card_eq_doubleFactorial (card_vertex m)] at h1
  omega

/-- The number of families with both `P` and `Q` zero states is
`#{X : ¬Ham P X ∧ ¬Ham Q X}^n` (`q-second-moment-extend.md` §2, Lemma 0, af8925f). -/
theorem card_isZeroState_two (ι : Type*) [Fintype ι] [DecidableEq ι]
    (P Q : PerfectMatching (Vertex m)) :
    #{M : ι → PerfectMatching (Vertex m) | IsZeroState M P ∧ IsZeroState M Q} =
      #{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} ^ Fintype.card ι := by
  have h : (univ.filter fun M : ι → PerfectMatching (Vertex m) ↦
      IsZeroState M P ∧ IsZeroState M Q) =
      Fintype.piFinset fun _ ↦ univ.filter fun X ↦ ¬Ham P X ∧ ¬Ham Q X := by
    ext M
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, IsZeroState]
    exact forall_and.symm
  rw [h, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

/-- **The second-moment identity** (`q-second-moment-extend.md` §2, Lemma 0, and §9 item 1,
af8925f): `∑_M |Z(M)|² = ∑_(P,Q) #{X : ¬Ham P X ∧ ¬Ham Q X}^n` over all families
`M : ι → PerfectMatching (Vertex m)`, with `n = |ι|`. By `card_not_ham_two_add` the base is
`N - 2D + J(P, Q)`. -/
theorem sum_card_zeroStates_sq (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card ^ 2 =
      ∑ P, ∑ Q, #{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} ^ Fintype.card ι := by
  calc ∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card ^ 2
      = ∑ M : ι → PerfectMatching (Vertex m), ∑ P, ∑ Q,
          if IsZeroState M P ∧ IsZeroState M Q then 1 else 0 := by
        refine sum_congr rfl fun M _ ↦ ?_
        rw [sq, zeroStates, card_filter, sum_mul_sum]
        refine sum_congr rfl fun P _ ↦ sum_congr rfl fun Q _ ↦ ?_
        split_ifs <;> simp_all
    _ = ∑ P, ∑ Q, ∑ M : ι → PerfectMatching (Vertex m),
          if IsZeroState M P ∧ IsZeroState M Q then 1 else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun P _ ↦ sum_comm
    _ = _ := by
        refine sum_congr rfl fun P _ ↦ sum_congr rfl fun Q _ ↦ ?_
        rw [← card_filter, card_isZeroState_two]

/-- `∑_Q J(P, Q) = D²`, by counting the pairs `(R, Q)` with `Ham R P` and `Ham R Q`
(`q-second-moment-extend.md` §2, Lemma 0, af8925f). So `E δ = 0`. -/
theorem sum_jointCount (P : PerfectMatching (Vertex m)) :
    ∑ Q, jointCount P Q = (2 ^ (m - 1) * (m - 1).factorial) ^ 2 := by
  unfold jointCount
  simp_rw [card_filter]
  rw [sum_comm]
  have h : ∀ R : PerfectMatching (Vertex m), (∑ Q, if Ham R P ∧ Ham R Q then 1 else 0) =
      if Ham R P then 2 ^ (m - 1) * (m - 1).factorial else 0 := by
    intro R
    split_ifs with hR
    · simp only [hR, true_and]
      rw [← card_filter, card_ham_left]
    · simp [hR]
  rw [sum_congr rfl fun R _ ↦ h R, ← sum_filter, sum_const, smul_eq_mul]
  have hc : #{R : PerfectMatching (Vertex m) | Ham R P} = 2 ^ (m - 1) * (m - 1).factorial := by
    rw [← card_ham_left P]
    congr 1
    ext R
    simp [ham_comm]
  rw [hc, sq]

/-- **Cauchy–Schwarz** (`q-second-moment-extend.md` §8, C1, af8925f):
`(∑_M |Z(M)|)² ≤ #{M : Z(M) ≠ ∅} · ∑_M |Z(M)|²`. -/
theorem sq_sum_card_zeroStates_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card : ℕ) : ℝ) ^ 2 ≤
      (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅} : ℝ) *
        ∑ M : ι → PerfectMatching (Vertex m), ((zeroStates M).card : ℝ) ^ 2 := by
  set S := univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ zeroStates M ≠ ∅
  have h1 : ∑ M : ι → PerfectMatching (Vertex m), ((zeroStates M).card : ℝ) =
      ∑ M ∈ S, ((zeroStates M).card : ℝ) := by
    rw [sum_filter]
    refine sum_congr rfl fun M _ ↦ ?_
    split_ifs with h
    · rfl
    · rw [not_not.mp h, card_empty, Nat.cast_zero]
  have h2 : ∑ M ∈ S, ((zeroStates M).card : ℝ) ^ 2 ≤
      ∑ M : ι → PerfectMatching (Vertex m), ((zeroStates M).card : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
  push_cast
  rw [h1]
  exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))

/-- **Lemma 1** (`q-second-moment-extend.md` §2, af8925f), upper half:
`x^(n+2) - 1 - (n + 2)(x - 1) ≤ C(n + 2, 2)(x - 1)² max(1, x)^n` for `x ≥ 0`. -/
theorem pow_sub_sub_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (n + 2) - 1 - (n + 2) * (x - 1) ≤
      (n + 2) * (n + 1) / 2 * (x - 1) ^ 2 * max 1 x ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, pow_zero, mul_one]
    nlinarith
  | succ n ih =>
    have hM1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
    have hMx : x ≤ max 1 x := le_max_right _ _
    have hf : 0 ≤ x ^ (n + 2) - 1 - (n + 2) * (x - 1) := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ x - 1 by linarith) (n + 2)
      rw [add_sub_cancel] at this
      push_cast at this
      linarith
    have hpow : (1 : ℝ) ≤ max 1 x ^ (n + 1) := one_le_pow₀ hM1
    have hy : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have e : x ^ (n + 1 + 2) - 1 - ((n + 1 : ℕ) + 2 : ℝ) * (x - 1) =
        x * (x ^ (n + 2) - 1 - (n + 2) * (x - 1)) + (n + 2) * (x - 1) ^ 2 := by
      push_cast
      ring
    rw [e]
    have h1 : x * (x ^ (n + 2) - 1 - (n + 2) * (x - 1)) ≤
        max 1 x * ((n + 2) * (n + 1) / 2 * (x - 1) ^ 2 * max 1 x ^ n) :=
      mul_le_mul hMx ih hf (by linarith)
    have h2 : (n + 2 : ℝ) * (x - 1) ^ 2 ≤ (n + 2) * (x - 1) ^ 2 * max 1 x ^ (n + 1) :=
      le_mul_of_one_le_right (by positivity) hpow
    have e2 : max 1 x * ((n + 2) * (n + 1) / 2 * (x - 1) ^ 2 * max 1 x ^ n) =
        (n + 2) * (n + 1) / 2 * (x - 1) ^ 2 * max 1 x ^ (n + 1) := by ring
    push_cast
    nlinarith

/-- An abstract form of C1: if `good + bad = fam`, `S₁² ≤ good · S₂` and `S₁, S₂ > 0`, then
`bad ≤ fam (S₂ fam / S₁² - 1)`. -/
theorem bad_le_of_sq_le {bad good fam S1 S2 : ℝ} (hsum : bad + good = fam) (hS1 : 0 < S1)
    (hS2 : 0 < S2) (hcs : S1 ^ 2 ≤ good * S2) :
    bad ≤ fam * (S2 * fam / S1 ^ 2 - 1) := by
  have hgood : S1 ^ 2 / S2 ≤ good := by rwa [div_le_iff₀ hS2]
  set t := S1 ^ 2 / S2 with ht
  have htpos : 0 < t := by positivity
  have hfam : fam * (S2 * fam / S1 ^ 2 - 1) = fam ^ 2 / t - fam := by
    rw [ht]
    field_simp
  rw [hfam]
  have key : 2 * fam - t ≤ fam ^ 2 / t := by
    rw [le_div_iff₀ htpos]
    nlinarith [sq_nonneg (fam - t)]
  linarith

/-- `x(P, Q) = (N - 2D + J(P, Q)) N / (N - D)² = 1 + aδ(P, Q)` with `a = p²/(1 - p)²` and
`δ = J N / D² - 1` (`q-second-moment-extend.md` §2, Lemma 0, af8925f). -/
noncomputable def pairX (P Q : PerfectMatching (Vertex m)) : ℝ :=
  ((Nat.doubleFactorial (2 * m - 1) : ℝ) - 2 * (2 ^ (m - 1) * (m - 1).factorial : ℕ) +
      jointCount P Q) * Nat.doubleFactorial (2 * m - 1) /
    ((Nat.doubleFactorial (2 * m - 1) : ℝ) - (2 ^ (m - 1) * (m - 1).factorial : ℕ)) ^ 2

/-- `D < N` for `m ≥ 2`: some `X` is not Hamiltonian with a given `P`, namely `P` itself. -/
theorem ham_count_lt (hm : 2 ≤ m) :
    2 ^ (m - 1) * (m - 1).factorial < Nat.doubleFactorial (2 * m - 1) := by
  have h := card_not_ham (factor m 0)
  have hpos : 0 < #{X : PerfectMatching (Vertex m) | ¬Ham (factor m 0) X} := by
    refine card_pos.mpr ⟨factor m 0, ?_⟩
    rw [mem_filter]
    refine ⟨mem_univ _, not_ham_of_mate_eq_of_two_lt (v := none) ?_ rfl⟩
    rw [card_vertex]
    omega
  have := ham_count_le (m := m)
  omega

/-- `∑_(P,Q) x(P, Q) = N²`, which is `E δ = 0` (`q-second-moment-extend.md` §2, Lemma 0,
af8925f). -/
theorem sum_pairX (hm : 2 ≤ m) :
    ∑ P : PerfectMatching (Vertex m), ∑ Q, pairX P Q =
      (Nat.doubleFactorial (2 * m - 1) : ℝ) ^ 2 := by
  have hlt : ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) <
      (Nat.doubleFactorial (2 * m - 1) : ℝ) := by exact_mod_cast ham_count_lt hm
  have hND : (Nat.doubleFactorial (2 * m - 1) : ℝ) -
      ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ≠ 0 := by linarith
  have hcard : Fintype.card (PerfectMatching (Vertex m)) = Nat.doubleFactorial (2 * m - 1) :=
    card_eq_doubleFactorial (card_vertex m)
  have hrow : ∀ P : PerfectMatching (Vertex m), ∑ Q, pairX P Q =
      (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
    intro P
    unfold pairX
    rw [← sum_div, ← sum_mul, sum_add_distrib, sum_const, card_univ, hcard, nsmul_eq_mul,
      ← Nat.cast_sum, sum_jointCount, Nat.cast_pow]
    set N : ℝ := ((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ)
    set D : ℝ := ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ)
    rw [div_eq_iff (pow_ne_zero 2 hND)]
    ring
  rw [sum_congr rfl fun P _ ↦ hrow P, sum_const, card_univ, hcard, nsmul_eq_mul, sq]

/-- **C1 with Lemma 0** (`q-second-moment-extend.md` §2 and §8, af8925f; checked in
`q-second-moment-factcheck-extend.md`, rows L0 and C1, af8925f). For `m ≥ 2`, the number of
families `M : ι → PerfectMatching (Vertex m)` with no zero state is at most the number of families
times `R = N^(-2) ∑_(P,Q) (x^n - 1 - n(x - 1))`, `x = pairX P Q`, `n = |ι|`. Here `1 + R` is
`E|Z|²/(E|Z|)²`, and Cauchy–Schwarz gives `P(Z = ∅) ≤ R/(1 + R) ≤ R`. -/
theorem card_emptyFamilies_le (hm : 2 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        ((∑ P : PerfectMatching (Vertex m), ∑ Q,
          (pairX P Q ^ Fintype.card ι - 1 - Fintype.card ι * (pairX P Q - 1))) /
            (Nat.doubleFactorial (2 * m - 1) : ℝ) ^ 2) := by
  set N : ℝ := ((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ) with hN
  set D : ℝ := ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) with hD
  set n := Fintype.card ι
  have hlt : D < N := by
    rw [hD, hN]
    exact_mod_cast ham_count_lt hm
  have hD0 : 0 < D := by
    rw [hD]
    exact_mod_cast Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have hN0 : 0 < N := by linarith
  have hcard : Fintype.card (PerfectMatching (Vertex m)) = Nat.doubleFactorial (2 * m - 1) :=
    card_eq_doubleFactorial (card_vertex m)
  have hfam : (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) = N ^ n := by
    rw [Fintype.card_fun, hcard]
    push_cast
    rfl
  set S1 : ℝ := ((∑ M : ι → PerfectMatching (Vertex m), (zeroStates M).card : ℕ) : ℝ)
  set S2 : ℝ := ∑ M : ι → PerfectMatching (Vertex m), ((zeroStates M).card : ℝ) ^ 2
  have hS1 : S1 = N * (N - D) ^ n := by
    simp only [S1]
    rw [sum_card_zeroStates, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub ham_count_le]
  have hbase : ∀ P Q : PerfectMatching (Vertex m),
      (#{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} : ℝ) =
        N - 2 * D + jointCount P Q := by
    intro P Q
    have := card_not_ham_two_add P Q
    have h' : (#{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} : ℝ) + 2 * D =
        N + jointCount P Q := by
      rw [hD, hN]
      exact_mod_cast this
    linarith
  have hS2 : S2 = ∑ P : PerfectMatching (Vertex m), ∑ Q, (N - 2 * D + jointCount P Q) ^ n := by
    simp only [S2]
    have := congrArg (Nat.cast (R := ℝ)) (sum_card_zeroStates_sq (m := m) ι)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun P _ ↦ sum_congr rfl fun Q _ ↦ ?_
    rw [hbase]
  have hS1pos : 0 < S1 := by
    rw [hS1]
    have : 0 < N - D := by linarith
    positivity
  have hcs : S1 ^ 2 ≤ (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅} : ℝ) * S2 :=
    sq_sum_card_zeroStates_le (m := m) ι
  have hgood : (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) +
      #{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅} =
        Fintype.card (ι → PerfectMatching (Vertex m)) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := univ)
      fun M : ι → PerfectMatching (Vertex m) ↦ zeroStates M = ∅
  have hS2pos : 0 < S2 := by
    by_contra h
    have h0 : S2 = 0 := le_antisymm (not_lt.mp h) (sum_nonneg fun _ _ ↦ sq_nonneg _)
    rw [h0, mul_zero] at hcs
    nlinarith [hS1pos]
  refine (bad_le_of_sq_le hgood hS1pos hS2pos hcs).trans (le_of_eq ?_)
  congr 1
  have hND : N - D ≠ 0 := by linarith
  have hx : ∀ P Q : PerfectMatching (Vertex m),
      pairX P Q = (N - 2 * D + jointCount P Q) * N / (N - D) ^ 2 := fun P Q ↦ rfl
  have hsumx := sum_pairX hm
  have hsplit : ∑ P : PerfectMatching (Vertex m), ∑ Q,
      (pairX P Q ^ n - 1 - n * (pairX P Q - 1)) =
        ∑ P : PerfectMatching (Vertex m), ∑ Q, pairX P Q ^ n - N ^ 2 := by
    simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, hcard, nsmul_eq_mul]
    rw [hsumx, ← hN]
    ring
  have hxn : ∑ P : PerfectMatching (Vertex m), ∑ Q, pairX P Q ^ n =
      S2 * N ^ n / (N - D) ^ (2 * n) := by
    have hterm : ∀ P Q : PerfectMatching (Vertex m), pairX P Q ^ n =
        (N - 2 * D + jointCount P Q) ^ n * N ^ n / (N - D) ^ (2 * n) := by
      intro P Q
      rw [hx, div_pow, mul_pow, ← pow_mul]
    simp_rw [hterm]
    rw [hS2, sum_mul, sum_div]
    refine sum_congr rfl fun P _ ↦ ?_
    rw [sum_mul, sum_div]
  rw [hsplit, hxn, hS1, hfam]
  field_simp
  ring

end RoundRobin.Canonical.RandomFamily

end Pairing
