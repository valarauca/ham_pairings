import Repair.PairVariance
import Repair.RandomFamily.SecondMoment

/-!
# Nonvacuity of the random-family lower bound (COD-288)

Source: `results/q-second-moment-extend.md` §2 to §6 and §8 (Lemma 0 to Lemma 4, Theorem 1,
C1, C2) and `results/q-second-moment-contra.md` §3 (organize-archive af8925f), checked in
`results/q-second-moment-factcheck-extend.md` and `results/q-second-moment-factcheck-contra.md`
(af8925f). Families `M : ι → PerfectMatching (Vertex m)` carry the counting measure,
`n = |ι|`, `N = (2m - 1)!!`, `D = 2^(m-1)(m-1)!`, `p = D/N`, `a = (p/(1 - p))²` and
`δ(P, Q) = J(P, Q) N / D² - 1`.

The route is the extend's, with one change in the treatment of the tail of `δ`. Lemma 4 bounds
`δ` through the number `l` of shared edges. Here the pairs are split at `s = 2l < 2⌊m/2⌋`.
On the small side `jointCount_div_psiK_sq_le` gives `1 + δ ≤ 27/16`. On the large side
`x ≤ 1/(1 - p)` and the number of such pairs is at most `N 4^m (2m - 2⌊m/2⌋ - 1)!!`
(`card_agree_ge_le`), a crude form of Lemma 4(c).

* `card_agree_ge_le` : at most `2^|W| (|W| - t - 1)!!` matchings `Q` agree with `P` on `t` or
  more vertices.
* `sum_sq_delta_eq` : `∑_Q δ(P, Q)² = N · cGen P`, so `cGen` of
  `repair/Repair/PairVariance.lean` (main 27c43f7) is
  `E δ²` (`q-second-moment-extend.md` §3, Lemma 2, the identification).
* `card_emptyFamilies_le_of_cGen` (Theorem 1, explicit form) : if `cGen B ≤ c/m²` for every
  `B`, then `P(Z(M) = ∅) ≤ C(n, 2)[a²(1 + 11a/16)^(n-2) c/m² + (1 - p)^(-n) 4^m /
  (m + 1)^⌊m/2⌋]` for `m ≥ 2`, `n ≥ 2`.
* `card_emptyFamilies_le_hundred` : at `n = 2m - 1` and `m ≥ 100`,
  `P(Z(M) = ∅) ≤ (7c + 1/100)/m²`.
* `nonvacuity_corollaryAPrime` (C2 with Theorem A′) : at `n = 2m - 1`, `m ≥ 100` and
  `K ≤ K_m`, at least a fraction `1 - m^(-3/2) - (7c + 1/100)/m²` of the families have
  `Z(M) ≠ ∅` and `¬RepairBoundFor (zeroStates M) G K` at every six-vertex gadget `G`.

The hypothesis `cGen B ≤ c/m²` is Lemma 2 of the extend, `E δ² = c_gen ≤ c1 + O(m^(-7/2))`
with `m² c1 → 1/8`. It needs the spherical functions of the Gelfand pair `(S_2m, H_m)`, which
are not formalized (`repair/Repair/PairVariance.lean`, main 27c43f7, takes a `HamSpectral`
resolution as input for the same
reason). `cGen_le` gives the trivial bound `cGen B ≤ (N/D)²`, which shows the hypothesis is
satisfiable at every `m` but carries no rate.
-/

open Finset

namespace Pairing

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching Real

section DoubleFactorial

/-- `n‼ ≤ (n + 1)‼`. -/
theorem doubleFactorial_le_succ : ∀ n : ℕ, n.doubleFactorial ≤ (n + 1).doubleFactorial
  | 0 => le_rfl
  | 1 => by decide
  | n + 2 => by
    rw [Nat.doubleFactorial_add_two, show n + 2 + 1 = (n + 1) + 2 by omega,
      Nat.doubleFactorial_add_two]
    exact Nat.mul_le_mul (by omega) (doubleFactorial_le_succ n)

/-- The double factorial is monotone. -/
theorem doubleFactorial_mono {a b : ℕ} (h : a ≤ b) : a.doubleFactorial ≤ b.doubleFactorial := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (doubleFactorial_le_succ b)

/-- `(n + 2)^k n‼ ≤ (n + 2k)‼`. -/
theorem pow_mul_doubleFactorial_le (n k : ℕ) :
    (n + 2) ^ k * n.doubleFactorial ≤ (n + 2 * k).doubleFactorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + 2 * (k + 1) = (n + 2 * k) + 2 by ring, Nat.doubleFactorial_add_two, pow_succ,
      mul_comm ((n + 2) ^ k), mul_assoc]
    exact Nat.mul_le_mul (by omega) ih

/-- `(m + 1)^⌊m/2⌋ (2m - 2⌊m/2⌋ - 1)‼ ≤ (2m - 1)‼`. -/
theorem pow_half_mul_doubleFactorial_le (m : ℕ) (hm : 1 ≤ m) :
    (m + 1) ^ (m / 2) * (2 * m - 2 * (m / 2) - 1).doubleFactorial ≤
      (2 * m - 1).doubleFactorial := by
  have h := pow_mul_doubleFactorial_le (2 * m - 2 * (m / 2) - 1) (m / 2)
  rw [show 2 * m - 2 * (m / 2) - 1 + 2 * (m / 2) = 2 * m - 1 by omega] at h
  refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)) h

end DoubleFactorial

section Tail

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The agreement set `{x : P(x) = Q(x)}` is closed under `P`. -/
theorem mate_mem_agree_compl (P Q : PerfectMatching W) :
    ∀ v ∈ (univ.filter fun x ↦ P.mate x = Q.mate x)ᶜ,
      P.mate v ∈ (univ.filter fun x ↦ P.mate x = Q.mate x)ᶜ := by
  intro v hv
  simp only [mem_compl, mem_filter, mem_univ, true_and] at hv ⊢
  intro h
  apply hv
  rw [P.mate_mate] at h
  calc P.mate v = Q.mate (Q.mate (P.mate v)) := (Q.mate_mate _).symm
    _ = Q.mate v := by rw [← h]

/-- **A crude Lemma 4(c)** (`q-second-moment-extend.md` §5, af8925f). At most
`2^|W| (|W| - t - 1)‼` perfect matchings `Q` agree with a fixed `P` on at least `t` vertices.
Each such `Q` is fixed off its agreement set `C`, and by `glueEquiv` there are
`(|W| - |C| - 1)‼` matchings that agree with `P` on `C`. -/
theorem card_agree_ge_le (P : PerfectMatching W) (t : ℕ) :
    #{Q : PerfectMatching W | t ≤ #{x | P.mate x = Q.mate x}} ≤
      2 ^ Fintype.card W * (Fintype.card W - t - 1).doubleFactorial := by
  set S := univ.filter fun Q : PerfectMatching W ↦ t ≤ #{x | P.mate x = Q.mate x}
  set ag : PerfectMatching W → Finset W := fun Q ↦ univ.filter fun x ↦ P.mate x = Q.mate x
  rw [card_eq_sum_card_fiberwise (f := ag) (t := univ) fun _ _ ↦ mem_coe.mpr (mem_univ _)]
  calc ∑ C : Finset W, #{Q ∈ S | ag Q = C}
      ≤ ∑ _C : Finset W, (Fintype.card W - t - 1).doubleFactorial := by
        refine sum_le_sum fun C _ ↦ ?_
        rcases Finset.eq_empty_or_nonempty (S.filter fun Q ↦ ag Q = C) with h | ⟨Q₀, hQ₀⟩
        · rw [h, card_empty]
          exact Nat.zero_le _
        rw [mem_filter] at hQ₀
        obtain ⟨hQ₀S, rfl⟩ := hQ₀
        have ht : t ≤ #(ag Q₀) := (mem_filter.mp hQ₀S).2
        have hA := mate_mem_agree_compl P Q₀
        have hsub : (S.filter fun Q ↦ ag Q = ag Q₀) ⊆
            univ.filter fun Z : PerfectMatching W ↦ ∀ v ∉ (ag Q₀)ᶜ, Z.mate v = P.mate v := by
          intro Q hQ
          rw [mem_filter] at hQ ⊢
          refine ⟨mem_univ _, fun v hv ↦ ?_⟩
          rw [Finset.notMem_compl, ← hQ.2] at hv
          exact ((mem_filter.mp hv).2).symm
        refine (card_le_card hsub).trans ?_
        rw [← Fintype.card_subtype, ← Fintype.card_congr (glueEquiv P _ hA)]
        have hcard : Fintype.card ((ag Q₀)ᶜ : Finset W) =
            2 * (pairType (restrict P _ hA) (restrict P _ hA)).sum :=
          (two_mul_sum_pairType _ _).symm
        rw [card_eq_doubleFactorial hcard]
        refine doubleFactorial_mono ?_
        have : Fintype.card ((ag Q₀)ᶜ : Finset W) = Fintype.card W - #(ag Q₀) := by
          rw [Fintype.card_coe, card_compl]
        omega
    _ = 2 ^ Fintype.card W * (Fintype.card W - t - 1).doubleFactorial := by
        rw [sum_const, card_univ, Fintype.card_finset, smul_eq_mul]

end Tail

section Main

variable {m : ℕ} [NeZero m]

/-- `∑_A h(R, A) h(A, B) = J(B, R)`. -/
theorem sum_hamInd_mul_hamInd (R B : PerfectMatching (Vertex m)) :
    ∑ A, hamInd R A * hamInd A B = (jointCount B R : ℝ) := by
  simp only [hamInd, ite_mul, one_mul, zero_mul, ← ite_and]
  rw [sum_boole, jointCount]
  congr 2
  ext A
  simp [ham_comm A B, ham_comm R A, and_comm]

/-- `|Ham(B)| = D`. -/
theorem hamDeg_eq_ham (B : PerfectMatching (Vertex m)) :
    hamDeg B = 2 ^ (m - 1) * (m - 1).factorial := by
  rw [hamDeg, ← card_ham_left B]
  congr 1
  ext C
  simp [ham_comm]

/-- `J(P, Q) ≤ D`. -/
theorem jointCount_le_ham (P Q : PerfectMatching (Vertex m)) :
    jointCount P Q ≤ 2 ^ (m - 1) * (m - 1).factorial := by
  rw [← card_ham_left P, jointCount]
  refine card_le_card fun R hR ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hR ⊢
  exact (ham_comm R P).mp hR.1

/-- `J(P, Q) = J(Q, P)`. -/
theorem jointCount_comm (P Q : PerfectMatching (Vertex m)) : jointCount P Q = jointCount Q P := by
  unfold jointCount
  congr 1
  ext R
  simp [and_comm]

/-- **The identification of `cGen`** (`q-second-moment-extend.md` §3, Lemma 2, and §7,
af8925f): `∑_Q δ(P, Q)² = N · cGen P` with `δ = J N / D² - 1`. So `cGen P = E_Q δ²`, the
quantity of Lemma 2. -/
theorem sum_sq_delta_eq (P : PerfectMatching (Vertex m)) :
    ∑ Q, ((jointCount P Q : ℝ) * (Nat.doubleFactorial (2 * m - 1) : ℕ) /
        ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ^ 2 - 1) ^ 2 =
      (Nat.doubleFactorial (2 * m - 1) : ℝ) * cGen P := by
  set N : ℝ := ((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ) with hN
  set D : ℝ := ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) with hD
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact_mod_cast (Nat.mul_pos (by positivity) (Nat.factorial_pos _)).ne'
  have hJ : ∑ Q, (jointCount P Q : ℝ) = D ^ 2 := by
    rw [hD]
    exact_mod_cast sum_jointCount P
  unfold cGen
  rw [hamDeg_eq_ham, card_eq_doubleFactorial (card_vertex m)]
  simp_rw [sum_hamInd_mul_hamInd, jointCount_comm P]
  rw [← hN, ← hD]
  have e : ∀ Q : PerfectMatching (Vertex m), ((jointCount Q P : ℝ) * N / D ^ 2 - 1) ^ 2 =
      N ^ 2 / D ^ 4 * (jointCount Q P : ℝ) ^ 2 - 2 * N / D ^ 2 * jointCount Q P + 1 := by
    intro Q
    field_simp
    ring
  simp_rw [e]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const, card_univ,
    card_eq_doubleFactorial (card_vertex m), nsmul_eq_mul, mul_one]
  simp_rw [jointCount_comm _ P]
  rw [hJ, ← hN]
  field_simp
  ring

/-- The trivial bound `cGen B ≤ (N/D)²`, from `J ≤ D`. It shows that the hypothesis
`cGen B ≤ c/m²` of `card_emptyFamilies_le_of_cGen` holds at every `m` for some `c`. -/
theorem cGen_le (B : PerfectMatching (Vertex m)) :
    cGen B ≤ ((Nat.doubleFactorial (2 * m - 1) : ℕ) /
      ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ)) ^ 2 := by
  set N : ℝ := ((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ) with hN
  set D : ℝ := ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]
    exact_mod_cast Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have hN0 : 0 < N := by
    rw [hN]
    exact_mod_cast Nat.doubleFactorial_pos _
  unfold cGen
  rw [hamDeg_eq_ham, card_eq_doubleFactorial (card_vertex m)]
  simp_rw [sum_hamInd_mul_hamInd]
  rw [← hN, ← hD]
  have hb : ∑ R : PerfectMatching (Vertex m), (jointCount B R : ℝ) ^ 2 ≤ N * D ^ 2 := by
    calc ∑ R : PerfectMatching (Vertex m), (jointCount B R : ℝ) ^ 2
        ≤ ∑ _R : PerfectMatching (Vertex m), D ^ 2 := by
          refine sum_le_sum fun R _ ↦ pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2
          rw [hD]
          exact_mod_cast jointCount_le_ham B R
      _ = N * D ^ 2 := by
          rw [sum_const, card_univ, card_eq_doubleFactorial (card_vertex m), nsmul_eq_mul]
  have : N / D ^ 4 * ∑ R : PerfectMatching (Vertex m), (jointCount B R : ℝ) ^ 2 ≤ (N / D) ^ 2 := by
    calc N / D ^ 4 * ∑ R : PerfectMatching (Vertex m), (jointCount B R : ℝ) ^ 2
        ≤ N / D ^ 4 * (N * D ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (N / D) ^ 2 := by field_simp
  linarith

/-- `x(P, Q) - 1 = a δ(P, Q)` with `a = (D/(N - D))²` and `δ = J N / D² - 1`
(`q-second-moment-extend.md` §2, Lemma 0, af8925f). -/
theorem pairX_sub_one (hm : 2 ≤ m) (P Q : PerfectMatching (Vertex m)) :
    pairX P Q - 1 = (((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) /
        ((Nat.doubleFactorial (2 * m - 1) : ℕ) - ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ))) ^ 2 *
      ((jointCount P Q : ℝ) * (Nat.doubleFactorial (2 * m - 1) : ℕ) /
        ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ^ 2 - 1) := by
  have hlt : ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) <
      (Nat.doubleFactorial (2 * m - 1) : ℝ) := by exact_mod_cast ham_count_lt hm
  have hD0 : ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.mul_pos (by positivity) (Nat.factorial_pos _)).ne'
  have hND : (Nat.doubleFactorial (2 * m - 1) : ℝ) -
      ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) ≠ 0 := by linarith
  unfold pairX
  field_simp
  ring

/-- **Theorem 1, explicit conditional form** (`q-second-moment-extend.md` §6, af8925f; with the
Cauchy–Schwarz repair of `q-second-moment-factcheck-contra.md` §1 built in, since the bound below
uses `E δ²` only through `cGen`). Let `m ≥ 2`, `n = |ι| ≥ 2`, `p = pHam m`, `a = (p/(1 - p))²`,
and suppose `cGen B ≤ c/m²` for every `B` (Lemma 2, an input here). Then the fraction of
families `M : ι → PerfectMatching (Vertex m)` with `Z(M) = ∅` is at most
`C(n, 2) [a² (1 + 11a/16)^(n-2) c/m² + (1 - p)^(-n) 4^m / (m + 1)^⌊m/2⌋]`.

The pairs `(P, Q)` sharing fewer than `⌊m/2⌋` edges have `1 + δ ≤ 27/16` by
`jointCount_div_psiK_sq_le`, so Lemma 1 bounds their term by `C(n, 2) (1 + 11a/16)^(n-2) a² δ²`.
The other pairs have `x ≤ 1/(1 - p)`, and there are at most `N 4^m (2m - 2⌊m/2⌋ - 1)‼` of them
by `card_agree_ge_le`. -/
theorem card_emptyFamilies_le_of_cGen (hm : 2 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) {c : ℝ}
    (hc : ∀ B : PerfectMatching (Vertex m), cGen B ≤ c / m ^ 2) :
    (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        ((Fintype.card ι : ℝ) * (Fintype.card ι - 1) / 2 *
          ((pHam m / (1 - pHam m)) ^ 4 *
              (1 + 11 / 16 * (pHam m / (1 - pHam m)) ^ 2) ^ (Fintype.card ι - 2) * (c / m ^ 2) +
            (1 / (1 - pHam m)) ^ Fintype.card ι * 4 ^ m / ((m : ℝ) + 1) ^ (m / 2))) := by
  refine (card_emptyFamilies_le hm ι).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 2 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
  rw [hk, show k + 2 - 2 = k by omega]
  set N : ℝ := ((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ) with hN
  set D : ℝ := ((2 ^ (m - 1) * (m - 1).factorial : ℕ) : ℝ) with hD
  have hlt : D < N := by
    rw [hD, hN]
    exact_mod_cast ham_count_lt hm
  have hD0 : 0 < D := by
    rw [hD]
    exact_mod_cast Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have hN0 : 0 < N := by linarith
  have hND : 0 < N - D := by linarith
  have hp : pHam m = D / N := by
    unfold pHam
    rw [hD, hN]
    push_cast
    rfl
  have hpa : pHam m / (1 - pHam m) = D / (N - D) := by
    rw [hp]
    field_simp
  have hpX : 1 / (1 - pHam m) = N / (N - D) := by
    rw [hp]
    field_simp
  rw [hpa, hpX]
  set a : ℝ := (D / (N - D)) ^ 2 with ha
  have ha0 : 0 ≤ a := sq_nonneg _
  set X0 : ℝ := N / (N - D) with hX0
  have hX01 : 1 ≤ X0 := by
    rw [hX0, le_div_iff₀ hND]
    linarith
  set W : ℝ := (1 + 11 / 16 * a) ^ k with hW
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  set C : ℝ := ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1) / 2 with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg <;> linarith
  set t := 2 * (m / 2) with ht
  set δ : PerfectMatching (Vertex m) → PerfectMatching (Vertex m) → ℝ :=
    fun P Q ↦ (jointCount P Q : ℝ) * N / D ^ 2 - 1 with hδ
  have hx1 : ∀ P Q, pairX P Q - 1 = a * δ P Q := fun P Q ↦ pairX_sub_one hm P Q
  have hxpt : ∀ P Q : PerfectMatching (Vertex m),
      pairX P Q ^ (k + 2) - 1 - ((k + 2 : ℕ) : ℝ) * (pairX P Q - 1) ≤
        C * W * (pairX P Q - 1) ^ 2 +
          C * X0 ^ (k + 2) * (if t ≤ #{x | P.mate x = Q.mate x} then 1 else 0) := by
    intro P Q
    set x := pairX P Q with hx
    have hJD : (jointCount P Q : ℝ) ≤ D := by
      rw [hD]
      exact_mod_cast jointCount_le_ham P Q
    have hJ0 : (0 : ℝ) ≤ jointCount P Q := Nat.cast_nonneg _
    have hbase : 0 ≤ N - 2 * D + jointCount P Q := by
      have h := card_not_ham_two_add P Q
      have h' : (#{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} : ℝ) + 2 * D =
          N + jointCount P Q := by
        rw [hD, hN]
        exact_mod_cast h
      have : (0 : ℝ) ≤ #{X : PerfectMatching (Vertex m) | ¬Ham P X ∧ ¬Ham Q X} :=
        Nat.cast_nonneg _
      linarith
    have hx0 : 0 ≤ x := by
      rw [hx, pairX, ← hN, ← hD]
      positivity
    have hxX : x ≤ X0 := by
      rw [hx, pairX, ← hN, ← hD, hX0, div_le_div_iff₀ (by positivity) hND]
      have : (N - 2 * D + jointCount P Q) * N ≤ (N - D) * N :=
        mul_le_mul_of_nonneg_right (by linarith) hN0.le
      nlinarith
    have htay := pow_sub_sub_le k hx0
    have hCe : ((k : ℝ) + 2) * (k + 1) / 2 = C := by
      rw [hC]
      push_cast
      ring
    rw [hCe] at htay
    have hM1 : 1 ≤ max 1 x := le_max_left _ _
    push_cast
    split_ifs with hs
    · have hMX : max 1 x ≤ X0 := max_le hX01 hxX
      have hsq : (x - 1) ^ 2 ≤ X0 ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hpow : max 1 x ^ k ≤ X0 ^ k := pow_le_pow_left₀ (by linarith) hMX k
      have h1 : (x - 1) ^ 2 * max 1 x ^ k ≤ X0 ^ (k + 2) := by
        calc (x - 1) ^ 2 * max 1 x ^ k ≤ X0 ^ 2 * X0 ^ k :=
              mul_le_mul hsq hpow (by positivity) (by positivity)
          _ = X0 ^ (k + 2) := by ring
      have h2 : 0 ≤ C * W * (x - 1) ^ 2 := by positivity
      calc x ^ (k + 2) - 1 - ((k : ℝ) + 2) * (x - 1) ≤ C * (x - 1) ^ 2 * max 1 x ^ k := htay
        _ = C * ((x - 1) ^ 2 * max 1 x ^ k) := by ring
        _ ≤ C * X0 ^ (k + 2) := mul_le_mul_of_nonneg_left h1 hC0
        _ ≤ C * W * (x - 1) ^ 2 + C * X0 ^ (k + 2) * 1 := by linarith
    · have hs' : #{x | P.mate x = Q.mate x} ≤ m - 1 := by omega
      have hG := jointCount_div_psiK_sq_le m (Vertex m) (by omega) (card_vertex m) P Q
      have hψ : psiK m = D ^ 2 / N := by rw [psiK, hD, hN]
      rw [hψ] at hG
      set G : ℝ := (jointCount P Q : ℝ) / (D ^ 2 / N) with hGdef
      have hGδ : G = δ P Q + 1 := by
        rw [hGdef, hδ]
        field_simp
        ring
      have hG0 : 0 ≤ G := by positivity
      have hsr : ((#{x | P.mate x = Q.mate x} : ℕ) : ℝ) ≤ m - 1 := by
        have : ((#{x | P.mate x = Q.mate x} : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hs'
        rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have hG2 : G ^ 2 * m ≤ (9 / 8) ^ 2 * (2 * m - 1) := by
        have : G ^ 2 * m ≤ G ^ 2 * (2 * m - 1 - ((#{x | P.mate x = Q.mate x} : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg G)
        linarith
      have hmpos : (0 : ℝ) < m := by linarith
      have hG2' : G ^ 2 ≤ 81 / 32 := by
        have : G ^ 2 * m ≤ 81 / 32 * m := by linarith
        exact le_of_mul_le_mul_right this hmpos
      have hGle : G ≤ 27 / 16 := by
        have : G ^ 2 ≤ (27 / 16) ^ 2 := by linarith
        exact (pow_le_pow_iff_left₀ hG0 (by norm_num) (by norm_num)).mp this
      have hxle : x ≤ 1 + 11 / 16 * a := by
        have := hx1 P Q
        rw [← hx] at this
        have hδle : δ P Q ≤ 11 / 16 := by linarith
        have := mul_le_mul_of_nonneg_left hδle ha0
        linarith
      have hMle : max 1 x ≤ 1 + 11 / 16 * a := max_le (by linarith) hxle
      have hpow : max 1 x ^ k ≤ W := pow_le_pow_left₀ (by linarith) hMle k
      calc x ^ (k + 2) - 1 - ((k : ℝ) + 2) * (x - 1) ≤ C * (x - 1) ^ 2 * max 1 x ^ k := htay
        _ ≤ C * (x - 1) ^ 2 * W :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0 (sq_nonneg _))
        _ = C * W * (x - 1) ^ 2 + C * X0 ^ (k + 2) * 0 := by ring
  have hsum1 : ∑ P : PerfectMatching (Vertex m), ∑ Q, (pairX P Q - 1) ^ 2 ≤
      a ^ 2 * (N ^ 2 * (c / m ^ 2)) := by
    have e : ∀ P : PerfectMatching (Vertex m),
        ∑ Q, (pairX P Q - 1) ^ 2 = a ^ 2 * (N * cGen P) := by
      intro P
      simp_rw [hx1, mul_pow, ← mul_sum]
      rw [← sum_sq_delta_eq P]
    rw [sum_congr rfl fun P _ ↦ e P, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg a)
    calc ∑ P : PerfectMatching (Vertex m), N * cGen P
        ≤ ∑ _P : PerfectMatching (Vertex m), N * (c / m ^ 2) :=
          sum_le_sum fun P _ ↦ mul_le_mul_of_nonneg_left (hc P) hN0.le
      _ = N ^ 2 * (c / m ^ 2) := by
          rw [sum_const, card_univ, card_eq_doubleFactorial (card_vertex m), nsmul_eq_mul, ← hN]
          ring
  have hsum2 : ∑ P : PerfectMatching (Vertex m), ∑ Q : PerfectMatching (Vertex m),
      (if t ≤ #{x | P.mate x = Q.mate x} then (1 : ℝ) else 0) ≤
        N * (4 ^ m * ((2 * m - t - 1).doubleFactorial : ℝ)) := by
    calc ∑ P : PerfectMatching (Vertex m), ∑ Q : PerfectMatching (Vertex m),
        (if t ≤ #{x | P.mate x = Q.mate x} then (1 : ℝ) else 0)
        ≤ ∑ _P : PerfectMatching (Vertex m), 4 ^ m * ((2 * m - t - 1).doubleFactorial : ℝ) := by
          refine sum_le_sum fun P _ ↦ ?_
          rw [sum_boole]
          have h := card_agree_ge_le P t
          rw [card_vertex, pow_mul] at h
          exact_mod_cast h
      _ = N * (4 ^ m * ((2 * m - t - 1).doubleFactorial : ℝ)) := by
          rw [sum_const, card_univ, card_eq_doubleFactorial (card_vertex m), nsmul_eq_mul, ← hN]
  have hdf : ((2 * m - t - 1).doubleFactorial : ℝ) / N ≤ 1 / ((m : ℝ) + 1) ^ (m / 2) := by
    rw [div_le_div_iff₀ hN0 (by positivity), one_mul, hN]
    have := pow_half_mul_doubleFactorial_le m (by omega)
    rw [← ht] at this
    have h2 : (2 * m - t - 1).doubleFactorial * (m + 1) ^ (m / 2) ≤
        (2 * m - 1).doubleFactorial := by
      rw [mul_comm]
      exact this
    exact_mod_cast h2
  have htot := sum_le_sum fun P (_ : P ∈ (univ : Finset (PerfectMatching (Vertex m)))) ↦
    sum_le_sum fun Q (_ : Q ∈ (univ : Finset (PerfectMatching (Vertex m)))) ↦ hxpt P Q
  simp only [sum_add_distrib, ← mul_sum] at htot
  rw [div_le_iff₀ (by positivity)]
  push_cast at htot ⊢
  calc _ ≤ _ := htot
    _ ≤ C * W * (a ^ 2 * (N ^ 2 * (c / m ^ 2))) +
        C * X0 ^ (k + 2) * (N * (4 ^ m * ((2 * m - t - 1).doubleFactorial : ℝ))) := by
        gcongr
    _ ≤ C * W * (a ^ 2 * (N ^ 2 * (c / m ^ 2))) +
        C * X0 ^ (k + 2) * (N * (4 ^ m * (N / ((m : ℝ) + 1) ^ (m / 2)))) := by
        have hdf' : ((2 * m - t - 1).doubleFactorial : ℝ) ≤ N / ((m : ℝ) + 1) ^ (m / 2) := by
          have := mul_le_mul_of_nonneg_left hdf hN0.le
          rwa [mul_div_cancel₀ _ hN0.ne', mul_one_div] at this
        gcongr
    _ = _ := by
        rw [hC, hW, hX0, ha]
        push_cast
        ring

end Main

section Numeric

/-- `e^(4/3) < 3.8`, from `e < 2.7182818286` and `2.7182818286⁴ < 3.8³`. -/
theorem exp_four_thirds_lt : exp (4 / 3) < 3.8 := by
  have h : exp (4 / 3) ^ 3 = exp 1 ^ 4 := by
    rw [← exp_nat_mul, ← exp_nat_mul]
    norm_num
  have h1 : exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  have h2 : exp (4 / 3) ^ 3 < (3.8 : ℝ) ^ 3 := by
    rw [h]
    exact h1.trans (by norm_num)
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h2

/-- `2000 m⁴ 121^m ≤ 250^m` for `m ≥ 100`. -/
theorem two_thousand_mul_pow_le {m : ℕ} (hm : 100 ≤ m) : 2000 * m ^ 4 * 121 ^ m ≤ 250 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 100 * (m + 1) ≤ 101 * m := by omega
    have h2 : (100 * (m + 1)) ^ 4 ≤ (101 * m) ^ 4 := Nat.pow_le_pow_left h1 4
    rw [mul_pow, mul_pow] at h2
    have h3 : 121 * (m + 1) ^ 4 * 100 ^ 4 ≤ 250 * m ^ 4 * 100 ^ 4 :=
      calc 121 * (m + 1) ^ 4 * 100 ^ 4 = 121 * (100 ^ 4 * (m + 1) ^ 4) := by ring
        _ ≤ 121 * (101 ^ 4 * m ^ 4) := Nat.mul_le_mul_left _ h2
        _ = 12591308521 * m ^ 4 := by ring
        _ ≤ 25000000000 * m ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 250 * m ^ 4 * 100 ^ 4 := by ring
    have h4 : 121 * (m + 1) ^ 4 ≤ 250 * m ^ 4 := Nat.le_of_mul_le_mul_right h3 (by norm_num)
    calc 2000 * (m + 1) ^ 4 * 121 ^ (m + 1) = (2000 * 121 ^ m) * (121 * (m + 1) ^ 4) := by ring
      _ ≤ (2000 * 121 ^ m) * (250 * m ^ 4) := Nat.mul_le_mul_left _ h4
      _ = 250 * (2000 * m ^ 4 * 121 ^ m) := by ring
      _ ≤ 250 * 250 ^ m := Nat.mul_le_mul_left _ ih
      _ = 250 ^ (m + 1) := by ring

/-- `10^(m-1) ≤ (m + 1)^⌊m/2⌋` for `m ≥ 99`. -/
theorem ten_pow_le_pow_half {m : ℕ} (hm : 99 ≤ m) : 10 ^ (m - 1) ≤ (m + 1) ^ (m / 2) := by
  calc 10 ^ (m - 1) ≤ 10 ^ (2 * (m / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 100 ^ (m / 2) := by rw [pow_mul]; norm_num
    _ ≤ (m + 1) ^ (m / 2) := Nat.pow_le_pow_left (by omega) _

variable {m : ℕ} [NeZero m]

/-- For `m ≥ 100`, `p ≤ 1/11` and `(2m - 1) p² ≤ 3.1416 · 100/199`, from `μ = (2m - 1)p ≤ √(πm)`
(`sub_le_mul_pHam`). -/
theorem pHam_bounds_of_hundred (hm : 100 ≤ m) :
    pHam m ≤ 1 / 11 ∧ (2 * m - 1 : ℝ) * pHam m ^ 2 ≤ 3.1416 * 100 / 199 := by
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hμ := (sub_le_mul_pHam (m := m)).2
  have hp0 := pHam_nonneg (m := m)
  have hn0 : (0 : ℝ) < 2 * m - 1 := by linarith
  have hπ := pi_lt_d4
  have hπ0 := pi_pos
  have hπm : π * m ≤ ((2 * m - 1) / 11 : ℝ) ^ 2 := by
    rw [div_pow]
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hsq : √(π * m) ≤ (2 * m - 1) / 11 := by
    calc √(π * m) ≤ √(((2 * m - 1) / 11 : ℝ) ^ 2) := Real.sqrt_le_sqrt hπm
      _ = (2 * m - 1) / 11 := Real.sqrt_sq (by linarith)
  refine ⟨?_, ?_⟩
  · have h := hμ.trans hsq
    rw [le_div_iff₀ (by norm_num)] at h
    nlinarith
  · have hμ0 : 0 ≤ (2 * m - 1 : ℝ) * pHam m := mul_nonneg hn0.le hp0
    have hμ2 : ((2 * m - 1 : ℝ) * pHam m) ^ 2 ≤ π * m := by
      calc ((2 * m - 1 : ℝ) * pHam m) ^ 2 ≤ √(π * m) ^ 2 := pow_le_pow_left₀ hμ0 hμ 2
        _ = π * m := Real.sq_sqrt (by positivity)
    have e : (2 * m - 1 : ℝ) * pHam m ^ 2 = ((2 * m - 1 : ℝ) * pHam m) ^ 2 / (2 * m - 1) := by
      field_simp
    rw [e, div_le_iff₀ hn0]
    nlinarith

/-- `cGen B ≥ 0`, since `N · cGen B = ∑_Q δ(B, Q)²` (`sum_sq_delta_eq`). -/
theorem cGen_nonneg (B : PerfectMatching (Vertex m)) : 0 ≤ cGen B := by
  have h := sum_sq_delta_eq B
  have hN : (0 : ℝ) < (Nat.doubleFactorial (2 * m - 1) : ℕ) :=
    Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  have h0 : 0 ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) * cGen B := by
    rw [← h]
    exact sum_nonneg fun _ _ ↦ sq_nonneg _
  exact nonneg_of_mul_nonneg_right (by linarith) hN

/-- **Theorem 1 with explicit constants** (`q-second-moment-extend.md` §6 and §8, C1, af8925f).
Let `m ≥ 100`, `|ι| = 2m - 1`, and suppose `cGen B ≤ c/m²` for every perfect matching `B` of
`V_m` (Lemma 2 of the extend gives this with `c ≈ 1/8`, through spherical functions that are not
formalized). Then at most a fraction `(7c + 1/100)/m²` of the families
`M : ι → PerfectMatching (Vertex m)` have no zero state. The constant `7` is
`C(n, 2) a² e^(11na/16)` with `na ≤ 1.911`, and `1/100` absorbs the pairs sharing at least
`⌊m/2⌋` edges. -/
theorem card_emptyFamilies_le_hundred (hm : 100 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {c : ℝ}
    (hc : ∀ B : PerfectMatching (Vertex m), cGen B ≤ c / m ^ 2) :
    (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * ((7 * c + 1 / 100) / m ^ 2) := by
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hc0 : 0 ≤ c / m ^ 2 := (cGen_nonneg (factor m 0)).trans (hc _)
  refine (card_emptyFamilies_le_of_cGen (by omega) ι (by omega) hc).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [hι, show 2 * m - 1 - 2 = 2 * m - 3 by omega]
  have hnr : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hnr]
  obtain ⟨hp1, hnp⟩ := pHam_bounds_of_hundred hm
  set p := pHam m with hpdef
  have hp0 : 0 ≤ p := pHam_nonneg
  have h1p : (10 / 11 : ℝ) ≤ 1 - p := by linarith
  set q := p / (1 - p) with hqdef
  have hq0 : 0 ≤ q := div_nonneg hp0 (by linarith)
  have hq : q ≤ 11 / 10 * p := by
    rw [hqdef, div_le_iff₀ (by linarith)]
    nlinarith
  set nr : ℝ := 2 * m - 1 with hnrdef
  have hnr1 : (199 : ℝ) ≤ nr := by linarith
  have hna : nr * q ^ 2 ≤ 1.911 := by
    have : q ^ 2 ≤ (11 / 10 * p) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    have h2 : nr * q ^ 2 ≤ nr * (11 / 10 * p) ^ 2 := mul_le_mul_of_nonneg_left this (by linarith)
    nlinarith
  have hna0 : 0 ≤ nr * q ^ 2 := by positivity
  have hC : nr * (nr - 1) / 2 * q ^ 4 ≤ 1.911 ^ 2 / 2 := by
    have : nr * (nr - 1) / 2 * q ^ 4 ≤ (nr * q ^ 2) ^ 2 / 2 := by
      have : nr * (nr - 1) ≤ nr * nr := by nlinarith
      have hq4 : 0 ≤ q ^ 4 := by positivity
      nlinarith
    have h2 : (nr * q ^ 2) ^ 2 ≤ 1.911 ^ 2 := pow_le_pow_left₀ hna0 hna 2
    linarith
  have hW : (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) ≤ 3.8 := by
    have hk : ((2 * m - 3 : ℕ) : ℝ) ≤ nr := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    calc (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) ≤ exp (11 / 16 * q ^ 2) ^ (2 * m - 3) :=
          pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp (11 / 16 * q ^ 2)]) _
      _ = exp (((2 * m - 3 : ℕ) : ℝ) * (11 / 16 * q ^ 2)) := by rw [← exp_nat_mul]
      _ ≤ exp (4 / 3) := by
          refine exp_le_exp.mpr ?_
          have : ((2 * m - 3 : ℕ) : ℝ) * q ^ 2 ≤ nr * q ^ 2 :=
            mul_le_mul_of_nonneg_right hk (sq_nonneg q)
          nlinarith
      _ ≤ 3.8 := exp_four_thirds_lt.le
  have hX : 1 / (1 - p) ≤ 11 / 10 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hX0 : 0 ≤ 1 / (1 - p) := by positivity
  have hXn : (1 / (1 - p)) ^ (2 * m - 1) ≤ (121 / 100 : ℝ) ^ m := by
    calc (1 / (1 - p)) ^ (2 * m - 1) ≤ (11 / 10 : ℝ) ^ (2 * m - 1) := pow_le_pow_left₀ hX0 hX _
      _ ≤ (11 / 10 : ℝ) ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (121 / 100 : ℝ) ^ m := by rw [pow_mul]; norm_num
  have hden : (10 : ℝ) ^ (m - 1) ≤ ((m : ℝ) + 1) ^ (m / 2) := by
    exact_mod_cast ten_pow_le_pow_half (by omega : 99 ≤ m)
  have hden0 : (0 : ℝ) < 10 ^ (m - 1) := by positivity
  have hkey : (2000 : ℝ) * m ^ 4 * 121 ^ m ≤ 250 ^ m := by
    exact_mod_cast two_thousand_mul_pow_le hm
  have hCn : nr * (nr - 1) / 2 ≤ 2 * m ^ 2 := by nlinarith
  have hCn0 : 0 ≤ nr * (nr - 1) / 2 := by nlinarith
  have htail : nr * (nr - 1) / 2 * ((1 / (1 - p)) ^ (2 * m - 1) * 4 ^ m / ((m : ℝ) + 1) ^ (m / 2))
      ≤ 1 / 100 / m ^ 2 := by
    have h10 : (10 : ℝ) ^ m = 10 * 10 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc nr * (nr - 1) / 2 * ((1 / (1 - p)) ^ (2 * m - 1) * 4 ^ m / ((m : ℝ) + 1) ^ (m / 2))
        ≤ 2 * m ^ 2 * ((121 / 100 : ℝ) ^ m * 4 ^ m / 10 ^ (m - 1)) := by
          gcongr
      _ = 20 * m ^ 2 * (121 ^ m / 250 ^ m) := by
          rw [div_pow, show (250 : ℝ) ^ m = 25 ^ m * 10 ^ m by rw [← mul_pow]; norm_num,
            show (100 : ℝ) ^ m = 10 ^ m * 10 ^ m by rw [← mul_pow]; norm_num,
            show (4 : ℝ) ^ m = 100 ^ m / 25 ^ m by rw [← div_pow]; norm_num,
            show (100 : ℝ) ^ m = 10 ^ m * 10 ^ m by rw [← mul_pow]; norm_num, h10]
          field_simp
          ring
      _ ≤ 1 / 100 / m ^ 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hmain : nr * (nr - 1) / 2 * (q ^ 4 * (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) * (c / m ^ 2))
      ≤ 7 * (c / m ^ 2) := by
    have hW0 : 0 ≤ (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) := by positivity
    calc nr * (nr - 1) / 2 * (q ^ 4 * (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) * (c / m ^ 2))
        = (nr * (nr - 1) / 2 * q ^ 4) * (1 + 11 / 16 * q ^ 2) ^ (2 * m - 3) * (c / m ^ 2) := by
          ring
      _ ≤ (1.911 ^ 2 / 2) * 3.8 * (c / m ^ 2) := by gcongr
      _ ≤ 7 * (c / m ^ 2) := by nlinarith
  rw [mul_add]
  calc _ ≤ 7 * (c / m ^ 2) + 1 / 100 / m ^ 2 := by linarith
    _ = (7 * c + 1 / 100) / m ^ 2 := by ring

/-- **C1, nonvacuity** (`q-second-moment-extend.md` §8, C1, af8925f). Under the hypotheses of
`card_emptyFamilies_le_hundred`, at least a fraction `1 - (7c + 1/100)/m²` of the families
`M : ι → PerfectMatching (Vertex m)` have a zero state. -/
theorem card_nonempty_zeroStates_ge (hm : 100 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {c : ℝ}
    (hc : ∀ B : PerfectMatching (Vertex m), cGen B ≤ c / m ^ 2) :
    (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * (1 - (7 * c + 1 / 100) / m ^ 2) ≤
      (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅} : ℝ) := by
  have hE := card_emptyFamilies_le_hundred hm ι hι hc
  have hsum : (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) +
      #{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅} =
        Fintype.card (ι → PerfectMatching (Vertex m)) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := univ)
      fun M : ι → PerfectMatching (Vertex m) ↦ zeroStates M = ∅
  linarith

open Classical in
/-- **C2 with Theorem A′** (`q-second-moment-extend.md` §8, C2, af8925f, with the corollary of
Theorem A′ in `repair/Repair/RandomFamily/TheoremAPrime.lean`, main 27c43f7). Let `m ≥ 100`,
`|ι| = 2m - 1`, `K ≤ K_m`, and suppose
`cGen B ≤ c/m²` for every `B`. Then at least a fraction `1 - m^(-3/2) - (7c + 1/100)/m²` of the
families `M : ι → PerfectMatching (Vertex m)` have `Z(M) ≠ ∅` and `N(M, G) ≥ K + 1`, that is
`¬RepairBoundFor (zeroStates M) G K`, at every six-vertex gadget `G` at once. -/
theorem nonvacuity_corollaryAPrime (hm : 100 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2 * m - 1) {c : ℝ}
    (hc : ∀ B : PerfectMatching (Vertex m), cGen B ≤ c / m ^ 2) {K : ℕ}
    (hK : (K : ℤ) ≤ kAPrime m) :
    (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        (1 - (m : ℝ) ^ (-(3 / 2 : ℝ)) - (7 * c + 1 / 100) / m ^ 2) ≤
      (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅ ∧
        ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K} : ℝ) := by
  have hE := card_emptyFamilies_le_hundred hm ι hι hc
  have hB := corollaryAPrime (by omega) ι hι hK
  set E := univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ zeroStates M = ∅
  have e : (univ.filter fun M : ι → PerfectMatching (Vertex m) ↦ zeroStates M ≠ ∅ ∧
      ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K) =
        (E ∪ badFamilies ι m K)ᶜ := by
    ext M
    simp [E, mem_badFamilies]
  rw [e, card_compl, Nat.cast_sub (card_le_univ _)]
  have hu : ((E ∪ badFamilies ι m K).card : ℝ) ≤ E.card + (badFamilies ι m K).card := by
    exact_mod_cast card_union_le _ _
  linarith

end Numeric

end RoundRobin.Canonical.RandomFamily

end Pairing
