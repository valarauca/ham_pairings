import Mathlib.Algebra.BigOperators.Field
import Suppression.Prob

/-!
# Known inputs cannot pass Chebyshev: the binomial mixture (COD-146)

This file formalizes Proposition 2 of the bounded-radius spike
(`results/bounded-radius-spike.md` §3.1). Fix `n` events. Let `X = 0` with probability `q`, and
otherwise `X ~ Bin(N, p)`. Given `X`, the true set `H` is a uniform `X`-subset of `Fin n`, and
`A_t = {t ∈ H}`. The law of `H` is `mixWeight n q N p`, with
`U(H) = P(X = |H|) / C(n, |H|)`. It is exchangeable, since `U(H)` depends on `|H|` alone
(`mixWeight_map_perm`).

* `mixLaw q N p` is the law of `X`, and `binPmf N p` the binomial law.
* `card_superset_mul_descFactorial` : `#{H ⊇ S : |H| = x} (n)_k = C(n, x) (x)_k` for `|S| = k`.
* `sum_binPmf_mul_descFactorial` : `E[(Bin(N, p))_k] = (N)_k p^k`.
* `isProb_mixWeight` : `U` is a probability weight.
* `prob_superset_eq` (Proposition 2, exact formula) : `P(∩_{t ∈ S} A_t) = E[(X)_k] / (n)_k`
  with `k = |S|`, and `sum_mixWeight_mul_descFactorial` : `E[(X)_k] = (1 - q) (N)_k p^k` for
  `k ≥ 1`.
* `jointRatio_mixWeight` (Proposition 2, exact formula) : for `1 ≤ |S| = k`,
  `R_S = (1 - q)^(1-k) ((N)_k / N^k) (n^k / (n)_k)`, and `descFactorial_div_pow_eq_prod` :
  `(N)_k / N^k = ∏_{i < k} (1 - i / N)`.
* `mixture_props` (Proposition 2, finite-parameter form) : for `2 ≤ N ≤ n`, `0 ≤ q ≤ 1/2`,
  `0 < μ ≤ (1 - q) N` and `p = μ / ((1 - q) N)`, the law has `∑_t P(A_t) = μ`,
  `R_{s,t} = (1 - 1/N) (n / (n - 1)) / (1 - q)` for every pair, `2^(-k) ≤ R_S ≤ 2^(2k-1)` for
  `1 ≤ k`, `2k ≤ N` and `2k ≤ n`, and `q ≤ P(X = 0) = q + (1 - q)(1 - p)^N ≤ q + e^(-μ)`.
* `mixture_barrier` (Proposition 2) : for `m ≥ 144`, `n = 2m - 1`, every mean `0 < μ ≤ 2√m` and
  every target pair ratio `r ∈ [1 - 1/m, 1]`, some mixture has `∑_t P(A_t) = μ`, `R_{s,t} = r`
  for every pair, `2^(-k) ≤ R_S ≤ 2^(2k-1)` for `1 ≤ k ≤ √m`, and
  `1/(12√m) ≤ q ≤ 1/(3√m)` with `q ≤ P(X = 0) ≤ q + e^(-μ)`.

The interval `[1 - 1/m, 1]` contains `1 - 1/(4m) + O(m^(-3/2))` for large `m`, the true pair
ratio of Lemma B, and `μ_m ≤ √π √m ≤ 2√m`.

The spike states `P(X = 0) = q`. The binomial part also has mass at `0`, so in fact
`P(X = 0) = q + (1 - q)(1 - λ/N)^N`, which lies in `[q, q + e^(-μ)]`. The order `m^(-1/2)` of
`P(X = 0)` is unaffected.
-/

namespace Pairing

namespace MixtureBarrier

open Finset ChainRule

/-- The binomial law `P(Bin(N, p) = x) = C(N, x) p^x (1 - p)^(N - x)`
(`results/bounded-radius-spike.md`, Proposition 2). -/
noncomputable def binPmf (N : ℕ) (p : ℝ) (x : ℕ) : ℝ :=
  N.choose x * p ^ x * (1 - p) ^ (N - x)

/-- The law of `X` in Proposition 2 of `results/bounded-radius-spike.md`: `X = 0` with
probability `q`, and otherwise `X ~ Bin(N, p)`. -/
noncomputable def mixLaw (q : ℝ) (N : ℕ) (p : ℝ) (x : ℕ) : ℝ :=
  (if x = 0 then q else 0) + (1 - q) * binPmf N p x

/-- The law of the true set `H ⊆ Fin n` in Proposition 2 of `results/bounded-radius-spike.md`:
given `X`, `H` is a uniform `X`-subset, so `U(H) = P(X = |H|) / C(n, |H|)`. -/
noncomputable def mixWeight (n : ℕ) (q : ℝ) (N : ℕ) (p : ℝ) (H : Finset (Fin n)) : ℝ :=
  mixLaw q N p #H / n.choose #H

/-- The mixture weight is exchangeable: `U(σ H) = U(H)` for every permutation `σ` of `Fin n`
(`results/bounded-radius-spike.md`, Proposition 2). -/
theorem mixWeight_map_perm {n N : ℕ} {q p : ℝ} (σ : Equiv.Perm (Fin n)) (H : Finset (Fin n)) :
    mixWeight n q N p (H.map σ.toEmbedding) = mixWeight n q N p H := by
  rw [mixWeight, mixWeight, card_map]

/-- The `k`-point ratio `R_S = P(∩_{t ∈ S} A_t) / ∏_{t ∈ S} P(A_t)` with `A_t = {t ∈ H}`
(`results/bounded-radius-spike.md`, Proposition 2). -/
noncomputable def jointRatio {n : ℕ} (w : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  prob w {H | S ⊆ H} / ∏ t ∈ S, prob w {H | t ∈ H}

section Count

variable {n : ℕ}

/-- `#{H ⊇ S : |H| = |S| + i} = C(n - |S|, i)` (`results/bounded-radius-spike.md`,
Proposition 2). -/
theorem card_superset_card_add (S : Finset (Fin n)) (i : ℕ) :
    #{H : Finset (Fin n) | S ⊆ H ∧ #H = #S + i} = (n - #S).choose i := by
  rw [show n - #S = #Sᶜ by rw [card_compl, Fintype.card_fin], ← card_powersetCard]
  refine card_nbij' (fun H ↦ H \ S) (fun T ↦ S ∪ T) ?_ ?_ ?_ ?_
  · intro H hH
    obtain ⟨hSH, hc⟩ := (mem_filter.mp (mem_coe.mp hH)).2
    refine mem_coe.mpr (mem_powersetCard.mpr ⟨fun x hx ↦ mem_compl.mpr (mem_sdiff.mp hx).2, ?_⟩)
    rw [card_sdiff_of_subset hSH]
    omega
  · intro T hT
    obtain ⟨hTS, hc⟩ := mem_powersetCard.mp (mem_coe.mp hT)
    have hd : Disjoint S T := disjoint_left.mpr fun x hxS hxT ↦ mem_compl.mp (hTS hxT) hxS
    refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, subset_union_left, ?_⟩)
    rw [card_union_of_disjoint hd, hc]
  · intro H hH
    exact union_sdiff_of_subset (mem_filter.mp (mem_coe.mp hH)).2.1
  · intro T hT
    have hTS := (mem_powersetCard.mp (mem_coe.mp hT)).1
    exact union_sdiff_cancel_left
      (disjoint_left.mpr fun x hxS hxT ↦ mem_compl.mp (hTS hxT) hxS)

/-- `#{H ⊇ S : |H| = x} (n)_k = C(n, x) (x)_k` with `k = |S|`, so a uniform `x`-subset contains
`S` with probability `(x)_k / (n)_k` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem card_superset_mul_descFactorial (S : Finset (Fin n)) (x : ℕ) :
    #{H : Finset (Fin n) | S ⊆ H ∧ #H = x} * n.descFactorial #S =
      n.choose x * x.descFactorial #S := by
  rcases lt_or_ge x #S with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, mul_zero, Nat.mul_eq_zero]
    left
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro H - ⟨hSH, rfl⟩
    exact absurd (card_le_card hSH) (by omega)
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    have hc := Nat.choose_mul (n := n) (k := #S + i) (s := #S) (by omega)
    rw [Nat.add_sub_cancel_left] at hc
    rw [card_superset_card_add, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    calc (n - #S).choose i * ((#S).factorial * n.choose #S)
        = (#S).factorial * (n.choose #S * (n - #S).choose i) := by ring
      _ = (#S).factorial * (n.choose (#S + i) * (#S + i).choose #S) := by rw [hc]
      _ = n.choose (#S + i) * ((#S).factorial * (#S + i).choose #S) := by ring

/-- `(n)_k > 0` for `k ≤ n` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem descFactorial_pos_of_le {k : ℕ} (h : k ≤ n) : 0 < n.descFactorial k :=
  Nat.pos_of_ne_zero fun h0 ↦ absurd (Nat.descFactorial_eq_zero_iff_lt.mp h0) (by omega)

/-- Summing over the supersets of `S`, grouped by size:
`∑_{H ⊇ S} f(|H|) / C(n, |H|) = ∑_{x ≤ n} f(x) (x)_k / (n)_k` with `k = |S|`
(`results/bounded-radius-spike.md`, Proposition 2). -/
theorem sum_superset (S : Finset (Fin n)) (f : ℕ → ℝ) :
    ∑ H : Finset (Fin n), (if S ⊆ H then f #H / n.choose #H else 0) =
      ∑ x ∈ range (n + 1), f x * x.descFactorial #S / n.descFactorial #S := by
  have hS : #S ≤ n := (card_le_univ S).trans_eq (Fintype.card_fin n)
  have hD : (0 : ℝ) < n.descFactorial #S := Nat.cast_pos.mpr (descFactorial_pos_of_le hS)
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1))
    (g := fun H : Finset (Fin n) ↦ #H)
    fun H _ ↦ mem_range.mpr (Nat.lt_succ_of_le ((card_le_univ H).trans_eq (Fintype.card_fin n)))]
  refine sum_congr rfl fun x hx ↦ ?_
  have hxn : x ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hx)
  have hC : (0 : ℝ) < n.choose x := Nat.cast_pos.mpr (Nat.choose_pos hxn)
  have hcount : (#{H : Finset (Fin n) | S ⊆ H ∧ #H = x} : ℝ) * n.descFactorial #S =
      n.choose x * x.descFactorial #S := by
    exact_mod_cast card_superset_mul_descFactorial S x
  rw [sum_congr rfl fun H hH ↦ by rw [(mem_filter.mp hH).2], ← sum_filter, sum_const,
    nsmul_eq_mul, filter_filter]
  have hset : #{H : Finset (Fin n) | #H = x ∧ S ⊆ H} = #{H : Finset (Fin n) | S ⊆ H ∧ #H = x} := by
    congr 1
    exact filter_congr fun H _ ↦ and_comm
  rw [hset]
  field_simp
  linear_combination f x * hcount

end Count

section Binomial

/-- The factorial moments of the binomial law (`results/bounded-radius-spike.md`,
Proposition 2): `E[(Bin(N, p))_k] = (N)_k p^k`. -/
theorem sum_binPmf_mul_descFactorial (N : ℕ) (p : ℝ) (k : ℕ) :
    ∑ x ∈ range (N + 1), binPmf N p x * x.descFactorial k = N.descFactorial k * p ^ k := by
  rcases lt_or_ge N k with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    refine sum_eq_zero fun x hx ↦ ?_
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by have := mem_range.mp hx; omega), Nat.cast_zero,
      mul_zero]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k + j + 1 = k + (j + 1) by ring, sum_range_add]
    rw [sum_eq_zero fun x hx ↦ by
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hx), Nat.cast_zero, mul_zero],
      zero_add]
    have hterm : ∀ y ∈ range (j + 1), binPmf (k + j) p (k + y) * ((k + y).descFactorial k : ℝ) =
        (k + j).descFactorial k * p ^ k * (p ^ y * (1 - p) ^ (j - y) * j.choose y) := by
      intro y hy
      have hc := Nat.choose_mul (n := k + j) (k := k + y) (s := k) (by omega)
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hc
      have hnat : (k + j).choose (k + y) * (k + y).descFactorial k =
          (k + j).descFactorial k * j.choose y := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
        calc (k + j).choose (k + y) * (k.factorial * (k + y).choose k)
            = k.factorial * ((k + j).choose (k + y) * (k + y).choose k) := by ring
          _ = k.factorial * ((k + j).choose k * j.choose y) := by rw [hc]
          _ = k.factorial * (k + j).choose k * j.choose y := by ring
      have hR : ((k + j).choose (k + y) : ℝ) * (k + y).descFactorial k =
          (k + j).descFactorial k * j.choose y := by exact_mod_cast hnat
      rw [binPmf, Nat.add_sub_add_left, pow_add]
      linear_combination (p ^ k * p ^ y * (1 - p) ^ (j - y)) * hR
    rw [sum_congr rfl hterm, ← mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]

/-- The binomial law vanishes above `N` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem binPmf_eq_zero {N x : ℕ} (p : ℝ) (h : N < x) : binPmf N p x = 0 := by
  rw [binPmf, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, zero_mul]

/-- The factorial moments of the mixture law of `X` (`results/bounded-radius-spike.md`,
Proposition 2): for `N ≤ n`, `∑_{x ≤ n} P(X = x) (x)_k = q (0)_k + (1 - q) (N)_k p^k`. -/
theorem sum_mixLaw_mul_descFactorial {N n : ℕ} (hN : N ≤ n) (q p : ℝ) (k : ℕ) :
    ∑ x ∈ range (n + 1), mixLaw q N p x * x.descFactorial k =
      q * (0 : ℕ).descFactorial k + (1 - q) * (N.descFactorial k * p ^ k) := by
  simp only [mixLaw, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_range,
    Nat.succ_pos, ite_true, mul_assoc, ← mul_sum]
  congr 2
  rw [← sum_binPmf_mul_descFactorial N p k, show n + 1 = (N + 1) + (n - N) by omega,
    sum_range_add, add_eq_left]
  exact sum_eq_zero fun y _ ↦ by rw [binPmf_eq_zero (x := N + 1 + y) p (by omega), zero_mul]

end Binomial

section Mixture

variable {n N : ℕ} {q p : ℝ}

/-- `∑_{H ⊇ S} U(H) g(|H|) = ∑_{x ≤ n} P(X = x) g(x) (x)_k / (n)_k` for the mixture weight
(`results/bounded-radius-spike.md`, Proposition 2). -/
theorem sum_superset_mixWeight (S : Finset (Fin n)) (g : ℕ → ℝ) :
    ∑ H : Finset (Fin n), (if S ⊆ H then mixWeight n q N p H * g #H else 0) =
      ∑ x ∈ range (n + 1), mixLaw q N p x * g x * x.descFactorial #S / n.descFactorial #S := by
  rw [← sum_superset S fun x ↦ mixLaw q N p x * g x]
  refine sum_congr rfl fun H _ ↦ ?_
  rw [mixWeight, div_mul_eq_mul_div]

/-- The exact formula of Proposition 2 (`results/bounded-radius-spike.md`):
`P(∩_{t ∈ S} A_t) = E[(X)_k] / (n)_k` with `k = |S|`. -/
theorem prob_superset_eq (S : Finset (Fin n)) :
    prob (mixWeight n q N p) {H | S ⊆ H} =
      (∑ H, mixWeight n q N p H * (#H).descFactorial #S) / n.descFactorial #S := by
  have h1 := sum_superset_mixWeight (n := n) (q := q) (N := N) (p := p) S fun _ ↦ 1
  have h2 := sum_superset_mixWeight (n := n) (q := q) (N := N) (p := p) ∅
    fun x ↦ (x.descFactorial #S : ℝ)
  simp only [empty_subset, ite_true, card_empty, Nat.descFactorial_zero, Nat.cast_one,
    div_one, mul_one] at h1 h2
  rw [prob, h2, sum_div]
  rw [← h1]
  refine sum_congr rfl fun H _ ↦ ?_
  simp [Set.indicator_apply]

/-- The mixture's mass at `0`, `P(X = 0) = q + (1 - q)(1 - p)^N`
(`results/bounded-radius-spike.md`, Proposition 2, corrected from `P(X = 0) = q`). -/
theorem lawOf_mixWeight_zero :
    lawOf (mixWeight n q N p) (fun H ↦ #H) 0 = q + (1 - q) * (1 - p) ^ N := by
  rw [lawOf, prob, sum_eq_single ∅]
  · simp [mixWeight, mixLaw, binPmf]
  · intro H _ hH
    rw [Set.indicator_of_notMem]
    simpa [card_eq_zero] using hH
  · simp

/-- The factorial moments of `X` under the mixture weight (`results/bounded-radius-spike.md`,
Proposition 2): `E[(X)_k] = q (0)_k + (1 - q) (N)_k p^k` for `N ≤ n`. -/
theorem sum_mixWeight_mul_descFactorial (hN : N ≤ n) (k : ℕ) :
    ∑ H, mixWeight n q N p H * (#H).descFactorial k =
      q * (0 : ℕ).descFactorial k + (1 - q) * (N.descFactorial k * p ^ k) := by
  have h := sum_superset_mixWeight (n := n) (q := q) (N := N) (p := p) ∅
    fun x ↦ (x.descFactorial k : ℝ)
  simp only [empty_subset, ite_true, card_empty, Nat.descFactorial_zero, Nat.cast_one,
    div_one, mul_one] at h
  rw [h, sum_mixLaw_mul_descFactorial hN]

/-- The mixture weight is a probability weight when `0 ≤ q ≤ 1`, `0 ≤ p ≤ 1` and `N ≤ n`
(`results/bounded-radius-spike.md`, Proposition 2). -/
theorem isProb_mixWeight (hN : N ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProb (mixWeight n q N p) where
  nonneg H := by
    unfold mixWeight mixLaw binPmf
    have : 0 ≤ 1 - q := by linarith
    have : 0 ≤ 1 - p := by linarith
    have : 0 ≤ (if #H = 0 then q else 0) := by split_ifs <;> linarith
    positivity
  sum_eq_one := by
    have h := sum_mixWeight_mul_descFactorial (q := q) (p := p) hN 0
    simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, pow_zero] at h
    rw [h]
    ring

/-- `P(∩_{t ∈ S} A_t) = (1 - q) (N)_k p^k / (n)_k` for `1 ≤ k = |S|` and `N ≤ n`
(`results/bounded-radius-spike.md`, Proposition 2). -/
theorem prob_superset_mixWeight (hN : N ≤ n) (S : Finset (Fin n)) (hS : 1 ≤ #S) :
    prob (mixWeight n q N p) {H | S ⊆ H} =
      (1 - q) * (N.descFactorial #S * p ^ #S) / n.descFactorial #S := by
  rw [prob_superset_eq, sum_mixWeight_mul_descFactorial hN]
  obtain ⟨j, hj⟩ : ∃ j, #S = j + 1 := ⟨#S - 1, by omega⟩
  rw [hj, Nat.zero_descFactorial_succ]
  simp

/-- `P(A_t) = (1 - q) N p / n` for `N ≤ n` (`results/bounded-radius-spike.md`,
Proposition 2). -/
theorem prob_mem_mixWeight (hN : N ≤ n) (t : Fin n) :
    prob (mixWeight n q N p) {H | t ∈ H} = (1 - q) * N * p / n := by
  have h := prob_superset_mixWeight (q := q) (p := p) hN {t} (by simp)
  simp only [card_singleton, Nat.descFactorial_one, pow_one, singleton_subset_iff] at h
  rw [h]
  ring

/-- `E X = ∑_t P(A_t) = (1 - q) N p` for `N ≤ n` (`results/bounded-radius-spike.md`,
Proposition 2). -/
theorem sum_prob_mem_mixWeight (hN : N ≤ n) (hn : 0 < n) :
    ∑ t, prob (mixWeight n q N p) {H | t ∈ H} = (1 - q) * N * p := by
  rw [sum_congr rfl fun t _ ↦ prob_mem_mixWeight hN t, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- `(N)_k = ∏_{i < k} (N - i)` in `ℝ` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem cast_descFactorial_eq_prod (N k : ℕ) :
    (N.descFactorial k : ℝ) = ∏ i ∈ range k, ((N : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih, Nat.descFactorial_succ]
    rcases le_or_gt k N with h | h
    · push_cast [Nat.cast_sub h]
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
      simp

/-- `(N)_k / N^k = ∏_{i < k} (1 - i / N)` for `N > 0` (`results/bounded-radius-spike.md`,
Proposition 2). -/
theorem descFactorial_div_pow_eq_prod {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (N.descFactorial k : ℝ) / (N : ℝ) ^ k = ∏ i ∈ range k, (1 - (i : ℝ) / N) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [cast_descFactorial_eq_prod,
    show (N : ℝ) ^ k = ∏ _i ∈ range k, (N : ℝ) by rw [prod_const, card_range], ← prod_div_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  field_simp

/-- The exact formula for the `k`-point ratio in Proposition 2 (`results/bounded-radius-spike.md`):
for `N ≤ n`, `q ≠ 1`, `p ≠ 0`, `N > 0` and `1 ≤ k = |S|`,
`R_S = (1 - q)^(1-k) ((N)_k / N^k) (n^k / (n)_k)`. -/
theorem jointRatio_mixWeight (hN : N ≤ n) (hN0 : 0 < N) (hq : q ≠ 1) (hp : p ≠ 0)
    (S : Finset (Fin n)) (hS : 1 ≤ #S) :
    jointRatio (mixWeight n q N p) S =
      ((1 - q) ^ (#S - 1))⁻¹ * ((N.descFactorial #S : ℝ) / (N : ℝ) ^ #S) *
        ((n : ℝ) ^ #S / n.descFactorial #S) := by
  have hSn : #S ≤ n := (card_le_univ S).trans_eq (Fintype.card_fin n)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hD : (n.descFactorial #S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (descFactorial_pos_of_le hSn).ne'
  rw [jointRatio, prob_superset_mixWeight hN S hS,
    prod_congr rfl fun t _ ↦ prob_mem_mixWeight hN t, prod_const]
  obtain ⟨j, hj⟩ : ∃ j, #S = j + 1 := ⟨#S - 1, by omega⟩
  rw [hj, Nat.add_sub_cancel, div_pow, mul_pow, mul_pow]
  rw [hj] at hD
  field_simp
  ring

end Mixture

section Bounds

/-- `N^k ≤ 2^k (N)_k` for `2k ≤ N` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem pow_le_two_pow_mul_descFactorial {N : ℕ} : ∀ {k : ℕ}, 2 * k ≤ N →
    N ^ k ≤ 2 ^ k * N.descFactorial k
  | 0, _ => by simp
  | k + 1, h => by
    have ih := pow_le_two_pow_mul_descFactorial (N := N) (k := k) (by omega)
    rw [pow_succ, Nat.descFactorial_succ, pow_succ]
    calc N ^ k * N ≤ 2 ^ k * N.descFactorial k * (2 * (N - k)) := Nat.mul_le_mul ih (by omega)
      _ = 2 ^ k * 2 * ((N - k) * N.descFactorial k) := by ring

/-- `(1/2)^k ≤ (N)_k / N^k ≤ 1` for `2k ≤ N` and `N > 0` (`results/bounded-radius-spike.md`,
Proposition 2). -/
theorem descFactorial_div_pow_mem {N k : ℕ} (hN : 0 < N) (h : 2 * k ≤ N) :
    (1 / 2 : ℝ) ^ k ≤ (N.descFactorial k : ℝ) / (N : ℝ) ^ k ∧
      (N.descFactorial k : ℝ) / (N : ℝ) ^ k ≤ 1 := by
  have hN' : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hN) k
  have h1 : (N : ℝ) ^ k ≤ 2 ^ k * N.descFactorial k := by
    exact_mod_cast pow_le_two_pow_mul_descFactorial h
  have h2 : (N.descFactorial k : ℝ) ≤ (N : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow N k
  refine ⟨?_, (div_le_one hN').mpr h2⟩
  rw [le_div_iff₀ hN', div_pow, one_pow, div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by positivity)]
  linarith [mul_comm ((2 : ℝ) ^ k) (N.descFactorial k : ℝ)]

/-- `1 ≤ n^k / (n)_k ≤ 2^k` for `2k ≤ n` (`results/bounded-radius-spike.md`, Proposition 2). -/
theorem pow_div_descFactorial_mem {n k : ℕ} (h : 2 * k ≤ n) :
    1 ≤ (n : ℝ) ^ k / n.descFactorial k ∧ (n : ℝ) ^ k / n.descFactorial k ≤ 2 ^ k := by
  have hD : (0 : ℝ) < n.descFactorial k :=
    Nat.cast_pos.mpr (descFactorial_pos_of_le (n := n) (by omega))
  have h1 : (n : ℝ) ^ k ≤ 2 ^ k * n.descFactorial k := by
    exact_mod_cast pow_le_two_pow_mul_descFactorial h
  have h2 : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  exact ⟨(one_le_div hD).mpr h2, (div_le_iff₀ hD).mpr h1⟩

end Bounds

/-- Proposition 2 of `results/bounded-radius-spike.md`, finite-parameter form. Let
`2 ≤ N ≤ n`, `0 ≤ q ≤ 1/2`, `0 < p ≤ 1` and `μ = (1 - q) N p`. Then the binomial mixture
`mixWeight n q N p` is a probability weight with `∑_t P(A_t) = μ`, its pair ratio is
`R_{s,t} = (1 - 1/N) (n / (n - 1)) / (1 - q)` for every pair, every `k`-point ratio with
`1 ≤ k`, `2k ≤ N` and `2k ≤ n` satisfies `2^(-k) ≤ R_S ≤ 2^(2k-1)`, and
`q ≤ P(X = 0) = q + (1 - q)(1 - p)^N ≤ q + e^(-μ)`. The spike's `P(X = 0) = q` is corrected
here to this two-sided bound. -/
theorem mixture_props {n N : ℕ} {q p μ : ℝ} (hN2 : 2 ≤ N) (hNn : N ≤ n) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (hp0 : 0 < p) (hp1 : p ≤ 1) (hμ : (1 - q) * N * p = μ) :
    IsProb (mixWeight n q N p) ∧
      ∑ t, prob (mixWeight n q N p) {H | t ∈ H} = μ ∧
      (∀ s t : Fin n, s ≠ t →
        jointRatio (mixWeight n q N p) {s, t} = (1 - 1 / N) * (n / (n - 1)) / (1 - q)) ∧
      (∀ S : Finset (Fin n), 1 ≤ #S → 2 * #S ≤ N → 2 * #S ≤ n →
        (1 / 2 : ℝ) ^ #S ≤ jointRatio (mixWeight n q N p) S ∧
          jointRatio (mixWeight n q N p) S ≤ 2 ^ (2 * #S - 1)) ∧
      lawOf (mixWeight n q N p) (fun H ↦ #H) 0 = q + (1 - q) * (1 - p) ^ N ∧
      q ≤ lawOf (mixWeight n q N p) (fun H ↦ #H) 0 ∧
      lawOf (mixWeight n q N p) (fun H ↦ #H) 0 ≤ q + Real.exp (-μ) := by
  have hN0 : 0 < N := by omega
  have hq1 : q ≠ 1 := fun h ↦ by linarith
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 ≤ 1 - p := by linarith
  refine ⟨isProb_mixWeight hNn hq0 (by linarith) hp0.le hp1, ?_, ?_, ?_, lawOf_mixWeight_zero,
    ?_, ?_⟩
  · rw [sum_prob_mem_mixWeight hNn (by omega), hμ]
  · intro s t hst
    have hS : #({s, t} : Finset (Fin n)) = 2 := card_pair hst
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hN2.trans hNn
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [jointRatio_mixWeight hNn hN0 hq1 hp0.ne' _ (by omega), hS, cast_descFactorial_eq_prod,
      cast_descFactorial_eq_prod]
    simp only [prod_range_succ, prod_range_zero, Nat.cast_zero, Nat.cast_one, sub_zero, one_mul,
      Nat.add_one_sub_one, pow_one]
    field_simp
  · intro S hS hSN hSn
    rw [jointRatio_mixWeight hNn hN0 hq1 hp0.ne' S hS]
    obtain ⟨hB1, hB2⟩ := descFactorial_div_pow_mem hN0 hSN
    obtain ⟨hC1, hC2⟩ := pow_div_descFactorial_mem hSn
    have hinv1 : 1 ≤ (1 - q)⁻¹ := (one_le_inv₀ h1q).mpr (by linarith)
    have hinv2 : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ h1q two_pos]
      linarith
    have hA1 : 1 ≤ ((1 - q) ^ (#S - 1))⁻¹ := by
      rw [← inv_pow]
      exact one_le_pow₀ hinv1
    have hA2 : ((1 - q) ^ (#S - 1))⁻¹ ≤ 2 ^ (#S - 1) := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (zero_le_one.trans hinv1) hinv2 _
    have hB0 : 0 ≤ (N.descFactorial #S : ℝ) / (N : ℝ) ^ #S := by positivity
    have hA0 : 0 ≤ ((1 - q) ^ (#S - 1))⁻¹ := zero_le_one.trans hA1
    constructor
    · calc (1 / 2 : ℝ) ^ #S = 1 * (1 / 2) ^ #S * 1 := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul hA1 hB1 (by positivity) hA0) hC1 zero_le_one
            (mul_nonneg hA0 hB0)
    · calc _ ≤ 2 ^ (#S - 1) * 1 * 2 ^ #S :=
            mul_le_mul (mul_le_mul hA2 hB2 hB0 (by positivity)) hC2
              (zero_le_one.trans hC1) (by positivity)
        _ = 2 ^ (2 * #S - 1) := by
          rw [mul_one, ← pow_add]
          congr 1
          omega
  · rw [lawOf_mixWeight_zero]
    have : 0 ≤ (1 - q) * (1 - p) ^ N := by positivity
    linarith
  · rw [lawOf_mixWeight_zero]
    have e1 : (1 - p) ^ N ≤ Real.exp (-p) ^ N :=
      pow_le_pow_left₀ h1p (by linarith [Real.add_one_le_exp (-p)]) N
    have e2 : Real.exp (-p) ^ N = Real.exp (-(N * p)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have e3 : Real.exp (-(N * p)) ≤ Real.exp (-μ) := by
      rw [Real.exp_le_exp, ← hμ]
      have : (0 : ℝ) ≤ N * p := by positivity
      nlinarith
    have e4 : (1 - q) * (1 - p) ^ N ≤ (1 - p) ^ N :=
      mul_le_of_le_one_left (pow_nonneg h1p N) (by linarith)
    linarith

/-- Proposition 2 of `results/bounded-radius-spike.md` (known inputs cannot pass Chebyshev).
Let `m ≥ 144` and `n = 2m - 1`. For every mean `0 < μ ≤ 2√m` and every target pair ratio
`r ∈ [1 - 1/m, 1]` there is a binomial mixture `mixWeight n q N p` (with `N = ⌈3√m⌉`) that is a
probability weight with `∑_t P(A_t) = μ`, has `R_{s,t} = r` for every pair, has
`2^(-k) ≤ R_S ≤ 2^(2k-1)` for every `k`-set with `1 ≤ k ≤ √m`, and has
`1/(12√m) ≤ q ≤ 1/(3√m)` and `q ≤ P(X = 0) ≤ q + e^(-μ)`.

The statement is abstract in `μ` and `r` on purpose. The true round-robin `R_2` (Lemma B,
`1 - 1/(4m) + O(m^(-3/2))`) is not in Lean, so the theorem covers every target in an interval
that contains it for large `m`, and every `μ` up to `2√m ≥ √π √m ≥ μ_m`. The spike's
`P(X = 0) = q` is corrected to `q ≤ P(X = 0) ≤ q + e^(-μ)`. -/
theorem mixture_barrier {m : ℕ} (hm : 144 ≤ m) {μ r : ℝ} (hμ0 : 0 < μ)
    (hμ : μ ≤ 2 * Real.sqrt m) (hr0 : 1 - 1 / m ≤ r) (hr1 : r ≤ 1) :
    ∃ (N : ℕ) (q p : ℝ),
      IsProb (mixWeight (2 * m - 1) q N p) ∧
      ∑ t, prob (mixWeight (2 * m - 1) q N p) {H | t ∈ H} = μ ∧
      (∀ s t : Fin (2 * m - 1), s ≠ t → jointRatio (mixWeight (2 * m - 1) q N p) {s, t} = r) ∧
      (∀ S : Finset (Fin (2 * m - 1)), 1 ≤ #S → (#S : ℝ) ≤ Real.sqrt m →
        (1 / 2 : ℝ) ^ #S ≤ jointRatio (mixWeight (2 * m - 1) q N p) S ∧
          jointRatio (mixWeight (2 * m - 1) q N p) S ≤ 2 ^ (2 * #S - 1)) ∧
      1 / (12 * Real.sqrt m) ≤ q ∧ q ≤ 1 / (3 * Real.sqrt m) ∧
      q ≤ lawOf (mixWeight (2 * m - 1) q N p) (fun H ↦ #H) 0 ∧
      lawOf (mixWeight (2 * m - 1) q N p) (fun H ↦ #H) 0 ≤ q + Real.exp (-μ) := by
  set s := Real.sqrt m with hs_def
  have hm' : (144 : ℝ) ≤ m := by exact_mod_cast hm
  have hs12 : 12 ≤ s := by
    rw [show (12 : ℝ) = Real.sqrt 144 by
      rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hm'
  have hss : s * s = m := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hsq : 12 * s ≤ s * s := mul_le_mul_of_nonneg_right hs12 (by linarith)
  set N := ⌈3 * s⌉₊ with hN_def
  have hN1 : 3 * s ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < 3 * s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  set n := 2 * m - 1 with hn_def
  have hn : (n : ℝ) = 2 * m - 1 := by
    rw [hn_def, Nat.cast_sub (by omega)]
    push_cast
    ring
  set v : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hv_def
  have hm2 : (0 : ℝ) < 2 * m - 2 := by linarith
  have hv1 : 1 ≤ v := by
    rw [hv_def, hn, le_div_iff₀ (by linarith)]
    linarith
  have hv2 : v ≤ 1 + 1 / (s * s) := by
    rw [hv_def, hn, hss, div_le_iff₀ (by linarith)]
    rw [show (1 + 1 / (m : ℝ)) * (2 * m - 1 - 1) = 2 * m - 2 / m by field_simp; ring]
    have : (2 : ℝ) / m ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hr : 0 < r := by
    have : (1 : ℝ) / m ≤ 1 / 144 := one_div_le_one_div_of_le (by norm_num) hm'
    linarith
  set q : ℝ := 1 - (1 - 1 / N) * v / r with hq_def
  have huN : 1 / (N : ℝ) ≤ 1 / (3 * s) := one_div_le_one_div_of_le (by linarith) hN1
  have hu4 : 1 / (4 * s) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos (by linarith)
  have hu0 : 0 ≤ 1 - 1 / (N : ℝ) := by
    rw [sub_nonneg, div_le_one hNpos]
    linarith
  have hqN : q ≤ 1 / N := by
    rw [hq_def, sub_le_comm, le_div_iff₀ hr]
    calc (1 - 1 / (N : ℝ)) * r ≤ (1 - 1 / N) * 1 := mul_le_mul_of_nonneg_left hr1 hu0
      _ ≤ (1 - 1 / N) * v := mul_le_mul_of_nonneg_left hv1 hu0
  set t : ℝ := 1 / s with ht_def
  have ht0 : 0 < t := by positivity
  have ht12 : t ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hs12
  have hpoly : (1 - t / 4) * (1 + t * t) ≤ (1 - t * t) * (1 - t / 12) := by
    have : 0 ≤ t * (1 / 6 - 2 * t) := mul_nonneg ht0.le (by linarith)
    nlinarith [pow_pos ht0 3]
  have hq12 : 1 / (12 * s) ≤ q := by
    have e1 : 1 / (4 * s) = t / 4 := by rw [ht_def]; field_simp
    have e2 : 1 / (s * s) = t * t := by rw [ht_def]; field_simp
    have e3 : 1 / (12 * s) = t / 12 := by rw [ht_def]; field_simp
    have hr' : 1 - t * t ≤ r := by rw [← e2, hss]; exact hr0
    have hkey : (1 - 1 / (N : ℝ)) * v ≤ r * (1 - t / 12) :=
      calc (1 - 1 / (N : ℝ)) * v ≤ (1 - t / 4) * (1 + t * t) :=
            mul_le_mul (by linarith) (by rw [← e2]; exact hv2) (by linarith) (by linarith)
        _ ≤ (1 - t * t) * (1 - t / 12) := hpoly
        _ ≤ r * (1 - t / 12) := mul_le_mul_of_nonneg_right hr' (by linarith)
    rw [e3, hq_def, le_sub_comm, div_le_iff₀ hr]
    linarith
  have hq0 : 0 ≤ q := le_trans (by positivity) hq12
  have hq3 : q ≤ 1 / (3 * s) := hqN.trans huN
  have hq2 : q ≤ 1 / 2 := by
    refine hq3.trans ?_
    rw [div_le_div_iff₀ (by linarith) two_pos]
    linarith
  have h1q : 0 < 1 - q := by linarith
  have hqNN : (N : ℝ) - 1 ≤ (1 - q) * N := by
    have : q * N ≤ 1 := by rwa [le_div_iff₀ hNpos] at hqN
    linarith
  set p : ℝ := μ / ((1 - q) * N) with hp_def
  have hden : 0 < (1 - q) * N := mul_pos h1q hNpos
  have hp0 : 0 < p := div_pos hμ0 hden
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one hden]
    linarith
  have hμeq : (1 - q) * N * p = μ := by
    rw [hp_def]
    field_simp
  have hN2' : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNn : N ≤ n := by
    have : (N : ℝ) ≤ n := by
      rw [hn, ← hss]
      linarith
    exact_mod_cast this
  obtain ⟨hP, hmean, hpair, hk, -, hlow, hup⟩ :=
    mixture_props (μ := μ) hN2' hNn hq0 hq2 hp0 hp1 hμeq
  refine ⟨N, q, p, hP, hmean, fun s' t' hst ↦ ?_, fun S hS hSs ↦ ?_, hq12, hq3, hlow, hup⟩
  · rw [hpair s' t' hst]
    have hne : (1 - 1 / (N : ℝ)) * v ≠ 0 := by
      have : 0 < 1 - 1 / (N : ℝ) := by
        rw [sub_pos, div_lt_one hNpos]
        linarith
      exact (mul_pos this (by linarith)).ne'
    rw [show (1 - q) = (1 - 1 / (N : ℝ)) * v / r by rw [hq_def]; ring, ← hv_def]
    have hN1' : (N : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  · have h2S : (2 * #S : ℝ) ≤ 2 * s := by linarith
    refine hk S hS ?_ ?_
    · have : (2 * #S : ℝ) ≤ N := by linarith
      exact_mod_cast this
    · have : (2 * #S : ℝ) ≤ n := by
        rw [hn, ← hss]
        linarith
      exact_mod_cast this

end MixtureBarrier

end Pairing
