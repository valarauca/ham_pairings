import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Repair.PartialCore
import Repair.SumCover

/-!
# An explicit near-core and the density bound `q_m ≥ (2m)^-(4√m + 3)` (COD-181)

This file formalizes Lemma 5, Theorem 6 and Corollary 7 of the COD-168 write-up. Put
`N = m - 2`, `a = ⌈√N⌉ = SumCover.L N` and `J = ⌊N / a⌋`.

* `NearCore.base N = C = {0, …, a - 1} ∪ {a, 2a, …, Ja}` and
  `NearCore.indices N = K = C ∪ (N - C)`. `NearCore.exists_add_eq` : `K + K ⊇ [0, 2N]`.
  `NearCore.card_indices_le`, `NearCore.L_add_J_le` : `|K| ≤ 2(a + J) ≤ 4 ⌊√m⌋ + 2`.
* `nearCore m = A_m`, the edges `s(2k + 1, 2k + 2)` for `k ∈ K` (Lemma 5).
  `isPartialMatching_nearCore`, `card_nearCore_le`, and `blocks_nearCore` : `A_m` blocks every
  `F_t` outside `openFactors m = {t | 2t ≡ ±1} = {m - 1, m}`.
* `doubleFactorial_le_zeroCount_mul_pow_of_le` (Theorem 6) : for `m ≥ 26`,
  `(2m - 1)!! ≤ Z_m (2m)^(4 ⌊√m⌋ + 3)`, from Theorem 4 with `T = openFactors m`.
* `doubleFactorial_le_pow_of_le` : `(2m - 1)!! ≤ (2m)^(4 ⌊√m⌋ + 3)` for `6 ≤ m ≤ 25`.
* `doubleFactorial_le_zeroCount_mul_pow` (Corollary 7, natural form) : for every `m ≥ 6`,
  `(2m - 1)!! ≤ Z_m (2m)^(4 ⌊√m⌋ + 3)`. `doubleFactorial_le_zeroCount_mul_pow_floor` replaces
  the exponent by `⌊4√m + 3⌋`.
* `density_ge_rpow` (Corollary 7) : `q_m = Z_m / (2m - 1)!! ≥ (2m)^-(4√m + 3)` for `m ≥ 6`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

namespace NearCore

/-- `J = ⌊N / a⌋` with `a = SumCover.L N = ⌈√N⌉`. -/
def J (N : ℕ) : ℕ :=
  N / SumCover.L N

/-- `C = {0, …, a - 1} ∪ {a, 2a, …, Ja}`. -/
def base (N : ℕ) : Finset ℕ :=
  Finset.range (SumCover.L N) ∪ (Finset.Icc 1 (J N)).image (· * SumCover.L N)

/-- `K = C ∪ (N - C)`. -/
def indices (N : ℕ) : Finset ℕ :=
  base N ∪ (base N).image (N - ·)

/-- The labels `2k + 1` and `2k + 2` for `k ∈ K`. -/
def labels (N : ℕ) : Finset ℕ :=
  (indices N).image (2 * · + 1) ∪ (indices N).image (2 * · + 2)

/-- The partner of a positive label, `2k + 1 ↔ 2k + 2`. -/
def mate (x : ℕ) : ℕ :=
  if x % 2 = 1 then x + 1 else x - 1

/-- `2k + 1 ↦ 2k + 2`. -/
theorem mate_odd (k : ℕ) : mate (2 * k + 1) = 2 * k + 2 := by
  unfold mate
  split_ifs <;> omega

/-- `2k + 2 ↦ 2k + 1`. -/
theorem mate_even (k : ℕ) : mate (2 * k + 2) = 2 * k + 1 := by
  unfold mate
  split_ifs <;> omega

variable {N : ℕ}

/-- Every member of `C` is at most `N`. -/
theorem le_of_mem_base (hN : 1 ≤ N) {c : ℕ} (hc : c ∈ base N) : c ≤ N := by
  rcases Finset.mem_union.mp hc with hc | hc
  · have h1 := Finset.mem_range.mp hc
    have h2 := Nat.sqrt_le_self (N - 1)
    unfold SumCover.L at h1
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact (Nat.mul_le_mul_right _ (Finset.mem_Icc.mp hj).2).trans (Nat.div_mul_le_self _ _)

/-- Every `x ≤ N` is a sum of two members of `C`. -/
theorem exists_add_eq_base {x : ℕ} (hx : x ≤ N) : ∃ c ∈ base N, ∃ c' ∈ base N, c + c' = x := by
  have hL := SumCover.L_pos (q := N)
  have hmod := Nat.mod_add_div' x (SumCover.L N)
  have hc : x % SumCover.L N ∈ base N :=
    Finset.mem_union_left _ (Finset.mem_range.mpr (Nat.mod_lt _ hL))
  rcases Nat.eq_zero_or_pos (x / SumCover.L N) with h0 | hpos
  · refine ⟨_, hc, 0, Finset.mem_union_left _ (Finset.mem_range.mpr hL), ?_⟩
    rw [h0, zero_mul] at hmod
    omega
  · refine ⟨_, hc, x / SumCover.L N * SumCover.L N, Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right hx⟩)), hmod⟩

/-- Every member of `K` is at most `N`. -/
theorem le_of_mem_indices (hN : 1 ≤ N) {k : ℕ} (hk : k ∈ indices N) : k ≤ N := by
  rcases Finset.mem_union.mp hk with hk | hk
  · exact le_of_mem_base hN hk
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hk
    exact Nat.sub_le N c

/-- Lemma 5.2 (COD-168): `K + K ⊇ [0, 2N]`. -/
theorem exists_add_eq (hN : 1 ≤ N) {x : ℕ} (hx : x ≤ 2 * N) :
    ∃ k ∈ indices N, ∃ k' ∈ indices N, k + k' = x := by
  rcases le_or_gt x N with hxN | hxN
  · obtain ⟨c, hc, c', hc', h⟩ := exists_add_eq_base hxN
    exact ⟨c, Finset.mem_union_left _ hc, c', Finset.mem_union_left _ hc', h⟩
  · obtain ⟨c, hc, c', hc', h⟩ := exists_add_eq_base (N := N) (x := 2 * N - x) (by omega)
    have h1 := le_of_mem_base hN hc
    have h2 := le_of_mem_base hN hc'
    exact ⟨N - c, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc), N - c',
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc'), by omega⟩

/-- `|C| ≤ a + J`. -/
theorem card_base_le : (base N).card ≤ SumCover.L N + J N := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_range _).le ?_)
  refine Finset.card_image_le.trans ?_
  rw [Nat.card_Icc]
  omega

/-- `|K| ≤ 2(a + J)`. -/
theorem card_indices_le : (indices N).card ≤ 2 * (SumCover.L N + J N) := by
  have h := card_base_le (N := N)
  have h' := Finset.card_image_le (s := base N) (f := (N - ·))
  have := Finset.card_union_le (base N) ((base N).image (N - ·))
  unfold indices
  omega

/-- `a + J ≤ 2 ⌊√(N + 2)⌋ + 1`, using `(a - 1)² < N ≤ a²` and `Ja ≤ N`. -/
theorem L_add_J_le (hN : 1 ≤ N) : SumCover.L N + J N ≤ 2 * Nat.sqrt (N + 2) + 1 := by
  obtain ⟨h1, h2⟩ := SumCover.L_spec hN
  have hL := SumCover.L_pos (q := N)
  have hJL : J N * SumCover.L N ≤ N := Nat.div_mul_le_self _ _
  have ha : SumCover.L N - 1 ≤ Nat.sqrt (N + 2) := Nat.le_sqrt.mpr (by omega)
  have hb : J N ≤ SumCover.L N := Nat.le_of_mul_le_mul_right (hJL.trans h2) hL
  rcases hb.lt_or_eq with hb | hb
  · omega
  · have hc : SumCover.L N ≤ Nat.sqrt (N + 2) := by
      rw [hb] at hJL
      exact Nat.le_sqrt.mpr (by omega)
    omega

/-- A label `x` of `A_m` is `2k + 1` or `2k + 2` for some `k ∈ K`. -/
theorem exists_of_mem_labels {x : ℕ} (hx : x ∈ labels N) :
    ∃ k ∈ indices N, x = 2 * k + 1 ∨ x = 2 * k + 2 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨k, hk, Or.inl rfl⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨k, hk, Or.inr rfl⟩

/-- `2k + 1` is a label for `k ∈ K`. -/
theorem odd_mem_labels {k : ℕ} (hk : k ∈ indices N) : 2 * k + 1 ∈ labels N :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)

/-- `2k + 2` is a label for `k ∈ K`. -/
theorem even_mem_labels {k : ℕ} (hk : k ∈ indices N) : 2 * k + 2 ∈ labels N :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (2 * · + 2) hk)

end NearCore

open NearCore

/-- Lemma 5 (COD-168), the near-core `A_m`. With `N = m - 2` it has the edges
`e_k = s(2k + 1, 2k + 2)` for `k ∈ K`. -/
def nearCore (m : ℕ) : Finset (Sym2 (Vertex m)) :=
  natMatching m NearCore.mate (labels (m - 2))

/-- The factors that `A_m` may leave open, those with `2t ≡ 1` or `2t ≡ -1`, that is `t = m`
and `t = m - 1`. -/
def openFactors (m : ℕ) [NeZero m] : Finset (ZMod (2 * m - 1)) :=
  Finset.univ.filter fun t ↦ (2 * t).val = 1 ∨ (2 * t).val = 2 * m - 2

variable {m : ℕ} [NeZero m]

/-- At most two factors are open. -/
theorem card_openFactors_le : (openFactors m).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn (fun t ↦ (2 * t).val)
    (t := ({1, 2 * m - 2} : Finset ℕ)) (fun t ht ↦ ?_) (fun t _ t' _ h ↦ ?_)).trans
    Finset.card_le_two
  · have h := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    simpa using h
  · exact (isUnit_two (modulus_odd m)).mul_left_cancel (ZMod.val_injective _ h)

omit [NeZero m] in
/-- The labels of `A_m` lie below `2m - 1`. -/
theorem lt_of_mem_labels (hm : 3 ≤ m) {x : ℕ} (hx : x ∈ labels (m - 2)) : x < 2 * m - 1 := by
  obtain ⟨k, hk, rfl | rfl⟩ := exists_of_mem_labels hx <;>
  · have := le_of_mem_indices (by omega) hk
    omega

omit [NeZero m] in
/-- The labels of `A_m` are closed under `2k + 1 ↔ 2k + 2`. -/
theorem mate_mem_labels {x : ℕ} (hx : x ∈ labels (m - 2)) : NearCore.mate x ∈ labels (m - 2) := by
  obtain ⟨k, hk, rfl | rfl⟩ := exists_of_mem_labels hx
  · rw [mate_odd]
    exact even_mem_labels hk
  · rw [mate_even]
    exact odd_mem_labels hk

omit [NeZero m] in
/-- Lemma 5.1 (COD-168): `A_m` is a partial matching of finite vertices. -/
theorem isPartialMatching_nearCore (hm : 3 ≤ m) : IsPartialMatching (nearCore m) := by
  refine isPartialMatching_natMatching (fun x hx ↦ lt_of_mem_labels hm hx)
    (fun x hx ↦ mate_mem_labels hx) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨k, -, rfl | rfl⟩ := exists_of_mem_labels hx
    · rw [mate_odd, mate_even]
    · rw [mate_even, mate_odd]
  · obtain ⟨k, -, rfl | rfl⟩ := exists_of_mem_labels hx
    · rw [mate_odd]
      omega
    · rw [mate_even]
      omega

omit [NeZero m] in
/-- `|A_m| ≤ |K|`. -/
theorem card_nearCore_le : (nearCore m).card ≤ (indices (m - 2)).card := by
  refine (Finset.card_le_card (t := (indices (m - 2)).image fun k : ℕ ↦
    s(some ((2 * k + 1 : ℕ) : ZMod (2 * m - 1)), some ((2 * k + 2 : ℕ) : ZMod (2 * m - 1))))
    fun e he ↦ ?_).trans Finset.card_image_le
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨k, hk, rfl | rfl⟩ := exists_of_mem_labels hx
  · rw [mate_odd]
    exact Finset.mem_image_of_mem _ hk
  · rw [mate_even, Sym2.eq_swap]
    exact Finset.mem_image_of_mem _ hk

/-- Lemma 5.3 (COD-168): `A_m` blocks every `F_t` with `t` outside `openFactors m`, by the
`2`-cycle `e_k` when `2t ≡ 2(2k) + 3` and by the `4`-cycle `e_k, e_{k'}` when
`2t ≡ 2(k + k') + 3`. -/
theorem blocks_nearCore (hm : 3 ≤ m) {t : ZMod (2 * m - 1)} (ht : t ∉ openFactors m) :
    Blocks (nearCore m) (factor m t) := by
  have hto : ¬((2 * t).val = 1 ∨ (2 * t).val = 2 * m - 2) := fun h ↦
    ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  generalize (2 * t).val = r at hr hrq hto
  obtain ⟨x, hx, hxr⟩ : ∃ x ≤ 2 * (m - 2), 2 * x + 3 = r ∨ 2 * x + 3 = r + (2 * m - 1) := by
    rcases Nat.even_or_odd' r with ⟨i, rfl | rfl⟩
    · exact ⟨i + m - 2, by omega, Or.inr (by omega)⟩
    · exact ⟨i - 1, by omega, Or.inl (by omega)⟩
  obtain ⟨k, hk, k', hk', rfl⟩ := exists_add_eq (by omega) hx
  refine blocks_natMatching (fun y hy ↦ lt_of_mem_labels hm hy) t hr
    {2 * k + 1, 2 * k + 2, 2 * k' + 1, 2 * k' + 2} (fun y hy ↦ ?_) ⟨2 * k + 1, by simp⟩
    (fun y hy ↦ ?_) (forall_exists_four (s := 2 * (k + k') + 3) (by omega) (by omega) (by omega)
      (by omega) hxr)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact odd_mem_labels hk
    · exact even_mem_labels hk
    · exact odd_mem_labels hk'
    · exact even_mem_labels hk'
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl
    · rw [mate_odd]
      simp
    · rw [mate_even]
      simp
    · rw [mate_odd]
      simp
    · rw [mate_even]
      simp

omit [NeZero m] in
/-- `|A_m| ≤ 4 ⌊√m⌋ + 2`. -/
theorem card_nearCore_le_sqrt (hm : 3 ≤ m) : (nearCore m).card ≤ 4 * Nat.sqrt m + 2 := by
  have h1 := card_nearCore_le (m := m)
  have h2 := card_indices_le (N := m - 2)
  have h3 := L_add_J_le (N := m - 2) (by omega)
  rw [show m - 2 + 2 = m by omega] at h3
  omega

omit [NeZero m] in
/-- `4 ⌊√m⌋ + 6 ≤ m` for `m ≥ 26`. -/
theorem four_mul_sqrt_add_six_le (hm : 26 ≤ m) : 4 * Nat.sqrt m + 6 ≤ m := by
  have h1 := Nat.sqrt_le m
  have h2 := Nat.lt_succ_sqrt m
  generalize Nat.sqrt m = g at h1 h2 ⊢
  rcases Nat.lt_or_ge g 6 with hg | hg
  · interval_cases g <;> omega
  · nlinarith

/-- Theorem 6 (COD-168) in natural numbers. For `m ≥ 26`,
`(2m - 1)!! ≤ Z_m (2m)^(4 ⌊√m⌋ + 3)`. With `s = |A_m| ≤ 4 ⌊√m⌋ + 2` and `r = m - s ≥ 4`,
Theorem 4 and the two open factors give `(2r - 1)!! ≤ 12 Z_m`, and `c_s(m) ≤ (2m)^s`. -/
theorem doubleFactorial_le_zeroCount_mul_pow_of_le (hm : 26 ≤ m) :
    Nat.doubleFactorial (2 * m - 1) ≤ zeroCount m * (2 * m) ^ (4 * Nat.sqrt m + 3) := by
  have hs := card_nearCore_le_sqrt (m := m) (by omega)
  have hsm := four_mul_sqrt_add_six_le hm
  obtain ⟨j, hj⟩ : ∃ j, m - (nearCore m).card = j + 1 := ⟨m - (nearCore m).card - 1, by omega⟩
  have h4 := doubleFactorial_le_zeroCount_add (isPartialMatching_nearCore (by omega))
    (by omega) (openFactors m) fun t ht ↦ blocks_nearCore (by omega) ht
  rw [hj, Nat.add_sub_cancel, show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at h4
  have hT := Nat.mul_le_mul_right (2 ^ j * j.factorial) (card_openFactors_le (m := m))
  have h24 := twentyfour_mul_le (j := j) (by omega)
  have hD : Nat.doubleFactorial (2 * j + 1) ≤ 12 * zeroCount m := by
    omega
  have hc := doubleFactorial_le_pow_mul (j + 1) (nearCore m).card
  rw [show j + 1 + (nearCore m).card = m by omega,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hc
  calc Nat.doubleFactorial (2 * m - 1)
      ≤ (2 * m) ^ (nearCore m).card * Nat.doubleFactorial (2 * j + 1) := hc
    _ ≤ (2 * m) ^ (nearCore m).card * (2 * m * zeroCount m) :=
        Nat.mul_le_mul_left _ (hD.trans (Nat.mul_le_mul_right _ (by omega)))
    _ = zeroCount m * (2 * m) ^ ((nearCore m).card + 1) := by ring
    _ ≤ zeroCount m * (2 * m) ^ (4 * Nat.sqrt m + 3) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

omit [NeZero m] in
/-- The small cases of Corollary 7: `(2m - 1)!! ≤ (2m)^(4 ⌊√m⌋ + 3)` for `6 ≤ m ≤ 25`. -/
theorem doubleFactorial_le_pow_of_le (h6 : 6 ≤ m) (h25 : m ≤ 25) :
    Nat.doubleFactorial (2 * m - 1) ≤ (2 * m) ^ (4 * Nat.sqrt m + 3) := by
  rcases Nat.lt_or_ge m 16 with h | h
  · have hg : 2 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
    refine le_trans ?_ (Nat.pow_le_pow_right (by omega) (by omega : 11 ≤ 4 * Nat.sqrt m + 3))
    interval_cases m <;> decide
  · have hg : 4 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
    refine le_trans ?_ (Nat.pow_le_pow_right (by omega) (by omega : 19 ≤ 4 * Nat.sqrt m + 3))
    interval_cases m <;> decide

/-- Corollary 7 (COD-168) in natural numbers. For every `m ≥ 6`,
`(2m - 1)!! ≤ Z_m (2m)^(4 ⌊√m⌋ + 3)`. For `m ≤ 25` this uses one zero state from
`nonempty_zeroState`, and for `m ≥ 26` the near-core `A_m`. -/
theorem doubleFactorial_le_zeroCount_mul_pow (hm : 6 ≤ m) :
    Nat.doubleFactorial (2 * m - 1) ≤ zeroCount m * (2 * m) ^ (4 * Nat.sqrt m + 3) := by
  rcases Nat.lt_or_ge m 26 with h | h
  · have hZ : 0 < zeroCount m := Fintype.card_pos_iff.mpr (nonempty_zeroState hm)
    exact (doubleFactorial_le_pow_of_le hm (by omega)).trans (Nat.le_mul_of_pos_left _ hZ)
  · exact doubleFactorial_le_zeroCount_mul_pow_of_le h

/-- `4 ⌊√m⌋ + 3 ≤ 4√m + 3`. -/
theorem cast_four_mul_sqrt_add_three_le (m : ℕ) :
    ((4 * Nat.sqrt m + 3 : ℕ) : ℝ) ≤ 4 * Real.sqrt m + 3 := by
  have := Real.nat_sqrt_le_real_sqrt (a := m)
  push_cast
  linarith

/-- Corollary 7 (COD-168) with the exponent `⌊4√m + 3⌋`. For every `m ≥ 6`,
`(2m - 1)!! ≤ Z_m (2m)^⌊4√m + 3⌋`. -/
theorem doubleFactorial_le_zeroCount_mul_pow_floor (hm : 6 ≤ m) :
    Nat.doubleFactorial (2 * m - 1) ≤ zeroCount m * (2 * m) ^ ⌊4 * Real.sqrt m + 3⌋₊ :=
  (doubleFactorial_le_zeroCount_mul_pow hm).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (Nat.le_floor (cast_four_mul_sqrt_add_three_le m))))

/-- Corollary 7 (COD-168). For every `m ≥ 6`,
`q_m = Z_m / (2m - 1)!! ≥ (2m)^-(4√m + 3)`. -/
theorem density_ge_rpow (hm : 6 ≤ m) :
    (2 * m : ℝ) ^ (-(4 * Real.sqrt m + 3)) ≤
      (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  have h := doubleFactorial_le_zeroCount_mul_pow hm
  have h2m : (1 : ℝ) ≤ 2 * m := by
    have : (6 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc (2 * m : ℝ) ^ (-(4 * Real.sqrt m + 3))
      ≤ (2 * m : ℝ) ^ (-((4 * Nat.sqrt m + 3 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h2m (neg_le_neg (cast_four_mul_sqrt_add_three_le m))
    _ = 1 / (2 * m : ℝ) ^ (4 * Nat.sqrt m + 3) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_natCast, one_div]
    _ ≤ (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)),
          one_mul]
        exact_mod_cast h

end RoundRobin.Canonical

end Pairing
