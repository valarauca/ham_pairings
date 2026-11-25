import Repair.ZeroState

/-!
# The sum-cover core (COD-165)

For odd `q = 2m - 1 ≥ 257` this builds a core `A_m` of `V_m` with at most `4 ⌈√q⌉ - 3` edges
that closes a cycle with every canonical factor. It follows section 2 of "Analyze Hamiltonian
Graphs" and the general arguments of the COD-156 audit.

* `L q = ⌈√q⌉`, written `Nat.sqrt (q - 1) + 1`, `J q = ⌊(q - 1) / L⌋`, `offset q = c ∈ {1, 2}`
  with `c ≠ q mod L`, `step q = h = L + c` and `rem q = (q - h) mod L`.
* `centers q` : the small centers `0, …, L - 1` outside `dropped q = {L - c, L - rem q}`, and the
  coarse centers `L, 2L, …, JL`. `no_conflict` : no two centers differ by `h` or by `q - h`.
* `baseCore m` : the center edges `e_b = s(b - δ, b + δ)` with `2δ = h`. They are pairwise
  disjoint (`isPartialMatching_baseCore`), and if `b + c ≡ 2t` then `e_b` and `e_c` close a
  `2`- or `4`-cycle with `F_t` (`blocks_baseCore`).
* `mem_openFactors_or` : writing `2t ≡ a + jL` with `0 ≤ a < L` and `0 ≤ j ≤ J`, either `a` was
  dropped and `t ∈ openFactors m`, or `2t` is the sum of two kept centers.
* `exists_sumCover_core` : the greedy step adds a shared edge for each open factor. The result
  is a partial matching with at most `L + 3J ≤ 4L - 3 < m` edges that blocks every `F_t`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

namespace SumCover

/-- `L = ⌈√q⌉` for `q ≥ 1`, written `Nat.sqrt (q - 1) + 1`. -/
def L (q : ℕ) : ℕ :=
  Nat.sqrt (q - 1) + 1

/-- `J = ⌊(q - 1) / L⌋`, the largest coarse index. -/
def J (q : ℕ) : ℕ :=
  (q - 1) / L q

/-- `c ∈ {1, 2}` with `c ≠ q mod L`. -/
def offset (q : ℕ) : ℕ :=
  if q % L q = 1 then 2 else 1

/-- The step `h = L + c`. Each center edge joins two labels that differ by `h`. -/
def step (q : ℕ) : ℕ :=
  L q + offset q

/-- `(q - h) mod L`. -/
def rem (q : ℕ) : ℕ :=
  (q - step q) % L q

/-- The two small centers that can conflict with a coarse center, `L - c` and
`L - (q - h) mod L`. -/
def dropped (q : ℕ) : Finset ℕ :=
  {L q - offset q, L q - rem q}

/-- The kept small centers, `{0, …, L - 1}` without `dropped q`. -/
def small (q : ℕ) : Finset ℕ :=
  (Finset.range (L q)).filter (· ∉ dropped q)

/-- The coarse centers `L, 2L, …, JL`. -/
def coarse (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (J q)).image (· * L q)

/-- The kept centers, small and coarse. -/
def centers (q : ℕ) : Finset ℕ :=
  small q ∪ coarse q

section Arith

variable {q : ℕ}

/-- `L > 0`. -/
theorem L_pos : 0 < L q :=
  Nat.succ_pos _

/-- `(L - 1)² < q ≤ L²`, so `L = ⌈√q⌉`. -/
theorem L_spec (hq : 1 ≤ q) : (L q - 1) * (L q - 1) < q ∧ q ≤ L q * L q := by
  have h1 := Nat.sqrt_le' (q - 1)
  have h2 := Nat.lt_succ_sqrt' (q - 1)
  rw [sq] at h1 h2
  simp only [L, Nat.add_sub_cancel, Nat.succ_eq_add_one] at h1 h2 ⊢
  omega

/-- `L ≥ 17` for `q ≥ 257`. -/
theorem seventeen_le_L (hq : 257 ≤ q) : 17 ≤ L q := by
  have : 16 ≤ Nat.sqrt (q - 1) := Nat.le_sqrt'.mpr (by norm_num; omega)
  unfold L
  omega

/-- `2L + 2 ≤ q` and `16L ≤ q + 15` for `q ≥ 257`, from `(L - 1)² < q` and `L ≥ 17`. -/
theorem L_bounds (hq : 257 ≤ q) : 2 * L q + 2 ≤ q ∧ 16 * L q ≤ q + 15 := by
  have h1 := (L_spec (by omega : 1 ≤ q)).1
  have h17 := seventeen_le_L hq
  have : 16 * (L q - 1) ≤ (L q - 1) * (L q - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- `J ≤ L - 1`, since `q ≤ L²`. -/
theorem J_le (hq : 1 ≤ q) : J q ≤ L q - 1 := by
  have h := (L_spec hq).2
  have : (q - 1) / L q < L q := (Nat.div_lt_iff_lt_mul L_pos).mpr (by omega)
  unfold J
  omega

/-- `JL ≤ q - 1`. -/
theorem J_mul_le : J q * L q ≤ q - 1 :=
  Nat.div_mul_le_self _ _

/-- `c ≥ 1`. -/
theorem offset_pos : 1 ≤ offset q := by
  unfold offset
  split_ifs <;> omega

/-- `c ≤ 2`. -/
theorem offset_le : offset q ≤ 2 := by
  unfold offset
  split_ifs <;> omega

/-- `c ≠ q mod L`. -/
theorem offset_ne : offset q ≠ q % L q := by
  unfold offset
  split_ifs <;> omega

/-- `h < q`. -/
theorem step_lt (hq : 257 ≤ q) : step q < q := by
  have := L_bounds hq
  have := offset_le (q := q)
  unfold step
  omega

/-- `(q - h) mod L ≠ 0`, since `c ≠ q mod L`. -/
theorem rem_ne_zero (hq : 257 ≤ q) : rem q ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
  have hs := step_lt hq
  have h17 := seventeen_le_L hq
  have hc := offset_le (q := q)
  have hq' : q = L q * (k + 1) + offset q := by
    rw [mul_add, mul_one, ← hk]
    unfold step at hs ⊢
    omega
  have hmod : q % L q = offset q :=
    calc q % L q = (L q * (k + 1) + offset q) % L q := by rw [← hq']
      _ = offset q := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact offset_ne hmod.symm

/-- Membership in `dropped q`. -/
theorem mem_dropped {a : ℕ} : a ∈ dropped q ↔ a = L q - offset q ∨ a = L q - rem q := by
  simp [dropped]

/-- The dropped centers lie in `[1, L)`. -/
theorem dropped_spec (hq : 257 ≤ q) {a : ℕ} (ha : a ∈ dropped q) : 1 ≤ a ∧ a < L q := by
  rw [mem_dropped] at ha
  have := Nat.mod_lt (q - step q) (L_pos (q := q))
  have := rem_ne_zero hq
  have := offset_pos (q := q)
  have := offset_le (q := q)
  have := seventeen_le_L hq
  unfold rem at *
  omega

/-- At most two centers are dropped. -/
theorem card_dropped_le : (dropped q).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

/-- Membership in `small q`. -/
theorem mem_small {b : ℕ} : b ∈ small q ↔ b < L q ∧ b ∉ dropped q := by
  simp [small]

/-- Membership in `coarse q`. -/
theorem mem_coarse {b : ℕ} : b ∈ coarse q ↔ ∃ j, (1 ≤ j ∧ j ≤ J q) ∧ j * L q = b := by
  simp [coarse]

/-- Every center is below `q`. -/
theorem centers_lt (hq : 257 ≤ q) {b : ℕ} (hb : b ∈ centers q) : b < q := by
  have := L_bounds hq
  rcases Finset.mem_union.mp hb with hb | hb
  · have := (mem_small.mp hb).1
    omega
  · obtain ⟨j, ⟨-, hj⟩, rfl⟩ := mem_coarse.mp hb
    have := Nat.mul_le_mul_right (L q) hj
    have := J_mul_le (q := q)
    omega

/-- No two centers differ by `h` or by `q - h`, written `b ≠ c + h` and `b + q ≠ c + h`.
Small centers are less than `L`, and both `h` and `q - h` exceed `L - 1`. Coarse differences
are multiples of `L`, and neither `h` nor `q - h` is. A mixed conflict forces the small center
to be `L - c` or `L - (q - h) mod L`, both dropped. -/
theorem no_conflict (hq : 257 ≤ q) {b c : ℕ} (hb : b ∈ centers q) (hc : c ∈ centers q) :
    b ≠ c + step q ∧ b + q ≠ c + step q := by
  have hL := seventeen_le_L hq
  have h2L := (L_bounds hq).1
  have ho1 := offset_pos (q := q)
  have ho2 := offset_le (q := q)
  have hs := step_lt hq
  unfold step at hs ⊢
  rcases Finset.mem_union.mp hb with hb | hb <;> rcases Finset.mem_union.mp hc with hc | hc
  · have := (mem_small.mp hb).1
    have := (mem_small.mp hc).1
    omega
  · obtain ⟨hbL, hbD⟩ := mem_small.mp hb
    obtain ⟨j, -, rfl⟩ := mem_coarse.mp hc
    refine ⟨by omega, fun h ↦ hbD ?_⟩
    have key : b + (q - (L q + offset q)) = j * L q := by omega
    have hmod : (b + rem q) % L q = 0 := by
      unfold rem step
      rw [Nat.add_mod_mod, key, Nat.mul_mod_left]
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hrem := Nat.mod_lt (q - step q) (L_pos (q := q))
    have hrem0 := rem_ne_zero hq
    unfold rem at hk hrem0
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k <;> omega
      · have := Nat.mul_le_mul_left (L q) hk2
        omega
    subst hk1
    rw [mem_dropped]
    right
    unfold rem
    omega
  · obtain ⟨j, -, rfl⟩ := mem_coarse.mp hb
    obtain ⟨hcL, hcD⟩ := mem_small.mp hc
    refine ⟨fun h ↦ ?_, by omega⟩
    rcases Nat.lt_or_ge j 3 with hj | hj
    · interval_cases j
      · omega
      · omega
      · exact hcD (mem_dropped.mpr (Or.inl (by omega)))
    · have := Nat.mul_le_mul_right (L q) hj
      omega
  · obtain ⟨i, -, rfl⟩ := mem_coarse.mp hb
    obtain ⟨j, -, rfl⟩ := mem_coarse.mp hc
    constructor
    · intro h
      rcases Nat.lt_or_ge i (j + 2) with hij | hij
      · have := Nat.mul_le_mul_right (L q) (by omega : i ≤ j + 1)
        rw [add_mul, one_mul] at this
        omega
      · have := Nat.mul_le_mul_right (L q) hij
        rw [add_mul] at this
        omega
    · intro h
      have e1 : (i * L q + q) % L q = q % L q := by
        rw [Nat.mul_comm i, Nat.mul_add_mod]
      have e2 : (j * L q + (L q + offset q)) % L q = offset q := by
        rw [show j * L q + (L q + offset q) = L q * (j + 1) + offset q by ring, Nat.mul_add_mod,
          Nat.mod_eq_of_lt (by omega)]
      rw [h, e2] at e1
      exact offset_ne e1

end Arith

/-- Distinct-residue test: if `b, c, k < n` with `b ≠ c + k` and `b + n ≠ c + k`, then
`b - c ≠ k` in `ℤ/n`. -/
theorem natCast_sub_ne {n b c k : ℕ} (hb : b < n) (hc : c < n) (hk : k < n)
    (h1 : b ≠ c + k) (h2 : b + n ≠ c + k) : (b : ZMod n) - c ≠ k := by
  intro h
  have h' : ((b : ℕ) : ZMod n) = ((c + k : ℕ) : ZMod n) := by
    push_cast
    rw [← h]
    ring
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb] at h'
  rcases Nat.lt_or_ge (c + k) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'
    exact h1 h'
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h'
    exact h2 (by omega)

/-- The half-step `δ = h / 2 = h m` in `ℤ/(2m-1)`. -/
def delta (m : ℕ) : ZMod (2 * m - 1) :=
  (step (2 * m - 1) : ZMod (2 * m - 1)) * m

/-- The center edge `e_b = s(b - δ, b + δ)`. -/
def centerEdge (m b : ℕ) : Sym2 (Vertex m) :=
  s(some ((b : ZMod (2 * m - 1)) - delta m), some ((b : ZMod (2 * m - 1)) + delta m))

/-- `A₀`, the center edges of the kept centers. -/
def baseCore (m : ℕ) : Finset (Sym2 (Vertex m)) :=
  (centers (2 * m - 1)).image (centerEdge m)

/-- The factors `A₀` may leave open, `t = (a + jL) / 2` for `a ∈ dropped` and `0 ≤ j ≤ J`.
Halving is multiplication by `m`. -/
def openFactors (m : ℕ) : Finset (ZMod (2 * m - 1)) :=
  (dropped (2 * m - 1) ×ˢ Finset.range (J (2 * m - 1) + 1)).image fun p ↦
    ((p.1 + p.2 * L (2 * m - 1) : ℕ) : ZMod (2 * m - 1)) * m

variable {m : ℕ} [NeZero m]

/-- `2δ = h`. -/
theorem two_mul_delta : 2 * delta m = step (2 * m - 1) := by
  rw [delta, mul_left_comm, two_mul_natCast_self, mul_one]

/-- No two kept centers differ by `2δ` in `ℤ/(2m-1)`. -/
theorem center_sub_ne (hq : 257 ≤ 2 * m - 1) {b c : ℕ} (hb : b ∈ centers (2 * m - 1))
    (hc : c ∈ centers (2 * m - 1)) : (b : ZMod (2 * m - 1)) - c ≠ 2 * delta m := by
  rw [two_mul_delta]
  obtain ⟨h1, h2⟩ := no_conflict hq hb hc
  exact natCast_sub_ne (centers_lt hq hb) (centers_lt hq hc) (step_lt hq) h1 h2

/-- The center edges of the kept centers form a partial matching. -/
theorem isPartialMatching_baseCore (hq : 257 ≤ 2 * m - 1) : IsPartialMatching (baseCore m) := by
  refine ⟨fun e he ↦ ?_, fun e he f hf v hve hvf ↦ ?_⟩
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    rw [centerEdge, Sym2.mk_isDiag_iff, Option.some_inj]
    exact fun h ↦ center_sub_ne hq hb hb (by linear_combination h)
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hf
    have hbc := center_sub_ne hq hb hc
    have hcb := center_sub_ne hq hc hb
    simp only [centerEdge, Sym2.mem_iff] at hve hvf
    rcases hve with rfl | rfl <;> rcases hvf with h | h <;> rw [Option.some_inj] at h
    · have hbc' : (b : ZMod (2 * m - 1)) = c := by linear_combination h
      simp only [centerEdge, hbc']
    · exact absurd (by linear_combination h) hbc
    · exact absurd (by linear_combination -h) hcb
    · have hbc' : (b : ZMod (2 * m - 1)) = c := by linear_combination h
      simp only [centerEdge, hbc']

/-- If `b + c ≡ 2t` for kept centers `b` and `c`, the edges `e_b` and `e_c` close a cycle with
`F_t`: the `4`-cycle `b - δ, b + δ, c - δ, c + δ`, or the shared edge `e_b` when `b = c`. -/
theorem blocks_baseCore (hq : 257 ≤ 2 * m - 1) {b c : ℕ} (hb : b ∈ centers (2 * m - 1))
    (hc : c ∈ centers (2 * m - 1)) (t : ZMod (2 * m - 1))
    (ht : (b : ZMod (2 * m - 1)) + c = 2 * t) : Blocks (baseCore m) (factor m t) := by
  have hbc := center_sub_ne hq hb hc
  have hcb := center_sub_ne hq hc hb
  have hbm : centerEdge m b ∈ baseCore m := Finset.mem_image_of_mem _ hb
  have hcm : centerEdge m c ∈ baseCore m := Finset.mem_image_of_mem _ hc
  refine blocks_factor _ t {(b : ZMod (2 * m - 1)) - delta m, (b : ZMod (2 * m - 1)) + delta m,
    (c : ZMod (2 * m - 1)) - delta m, (c : ZMod (2 * m - 1)) + delta m}
    ⟨_, Finset.mem_insert_self _ _⟩ (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨(b : ZMod (2 * m - 1)) + delta m, by simp, hbm⟩
    · exact ⟨(b : ZMod (2 * m - 1)) - delta m, by simp, by rw [Sym2.eq_swap]; exact hbm⟩
    · exact ⟨(c : ZMod (2 * m - 1)) + delta m, by simp, hcm⟩
    · exact ⟨(c : ZMod (2 * m - 1)) - delta m, by simp, by rw [Sym2.eq_swap]; exact hcm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [show 2 * t - ((b : ZMod (2 * m - 1)) - delta m) = c + delta m by
        linear_combination -ht]
      exact ⟨by simp, fun h ↦ hbc (by linear_combination -h)⟩
    · rw [show 2 * t - ((b : ZMod (2 * m - 1)) + delta m) = c - delta m by
        linear_combination -ht]
      exact ⟨by simp, fun h ↦ hcb (by linear_combination h)⟩
    · rw [show 2 * t - ((c : ZMod (2 * m - 1)) - delta m) = b + delta m by
        linear_combination -ht]
      exact ⟨by simp, fun h ↦ hcb (by linear_combination -h)⟩
    · rw [show 2 * t - ((c : ZMod (2 * m - 1)) + delta m) = b - delta m by
        linear_combination -ht]
      exact ⟨by simp, fun h ↦ hbc (by linear_combination h)⟩

/-- Every factor is open or covered. Write `2t ≡ r = a + jL` with `a = r mod L` and
`j = ⌊r / L⌋ ≤ J`. If `a` was dropped then `t ∈ openFactors m`. Otherwise `a` and `jL` (or `0`
when `j = 0`) are kept centers with sum `2t`. -/
theorem mem_openFactors_or (hq : 257 ≤ 2 * m - 1) (t : ZMod (2 * m - 1)) :
    t ∈ openFactors m ∨ ∃ b ∈ centers (2 * m - 1), ∃ c ∈ centers (2 * m - 1),
      (b : ZMod (2 * m - 1)) + c = 2 * t := by
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  generalize (2 * t).val = r at hr hrq
  have hLpos : 0 < L (2 * m - 1) := L_pos
  have hdiv : r % L (2 * m - 1) + r / L (2 * m - 1) * L (2 * m - 1) = r :=
    Nat.mod_add_div' r _
  have hjJ : r / L (2 * m - 1) ≤ J (2 * m - 1) := Nat.div_le_div_right (by omega)
  by_cases ha : r % L (2 * m - 1) ∈ dropped (2 * m - 1)
  · left
    refine Finset.mem_image.mpr ⟨(r % L (2 * m - 1), r / L (2 * m - 1)),
      Finset.mem_product.mpr ⟨ha, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    simp only
    rw [hdiv, hr, mul_comm 2 t, mul_assoc, two_mul_natCast_self, mul_one]
  · right
    have hsmall : r % L (2 * m - 1) ∈ centers (2 * m - 1) :=
      Finset.mem_union_left _ (mem_small.mpr ⟨Nat.mod_lt _ hLpos, ha⟩)
    rcases Nat.eq_zero_or_pos (r / L (2 * m - 1)) with hj | hj
    · refine ⟨_, hsmall, 0, Finset.mem_union_left _ (mem_small.mpr ⟨hLpos, fun h0 ↦ ?_⟩), ?_⟩
      · have := (dropped_spec hq h0).1
        omega
      · rw [hj, zero_mul, add_zero] at hdiv
        rw [Nat.cast_zero, add_zero, hdiv, hr]
    · refine ⟨_, hsmall, r / L (2 * m - 1) * L (2 * m - 1),
        Finset.mem_union_right _ (mem_coarse.mpr ⟨_, ⟨hj, hjJ⟩, rfl⟩), ?_⟩
      rw [← Nat.cast_add, hdiv, hr]

omit [NeZero m] in
/-- `|A₀| + |open factors| ≤ (L - |D|) + J + |D| (J + 1) ≤ L + 3J ≤ 4L - 3`. -/
theorem card_baseCore_add_le (hq : 257 ≤ 2 * m - 1) :
    (baseCore m).card + (openFactors m).card ≤ 4 * L (2 * m - 1) - 3 := by
  have h1 : (baseCore m).card ≤ (small (2 * m - 1)).card + (coarse (2 * m - 1)).card :=
    Finset.card_image_le.trans (Finset.card_union_le _ _)
  have h2 : (small (2 * m - 1)).card + (dropped (2 * m - 1)).card ≤ L (2 * m - 1) := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_left.mpr fun a ha hd ↦ (mem_small.mp ha).2 hd)]
    calc _ ≤ (Finset.range (L (2 * m - 1))).card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
            fun a ha ↦ Finset.mem_range.mpr (dropped_spec hq ha).2)
      _ = L (2 * m - 1) := Finset.card_range _
  have h3 : (coarse (2 * m - 1)).card ≤ J (2 * m - 1) :=
    Finset.card_image_le.trans (by simp)
  have h4 : (openFactors m).card ≤ (dropped (2 * m - 1)).card * (J (2 * m - 1) + 1) :=
    Finset.card_image_le.trans (by rw [Finset.card_product, Finset.card_range])
  have h5 := card_dropped_le (q := 2 * m - 1)
  have h6 := J_le (q := 2 * m - 1) (by omega)
  have h7 := seventeen_le_L hq
  generalize (dropped (2 * m - 1)).card = d at h2 h4 h5
  interval_cases d <;> omega

/-- The sum-cover core. For `q = 2m - 1 ≥ 257` some partial matching `A` of `V_m` has
`|A| ≤ 4 ⌈√q⌉ - 3 < m` and closes a cycle with every canonical factor `F_t`. -/
theorem exists_sumCover_core (hq : 257 ≤ 2 * m - 1) :
    ∃ A : Finset (Sym2 (Vertex m)), IsPartialMatching A ∧ A.card ≤ 4 * L (2 * m - 1) - 3 ∧
      A.card < m ∧ ∀ t, Blocks A (factor m t) := by
  have hV : Even (Fintype.card (Vertex m)) := by
    rw [card_vertex]
    exact even_two_mul m
  have hcard := card_baseCore_add_le hq
  have h16 := (L_bounds hq).2
  have h17 := seventeen_le_L hq
  obtain ⟨A, hA₀A, hA, hAcard, hB⟩ := exists_greedy hV (factor m)
    (isPartialMatching_baseCore hq) (openFactors m) (by rw [card_vertex]; omega)
  refine ⟨A, hA, by omega, by omega, fun t ↦ ?_⟩
  rcases mem_openFactors_or hq t with ht | ⟨b, hb, c, hc, hbc⟩
  · exact hB t ht
  · exact (blocks_baseCore hq hb hc t hbc).mono hA₀A

end SumCover

end RoundRobin.Canonical

end Pairing
