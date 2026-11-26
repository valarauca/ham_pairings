import Mathlib.Data.ZMod.ValMinAbs
import Repair.ZeroState

/-!
# The zig-zag cycle of `F_0 ∪ F_{1/2}` and the segment lemma (P9, task T2)

Put `n = 2m - 1`. In `ℤ/n` the half is `1/2 = m`, since `2m = 1`. Lemma 1 of the direct
construction says that `F_0 ∪ F_{1/2}` is the single cycle

  `∞, 0, 1, -1, 2, -2, …, m - 1, -(m - 1), ∞`.

`zigPos m v` is the position of `v` on it: `∞` is at `0`, and a finite vertex whose least
absolute residue is `k` is at `2k` for `k > 0` and at `1 - 2k` for `k ≤ 0`. In positions `F_0`
pairs `2i ↔ 2i + 1`, and `F_{1/2}` pairs `2i + 1 ↔ 2i + 2` and `2m - 1 ↔ 0`.

* `zigPos_factor_zero`, `zigPos_factor_half` : the two factors in positions, read off the least
  absolute residue with `ZMod.valMinAbs_spec`.
* `zigPos_injective`, `zigPos_bounds` : positions are distinct and lie in `[0, 2m - 1]`.
* `zigCount L p = #{r | 2 L_r < p}` counts the levels `L_r` whose edge comes before position `p`.
  It is constant on every edge of `F_{1/2}` up to the wrap `0 ↔ 2m - 1`, and on every edge of
  `F_0` that is not at a level. On a strictly increasing `L` it is `r` at the entry end `2 L_r`
  of the `r`-th level and `r + 1` at its exit end `2 L_r + 1` (`zigCount_entry`,
  `zigCount_exit`).
* `not_ham_of_segments` (T2) : the zig-zag segment lemma. The segments between consecutive
  levels, with the wrap segment through `∞` and `0`, are the classes of `zigCount` mod `j`. A
  union of segments closed under `X` at the level edges is closed under `X` and `Y`, so it blocks
  `Ham X Y` by `not_ham_of_closed`.

Source: `results/cod-186-direct-construction-spike.md`, Lemma 1 and the non-Hamiltonian half of
Lemma 2(b), in the segment form of `results/lean-scope-p9-p10.md` §1, step 4.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The least absolute residue `k` of `y ∈ ℤ/(2m-1)` satisfies `-(2m-1) < 2k ≤ 2m-1`. -/
theorem valMinAbs_bounds (y : ZMod (2 * m - 1)) :
    -(2 * m - 1 : ℤ) < 2 * y.valMinAbs ∧ 2 * y.valMinAbs ≤ 2 * m - 1 := by
  have hm := NeZero.pos m
  have h := y.valMinAbs_mem_Ioc
  rw [Set.mem_Ioc, Nat.cast_sub (by omega : 1 ≤ 2 * m)] at h
  push_cast at h
  constructor <;> linarith [h.1, h.2]

/-- `y = k` with `-(2m-1) < 2k ≤ 2m-1` fixes the least absolute residue of `y`. -/
theorem valMinAbs_eq_of_eq {y : ZMod (2 * m - 1)} {k : ℤ} (hy : y = k)
    (h1 : -(2 * m - 1 : ℤ) < 2 * k) (h2 : 2 * k ≤ 2 * m - 1) : y.valMinAbs = k := by
  have hm := NeZero.pos m
  rw [ZMod.valMinAbs_spec, Set.mem_Ioc, Nat.cast_sub (by omega : 1 ≤ 2 * m)]
  push_cast
  exact ⟨hy, by linarith, by linarith⟩

/-- The position of a vertex on the zig-zag cycle `∞, 0, 1, -1, 2, -2, …` of `F_0 ∪ F_{1/2}`.
`∞` is at `0`, and a finite vertex with least absolute residue `k` is at `2k` for `k > 0` and at
`1 - 2k` for `k ≤ 0`. -/
def zigPos (m : ℕ) [NeZero m] : Vertex m → ℤ
  | none => 0
  | some y => if 0 < y.valMinAbs then 2 * y.valMinAbs else 1 - 2 * y.valMinAbs

/-- `∞` is at position `0`. -/
@[simp]
theorem zigPos_none : zigPos m none = 0 :=
  rfl

/-- The position of a finite vertex. -/
theorem zigPos_some (y : ZMod (2 * m - 1)) :
    zigPos m (some y) = if 0 < y.valMinAbs then 2 * y.valMinAbs else 1 - 2 * y.valMinAbs :=
  rfl

/-- The position of `y = k`, for `-(2m-1) < 2k ≤ 2m-1`. -/
theorem zigPos_some_of_eq {y : ZMod (2 * m - 1)} {k : ℤ} (hy : y = k)
    (h1 : -(2 * m - 1 : ℤ) < 2 * k) (h2 : 2 * k ≤ 2 * m - 1) :
    zigPos m (some y) = if 0 < k then 2 * k else 1 - 2 * k := by
  rw [zigPos_some, valMinAbs_eq_of_eq hy h1 h2]

/-- Positions lie in `[0, 2m - 1]`. -/
theorem zigPos_bounds (v : Vertex m) : 0 ≤ zigPos m v ∧ zigPos m v ≤ 2 * m - 1 := by
  have hm := NeZero.pos m
  rcases v with _ | y
  · simp only [zigPos_none]
    omega
  · have := valMinAbs_bounds y
    rw [zigPos_some]
    split_ifs <;> omega

/-- Distinct vertices have distinct positions. -/
theorem zigPos_injective : Function.Injective (zigPos m) := by
  rintro (_ | y) (_ | y') h
  · rfl
  · rw [zigPos_none, zigPos_some] at h
    split_ifs at h <;> omega
  · rw [zigPos_none, zigPos_some] at h
    split_ifs at h <;> omega
  · rw [zigPos_some, zigPos_some] at h
    have hk : y.valMinAbs = y'.valMinAbs := by
      split_ifs at h <;> omega
    rw [← y.coe_valMinAbs, hk, y'.coe_valMinAbs]

/-- `F_0` in positions: it pairs `2i ↔ 2i + 1`. -/
theorem zigPos_factor_zero (v : Vertex m) :
    zigPos m ((factor m 0).mate v) =
      if zigPos m v % 2 = 0 then zigPos m v + 1 else zigPos m v - 1 := by
  rcases v with _ | y
  · simp [factor, zigPos_some]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [factor, zigPos_some]
  have hb := valMinAbs_bounds y
  have hk : y.valMinAbs ≠ 0 := by rwa [Ne, ZMod.valMinAbs_eq_zero]
  have hneg : (2 * 0 - y).valMinAbs = -y.valMinAbs :=
    valMinAbs_eq_of_eq (by rw [Int.cast_neg, ZMod.coe_valMinAbs]; ring) (by omega) (by omega)
  simp only [factor, factor_mate, mateFn_of_ne _ _ hy, zigPos_some, hneg]
  split_ifs <;> omega

/-- `1/2 = m` has least absolute residue `1 - m`. -/
theorem valMinAbs_half : (m : ZMod (2 * m - 1)).valMinAbs = 1 - m := by
  have hm := NeZero.pos m
  refine valMinAbs_eq_of_eq ?_ (by omega) (by omega)
  push_cast
  linear_combination (two_mul_natCast_self (m := m))

/-- `F_{1/2}` in positions: it pairs `2i + 1 ↔ 2i + 2` and `2m - 1 ↔ 0`. With
`zigPos_factor_zero` this is Lemma 1 of `cod-186-direct-construction-spike.md` for `s = 0`,
`t = 1/2`. -/
theorem zigPos_factor_half (hm : 2 ≤ m) (v : Vertex m) :
    zigPos m ((factor m m).mate v) =
      if zigPos m v = 0 then (2 * m - 1 : ℤ) else if zigPos m v = 2 * m - 1 then 0
      else if zigPos m v % 2 = 1 then zigPos m v + 1 else zigPos m v - 1 := by
  have hh := valMinAbs_half (m := m)
  rcases v with _ | y
  · simp only [factor, factor_mate, mateFn_none, zigPos_some, hh, zigPos_none]
    split_ifs <;> omega
  rcases eq_or_ne y m with rfl | hy
  · simp only [factor, factor_mate, mateFn_self, zigPos_some, hh, zigPos_none]
    split_ifs <;> omega
  have hb := valMinAbs_bounds y
  have hk : y.valMinAbs ≠ 1 - m := fun h ↦ hy (by rw [← y.coe_valMinAbs, h, ← hh,
    ZMod.coe_valMinAbs])
  have hsub : (2 * (m : ZMod (2 * m - 1)) - y).valMinAbs = 1 - y.valMinAbs := by
    refine valMinAbs_eq_of_eq ?_ (by omega) (by omega)
    rw [two_mul_natCast_self, Int.cast_sub, Int.cast_one, ZMod.coe_valMinAbs]
  simp only [factor, factor_mate, mateFn_of_ne _ _ hy, zigPos_some, hsub]
  split_ifs <;> omega

/-- `#{r | 2 L_r < p}`, the number of levels `L_r` whose edge comes before position `p`. -/
def zigCount {j : ℕ} (L : Fin j → ℤ) (p : ℤ) : ℕ :=
  (Finset.univ.filter fun r ↦ 2 * L r < p).card

/-- `zigCount` is constant on `2k + 1 ↔ 2k + 2`. -/
theorem zigCount_odd_succ {j : ℕ} (L : Fin j → ℤ) (k : ℤ) :
    zigCount L (2 * k + 2) = zigCount L (2 * k + 1) := by
  unfold zigCount
  congr 1
  exact Finset.filter_congr fun r _ ↦ by omega

/-- `zigCount` is constant on `2k ↔ 2k + 1` when `k` is not a level. -/
theorem zigCount_even_succ {j : ℕ} (L : Fin j → ℤ) {k : ℤ} (hk : ∀ r, L r ≠ k) :
    zigCount L (2 * k + 1) = zigCount L (2 * k) := by
  unfold zigCount
  congr 1
  exact Finset.filter_congr fun r _ ↦ by have := hk r; omega

/-- `zigCount L p = 0` before every level. -/
theorem zigCount_of_le {j : ℕ} (L : Fin j → ℤ) {p : ℤ} (h : ∀ r, p ≤ 2 * L r) :
    zigCount L p = 0 := by
  unfold zigCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun r _ ↦ by have := h r; omega

/-- `zigCount L p = j` after every level. -/
theorem zigCount_of_lt {j : ℕ} (L : Fin j → ℤ) {p : ℤ} (h : ∀ r, 2 * L r < p) :
    zigCount L p = j := by
  unfold zigCount
  rw [Finset.filter_true_of_mem fun r _ ↦ h r, Finset.card_univ, Fintype.card_fin]

/-- For strictly increasing levels, `zigCount` is `r` at the entry end `2 L_r` of level `r`. -/
theorem zigCount_entry {j : ℕ} {L : Fin j → ℤ} (hL : StrictMono L) (r : Fin j) :
    zigCount L (2 * L r) = r := by
  unfold zigCount
  rw [← Fin.card_Iio r]
  congr 1
  ext r'
  rw [Finset.mem_filter, Finset.mem_Iio, ← hL.lt_iff_lt]
  simp only [Finset.mem_univ, true_and]
  omega

/-- For strictly increasing levels, `zigCount` is `r + 1` at the exit end `2 L_r + 1` of
level `r`. -/
theorem zigCount_exit {j : ℕ} {L : Fin j → ℤ} (hL : StrictMono L) (r : Fin j) :
    zigCount L (2 * L r + 1) = r + 1 := by
  unfold zigCount
  rw [← Fin.card_Iic r]
  congr 1
  ext r'
  rw [Finset.mem_filter, Finset.mem_Iic, ← hL.le_iff_le]
  simp only [Finset.mem_univ, true_and]
  omega

/-- T2, the zig-zag segment lemma. Let `pos` place the vertices on a cycle of length `2M` on
which `Y` pairs `2i + 1 ↔ 2i + 2` and `2M - 1 ↔ 0`, and let `X` pair `2i ↔ 2i + 1` away from the
level edges `{2 L_r, 2 L_r + 1}`, with `0 ≤ L_r` and `2 L_r < 2M - 1`. A set `S` of segment
classes `zigCount mod j` that `X` preserves at the level edges, and that holds at `u` but not at
`w`, makes `X ∪ Y` disconnected. The classes `0` and `j` are identified, which joins the two
halves of the wrap segment through position `0`. This is the non-Hamiltonian half of Lemma 2(b)
of `cod-186-direct-construction-spike.md`, in the segment form of `lean-scope-p9-p10.md` §1,
step 4. -/
theorem not_ham_of_segments {V : Type*} (X Y : PerfectMatching V) (pos : V → ℤ) {j : ℕ}
    (L : Fin j → ℤ) (M : ℤ) (hL0 : ∀ r, 0 ≤ L r) (hLM : ∀ r, 2 * L r < 2 * M - 1)
    (hY : ∀ v, pos (Y.mate v) = if pos v = 0 then 2 * M - 1 else if pos v = 2 * M - 1 then 0
      else if pos v % 2 = 1 then pos v + 1 else pos v - 1)
    (hX : ∀ v, (∀ r, 2 * L r ≠ pos v ∧ 2 * L r + 1 ≠ pos v) →
      pos (X.mate v) = if pos v % 2 = 0 then pos v + 1 else pos v - 1)
    (S : ℕ → Prop)
    (hXS : ∀ v, (∃ r, 2 * L r = pos v ∨ 2 * L r + 1 = pos v) →
      S (zigCount L (pos v) % j) → S (zigCount L (pos (X.mate v)) % j))
    {u w : V} (hu : S (zigCount L (pos u) % j)) (hw : ¬S (zigCount L (pos w) % j)) :
    ¬Ham X Y := by
  refine not_ham_of_closed X Y {v | S (zigCount L (pos v) % j)} (fun v hv ↦ ?_)
    (fun v hv ↦ ?_) hu hw
  · by_cases hlev : ∃ r, 2 * L r = pos v ∨ 2 * L r + 1 = pos v
    · exact hXS v hlev hv
    simp only [not_exists, not_or] at hlev
    have hx := hX v hlev
    change S _
    rw [hx]
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (pos v)
    · rw [ite_eq_left (by omega), hk, zigCount_even_succ L fun r h ↦ (hlev r).1 (by omega)]
      rwa [Set.mem_ofPred_eq, hk] at hv
    · rw [ite_eq_right (by omega), hk, add_sub_cancel_right,
        ← zigCount_even_succ L fun r h ↦ (hlev r).2 (by omega)]
      rwa [Set.mem_ofPred_eq, hk] at hv
  · change S _
    rw [Set.mem_ofPred_eq] at hv
    rw [hY v]
    split_ifs with h0 h1 h2
    · rw [h0, zigCount_of_le L fun r ↦ by linarith [hL0 r]] at hv
      rwa [zigCount_of_lt L hLM, Nat.mod_self]
    · rw [h1, zigCount_of_lt L hLM, Nat.mod_self] at hv
      rwa [zigCount_of_le L fun r ↦ by linarith [hL0 r]]
    · obtain ⟨k, hk⟩ : ∃ k, pos v = 2 * k + 1 := ⟨pos v / 2, by omega⟩
      rwa [hk, add_assoc, show (1 : ℤ) + 1 = 2 by norm_num, zigCount_odd_succ, ← hk]
    · obtain ⟨k, hk⟩ : ∃ k, pos v = 2 * k + 2 := ⟨pos v / 2 - 1, by omega⟩
      rwa [hk, show 2 * k + 2 - 1 = 2 * k + 1 by ring, ← zigCount_odd_succ, ← hk]

end RoundRobin.Canonical

end Pairing
