import Repair.NearCore
import Repair.SqrtObstructions.CertLength

/-!
# Two dual orbits for the round-robin factors (COD-262)

Put `n = 2m - 1`, `N = m - 2` and `e_k = {2k + 1, 2k + 2}` (`NearCore.mate`, ham_pairings main
978559a). Two matchings are paired against the factors `F_t`, and their translates `x ↦ x + b`
(`shift`, ham-spin 55c17eb) form the dual orbits of `RoundRobinSpan.lean`.

* `pStar m hm = P* = {∞ 0} ∪ {e_k : 0 ≤ k ≤ N}` (`results/f2-slice-extend.md`, organize-archive
  cd0ed47, Lemma 1). `ham_pStar_iff` : `P* ∪ F_t` is one cycle iff `t ∈ {m - 1, m}`, for every
  `m ≥ 2`. `ham_shift_pStar_iff` : the profile of `P* + b` is `e_{m-1+b} + e_{m+b}`.
* `oneQ m hm = Q = {0 3, ∞ 4, e_0} ∪ {e_k : 2 ≤ k ≤ N}`, the two-switch of `P*` on `{∞, 0}` and
  `{3, 4}` (Proposition Q of `results/f2-slice-factcheck-extend.md`, cd0ed47, §2).
  `ham_oneQ_iff` : `Q ∪ F_t` is one cycle iff `t = m + 2`, for every `m ≥ 5`, and
  `hamCount_oneQ` : `X(Q) = 1`. `ham_shift_oneQ_iff` : the profile of `Q + b` is `e_{m+2+b}`.

The proofs are those of `results/one-factor-q-review.md` (organize-archive, not committed yet).
* Blocking, `not_ham_of_labels` : a set of labels closed under the matching and paired by
  `x ↦ 2t - x` is a proper closed set. It gives the `2`- and `4`-cycles of
  `results/cod-168-density-lower-bound.md` (1769b9b) Lemma 5.3 (`not_ham_pStar`,
  `not_ham_oneQ`), and for `Q` also the `8`-cycle `0, n-1, n-2, 1, 2, n-3, n-4, 3` at `t = m - 1`
  and the `6`-cycle `0, 1, 2, n-1, n-2, 3` at `t = m`.
* Connectivity, `reachable_factor_of_add` : in `F_t` the labels `a` and `2t - a` lie in one
  component, even at the fixed point `a = t`. Chains of such steps through the `e_k` connect
  `P* ∪ F_{m-1}`, `P* ∪ F_m` and `Q ∪ F_{m+2}` (`ham_pStar_sub_one`, `ham_pStar_self`,
  `ham_oneQ_self`), with no case split on where the walk meets the fixed point.
-/

namespace Pairing.RoundRobin.Canonical

open PerfectMatching

namespace NearCore

/-- `2k + 1 ↔ 2k + 2` is an involution of the positive labels. -/
theorem mate_mate (v : ℕ) : mate (mate v) = v := by
  unfold mate
  split_ifs <;> omega

/-- `2k + 1 ↔ 2k + 2` sends positive labels to positive labels. -/
theorem mate_ne_zero {v : ℕ} (hv : v ≠ 0) : mate v ≠ 0 := by
  unfold mate
  split_ifs <;> omega

/-- `2k + 1 ↔ 2k + 2` has no fixed point among the positive labels. -/
theorem mate_ne_self {v : ℕ} (hv : v ≠ 0) : mate v ≠ v := by
  unfold mate
  split_ifs <;> omega

/-- `2k + 1 ↔ 2k + 2` keeps labels below the odd number `2m - 1`. -/
theorem mate_lt {m v : ℕ} (hm : 1 ≤ m) (hv : v < 2 * m - 1) : mate v < 2 * m - 1 := by
  unfold mate
  split_ifs <;> omega

end NearCore

variable {m : ℕ} [NeZero m]

section Tools

/-- A set `W` of labels that is closed under `P` and pairs up with sum `r` or `r + 2m - 1`, where
`r ≡ 2t`, is closed under `P` and `F_t` and misses `∞`, so `P ∪ F_t` is not one cycle
(`results/one-factor-q-review.md`, organize-archive not committed yet, steps 1 and 2). -/
theorem not_ham_of_labels {P : PerfectMatching (Vertex m)} (t : ZMod (2 * m - 1)) {r : ℕ}
    (hr : (r : ZMod (2 * m - 1)) = 2 * t) (W : Finset ℕ) (hWn : ∀ x ∈ W, x < 2 * m - 1)
    {w₀ : ℕ} (hw₀ : w₀ ∈ W)
    (hP : ∀ x ∈ W, ∃ y ∈ W, P.mate (some (x : ZMod (2 * m - 1))) = some (y : ZMod (2 * m - 1)))
    (hF : ∀ x ∈ W, ∃ y ∈ W, x ≠ y ∧ (x + y = r ∨ x + y = r + (2 * m - 1))) :
    ¬Ham P (factor m t) := by
  refine not_ham_of_closed P (factor m t)
    {v | ∃ x ∈ W, v = some (x : ZMod (2 * m - 1))} ?_ ?_ (u := some (w₀ : ZMod (2 * m - 1)))
    (w := none) ⟨w₀, hw₀, rfl⟩ (by simp)
  · rintro v ⟨x, hx, rfl⟩
    obtain ⟨y, hy, h⟩ := hP x hx
    exact ⟨y, hy, h⟩
  · rintro v ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy, hsum⟩ := hF x hx
    have hcast : ((x + y : ℕ) : ZMod (2 * m - 1)) = r := by
      rcases hsum with h | h
      · rw [h]
      · rw [h, Nat.cast_add, ZMod.natCast_self, add_zero]
    have h2 : 2 * t - (x : ZMod (2 * m - 1)) = y := by
      rw [← hr, ← hcast]
      push_cast
      ring
    have hxt : (x : ZMod (2 * m - 1)) ≠ t := by
      intro h
      have hyx : (y : ZMod (2 * m - 1)) = x := by
        rw [← h2, h]
        ring
      exact hxy (natCast_injOn (hWn x hx) (hWn y hy) hyx.symm)
    exact ⟨y, hy, by rw [factor_mate_some_of_ne hxt, h2]⟩

/-- In `F_t` the label `a` is joined to `b` (or equals it, at the fixed point `t`) whenever
`a + b ≡ 2t` (`results/one-factor-q-review.md`, organize-archive not committed yet, step 3). -/
theorem reachable_factor_of_add (t : ZMod (2 * m - 1)) {r a b : ℕ}
    (hr : (r : ZMod (2 * m - 1)) = 2 * t) (hab : a + b = r ∨ a + b = r + (2 * m - 1)) :
    (factor m t).toGraph.Reachable (some (a : ZMod (2 * m - 1))) (some (b : ZMod (2 * m - 1))) := by
  have hcast : ((a + b : ℕ) : ZMod (2 * m - 1)) = r := by
    rcases hab with h | h
    · rw [h]
    · rw [h, Nat.cast_add, ZMod.natCast_self, add_zero]
  have h2 : 2 * t - (a : ZMod (2 * m - 1)) = b := by
    rw [← hr, ← hcast]
    push_cast
    ring
  by_cases hat : (a : ZMod (2 * m - 1)) = t
  · have hba : (b : ZMod (2 * m - 1)) = a := by
      rw [← h2, hat]
      ring
    rw [hba]
  · exact SimpleGraph.Adj.reachable (by rw [toGraph_adj, factor_mate_some_of_ne hat, h2])

omit [NeZero m] in
/-- If `r ≡ 2t` with `r ∉ {1, 2m - 2}`, then `2x + 3 ≡ r` for some `x ≤ 2(m - 2)`, so `t` lies
outside the two open factors of the near-core (`results/cod-168-density-lower-bound.md`, 1769b9b,
Lemma 5.3). If moreover `m ≥ 5` and `r ≠ 5`, then `x ≠ 1`. -/
theorem exists_two_mul_add_three {r : ℕ} (hrq : r < 2 * m - 1) (hr1 : r ≠ 1)
    (hr2 : r ≠ 2 * m - 2) : ∃ x ≤ 2 * (m - 2), (5 ≤ m → r ≠ 5 → x ≠ 1) ∧
      (2 * x + 3 = r ∨ 2 * x + 3 = r + (2 * m - 1)) := by
  rcases Nat.even_or_odd' r with ⟨i, rfl | rfl⟩
  · exact ⟨i + m - 2, by omega, fun h5 _ ↦ by omega, Or.inr (by omega)⟩
  · exact ⟨i - 1, by omega, fun _ h5 ↦ by omega, Or.inl (by omega)⟩

/-- `2t = 2u` gives `t = u` in `ℤ/(2m - 1)`. -/
theorem eq_of_two_mul_eq {t u : ZMod (2 * m - 1)} (h : 2 * t = 2 * u) : t = u :=
  (isUnit_two (modulus_odd m)).mul_left_cancel h

/-- `2(m - 1) = 2m - 2` in `ℤ/(2m - 1)`, read as a label. -/
theorem natCast_two_mul_sub_two :
    ((2 * m - 2 : ℕ) : ZMod (2 * m - 1)) = 2 * ((m : ZMod (2 * m - 1)) - 1) := by
  have hm := NeZero.pos m
  rw [Nat.cast_sub (show 2 ≤ 2 * m by omega)]
  push_cast
  ring

/-- Translating `P` by `b` moves its profile by `b`: `P + b` closes one cycle with `F_t` iff `P`
does with `F_{t-b}` (`shift_smul_factor`, ham-spin 55c17eb). -/
theorem ham_shift_iff (P : PerfectMatching (Vertex m)) (b t : ZMod (2 * m - 1)) :
    Ham (shift m b • P) (factor m t) ↔ Ham P (factor m (t - b)) := by
  rw [show factor m t = shift m b • factor m (t - b) by rw [shift_smul_factor, sub_add_cancel],
    ham_smul]

end Tools

section PStar

/-- The partner map of `P*` on `V_m`: `∞ ↔ 0` and `2k + 1 ↔ 2k + 2` (`NearCore.mate`) on the
positive labels (`results/f2-slice-extend.md`, organize-archive cd0ed47, Lemma 1). -/
def pStarFn (m : ℕ) [NeZero m] : Vertex m → Vertex m
  | none => some ((0 : ℕ) : ZMod (2 * m - 1))
  | some x => if x.val = 0 then none else some ((NearCore.mate x.val : ℕ) : ZMod (2 * m - 1))

/-- The partner map of `P*` is an involution. -/
theorem pStarFn_involutive : Function.Involutive (pStarFn m) := by
  have h0 : ((0 : ℕ) : ZMod (2 * m - 1)).val = 0 := by simp
  rintro (_ | x)
  · simp only [pStarFn, h0, ↓reduceIte]
  by_cases hx : x.val = 0
  · simp only [pStarFn, hx, ↓reduceIte, Option.some.injEq]
    rw [← hx, ZMod.natCast_zmod_val]
  · have hv : ((NearCore.mate x.val : ℕ) : ZMod (2 * m - 1)).val = NearCore.mate x.val :=
      ZMod.val_natCast_of_lt (NearCore.mate_lt NeZero.one_le (ZMod.val_lt x))
    simp only [pStarFn, hx, ↓reduceIte, hv, NearCore.mate_ne_zero hx, NearCore.mate_mate,
      ZMod.natCast_zmod_val]

/-- The partner map of `P*` has no fixed point. -/
theorem pStarFn_ne (v : Vertex m) : pStarFn m v ≠ v := by
  rcases v with _ | x
  · simp [pStarFn]
  by_cases hx : x.val = 0
  · simp [pStarFn, hx]
  · simp only [pStarFn, hx, ↓reduceIte, ne_eq, Option.some.injEq]
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (NearCore.mate_lt NeZero.one_le (ZMod.val_lt x))] at h'
    exact NearCore.mate_ne_self hx h'

/-- The matching `P* = {∞ 0} ∪ {e_k : 0 ≤ k ≤ m - 2}` on `V_m`, `e_k = {2k + 1, 2k + 2}`
(`results/f2-slice-extend.md`, organize-archive cd0ed47, Lemma 1). It is the near-core of
`results/cod-168-density-lower-bound.md` (1769b9b) Lemma 5 with `K = [0, N]`, completed by
`∞ 0`. -/
def pStar (m : ℕ) [NeZero m] : PerfectMatching (Vertex m) where
  mate := Function.Involutive.toPerm _ pStarFn_involutive
  mate_mate := pStarFn_involutive
  mate_ne := pStarFn_ne

/-- The partner map of `P*`. -/
@[simp]
theorem pStar_mate (v : Vertex m) : (pStar m).mate v = pStarFn m v :=
  rfl

/-- `P*` pairs `0` with `∞`. -/
theorem pStar_mate_zero : (pStar m).mate (some ((0 : ℕ) : ZMod (2 * m - 1))) = none := by
  simp only [pStar_mate, pStarFn, ZMod.val_natCast_of_lt (modulus_odd m).pos, ↓reduceIte]

/-- `P*` pairs a positive label `x` with `NearCore.mate x`. -/
theorem pStar_mate_label {x : ℕ} (hx : x < 2 * m - 1) (hx0 : x ≠ 0) :
    (pStar m).mate (some (x : ZMod (2 * m - 1))) =
      some (NearCore.mate x : ZMod (2 * m - 1)) := by
  simp only [pStar_mate, pStarFn, ZMod.val_natCast_of_lt hx, hx0, ↓reduceIte]

/-- `P* ∪ F_t` is not one cycle for `t ∉ {m - 1, m}`, by the `2`- or `4`-cycle of `e_k, e_{k'}`
with `2(k + k') + 3 ≡ 2t` and `k, k' ∈ [0, m - 2]` (`results/cod-168-density-lower-bound.md`,
1769b9b, Lemma 5.3, with `K = [0, N]`; `results/f2-slice-extend.md`, cd0ed47, Lemma 1). -/
theorem not_ham_pStar {t : ZMod (2 * m - 1)} (ht1 : t ≠ (m : ZMod (2 * m - 1)) - 1)
    (ht2 : t ≠ m) : ¬Ham (pStar m) (factor m t) := by
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  have hr1 : (2 * t).val ≠ 1 := fun h ↦ ht2 (eq_of_two_mul_eq (by
    rw [← hr, h, two_mul_natCast_self, Nat.cast_one]))
  have hr2 : (2 * t).val ≠ 2 * m - 2 := fun h ↦ ht1 (eq_of_two_mul_eq (by
    rw [← hr, h, natCast_two_mul_sub_two]))
  generalize (2 * t).val = r at hr hrq hr1 hr2
  obtain ⟨x, hx, -, hxr⟩ := exists_two_mul_add_three hrq hr1 hr2
  set k := min x (m - 2) with hk
  refine not_ham_of_labels t hr {2 * k + 1, 2 * k + 2, 2 * (x - k) + 1, 2 * (x - k) + 2}
    (fun y hy ↦ ?_) (w₀ := 2 * k + 1) (by simp) (fun y hy ↦ ?_)
    (forall_exists_four (s := 2 * x + 3) (by omega) (by omega) (by omega) (by omega) hxr)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨2 * k + 2, by simp,
        by rw [pStar_mate_label (by omega) (by omega), NearCore.mate_odd]⟩
    · exact ⟨2 * k + 1, by simp,
        by rw [pStar_mate_label (by omega) (by omega), NearCore.mate_even]⟩
    · exact ⟨2 * (x - k) + 2, by simp,
        by rw [pStar_mate_label (by omega) (by omega), NearCore.mate_odd]⟩
    · exact ⟨2 * (x - k) + 1, by simp,
        by rw [pStar_mate_label (by omega) (by omega), NearCore.mate_even]⟩

/-- Every vertex of `V_m` is reachable from `0` in `P* ∪ F`, once every bottom label `2j + 1` with
`j ≤ m - 2` is. The tops follow by the edges `e_j` and `∞` by `∞ 0`. -/
theorem pStar_connected_of_bottoms {F : PerfectMatching (Vertex m)}
    (h : ∀ j ≤ m - 2, ((pStar m).toGraph ⊔ F.toGraph).Reachable
      (some ((0 : ℕ) : ZMod (2 * m - 1))) (some ((2 * j + 1 : ℕ) : ZMod (2 * m - 1)))) :
    Ham (pStar m) F := by
  set G := (pStar m).toGraph ⊔ F.toGraph
  have hP : ∀ {a : ℕ}, a < 2 * m - 1 → a ≠ 0 →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (NearCore.mate a : ZMod (2 * m - 1))) :=
    fun ha ha0 ↦ (SimpleGraph.Adj.reachable
      (by rw [toGraph_adj, pStar_mate_label ha ha0])).mono le_sup_left
  have hall : ∀ v, G.Reachable (some ((0 : ℕ) : ZMod (2 * m - 1))) v := by
    rintro (_ | x)
    · exact (SimpleGraph.Adj.reachable (by rw [toGraph_adj, pStar_mate_zero])).mono le_sup_left
    rw [← ZMod.natCast_zmod_val x]
    have hxl := ZMod.val_lt x
    generalize x.val = k at hxl
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · rfl
      · have := hP (a := 2 * (j - 1) + 1) (by omega) (by omega)
        rw [NearCore.mate_odd, show 2 * (j - 1) + 2 = 2 * j by omega] at this
        exact (h (j - 1) (by omega)).trans this
    · exact h j (by omega)
  exact ⟨fun u v ↦ (hall u).symm.trans (hall v)⟩

/-- `P* ∪ F_{m-1}` is one cycle. Here `2t ≡ 2m - 2`, and the bottom of `e_k` reaches the bottom
of `e_{k-1}` through `e_{N-k}` (`results/f2-slice-extend.md`, organize-archive cd0ed47,
Lemma 1). -/
theorem ham_pStar_sub_one (hm : 2 ≤ m) :
    Ham (pStar m) (factor m ((m : ZMod (2 * m - 1)) - 1)) := by
  set G := (pStar m).toGraph ⊔ (factor m ((m : ZMod (2 * m - 1)) - 1)).toGraph
  have hF : ∀ {a b : ℕ}, a + b = 2 * m - 2 →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (b : ZMod (2 * m - 1))) := fun hab ↦
    (reachable_factor_of_add _ natCast_two_mul_sub_two (Or.inl hab)).mono le_sup_right
  have hP : ∀ {a : ℕ}, a < 2 * m - 1 → a ≠ 0 →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (NearCore.mate a : ZMod (2 * m - 1))) :=
    fun ha ha0 ↦ (SimpleGraph.Adj.reachable
      (by rw [toGraph_adj, pStar_mate_label ha ha0])).mono le_sup_left
  have hdown : ∀ i ≤ m - 2, G.Reachable (some ((0 : ℕ) : ZMod (2 * m - 1)))
      (some ((2 * (m - 2 - i) + 1 : ℕ) : ZMod (2 * m - 1))) := by
    intro i
    induction i with
    | zero =>
      intro _
      have s1 := hF (a := 0) (b := 2 * (m - 2) + 2) (by omega)
      have s2 := hP (a := 2 * (m - 2) + 2) (by omega) (by omega)
      rw [NearCore.mate_even] at s2
      exact s1.trans s2
    | succ i ih =>
      intro hi
      have s1 := hF (a := 2 * (m - 2 - i) + 1) (b := 2 * i + 1) (by omega)
      have s2 := hP (a := 2 * i + 1) (by omega) (by omega)
      rw [NearCore.mate_odd] at s2
      have s3 := hF (a := 2 * i + 2) (b := 2 * (m - 2 - (i + 1)) + 2) (by omega)
      have s4 := hP (a := 2 * (m - 2 - (i + 1)) + 2) (by omega) (by omega)
      rw [NearCore.mate_even] at s4
      exact (ih (by omega)).trans (s1.trans (s2.trans (s3.trans s4)))
  refine pStar_connected_of_bottoms fun j hj ↦ ?_
  have := hdown (m - 2 - j) (by omega)
  rwa [show m - 2 - (m - 2 - j) = j by omega] at this

/-- `P* ∪ F_m` is one cycle. Here `2t ≡ 1`, and the bottom of `e_k` reaches the bottom of
`e_{k+1}` through `e_{N-k}` (`results/f2-slice-extend.md`, organize-archive cd0ed47, Lemma 1). -/
theorem ham_pStar_self (hm : 2 ≤ m) : Ham (pStar m) (factor m (m : ZMod (2 * m - 1))) := by
  set G := (pStar m).toGraph ⊔ (factor m (m : ZMod (2 * m - 1))).toGraph
  have h1 : ((1 : ℕ) : ZMod (2 * m - 1)) = 2 * (m : ZMod (2 * m - 1)) := by
    rw [two_mul_natCast_self, Nat.cast_one]
  have hF : ∀ {a b : ℕ}, (a + b = 1 ∨ a + b = 1 + (2 * m - 1)) →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (b : ZMod (2 * m - 1))) := fun hab ↦
    (reachable_factor_of_add _ h1 hab).mono le_sup_right
  have hP : ∀ {a : ℕ}, a < 2 * m - 1 → a ≠ 0 →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (NearCore.mate a : ZMod (2 * m - 1))) :=
    fun ha ha0 ↦ (SimpleGraph.Adj.reachable
      (by rw [toGraph_adj, pStar_mate_label ha ha0])).mono le_sup_left
  refine pStar_connected_of_bottoms fun j hj ↦ ?_
  induction j with
  | zero => exact hF (a := 0) (b := 1) (Or.inl rfl)
  | succ j ih =>
    have s1 := hP (a := 2 * j + 1) (by omega) (by omega)
    rw [NearCore.mate_odd] at s1
    have s2 := hF (a := 2 * j + 2) (b := 2 * (m - 2 - j) + 2) (Or.inr (by omega))
    have s3 := hP (a := 2 * (m - 2 - j) + 2) (by omega) (by omega)
    rw [NearCore.mate_even] at s3
    have s4 := hF (a := 2 * (m - 2 - j) + 1) (b := 2 * (j + 1) + 1) (Or.inr (by omega))
    exact (ih (by omega)).trans (s1.trans (s2.trans (s3.trans s4)))

/-- Lemma 1 of `results/f2-slice-extend.md` (organize-archive cd0ed47): `P* ∪ F_t` is one cycle
exactly for `t ∈ {m - 1, m}`, for every `m ≥ 2`. -/
theorem ham_pStar_iff (hm : 2 ≤ m) (t : ZMod (2 * m - 1)) :
    Ham (pStar m) (factor m t) ↔ t = (m : ZMod (2 * m - 1)) - 1 ∨ t = m := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra ht
    rw [not_or] at ht
    exact not_ham_pStar ht.1 ht.2 h
  · rintro (rfl | rfl)
    · exact ham_pStar_sub_one hm
    · exact ham_pStar_self hm

/-- The translate `P* + b` (`shift`, ham-spin 55c17eb) closes one cycle with `F_t` exactly for
`t ∈ {m - 1 + b, m + b}`, so its profile is `e_{m-1+b} + e_{m+b}` (`results/f2-slice-extend.md`,
organize-archive cd0ed47, §1.3). -/
theorem ham_shift_pStar_iff (hm : 2 ≤ m) (b t : ZMod (2 * m - 1)) :
    Ham (shift m b • pStar m) (factor m t) ↔
      t = (m : ZMod (2 * m - 1)) - 1 + b ∨ t = m + b := by
  rw [ham_shift_iff, ham_pStar_iff hm, sub_eq_iff_eq_add, sub_eq_iff_eq_add]

end PStar

section OneQ

/-- The partner of a finite label in `Q` (`results/f2-slice-factcheck-extend.md`, organize-archive
cd0ed47, §2): `0 ↔ 3`, and `2k + 1 ↔ 2k + 2` (`NearCore.mate`) otherwise. Label `4` is paired
with `∞` by `oneQFn`. -/
def oneQLabel (v : ℕ) : ℕ :=
  if v = 0 then 3 else if v = 3 then 0 else NearCore.mate v

/-- `oneQLabel` is an involution off the label `4`. -/
theorem oneQLabel_oneQLabel {v : ℕ} (hv : v ≠ 4) : oneQLabel (oneQLabel v) = v := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> first | contradiction | omega

/-- `oneQLabel` never returns `4`. -/
theorem oneQLabel_ne_four (v : ℕ) : oneQLabel v ≠ 4 := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> omega

/-- `oneQLabel` has no fixed point. -/
theorem oneQLabel_ne_self (v : ℕ) : oneQLabel v ≠ v := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> omega

omit [NeZero m] in
/-- `oneQLabel` keeps labels below `2m - 1` for `m ≥ 3`. -/
theorem oneQLabel_lt {v : ℕ} (hm : 3 ≤ m) (hv : v < 2 * m - 1) : oneQLabel v < 2 * m - 1 := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> omega

/-- `2k + 1 ↦ 2k + 2` in `Q` for `k ≠ 1`. -/
theorem oneQLabel_odd {k : ℕ} (hk : k ≠ 1) : oneQLabel (2 * k + 1) = 2 * k + 2 := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> first | contradiction | omega

/-- `2k + 2 ↦ 2k + 1` in `Q`. -/
theorem oneQLabel_even (k : ℕ) : oneQLabel (2 * k + 2) = 2 * k + 1 := by
  unfold oneQLabel NearCore.mate
  split_ifs <;> first | contradiction | omega

/-- The partner map of `Q` on `V_m`: `∞ ↔ 4`, and `oneQLabel` on the other labels
(`results/f2-slice-factcheck-extend.md`, organize-archive cd0ed47, §2). -/
def oneQFn (m : ℕ) [NeZero m] : Vertex m → Vertex m
  | none => some ((4 : ℕ) : ZMod (2 * m - 1))
  | some x => if x.val = 4 then none else some ((oneQLabel x.val : ℕ) : ZMod (2 * m - 1))

/-- The partner map of `Q` is an involution for `m ≥ 3`. -/
theorem oneQFn_involutive (hm : 3 ≤ m) : Function.Involutive (oneQFn m) := by
  have h4 : ((4 : ℕ) : ZMod (2 * m - 1)).val = 4 := ZMod.val_natCast_of_lt (by omega)
  rintro (_ | x)
  · simp only [oneQFn, h4, ↓reduceIte]
  by_cases hx : x.val = 4
  · simp only [oneQFn, hx, ↓reduceIte, Option.some.injEq]
    rw [← hx, ZMod.natCast_zmod_val]
  · have hv : ((oneQLabel x.val : ℕ) : ZMod (2 * m - 1)).val = oneQLabel x.val :=
      ZMod.val_natCast_of_lt (oneQLabel_lt hm (ZMod.val_lt x))
    simp only [oneQFn, hx, ↓reduceIte, hv, oneQLabel_ne_four, oneQLabel_oneQLabel hx,
      ZMod.natCast_zmod_val]

/-- The partner map of `Q` has no fixed point for `m ≥ 3`. -/
theorem oneQFn_ne (hm : 3 ≤ m) (v : Vertex m) : oneQFn m v ≠ v := by
  rcases v with _ | x
  · simp [oneQFn]
  by_cases hx : x.val = 4
  · simp [oneQFn, hx]
  · simp only [oneQFn, hx, ↓reduceIte, ne_eq, Option.some.injEq]
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (oneQLabel_lt hm (ZMod.val_lt x))] at h'
    exact oneQLabel_ne_self _ h'

/-- The matching `Q = {0 3, ∞ 4, e_0} ∪ {e_k : 2 ≤ k ≤ m - 2}` on `V_m`, `e_k = {2k + 1, 2k + 2}`
(Proposition Q of `results/f2-slice-factcheck-extend.md`, organize-archive cd0ed47, §2). It is
the two-switch of `pStar` on `{∞, 0}` and `{3, 4}`. -/
def oneQ (m : ℕ) [NeZero m] (hm : 5 ≤ m) : PerfectMatching (Vertex m) where
  mate := Function.Involutive.toPerm _ (oneQFn_involutive (by omega))
  mate_mate := oneQFn_involutive (by omega)
  mate_ne := oneQFn_ne (by omega)

/-- The partner map of `Q`. -/
@[simp]
theorem oneQ_mate (hm : 5 ≤ m) (v : Vertex m) : (oneQ m hm).mate v = oneQFn m v :=
  rfl

/-- `Q` pairs `4` with `∞`. -/
theorem oneQ_mate_four (hm : 5 ≤ m) :
    (oneQ m hm).mate (some ((4 : ℕ) : ZMod (2 * m - 1))) = none := by
  simp only [oneQ_mate, oneQFn, ZMod.val_natCast_of_lt (show 4 < 2 * m - 1 by omega), ↓reduceIte]

/-- `Q` pairs a label `x ≠ 4` with `oneQLabel x`. -/
theorem oneQ_mate_label (hm : 5 ≤ m) {x : ℕ} (hx : x < 2 * m - 1) (hx4 : x ≠ 4) :
    (oneQ m hm).mate (some (x : ZMod (2 * m - 1))) = some (oneQLabel x : ZMod (2 * m - 1)) := by
  simp only [oneQ_mate, oneQFn, ZMod.val_natCast_of_lt hx, hx4, ↓reduceIte]

/-- `Q` maps a set of labels that avoids `4` and is closed under `oneQLabel` into itself. -/
theorem oneQ_mate_mem (hm : 5 ≤ m) {W : Finset ℕ} (hWn : ∀ x ∈ W, x < 2 * m - 1) (hW4 : 4 ∉ W)
    (hQ : ∀ x ∈ W, oneQLabel x ∈ W) : ∀ x ∈ W, ∃ y ∈ W,
      (oneQ m hm).mate (some (x : ZMod (2 * m - 1))) = some (y : ZMod (2 * m - 1)) :=
  fun x hx ↦ ⟨oneQLabel x, hQ x hx, oneQ_mate_label hm (hWn x hx) fun h ↦ hW4 (h ▸ hx)⟩

/-- `Q ∪ F_t` is not one cycle for `t ≠ m + 2`. With `r ≡ 2t` in `[0, 2m - 1)`, the block is the
`8`-cycle on `0, 1, 2, 3, n-4, …, n-1` for `t = m - 1` (`r = 2m - 2`), the `6`-cycle on
`0, 1, 2, 3, n-2, n-1` for `t = m` (`r = 1`), and otherwise the `2`- or `4`-cycle of `e_k, e_{k'}`
with `2(k + k') + 3 ≡ r` and `k, k' ∈ {0} ∪ [2, m - 2]` (`results/one-factor-q-review.md`,
organize-archive not committed yet, steps 1 and 2; `results/f2-slice-factcheck-extend.md`,
cd0ed47, §2). -/
theorem not_ham_oneQ (hm : 5 ≤ m) {t : ZMod (2 * m - 1)} (ht : t ≠ (m : ZMod (2 * m - 1)) + 2) :
    ¬Ham (oneQ m hm) (factor m t) := by
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  have hr5 : (2 * t).val ≠ 5 := fun h5 ↦ ht (eq_of_two_mul_eq (by
    rw [← hr, h5, mul_add, two_mul_natCast_self]
    norm_num))
  generalize (2 * t).val = r at hr hrq hr5
  have hlt : ∀ x ∈ ({0, 1, 2, 3, 2 * m - 5, 2 * m - 4, 2 * m - 3, 2 * m - 2} : Finset ℕ),
      x < 2 * m - 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  rcases (by omega : r = 2 * m - 2 ∨ r = 1 ∨ (r ≠ 1 ∧ r ≠ 2 * m - 2)) with hr1 | hr1 | ⟨hr1, hr2⟩
  · refine not_ham_of_labels t hr {0, 1, 2, 3, 2 * m - 5, 2 * m - 4, 2 * m - 3, 2 * m - 2}
      hlt (w₀ := 0) (by simp) (oneQ_mate_mem hm hlt (by simp; omega) fun x hx ↦ ?_)
      (fun x hx ↦ ?_)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      unfold oneQLabel NearCore.mate
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
      omega
  · have hlt' : ∀ x ∈ ({0, 1, 2, 3, 2 * m - 3, 2 * m - 2} : Finset ℕ), x < 2 * m - 1 :=
      fun x hx ↦ hlt x (by simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    refine not_ham_of_labels t hr {0, 1, 2, 3, 2 * m - 3, 2 * m - 2} hlt' (w₀ := 0) (by simp)
      (oneQ_mate_mem hm hlt' (by simp; omega) fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      unfold oneQLabel NearCore.mate
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
      omega
  · obtain ⟨x, hx, hx1, hxr⟩ := exists_two_mul_add_three hrq hr1 hr2
    obtain ⟨k, hk, k', hk', rfl⟩ : ∃ k, (k = 0 ∨ (2 ≤ k ∧ k ≤ m - 2)) ∧ ∃ k',
        (k' = 0 ∨ (2 ≤ k' ∧ k' ≤ m - 2)) ∧ k + k' = x := by
      have := hx1 hm hr5
      rcases (by omega : x = 0 ∨ (2 ≤ x ∧ x ≤ m - 2) ∨ x = m - 1 ∨ (m ≤ x ∧ x ≤ 2 * (m - 2)))
        with h | h | h | h
      · exact ⟨0, Or.inl rfl, 0, Or.inl rfl, by omega⟩
      · exact ⟨0, Or.inl rfl, x, Or.inr h, by omega⟩
      · exact ⟨m - 3, Or.inr (by omega), 2, Or.inr (by omega), by omega⟩
      · exact ⟨m - 2, Or.inr (by omega), x - (m - 2), Or.inr (by omega), by omega⟩
    have hWn : ∀ y ∈ ({2 * k + 1, 2 * k + 2, 2 * k' + 1, 2 * k' + 2} : Finset ℕ),
        y < 2 * m - 1 := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    refine not_ham_of_labels t hr {2 * k + 1, 2 * k + 2, 2 * k' + 1, 2 * k' + 2} hWn
      (w₀ := 2 * k + 1) (by simp) (oneQ_mate_mem hm hWn (by simp; omega) fun y hy ↦ ?_)
      (forall_exists_four (s := 2 * (k + k') + 3) (by omega) (by omega) (by omega) (by omega) hxr)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl
    · rw [oneQLabel_odd (by omega)]
      simp
    · rw [oneQLabel_even]
      simp
    · rw [oneQLabel_odd (by omega)]
      simp
    · rw [oneQLabel_even]
      simp

/-- `Q ∪ F_{m+2}` is one cycle for `m ≥ 5`. Here `2t ≡ 5`, the labels `x` and `5 - x` always lie
in one component, and the chain `e_j → e_{N+2-j} → e_{j+1}` reaches every `e_j` from `0`
(`results/one-factor-q-review.md`, organize-archive not committed yet, step 3;
`results/f2-slice-factcheck-extend.md`, cd0ed47, §2 step 3). -/
theorem ham_oneQ_self (hm : 5 ≤ m) :
    Ham (oneQ m hm) (factor m ((m : ZMod (2 * m - 1)) + 2)) := by
  set t : ZMod (2 * m - 1) := (m : ZMod (2 * m - 1)) + 2 with ht
  set G := (oneQ m hm).toGraph ⊔ (factor m t).toGraph with hG
  have h5 : ((5 : ℕ) : ZMod (2 * m - 1)) = 2 * t := by
    rw [ht, mul_add, two_mul_natCast_self]
    norm_num
  have hF : ∀ {a b : ℕ}, (a + b = 5 ∨ a + b = 5 + (2 * m - 1)) →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (b : ZMod (2 * m - 1))) := fun hab ↦
    (reachable_factor_of_add t h5 hab).mono le_sup_right
  have hQ : ∀ {a : ℕ}, a < 2 * m - 1 → a ≠ 4 →
      G.Reachable (some (a : ZMod (2 * m - 1))) (some (oneQLabel a : ZMod (2 * m - 1))) :=
    fun ha ha4 ↦ (SimpleGraph.Adj.reachable
      (by rw [toGraph_adj, oneQ_mate_label hm ha ha4])).mono le_sup_left
  have r03 : G.Reachable (some ((0 : ℕ) : ZMod (2 * m - 1)))
      (some ((3 : ℕ) : ZMod (2 * m - 1))) :=
    hQ (a := 0) (by omega) (by omega)
  have r32 := hF (a := 3) (b := 2) (Or.inl rfl)
  have r21 : G.Reachable (some ((2 : ℕ) : ZMod (2 * m - 1)))
      (some ((1 : ℕ) : ZMod (2 * m - 1))) :=
    hQ (a := 2) (by omega) (by omega)
  have r14 := hF (a := 1) (b := 4) (Or.inl rfl)
  have r4i : G.Reachable (some ((4 : ℕ) : ZMod (2 * m - 1))) none :=
    (SimpleGraph.Adj.reachable (by rw [toGraph_adj, oneQ_mate_four hm])).mono le_sup_left
  have r05 := hF (a := 0) (b := 5) (Or.inl rfl)
  have hodd : ∀ j, 2 ≤ j → j ≤ m - 2 → G.Reachable (some ((0 : ℕ) : ZMod (2 * m - 1)))
      (some ((2 * j + 1 : ℕ) : ZMod (2 * m - 1))) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ ↦ r05
    | succ j hj ih =>
      intro hjm
      have s1 : G.Reachable (some ((2 * j + 1 : ℕ) : ZMod (2 * m - 1)))
          (some ((2 * j + 2 : ℕ) : ZMod (2 * m - 1))) := by
        have := hQ (a := 2 * j + 1) (by omega) (by omega)
        rwa [oneQLabel_odd (by omega)] at this
      have s2 := hF (a := 2 * j + 2) (b := 2 * (m - j) + 2) (Or.inr (by omega))
      have s3 : G.Reachable (some ((2 * (m - j) + 2 : ℕ) : ZMod (2 * m - 1)))
          (some ((2 * (m - j) + 1 : ℕ) : ZMod (2 * m - 1))) := by
        have := hQ (a := 2 * (m - j) + 2) (by omega) (by omega)
        rwa [oneQLabel_even] at this
      have s4 := hF (a := 2 * (m - j) + 1) (b := 2 * (j + 1) + 1) (Or.inr (by omega))
      exact (ih (by omega)).trans (s1.trans (s2.trans (s3.trans s4)))
  have hall : ∀ v, G.Reachable (some ((0 : ℕ) : ZMod (2 * m - 1))) v := by
    rintro (_ | x)
    · exact r03.trans (r32.trans (r21.trans (r14.trans r4i)))
    rw [← ZMod.natCast_zmod_val x]
    have hxl := ZMod.val_lt x
    generalize x.val = k at hxl
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k) with
      rfl | rfl | rfl | rfl | rfl | hk
    · rfl
    · exact r03.trans (r32.trans r21)
    · exact r03.trans r32
    · exact r03
    · exact r03.trans (r32.trans (r21.trans r14))
    · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · have := hQ (a := 2 * (j - 1) + 1) (by omega) (by omega)
        rw [oneQLabel_odd (by omega), show 2 * (j - 1) + 2 = 2 * j by omega] at this
        exact (hodd (j - 1) (by omega) (by omega)).trans this
      · exact hodd j (by omega) (by omega)
  exact ⟨fun u v ↦ (hall u).symm.trans (hall v)⟩

/-- Proposition Q (`results/f2-slice-factcheck-extend.md`, organize-archive cd0ed47, §2, reviewed
in `results/one-factor-q-review.md`, organize-archive not committed yet): for `m ≥ 5`, `Q ∪ F_t`
is one cycle exactly for `t = m + 2`. -/
theorem ham_oneQ_iff (hm : 5 ≤ m) (t : ZMod (2 * m - 1)) :
    Ham (oneQ m hm) (factor m t) ↔ t = (m : ZMod (2 * m - 1)) + 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ham_oneQ_self hm⟩
  by_contra ht
  exact not_ham_oneQ hm ht h

/-- `X(Q) = 1` for `m ≥ 5` (`hamCount`, ham_pairings main 978559a; Proposition Q of
`results/f2-slice-factcheck-extend.md`, organize-archive cd0ed47, §2, reviewed in
`results/one-factor-q-review.md`, organize-archive not committed yet). -/
theorem hamCount_oneQ (hm : 5 ≤ m) : hamCount m (oneQ m hm) = 1 := by
  rw [hamCount, Finset.card_eq_one]
  exact ⟨(m : ZMod (2 * m - 1)) + 2, by ext t; simp [ham_oneQ_iff hm]⟩

/-- The translate `Q + b` (`shift`, ham-spin 55c17eb) closes one cycle with `F_t` exactly for
`t = m + 2 + b`, so its profile is the unit vector `e_{m+2+b}` (`results/one-factor-q-review.md`,
organize-archive not committed yet, step 4; `results/f2-slice-factcheck-extend.md`, cd0ed47). -/
theorem ham_shift_oneQ_iff (hm : 5 ≤ m) (b t : ZMod (2 * m - 1)) :
    Ham (shift m b • oneQ m hm) (factor m t) ↔ t = (m : ZMod (2 * m - 1)) + 2 + b := by
  rw [ham_shift_iff, ham_oneQ_iff hm, sub_eq_iff_eq_add]

end OneQ

end Pairing.RoundRobin.Canonical
