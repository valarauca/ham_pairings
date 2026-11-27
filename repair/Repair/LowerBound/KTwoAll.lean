import Repair.LowerBound.LineSmallTable
import Repair.LowerBound.SevenSmall
import Repair.LowerBound.Thirteen

/-!
# `N_m ≥ 2` for every `m ≥ 6` with `2m - 1` prime

Source: `results/struct-lb-extend.md` §3.3, Theorem B, all three cases and the case `m = 7`, with
`results/struct-lb-factcheck-extend.md` §1 and §3 (organize-archive b5cb45e). The contra form is
`results/struct-lb-contra.md` §3.2, Theorem 2 (b5cb45e).

`KTwo.lean` proves Theorem B at every prime `n ≥ 1177`. This file closes the primes below.

* **`e = e_∞`.** At `n ≥ 25` a cell of length `1/24` holds a point `μ/n`. At `n = 11, 17, 19, 23`
  the points are named (`exists_cell7_small`).
* **`e = e_x`.** At `n < 1177` a shortest vector of `Λ_X` is a line of the small table
  (`lineGoodAt_of_lt_1177`).
* **`n = 13`.** The factor tail has `ρ = 1`, and the second tail `T7` has `ρ ≥ 2`
  (`not_repairBound_one_seven`).

* `exists_ham_of_agree_one_of_ne` : Theorem B in walk form, at every prime `n ≥ 11`, `n ≠ 13`.
* `two_le_tailDist_factorTail_of_ne` : `ρ(T(n)) ≥ 2` at every prime `n = 2m - 1 ≥ 11`, `n ≠ 13`.
* `not_repairBound_one_of_prime` : `N_m ≥ 2`, as `¬ RepairBound m G0 1`, for every `m ≥ 6` with
  `2m - 1` prime.
-/

namespace Pairing

namespace LowerBound

open PerfectMatching RoundRobin

variable {n : ℕ}

/-- **The core `{e_∞}` from its cells** (`results/struct-lb-extend.md` §3.3, Theorem B case 1,
organize-archive b5cb45e). For a prime `n ≥ 11`, if every involution of the seven points with at
most one fixed point is covered by the context of a cell that holds a point `μ/n`, then every `P`
that agrees with `F_{s0}` off `G0 ∪ {∞, s0}` has some `P ∪ F_t` one cycle. -/
theorem exists_ham_inf_of (hn : Odd n) (hp : n.Prime) (h11 : 11 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ none → v ≠ some s0 →
      P.mate v = (factor hn s0).mate v)
    (hcell : ∀ r : Fin 7 → Fin 7, (∀ j, r (r j) = j) → (∀ i j, r i = i → r j = j → i = j) →
      ∃ (o oi : List ℕ) (k : List ℤ) (μ : ℤ), (∀ j, fin7 o (fin7 oi j) = j) ∧
        ArcCovers (fin7 o) (fin7 oi) tau7 r ∧ RealCell7 o k ((μ : ℝ) / n)) :
    ∃ t, Ham P (factor hn t) := by
  have : NeZero n := ⟨hp.ne_zero⟩
  have hinj := pt7_injective h11 hs0
  have hspec : ∀ y, (∀ j, y ≠ pt7 n s0 j) →
      P.mate (some y) = (factor hn s0).mate (some y) := by
    intro y hy
    rw [pt7_eq] at hy
    refine hP _ (fun j h ↦ ?_) (by simp) (fun h ↦ hy 6 (Option.some_inj.mp h))
    have h' := Option.some_inj.mp h
    fin_cases j
    · exact hy 5 h'
    · exact hy 4 h'
    · exact hy 3 h'
    · exact hy 0 h'
    · exact hy 1 h'
    · exact hy 2 h'
  have hP7 : ∀ y, (∀ j, y ≠ pt7 n s0 j) → pinned P y = 2 * s0 - y :=
    fun y hy ↦ pinned_eq_of_mate_eq (hspec y hy)
  have hex : ∀ j, ∃ k, pinned P (pt7 n s0 j) = pt7 n s0 k := by
    intro j
    rcases hw : P.mate (some (pt7 n s0 j)) with _ | y
    · exact ⟨j, pinned_apply_of_mate_eq_none P hw⟩
    · by_contra hcon
      have hy : ∀ k, y ≠ pt7 n s0 k := fun k h ↦ hcon ⟨k, by
        rw [pinned_apply_of_mate_eq_some P hw, h]⟩
      have h1 := hspec y hy
      have h2 : P.mate (some y) = some (pt7 n s0 j) := by rw [← hw, mate_mate]
      have hys : y ≠ s0 := fun h ↦ hy 6 (by rw [h]; rfl)
      rw [factor_mate, mateFn_of_ne _ _ hys, h2, Option.some_inj] at h1
      apply hy (tau7 j)
      rw [pt7_tau7 hs0, h1]
      ring
  choose r hr using hex
  have hr1 : ∀ j, r (r j) = j := by
    intro j
    apply hinj
    rw [← hr, ← hr]
    exact pinnedFn_involutive P _
  have hfix : ∀ j, r j = j → P.mate (some (pt7 n s0 j)) = none := by
    intro j hj
    have h1 := hr j
    rw [hj] at h1
    rcases hw : P.mate (some (pt7 n s0 j)) with _ | z
    · rfl
    · rw [pinned_apply_of_mate_eq_some P hw] at h1
      have := P.mate_ne (some (pt7 n s0 j))
      rw [hw, h1] at this
      exact absurd rfl this
  have hr2 : ∀ i j, r i = i → r j = j → i = j := by
    intro i j hi hj
    apply hinj
    have h1 : P.mate none = some (pt7 n s0 i) := by rw [← hfix i hi, mate_mate]
    have h2 : P.mate none = some (pt7 n s0 j) := by rw [← hfix j hj, mate_mate]
    exact Option.some_inj.mp (h1.symm.trans h2)
  obtain ⟨o, oi, k, μ, hoi, hcov, hcell'⟩ := hcell r hr1 hr2
  exact ham_of_realCell7 hn hp hs0 hP7 hr hoi hcell' hcov

/-- **A finite 1-core from its samples** (`results/struct-lb-extend.md` §3.3, Theorem B case 2,
organize-archive b5cb45e). Let `n ≥ 11` be prime, `x ≠ 0`, and `s0 ± x` not gadget points. If
every matching of the eight ends is covered by the context of a cell that holds a lift
`(μ', a')/n` with `a' ≡ 2x μ'`, then every `P` that agrees with `F_{s0}` off
`G0 ∪ {s0 + x, s0 - x}` has some `P ∪ F_t` one cycle. -/
theorem exists_ham_finite_of (hn : Odd n) (hp : n.Prime) (h11 : 11 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))} {x : ZMod n} (hx : x ≠ 0)
    (hxg : ∀ j, s0 + x ≠ gadgetPt n j) (hxg' : ∀ j, s0 - x ≠ gadgetPt n j)
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ some (s0 + x) → v ≠ some (s0 - x) →
      P.mate v = (factor hn s0).mate v)
    (hcell : ∀ r : Fin 8 → Fin 8, (∀ j, r (r j) = j) → (∀ j, r j ≠ j) →
      ∃ (o oi : List ℕ) (k : List ℤ) (μ' a' : ℤ), (∀ j, fin8 o (fin8 oi j) = j) ∧
        ArcCovers (fin8 o) (fin8 oi) tau8 r ∧
        (n : ℤ) ∣ a' - ((2 * x : ZMod n).val : ℤ) * μ' ∧ RealCell8 o k (μ' / n) (a' / n)) :
    ∃ t, Ham P (factor hn t) := by
  have : NeZero n := ⟨hp.ne_zero⟩
  have hx2 : x + x ≠ 0 := fun h ↦ hx ((isUnit_two hn).mul_left_cancel (by linear_combination h))
  have hinj := pt8_injective h11 hx2 hxg hxg'
  have hspec : ∀ y, (∀ j, y ≠ pt8 n s0 x j) →
      P.mate (some y) = (factor hn s0).mate (some y) := by
    intro y hy
    rw [pt8_eq] at hy
    refine hP _ (fun j h ↦ ?_) (fun h ↦ hy 3 (Option.some_inj.mp h))
      (fun h ↦ hy 7 (Option.some_inj.mp h))
    have h' := Option.some_inj.mp h
    fin_cases j
    · exact hy 6 h'
    · exact hy 5 h'
    · exact hy 4 h'
    · exact hy 0 h'
    · exact hy 1 h'
    · exact hy 2 h'
  have hP8 : ∀ y, (∀ j, y ≠ pt8 n s0 x j) → pinned P y = 2 * s0 - y :=
    fun y hy ↦ pinned_eq_of_mate_eq (hspec y hy)
  have hnone : P.mate none = some s0 := by
    rw [hP none (fun j h ↦ by simp at h) (by simp) (by simp), factor_mate, mateFn_none]
  have hns : ∀ j, pt8 n s0 x j ≠ s0 := by
    intro j h
    rw [pt8_eq] at h
    fin_cases j
    all_goals first
      | exact ne_gadgetPt_of_two_mul h11 hs0 _ h.symm
      | exact hx (by
          have h' : s0 + x = s0 := h
          linear_combination h')
      | exact hx (by
          have h' : s0 - x = s0 := h
          linear_combination -h')
  have hex : ∀ j, ∃ k, P.mate (some (pt8 n s0 x j)) = some (pt8 n s0 x k) := by
    intro j
    rcases hw : P.mate (some (pt8 n s0 x j)) with _ | y
    · exfalso
      have h1 : P.mate none = some (pt8 n s0 x j) := by rw [← hw, mate_mate]
      rw [hnone, Option.some_inj] at h1
      exact hns j h1.symm
    · by_contra hcon
      have hy : ∀ k, y ≠ pt8 n s0 x k := fun k h ↦ hcon ⟨k, by rw [h]⟩
      have h1 := hspec y hy
      have h2 : P.mate (some y) = some (pt8 n s0 x j) := by rw [← hw, mate_mate]
      by_cases hys : y = s0
      · rw [hys, factor_mate, mateFn_self] at h1
        rw [hys, h1] at h2
        simp at h2
      · rw [factor_mate, mateFn_of_ne _ _ hys, h2, Option.some_inj] at h1
        apply hy (tau8 j)
        rw [pt8_tau8 hs0, h1]
        ring
  choose r hr using hex
  have hr' : ∀ j, pinned P (pt8 n s0 x j) = pt8 n s0 x (r j) :=
    fun j ↦ pinned_apply_of_mate_eq_some P (hr j)
  have hr1 : ∀ j, r (r j) = j := by
    intro j
    have h1 := P.mate_mate (some (pt8 n s0 x j))
    rw [hr, hr, Option.some_inj] at h1
    exact hinj h1
  have hr2 : ∀ j, r j ≠ j := by
    intro j h
    have h1 := P.mate_ne (some (pt8 n s0 x j))
    rw [hr, h] at h1
    exact h1 rfl
  obtain ⟨o, oi, k, μ', a', hoi, hcov, hdvd, hcell'⟩ := hcell r hr1 hr2
  exact ham_of_realCell8 hn hp hs0 hP8 hr' (X := ((2 * x : ZMod n).val : ℤ)) (by simp) hoi hdvd
    hcell' hcov

/-- **A finite 1-core is bad below `n = 1177`** (`results/struct-lb-extend.md` §3.3, Theorem B
cases 2 and 3, organize-archive b5cb45e). Let `n` be a prime with `11 ≤ n < 1177`, `n ≠ 13`,
`x ≠ 0`, and `s0 ± x` not gadget points. Every `P` that agrees with `F_{s0}` off
`G0 ∪ {s0 + x, s0 - x}` has some `P ∪ F_t` one cycle. -/
theorem exists_ham_finite_lt (hn : Odd n) (hp : n.Prime) (h11 : 11 ≤ n) (h13 : n ≠ 13)
    (h1177 : n < 1177) {s0 : ZMod n} (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))}
    {x : ZMod n} (hx : x ≠ 0) (hxg : ∀ j, s0 + x ≠ gadgetPt n j)
    (hxg' : ∀ j, s0 - x ≠ gadgetPt n j)
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ some (s0 + x) → v ≠ some (s0 - x) →
      P.mate v = (factor hn s0).mate v) : ∃ t, Ham P (factor hn t) := by
  have : NeZero n := ⟨hp.ne_zero⟩
  have : Fact n.Prime := ⟨hp⟩
  have hx2 : x + x ≠ 0 := fun h ↦ hx ((isUnit_two hn).mul_left_cancel (by linear_combination h))
  set X : ℤ := ((2 * x : ZMod n).val : ℤ) with hXdef
  have hX : (X : ZMod n) = 2 * x := by simp [X]
  refine exists_ham_finite_of hn hp h11 hs0 hx hxg hxg' hP fun r hr1 hr2 ↦ ?_
  obtain ⟨c, a, hlat, -, -, hH, hgcd, hnc⟩ := exists_shortVector hp X
  obtain ⟨c, a, hlat, hH, hgcd, hnc, hc1⟩ : ∃ c a : ℤ, InLattice n X c a ∧
      3 * (c ^ 2 + a ^ 2) ^ 2 ≤ 4 * (n : ℤ) ^ 2 ∧ Int.gcd c a = 1 ∧ ¬(n : ℤ) ∣ c ∧ 1 ≤ c := by
    have hc0 : c ≠ 0 := fun h ↦ hnc (h ▸ dvd_zero _)
    rcases lt_or_gt_of_ne hc0 with hc | hc
    · refine ⟨-c, -a, ?_, by rw [neg_sq, neg_sq]; exact hH,
        by rw [Int.gcd_neg, Int.neg_gcd]; exact hgcd, fun h ↦ hnc ((dvd_neg).mp h), by omega⟩
      obtain ⟨w, hw⟩ := hlat
      exact ⟨-w, by linear_combination -hw⟩
    · exact ⟨c, a, hlat, hH, hgcd, hnc, hc⟩
  have hcz : (c : ZMod n) ≠ 0 := fun h ↦ hnc ((ZMod.intCast_zmod_eq_zero_iff_dvd c n).mp h)
  have hXl : ∀ l : ℤ, (n : ℤ) ∣ a - l * c → (X : ZMod n) = l := by
    intro l hl
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hlat
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hl
    push_cast at h1 h2
    have h3 : ((l : ZMod n) - X) * c = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linear_combination -h4
    · exact absurd h4 hcz
  have hlab : ∀ (l : ℤ) (j : Fin 6), (l : ZMod n) = 2 * gadgetPt n j - 7 →
      ¬(n : ℤ) ∣ a - l * c := by
    intro l j hlj hl
    apply two_mul_ne_of_ne_gadgetPt hn hs0 hxg j
    rw [← hX, hXl l hl, hlj]
  have e0 : ¬(n : ℤ) ∣ a - 0 * c := by
    intro hl
    have := hXl 0 hl
    rw [hX, Int.cast_zero] at this
    exact hx2 (by linear_combination this)
  have e1 := hlab 1 3 (by simp [gadgetPt]; norm_num)
  have e2 := hlab (-1) 2 (by simp [gadgetPt]; norm_num)
  have e3 := hlab 3 4 (by simp [gadgetPt]; norm_num)
  have e4 := hlab (-3) 1 (by simp [gadgetPt]; norm_num)
  have e5 := hlab 5 5 (by simp [gadgetPt]; norm_num)
  have e6 := hlab (-5) 0 (by simp [gadgetPt]; norm_num)
  have hne : ∀ l : ℤ, ¬(n : ℤ) ∣ a - l * c → a ≠ l * c :=
    fun l h he ↦ h (by rw [he, sub_self]; exact dvd_zero _)
  have ha0 : a ≠ 0 := fun h ↦ hne 0 e0 (by rw [h, zero_mul])
  have hadm : admB c a = true := by
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hc1, ha0⟩, hgcd⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact fun h ↦ hne 1 e1 (by rw [h, one_mul])
    · exact fun h ↦ hne (-1) e2 (by rw [h]; ring)
    · exact hne 3 e3
    · exact fun h ↦ hne (-3) e4 (by rw [h]; ring)
    · exact hne 5 e5
    · exact fun h ↦ hne (-5) e6 (by rw [h]; ring)
  have hlabB : labelB c a n = true := by
    simp only [labelB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
      ne_eq]
    exact ⟨fun h ↦ e0 (Int.dvd_iff_emod_eq_zero.mpr h), fun h ↦ e1 (Int.dvd_iff_emod_eq_zero.mpr h),
      fun h ↦ e2 (Int.dvd_iff_emod_eq_zero.mpr h), fun h ↦ e3 (Int.dvd_iff_emod_eq_zero.mpr h),
      fun h ↦ e4 (Int.dvd_iff_emod_eq_zero.mpr h), fun h ↦ e5 (Int.dvd_iff_emod_eq_zero.mpr h),
      fun h ↦ e6 (Int.dvd_iff_emod_eq_zero.mpr h)⟩
  obtain ⟨o, oi, k, ν, hoi, hcov, hcell⟩ :=
    lineGoodAt_of_lt_1177 hp h11 h13 h1177 hadm hH hlabB r hr1 hr2
  refine ⟨o, oi, k, c * ν, a * ν, hoi, hcov, ?_, hcell⟩
  obtain ⟨w, hw⟩ := hlat
  exact ⟨w * ν, by linear_combination ν * hw⟩

/-- The primes `11 ≤ n < 25` other than `13`. -/
theorem mem_small_primes (hp : n.Prime) (h11 : 11 ≤ n) (h13 : n ≠ 13) (h25 : n < 25) :
    n ∈ [11, 17, 19, 23] := by
  interval_cases n <;> first | decide | exact absurd rfl h13 | (exfalso; norm_num at hp)

/-- **Theorem B of `results/struct-lb-extend.md`, in walk form, at every prime `n ≥ 11` other
than `13`** (organize-archive b5cb45e). With `2 s0 = 7`, let `u` be a vertex off the gadget `G0`.
Every perfect matching `P` that agrees with `F_{s0}` off `G0 ∪ {u, F_{s0} u}` has some round-robin
factor `F_t` with `P ∪ F_t` one cycle. -/
theorem exists_ham_of_agree_one_of_ne (hn : Odd n) (hp : n.Prime) (h11 : 11 ≤ n) (h13 : n ≠ 13)
    {s0 : ZMod n} (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))}
    {u : Option (ZMod n)} (hu : ∀ j, u ≠ some (gadgetPt n j))
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ u → v ≠ (factor hn s0).mate u →
      P.mate v = (factor hn s0).mate v) : ∃ t, Ham P (factor hn t) := by
  have hinf : ∀ P' : PerfectMatching (Option (ZMod n)),
      (∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ none → v ≠ some s0 →
        P'.mate v = (factor hn s0).mate v) → ∃ t, Ham P' (factor hn t) := by
    intro P' hP'
    by_cases h25 : 25 ≤ n
    · exact exists_ham_inf hn hp h25 hs0 hP'
    · exact exists_ham_inf_of hn hp h11 hs0 hP' fun r h1 h2 ↦
        exists_cell7_small (mem_small_primes hp h11 h13 (by omega)) h1 h2
  rcases u with _ | y
  · rw [factor_mate, mateFn_none] at hP
    exact hinf P hP
  · by_cases hys : y = s0
    · subst hys
      rw [factor_mate, mateFn_self] at hP
      exact hinf P fun v hv h1 h2 ↦ hP v hv h2 h1
    · rw [factor_mate, mateFn_of_ne _ _ hys] at hP
      have hx : y - s0 ≠ 0 := fun h ↦ hys (by linear_combination h)
      have hxg : ∀ j, s0 + (y - s0) ≠ gadgetPt n j := fun j h ↦ hu j (by rw [← h]; ring_nf)
      have hxg' : ∀ j, s0 - (y - s0) ≠ gadgetPt n j := by
        intro j h
        apply hu (Fin.rev j)
        rw [gadgetPt_rev, ← h, ← hs0]
        ring_nf
      have hP' : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ some (s0 + (y - s0)) →
          v ≠ some (s0 - (y - s0)) → P.mate v = (factor hn s0).mate v :=
        fun v hv h1 h2 ↦ hP v hv (by rw [show s0 + (y - s0) = y by ring] at h1; exact h1)
          (by rw [show s0 - (y - s0) = 2 * s0 - y by ring] at h2; exact h2)
      by_cases h1177 : 1177 ≤ n
      · exact exists_ham_finite hn hp h1177 hs0 hx hxg hxg' hP'
      · exact exists_ham_finite_lt hn hp h11 h13 (by omega) hs0 hx hxg hxg' hP'

end LowerBound

namespace RoundRobin.Canonical

open PerfectMatching LowerBound

variable {m : ℕ} [NeZero m]

/-- **`ρ(T(n)) ≥ 2` at every prime `n = 2m - 1 ≥ 11` other than `13`**
(`results/struct-lb-extend.md` Theorem B, organize-archive b5cb45e). Every zero state differs from
the factor tail `T(n)` in at least two edges. -/
theorem two_le_tailDist_factorTail_of_ne (hm : 6 ≤ m) (hp : (2 * m - 1).Prime)
    (h13 : 2 * m - 1 ≠ 13) (P : ZeroState m) :
    2 ≤ tailDist P.1 (FactorCap.factorTail m (by omega)) := by
  by_contra h0
  obtain ⟨u, hu, hagree⟩ := exists_agree_of_tailDist_le_one
    (T := FactorCap.factorTail m (by omega)) (Q := factor m (FactorCap.capCenter m)) (P := P.1)
    (FactorCap.factorTail_mate _) (by omega)
  have hng : ∀ v : Vertex m, (∀ j, v ≠ some (gadgetPt (2 * m - 1) j)) → v ∉ FactorCap.gadget m :=
    fun v hv h ↦ by
      obtain ⟨j, hj⟩ := (mem_gadget_iff v).mp h
      exact hv j hj
  obtain ⟨t, ht⟩ := exists_ham_of_agree_one_of_ne (modulus_odd m) hp (by omega) h13
    FactorCap.two_mul_capCenter (u := u) (fun j h ↦ hu ((mem_gadget_iff u).mpr ⟨j, h⟩))
    (fun v hv h1 h2 ↦ hagree v (hng v hv) h1 h2)
  exact P.2 t ht

/-- **`N_m ≥ 2` for every `m ≥ 6` with `2m - 1` prime** (`results/struct-lb-extend.md`
Theorem B, organize-archive b5cb45e). At `m ≠ 7` no zero state lies within distance `1` of the
factor tail `T(n)`. At `m = 7` the second tail `T7` plays its part. So `RepairBound m G0 1`
fails. -/
theorem not_repairBound_one_of_prime (hm : 6 ≤ m) (hp : (2 * m - 1).Prime) :
    ¬RepairBound m (FactorCap.gadget m) 1 := by
  rcases eq_or_ne m 7 with rfl | h7
  · exact not_repairBound_one_seven
  · intro h
    obtain ⟨P, hP⟩ := h (FactorCap.factorTail m (by omega))
    have := two_le_tailDist_factorTail_of_ne hm hp (by omega) P
    omega

end RoundRobin.Canonical

end Pairing
