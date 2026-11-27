import Repair.LowerBound.Cert
import Repair.LowerBound.Lattice
import Repair.LowerBound.LineTable
import Repair.LowerBound.Seven

/-!
# `N_m ≥ 2` for every `m ≥ 1069` with `2m - 1` prime

Source: `results/struct-lb-extend.md` §3.3, Theorem B, cases 1 and 2, with
`results/struct-lb-factcheck-extend.md` §1 and §3, claims 1 and 7 (organize-archive b5cb45e).
The contra form is `results/struct-lb-contra.md` §3.2, Theorem 2 (b5cb45e).

A zero state `P` with `|T(n) ∖ P| ≤ 1` agrees with `F_{s0}` off `G0 ∪ e` for one tail edge
`e = {u, F_{s0} u}`. That is the reduction of COD-186 Corollary 3 at `K = 1`, done here directly.
There are two cases.

* **`e = e_∞`.** `P̃` is an involution of the seven points `G0 ∪ {s0}` with one fixed point, and
  the circle cells of `(1, 3, 5, ∞)` cover it once `n > 24` (`exists_ham_inf`).
* **`e = e_x`, `x ≠ 0`.** `P̃` is a fixed-point-free involution of the eight ends. With `X = 2x`,
  the dichotomy `shortVector_or_forall_disk` gives either a short line `(c, a)`, covered by the
  844-line table, or a sample in every certificate disk (`exists_ham_finite`).

* `exists_ham_of_agree_one` : for a prime `n ≥ 2137`, every `P` that agrees with `F_{s0}` off
  `G0 ∪ {u, F_{s0} u}` has some `P ∪ F_t` one cycle.
* `two_le_tailDist_factorTail` : `ρ(T(n)) ≥ 2` at every prime `n = 2m - 1 ≥ 2137`.
* `not_repairBound_one_of_two_one_three_seven_le` : `N_m ≥ 2`, as `¬ RepairBound m G0 1`, for
  every `m ≥ 1069` with `2m - 1` prime.

The primes `17 ≤ n < 2137` and `n = 11` are not formalized here.
-/

namespace Pairing

namespace LowerBound

open PerfectMatching RoundRobin

variable {n : ℕ}

/-- An open interval of length more than `1/n` contains a point `ν/n`
(`results/struct-lb-extend.md` §3.3, Theorem B case 2, organize-archive b5cb45e). -/
theorem exists_int_div_between {lo hi den L : ℤ} (hden : 0 < den) (hL0 : 0 < L)
    (hlen : den ≤ (hi - lo) * L) (hL : L < n) :
    ∃ ν : ℤ, (lo : ℝ) / den < (ν : ℝ) / n ∧ (ν : ℝ) / n < (hi : ℝ) / den := by
  have hn : (0 : ℤ) < n := by omega
  have hhl : 0 < hi - lo := by
    by_contra h
    push Not at h
    nlinarith
  set q := (n * lo) / den with hq
  have h1 : den * q ≤ n * lo := Int.mul_ediv_self_le (by omega)
  have h2 : n * lo < den * (q + 1) := by
    have := Int.lt_mul_ediv_self_add (x := n * lo) hden
    linarith
  have h3 : den < (hi - lo) * n := by nlinarith
  refine ⟨q + 1, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by exact_mod_cast hden) (by exact_mod_cast hn)]
    have : (lo : ℤ) * n < (q + 1) * den := by linarith
    exact_mod_cast this
  · rw [div_lt_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hden)]
    have : (q + 1) * den < (hi : ℤ) * n := by nlinarith
    exact_mod_cast this

/-- The ends `pt8` in terms of the gadget points (`results/struct-lb-extend.md` §1,
organize-archive b5cb45e). -/
theorem pt8_eq (s0 x : ZMod n) : pt8 n s0 x = ![gadgetPt n 3, gadgetPt n 4, gadgetPt n 5,
    s0 + x, gadgetPt n 2, gadgetPt n 1, gadgetPt n 0, s0 - x] := by
  funext j
  fin_cases j <;> simp [pt8, gadgetPt]

/-- The points `pt7` in terms of the gadget points (`results/struct-lb-extend.md` §1,
organize-archive b5cb45e). -/
theorem pt7_eq (s0 : ZMod n) : pt7 n s0 = ![gadgetPt n 3, gadgetPt n 4, gadgetPt n 5,
    gadgetPt n 2, gadgetPt n 1, gadgetPt n 0, s0] := by
  funext j
  fin_cases j <;> simp [pt7, gadgetPt]

/-- The eight ends are distinct (`results/struct-lb-extend.md` §1, organize-archive b5cb45e). -/
theorem pt8_injective (h11 : 11 ≤ n) {s0 x : ZMod n} (hx2 : x + x ≠ 0)
    (hxg : ∀ j, s0 + x ≠ gadgetPt n j) (hxg' : ∀ j, s0 - x ≠ gadgetPt n j) :
    Function.Injective (pt8 n s0 x) := by
  have hg := gadgetPt_injective (n := n) (by omega)
  rw [pt8_eq]
  intro a b h
  fin_cases a <;> fin_cases b <;> first
    | rfl
    | exact absurd (hg h) (by decide)
    | exact absurd h (hxg _)
    | exact absurd h.symm (hxg _)
    | exact absurd h (hxg' _)
    | exact absurd h.symm (hxg' _)
    | exact absurd (show x + x = 0 by
        have h' : s0 + x = s0 - x := h
        linear_combination h') hx2
    | exact absurd (show x + x = 0 by
        have h' : s0 - x = s0 + x := h
        linear_combination -h') hx2

/-- The seven points are distinct (`results/struct-lb-extend.md` §1, organize-archive
b5cb45e). -/
theorem pt7_injective (h11 : 11 ≤ n) {s0 : ZMod n} (hs0 : 2 * s0 = 7) :
    Function.Injective (pt7 n s0) := by
  have hg := gadgetPt_injective (n := n) (by omega)
  have hs := ne_gadgetPt_of_two_mul h11 hs0
  rw [pt7_eq]
  intro a b h
  fin_cases a <;> fin_cases b <;> first
    | rfl
    | exact absurd (hg h) (by decide)
    | exact absurd h (hs _)
    | exact absurd h.symm (hs _)

/-- `P̃ y = 2 s0 - y` wherever `P` agrees with `F_{s0}`. -/
theorem pinned_eq_of_mate_eq {hn : Odd n} {s0 y : ZMod n} {P : PerfectMatching (Option (ZMod n))}
    (h : P.mate (some y) = (factor hn s0).mate (some y)) : pinned P y = 2 * s0 - y := by
  rw [← pinned_factor hn s0 y]
  simp only [pinned, Function.Involutive.coe_toPerm, pinnedFn, h]

/-- `2x` is not the label `2k - 7` of a gadget point `k`, when `s0 + x` is not a gadget point. -/
theorem two_mul_ne_of_ne_gadgetPt (hn : Odd n) {s0 x : ZMod n} (hs0 : 2 * s0 = 7)
    (hxg : ∀ j, s0 + x ≠ gadgetPt n j) (j : Fin 6) : 2 * x ≠ 2 * gadgetPt n j - 7 := by
  intro h
  apply hxg j
  apply (isUnit_two hn).mul_left_cancel
  linear_combination h + hs0

/-- **A finite 1-core is bad** (`results/struct-lb-extend.md` §3.3, Theorem B case 2,
organize-archive b5cb45e). Let `n ≥ 2137` be prime, `x ≠ 0`, and `s0 ± x` not gadget points.
Every `P` that agrees with `F_{s0}` off `G0 ∪ {s0 + x, s0 - x}` has some `P ∪ F_t` one cycle. -/
theorem exists_ham_finite (hn : Odd n) (hp : n.Prime) (h2137 : 2137 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))} {x : ZMod n} (hx : x ≠ 0)
    (hxg : ∀ j, s0 + x ≠ gadgetPt n j) (hxg' : ∀ j, s0 - x ≠ gadgetPt n j)
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ some (s0 + x) → v ≠ some (s0 - x) →
      P.mate v = (factor hn s0).mate v) : ∃ t, Ham P (factor hn t) := by
  have h11 : 11 ≤ n := by omega
  have : NeZero n := ⟨hp.ne_zero⟩
  have : Fact n.Prime := ⟨hp⟩
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
  set X : ℤ := ((2 * x : ZMod n).val : ℤ) with hXdef
  have hX : (X : ZMod n) = 2 * x := by simp [X]
  rcases shortVector_or_forall_disk hp h2137 X with ⟨c, a, hlat, hne, hle, hgcd, hnc⟩ | hdisk
  · obtain ⟨c, a, hlat, hle, hgcd, hnc, hc1⟩ : ∃ c a : ℤ, InLattice n X c a ∧
        c ^ 2 + a ^ 2 ≤ 900 ∧ Int.gcd c a = 1 ∧ ¬(n : ℤ) ∣ c ∧ 1 ≤ c := by
      have hc0 : c ≠ 0 := fun h ↦ hnc (h ▸ dvd_zero _)
      rcases lt_or_gt_of_ne hc0 with hc | hc
      · refine ⟨-c, -a, ?_, by nlinarith, by rw [Int.gcd_neg, Int.neg_gcd]; exact hgcd,
          fun h ↦ hnc ((dvd_neg).mp h), by omega⟩
        obtain ⟨w, hw⟩ := hlat
        exact ⟨-w, by linear_combination -hw⟩
      · exact ⟨c, a, hlat, hle, hgcd, hnc, hc⟩
    have hcz : (c : ZMod n) ≠ 0 := fun h ↦ hnc ((ZMod.intCast_zmod_eq_zero_iff_dvd c n).mp h)
    have hXl : ∀ l : ℤ, a = l * c → (X : ZMod n) = l := by
      intro l hl
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hlat
      rw [hl] at h1
      push_cast at h1
      have h2 : ((l : ZMod n) - X) * c = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linear_combination -h3
      · exact absurd h3 hcz
    have hlab : ∀ (l : ℤ) (j : Fin 6), (l : ZMod n) = 2 * gadgetPt n j - 7 → a ≠ l * c := by
      intro l j hlj hl
      apply two_mul_ne_of_ne_gadgetPt hn hs0 hxg j
      rw [← hX, hXl l hl, hlj]
    have ha0 : a ≠ 0 := by
      intro h
      have := hXl 0 (by rw [h, zero_mul])
      rw [hX, Int.cast_zero] at this
      exact hx2 (by linear_combination this)
    have hadm : admB c a = true := by
      have e1 := hlab 1 3 (by simp [gadgetPt]; norm_num)
      have e2 := hlab (-1) 2 (by simp [gadgetPt]; norm_num)
      have e3 := hlab 3 4 (by simp [gadgetPt]; norm_num)
      have e4 := hlab (-3) 1 (by simp [gadgetPt]; norm_num)
      have e5 := hlab 5 5 (by simp [gadgetPt]; norm_num)
      have e6 := hlab (-5) 0 (by simp [gadgetPt]; norm_num)
      simp only [admB, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨hc1, ha0⟩, hgcd⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact fun h ↦ e1 (by rw [h, one_mul])
      · exact fun h ↦ e2 (by rw [h]; ring)
      · exact e3
      · exact fun h ↦ e4 (by rw [h]; ring)
      · exact e5
      · exact fun h ↦ e6 (by rw [h]; ring)
    obtain ⟨o, oi, k, lo, hi, den, hoi, hcov, hwit, hlen⟩ := lineGood_of_le_900 hadm hle r hr1 hr2
    have hden : 0 < den := by
      simp only [lineWitOK, Bool.and_eq_true, decide_eq_true_eq] at hwit
      exact hwit.1.1
    obtain ⟨ν, hν1, hν2⟩ := exists_int_div_between (n := n) hden (by norm_num) hlen (by omega)
    have hcell := lineWitOK_spec hwit hν1 hν2
    refine ham_of_realCell8 hn hp hs0 hP8 hr' hX hoi (k := k) (μ' := c * ν) (a' := a * ν) ?_ ?_
      hcov
    · obtain ⟨w, hw⟩ := hlat
      exact ⟨w * ν, by linear_combination ν * hw⟩
    · convert hcell using 2 <;> push_cast <;> ring
  · obtain ⟨o, oi, k, u, w, hoi, hcov, hcellD⟩ := exists_cert8 hr1 hr2
    obtain ⟨c', a', hlat, hd⟩ := hdisk u w
    exact ham_of_realCell8 hn hp hs0 hP8 hr' hX hoi hlat (hcellD _ _ hd) hcov

/-- **The core `{e_∞}` is bad** (`results/struct-lb-extend.md` §3.3, Theorem B case 1, and
`results/struct-lb-contra.md` §3.1, Lemma 2a, organize-archive b5cb45e). For a prime `n ≥ 25`,
every `P` that agrees with `F_{s0}` off `G0 ∪ {∞, s0}` has some `P ∪ F_t` one cycle. -/
theorem exists_ham_inf (hn : Odd n) (hp : n.Prime) (h25 : 25 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ none → v ≠ some s0 →
      P.mate v = (factor hn s0).mate v) : ∃ t, Ham P (factor hn t) := by
  have h11 : 11 ≤ n := by omega
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
  obtain ⟨o, oi, k, lo, hi, den, hoi, hcov, hwit, hlen⟩ := exists_cell7 hr1 hr2
  have hden : 0 < den := by
    simp only [cellWitOK7, Bool.and_eq_true, decide_eq_true_eq] at hwit
    exact hwit.1.1
  obtain ⟨ν, hν1, hν2⟩ := exists_int_div_between (n := n) hden (by norm_num) hlen (by omega)
  exact ham_of_realCell7 hn hp hs0 hP7 hr hoi (cellWitOK7_spec hwit hν1 hν2) hcov

/-- **Theorem B of `results/struct-lb-extend.md`, in walk form, for `n ≥ 2137`**
(organize-archive b5cb45e). For a prime `n ≥ 2137`, with `2 s0 = 7`, let `u` be a vertex off the
gadget `G0`. Every perfect matching `P` that agrees with `F_{s0}` off `G0 ∪ {u, F_{s0} u}` has
some round-robin factor `F_t` with `P ∪ F_t` one cycle. -/
theorem exists_ham_of_agree_one (hn : Odd n) (hp : n.Prime) (h2137 : 2137 ≤ n) {s0 : ZMod n}
    (hs0 : 2 * s0 = 7) {P : PerfectMatching (Option (ZMod n))} {u : Option (ZMod n)}
    (hu : ∀ j, u ≠ some (gadgetPt n j))
    (hP : ∀ v, (∀ j, v ≠ some (gadgetPt n j)) → v ≠ u → v ≠ (factor hn s0).mate u →
      P.mate v = (factor hn s0).mate v) : ∃ t, Ham P (factor hn t) := by
  rcases u with _ | y
  · rw [factor_mate, mateFn_none] at hP
    exact exists_ham_inf hn hp (by omega) hs0 hP
  · by_cases hys : y = s0
    · subst hys
      rw [factor_mate, mateFn_self] at hP
      exact exists_ham_inf hn hp (by omega) hs0 fun v hv h1 h2 ↦ hP v hv h2 h1
    · rw [factor_mate, mateFn_of_ne _ _ hys] at hP
      refine exists_ham_finite hn hp h2137 hs0 (x := y - s0) (fun h ↦ hys (by
        linear_combination h)) (fun j h ↦ hu j (by rw [← h]; ring_nf)) (fun j h ↦ ?_)
        (fun v hv h1 h2 ↦ hP v hv (by rw [show s0 + (y - s0) = y by ring] at h1; exact h1)
          (by rw [show s0 - (y - s0) = 2 * s0 - y by ring] at h2; exact h2))
      apply hu (Fin.rev j)
      rw [gadgetPt_rev, ← h, ← hs0]
      ring_nf

end LowerBound

namespace RoundRobin.Canonical

open PerfectMatching LowerBound

variable {m : ℕ} [NeZero m]

/-- **`ρ(T(n)) ≥ 2` at every prime `n = 2m - 1 ≥ 2137`** (`results/struct-lb-extend.md`
Theorem B, organize-archive b5cb45e). Every zero state differs from the factor tail `T(n)` in at
least two edges. -/
theorem two_le_tailDist_factorTail (hm : 6 ≤ m) (hp : (2 * m - 1).Prime)
    (h2137 : 2137 ≤ 2 * m - 1) (P : ZeroState m) :
    2 ≤ tailDist P.1 (FactorCap.factorTail m (by omega)) := by
  by_contra h0
  set T := FactorCap.factorTail m (by omega)
  have h2 := two_mul_tailDist P.1 T
  set D := Finset.univ.filter fun u : ((FactorCap.gadget m)ᶜ : Finset (Vertex m)) ↦
    (T.mate u : Vertex m) ≠ P.1.mate u with hD
  have hcard : D.card ≤ 2 := by omega
  have hmem : ∀ u, u ∈ D ↔ (T.mate u : Vertex m) ≠ P.1.mate u := by
    intro u
    simp [hD]
  obtain ⟨u, hu, hagree⟩ : ∃ u : Vertex m, u ∉ FactorCap.gadget m ∧ ∀ v, v ∉ FactorCap.gadget m →
      v ≠ u → v ≠ (factor m (FactorCap.capCenter m)).mate u →
        P.1.mate v = (factor m (FactorCap.capCenter m)).mate v := by
    by_cases hne : D.Nonempty
    · obtain ⟨w, hw⟩ := hne
      refine ⟨w, Finset.mem_compl.mp w.2, fun v hv hvw hvm ↦ ?_⟩
      by_contra hcon
      set v' : ((FactorCap.gadget m)ᶜ : Finset (Vertex m)) := ⟨v, Finset.mem_compl.mpr hv⟩
      have hv' : v' ∈ D := by
        rw [hmem, FactorCap.factorTail_mate]
        exact Ne.symm hcon
      have hw' : T.mate w ∈ D := by
        rw [hmem, mate_mate]
        intro h
        apply (hmem w).mp hw
        rw [h, mate_mate]
      have h3 : 2 < D.card := by
        rw [Finset.two_lt_card]
        refine ⟨w, hw, T.mate w, hw', v', hv', fun h ↦ T.mate_ne w h.symm, fun h ↦ hvw ?_,
          fun h ↦ hvm ?_⟩
        · exact (congrArg Subtype.val h).symm
        · rw [← FactorCap.factorTail_mate]
          exact (congrArg Subtype.val h).symm
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨none, fun h ↦ ?_, fun v hv _ _ ↦ ?_⟩
      · obtain ⟨j, hj⟩ := (mem_gadget_iff none).mp h
        simp at hj
      · have h1 : (⟨v, Finset.mem_compl.mpr hv⟩ :
            ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) ∉ D := by
          rw [hne]
          exact Finset.notMem_empty _
        rw [hmem, not_not, FactorCap.factorTail_mate] at h1
        exact h1.symm
  have hng : ∀ v : Vertex m, (∀ j, v ≠ some (gadgetPt (2 * m - 1) j)) → v ∉ FactorCap.gadget m :=
    fun v hv h ↦ by
      obtain ⟨j, hj⟩ := (mem_gadget_iff v).mp h
      exact hv j hj
  obtain ⟨t, ht⟩ := exists_ham_of_agree_one (modulus_odd m) hp h2137
    FactorCap.two_mul_capCenter (u := u) (fun j h ↦ hu ((mem_gadget_iff u).mpr ⟨j, h⟩))
    (fun v hv h1 h2 ↦ hagree v (hng v hv) h1 h2)
  exact P.2 t ht

/-- **`N_m ≥ 2` for every `m ≥ 1069` with `2m - 1` prime** (`results/struct-lb-extend.md`
Theorem B, the `n`-uniform range `n ≥ 2137`, organize-archive b5cb45e). No zero state lies within
distance `1` of the factor tail `T(n)`, so `RepairBound m G0 1` fails. -/
theorem not_repairBound_one_of_two_one_three_seven_le (hm : 1069 ≤ m) (hp : (2 * m - 1).Prime) :
    ¬RepairBound m (FactorCap.gadget m) 1 := by
  intro h
  obtain ⟨P, hP⟩ := h (FactorCap.factorTail m (by omega))
  have := two_le_tailDist_factorTail (by omega) hp (by omega) P
  omega

end RoundRobin.Canonical

end Pairing
