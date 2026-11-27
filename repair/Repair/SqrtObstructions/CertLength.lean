import Repair.Automorphism
import Repair.SqrtObstructions.Defect

/-!
# NG-B(b), Theorem C′: certificate length on factor tails

Source: `results/factor-tail-L-test.md`, Theorem C′, with the walk lemma of
`results/cod-149-core-sharpening.md` (Theorem C), as used in `results/sqrt-m-obstructions.md`
§1.3, Theorem NG-B(b). Put `n = 2m - 1`, prime, and fix the factor `F_s` of the tail.

For a perfect matching `P` of `V_m` and a factor `t`, the cycles of `P ∪ F_t` are the orbits of
`σ_t = P F_t` (`certPerm`). The orbit of `y` has length `r` exactly when the cycle through `y` has
`r` edges of `P`. So "`P ∪ F_t` has a cycle with at most `L` edges of `P`" reads
`∃ y, ∃ r ∈ [1, L], σ_t^r y = y`. The defect `X = defect F_s P` is the vertex set of `P ∖ F_s`,
and `|X| = 2k` with `k = |P ∖ F_s|` (`two_mul_card_edgesOutside`).

* `walkEnd s t y i = E_t(y, i)`, the end of the walk `y, F_t, F_s, …` after `2i + 1` steps.
* `card_walkHit_le` (the walk lemma, prefix form) : for `L ≤ m - 1`, at most
  `L |X| + 2L - 1` factors `t ≠ s` have `E_t(y, i) ∈ X` for some `i < L`.
* `exists_walkEnd_mem_of_agree` : the walk step, for any `X` on which `P` agrees with `F_s` along
  the cycle. `exists_walkEnd_mem` : a cycle of `P ∪ F_t` through `y ∈ X` with `r` edges of `P`
  gives `E_t(y, i) ∈ X` for some `i < r`.
* `certLength_bound` (Theorem C′) : if every `t ≠ s` has such a cycle through `X` with at most `L`
  edges of `P`, then `n - 1 ≤ |X| (|X| L + 2L - 1)`, and `certLength_bound_edges` :
  `n - 1 ≤ 2k((2k + 2)L - 1)`.
* `certLength_bound_of_isZeroState` : for a zero state the condition "through `X`" is automatic,
  since `F_s ∪ F_t` is one cycle (`ham_factor_of_ne`).
* `factorTail_certLength` : a zero state within `d` of the factor tail `T(n)` has `k ≤ d + 3`, so
  `n - 1 ≤ 2(d + 3)((2(d + 3) + 2)L - 1)`. `factorTail_certLength_five` : cost at most `5` forces
  `n + 15 ≤ 288 L`, that is `L(P) ≥ (n + 15)/288`.

The source states Theorem C′ for `L ≤ m - 1`. `certLength_bound` holds for every `L`.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `P` outside `Q`, `P ∖ Q`, read off at the defect (`factor-tail-L-test.md`,
Theorem C′). -/
def edgesOutside (Q P : PerfectMatching V) : Finset (Sym2 V) :=
  (defect Q P).image fun w ↦ s(w, P.mate w)

/-- `|defect Q P| = 2 |P ∖ Q|` (`factor-tail-L-test.md`, Theorem C′, `|X| = 2k`). -/
theorem two_mul_card_edgesOutside (Q P : PerfectMatching V) :
    2 * (edgesOutside Q P).card = (defect Q P).card :=
  two_mul_card_image_mate P (defect Q P) fun _ hw ↦ mate_mem_defect Q P hw

/-- The members of `edgesOutside Q P` are the edges of `P` that are not edges of `Q`
(`factor-tail-L-test.md`, Theorem C′). -/
theorem mem_edgesOutside {Q P : PerfectMatching V} {e : Sym2 V} :
    e ∈ edgesOutside Q P ↔ e ∈ P.toGraph.edgeSet ∧ e ∉ Q.toGraph.edgeSet := by
  induction e using Sym2.ind with
  | h v w =>
  simp only [edgesOutside, Finset.mem_image, SimpleGraph.mem_edgeSet, toGraph_adj]
  constructor
  · rintro ⟨u, hu, he⟩
    have hu' := mem_defect.mp hu
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, fun h ↦ hu' h.symm⟩
    · refine ⟨P.mate_mate u, fun h ↦ hu' ?_⟩
      have h' := congrArg Q.mate h
      rw [mate_mate] at h'
      exact h'
  · rintro ⟨hP, hQ⟩
    exact ⟨v, mem_defect.mpr fun h ↦ hQ (h ▸ hP), by rw [hP]⟩

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `F_t` pairs `∞` with `t`. -/
theorem factor_mate_none' (t : ZMod (2 * m - 1)) : (factor m t).mate none = some t := by
  rw [factor, factor_mate, mateFn_none]

/-- `F_t` pairs `x ≠ t` with `2t - x`. -/
theorem factor_mate_some_of_ne {t x : ZMod (2 * m - 1)} (h : x ≠ t) :
    (factor m t).mate (some x) = some (2 * t - x) := by
  rw [factor, factor_mate, mateFn_of_ne t x h]

omit [NeZero m] in
/-- A natural `0 < k < 2m - 1` is nonzero in `ℤ/(2m - 1)`. -/
theorem natCast_ne_zero_of_lt {k : ℕ} (hk : 0 < k) (hk' : k < 2 * m - 1) :
    (k : ZMod (2 * m - 1)) ≠ 0 := by
  simpa using natCast_ne hk' (by omega : 0 < 2 * m - 1) (by omega : k ≠ 0)

/-- At prime `n`, `F_s ∪ F_t` is one cycle for `s ≠ t` (the gcd law of
`cod-149-core-sharpening.md`, Theorem B(i), at prime `n`). For composite `n` see
`ham_factor_of_isUnit_sub`. -/
theorem ham_factor_of_ne (hp : (2 * m - 1).Prime) {s t : ZMod (2 * m - 1)} (h : s ≠ t) :
    Ham (factor m s) (factor m t) := by
  have := Fact.mk hp
  exact ham_factor_of_isUnit_sub m (sub_ne_zero.mpr h).isUnit

/-- `σ_t = P F_t`. Its orbits are the cycles of `P ∪ F_t`, and an orbit of length `r` is a cycle
with `r` edges of `P` (`factor-tail-L-test.md`, Theorem C′). -/
def certPerm (P : PerfectMatching (Vertex m)) (t : ZMod (2 * m - 1)) : Equiv.Perm (Vertex m) :=
  P.mate * (factor m t).mate

/-- `τ = F_s F_t`, two steps of the walk of the walk lemma (`cod-149-core-sharpening.md`,
Theorem C). -/
def walkPerm (s t : ZMod (2 * m - 1)) : Equiv.Perm (Vertex m) :=
  (factor m s).mate * (factor m t).mate

/-- `E_t(y, i) = F_t((F_s F_t)^i y)`, the end of the walk `y, F_t, F_s, …` after `2i + 1` steps
(`cod-149-core-sharpening.md`, walk lemma). -/
def walkEnd (s t : ZMod (2 * m - 1)) (y : Vertex m) (i : ℕ) : Vertex m :=
  (factor m t).mate ((walkPerm s t ^ i) y)

/-- The regular formula of the walk from a finite start `a` (`cod-149-core-sharpening.md`, walk
lemma): `v_{2l} = a + 2l(s - t)` while no step is exceptional. -/
theorem walkPerm_pow_some {s t a : ZMod (2 * m - 1)} {L : ℕ}
    (h1 : ∀ j < L, a + 2 * (j : ZMod (2 * m - 1)) * (s - t) ≠ t)
    (h2 : ∀ j, j + 1 < L → 2 * ((j : ZMod (2 * m - 1)) + 1) * t - 2 * j * s - a ≠ s) :
    ∀ l < L, (walkPerm s t ^ l) (some a) = some (a + 2 * (l : ZMod (2 * m - 1)) * (s - t)) := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
    intro hl
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), walkPerm, Equiv.Perm.mul_apply,
      factor_mate_some_of_ne (h1 l (by omega))]
    have h3 : 2 * t - (a + 2 * (l : ZMod (2 * m - 1)) * (s - t)) ≠ s := by
      intro h
      exact h2 l hl (by linear_combination h)
    rw [factor_mate_some_of_ne h3, Option.some_inj]
    push_cast
    ring

/-- `E_t(a, i) = 2(i + 1)t - 2is - a` for a regular `t` (`cod-149-core-sharpening.md`, walk
lemma). -/
theorem walkEnd_some {s t a : ZMod (2 * m - 1)} {L : ℕ}
    (h1 : ∀ j < L, a + 2 * (j : ZMod (2 * m - 1)) * (s - t) ≠ t)
    (h2 : ∀ j, j + 1 < L → 2 * ((j : ZMod (2 * m - 1)) + 1) * t - 2 * j * s - a ≠ s)
    {i : ℕ} (hi : i < L) :
    walkEnd s t (some a) i =
      some (2 * ((i : ZMod (2 * m - 1)) + 1) * t + (-(2 * (i : ZMod (2 * m - 1)) * s) - a)) := by
  rw [walkEnd, walkPerm_pow_some h1 h2 i hi, factor_mate_some_of_ne (h1 i hi), Option.some_inj]
  ring

/-- The walk from `∞` (`cod-149-core-sharpening.md`, walk lemma): for `t ≠ s` at prime `n`,
`v_{2l} = t + 2l(s - t)` for `1 ≤ l < L ≤ m - 1`. -/
theorem walkPerm_pow_none (hp : (2 * m - 1).Prime) {s t : ZMod (2 * m - 1)} (hts : t ≠ s)
    {L : ℕ} (hL : L ≤ m - 1) :
    ∀ l, l + 1 < L → (walkPerm s t ^ (l + 1)) none =
      some (t + 2 * ((l : ZMod (2 * m - 1)) + 1) * (s - t)) := by
  have := Fact.mk hp
  have hst : s - t ≠ 0 := sub_ne_zero.mpr hts.symm
  intro l
  induction l with
  | zero =>
    intro _
    rw [zero_add, pow_one, walkPerm, Equiv.Perm.mul_apply, factor_mate_none',
      factor_mate_some_of_ne hts, Option.some_inj]
    push_cast
    ring
  | succ l ih =>
    intro hl
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), walkPerm, Equiv.Perm.mul_apply]
    have hc1 := natCast_ne_zero_of_lt (m := m) (k := 2 * l + 2) (by omega) (by omega)
    have hc2 := natCast_ne_zero_of_lt (m := m) (k := 2 * l + 3) (by omega) (by omega)
    push_cast at hc1 hc2
    have h3 : t + 2 * ((l : ZMod (2 * m - 1)) + 1) * (s - t) ≠ t := by
      intro h
      exact mul_ne_zero hc1 hst (by linear_combination h)
    have h4 : 2 * t - (t + 2 * ((l : ZMod (2 * m - 1)) + 1) * (s - t)) ≠ s := by
      intro h
      exact mul_ne_zero hc2 hst (by linear_combination -h)
    rw [factor_mate_some_of_ne h3, factor_mate_some_of_ne h4, Option.some_inj]
    push_cast
    ring

/-- `E_t(∞, i) = (2i + 1)t - 2is` for `t ≠ s` at prime `n` (`cod-149-core-sharpening.md`, walk
lemma). -/
theorem walkEnd_none (hp : (2 * m - 1).Prime) {s t : ZMod (2 * m - 1)} (hts : t ≠ s) {L : ℕ}
    (hL : L ≤ m - 1) {i : ℕ} (hi : i < L) :
    walkEnd s t none i =
      some ((2 * (i : ZMod (2 * m - 1)) + 1) * t + -(2 * (i : ZMod (2 * m - 1)) * s)) := by
  have := Fact.mk hp
  have hst : s - t ≠ 0 := sub_ne_zero.mpr hts.symm
  rcases i with _ | j
  · rw [walkEnd, pow_zero, Equiv.Perm.one_apply, factor_mate_none', Option.some_inj]
    push_cast
    ring
  · rw [walkEnd, walkPerm_pow_none hp hts hL j hi]
    have hc1 := natCast_ne_zero_of_lt (m := m) (k := 2 * j + 2) (by omega) (by omega)
    push_cast at hc1
    have h3 : t + 2 * ((j : ZMod (2 * m - 1)) + 1) * (s - t) ≠ t := by
      intro h
      exact mul_ne_zero hc1 hst (by linear_combination h)
    rw [factor_mate_some_of_ne h3, Option.some_inj]
    push_cast
    ring

/-- Counting regular hits (`cod-149-core-sharpening.md`, walk lemma). If off a set `Irr` the
walk end is the affine map `t ↦ c_i t + d_i` with `c_i ≠ 0`, then at most `L |X| + |Irr|`
factors `t ≠ s` hit `X` within `L` steps. -/
theorem card_hit_le (hp : (2 * m - 1).Prime) (s : ZMod (2 * m - 1))
    (E : ZMod (2 * m - 1) → ℕ → Vertex m) (X : Finset (Vertex m)) (L : ℕ)
    (Irr : Finset (ZMod (2 * m - 1))) (c d : ℕ → ZMod (2 * m - 1)) (hc : ∀ i < L, c i ≠ 0)
    (hE : ∀ t, t ≠ s → t ∉ Irr → ∀ i < L, E t i = some (c i * t + d i)) :
    (Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, E t i ∈ X).card ≤ L * X.card + Irr.card := by
  have := Fact.mk hp
  calc (Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, E t i ∈ X).card
      ≤ (Irr ∪ (Finset.range L).biUnion fun i ↦
          Finset.univ.filter fun t ↦ some (c i * t + d i) ∈ X).card := by
        refine Finset.card_le_card fun t ht ↦ ?_
        obtain ⟨hts, i, hi, hX⟩ := (Finset.mem_filter.mp ht).2
        by_cases hI : t ∈ Irr
        · exact Finset.mem_union_left _ hI
        · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩)
          rw [hE t hts hI i hi] at hX
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
    _ ≤ Irr.card + ∑ i ∈ Finset.range L,
          (Finset.univ.filter fun t ↦ some (c i * t + d i) ∈ X).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    _ ≤ Irr.card + ∑ _i ∈ Finset.range L, X.card := by
        refine Nat.add_le_add_left (Finset.sum_le_sum fun i hi ↦ ?_) _
        refine Finset.card_le_card_of_injOn (fun t ↦ some (c i * t + d i)) (fun t ht ↦ ?_)
          (fun t _ t' _ h ↦ ?_)
        · exact (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
        · have h' : c i * t + d i = c i * t' + d i := Option.some_inj.mp h
          exact mul_left_cancel₀ (hc i (Finset.mem_range.mp hi)) (add_right_cancel h')
    _ = L * X.card + Irr.card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, add_comm]

/-- **The walk lemma, prefix form** (`factor-tail-L-test.md`, proof of Theorem C′, refining the
walk lemma of `cod-149-core-sharpening.md`). At prime `n = 2m - 1` and for `L ≤ m - 1`, at most
`L |X| + 2L - 1` factors `t ≠ s` have `E_t(y, i) ∈ X` for some `i < L`. -/
theorem card_walkHit_le (hp : (2 * m - 1).Prime) (s : ZMod (2 * m - 1)) (y : Vertex m)
    (X : Finset (Vertex m)) {L : ℕ} (hL : L ≤ m - 1) :
    (Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, walkEnd s t y i ∈ X).card ≤
      L * X.card + (2 * L - 1) := by
  have := Fact.mk hp
  rcases y with _ | a
  · refine (card_hit_le hp s (fun t i ↦ walkEnd s t none i) X L ∅
      (fun i ↦ 2 * (i : ZMod (2 * m - 1)) + 1) (fun i ↦ -(2 * (i : ZMod (2 * m - 1)) * s))
      (fun i hi ↦ ?_) (fun t hts _ i hi ↦ walkEnd_none hp hts hL hi)).trans (by simp)
    have := natCast_ne_zero_of_lt (m := m) (k := 2 * i + 1) (by omega) (by omega)
    push_cast at this
    exact this
  · set Irr : Finset (ZMod (2 * m - 1)) :=
      (Finset.range L).image (fun j : ℕ ↦ (a + 2 * (j : ZMod (2 * m - 1)) * s) /
          (2 * (j : ZMod (2 * m - 1)) + 1)) ∪
        (Finset.range (L - 1)).image (fun j : ℕ ↦
          ((2 * (j : ZMod (2 * m - 1)) + 1) * s + a) / (2 * ((j : ZMod (2 * m - 1)) + 1)))
      with hIrr
    have hcard : Irr.card ≤ 2 * L - 1 := by
      refine (Finset.card_union_le _ _).trans ?_
      have e1 := (Finset.card_image_le (s := Finset.range L) (f := fun j : ℕ ↦
        (a + 2 * (j : ZMod (2 * m - 1)) * s) / (2 * (j : ZMod (2 * m - 1)) + 1)))
      have e2 := (Finset.card_image_le (s := Finset.range (L - 1)) (f := fun j : ℕ ↦
        ((2 * (j : ZMod (2 * m - 1)) + 1) * s + a) / (2 * ((j : ZMod (2 * m - 1)) + 1))))
      rw [Finset.card_range] at e1 e2
      omega
    refine (card_hit_le hp s (fun t i ↦ walkEnd s t (some a) i) X L Irr
      (fun i ↦ 2 * ((i : ZMod (2 * m - 1)) + 1)) (fun i ↦ -(2 * (i : ZMod (2 * m - 1)) * s) - a)
      (fun i hi ↦ ?_) (fun t _ hI i hi ↦ walkEnd_some ?_ ?_ hi)).trans
      (Nat.add_le_add_left hcard _)
    · have := natCast_ne_zero_of_lt (m := m) (k := 2 * i + 2) (by omega) (by omega)
      push_cast at this
      intro h0
      exact this (by linear_combination h0)
    · intro j hj h
      have hc := natCast_ne_zero_of_lt (m := m) (k := 2 * j + 1) (by omega) (by omega)
      push_cast at hc
      refine hI (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩))
      rw [div_eq_iff hc]
      linear_combination h
    · intro j hj h
      have hc := natCast_ne_zero_of_lt (m := m) (k := 2 * j + 2) (by omega) (by omega)
      push_cast at hc
      have hc' : 2 * ((j : ZMod (2 * m - 1)) + 1) ≠ 0 := by
        intro h0
        exact hc (by linear_combination h0)
      refine hI (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr (by omega), ?_⟩))
      rw [div_eq_iff hc']
      linear_combination -h

/-- **The walk step of Theorem C′** (`factor-tail-L-test.md`, proof of Theorem C′; the proof of
Theorem C in `cod-149-core-sharpening.md`). Let `σ_t^r y = y` with `r ≥ 1` and `P y ∈ X`, and
suppose `P` agrees with `F_s` at every point `F_t(σ_t^j y)`, `j < r`, outside `X`. Then
`E_t(y, i) ∈ X` for some `i < r`. -/
theorem exists_walkEnd_mem_of_agree (P : PerfectMatching (Vertex m)) (s t : ZMod (2 * m - 1))
    (X : Finset (Vertex m)) {y : Vertex m} (hyP : P.mate y ∈ X) {r : ℕ} (hr : 1 ≤ r)
    (hcyc : (certPerm P t ^ r) y = y)
    (hagree : ∀ j < r, (factor m t).mate ((certPerm P t ^ j) y) ∉ X →
      P.mate ((factor m t).mate ((certPerm P t ^ j) y)) =
        (factor m s).mate ((factor m t).mate ((certPerm P t ^ j) y))) :
    ∃ i < r, walkEnd s t y i ∈ X := by
  have hlast : (factor m t).mate ((certPerm P t ^ (r - 1)) y) ∈ X := by
    have h : P.mate ((factor m t).mate ((certPerm P t ^ (r - 1)) y)) = y :=
      calc P.mate ((factor m t).mate ((certPerm P t ^ (r - 1)) y))
          = certPerm P t ((certPerm P t ^ (r - 1)) y) := rfl
        _ = (certPerm P t ^ r) y := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hr]
        _ = y := hcyc
    have h' : (factor m t).mate ((certPerm P t ^ (r - 1)) y) = P.mate y := by
      have h'' := congrArg P.mate h
      rwa [mate_mate] at h''
    rw [h']
    exact hyP
  have hex : ∃ i, i < r ∧ (factor m t).mate ((certPerm P t ^ i) y) ∈ X :=
    ⟨r - 1, by omega, hlast⟩
  obtain ⟨hlt, hmem⟩ := Nat.find_spec hex
  have hsame : ∀ j ≤ Nat.find hex, (certPerm P t ^ j) y = (walkPerm s t ^ j) y := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hnot := Nat.find_min hex (show j < Nat.find hex by omega)
      have hj' : (factor m t).mate ((certPerm P t ^ j) y) ∉ X := fun h ↦ hnot ⟨by omega, h⟩
      have hPs := hagree j (by omega) hj'
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ih (by omega)]
      exact hPs
  exact ⟨Nat.find hex, hlt, by rw [walkEnd, ← hsame _ le_rfl]; exact hmem⟩

/-- A certificate cycle reaches the defect along the walk (`factor-tail-L-test.md`, proof of
Theorem C′). If `y ∈ X = defect F_s P` and `σ_t^r y = y` with `r ≥ 1`, then `E_t(y, i) ∈ X` for
some `i < r`. -/
theorem exists_walkEnd_mem (P : PerfectMatching (Vertex m)) (s t : ZMod (2 * m - 1))
    {y : Vertex m} (hy : y ∈ defect (factor m s) P) {r : ℕ} (hr : 1 ≤ r)
    (hcyc : (certPerm P t ^ r) y = y) : ∃ i < r, walkEnd s t y i ∈ defect (factor m s) P :=
  exists_walkEnd_mem_of_agree P s t _ (mate_mem_defect _ P hy) hr hcyc fun _ _ hj ↦ by
    rwa [mem_defect, not_not] at hj

/-- **Theorem C′** (`factor-tail-L-test.md`; NG-B(b) of `sqrt-m-obstructions.md` §1.3), defect
form. Let `n = 2m - 1` be prime, `P` a perfect matching of `V_m` and `X = defect F_s P`. If every
`t ≠ s` has a cycle of `P ∪ F_t` through `X` with at most `L` edges of `P`, then
`n - 1 ≤ |X| (|X| L + 2L - 1)`. -/
theorem certLength_bound (hp : (2 * m - 1).Prime) (P : PerfectMatching (Vertex m))
    (s : ZMod (2 * m - 1)) {L : ℕ}
    (hcert : ∀ t ≠ s, ∃ y ∈ defect (factor m s) P, ∃ r, 1 ≤ r ∧ r ≤ L ∧
      (certPerm P t ^ r) y = y) :
    2 * m - 2 ≤
      (defect (factor m s) P).card * ((defect (factor m s) P).card * L + 2 * L - 1) := by
  set X := defect (factor m s) P with hX
  have hcardne : (Finset.univ.filter fun t : ZMod (2 * m - 1) ↦ t ≠ s).card = 2 * m - 2 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
    omega
  by_cases hL : L ≤ m - 1
  · rw [← hcardne]
    calc (Finset.univ.filter fun t : ZMod (2 * m - 1) ↦ t ≠ s).card
        ≤ (X.biUnion fun y ↦
            Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, walkEnd s t y i ∈ X).card := by
          refine Finset.card_le_card fun t ht ↦ ?_
          have hts := (Finset.mem_filter.mp ht).2
          obtain ⟨y, hy, r, hr1, hrL, hcyc⟩ := hcert t hts
          obtain ⟨i, hi, hiX⟩ := exists_walkEnd_mem P s t hy hr1 hcyc
          exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hts, i, by omega, hiX⟩⟩
      _ ≤ ∑ y ∈ X, (Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, walkEnd s t y i ∈ X).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ X, (L * X.card + (2 * L - 1)) :=
          Finset.sum_le_sum fun y _ ↦ card_walkHit_le hp s y X hL
      _ = X.card * (L * X.card + (2 * L - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ X.card * (X.card * L + 2 * L - 1) := by
          refine Nat.mul_le_mul_left _ ?_
          rcases Nat.eq_zero_or_pos L with rfl | hLpos
          · simp
          · rw [mul_comm L]
            generalize X.card * L = q
            omega
  · rcases X.eq_empty_or_nonempty with hXe | hXne
    · have hm : m = 1 := by
        by_contra hm
        have hm2 : 2 ≤ m := by have := NeZero.pos m; omega
        obtain ⟨y, hy, -⟩ := hcert (s + 1) (by
          intro h
          have h1 : ((1 : ℕ) : ZMod (2 * m - 1)) = 0 := by
            have : s + 1 - s = s - s := by rw [h]
            simpa using this
          exact natCast_ne_zero_of_lt (m := m) (k := 1) (by omega) (by omega) h1)
        rw [hXe] at hy
        exact Finset.notMem_empty _ hy
      subst hm
      omega
    · have hpos := hXne.card_pos
      have h1 : L ≤ X.card * L := Nat.le_mul_of_pos_left L hpos
      have h2 : X.card * L + 2 * L - 1 ≤ X.card * (X.card * L + 2 * L - 1) :=
        Nat.le_mul_of_pos_left _ hpos
      generalize X.card * (X.card * L + 2 * L - 1) = q at h2 ⊢
      generalize X.card * L = q' at h1 h2
      omega

/-- **Theorem C′** (`factor-tail-L-test.md`; NG-B(b) of `sqrt-m-obstructions.md` §1.3), edge
form. With `k = |P ∖ F_s|`, if every `t ≠ s` has a cycle of `P ∪ F_t` through `V(P ∖ F_s)` with
at most `L` edges of `P`, then `n - 1 ≤ 2k((2k + 2)L - 1)`. -/
theorem certLength_bound_edges (hp : (2 * m - 1).Prime) (P : PerfectMatching (Vertex m))
    (s : ZMod (2 * m - 1)) {L : ℕ}
    (hcert : ∀ t ≠ s, ∃ y ∈ defect (factor m s) P, ∃ r, 1 ≤ r ∧ r ≤ L ∧
      (certPerm P t ^ r) y = y) :
    2 * m - 2 ≤ 2 * (edgesOutside (factor m s) P).card *
      ((2 * (edgesOutside (factor m s) P).card + 2) * L - 1) := by
  have h := certLength_bound hp P s hcert
  rw [← two_mul_card_edgesOutside] at h
  rwa [add_mul]

/-- For a zero state every cycle of `P ∪ F_t`, `t ≠ s`, meets the defect `X = defect F_s P`
(`factor-tail-L-test.md`, proof of Theorem C′, by Theorem B(i) of
`cod-149-core-sharpening.md`). So a cycle with `r` edges of `P` gives one through `X`. -/
theorem exists_defect_of_cycle (hp : (2 * m - 1).Prime) {P : PerfectMatching (Vertex m)}
    (hP : IsZeroState (factor m) P) {s t : ZMod (2 * m - 1)} (hts : t ≠ s) {y : Vertex m}
    {r : ℕ} (hcyc : (certPerm P t ^ r) y = y) :
    ∃ y' ∈ defect (factor m s) P, (certPerm P t ^ r) y' = y' := by
  set σ := certPerm P t with hσ
  have hσapp : ∀ v, σ v = P.mate ((factor m t).mate v) := fun _ ↦ rfl
  have hfix : ∀ v, σ.SameCycle y v → (σ ^ r) v = v := by
    rintro v ⟨i, rfl⟩
    rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add, add_comm (r : ℤ) i, zpow_add,
      Equiv.Perm.mul_apply, zpow_natCast, hcyc]
  set B : Set (Vertex m) := {v | σ.SameCycle y v ∨ σ.SameCycle y ((factor m t).mate v)} with hB
  by_contra hno
  push Not at hno
  have hout : ∀ v ∈ B, v ∉ defect (factor m s) P := by
    rintro v (hv | hv) hX
    · exact hno v hX (hfix v hv)
    · refine hno (P.mate v) (mate_mem_defect _ P hX) (hfix _ ?_)
      have h : P.mate v = σ ((factor m t).mate v) := by rw [hσapp, mate_mate]
      rw [h, Equiv.Perm.sameCycle_apply_right]
      exact hv
  have hBt : ∀ v ∈ B, (factor m t).mate v ∈ B := by
    rintro v (hv | hv)
    · exact Or.inr (by rwa [mate_mate])
    · exact Or.inl hv
  have hBP : ∀ v ∈ B, P.mate v ∈ B := by
    rintro v (hv | hv)
    · refine Or.inr ?_
      have h : (factor m t).mate (P.mate v) = σ.symm v := by
        rw [Equiv.eq_symm_apply, hσapp, mate_mate, mate_mate]
      rw [h, Equiv.Perm.sameCycle_symm_apply_right]
      exact hv
    · refine Or.inl ?_
      have h : P.mate v = σ ((factor m t).mate v) := by rw [hσapp, mate_mate]
      rw [h, Equiv.Perm.sameCycle_apply_right]
      exact hv
  have hBs : ∀ v ∈ B, (factor m s).mate v ∈ B := by
    intro v hv
    have h := hout v hv
    rw [mem_defect, not_not] at h
    rw [← h]
    exact hBP v hv
  have hyB : y ∈ B := Or.inl (Equiv.Perm.SameCycle.refl σ y)
  by_cases hall : ∀ w, w ∈ B
  · have hPs : P = factor m s := PerfectMatching.ext (Equiv.ext fun w ↦ by
      have h := hout w (hall w)
      rwa [mem_defect, not_not] at h)
    exact hP t (hPs ▸ ham_factor_of_ne hp (Ne.symm hts))
  · push Not at hall
    obtain ⟨w, hw⟩ := hall
    exact not_ham_of_closed (factor m s) (factor m t) B hBs hBt hyB hw
      (ham_factor_of_ne hp (Ne.symm hts))

/-- **Theorem C′ for zero states** (`factor-tail-L-test.md`; NG-B(b) of
`sqrt-m-obstructions.md` §1.3). Let `n = 2m - 1` be prime and `P` a zero state with
`k = |P ∖ F_s|`. If every `t ≠ s` has a cycle of `P ∪ F_t` with at most `L` edges of `P`, so
`L(P) ≤ L`, then `n - 1 ≤ 2k((2k + 2)L - 1)`. -/
theorem certLength_bound_of_isZeroState (hp : (2 * m - 1).Prime) {P : PerfectMatching (Vertex m)}
    (hP : IsZeroState (factor m) P) (s : ZMod (2 * m - 1)) {L : ℕ}
    (hcert : ∀ t ≠ s, ∃ y r, 1 ≤ r ∧ r ≤ L ∧ (certPerm P t ^ r) y = y) :
    2 * m - 2 ≤ 2 * (edgesOutside (factor m s) P).card *
      ((2 * (edgesOutside (factor m s) P).card + 2) * L - 1) := by
  refine certLength_bound_edges hp P s fun t hts ↦ ?_
  obtain ⟨y, r, hr1, hrL, hcyc⟩ := hcert t hts
  obtain ⟨y', hy', hcyc'⟩ := exists_defect_of_cycle hp hP hts hcyc
  exact ⟨y', hy', r, hr1, hrL, hcyc'⟩

omit [NeZero m] in
/-- The default gadget `G0 = {1, …, 6}` has six vertices for `m ≥ 5`. -/
theorem card_gadget (hm : 5 ≤ m) : (FactorCap.gadget m).card = 6 := by
  rw [FactorCap.gadget, Finset.card_image_of_injOn]
  · simp
  · intro x hx y hy h
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    exact natCast_injOn (by omega) (by omega) (Option.some_inj.mp h)

/-- A matching within `d` of the factor tail `T(n)` differs from `F_{s0}` on at most `2d + 6`
vertices, so `k = |P ∖ F_{s0}| ≤ d + 3` (`factor-tail-L-test.md`, consequences of Theorem C′). -/
theorem card_defect_factorTail_le (hm : 5 ≤ m) (P : PerfectMatching (Vertex m)) :
    (defect (factor m (FactorCap.capCenter m)) P).card ≤
      2 * tailDist P (FactorCap.factorTail m hm) + 6 := by
  have h := card_defect_le_of_extends (factor m (FactorCap.capCenter m))
    (FactorCap.factorTail m hm) (fun u ↦ (FactorCap.factorTail_mate hm u).symm) P
  rwa [compl_compl, card_gadget hm] at h

/-- **Theorem C′ on the factor tail** (`factor-tail-L-test.md`; NG-B(b) of
`sqrt-m-obstructions.md` §1.3). Let `n = 2m - 1 ≥ 9` be prime and `P` a zero state within `d`
edges of the factor tail `T(n)` of the gadget `G0`. If every `t ≠ s0` has a cycle of `P ∪ F_t`
with at most `L` edges of `P`, then `n - 1 ≤ 2(d + 3)((2(d + 3) + 2)L - 1)`. -/
theorem factorTail_certLength (hp : (2 * m - 1).Prime) (hm : 5 ≤ m)
    {P : PerfectMatching (Vertex m)} (hP : IsZeroState (factor m) P) {d L : ℕ}
    (hd : tailDist P (FactorCap.factorTail m hm) ≤ d)
    (hcert : ∀ t ≠ FactorCap.capCenter m, ∃ y r, 1 ≤ r ∧ r ≤ L ∧ (certPerm P t ^ r) y = y) :
    2 * m - 2 ≤ 2 * (d + 3) * ((2 * (d + 3) + 2) * L - 1) := by
  have h := certLength_bound_of_isZeroState hp hP _ hcert
  have hk : (edgesOutside (factor m (FactorCap.capCenter m)) P).card ≤ d + 3 := by
    have h1 := two_mul_card_edgesOutside (factor m (FactorCap.capCenter m)) P
    have h2 := card_defect_factorTail_le hm P
    omega
  exact h.trans (Nat.mul_le_mul (by omega)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right L (by omega)) 1))

/-- **Bounded cost forces linear certificate length** (`factor-tail-L-test.md`, consequences of
Theorem C′; NG-B(b) of `sqrt-m-obstructions.md` §1.3). A repair `P` of `T(n)` of cost at most
`5` at prime `n = 2m - 1 ≥ 9` has `L(P) ≥ (n + 15)/288`: if every `t ≠ s0` has a cycle of
`P ∪ F_t` with at most `L` edges of `P`, then `n + 15 ≤ 288 L`. -/
theorem factorTail_certLength_five (hp : (2 * m - 1).Prime) (hm : 5 ≤ m)
    {P : PerfectMatching (Vertex m)} (hP : IsZeroState (factor m) P) {L : ℕ}
    (hd : tailDist P (FactorCap.factorTail m hm) ≤ 5)
    (hcert : ∀ t ≠ FactorCap.capCenter m, ∃ y r, 1 ≤ r ∧ r ≤ L ∧ (certPerm P t ^ r) y = y) :
    2 * m - 1 + 15 ≤ 288 * L := by
  have h := factorTail_certLength hp hm hP hd hcert
  omega

end RoundRobin.Canonical

end Pairing
