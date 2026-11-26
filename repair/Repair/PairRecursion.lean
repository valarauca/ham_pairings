import Clifford.Contraction
import Suppression.Canonical

/-!
# The k = 2 pair recursion (Lemma K2)

Source: `results/k3-counterexample-hunt.md` (e5bd2f7), §3, Lemma K2.

For two perfect matchings `F₀, F₁` of a finite vertex set `V`, `hamPairCount F₀ F₁` is the
number of perfect matchings `P` with `P ∪ F₀` and `P ∪ F₁` both one cycle. The type
`pairType F₀ F₁` is the multiset of half-lengths of the cycles of `F₀ ∪ F₁`, a part `1` being a
shared edge.

* `alt F₀ F₁ v` : the alternating walk `c_0 c_1 …` from `v`, with `c_{k+1} = F_{k mod 2}(c_k)`.
  `cycLen F₀ F₁ v` is its period `2a`, and `card_cycleOf` : the cycle through `v` has `2a`
  vertices `c_0, …, c_{2a-1}`.
* `red F hvu` : the reduction of `F` by a red edge `vu`, a matching of `V ∖ {v, u}` that
  replaces `v F(v)` and `u F(u)` by `F(v) F(u)`.
* `card_fiber_eq` : the matchings `P ∋ vu` with both unions Hamiltonian correspond to the pairs
  counted by `hamPairCount (red F₀ hvu) (red F₁ hvu)`. `card_fiber_mate_eq_zero` : the two
  neighbours `F₀(v), F₁(v)` are forbidden.
* Lemma K2 : `redType_of_even`, `redType_of_odd`, `redType_of_notMem` give the type of the
  reduced pair for `u = c_d` with `d` even, `u = c_{2x+1}`, and `u` in another cycle.
* `hamPairCount_eq_k2Count` : `hamPairCount F₀ F₁ = k2Count (pairType F₀ F₁)`, where
  `k2Count` is the recursion over partitions with `k2Count {1} = 1`.
  `hamPairCount_eq_k2Step` : the recursion holds at every vertex `v`.
-/

open Finset

namespace Pairing

namespace PerfectMatching

variable {V : Type*}

section Walk

variable (F0 F1 : PerfectMatching V)

/-- The matching used by step `k` of the alternating walk, `F₀` at even `k` and `F₁` at odd `k`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def stepMatching (k : ℕ) : PerfectMatching V :=
  if k % 2 = 0 then F0 else F1

/-- The alternating walk `c_0 = v`, `c_{k+1} = F_{k mod 2}(c_k)`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def alt (v : V) : ℕ → V
  | 0 => v
  | k + 1 => (stepMatching F0 F1 k).mate (alt v k)

variable {F0 F1}

/-- Even steps use `F₀` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem stepMatching_of_even {k : ℕ} (h : k % 2 = 0) : stepMatching F0 F1 k = F0 := by
  simp [stepMatching, h]

/-- Odd steps use `F₁` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem stepMatching_of_odd {k : ℕ} (h : k % 2 = 1) : stepMatching F0 F1 k = F1 := by
  simp [stepMatching, h]

/-- Every step uses `F₀` or `F₁` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem stepMatching_eq_or (k : ℕ) : stepMatching F0 F1 k = F0 ∨ stepMatching F0 F1 k = F1 := by
  unfold stepMatching
  split_ifs <;> simp

/-- Steps of equal parity use the same matching (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem stepMatching_congr {k l : ℕ} (h : k % 2 = l % 2) :
    stepMatching F0 F1 k = stepMatching F0 F1 l := by
  simp [stepMatching, h]

/-- The walk starts at `c_0 = v` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
@[simp]
theorem alt_zero (v : V) : alt F0 F1 v 0 = v :=
  rfl

/-- `c_{k+1} = F_{k mod 2}(c_k)` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_succ (v : V) (k : ℕ) :
    alt F0 F1 v (k + 1) = (stepMatching F0 F1 k).mate (alt F0 F1 v k) :=
  rfl

/-- `F_{k mod 2}(c_{k+1}) = c_k` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mate_alt_succ (v : V) (k : ℕ) :
    (stepMatching F0 F1 k).mate (alt F0 F1 v (k + 1)) = alt F0 F1 v k := by
  rw [alt_succ, mate_mate]

/-- Positions at odd distance along the walk are distinct (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem alt_ne_add_odd (v : V) (t i : ℕ) : alt F0 F1 v i ≠ alt F0 F1 v (i + 2 * t + 1) := by
  induction t generalizing i with
  | zero =>
    intro h
    rw [mul_zero, add_zero, alt_succ] at h
    exact (stepMatching F0 F1 i).mate_ne _ h.symm
  | succ t ih =>
    intro h
    apply ih (i + 1)
    have h1 := congrArg (stepMatching F0 F1 i).mate h
    rw [← alt_succ, stepMatching_congr (l := i + 2 * t + 2) (by omega),
      show i + 2 * (t + 1) + 1 = i + 2 * t + 2 + 1 by ring, mate_alt_succ] at h1
    rw [h1]
    ring_nf

/-- Equal positions of the walk have equal parity (`results/k3-counterexample-hunt.md`, Lemma K2).
-/
theorem alt_mod_two_eq {v : V} {i j : ℕ} (h : alt F0 F1 v i = alt F0 F1 v j) : i % 2 = j % 2 := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_contra hne
    obtain ⟨t, rfl⟩ : ∃ t, j = i + 2 * t + 1 := ⟨(j - i - 1) / 2, by omega⟩
    exact alt_ne_add_odd v t i h
  · rfl
  · by_contra hne
    obtain ⟨t, rfl⟩ : ∃ t, i = j + 2 * t + 1 := ⟨(i - j - 1) / 2, by omega⟩
    exact alt_ne_add_odd v t j h.symm

/-- Equal successors at equal parity have equal predecessors (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem alt_eq_of_succ_eq {v : V} {i j : ℕ} (h2 : i % 2 = j % 2)
    (h : alt F0 F1 v (i + 1) = alt F0 F1 v (j + 1)) : alt F0 F1 v i = alt F0 F1 v j := by
  have h1 := congrArg (stepMatching F0 F1 i).mate h
  rwa [mate_alt_succ, stepMatching_congr h2, mate_alt_succ] at h1

/-- Equal positions at equal parity have equal successors (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem alt_succ_eq_of_eq {v : V} {i j : ℕ} (h2 : i % 2 = j % 2)
    (h : alt F0 F1 v i = alt F0 F1 v j) : alt F0 F1 v (i + 1) = alt F0 F1 v (j + 1) := by
  rw [alt_succ, alt_succ, h, stepMatching_congr h2]

/-- A repeat at even distance `2t` gives `c_{2t} = v` (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem alt_two_mul_eq_self {v : V} (t i : ℕ) (h : alt F0 F1 v i = alt F0 F1 v (i + 2 * t)) :
    alt F0 F1 v (2 * t) = v := by
  induction i with
  | zero => simpa using h.symm
  | succ i ih =>
    exact ih (alt_eq_of_succ_eq (by omega) (by rwa [show i + 2 * t + 1 = i + 1 + 2 * t by ring]))

variable (F0 F1) in
/-- The alternating walk returns to `v` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem exists_alt_eq_self [Finite V] (v : V) : ∃ k, 0 < k ∧ alt F0 F1 v k = v := by
  obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (alt F0 F1 v)
  have h2 := alt_mod_two_eq h
  rcases lt_or_gt_of_ne hne with hij | hij
  · obtain ⟨t, rfl⟩ : ∃ t, j = i + 2 * t := ⟨(j - i) / 2, by omega⟩
    exact ⟨2 * t, by omega, alt_two_mul_eq_self t i h⟩
  · obtain ⟨t, rfl⟩ : ∃ t, i = j + 2 * t := ⟨(i - j) / 2, by omega⟩
    exact ⟨2 * t, by omega, alt_two_mul_eq_self t j h.symm⟩

end Walk

section Cycle

variable [Fintype V] [DecidableEq V] (F0 F1 : PerfectMatching V)

/-- The length `2a` of the cycle of `F₀ ∪ F₁` through `v`, the first return time of the
alternating walk (`results/k3-counterexample-hunt.md`, Lemma K2). -/
def cycLen (v : V) : ℕ :=
  Nat.find (exists_alt_eq_self F0 F1 v)

variable {F0 F1}

/-- `2a > 0` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cycLen_pos (v : V) : 0 < cycLen F0 F1 v :=
  (Nat.find_spec (exists_alt_eq_self F0 F1 v)).1

/-- `c_{2a} = v` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_cycLen (v : V) : alt F0 F1 v (cycLen F0 F1 v) = v :=
  (Nat.find_spec (exists_alt_eq_self F0 F1 v)).2

/-- `c_k ≠ v` for `0 < k < 2a` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_ne_self {v : V} {k : ℕ} (h0 : 0 < k) (hk : k < cycLen F0 F1 v) :
    alt F0 F1 v k ≠ v :=
  fun h ↦ Nat.find_min (exists_alt_eq_self F0 F1 v) hk ⟨h0, h⟩

/-- The cycle length `2a` is even (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cycLen_even (v : V) : cycLen F0 F1 v % 2 = 0 := by
  have := alt_mod_two_eq (F0 := F0) (F1 := F1) (v := v) (i := 0) (j := cycLen F0 F1 v)
    (by rw [alt_cycLen, alt_zero])
  omega

/-- `c_0, …, c_{2a-1}` are distinct (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_injOn {v : V} {i j : ℕ} (hi : i < cycLen F0 F1 v) (hj : j < cycLen F0 F1 v)
    (h : alt F0 F1 v i = alt F0 F1 v j) : i = j := by
  have h2 := alt_mod_two_eq h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · obtain ⟨t, rfl⟩ : ∃ t, j = i + 2 * t := ⟨(j - i) / 2, by omega⟩
    exact alt_ne_self (by omega) (by omega) (alt_two_mul_eq_self t i h)
  · obtain ⟨t, rfl⟩ : ∃ t, i = j + 2 * t := ⟨(i - j) / 2, by omega⟩
    exact alt_ne_self (by omega) (by omega) (alt_two_mul_eq_self t j h.symm)

/-- The walk has period `2a` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_add_cycLen (v : V) (k : ℕ) :
    alt F0 F1 v (k + cycLen F0 F1 v) = alt F0 F1 v k := by
  induction k with
  | zero => simpa using alt_cycLen v
  | succ k ih =>
    rw [show k + 1 + cycLen F0 F1 v = k + cycLen F0 F1 v + 1 by ring]
    exact alt_succ_eq_of_eq (by have := cycLen_even (F0 := F0) (F1 := F1) v; omega) ih

/-- `c_{k mod 2a} = c_k` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_mod (v : V) (k : ℕ) : alt F0 F1 v (k % cycLen F0 F1 v) = alt F0 F1 v k := by
  conv_rhs => rw [← Nat.mod_add_div k (cycLen F0 F1 v)]
  generalize k / cycLen F0 F1 v = q
  induction q with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, alt_add_cycLen, ih]

variable (F0 F1) in
/-- The cycle of `F₀ ∪ F₁` through `v`, as the vertices `c_0, …, c_{2a-1}` of the walk
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def cyc (v : V) : Finset V :=
  (range (cycLen F0 F1 v)).image (alt F0 F1 v)

/-- The cycle of `v` is the set of all positions of the walk (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem mem_cyc {v x : V} : x ∈ cyc F0 F1 v ↔ ∃ k, alt F0 F1 v k = x := by
  simp only [cyc, mem_image, mem_range]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k % cycLen F0 F1 v, Nat.mod_lt _ (cycLen_pos v), alt_mod v k⟩

/-- Every position of the walk lies on the cycle of `v` (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem alt_mem_cyc (v : V) (k : ℕ) : alt F0 F1 v k ∈ cyc F0 F1 v :=
  mem_cyc.mpr ⟨k, rfl⟩

/-- The cycle of `v` has `2a` vertices (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem card_cyc (v : V) : #(cyc F0 F1 v) = cycLen F0 F1 v := by
  rw [cyc, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact alt_injOn (mem_range.mp hi) (mem_range.mp hj) h

/-- The other partner of `c_k` lies on the cycle (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem stepMatching_mate_alt (v : V) (k : ℕ) :
    (stepMatching F0 F1 (k + 1)).mate (alt F0 F1 v k) ∈ cyc F0 F1 v := by
  rw [← alt_add_cycLen v k]
  obtain ⟨L, hL⟩ : ∃ L, cycLen F0 F1 v = L + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (cycLen_pos v)).symm⟩
  have he := cycLen_even (F0 := F0) (F1 := F1) v
  rw [hL, ← add_assoc, stepMatching_congr (l := k + L) (by omega), mate_alt_succ]
  exact alt_mem_cyc v _

/-- The cycle of `v` is closed under `F₀` and `F₁` (`results/k3-counterexample-hunt.md`, Lemma K2).
-/
theorem mate_mem_cyc {v x : V} (hx : x ∈ cyc F0 F1 v) :
    F0.mate x ∈ cyc F0 F1 v ∧ F1.mate x ∈ cyc F0 F1 v := by
  obtain ⟨k, rfl⟩ := mem_cyc.mp hx
  have h1 : (stepMatching F0 F1 k).mate (alt F0 F1 v k) ∈ cyc F0 F1 v := by
    rw [← alt_succ]
    exact alt_mem_cyc v _
  have h2 := stepMatching_mate_alt (F0 := F0) (F1 := F1) v k
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [stepMatching_of_even hk] at h1
    rw [stepMatching_of_odd (by omega)] at h2
    exact ⟨h1, h2⟩
  · rw [stepMatching_of_odd hk] at h1
    rw [stepMatching_of_even (by omega)] at h2
    exact ⟨h2, h1⟩

omit [Fintype V] [DecidableEq V] in
/-- Each step of the walk is an edge of `F₀ ∪ F₁` (`results/k3-counterexample-hunt.md`, Lemma K2).
-/
theorem stepMatching_adj (k : ℕ) (x : V) :
    (F0.toGraph ⊔ F1.toGraph).Adj x ((stepMatching F0 F1 k).mate x) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [stepMatching_of_even hk]
    exact adj_mate_left _ _ x
  · rw [stepMatching_of_odd hk]
    exact adj_mate_right _ _ x

omit [Fintype V] [DecidableEq V] in
/-- Every position of the walk is reachable from `v` in `F₀ ∪ F₁`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem reachable_alt (v : V) (k : ℕ) : (F0.toGraph ⊔ F1.toGraph).Reachable v (alt F0 F1 v k) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih => exact ih.trans (stepMatching_adj k _).reachable

end Cycle

section Block

variable [Fintype V] [DecidableEq V] (F0 F1 : PerfectMatching V)

/-- The vertex set of the cycle of `F₀ ∪ F₁` through `w`, the vertices reachable from `w`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def cycleOf (w : V) : Finset V :=
  {x | (F0.toGraph ⊔ F1.toGraph).Reachable w x}

/-- The type of `(F₀, F₁)`, the multiset of half-lengths of the cycles of `F₀ ∪ F₁`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def pairType : Multiset ℕ :=
  (univ.image (cycleOf F0 F1)).val.map fun S ↦ #S / 2

/-- `N(F₀, F₁)`, the number of perfect matchings `P` with `P ∪ F₀` and `P ∪ F₁` both one cycle
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def hamPairCount : ℕ :=
  #{P : PerfectMatching V | Ham P F0 ∧ Ham P F1}

variable {F0 F1}

/-- Membership in the cycle through `w` is reachability from `w`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_cycleOf {w x : V} :
    x ∈ cycleOf F0 F1 w ↔ (F0.toGraph ⊔ F1.toGraph).Reachable w x := by
  simp [cycleOf]

omit [Fintype V] [DecidableEq V] in
/-- A set closed under `F₀` and `F₁` is closed under reachability
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_of_reachable_of_closed {S : Finset V}
    (hS : ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S) {x y : V}
    (h : (F0.toGraph ⊔ F1.toGraph).Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons hadj _ ih =>
    rcases (sup_toGraph_adj _ _ _ _).mp hadj with rfl | rfl
    · exact ih (hS _ hx).1
    · exact ih (hS _ hx).2

/-- A closed connected set is the cycle through each of its vertices
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cycleOf_eq_of_block {S : Finset V} (hS : ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, (F0.toGraph ⊔ F1.toGraph).Reachable x y) {w : V} (hw : w ∈ S) :
    cycleOf F0 F1 w = S := by
  ext x
  rw [mem_cycleOf]
  exact ⟨fun h ↦ mem_of_reachable_of_closed hS h hw, fun hx ↦ hc w hw x hx⟩

/-- A family of closed connected blocks covering `V` is the set of cycles of `F₀ ∪ F₁`. -/
theorem image_cycleOf_eq {𝓑 : Finset (Finset V)}
    (hS : ∀ S ∈ 𝓑, ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    (hc : ∀ S ∈ 𝓑, ∀ x ∈ S, ∀ y ∈ S, (F0.toGraph ⊔ F1.toGraph).Reachable x y)
    (hne : ∀ S ∈ 𝓑, S.Nonempty) (hcov : ∀ w, ∃ S ∈ 𝓑, w ∈ S) :
    univ.image (cycleOf F0 F1) = 𝓑 := by
  ext S
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨T, hT, hw⟩ := hcov w
    rwa [cycleOf_eq_of_block (hS T hT) (hc T hT) hw]
  · intro hS'
    obtain ⟨w, hw⟩ := hne S hS'
    exact ⟨w, cycleOf_eq_of_block (hS S hS') (hc S hS') hw⟩

/-- The type computed from any family of closed connected blocks covering `V`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem pairType_eq_of_blocks {𝓑 : Finset (Finset V)}
    (hS : ∀ S ∈ 𝓑, ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    (hc : ∀ S ∈ 𝓑, ∀ x ∈ S, ∀ y ∈ S, (F0.toGraph ⊔ F1.toGraph).Reachable x y)
    (hne : ∀ S ∈ 𝓑, S.Nonempty) (hcov : ∀ w, ∃ S ∈ 𝓑, w ∈ S) :
    pairType F0 F1 = 𝓑.val.map fun S ↦ #S / 2 := by
  rw [pairType, image_cycleOf_eq hS hc hne hcov]

/-- The cycle through `v` is the set `c_0, …, c_{2a-1}` of the walk
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cycleOf_eq_cyc (v : V) : cycleOf F0 F1 v = cyc F0 F1 v := by
  refine cycleOf_eq_of_block (fun x hx ↦ mate_mem_cyc hx) (fun x hx y hy ↦ ?_)
    (by simpa using alt_mem_cyc (F0 := F0) (F1 := F1) v 0)
  obtain ⟨i, rfl⟩ := mem_cyc.mp hx
  obtain ⟨j, rfl⟩ := mem_cyc.mp hy
  exact (reachable_alt v i).symm.trans (reachable_alt v j)

/-- The cycle through `v` has `cycLen` vertices (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem card_cycleOf (v : V) : #(cycleOf F0 F1 v) = cycLen F0 F1 v := by
  rw [cycleOf_eq_cyc, card_cyc]

/-- `v` lies on its own cycle (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_cycleOf_self (v : V) : v ∈ cycleOf F0 F1 v :=
  mem_cycleOf.mpr (SimpleGraph.Reachable.refl _)

/-- Two vertices of one cycle have the same cycle (`results/k3-counterexample-hunt.md`, Lemma K2).
-/
theorem cycleOf_eq_of_mem {v w : V} (h : w ∈ cycleOf F0 F1 v) :
    cycleOf F0 F1 w = cycleOf F0 F1 v := by
  ext x
  simp only [mem_cycleOf] at h ⊢
  exact ⟨fun h' ↦ h.trans h', fun h' ↦ h.symm.trans h'⟩

/-- The cycle through `v` is closed under `F₀` and `F₁` (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem mate_mem_cycleOf {v x : V} (hx : x ∈ cycleOf F0 F1 v) :
    F0.mate x ∈ cycleOf F0 F1 v ∧ F1.mate x ∈ cycleOf F0 F1 v := by
  rw [cycleOf_eq_cyc] at hx ⊢
  exact mate_mem_cyc hx

/-- Every cycle has an even number `2a` of vertices (`results/k3-counterexample-hunt.md`, Lemma K2).
-/
theorem two_mul_card_cycleOf_div_two (v : V) :
    2 * (#(cycleOf F0 F1 v) / 2) = #(cycleOf F0 F1 v) := by
  rw [card_cycleOf]
  have := cycLen_even (F0 := F0) (F1 := F1) v
  omega

end Block

section Switch

variable [DecidableEq V] (F : PerfectMatching V) {v u : V}

/-- `swap(u, F(v)) • F`, the matching with `vu` and `F(v) F(u)` in place of `v F(v)` and `u F(u)`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def switch (F : PerfectMatching V) (v u : V) : PerfectMatching V :=
  Equiv.swap u (F.mate v) • F

/-- The switched matching contains `vu` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_self (hvu : v ≠ u) : (switch F v u).mate v = u := by
  rw [switch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hvu (F.mate_ne v).symm,
    Equiv.swap_apply_right]

/-- The switched matching maps `u` to `v` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_right (hvu : v ≠ u) : (switch F v u).mate u = v := by
  have h := (switch F v u).mate_mate v
  rwa [switch_mate_self F hvu] at h

/-- The switched matching agrees with `F` away from `v`, `u`, `F(v)`, `F(u)`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_of_ne {x : V} (hxv : x ≠ v) (hxu : x ≠ u) (h1 : F.mate x ≠ v)
    (h2 : F.mate x ≠ u) : (switch F v u).mate x = F.mate x := by
  have h3 : x ≠ F.mate v := fun h ↦ h1 (by rw [h, mate_mate])
  have h4 : F.mate x ≠ F.mate v := fun h ↦ hxv (F.mate.injective h)
  rw [switch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hxu h3,
    Equiv.swap_apply_of_ne_of_ne h2 h4]

/-- The switched matching contains `F(v) F(u)` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_mate_self (hvu : v ≠ u) : (switch F v u).mate (F.mate v) = F.mate u := by
  have h4 : F.mate u ≠ F.mate v := fun h ↦ hvu (F.mate.injective h).symm
  rw [switch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (F.mate_ne u) h4]

/-- The switched matching maps `F(u)` to `F(v)` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_mate_right (hvu : v ≠ u) : (switch F v u).mate (F.mate u) = F.mate v := by
  have h4 : F.mate u ≠ F.mate v := fun h ↦ hvu (F.mate.injective h).symm
  rw [switch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (F.mate_ne u) h4,
    mate_mate, Equiv.swap_apply_left]

end Switch

section Reduction

variable [Fintype V] [DecidableEq V]

/-- `V ∖ {v, u}`, the vertex set after the reduction by the red edge `vu`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def redSet (v u : V) : Finset V :=
  (univ.erase v).erase u

/-- Membership in `V ∖ {v, u}` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_redSet {v u x : V} : x ∈ redSet v u ↔ x ≠ v ∧ x ≠ u := by
  simp [redSet, and_comm]

/-- A matching containing `vu` maps `V ∖ {v, u}` into itself (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem mate_mem_redSet_of {P : PerfectMatching V} {v u : V} (hP : P.mate v = u) :
    ∀ x ∈ redSet v u, P.mate x ∈ redSet v u := by
  intro x hx
  rw [mem_redSet] at hx ⊢
  refine ⟨fun h ↦ hx.2 ?_, fun h ↦ hx.1 ?_⟩
  · rw [← hP, ← h, mate_mate]
  · rw [← P.mate_mate v, hP, ← h, mate_mate]

/-- The switched matching maps `V ∖ {v, u}` into itself (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem switch_mem_redSet (F : PerfectMatching V) {v u : V} (hvu : v ≠ u) :
    ∀ x ∈ redSet v u, (switch F v u).mate x ∈ redSet v u :=
  mate_mem_redSet_of (switch_mate_self F hvu)

/-- The reduction of `F` by the red edge `vu`, the matching of `V ∖ {v, u}` that replaces
`v F(v)` and `u F(u)` by `F(v) F(u)` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
def red (F : PerfectMatching V) {v u : V} (hvu : v ≠ u) : PerfectMatching (redSet v u) :=
  restrict (switch F v u) (redSet v u) (switch_mem_redSet F hvu)

/-- The reduced matching is the switched matching on `V ∖ {v, u}`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem red_mate_coe (F : PerfectMatching V) {v u : V} (hvu : v ≠ u) (x : redSet v u) :
    ((red F hvu).mate x : V) = (switch F v u).mate x :=
  rfl

/-- The endpoint pairing of `F ∪ {vu}` on `V ∖ {v, u}` is the reduction of `F`. -/
theorem contract_eq_red (P F : PerfectMatching V) {v u : V} (hvu : v ≠ u) (hP : P.mate v = u)
    (hF : F.mate v ≠ u) (hA : ∀ x ∈ redSet v u, P.mate x ∈ redSet v u) :
    contract P F (redSet v u) hA = red F hvu := by
  have hPu : P.mate u = v := by rw [← hP, mate_mate]
  have hFu : F.mate u ≠ v := fun h ↦ hF (by rw [← h, mate_mate])
  ext a
  obtain ⟨x, hx⟩ := a
  have hx' := mem_redSet.mp hx
  rw [red_mate_coe]
  by_cases hFx : F.mate x ∈ redSet v u
  · rw [contract_mate_of_mem P F _ hA ⟨x, hx⟩ hFx]
    exact (switch_mate_of_ne F hx'.1 hx'.2 (mem_redSet.mp hFx).1 (mem_redSet.mp hFx).2).symm
  · have hFx' : F.mate x = v ∨ F.mate x = u := by
      rw [mem_redSet] at hFx
      tauto
    have hmem : F.mate (P.mate (F.mate x)) ∈ redSet v u := by
      rw [mem_redSet]
      rcases hFx' with h | h <;> rw [h]
      · rw [hP]
        exact ⟨hFu, F.mate_ne u⟩
      · rw [hPu]
        exact ⟨F.mate_ne v, hF⟩
    have h1 : exitIdx P F (redSet v u) hA ⟨x, hx⟩ = 1 := by
      rw [exitIdx, Nat.find_eq_iff]
      refine ⟨by simpa [oddPt, evenPt] using hmem, fun n hn ↦ ?_⟩
      obtain rfl : n = 0 := by omega
      simpa [oddPt, evenPt] using hFx
    rw [contract_mate, coe_contractFun, h1]
    simp only [oddPt, evenPt, pow_one, Equiv.Perm.mul_apply]
    rcases hFx' with h | h
    · have hxe : x = F.mate v := by rw [← h, mate_mate]
      rw [h, hP, hxe, switch_mate_mate_self F hvu]
    · have hxe : x = F.mate u := by rw [← h, mate_mate]
      rw [h, hPu, hxe, switch_mate_mate_right F hvu]

/-- For `P ∋ vu` and `F(v) ≠ u`, `P ∪ F` is one cycle iff the reduced pair is. -/
theorem ham_iff_red (P F : PerfectMatching V) {v u : V} (hvu : v ≠ u) (hP : P.mate v = u)
    (hF : F.mate v ≠ u) (hA : ∀ x ∈ redSet v u, P.mate x ∈ redSet v u) :
    Ham P F ↔ Ham (restrict P (redSet v u) hA) (red F hvu) := by
  have hPu : P.mate u = v := by rw [← hP, mate_mate]
  have hC : ¬HasClosedCycle P F (redSet v u) := by
    rintro ⟨C, ⟨w, hw⟩, hdisj, hPC, hFC⟩
    have hout : ∀ y ∈ C, y = v ∨ y = u := by
      intro y hy
      have := Finset.disjoint_left.mp hdisj hy
      rw [mem_redSet] at this
      tauto
    have hv : v ∈ C := by
      rcases hout w hw with rfl | rfl
      · exact hw
      · exact hPu ▸ hPC _ hw
    rcases hout _ (hFC v hv) with h | h
    · exact F.mate_ne v h
    · exact hF h
  have := ham_glue_iff P F (redSet v u) hA hC (restrict P (redSet v u) hA)
  rwa [glue_restrict, contract_eq_red P F hvu hP hF hA] at this

/-- The matchings `P ∋ vu` with both unions Hamiltonian correspond to the pairs counted for the
reduced pair (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem card_fiber_eq (F0 F1 : PerfectMatching V) {v u : V} (hvu : v ≠ u) (h0 : F0.mate v ≠ u)
    (h1 : F1.mate v ≠ u) :
    #{P : PerfectMatching V | P.mate v = u ∧ Ham P F0 ∧ Ham P F1} =
      hamPairCount (red F0 hvu) (red F1 hvu) := by
  rw [hamPairCount]
  have hK := switch_mem_redSet F0 hvu
  refine card_bij' (fun P hP ↦ restrict P (redSet v u)
      (mate_mem_redSet_of (mem_filter.mp hP).2.1))
    (fun X _ ↦ glue (switch F0 v u) (redSet v u) hK X) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨-, hPv, hP0, hP1⟩ := mem_filter.mp hP
    exact mem_filter.mpr ⟨mem_univ _, (ham_iff_red P F0 hvu hPv h0 _).mp hP0,
      (ham_iff_red P F1 hvu hPv h1 _).mp hP1⟩
  · intro X hX
    obtain ⟨-, hX0, hX1⟩ := mem_filter.mp hX
    have hv : v ∉ redSet v u := fun h ↦ (mem_redSet.mp h).1 rfl
    have hgv : (glue (switch F0 v u) (redSet v u) hK X).mate v = u := by
      rw [glue_mate_of_notMem _ _ hK X hv, switch_mate_self F0 hvu]
    have hr : restrict (glue (switch F0 v u) (redSet v u) hK X) (redSet v u)
        (mate_mem_redSet_of hgv) = X := restrict_glue _ _ hK X
    refine mem_filter.mpr ⟨mem_univ _, hgv, ?_, ?_⟩
    · rw [ham_iff_red _ F0 hvu hgv h0 (mate_mem_redSet_of hgv), hr]
      exact hX0
    · rw [ham_iff_red _ F1 hvu hgv h1 (mate_mem_redSet_of hgv), hr]
      exact hX1
  · intro P hP
    have hPv := (mem_filter.mp hP).2.1
    have hPu : P.mate u = v := by rw [← hPv, mate_mate]
    ext x
    by_cases hx : x ∈ redSet v u
    · rw [glue_mate_of_mem _ _ hK _ hx]
      rfl
    · rw [glue_mate_of_notMem _ _ hK _ hx]
      rw [mem_redSet] at hx
      by_cases hxv : x = v
      · rw [hxv, switch_mate_self F0 hvu, hPv]
      · have hxu : x = u := by tauto
        rw [hxu, switch_mate_right F0 hvu, hPu]
  · intro X _
    exact restrict_glue _ _ hK X

omit [DecidableEq V] in
/-- The two neighbours `F₀(v)` and `F₁(v)` are forbidden partners of `v` once `|V| > 2`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem not_ham_of_mate_eq {P F : PerfectMatching V} {v : V} (hV : 2 < Fintype.card V)
    (h : P.mate v = F.mate v) : ¬Ham P F := by
  classical
  have hcard : #({v, F.mate v} : Finset V) < #(univ : Finset V) := by
    rw [card_univ]
    exact lt_of_le_of_lt (card_le_two) hV
  obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hPF : P.mate (F.mate v) = v := by rw [← h, mate_mate]
  refine not_ham_of_closed P F ({v, F.mate v} : Finset V) ?_ ?_ (u := v) (w := w)
    (by simp) (by simpa using hw)
  · intro x hx
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr h
    · exact Or.inl hPF
  · intro x hx
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (mate_mate _ _)

/-- `N` of the reduced pair by the red edge `vu`, and `0` for `u = v`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def redCount (F0 F1 : PerfectMatching V) (v u : V) : ℕ :=
  if h : v = u then 0 else hamPairCount (red F0 h) (red F1 h)

/-- The type of the reduced pair by the red edge `vu`, and `0` for `u = v`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def redType (F0 F1 : PerfectMatching V) (v u : V) : Multiset ℕ :=
  if h : v = u then 0 else pairType (red F0 h) (red F1 h)

/-- The GS reduction: `N(F₀, F₁)` is the sum over the allowed partners `u` of `v` of `N` of the
reduced pair (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_eq_sum_redCount (F0 F1 : PerfectMatching V) (v : V)
    (hV : 2 < Fintype.card V) :
    hamPairCount F0 F1 =
      ∑ u ∈ ((univ.erase v).erase (F0.mate v)).erase (F1.mate v), redCount F0 F1 v u := by
  have hfib : hamPairCount F0 F1 =
      ∑ u, #{P : PerfectMatching V | P.mate v = u ∧ Ham P F0 ∧ Ham P F1} := by
    rw [hamPairCount, card_eq_sum_card_fiberwise (f := fun P ↦ P.mate v) (t := univ)
      (fun _ _ ↦ mem_coe.mpr (mem_univ _))]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [filter_filter]
    congr 1
    ext P
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [hfib, ← sum_subset (subset_univ (((univ.erase v).erase (F0.mate v)).erase (F1.mate v)))]
  · refine sum_congr rfl fun u hu ↦ ?_
    simp only [mem_erase, mem_univ, and_true] at hu
    obtain ⟨h1, h0, hvu⟩ := hu
    rw [redCount, dite_eq_right (Ne.symm hvu)]
    exact card_fiber_eq F0 F1 (Ne.symm hvu) (Ne.symm h0) (Ne.symm h1)
  · intro u _ hu
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro P - ⟨hPv, hP0, hP1⟩
    simp only [mem_erase, mem_univ, and_true, not_and, not_not] at hu
    by_cases h1 : u = F1.mate v
    · exact not_ham_of_mate_eq hV (hPv.trans h1) hP1
    by_cases h0 : u = F0.mate v
    · exact not_ham_of_mate_eq hV (hPv.trans h0) hP0
    exact P.mate_ne v (hPv.trans (hu h1 h0))

end Reduction

section RedBlocks

variable [Fintype V] [DecidableEq V] {F0 F1 : PerfectMatching V}

/-- Lying on a common cycle is symmetric (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_cycleOf_comm {x y : V} : x ∈ cycleOf F0 F1 y ↔ y ∈ cycleOf F0 F1 x := by
  simp only [mem_cycleOf]
  exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

/-- Every position of the walk from `v` lies on the cycle through `v`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mem_cycleOf_alt (v : V) (k : ℕ) : alt F0 F1 v k ∈ cycleOf F0 F1 v := by
  rw [cycleOf_eq_cyc]
  exact alt_mem_cyc v k

/-- Every vertex of the cycle through `v` is some `c_k` with `k < 2a`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem exists_lt_of_mem_cycleOf {v x : V} (hx : x ∈ cycleOf F0 F1 v) :
    ∃ k < cycLen F0 F1 v, alt F0 F1 v k = x := by
  rw [cycleOf_eq_cyc, cyc, mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, mem_range.mp hk, rfl⟩

/-- Two cycles agree iff one vertex lies on the other (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem cycleOf_eq_iff_mem {v w : V} : cycleOf F0 F1 w = cycleOf F0 F1 v ↔ w ∈ cycleOf F0 F1 v :=
  ⟨fun h ↦ h ▸ mem_cycleOf_self w, cycleOf_eq_of_mem⟩

/-- `c_j` survives the reduction by `v c_d` for `0 < j < 2a`, `j ≠ d`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem alt_mem_redSet {v : V} {d j : ℕ} (hd : d < cycLen F0 F1 v) (hj0 : 0 < j)
    (hjL : j < cycLen F0 F1 v) (hjd : j ≠ d) : alt F0 F1 v j ∈ redSet v (alt F0 F1 v d) :=
  mem_redSet.mpr ⟨alt_ne_self hj0 hjL, fun h ↦ hjd (alt_injOn hjL hd h)⟩

omit [Fintype V] [DecidableEq V] in
/-- `F₀(v) = c_1` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mate_zero_eq_alt_one (v : V) : F0.mate v = alt F0 F1 v 1 := by
  rw [alt_succ, stepMatching_of_even (by norm_num), alt_zero]

/-- `F₁(v) = c_{2a-1}` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem mate_one_eq_alt_pred (v : V) :
    F1.mate v = alt F0 F1 v (cycLen F0 F1 v - 1) := by
  have he := cycLen_even (F0 := F0) (F1 := F1) v
  have hp := cycLen_pos (F0 := F0) (F1 := F1) v
  have h := mate_alt_succ (F0 := F0) (F1 := F1) v (cycLen F0 F1 v - 1)
  rw [Nat.sub_add_cancel hp, alt_cycLen, stepMatching_of_odd (by omega)] at h
  exact h

/-- An `F₀` or `F₁` edge avoiding `v` and `u` is an edge of the reduced union
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem red_adj {v u : V} (hvu : v ≠ u) {F : PerfectMatching V} (hF : F = F0 ∨ F = F1) {x : V}
    (hx : x ∈ redSet v u) (hy : F.mate x ∈ redSet v u) :
    ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Adj ⟨x, hx⟩ ⟨F.mate x, hy⟩ := by
  have hx' := mem_redSet.mp hx
  have hy' := mem_redSet.mp hy
  have h := switch_mate_of_ne F hx'.1 hx'.2 hy'.1 hy'.2
  rcases hF with rfl | rfl
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- A stretch of the walk avoiding `v` and `u` is a path of the reduced union
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem reachable_red_alt {v u : V} (hvu : v ≠ u) (w : V) (p n : ℕ)
    (h : ∀ k ≤ n, alt F0 F1 w (p + k) ∈ redSet v u) :
    ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable ⟨alt F0 F1 w p, h 0 (Nat.zero_le _)⟩
      ⟨alt F0 F1 w (p + n), h n le_rfl⟩ := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    exact (ih fun k hk ↦ h k (by omega)).trans
      (red_adj hvu (stepMatching_eq_or (p + n)) (h n (by omega)) (h (n + 1) le_rfl)).reachable

/-- A stretch `c_p, …, c_q` avoiding `v` and `u` joins `c_p` to `c_q` after the reduction
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem reachable_red_alt' {v u : V} (hvu : v ≠ u) (w : V) {p q : ℕ} (hpq : p ≤ q)
    (h : ∀ k, p ≤ k → k ≤ q → alt F0 F1 w k ∈ redSet v u) :
    ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable ⟨alt F0 F1 w p, h p le_rfl hpq⟩
      ⟨alt F0 F1 w q, h q hpq le_rfl⟩ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hpq
  exact reachable_red_alt hvu w p n (fun k hk ↦ h (p + k) (by omega) (by omega))

omit [Fintype V] in
/-- A set closed under `F₀`, `F₁` and containing `v`, `u` is closed under the switched matchings
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mem_of_closed {S : Finset V} (hS : ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    {v u : V} (hvu : v ≠ u) (hv : v ∈ S) (hu : u ∈ S) {F : PerfectMatching V}
    (hF : F = F0 ∨ F = F1) {x : V} (hx : x ∈ S) : (switch F v u).mate x ∈ S := by
  have hFS : ∀ y ∈ S, F.mate y ∈ S := by
    rcases hF with rfl | rfl
    · exact fun y hy ↦ (hS y hy).1
    · exact fun y hy ↦ (hS y hy).2
  by_cases hxv : x = v
  · rw [hxv, switch_mate_self F hvu]
    exact hu
  by_cases hxu : x = u
  · rw [hxu, switch_mate_right F hvu]
    exact hv
  by_cases h1 : F.mate x = v
  · have hx' : x = F.mate v := by rw [← h1, mate_mate]
    rw [hx', switch_mate_mate_self F hvu]
    exact hFS u hu
  by_cases h2 : F.mate x = u
  · have hx' : x = F.mate u := by rw [← h2, mate_mate]
    rw [hx', switch_mate_mate_right F hvu]
    exact hFS v hv
  rw [switch_mate_of_ne F hxv hxu h1 h2]
  exact hFS x hx

omit [Fintype V] in
/-- The switched matching agrees with `F` on a closed set avoiding `v` and `u`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mate_of_avoid {S : Finset V} (hS : ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    {v u : V} (hvS : v ∉ S) (huS : u ∉ S) {F : PerfectMatching V} (hF : F = F0 ∨ F = F1)
    {x : V} (hx : x ∈ S) : (switch F v u).mate x = F.mate x := by
  have hFx : F.mate x ∈ S := by
    rcases hF with rfl | rfl
    · exact (hS x hx).1
    · exact (hS x hx).2
  exact switch_mate_of_ne F (fun h ↦ hvS (h ▸ hx)) (fun h ↦ huS (h ▸ hx))
    (fun h ↦ hvS (h ▸ hFx)) (fun h ↦ huS (h ▸ hFx))

/-- Reachability inside a closed set avoiding `v` and `u` survives the reduction
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem reachable_red_of_avoid {S : Finset V} (hS : ∀ x ∈ S, F0.mate x ∈ S ∧ F1.mate x ∈ S)
    {v u : V} (hvu : v ≠ u) (hvS : v ∉ S) (huS : u ∉ S) {x y : V}
    (h : (F0.toGraph ⊔ F1.toGraph).Reachable x y) (hxS : x ∈ S) (hx : x ∈ redSet v u)
    (hy : y ∈ redSet v u) :
    ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a z b hadj q ih =>
    have hzS : z ∈ S := by
      rcases (sup_toGraph_adj _ _ _ _).mp hadj with rfl | rfl
      · exact (hS a hxS).1
      · exact (hS a hxS).2
    have hz : z ∈ redSet v u :=
      mem_redSet.mpr ⟨fun h ↦ hvS (h ▸ hzS), fun h ↦ huS (h ▸ hzS)⟩
    refine SimpleGraph.Reachable.trans ?_ (ih hzS hz hy)
    rcases (sup_toGraph_adj _ _ _ _).mp hadj with h | h
    · subst h
      exact (red_adj hvu (Or.inl rfl) hx hz).reachable
    · subst h
      exact (red_adj hvu (Or.inr rfl) hx hz).reachable

/-- An arc `c_p, …, c_q` of even length whose outer neighbours are `v` and `u` is closed under the
switched matchings (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem switch_mem_segment {v u : V} (hvu : v ≠ u) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpar : (p - 1) % 2 = q % 2)
    (hends : (alt F0 F1 v (p - 1) = v ∧ alt F0 F1 v (q + 1) = u) ∨
      (alt F0 F1 v (p - 1) = u ∧ alt F0 F1 v (q + 1) = v))
    (hin : ∀ k, p ≤ k → k ≤ q → alt F0 F1 v k ∈ redSet v u) (j : ℕ) {k : ℕ} (hpk : p ≤ k)
    (hkq : k ≤ q) :
    (switch (stepMatching F0 F1 j) v u).mate (alt F0 F1 v k) ∈ (Icc p q).image (alt F0 F1 v) := by
  have himg : ∀ i, p ≤ i → i ≤ q → alt F0 F1 v i ∈ (Icc p q).image (alt F0 F1 v) :=
    fun i h1 h2 ↦ mem_image.mpr ⟨i, mem_Icc.mpr ⟨h1, h2⟩, rfl⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hpar hends
  have hc : stepMatching F0 F1 p' = stepMatching F0 F1 q := stepMatching_congr hpar
  have hkey : (switch (stepMatching F0 F1 q) v u).mate (alt F0 F1 v (p' + 1)) =
      alt F0 F1 v q := by
    rw [alt_succ, hc]
    have h := mate_alt_succ (F0 := F0) (F1 := F1) v q
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at h
      rw [h1, switch_mate_mate_self _ hvu, h]
    · rw [h2] at h
      rw [h1, switch_mate_mate_right _ hvu, h]
  have hkey' : (switch (stepMatching F0 F1 q) v u).mate (alt F0 F1 v q) = alt F0 F1 v (p' + 1) := by
    rw [← hkey, mate_mate]
  have hne : ∀ i, p' + 1 ≤ i → i ≤ q → alt F0 F1 v i ≠ v ∧ alt F0 F1 v i ≠ u :=
    fun i h1 h2 ↦ mem_redSet.mp (hin i h1 h2)
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  all_goals first
    | (have hjk : stepMatching F0 F1 j = stepMatching F0 F1 k := stepMatching_congr (by omega)
       rw [hjk]
       rcases Nat.lt_or_ge k q with hlt | hge
       · have h1 := hne k hpk hkq
         have h2 := hne (k + 1) (by omega) hlt
         rw [alt_succ] at h2
         rw [switch_mate_of_ne _ h1.1 h1.2 h2.1 h2.2, ← alt_succ]
         exact himg _ (by omega) hlt
       · obtain rfl : k = q := le_antisymm hkq hge
         rw [hkey']
         exact himg _ le_rfl hpq)
    | (obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
       have hjk : stepMatching F0 F1 j = stepMatching F0 F1 k' := stepMatching_congr (by omega)
       rw [hjk]
       rcases Nat.lt_or_ge p' k' with hlt | hge
       · have h1 := hne (k' + 1) hpk hkq
         have h2 := hne k' (by omega) (by omega)
         rw [← mate_alt_succ (F0 := F0) (F1 := F1) v k'] at h2
         rw [switch_mate_of_ne _ h1.1 h1.2 h2.1 h2.2, mate_alt_succ]
         exact himg _ (by omega) (by omega)
       · obtain rfl : k' = p' := le_antisymm hge (by omega)
         rw [hc, hkey]
         exact himg _ (by omega) le_rfl)

/-- The cycles of `F₀ ∪ F₁` that avoid `v` and `u` (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
def avoidCycles (F0 F1 : PerfectMatching V) (v u : V) : Finset (Finset V) :=
  (univ.image (cycleOf F0 F1)).filter fun S ↦ v ∉ S ∧ u ∉ S

/-- The type of the reduced pair: the new blocks inside the cycles of `v` and `u`, plus the cycles
avoiding both (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem pairType_red {v u : V} (hvu : v ≠ u) (𝓝 : Finset (Finset (redSet v u)))
    (hS : ∀ N ∈ 𝓝, ∀ X ∈ N, (red F0 hvu).mate X ∈ N ∧ (red F1 hvu).mate X ∈ N)
    (hc : ∀ N ∈ 𝓝, ∀ X ∈ N, ∀ Y ∈ N,
      ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable X Y)
    (hne : ∀ N ∈ 𝓝, N.Nonempty)
    (hsub : ∀ N ∈ 𝓝, ∀ X ∈ N, (X : V) ∈ cycleOf F0 F1 v ∨ (X : V) ∈ cycleOf F0 F1 u)
    (hcov : ∀ X : redSet v u, (X : V) ∈ cycleOf F0 F1 v ∨ (X : V) ∈ cycleOf F0 F1 u →
      ∃ N ∈ 𝓝, X ∈ N) :
    pairType (red F0 hvu) (red F1 hvu) =
      𝓝.val.map (fun N ↦ #N / 2) + (avoidCycles F0 F1 v u).val.map (fun S ↦ #S / 2) := by
  set 𝓔 := avoidCycles F0 F1 v u with h𝓔
  have hmemE : ∀ S ∈ 𝓔, (∃ w, cycleOf F0 F1 w = S) ∧ v ∉ S ∧ u ∉ S := by
    intro S hS
    simpa [h𝓔, avoidCycles] using hS
  have hin : ∀ S ∈ 𝓔, ∀ x ∈ S, x ∈ redSet v u := by
    intro S hS x hx
    obtain ⟨-, hvS, huS⟩ := hmemE S hS
    exact mem_redSet.mpr ⟨fun h ↦ hvS (h ▸ hx), fun h ↦ huS (h ▸ hx)⟩
  let sub : Finset V → Finset (redSet v u) := fun S ↦ S.subtype (· ∈ redSet v u)
  have hdisj : Disjoint 𝓝 (𝓔.image sub) := by
    rw [Finset.disjoint_left]
    intro N hN hN'
    obtain ⟨S, hSE, rfl⟩ := mem_image.mp hN'
    obtain ⟨X, hX⟩ := hne _ hN
    have h2 : (X : V) ∈ S := mem_subtype.mp hX
    obtain ⟨⟨w, rfl⟩, hvS, huS⟩ := hmemE S hSE
    have hw := cycleOf_eq_of_mem h2
    rcases hsub _ hN X hX with h | h
    · exact hvS (by rw [← hw, cycleOf_eq_of_mem h]; exact mem_cycleOf_self v)
    · exact huS (by rw [← hw, cycleOf_eq_of_mem h]; exact mem_cycleOf_self u)
  have hinj : Set.InjOn sub 𝓔 := by
    intro S hS T hT hST
    ext x
    by_cases hx : x ∈ redSet v u
    · have := congrArg (fun N ↦ (⟨x, hx⟩ : redSet v u) ∈ N) hST
      simpa [sub, mem_subtype] using this
    · exact ⟨fun h ↦ absurd (hin S hS x h) hx, fun h ↦ absurd (hin T hT x h) hx⟩
  rw [pairType_eq_of_blocks (𝓑 := 𝓝.disjUnion (𝓔.image sub) hdisj)]
  · change (𝓝.val + (𝓔.image sub).val).map _ = _
    rw [Multiset.map_add, image_val_of_injOn hinj, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun S hS ↦ ?_
    simp only [Function.comp_apply, sub, card_subtype]
    rw [filter_true_of_mem (hin S hS)]
  · intro N hN
    rcases mem_disjUnion.mp hN with hN | hN
    · exact hS N hN
    · obtain ⟨S, hSE, rfl⟩ := mem_image.mp hN
      obtain ⟨⟨w, rfl⟩, hvS, huS⟩ := hmemE _ hSE
      rintro ⟨x, hx⟩ hX
      have hxS : x ∈ cycleOf F0 F1 w := mem_subtype.mp hX
      have hcl := fun y (hy : y ∈ cycleOf F0 F1 w) ↦ mate_mem_cycleOf hy
      refine ⟨mem_subtype.mpr ?_, mem_subtype.mpr ?_⟩
      · rw [red_mate_coe, switch_mate_of_avoid hcl hvS huS (Or.inl rfl) hxS]
        exact (mate_mem_cycleOf hxS).1
      · rw [red_mate_coe, switch_mate_of_avoid hcl hvS huS (Or.inr rfl) hxS]
        exact (mate_mem_cycleOf hxS).2
  · intro N hN
    rcases mem_disjUnion.mp hN with hN | hN
    · exact hc N hN
    · obtain ⟨S, hSE, rfl⟩ := mem_image.mp hN
      obtain ⟨⟨w, rfl⟩, hvS, huS⟩ := hmemE _ hSE
      rintro ⟨x, hx⟩ hX ⟨y, hy⟩ hY
      have hxS : x ∈ cycleOf F0 F1 w := mem_subtype.mp hX
      have hyS : y ∈ cycleOf F0 F1 w := mem_subtype.mp hY
      exact reachable_red_of_avoid (fun z hz ↦ mate_mem_cycleOf hz) hvu hvS huS
        ((mem_cycleOf.mp hxS).symm.trans (mem_cycleOf.mp hyS)) hxS hx hy
  · intro N hN
    rcases mem_disjUnion.mp hN with hN | hN
    · exact hne N hN
    · obtain ⟨S, hSE, rfl⟩ := mem_image.mp hN
      obtain ⟨⟨w, rfl⟩, hvS, huS⟩ := hmemE _ hSE
      have hw : w ∈ redSet v u := hin _ hSE w (mem_cycleOf_self w)
      exact ⟨⟨w, hw⟩, mem_subtype.mpr (mem_cycleOf_self w)⟩
  · intro X
    by_cases hX : (X : V) ∈ cycleOf F0 F1 v ∨ (X : V) ∈ cycleOf F0 F1 u
    · obtain ⟨N, hN, hXN⟩ := hcov X hX
      exact ⟨N, mem_disjUnion.mpr (Or.inl hN), hXN⟩
    · simp only [not_or] at hX
      refine ⟨sub (cycleOf F0 F1 X), mem_disjUnion.mpr (Or.inr (mem_image.mpr
        ⟨cycleOf F0 F1 X, ?_, rfl⟩)), mem_subtype.mpr (mem_cycleOf_self _)⟩
      simp only [h𝓔, avoidCycles, mem_filter, mem_image, mem_univ, true_and]
      exact ⟨⟨X, rfl⟩, fun h ↦ hX.1 (mem_cycleOf_comm.mp h),
        fun h ↦ hX.2 (mem_cycleOf_comm.mp h)⟩

/-- Removing one block removes its part from the multiset of parts
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem map_erase_val {β : Type*} [DecidableEq β] (𝓑 : Finset β) {C : β} (hC : C ∈ 𝓑)
    (f : β → ℕ) : (𝓑.erase C).val.map f = (𝓑.val.map f).erase (f C) := by
  conv_rhs => rw [← Multiset.cons_erase (Finset.mem_val.mpr hC)]
  rw [Multiset.map_cons, Multiset.erase_cons_head, Finset.erase_val]

/-- The cycle through `v` is one of the cycles (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cycleOf_mem_image (v : V) : cycleOf F0 F1 v ∈ univ.image (cycleOf F0 F1) :=
  mem_image_of_mem _ (mem_univ v)

/-- For `u` on the cycle of `v`, the cycles avoiding both are all others
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem avoidCycles_of_mem {v u : V} (hu : u ∈ cycleOf F0 F1 v) :
    avoidCycles F0 F1 v u = (univ.image (cycleOf F0 F1)).erase (cycleOf F0 F1 v) := by
  ext S
  simp only [avoidCycles, mem_filter, mem_erase, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨w, rfl⟩, hv, -⟩
    exact ⟨fun h ↦ hv (h ▸ mem_cycleOf_self v), w, rfl⟩
  · rintro ⟨hne, w, rfl⟩
    refine ⟨⟨w, rfl⟩, fun h ↦ hne (cycleOf_eq_of_mem (mem_cycleOf_comm.mp h)), fun h ↦ hne ?_⟩
    exact (cycleOf_eq_of_mem h).symm.trans (cycleOf_eq_of_mem hu)

/-- The cycles avoiding `v` and `u` are those other than the cycles of `v` and `u`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem avoidCycles_eq (v u : V) :
    avoidCycles F0 F1 v u =
      ((univ.image (cycleOf F0 F1)).erase (cycleOf F0 F1 v)).erase (cycleOf F0 F1 u) := by
  ext S
  simp only [avoidCycles, mem_filter, mem_erase, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨w, rfl⟩, hv, hu'⟩
    exact ⟨fun h ↦ hu' (h ▸ mem_cycleOf_self u), fun h ↦ hv (h ▸ mem_cycleOf_self v), w, rfl⟩
  · rintro ⟨hne2, hne1, w, rfl⟩
    exact ⟨⟨w, rfl⟩, fun h ↦ hne1 (cycleOf_eq_of_mem (mem_cycleOf_comm.mp h)),
      fun h ↦ hne2 (cycleOf_eq_of_mem (mem_cycleOf_comm.mp h))⟩

/-- For `u` on the cycle of `v`, the cycles avoiding both have type `μ - a`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem map_avoidCycles_of_mem {v u : V} (hu : u ∈ cycleOf F0 F1 v) :
    (avoidCycles F0 F1 v u).val.map (fun S ↦ #S / 2) =
      (pairType F0 F1).erase (#(cycleOf F0 F1 v) / 2) := by
  rw [avoidCycles_of_mem hu, map_erase_val _ (cycleOf_mem_image v), pairType]

/-- For `u` off the cycle of `v`, the cycles avoiding both have type `μ - a - b`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem map_avoidCycles_of_notMem {v u : V} (hu : u ∉ cycleOf F0 F1 v) :
    (avoidCycles F0 F1 v u).val.map (fun S ↦ #S / 2) =
      ((pairType F0 F1).erase (#(cycleOf F0 F1 v) / 2)).erase (#(cycleOf F0 F1 u) / 2) := by
  have hne : cycleOf F0 F1 u ≠ cycleOf F0 F1 v := fun h ↦ hu (h ▸ mem_cycleOf_self u)
  rw [avoidCycles_eq, map_erase_val _ (mem_erase.mpr ⟨hne, cycleOf_mem_image u⟩),
    map_erase_val _ (cycleOf_mem_image v), pairType]

end RedBlocks

section TypeChange

variable [Fintype V] [DecidableEq V] {F0 F1 : PerfectMatching V}

/-- Removing `v` and `u` from a set containing both removes two vertices
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem card_filter_redSet {S : Finset V} {v u : V} (hvu : v ≠ u) (hv : v ∈ S) (hu : u ∈ S) :
    #(S.filter (· ∈ redSet v u)) = #S - 2 := by
  have h : S.filter (· ∈ redSet v u) = (S.erase v).erase u := by
    ext x
    simp only [mem_filter, mem_redSet, mem_erase]
    tauto
  rw [h, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hvu, hu⟩), card_erase_of_mem hv]
  omega

/-- Lemma K2, even distance: for `u = c_d` with `d ∈ {2, 4, …, 2a - 2}` the reduced pair has
the type `μ` with `a` replaced by `a - 1` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem redType_of_even (v : V) {a d : ℕ} (ha : #(cycleOf F0 F1 v) = 2 * a) (hd2 : 2 ≤ d)
    (hd : d ≤ 2 * a - 2) (he : d % 2 = 0) :
    redType F0 F1 v (alt F0 F1 v d) = (a - 1) ::ₘ (pairType F0 F1).erase a := by
  have hL : cycLen F0 F1 v = 2 * a := by rw [← card_cycleOf, ha]
  have hdL : d < cycLen F0 F1 v := by omega
  have hvu : v ≠ alt F0 F1 v d := (alt_ne_self (by omega) hdL).symm
  have huC : alt F0 F1 v d ∈ cycleOf F0 F1 v := mem_cycleOf_alt v d
  have hmem : ∀ j, 0 < j → j < 2 * a → j ≠ d → alt F0 F1 v j ∈ redSet v (alt F0 F1 v d) :=
    fun j h0 h1 h2 ↦ alt_mem_redSet hdL h0 (by omega) h2
  have hcl := fun y (hy : y ∈ cycleOf F0 F1 v) ↦ mate_mem_cycleOf (F0 := F0) (F1 := F1) hy
  have ha2 : #(cycleOf F0 F1 v) / 2 = a := by omega
  rw [redType, dite_eq_right hvu]
  let N : Finset (redSet v (alt F0 F1 v d)) := (cycleOf F0 F1 v).subtype (· ∈ redSet v _)
  have h1mem := hmem 1 one_pos (by omega) (by omega)
  have hreach : ∀ X ∈ N, ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable
      ⟨alt F0 F1 v 1, h1mem⟩ X := by
    rintro ⟨x, hx⟩ hX
    obtain ⟨k, hkL, rfl⟩ := exists_lt_of_mem_cycleOf (mem_subtype.mp hX)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (mem_redSet.mp hx).1 rfl
    have hkd : k ≠ d := by
      rintro rfl
      exact (mem_redSet.mp hx).2 rfl
    rcases Nat.lt_or_gt_of_ne hkd with hlt | hgt
    · exact reachable_red_alt' hvu v (p := 1) (q := k) (by omega)
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
    · have hA := reachable_red_alt' hvu v (p := 1) (q := d - 1) (by omega)
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      have hB := reachable_red_alt' hvu v (p := k) (q := 2 * a - 1) (by omega)
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      have hedge : ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Adj
          ⟨alt F0 F1 v (d - 1), hmem (d - 1) (by omega) (by omega) (by omega)⟩
          ⟨alt F0 F1 v (2 * a - 1), hmem (2 * a - 1) (by omega) (by omega) (by omega)⟩ := by
        refine Or.inr (Subtype.ext ?_)
        change (switch F1 v (alt F0 F1 v d)).mate (alt F0 F1 v (d - 1)) = alt F0 F1 v (2 * a - 1)
        have e1 : F1.mate (alt F0 F1 v d) = alt F0 F1 v (d - 1) := by
          have h := mate_alt_succ (F0 := F0) (F1 := F1) v (d - 1)
          rwa [Nat.sub_add_cancel (by omega : 1 ≤ d), stepMatching_of_odd (by omega)] at h
        rw [← e1, switch_mate_mate_right _ hvu, mate_one_eq_alt_pred (F0 := F0) v, hL]
      exact hA.trans (hedge.reachable.trans hB.symm)
  rw [pairType_red hvu {N}, map_avoidCycles_of_mem huC, ha2]
  · simp only [Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_add]
    congr 1
    rw [card_subtype, card_filter_redSet hvu (mem_cycleOf_self v) huC, ha]
    omega
  · intro N' hN'
    rw [mem_singleton] at hN'
    subst hN'
    rintro ⟨x, hx⟩ hX
    exact ⟨mem_subtype.mpr (switch_mem_of_closed hcl hvu (mem_cycleOf_self v) huC (Or.inl rfl)
      (mem_subtype.mp hX)), mem_subtype.mpr (switch_mem_of_closed hcl hvu (mem_cycleOf_self v)
      huC (Or.inr rfl) (mem_subtype.mp hX))⟩
  · intro N' hN' X hX Y hY
    rw [mem_singleton] at hN'
    subst hN'
    exact (hreach X hX).symm.trans (hreach Y hY)
  · intro N' hN'
    rw [mem_singleton] at hN'
    subst hN'
    exact ⟨⟨alt F0 F1 v 1, h1mem⟩, mem_subtype.mpr (mem_cycleOf_alt v 1)⟩
  · intro N' hN' X hX
    rw [mem_singleton] at hN'
    subst hN'
    exact Or.inl (mem_subtype.mp hX)
  · intro X hX
    refine ⟨N, mem_singleton_self _, mem_subtype.mpr ?_⟩
    rcases hX with h | h
    · exact h
    · rwa [cycleOf_eq_of_mem huC] at h

/-- Lemma K2, odd distance: for `u = c_{2x+1}` with `1 ≤ x ≤ a - 2` the reduced pair has the
type `μ` with `a` split into `x` and `a - 1 - x` (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem redType_of_odd (v : V) {a x : ℕ} (ha : #(cycleOf F0 F1 v) = 2 * a) (hx1 : 1 ≤ x)
    (hx : x ≤ a - 2) :
    redType F0 F1 v (alt F0 F1 v (2 * x + 1)) = x ::ₘ (a - 1 - x) ::ₘ (pairType F0 F1).erase a := by
  have hL : cycLen F0 F1 v = 2 * a := by rw [← card_cycleOf, ha]
  have hdL : 2 * x + 1 < cycLen F0 F1 v := by omega
  have hvu : v ≠ alt F0 F1 v (2 * x + 1) := (alt_ne_self (by omega) hdL).symm
  have huC : alt F0 F1 v (2 * x + 1) ∈ cycleOf F0 F1 v := mem_cycleOf_alt v _
  have hmem : ∀ j, 0 < j → j < 2 * a → j ≠ 2 * x + 1 →
      alt F0 F1 v j ∈ redSet v (alt F0 F1 v (2 * x + 1)) :=
    fun j h0 h1 h2 ↦ alt_mem_redSet hdL h0 (by omega) h2
  have ha2 : #(cycleOf F0 F1 v) / 2 = a := by omega
  have hinj : Set.InjOn (alt F0 F1 v) (Set.Iio (2 * a)) := fun i hi j hj h ↦
    alt_injOn (by rw [hL]; exact hi) (by rw [hL]; exact hj) h
  rw [redType, dite_eq_right hvu]
  let N1 : Finset (redSet v (alt F0 F1 v (2 * x + 1))) :=
    ((Icc 1 (2 * x)).image (alt F0 F1 v)).subtype (· ∈ redSet v (alt F0 F1 v (2 * x + 1)))
  let N2 : Finset (redSet v (alt F0 F1 v (2 * x + 1))) :=
    ((Icc (2 * x + 2) (2 * a - 1)).image (alt F0 F1 v)).subtype
      (· ∈ redSet v (alt F0 F1 v (2 * x + 1)))
  have hN1 : ∀ y (hy : y ∈ redSet v (alt F0 F1 v (2 * x + 1))),
      (⟨y, hy⟩ : redSet v (alt F0 F1 v (2 * x + 1))) ∈ N1 ↔
      ∃ k, 1 ≤ k ∧ k ≤ 2 * x ∧ alt F0 F1 v k = y := by
    intro y hy
    simp [N1, mem_subtype, and_assoc]
  have hN2 : ∀ y (hy : y ∈ redSet v (alt F0 F1 v (2 * x + 1))),
      (⟨y, hy⟩ : redSet v (alt F0 F1 v (2 * x + 1))) ∈ N2 ↔
      ∃ k, 2 * x + 2 ≤ k ∧ k ≤ 2 * a - 1 ∧ alt F0 F1 v k = y := by
    intro y hy
    simp [N2, mem_subtype, and_assoc]
  have hseg1 := fun j k (h1 : 1 ≤ k) (h2 : k ≤ 2 * x) ↦ switch_mem_segment (F0 := F0) (F1 := F1)
    hvu (p := 1) (q := 2 * x) le_rfl (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩)
    (fun k h1 h2 ↦ hmem k (by omega) (by omega) (by omega)) j h1 h2
  have hv2 : alt F0 F1 v (2 * a - 1 + 1) = v := by
    rw [Nat.sub_add_cancel (by omega), ← hL, alt_cycLen]
  have hseg2 := fun j k (h1 : 2 * x + 2 ≤ k) (h2 : k ≤ 2 * a - 1) ↦ switch_mem_segment
    (F0 := F0) (F1 := F1) hvu (p := 2 * x + 2) (q := 2 * a - 1) (by omega) (by omega) (by omega)
    (Or.inr ⟨rfl, hv2⟩) (fun k h1 h2 ↦ hmem k (by omega) (by omega) (by omega)) j h1 h2
  have hsw0 : stepMatching F0 F1 0 = F0 := stepMatching_of_even (by norm_num)
  have hsw1 : stepMatching F0 F1 1 = F1 := stepMatching_of_odd (by norm_num)
  have hne12 : N1 ≠ N2 := by
    intro h
    have h1 : (⟨alt F0 F1 v 1, hmem 1 one_pos (by omega) (by omega)⟩ :
        redSet v (alt F0 F1 v (2 * x + 1))) ∈ N1 :=
      (hN1 _ _).mpr ⟨1, le_rfl, by omega, rfl⟩
    rw [h] at h1
    obtain ⟨k, hk1, hk2, hk⟩ := (hN2 _ _).mp h1
    have := hinj (show k ∈ Set.Iio (2 * a) by simp; omega)
      (show 1 ∈ Set.Iio (2 * a) by simp; omega) hk
    omega
  have hpair : ({N1, N2} : Finset (Finset (redSet v (alt F0 F1 v (2 * x + 1))))).val =
      N1 ::ₘ N2 ::ₘ 0 := by
    rw [insert_val_of_notMem (by simpa using hne12)]
    rfl
  rw [pairType_red hvu {N1, N2}, map_avoidCycles_of_mem huC, ha2, hpair]
  · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.cons_add, Multiset.zero_add]
    have hc1 : #N1 = 2 * x := by
      rw [card_subtype, filter_true_of_mem, card_image_of_injOn, Nat.card_Icc]
      · omega
      · exact fun i hi j hj h ↦ hinj (by simp at hi ⊢; omega) (by simp at hj ⊢; omega) h
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
        rw [mem_Icc] at hk
        exact hmem k (by omega) (by omega) (by omega)
    have hc2 : #N2 = 2 * a - 2 * x - 2 := by
      rw [card_subtype, filter_true_of_mem, card_image_of_injOn, Nat.card_Icc]
      · omega
      · exact fun i hi j hj h ↦ hinj (by simp at hi ⊢; omega) (by simp at hj ⊢; omega) h
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
        rw [mem_Icc] at hk
        exact hmem k (by omega) (by omega) (by omega)
    rw [hc1, hc2]
    congr 2 <;> omega
  · intro N' hN'
    rcases mem_insert.mp hN' with rfl | hN'
    · rintro ⟨y, hy⟩ hX
      obtain ⟨k, hk1, hk2, rfl⟩ := (hN1 y hy).mp hX
      have h0 := hseg1 0 k hk1 hk2
      have h1 := hseg1 1 k hk1 hk2
      rw [hsw0] at h0
      rw [hsw1] at h1
      exact ⟨mem_subtype.mpr h0, mem_subtype.mpr h1⟩
    · rw [mem_singleton] at hN'
      subst hN'
      rintro ⟨y, hy⟩ hX
      obtain ⟨k, hk1, hk2, rfl⟩ := (hN2 y hy).mp hX
      have h0 := hseg2 0 k hk1 hk2
      have h1 := hseg2 1 k hk1 hk2
      rw [hsw0] at h0
      rw [hsw1] at h1
      exact ⟨mem_subtype.mpr h0, mem_subtype.mpr h1⟩
  · rintro N' hN' ⟨y, hy⟩ hX ⟨z, hz⟩ hY
    rcases mem_insert.mp hN' with rfl | hN'
    · obtain ⟨k, hk1, hk2, rfl⟩ := (hN1 y hy).mp hX
      obtain ⟨l, hl1, hl2, rfl⟩ := (hN1 z hz).mp hY
      have hk := reachable_red_alt' hvu v (p := 1) (q := k) hk1
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      have hl := reachable_red_alt' hvu v (p := 1) (q := l) hl1
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      exact hk.symm.trans hl
    · rw [mem_singleton] at hN'
      subst hN'
      obtain ⟨k, hk1, hk2, rfl⟩ := (hN2 y hy).mp hX
      obtain ⟨l, hl1, hl2, rfl⟩ := (hN2 z hz).mp hY
      have hk := reachable_red_alt' hvu v (p := 2 * x + 2) (q := k) hk1
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      have hl := reachable_red_alt' hvu v (p := 2 * x + 2) (q := l) hl1
        fun j h1 h2 ↦ hmem j (by omega) (by omega) (by omega)
      exact hk.symm.trans hl
  · intro N' hN'
    rcases mem_insert.mp hN' with rfl | hN'
    · exact ⟨⟨alt F0 F1 v 1, hmem 1 one_pos (by omega) (by omega)⟩,
        (hN1 _ _).mpr ⟨1, le_rfl, by omega, rfl⟩⟩
    · rw [mem_singleton] at hN'
      subst hN'
      exact ⟨⟨alt F0 F1 v (2 * x + 2), hmem _ (by omega) (by omega) (by omega)⟩,
        (hN2 _ _).mpr ⟨2 * x + 2, le_rfl, by omega, rfl⟩⟩
  · rintro N' hN' ⟨y, hy⟩ hX
    left
    rcases mem_insert.mp hN' with rfl | hN'
    · obtain ⟨k, -, -, rfl⟩ := (hN1 y hy).mp hX
      exact mem_cycleOf_alt v k
    · rw [mem_singleton] at hN'
      subst hN'
      obtain ⟨k, -, -, rfl⟩ := (hN2 y hy).mp hX
      exact mem_cycleOf_alt v k
  · rintro ⟨y, hy⟩ hX
    have hyC : y ∈ cycleOf F0 F1 v := by
      rcases hX with h | h
      · exact h
      · rwa [cycleOf_eq_of_mem huC] at h
    obtain ⟨k, hkL, rfl⟩ := exists_lt_of_mem_cycleOf hyC
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (mem_redSet.mp hy).1 rfl
    have hkd : k ≠ 2 * x + 1 := by
      rintro rfl
      exact (mem_redSet.mp hy).2 rfl
    rcases Nat.lt_or_gt_of_ne hkd with hlt | hgt
    · exact ⟨N1, mem_insert_self _ _, (hN1 _ _).mpr ⟨k, by omega, by omega, rfl⟩⟩
    · exact ⟨N2, mem_insert_of_mem (mem_singleton_self _),
        (hN2 _ _).mpr ⟨k, by omega, by omega, rfl⟩⟩

/-- Lemma K2, another cycle: for `u` in a cycle of half-length `b` other than that of `v`, the
reduced pair has the type `μ` with `a` and `b` merged into `a + b - 1`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem redType_of_notMem {v u : V} (hu : u ∉ cycleOf F0 F1 v) {a b : ℕ}
    (ha : #(cycleOf F0 F1 v) = 2 * a) (hb : #(cycleOf F0 F1 u) = 2 * b) :
    redType F0 F1 v u = (a + b - 1) ::ₘ ((pairType F0 F1).erase a).erase b := by
  have hLv : cycLen F0 F1 v = 2 * a := by rw [← card_cycleOf, ha]
  have hLu : cycLen F0 F1 u = 2 * b := by rw [← card_cycleOf, hb]
  have hvu : v ≠ u := fun h ↦ hu (h ▸ mem_cycleOf_self v)
  have hvU : v ∉ cycleOf F0 F1 u := fun h ↦ hu (mem_cycleOf_comm.mp h)
  have hapos : 0 < a := by have := cycLen_pos (F0 := F0) (F1 := F1) v; omega
  have hbpos : 0 < b := by have := cycLen_pos (F0 := F0) (F1 := F1) u; omega
  have ha2 : #(cycleOf F0 F1 v) / 2 = a := by omega
  have hb2 : #(cycleOf F0 F1 u) / 2 = b := by omega
  have hmemv : ∀ j, 0 < j → j < 2 * a → alt F0 F1 v j ∈ redSet v u := fun j h0 h1 ↦
    mem_redSet.mpr ⟨alt_ne_self h0 (by omega), fun h ↦ hu (h ▸ mem_cycleOf_alt v j)⟩
  have hmemu : ∀ j, 0 < j → j < 2 * b → alt F0 F1 u j ∈ redSet v u := fun j h0 h1 ↦
    mem_redSet.mpr ⟨fun h ↦ hvU (h ▸ mem_cycleOf_alt u j), alt_ne_self h0 (by omega)⟩
  have hdisj : Disjoint (cycleOf F0 F1 v) (cycleOf F0 F1 u) := by
    rw [Finset.disjoint_left]
    intro y hyv hyu
    exact hu (by rw [← cycleOf_eq_of_mem hyv, cycleOf_eq_of_mem hyu]; exact mem_cycleOf_self u)
  have hcl : ∀ y ∈ cycleOf F0 F1 v ∪ cycleOf F0 F1 u,
      F0.mate y ∈ cycleOf F0 F1 v ∪ cycleOf F0 F1 u ∧
        F1.mate y ∈ cycleOf F0 F1 v ∪ cycleOf F0 F1 u := by
    intro y hy
    rcases mem_union.mp hy with h | h
    · exact ⟨mem_union_left _ (mate_mem_cycleOf h).1, mem_union_left _ (mate_mem_cycleOf h).2⟩
    · exact ⟨mem_union_right _ (mate_mem_cycleOf h).1, mem_union_right _ (mate_mem_cycleOf h).2⟩
  rw [redType, dite_eq_right hvu]
  let N : Finset (redSet v u) := (cycleOf F0 F1 v ∪ cycleOf F0 F1 u).subtype (· ∈ redSet v u)
  have h1v := hmemv 1 one_pos (by omega)
  have h1u := hmemu 1 one_pos (by omega)
  have hedge : ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Adj ⟨alt F0 F1 v 1, h1v⟩
      ⟨alt F0 F1 u 1, h1u⟩ := by
    refine Or.inl (Subtype.ext ?_)
    change (switch F0 v u).mate (alt F0 F1 v 1) = alt F0 F1 u 1
    rw [← mate_zero_eq_alt_one (F1 := F1), ← mate_zero_eq_alt_one (F1 := F1),
      switch_mate_mate_self _ hvu]
  have hreach : ∀ X ∈ N, ((red F0 hvu).toGraph ⊔ (red F1 hvu).toGraph).Reachable
      ⟨alt F0 F1 v 1, h1v⟩ X := by
    rintro ⟨y, hy⟩ hX
    rcases mem_union.mp (mem_subtype.mp hX) with h | h
    · obtain ⟨k, hkL, rfl⟩ := exists_lt_of_mem_cycleOf h
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact (mem_redSet.mp hy).1 rfl
      exact reachable_red_alt' hvu v (p := 1) (q := k) (by omega)
        fun j h1 h2 ↦ hmemv j (by omega) (by omega)
    · obtain ⟨k, hkL, rfl⟩ := exists_lt_of_mem_cycleOf h
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact (mem_redSet.mp hy).2 rfl
      exact hedge.reachable.trans (reachable_red_alt' hvu u (p := 1) (q := k) (by omega)
        fun j h1 h2 ↦ hmemu j (by omega) (by omega))
  rw [pairType_red hvu {N}, map_avoidCycles_of_notMem hu, ha2, hb2]
  · simp only [Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_add]
    congr 1
    rw [card_subtype, card_filter_redSet hvu (mem_union_left _ (mem_cycleOf_self v))
      (mem_union_right _ (mem_cycleOf_self u)), card_union_of_disjoint hdisj, ha, hb]
    omega
  · intro N' hN'
    rw [mem_singleton] at hN'
    subst hN'
    rintro ⟨y, hy⟩ hX
    have hv' := mem_union_left (cycleOf F0 F1 u) (mem_cycleOf_self (F0 := F0) (F1 := F1) v)
    have hu' := mem_union_right (cycleOf F0 F1 v) (mem_cycleOf_self (F0 := F0) (F1 := F1) u)
    exact ⟨mem_subtype.mpr (switch_mem_of_closed hcl hvu hv' hu' (Or.inl rfl)
      (mem_subtype.mp hX)), mem_subtype.mpr (switch_mem_of_closed hcl hvu hv' hu' (Or.inr rfl)
      (mem_subtype.mp hX))⟩
  · intro N' hN' X hX Y hY
    rw [mem_singleton] at hN'
    subst hN'
    exact (hreach X hX).symm.trans (hreach Y hY)
  · intro N' hN'
    rw [mem_singleton] at hN'
    subst hN'
    exact ⟨⟨alt F0 F1 v 1, h1v⟩, mem_subtype.mpr (mem_union_left _ (mem_cycleOf_alt v 1))⟩
  · intro N' hN' X hX
    rw [mem_singleton] at hN'
    subst hN'
    exact mem_union.mp (mem_subtype.mp hX)
  · intro X hX
    exact ⟨N, mem_singleton_self _, mem_subtype.mpr (mem_union.mpr hX)⟩

end TypeChange

section Recursion

/-- One step of the Lemma K2 recursion at a part `a` of `μ`. The `a - 1` partners at even
distance give `μ - a + (a - 1)`, the partner at distance `2x + 1`, `1 ≤ x ≤ a - 2`, gives
`μ - a + x + (a - 1 - x)`, and the `2b` partners in each other cycle of half-length `b` give
`μ - a - b + (a + b - 1)` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
def k2Step (g : Multiset ℕ → ℕ) (μ : Multiset ℕ) (a : ℕ) : ℕ :=
  (a - 1) * g ((a - 1) ::ₘ μ.erase a) +
    ∑ x ∈ Icc 1 (a - 2), g (x ::ₘ (a - 1 - x) ::ₘ μ.erase a) +
    ((μ.erase a).map fun b ↦ 2 * b * g ((a + b - 1) ::ₘ (μ.erase a).erase b)).sum

/-- The largest part of `μ`, the part at which `k2Aux` applies the recursion
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def maxPart (μ : Multiset ℕ) : ℕ :=
  μ.toFinset.sup id

/-- The Lemma K2 recursion for a type of size `j`, with value `1` at `j = 1`, that is at `(1)`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def k2Aux : ℕ → Multiset ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | j + 2, μ => k2Step (k2Aux (j + 1)) μ (maxPart μ)

/-- `N(μ)`, the count defined by the Lemma K2 recursion over partitions
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
def k2Count (μ : Multiset ℕ) : ℕ :=
  k2Aux μ.sum μ

/-- The largest part of a nonempty multiset is a part (`results/k3-counterexample-hunt.md`, Lemma
K2). -/
theorem maxPart_mem {μ : Multiset ℕ} (h : μ ≠ 0) : maxPart μ ∈ μ := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup μ.toFinset
    (Multiset.toFinset_nonempty.mpr h) id
  rw [maxPart, he]
  exact Multiset.mem_toFinset.mp hi

variable [Fintype V] [DecidableEq V] {F0 F1 : PerfectMatching V}

/-- The vertices whose cycle is `S` are the vertices of `S` (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem fiber_cycleOf {s : Finset V} {S : Finset V} (hS : ∃ w, cycleOf F0 F1 w = S)
    (hs : ∀ u ∈ S, u ∈ s) : #{u ∈ s | cycleOf F0 F1 u = S} = #S := by
  obtain ⟨w, rfl⟩ := hS
  congr 1
  ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨-, h⟩
    rw [← h]
    exact mem_cycleOf_self u
  · intro h
    exact ⟨hs u h, cycleOf_eq_of_mem h⟩

/-- `2 · |μ| = |V|`: the type of `(F₀, F₁)` is a partition of `|V| / 2`. -/
theorem two_mul_sum_pairType (F0 F1 : PerfectMatching V) :
    2 * (pairType F0 F1).sum = Fintype.card V := by
  rw [pairType, ← sum_eq_multiset_sum, mul_sum, ← card_univ,
    card_eq_sum_card_image (cycleOf F0 F1) univ]
  refine sum_congr rfl fun S hS ↦ ?_
  obtain ⟨w, -, rfl⟩ := mem_image.mp hS
  rw [fiber_cycleOf ⟨w, rfl⟩ fun u _ ↦ mem_univ u, two_mul_card_cycleOf_div_two]

/-- The recursion at the vertex `v`: given `N` of every reduced pair as `g` of its type, the sum
over the allowed partners of `v` is `k2Step g μ a` with `a` the half-length of the cycle of
`v` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem sum_redCount_eq_k2Step (F0 F1 : PerfectMatching V) (v : V) (g : Multiset ℕ → ℕ)
    (hg : ∀ u, v ≠ u → redCount F0 F1 v u = g (redType F0 F1 v u)) :
    ∑ u ∈ ((univ.erase v).erase (F0.mate v)).erase (F1.mate v), redCount F0 F1 v u =
      k2Step g (pairType F0 F1) (#(cycleOf F0 F1 v) / 2) := by
  set a := #(cycleOf F0 F1 v) / 2 with ha_def
  set μ := pairType F0 F1 with hμ
  have ha : #(cycleOf F0 F1 v) = 2 * a := (two_mul_card_cycleOf_div_two v).symm
  have hL : cycLen F0 F1 v = 2 * a := by rw [← card_cycleOf, ha]
  have hapos : 0 < a := by have := cycLen_pos (F0 := F0) (F1 := F1) v; omega
  have h0 : F0.mate v = alt F0 F1 v 1 := mate_zero_eq_alt_one v
  have h1 : F1.mate v = alt F0 F1 v (2 * a - 1) := by
    rw [mate_one_eq_alt_pred (F0 := F0) v, hL]
  have hinj : ∀ i j, i < 2 * a → j < 2 * a → alt F0 F1 v i = alt F0 F1 v j → i = j :=
    fun i j hi hj h ↦ alt_injOn (by rw [hL]; exact hi) (by rw [hL]; exact hj) h
  set A := ((univ.erase v).erase (F0.mate v)).erase (F1.mate v) with hA
  have hmemA : ∀ u, u ∈ A ↔ u ≠ F1.mate v ∧ u ≠ F0.mate v ∧ u ≠ v := by
    intro u
    simp [hA]
  rw [sum_congr rfl fun u hu ↦ hg u (Ne.symm ((hmemA u).mp hu).2.2),
    ← sum_filter_add_sum_filter_not A (· ∈ cycleOf F0 F1 v)]
  have hA1 : A.filter (· ∈ cycleOf F0 F1 v) = (Icc 2 (2 * a - 2)).image (alt F0 F1 v) := by
    ext u
    simp only [mem_filter, hmemA, mem_image, mem_Icc, h0, h1]
    constructor
    · rintro ⟨⟨hu1, hu0, huv⟩, hu⟩
      obtain ⟨k, hkL, rfl⟩ := exists_lt_of_mem_cycleOf hu
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · by_contra hk
        interval_cases k
        · exact huv rfl
        · exact hu0 rfl
      · by_contra hk
        exact hu1 (by rw [show k = 2 * a - 1 by omega])
    · rintro ⟨d, ⟨hd1, hd2⟩, rfl⟩
      refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_, alt_ne_self (by omega) (by omega)⟩, mem_cycleOf_alt v d⟩
      · have := hinj _ _ (by omega) (by omega) h
        omega
      · have := hinj _ _ (by omega) (by omega) h
        omega
  have hA2 : A.filter (fun u ↦ u ∉ cycleOf F0 F1 v) = univ.filter (· ∉ cycleOf F0 F1 v) := by
    ext u
    simp only [mem_filter, hmemA, mem_univ, true_and]
    constructor
    · exact fun h ↦ h.2
    · intro h
      refine ⟨⟨fun h' ↦ h ?_, fun h' ↦ h ?_, fun h' ↦ h ?_⟩, h⟩
      · rw [h']
        exact (mate_mem_cycleOf (mem_cycleOf_self v)).2
      · rw [h']
        exact (mate_mem_cycleOf (mem_cycleOf_self v)).1
      · rw [h']
        exact mem_cycleOf_self v
  rw [hA1, hA2, sum_image fun i hi j hj h ↦ hinj i j (by simp at hi; omega)
    (by simp at hj; omega) h, ← sum_filter_add_sum_filter_not (Icc 2 (2 * a - 2)) (· % 2 = 0)]
  have hE : (Icc 2 (2 * a - 2)).filter (· % 2 = 0) = (Icc 1 (a - 1)).image (2 * ·) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨d / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      omega
  have hO : (Icc 2 (2 * a - 2)).filter (fun d ↦ ¬d % 2 = 0) =
      (Icc 1 (a - 2)).image (2 * · + 1) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨d / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      omega
  rw [hE, hO, sum_image fun i _ j _ h ↦ Nat.eq_of_mul_eq_mul_left two_pos h,
    sum_image fun i _ j _ h ↦ Nat.eq_of_mul_eq_mul_left two_pos (Nat.add_right_cancel h)]
  have hEsum : ∑ i ∈ Icc 1 (a - 1), g (redType F0 F1 v (alt F0 F1 v (2 * i))) =
      (a - 1) * g ((a - 1) ::ₘ μ.erase a) := by
    have hc : ∀ i ∈ Icc 1 (a - 1), g (redType F0 F1 v (alt F0 F1 v (2 * i))) =
        g ((a - 1) ::ₘ μ.erase a) := by
      intro i hi
      rw [mem_Icc] at hi
      rw [redType_of_even v ha (d := 2 * i) (by omega) (by omega) (by omega)]
    rw [sum_congr rfl hc, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
  have hOsum : ∑ x ∈ Icc 1 (a - 2), g (redType F0 F1 v (alt F0 F1 v (2 * x + 1))) =
      ∑ x ∈ Icc 1 (a - 2), g (x ::ₘ (a - 1 - x) ::ₘ μ.erase a) := by
    refine sum_congr rfl fun x hx ↦ ?_
    rw [mem_Icc] at hx
    rw [redType_of_odd v ha hx.1 hx.2]
  rw [hEsum, hOsum, k2Step]
  congr 1
  have hmaps : ∀ u ∈ univ.filter (· ∉ cycleOf F0 F1 v),
      cycleOf F0 F1 u ∈ (univ.image (cycleOf F0 F1)).erase (cycleOf F0 F1 v) := by
    intro u hu
    refine mem_erase.mpr ⟨fun h ↦ (mem_filter.mp hu).2 ?_, cycleOf_mem_image u⟩
    rw [← h]
    exact mem_cycleOf_self u
  let G : ℕ → ℕ := fun b ↦ g ((a + b - 1) ::ₘ (μ.erase a).erase b)
  calc ∑ u ∈ univ.filter (· ∉ cycleOf F0 F1 v), g (redType F0 F1 v u)
      = ∑ u ∈ univ.filter (· ∉ cycleOf F0 F1 v), (fun S ↦ G (#S / 2)) (cycleOf F0 F1 u) := by
        refine sum_congr rfl fun u hu ↦ ?_
        rw [redType_of_notMem (mem_filter.mp hu).2 ha (two_mul_card_cycleOf_div_two u).symm]
    _ = ∑ S ∈ (univ.image (cycleOf F0 F1)).erase (cycleOf F0 F1 v),
          ∑ u ∈ univ.filter (· ∉ cycleOf F0 F1 v) with cycleOf F0 F1 u = S, G (#S / 2) :=
        (sum_fiberwise_of_maps_to' hmaps (fun S ↦ G (#S / 2))).symm
    _ = ∑ S ∈ (univ.image (cycleOf F0 F1)).erase (cycleOf F0 F1 v), 2 * (#S / 2) * G (#S / 2) := by
        refine sum_congr rfl fun S hS ↦ ?_
        obtain ⟨hne, hS'⟩ := mem_erase.mp hS
        obtain ⟨w, -, rfl⟩ := mem_image.mp hS'
        rw [sum_const, smul_eq_mul, fiber_cycleOf ⟨w, rfl⟩, two_mul_card_cycleOf_div_two]
        intro y hy
        refine mem_filter.mpr ⟨mem_univ y, fun h ↦ hne ?_⟩
        rw [← cycleOf_eq_of_mem hy, cycleOf_eq_of_mem h]
    _ = ((μ.erase a).map fun b ↦ 2 * b * G b).sum := by
        rw [hμ, ha_def, pairType, ← map_erase_val _ (cycleOf_mem_image v), Multiset.map_map,
          sum_eq_multiset_sum]
        rfl

/-- `N = 0` on the empty vertex set (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_of_card_eq_zero (F0 F1 : PerfectMatching V) (hV : Fintype.card V = 0) :
    hamPairCount F0 F1 = 0 := by
  rw [hamPairCount, card_eq_zero, filter_eq_empty_iff]
  intro P _ h
  obtain ⟨x⟩ := h.1.nonempty
  exact (Fintype.card_eq_zero_iff.mp hV).elim x

/-- `N((1)) = 1`: on two vertices the only matching is Hamiltonian with itself
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_of_card_eq_two (F0 F1 : PerfectMatching V) (hV : Fintype.card V = 2) :
    hamPairCount F0 F1 = 1 := by
  have hPM : Fintype.card (PerfectMatching V) = 1 := by
    rw [card_eq_doubleFactorial (n := 1) (by rw [hV])]
    rfl
  have hall : ∀ P Q : PerfectMatching V, P = Q := fun P Q ↦
    Fintype.card_le_one_iff.mp hPM.le P Q
  have hham : ∀ P : PerfectMatching V, Ham P P := by
    intro P
    have hx : ∀ x y : V, y = x ∨ y = P.mate x := by
      intro x y
      by_contra h
      push Not at h
      have : #({x, P.mate x, y} : Finset V) ≤ Fintype.card V := card_le_univ _
      rw [card_insert_of_notMem (by simp [h.1.symm, (P.mate_ne x).symm]),
        card_pair (Ne.symm h.2), hV] at this
      omega
    rw [Ham, SimpleGraph.connected_iff]
    refine ⟨fun x y ↦ ?_, ?_⟩
    · rcases hx x y with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact (adj_mate_left _ _ x).reachable
    · exact Fintype.card_pos_iff.mp (by omega)
  rw [hamPairCount, filter_true_of_mem, card_univ, hPM]
  intro P _
  rw [hall P F0, hall F1 F0]
  exact ⟨hham F0, hham F0⟩

/-- `|V ∖ {v, u}| = |V| - 2` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem card_redSet {v u : V} (hvu : v ≠ u) : #(redSet v u) = Fintype.card V - 2 := by
  rw [redSet, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hvu, mem_univ u⟩),
    card_erase_of_mem (mem_univ v), card_univ]
  omega

end Recursion

section Main

universe u

/-- `N(F₀, F₁) = k2Aux n μ` for `|V| = 2n`, by induction on `n`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_eq_k2Aux_aux (n : ℕ) : ∀ (W : Type u) [Fintype W] [DecidableEq W],
    Fintype.card W = 2 * n → ∀ F0 F1 : PerfectMatching W,
      hamPairCount F0 F1 = k2Aux n (pairType F0 F1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ hW F0 F1
    match n, ih, hW with
    | 0, _, hW => exact hamPairCount_of_card_eq_zero F0 F1 hW
    | 1, _, hW => exact hamPairCount_of_card_eq_two F0 F1 hW
    | j + 2, ih, hW =>
      have hne : pairType F0 F1 ≠ 0 := by
        intro h
        have := two_mul_sum_pairType F0 F1
        rw [h, Multiset.sum_zero] at this
        omega
      obtain ⟨S, hS, hSa⟩ := Multiset.mem_map.mp (maxPart_mem hne)
      obtain ⟨v, -, rfl⟩ := mem_image.mp (Finset.mem_val.mp hS)
      rw [hamPairCount_eq_sum_redCount F0 F1 v (by omega),
        sum_redCount_eq_k2Step F0 F1 v (k2Aux (j + 1)), hSa]
      · rfl
      · intro u hvu
        rw [redCount, redType, dite_eq_right hvu, dite_eq_right hvu]
        refine ih (j + 1) (by omega) (redSet v u) ?_ (red F0 hvu) (red F1 hvu)
        rw [Fintype.card_coe, card_redSet hvu, hW]
        omega

/-- `N(F₀, F₁) = N(μ)`: the number of perfect matchings Hamiltonian with both `F₀` and `F₁`
depends only on the type `μ` of `F₀ ∪ F₁` and is given by the Lemma K2 recursion
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_eq_k2Count {V : Type u} [Fintype V] [DecidableEq V]
    (F0 F1 : PerfectMatching V) : hamPairCount F0 F1 = k2Count (pairType F0 F1) :=
  hamPairCount_eq_k2Aux_aux _ V (two_mul_sum_pairType F0 F1).symm F0 F1

/-- Lemma K2 as a recursion: for every vertex `v`, in a cycle of half-length `a`, and
`|V| > 2`, `N(F₀, F₁) = k2Step N μ a` where `μ` is the type of `F₀ ∪ F₁`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem hamPairCount_eq_k2Step {V : Type u} [Fintype V] [DecidableEq V]
    (F0 F1 : PerfectMatching V) (v : V) (hV : 2 < Fintype.card V) :
    hamPairCount F0 F1 = k2Step k2Count (pairType F0 F1) (#(cycleOf F0 F1 v) / 2) := by
  rw [hamPairCount_eq_sum_redCount F0 F1 v hV]
  refine sum_redCount_eq_k2Step F0 F1 v k2Count fun u hvu ↦ ?_
  rw [redCount, redType, dite_eq_right hvu, dite_eq_right hvu]
  exact hamPairCount_eq_k2Count _ _

end Main

end PerfectMatching

end Pairing
