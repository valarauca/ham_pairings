import Mathlib.Combinatorics.SimpleGraph.Clique
import Pairing.RoundRobin

/-!
# Short cycles of a triple union (Lemma M)

Put `n = 2m - 1`. For `r ∉ {0, 1}` the triple union `G_r = F_0 ∪ F_1 ∪ F_r` is the cubic graph
on `V_m` whose edges are those of the three round-robin factors. The factors are pairwise
edge-disjoint, so the multigraph union is a simple graph.

* `tripleUnion m r` : `G_r`, and `tripleUnion_adj_some`, `tripleUnion_adj_none` : two finite
  vertices `x ≠ y` are adjacent iff `x + y ∈ {0, 2, 2r}`, and `∞` is adjacent to `0, 1, r`.
* `IsAP r` : `{0, 1, r}` is a progression, `r ∈ {2, -1, 1/2}`. `IsA3 r` : `r` lies in the
  anharmonic orbit `{3, -2, 1/3, -1/2, 3/2, 2/3}` of `3`. Both are stated without division.
* `fourCycles G` : the 4-cycles of a simple graph, each recorded by its edge set, from closed
  walks `a b c d a` with `ab, bc, cd, da` edges, `a ≠ c` and `b ≠ d`.
* (a) `cliqueFinset_tripleUnion` : for non-AP `r` the only triangle is the rainbow triangle
  `{1 - r, r - 1, r + 1}`, for every odd `n`. The AP half of (a) is not formalized here.
* (b) `fourCyclesAvoiding_nonempty_iff` : for `3 ∤ n`, `G_r` has a 4-cycle avoiding `∞` iff
  `r` is an AP.
* (c) `fourCyclesThrough_nonempty_iff` : for `3 ∤ n`, `G_r` has a 4-cycle through `∞` iff
  `r ∈ A_3`. `card_fourCyclesThrough` : for `n` coprime to `105` it is then unique, and
  `fourCyclesThrough_eq_empty_of_isAP` : for `n` coprime to `15` AP triples have none.
* (d) `fourCycles_two`, `card_fourCycles_two` : for `n` coprime to `15` the 4-cycles of `G_2`
  are the ladder squares `Q_v = {v, -v, v + 2, 2 - v}`, `v ∉ {0, 1, -1}`, with `Q_w = Q_v` iff
  `w = ±v` (`ladderSquare_eq_iff`), so there are exactly `m - 2` of them. The file checks the
  count only for prime `n ≤ 61`.
* Small cases at `n = 11`, by `decide +kernel` : `cliqueFinset_tripleUnion_six_three`,
  `card_fourCyclesThrough_six_three`, `card_fourCycles_six_two`.

Source: `results/k3-workaround-spike.md` §2.1, Lemma M. The file assumes `n ≥ 11` prime.
`coprime_105_of_prime` shows that this implies every coprimality hypothesis used here.
-/

local macro "lcpm " e:term : tactic =>
  `(tactic| first | linear_combination (exp := 1) $e | linear_combination (exp := 1) -($e))

namespace Pairing

section FourCycle

variable {V : Type*} [DecidableEq V]

/-- The edge set `{ab, bc, cd, da}` of the closed walk `a b c d a`
(`results/k3-workaround-spike.md`, Lemma M). -/
def fourCycleEdges (a b c d : V) : Finset (Sym2 V) :=
  {s(a, b), s(b, c), s(c, d), s(d, a)}

/-- `a b c d a` is a 4-cycle of `G`, that is `ab, bc, cd, da` are edges, `a ≠ c` and `b ≠ d`
(`results/k3-workaround-spike.md`, Lemma M). -/
def IsFourCycle (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ a ≠ c ∧ b ≠ d

instance (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d : V) :
    Decidable (IsFourCycle G a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The 4-cycles of `G`, each recorded by its edge set (`results/k3-workaround-spike.md`,
Lemma M). -/
def fourCycles [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  ({x : V × V × V × V | IsFourCycle G x.1 x.2.1 x.2.2.1 x.2.2.2} : Finset _).image
    fun x ↦ fourCycleEdges x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The 4-cycles of `G` through the vertex `v` (`results/k3-workaround-spike.md`, Lemma M). -/
def fourCyclesThrough [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Finset (Sym2 V)) :=
  {s ∈ fourCycles G | ∃ e ∈ s, v ∈ e}

/-- The 4-cycles of `G` avoiding the vertex `v` (`results/k3-workaround-spike.md`, Lemma M). -/
def fourCyclesAvoiding [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Finset (Sym2 V)) :=
  {s ∈ fourCycles G | ∀ e ∈ s, v ∉ e}

variable {G : SimpleGraph V}

/-- Membership in `fourCycles G` (`results/k3-workaround-spike.md`, Lemma M). -/
theorem mem_fourCycles [Fintype V] [DecidableRel G.Adj] {s : Finset (Sym2 V)} :
    s ∈ fourCycles G ↔ ∃ a b c d, IsFourCycle G a b c d ∧ fourCycleEdges a b c d = s := by
  simp [fourCycles]

/-- A vertex lies on an edge of `a b c d a` iff it is one of `a, b, c, d`
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem exists_mem_fourCycleEdges {a b c d v : V} :
    (∃ e ∈ fourCycleEdges a b c d, v ∈ e) ↔ v = a ∨ v = b ∨ v = c ∨ v = d := by
  simp only [fourCycleEdges, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, Sym2.mem_iff]
  tauto

/-- Rotating `a b c d a` to `b c d a b` keeps the edge set (`results/k3-workaround-spike.md`,
Lemma M). -/
theorem fourCycleEdges_rotate (a b c d : V) :
    fourCycleEdges b c d a = fourCycleEdges a b c d := by
  ext e
  simp only [fourCycleEdges, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Reversing `a b c d a` to `a d c b a` keeps the edge set (`results/k3-workaround-spike.md`,
Lemma M). -/
theorem fourCycleEdges_reverse (a b c d : V) :
    fourCycleEdges a d c b = fourCycleEdges a b c d := by
  ext e
  simp only [fourCycleEdges, Finset.mem_insert, Finset.mem_singleton]
  rw [Sym2.eq_swap (a := d) (b := c), Sym2.eq_swap (a := c) (b := b),
    Sym2.eq_swap (a := b) (b := a), Sym2.eq_swap (a := d) (b := a)]
  tauto

/-- Reflecting `a b c d a` through the edge `ab` to `b a d c b` keeps the edge set
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem fourCycleEdges_swap (a b c d : V) :
    fourCycleEdges b a d c = fourCycleEdges a b c d := by
  rw [fourCycleEdges_rotate, fourCycleEdges_rotate, fourCycleEdges_rotate, fourCycleEdges_reverse]

omit [DecidableEq V] in
/-- Rotation preserves 4-cycles (`results/k3-workaround-spike.md`, Lemma M). -/
theorem IsFourCycle.rotate {a b c d : V} (h : IsFourCycle G a b c d) : IsFourCycle G b c d a :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.1, h.2.2.2.2.2, h.2.2.2.2.1.symm⟩

/-- A 4-cycle through `v` can be written to start at `v` (`results/k3-workaround-spike.md`,
Lemma M). -/
theorem IsFourCycle.exists_start {a b c d v : V} (h : IsFourCycle G a b c d)
    (hv : v = a ∨ v = b ∨ v = c ∨ v = d) :
    ∃ b' c' d', IsFourCycle G v b' c' d' ∧ fourCycleEdges a b c d = fourCycleEdges v b' c' d' := by
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨b, c, d, h, rfl⟩
  · exact ⟨c, d, a, h.rotate, (fourCycleEdges_rotate _ _ _ _).symm⟩
  · exact ⟨d, a, b, h.rotate.rotate, by rw [fourCycleEdges_rotate, fourCycleEdges_rotate]⟩
  · exact ⟨a, b, c, h.rotate.rotate.rotate, by
      rw [fourCycleEdges_rotate, fourCycleEdges_rotate, fourCycleEdges_rotate]⟩

end FourCycle

section TripleArith

variable {R : Type*} [CommRing R]

private theorem tri_vertex {x y z r : R} (u2 : IsUnit (2 : R)) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (h1 : x + y = 0 ∨ x + y = 2 ∨ x + y = 2 * r)
    (h2 : x + z = 0 ∨ x + z = 2 ∨ x + z = 2 * r) (h3 : y + z = 0 ∨ y + z = 2 ∨ y + z = 2 * r) :
    x = 1 - r ∨ x = r - 1 ∨ x = r + 1 := by
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
    first
    | exact absurd (by lcpm h1 - h2) hyz
    | exact absurd (by lcpm h1 - h3) hxz
    | exact absurd (by lcpm h2 - h3) hxy
    | exact Or.inl (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3)))
    | exact Or.inr (Or.inl (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3))))
    | exact Or.inr (Or.inr (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3))))

private theorem label_pair {x y r : R} (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hx : x = 0 ∨ x = 1 ∨ x = r)
    (hy : y = 0 ∨ y = 1 ∨ y = r) (hxy : x ≠ y) (h : x + y = 0 ∨ x + y = 2 ∨ x + y = 2 * r) :
    (r = 2 ∧ (x = 0 ∧ y = r ∨ x = r ∧ y = 0)) ∨ (r = -1 ∧ (x = 1 ∧ y = r ∨ x = r ∧ y = 1)) ∨
      (2 * r = 1 ∧ (x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0)) := by
  rcases hx with hx | hx | hx <;> subst x <;> rcases hy with hy | hy | hy <;> subst y <;>
    rcases h with h | h | h <;>
    first
    | exact absurd rfl hxy
    | exact absurd (by lcpm r * h) hr0
    | exact absurd (by lcpm h) hr0
    | exact absurd (by lcpm h) hr1
    | exact Or.inl ⟨by lcpm h, by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr (Or.inl ⟨by lcpm h,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩)
    | exact Or.inr (Or.inr ⟨by lcpm h,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩)

private theorem inf_classify {p q x r : R} (u3 : IsUnit (3 : R)) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hp : p = 0 ∨ p = 1 ∨ p = r) (hq : q = 0 ∨ q = 1 ∨ q = r) (hpq : p ≠ q) (hxp : x ≠ p)
    (hxq : x ≠ q) (h1 : x + p = 0 ∨ x + p = 2 ∨ x + p = 2 * r)
    (h2 : x + q = 0 ∨ x + q = 2 ∨ x + q = 2 * r) :
    (2 * r = 3 ∧ x = 2 ∧ (p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0)) ∨
    (2 * r = -1 ∧ x = -1 ∧ (p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0)) ∨
    (r = -2 ∧ x = 2 ∧ (p = 0 ∧ q = r ∨ p = r ∧ q = 0)) ∨
    (3 * r = 2 ∧ x = 2 * r ∧ (p = 0 ∧ q = r ∨ p = r ∧ q = 0)) ∨
    (r = 3 ∧ x = -1 ∧ (p = 1 ∧ q = r ∨ p = r ∧ q = 1)) ∨
    (3 * r = 1 ∧ x = -r ∧ (p = 1 ∧ q = r ∨ p = r ∧ q = 1)) := by
  rcases hp with hp | hp | hp <;> subst p <;> rcases hq with hq | hq | hq <;> subst q <;>
    rcases h1 with h1 | h1 | h1 <;> obtain rfl := eq_sub_of_add_eq h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    first
    | exact absurd rfl hpq
    | exact absurd (by ring1) hxp
    | exact absurd (by linear_combination h2) hxq
    | exact absurd (by lcpm r * h2) hr0
    | exact absurd (by lcpm h2) hr0
    | exact absurd (by lcpm h2) hr1
    | exact absurd (u3.mul_right_eq_zero.1 (by lcpm h2)) hr0
    | exact absurd (u3.mul_right_eq_zero.1 (by lcpm r * h2)) hr0
    | exact absurd (sub_eq_zero.1 (u3.mul_right_eq_zero.1 (by lcpm h2))) hr1
    | exact Or.inl ⟨by lcpm h2, by first | ring1 | lcpm h2,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr <| Or.inl ⟨by lcpm h2, by first | ring1 | lcpm h2,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr <| Or.inr <| Or.inl ⟨by lcpm h2, by first | ring1 | lcpm h2,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by lcpm h2, by first | ring1 | lcpm h2,
        by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by lcpm h2,
        by first | ring1 | lcpm h2, by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨by lcpm h2,
        by first | ring1 | lcpm h2, by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩

private theorem fin_classify {a b c d r : R} (u2 : IsUnit (2 : R)) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hac : a ≠ c) (hbd : b ≠ d) (h1 : a + b = 0 ∨ a + b = 2 ∨ a + b = 2 * r)
    (h2 : b + c = 0 ∨ b + c = 2 ∨ b + c = 2 * r) (h3 : c + d = 0 ∨ c + d = 2 ∨ c + d = 2 * r)
    (h4 : d + a = 0 ∨ d + a = 2 ∨ d + a = 2 * r) :
    r = 2 ∨ r = -1 ∨ 2 * r = 1 := by
  rcases h1 with h1 | h1 | h1 <;> obtain rfl := eq_sub_of_add_eq h1 <;>
    rcases h2 with h2 | h2 | h2 <;> obtain rfl := eq_sub_of_add_eq' h2 <;>
    rcases h3 with h3 | h3 | h3 <;> obtain rfl := eq_sub_of_add_eq' h3 <;>
    rcases h4 with h4 | h4 | h4 <;>
    first
    | exact absurd (by ring1) hac
    | exact absurd (by lcpm h4) hac
    | exact absurd (by ring1) hbd
    | exact absurd (by lcpm h4) hbd
    | exact Or.inl (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h4)))
    | exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left (u2.mul_right_eq_zero.1 (by lcpm h4))))
    | exact Or.inr (Or.inr (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h4))))
    | exact absurd (u2.mul_right_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm r * h4))) hr0
    | exact absurd (u2.mul_right_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h4))) hr0
    | exact absurd (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (u2.mul_right_eq_zero.1
        (by lcpm h4)))) hr1

private theorem ladder_classify [Nontrivial R] {a b c d : R} (u2 : IsUnit (2 : R))
    (u3 : IsUnit (3 : R)) (hac : a ≠ c) (hbd : b ≠ d)
    (h1 : a + b = 0 ∨ a + b = 2 ∨ a + b = 2 * 2) (h2 : b + c = 0 ∨ b + c = 2 ∨ b + c = 2 * 2)
    (h3 : c + d = 0 ∨ c + d = 2 ∨ c + d = 2 * 2) (h4 : d + a = 0 ∨ d + a = 2 ∨ d + a = 2 * 2) :
    (b = -a ∧ c = a + 2 ∧ d = 2 - a) ∨ (c = -b ∧ d = b + 2 ∧ a = 2 - b) ∨
      (d = -c ∧ a = c + 2 ∧ b = 2 - c) ∨ (a = -d ∧ b = d + 2 ∧ c = 2 - d) := by
  rcases h1 with h1 | h1 | h1 <;> obtain rfl := eq_sub_of_add_eq h1 <;>
    rcases h2 with h2 | h2 | h2 <;> obtain rfl := eq_sub_of_add_eq' h2 <;>
    rcases h3 with h3 | h3 | h3 <;> obtain rfl := eq_sub_of_add_eq' h3 <;>
    rcases h4 with h4 | h4 | h4 <;>
    first
    | exact absurd (by ring1) hac
    | exact absurd (by lcpm h4) hac
    | exact absurd (by ring1) hbd
    | exact absurd (by lcpm h4) hbd
    | exact absurd (by lcpm h4) (u2.mul u2).ne_zero
    | exact absurd (by lcpm h4) ((u2.mul u2).mul u2).ne_zero
    | exact absurd (by lcpm h4) (u2.mul u3).ne_zero
    | exact Or.inl ⟨by ring1, by ring1, by ring1⟩
    | exact Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by ring1, by ring1, by ring1⟩))

end TripleArith

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The triple union `G_r = F_0 ∪ F_1 ∪ F_r` on `V_m`. For `r ∉ {0, 1}` the three factors are
edge-disjoint (`distinct_factors_edge_disjoint`), so this simple graph is the multigraph union
(`results/k3-workaround-spike.md`, Lemma M). -/
def tripleUnion (m : ℕ) [NeZero m] (r : ZMod (2 * m - 1)) : SimpleGraph (Vertex m) :=
  (factor m 0).toGraph ⊔ (factor m 1).toGraph ⊔ (factor m r).toGraph

instance (r : ZMod (2 * m - 1)) : DecidableRel (tripleUnion m r).Adj :=
  fun v w ↦ inferInstanceAs
    (Decidable (((factor m 0).toGraph ⊔ (factor m 1).toGraph ⊔ (factor m r).toGraph).Adj v w))

/-- `{0, 1, r}` is a 3-term progression, `r ∈ {2, -1, 1/2}` (`results/k3-workaround-spike.md`,
Lemma M). -/
def IsAP (r : ZMod (2 * m - 1)) : Prop :=
  r = 2 ∨ r = -1 ∨ 2 * r = 1

/-- `r` lies in the anharmonic orbit `A_3 = {3/2, -1/2, -2, 2/3, 3, 1/3}` of `3`
(`results/k3-workaround-spike.md`, Lemma M). -/
def IsA3 (r : ZMod (2 * m - 1)) : Prop :=
  2 * r = 3 ∨ 2 * r = -1 ∨ r = -2 ∨ 3 * r = 2 ∨ r = 3 ∨ 3 * r = 1

/-- The rainbow triangle `T_r = {1 - r, r - 1, r + 1}` (`results/k3-workaround-spike.md`,
Lemma M (a)). -/
def rainbow (m : ℕ) (r : ZMod (2 * m - 1)) : Finset (Vertex m) :=
  {some (1 - r), some (r - 1), some (r + 1)}

/-- `2` is a unit of `ℤ/(2m-1)` (`results/k3-workaround-spike.md`, Lemma M). -/
theorem isUnit_two' : IsUnit (2 : ZMod (2 * m - 1)) :=
  RoundRobin.isUnit_two (modulus_odd m)

/-- Two finite vertices are adjacent in `F_t` iff they are distinct with sum `2t`
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem factor_adj_some {t x y : ZMod (2 * m - 1)} :
    (factor m t).toGraph.Adj (some x) (some y) ↔ x ≠ y ∧ x + y = 2 * t := by
  rw [toGraph_adj, factor, RoundRobin.factor_mate]
  rcases eq_or_ne x t with rfl | hxt
  · simp only [mateFn_self, reduceCtorEq, false_iff, not_and]
    intro hne h
    exact hne (by linear_combination -h)
  · rw [mateFn_of_ne _ _ hxt, Option.some_inj]
    constructor
    · rintro rfl
      exact ⟨fun h ↦ hxt (isUnit_two'.mul_left_cancel (by linear_combination -h)).symm, by ring⟩
    · rintro ⟨-, h⟩
      linear_combination -h

/-- `∞` is adjacent to `x` in `F_t` iff `x = t` (`results/k3-workaround-spike.md`, Lemma M). -/
theorem factor_adj_none {t x : ZMod (2 * m - 1)} :
    (factor m t).toGraph.Adj none (some x) ↔ x = t := by
  rw [toGraph_adj, factor, RoundRobin.factor_mate, mateFn_none, Option.some_inj, eq_comm]

/-- Two finite vertices of `G_r` are adjacent iff they are distinct with sum in `{0, 2, 2r}`
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem tripleUnion_adj_some {r x y : ZMod (2 * m - 1)} :
    (tripleUnion m r).Adj (some x) (some y) ↔
      x ≠ y ∧ (x + y = 0 ∨ x + y = 2 ∨ x + y = 2 * r) := by
  simp only [tripleUnion, SimpleGraph.sup_adj, factor_adj_some, mul_zero, mul_one]
  tauto

/-- The neighbours of `∞` in `G_r` are `0, 1, r` (`results/k3-workaround-spike.md`,
Lemma M). -/
theorem tripleUnion_adj_none {r x : ZMod (2 * m - 1)} :
    (tripleUnion m r).Adj none (some x) ↔ x = 0 ∨ x = 1 ∨ x = r := by
  simp only [tripleUnion, SimpleGraph.sup_adj, factor_adj_none]
  tauto


/-- `∞` is adjacent to `x` in `G_r` iff `x ∈ {0, 1, r}`, from the other side
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem tripleUnion_adj_some_none {r x : ZMod (2 * m - 1)} :
    (tripleUnion m r).Adj (some x) none ↔ x = 0 ∨ x = 1 ∨ x = r := by
  rw [SimpleGraph.adj_comm, tripleUnion_adj_none]

omit [NeZero m] in
/-- `k` is a unit of `ℤ/(2m-1)` when `2m - 1` is coprime to `k` (`results/k3-workaround-spike.md`,
Lemma M). -/
theorem isUnit_natCast_of_coprime {k : ℕ} (h : Nat.Coprime (2 * m - 1) k) :
    IsUnit (k : ZMod (2 * m - 1)) := by
  rw [← ZMod.coe_unitOfCoprime k h.symm]
  exact Units.isUnit _

omit [NeZero m] in
/-- For prime `n = 2m - 1 ≥ 11`, the hypothesis of the file, `n` is coprime to `105`
(`results/k3-workaround-spike.md`, Lemma M). -/
theorem coprime_105_of_prime (hp : (2 * m - 1).Prime) (hm : 6 ≤ m) :
    Nat.Coprime (2 * m - 1) 105 := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ ?_
  have h105 : (2 * m - 1) ∣ 3 * 5 * 7 := h
  rcases (Nat.Prime.dvd_mul hp).1 h105 with h' | h'
  · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
    · exact absurd (Nat.le_of_dvd (by norm_num) h'') (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h'') (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)

section Units

variable {D : ℕ}

omit [NeZero m] in
private theorem unit_of {k : ℕ} (hD : Nat.Coprime (2 * m - 1) D) (hk : k ∣ D) :
    IsUnit (k : ZMod (2 * m - 1)) :=
  isUnit_natCast_of_coprime (Nat.Coprime.coprime_dvd_right hk hD)

omit [NeZero m] in
private theorem unit3 (hD : Nat.Coprime (2 * m - 1) D) (hk : 3 ∣ D) :
    IsUnit (3 : ZMod (2 * m - 1)) := by
  simpa using unit_of (k := 3) hD hk

end Units

/-! ### (a) Triangles -/

/-- The rainbow triangle `T_r` is a triangle of `G_r` for every `r ∉ {0, 1}`
(`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem rainbow_isClique {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (tripleUnion m r).IsNClique 3 (rainbow m r) := by
  rw [rainbow, SimpleGraph.is3Clique_triple_iff, tripleUnion_adj_some, tripleUnion_adj_some,
    tripleUnion_adj_some]
  refine ⟨⟨fun h ↦ hr1 (sub_eq_zero.1 (isUnit_two'.mul_right_eq_zero.1 (by linear_combination -h))),
    Or.inl (by ring)⟩, ⟨fun h ↦ hr0 (isUnit_two'.mul_right_eq_zero.1 (by linear_combination -h)),
    Or.inr (Or.inl (by ring))⟩, ⟨fun h ↦ hr0 (isUnit_two'.mul_right_eq_zero.1
    (by linear_combination -r * h)), Or.inr (Or.inr (by ring))⟩⟩

private theorem ne_none_of_triangle {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hAP : ¬IsAP r) {u v w : Vertex m} (huv : (tripleUnion m r).Adj u v)
    (huw : (tripleUnion m r).Adj u w) (hvw : (tripleUnion m r).Adj v w) : u ≠ none := by
  rintro rfl
  obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 huv.ne.symm
  obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 huw.ne.symm
  rw [tripleUnion_adj_none] at huv huw
  obtain ⟨hyz, hs⟩ := tripleUnion_adj_some.1 hvw
  rcases label_pair hr0 hr1 huv huw hyz hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  exacts [hAP (Or.inl h), hAP (Or.inr (Or.inl h)), hAP (Or.inr (Or.inr h))]

private theorem mem_rainbow_of_triangle {r : ZMod (2 * m - 1)} {u v w : Vertex m}
    (hu : u ≠ none) (hv : v ≠ none) (hw : w ≠ none) (huv : (tripleUnion m r).Adj u v)
    (huw : (tripleUnion m r).Adj u w) (hvw : (tripleUnion m r).Adj v w) : u ∈ rainbow m r := by
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 hu
  obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hv
  obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 hw
  obtain ⟨hxy, h1⟩ := tripleUnion_adj_some.1 huv
  obtain ⟨hxz, h2⟩ := tripleUnion_adj_some.1 huw
  obtain ⟨hyz, h3⟩ := tripleUnion_adj_some.1 hvw
  rcases tri_vertex isUnit_two' hxy hxz hyz h1 h2 h3 with h | h | h <;> simp [rainbow, h]

private theorem eq_rainbow_of_triangle {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    {a b c : Vertex m} (ha : a ≠ none) (hb : b ≠ none) (hc : c ≠ none)
    (hab : (tripleUnion m r).Adj a b) (hac : (tripleUnion m r).Adj a c)
    (hbc : (tripleUnion m r).Adj b c) : ({a, b, c} : Finset (Vertex m)) = rainbow m r := by
  refine Finset.eq_of_subset_of_card_le ?_ (by
    rw [(rainbow_isClique hr0 hr1).card_eq,
      (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩).card_eq])
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_rainbow_of_triangle ha hb hc hab hac hbc
  · exact mem_rainbow_of_triangle hb ha hc hab.symm hbc hac
  · exact mem_rainbow_of_triangle hc ha hb hac.symm hbc.symm hab

/-- **Lemma M (a)**, non-AP case. If `{0, 1, r}` is not a progression, the rainbow triangle
`T_r = {1 - r, r - 1, r + 1}` is the only triangle of `G_r`. This holds for every odd `n`; the
file's hypothesis `n ≥ 11` prime is not needed (`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem cliqueFinset_tripleUnion {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hAP : ¬IsAP r) : (tripleUnion m r).cliqueFinset 3 = {rainbow m r} := by
  ext s
  rw [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_singleton]
  refine ⟨fun hs ↦ ?_, fun hs ↦ hs ▸ rainbow_isClique hr0 hr1⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hs
  exact eq_rainbow_of_triangle hr0 hr1 (ne_none_of_triangle hr0 hr1 hAP hab hac hbc)
    (ne_none_of_triangle hr0 hr1 hAP hab.symm hbc hac)
    (ne_none_of_triangle hr0 hr1 hAP hac.symm hbc.symm hab) hab hac hbc

/-! ### (c) 4-cycles through `∞` -/

/-- The six equations of `A_3`, indexed by `Fin 6` (`results/k3-workaround-spike.md`,
Lemma M (c)). -/
def a3Eq (r : ZMod (2 * m - 1)) : Fin 6 → Prop
  | 0 => 2 * r = 3
  | 1 => 2 * r = -1
  | 2 => r = -2
  | 3 => 3 * r = 2
  | 4 => r = 3
  | 5 => 3 * r = 1

/-- The 4-cycle through `∞` attached to each equation of `A_3`, `∞, a, x, b` with
`x = 2c - a = 2c' - b` (`results/k3-workaround-spike.md`, Lemma M (c)). -/
def infSquare (m : ℕ) (r : ZMod (2 * m - 1)) : Fin 6 → Finset (Sym2 (Vertex m))
  | 0 => fourCycleEdges none (some 0) (some 2) (some 1)
  | 1 => fourCycleEdges none (some 0) (some (-1)) (some 1)
  | 2 => fourCycleEdges none (some 0) (some 2) (some r)
  | 3 => fourCycleEdges none (some 0) (some (2 * r)) (some r)
  | 4 => fourCycleEdges none (some 1) (some (-1)) (some r)
  | 5 => fourCycleEdges none (some 1) (some (-r)) (some r)

omit [NeZero m] in
/-- `IsA3 r` holds iff one of the six equations does (`results/k3-workaround-spike.md`,
Lemma M (c)). -/
theorem isA3_iff_exists {r : ZMod (2 * m - 1)} : IsA3 r ↔ ∃ i, a3Eq r i := by
  constructor
  · rintro (h | h | h | h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩]
  · rintro ⟨i, h⟩
    fin_cases i
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]

private theorem isFourCycle_none {r p x q : ZMod (2 * m - 1)} (hp : p = 0 ∨ p = 1 ∨ p = r)
    (hq : q = 0 ∨ q = 1 ∨ q = r) (hpq : p ≠ q) (hpx : p ≠ x) (hxq : x ≠ q)
    (h1 : p + x = 0 ∨ p + x = 2 ∨ p + x = 2 * r) (h2 : x + q = 0 ∨ x + q = 2 ∨ x + q = 2 * r) :
    IsFourCycle (tripleUnion m r) none (some p) (some x) (some q) :=
  ⟨tripleUnion_adj_none.2 hp, tripleUnion_adj_some.2 ⟨hpx, h1⟩,
    tripleUnion_adj_some.2 ⟨hxq, h2⟩, tripleUnion_adj_some_none.2 hq, by simp,
    fun h ↦ hpq (Option.some_inj.1 h)⟩

private theorem isFourCycle_infSquare {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    {i : Fin 6} (hi : a3Eq r i) : ∃ p x q, IsFourCycle (tripleUnion m r) none (some p) (some x)
      (some q) ∧ fourCycleEdges none (some p) (some x) (some q) = infSquare m r i := by
  have : Nontrivial (ZMod (2 * m - 1)) := nontrivial_of_ne r 0 hr0
  have u2 := isUnit_two' (m := m)
  fin_cases i <;> simp only [a3Eq] at hi
  · exact ⟨0, 2, 1, isFourCycle_none (Or.inl rfl) (Or.inr (Or.inl rfl)) zero_ne_one
      (fun h ↦ u2.ne_zero h.symm) (fun h ↦ one_ne_zero (by lcpm h))
      (Or.inr (Or.inl (by ring))) (Or.inr (Or.inr (by lcpm hi))), rfl⟩
  · exact ⟨0, -1, 1, isFourCycle_none (Or.inl rfl) (Or.inr (Or.inl rfl)) zero_ne_one
      (fun h ↦ one_ne_zero (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
      (Or.inr (Or.inr (by lcpm hi))) (Or.inl (by ring)), rfl⟩
  · exact ⟨0, 2, r, isFourCycle_none (Or.inl rfl) (Or.inr (Or.inr rfl)) hr0.symm
      (fun h ↦ u2.ne_zero h.symm) (fun h ↦ (u2.mul u2).ne_zero (by lcpm h + hi))
      (Or.inr (Or.inl (by ring))) (Or.inl (by lcpm hi)), rfl⟩
  · exact ⟨0, 2 * r, r, isFourCycle_none (Or.inl rfl) (Or.inr (Or.inr rfl)) hr0.symm
      (fun h ↦ hr0 (u2.mul_right_eq_zero.1 h.symm)) (fun h ↦ hr0 (by lcpm h))
      (Or.inr (Or.inr (by ring))) (Or.inr (Or.inl (by lcpm hi))), rfl⟩
  · exact ⟨1, -1, r, isFourCycle_none (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hr1.symm
      (fun h ↦ u2.ne_zero (by lcpm h)) (fun h ↦ (u2.mul u2).ne_zero (by lcpm h + hi))
      (Or.inl (by ring)) (Or.inr (Or.inl (by lcpm hi))), rfl⟩
  · exact ⟨1, -r, r, isFourCycle_none (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hr1.symm
      (fun h ↦ (u2.mul u2).ne_zero (by lcpm 3 * h - hi))
      (fun h ↦ hr0 (u2.mul_right_eq_zero.1 (by lcpm h)))
      (Or.inr (Or.inr (by lcpm hi))) (Or.inl (by ring)), rfl⟩

/-- **Lemma M (c)**, classification. For `3 ∤ n`, the 4-cycles of `G_r` through `∞` are exactly
the `infSquare m r i` with `a3Eq r i` (`results/k3-workaround-spike.md`, Lemma M (c)). -/
theorem mem_fourCyclesThrough_none {r : ZMod (2 * m - 1)} (h3 : Nat.Coprime (2 * m - 1) 3)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) {s : Finset (Sym2 (Vertex m))} :
    s ∈ fourCyclesThrough (tripleUnion m r) none ↔ ∃ i, a3Eq r i ∧ infSquare m r i = s := by
  constructor
  · rw [fourCyclesThrough, Finset.mem_filter, mem_fourCycles]
    rintro ⟨⟨a, b, c, d, hsq, rfl⟩, hv⟩
    obtain ⟨b', c', d', hsq', he⟩ := hsq.exists_start (exists_mem_fourCycleEdges.1 hv)
    rw [he]
    obtain ⟨hab, hbc, hcd, hda, hac, hbd⟩ := hsq'
    obtain ⟨p, rfl⟩ := Option.ne_none_iff_exists'.1 hab.ne.symm
    obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 hac.symm
    obtain ⟨q, rfl⟩ := Option.ne_none_iff_exists'.1 hda.ne
    rw [tripleUnion_adj_none] at hab
    rw [tripleUnion_adj_some_none] at hda
    obtain ⟨hpx, h1⟩ := tripleUnion_adj_some.1 hbc
    obtain ⟨hxq, h2⟩ := tripleUnion_adj_some.1 hcd
    rw [add_comm p x] at h1
    rcases inf_classify (unit3 h3 dvd_rfl) hr0 hr1 hab hda (fun h ↦ hbd (congrArg some h))
      (Ne.symm hpx) hxq h1 h2 with
      ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    exacts [⟨0, h, rfl⟩, ⟨0, h, fourCycleEdges_reverse _ _ _ _⟩, ⟨1, h, rfl⟩,
      ⟨1, h, fourCycleEdges_reverse _ _ _ _⟩, ⟨2, h, rfl⟩, ⟨2, h, fourCycleEdges_reverse _ _ _ _⟩,
      ⟨3, h, rfl⟩, ⟨3, h, fourCycleEdges_reverse _ _ _ _⟩, ⟨4, h, rfl⟩,
      ⟨4, h, fourCycleEdges_reverse _ _ _ _⟩, ⟨5, h, rfl⟩, ⟨5, h, fourCycleEdges_reverse _ _ _ _⟩]
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨p, x, q, hsq, he⟩ := isFourCycle_infSquare hr0 hr1 hi
    rw [← he]
    exact Finset.mem_filter.2 ⟨mem_fourCycles.2 ⟨_, _, _, _, hsq, rfl⟩,
      exists_mem_fourCycleEdges.2 (Or.inl rfl)⟩

/-- **Lemma M (c)**, existence. For `3 ∤ n`, `G_r` has a 4-cycle through `∞` iff `r ∈ A_3`
(`results/k3-workaround-spike.md`, Lemma M (c)). -/
theorem fourCyclesThrough_nonempty_iff {r : ZMod (2 * m - 1)} (h3 : Nat.Coprime (2 * m - 1) 3)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (fourCyclesThrough (tripleUnion m r) none).Nonempty ↔ IsA3 r := by
  rw [isA3_iff_exists]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨i, hi, -⟩ := (mem_fourCyclesThrough_none h3 hr0 hr1).1 hs
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, (mem_fourCyclesThrough_none h3 hr0 hr1).2 ⟨i, hi, rfl⟩⟩

private def a3Six : Fin 6 → ℤ := ![9, -3, -12, 4, 18, 2]

private def apSix : Fin 3 → ℤ := ![12, -6, 3]

private theorem a3Six_dvd : ∀ i j : Fin 6, i ≠ j → a3Six i - a3Six j ∣ (2 * 105) ^ 4 := by
  decide

private theorem apSix_dvd : ∀ (k : Fin 3) (i : Fin 6), apSix k - a3Six i ∣ (2 * 15) ^ 4 := by
  decide

private theorem intCast_ne_zero {D : ℕ} (h : Nat.Coprime (2 * m - 1) D)
    [Nontrivial (ZMod (2 * m - 1))] {z : ℤ} (hz : z ∣ (2 * D) ^ 4) :
    (z : ZMod (2 * m - 1)) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have h2D : Nat.Coprime (2 * m - 1) (2 * D) :=
    Nat.Coprime.mul_right (Nat.coprime_two_left.2 (modulus_odd m)).symm h
  have hd : (2 * m - 1) ∣ (2 * D) ^ 4 := by
    have := Int.natAbs_dvd_natAbs.2 (h0.trans hz)
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  exact (ZMod.nontrivial_iff.1 ‹_›) (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 4 h2D) hd)

omit [NeZero m] in
private theorem six_mul_of_a3Eq {r : ZMod (2 * m - 1)} {i : Fin 6} (hi : a3Eq r i) :
    6 * r = (a3Six i : ZMod (2 * m - 1)) := by
  fin_cases i <;> simp only [a3Eq] at hi <;>
    simp only [a3Six, Int.reduceNeg, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Int.cast_neg, Int.cast_ofNat] <;>
    first
    | linear_combination 3 * hi
    | linear_combination 6 * hi
    | linear_combination 2 * hi

private theorem a3Eq_unique {r : ZMod (2 * m - 1)} (h : Nat.Coprime (2 * m - 1) 105)
    (hr0 : r ≠ 0) {i j : Fin 6} (hi : a3Eq r i) (hj : a3Eq r j) : i = j := by
  have : Nontrivial (ZMod (2 * m - 1)) := nontrivial_of_ne r 0 hr0
  by_contra hij
  refine intCast_ne_zero h (a3Six_dvd i j hij) ?_
  push_cast
  linear_combination (six_mul_of_a3Eq hj) - (six_mul_of_a3Eq hi)

/-- **Lemma M (c)**, uniqueness. For `n` coprime to `105` and `r ∈ A_3`, `G_r` has exactly one
4-cycle through `∞`. The file states this for prime `n ≥ 11`, which implies the coprimality
(`coprime_105_of_prime`). At `n = 7` it fails, since `r = 3` then satisfies three of the six
equations (`results/k3-workaround-spike.md`, Lemma M (c)). -/
theorem card_fourCyclesThrough {r : ZMod (2 * m - 1)} (h : Nat.Coprime (2 * m - 1) 105)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hA3 : IsA3 r) :
    (fourCyclesThrough (tripleUnion m r) none).card = 1 := by
  have h3 : Nat.Coprime (2 * m - 1) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  obtain ⟨i, hi⟩ := isA3_iff_exists.1 hA3
  rw [Finset.card_eq_one]
  refine ⟨infSquare m r i, Finset.ext fun s ↦ ?_⟩
  rw [mem_fourCyclesThrough_none h3 hr0 hr1, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [a3Eq_unique h hr0 hj hi]
  · rintro rfl
    exact ⟨i, hi, rfl⟩

private theorem not_a3Eq_of_isAP {r : ZMod (2 * m - 1)} (h : Nat.Coprime (2 * m - 1) 15)
    (hr0 : r ≠ 0) (hAP : IsAP r) (i : Fin 6) : ¬a3Eq r i := by
  have : Nontrivial (ZMod (2 * m - 1)) := nontrivial_of_ne r 0 hr0
  intro hi
  have hk : ∃ k, 6 * r = (apSix k : ZMod (2 * m - 1)) := by
    rcases hAP with h' | h' | h'
    · exact ⟨0, by
        simp only [apSix, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, Int.cast_ofNat]
        linear_combination 6 * h'⟩
    · exact ⟨1, by
        simp only [apSix, Int.reduceNeg, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Int.cast_neg, Int.cast_ofNat]
        linear_combination 6 * h'⟩
    · exact ⟨2, by
        simp only [apSix, Int.reduceNeg, Fin.isValue, Matrix.cons_val, Int.cast_ofNat]
        linear_combination 3 * h'⟩
  obtain ⟨k, hk⟩ := hk
  refine intCast_ne_zero h (apSix_dvd k i) ?_
  push_cast
  linear_combination (six_mul_of_a3Eq hi) - hk

/-- **Lemma M (c)**, AP case. For `n` coprime to `15`, AP triples have no 4-cycle through `∞`
(`results/k3-workaround-spike.md`, Lemma M (c)). -/
theorem fourCyclesThrough_eq_empty_of_isAP {r : ZMod (2 * m - 1)}
    (h : Nat.Coprime (2 * m - 1) 15) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hAP : IsAP r) :
    fourCyclesThrough (tripleUnion m r) none = ∅ := by
  have h3 : Nat.Coprime (2 * m - 1) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  refine Finset.eq_empty_of_forall_notMem fun s hs ↦ ?_
  obtain ⟨i, hi, -⟩ := (mem_fourCyclesThrough_none h3 hr0 hr1).1 hs
  exact not_a3Eq_of_isAP h hr0 hAP i hi


/-! ### (b) 4-cycles avoiding `∞` -/

private theorem isFourCycle_some {r a b c d : ZMod (2 * m - 1)} (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (hda : d ≠ a) (hac : a ≠ c) (hbd : b ≠ d)
    (h1 : a + b = 0 ∨ a + b = 2 ∨ a + b = 2 * r) (h2 : b + c = 0 ∨ b + c = 2 ∨ b + c = 2 * r)
    (h3 : c + d = 0 ∨ c + d = 2 ∨ c + d = 2 * r) (h4 : d + a = 0 ∨ d + a = 2 ∨ d + a = 2 * r) :
    IsFourCycle (tripleUnion m r) (some a) (some b) (some c) (some d) :=
  ⟨tripleUnion_adj_some.2 ⟨hab, h1⟩, tripleUnion_adj_some.2 ⟨hbc, h2⟩,
    tripleUnion_adj_some.2 ⟨hcd, h3⟩, tripleUnion_adj_some.2 ⟨hda, h4⟩,
    fun h ↦ hac (Option.some_inj.1 h), fun h ↦ hbd (Option.some_inj.1 h)⟩

private theorem mem_fourCyclesAvoiding_some {r a b c d : ZMod (2 * m - 1)}
    (h : IsFourCycle (tripleUnion m r) (some a) (some b) (some c) (some d)) :
    fourCycleEdges (some a) (some b) (some c) (some d) ∈
      fourCyclesAvoiding (tripleUnion m r) none :=
  Finset.mem_filter.2 ⟨mem_fourCycles.2 ⟨_, _, _, _, h, rfl⟩, by simp [fourCycleEdges]⟩

/-- **Lemma M (b)** (COD-169 Lemma C). For `3 ∤ n`, `G_r` has a 4-cycle avoiding `∞` iff
`{0, 1, r}` is a progression. The forward direction holds for every odd `n`
(`results/k3-workaround-spike.md`, Lemma M (b)). -/
theorem fourCyclesAvoiding_nonempty_iff {r : ZMod (2 * m - 1)} (h3 : Nat.Coprime (2 * m - 1) 3)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (fourCyclesAvoiding (tripleUnion m r) none).Nonempty ↔ IsAP r := by
  have : Nontrivial (ZMod (2 * m - 1)) := nontrivial_of_ne r 0 hr0
  have u2 := isUnit_two' (m := m)
  have u3 := unit3 h3 dvd_rfl
  constructor
  · rintro ⟨s, hs⟩
    rw [fourCyclesAvoiding, Finset.mem_filter, mem_fourCycles] at hs
    obtain ⟨⟨a, b, c, d, ⟨hab, hbc, hcd, hda, hac, hbd⟩, rfl⟩, hv⟩ := hs
    have hn : ¬(none = a ∨ none = b ∨ none = c ∨ none = d) := fun h ↦ by
      obtain ⟨e, he, hne⟩ := exists_mem_fourCycleEdges.2 h
      exact hv e he hne
    obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inl h.symm)
    obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inl h.symm))
    obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inr (Or.inl h.symm)))
    obtain ⟨w, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inr (Or.inr h.symm)))
    exact fin_classify u2 hr0 hr1 (fun h ↦ hac (congrArg some h)) (fun h ↦ hbd (congrArg some h))
      (tripleUnion_adj_some.1 hab).2 (tripleUnion_adj_some.1 hbc).2 (tripleUnion_adj_some.1 hcd).2
      (tripleUnion_adj_some.1 hda).2
  · rintro (h | h | h)
    · subst h
      exact ⟨_, mem_fourCyclesAvoiding_some (a := 2) (b := -2) (c := 4) (d := 0) (isFourCycle_some
        (fun h ↦ (u2.mul u2).ne_zero (by lcpm h)) (fun h ↦ (u2.mul u3).ne_zero (by lcpm h))
        (fun h ↦ (u2.mul u2).ne_zero (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
        (fun h ↦ u2.ne_zero (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
        (Or.inl (by ring)) (Or.inr (Or.inl (by ring))) (Or.inr (Or.inr (by ring)))
        (Or.inr (Or.inl (by ring))))⟩
    · subst h
      exact ⟨_, mem_fourCyclesAvoiding_some (a := 1) (b := -1) (c := 3) (d := -3) (isFourCycle_some
        (fun h ↦ u2.ne_zero (by lcpm h)) (fun h ↦ (u2.mul u2).ne_zero (by lcpm h))
        (fun h ↦ (u2.mul u3).ne_zero (by lcpm h)) (fun h ↦ (u2.mul u2).ne_zero (by lcpm h))
        (fun h ↦ u2.ne_zero (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
        (Or.inl (by ring)) (Or.inr (Or.inl (by ring))) (Or.inl (by ring))
        (Or.inr (Or.inr (by ring))))⟩
    · have u1 : (1 : ZMod (2 * m - 1)) ≠ 0 := one_ne_zero
      exact ⟨_, mem_fourCyclesAvoiding_some (a := 0) (b := 1) (c := -1) (d := 2) (isFourCycle_some
        (fun h ↦ u1 (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
        (fun h ↦ u3.ne_zero (by lcpm h)) (fun h ↦ u2.ne_zero (by lcpm h))
        (fun h ↦ u1 (by lcpm h)) (fun h ↦ u1 (by lcpm h))
        (Or.inr (Or.inr (by lcpm h))) (Or.inl (by ring)) (Or.inr (Or.inr (by lcpm h)))
        (Or.inr (Or.inl (by ring))))⟩

/-! ### (d) The ladder of `{0, 1, 2}` -/

/-- The ladder square `Q_v = v, -v, v + 2, 2 - v` of `G_2`, with colour word `0, 1, 2, 1`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
def ladderSquare (m : ℕ) (v : ZMod (2 * m - 1)) : Finset (Sym2 (Vertex m)) :=
  fourCycleEdges (some v) (some (-v)) (some (v + 2)) (some (2 - v))

/-- `Q_v` is a 4-cycle of `G_2` iff `v ∉ {0, 1, -1}` (`results/k3-workaround-spike.md`,
Lemma M (d)). -/
theorem isFourCycle_ladder_iff [Nontrivial (ZMod (2 * m - 1))] {v : ZMod (2 * m - 1)} :
    IsFourCycle (tripleUnion m 2) (some v) (some (-v)) (some (v + 2)) (some (2 - v)) ↔
      v ≠ 0 ∧ v ≠ 1 ∧ v ≠ -1 := by
  have u2 := isUnit_two' (m := m)
  simp only [IsFourCycle, tripleUnion_adj_some, ne_eq, Option.some_inj]
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩, -, ⟨h4, -⟩, -, -⟩
    exact ⟨fun h ↦ h1 (by rw [h]; ring), fun h ↦ h4 (by rw [h]; ring),
      fun h ↦ h2 (by rw [h]; ring)⟩
  · rintro ⟨h0, h1, hm1⟩
    exact ⟨⟨fun h ↦ h0 (u2.mul_right_eq_zero.1 (by lcpm h)), Or.inl (by ring)⟩,
      ⟨fun h ↦ hm1 (eq_neg_of_add_eq_zero_left (u2.mul_right_eq_zero.1 (by lcpm h))),
        Or.inr (Or.inl (by ring))⟩,
      ⟨fun h ↦ h0 (u2.mul_right_eq_zero.1 (by lcpm h)), Or.inr (Or.inr (by ring))⟩,
      ⟨fun h ↦ h1 (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h))), Or.inr (Or.inl (by ring))⟩,
      fun h ↦ u2.ne_zero (by lcpm h), fun h ↦ u2.ne_zero (by lcpm h)⟩

/-- `Q_w = Q_v` iff `w = ±v`, since `{v, -v}` is the only `F_0`-edge of `Q_v`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem ladderSquare_eq_iff [Nontrivial (ZMod (2 * m - 1))] {v w : ZMod (2 * m - 1)} :
    ladderSquare m w = ladderSquare m v ↔ w = v ∨ w = -v := by
  have u2 := isUnit_two' (m := m)
  constructor
  · intro h
    have hmem : s(some w, some (-w)) ∈ ladderSquare m v :=
      h ▸ by simp [ladderSquare, fourCycleEdges]
    simp only [ladderSquare, fourCycleEdges, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [Option.some_inj] at h1 h2 <;>
      first
      | exact Or.inl h1
      | exact Or.inr h1
      | exact absurd (by lcpm h1 + h2) u2.ne_zero
      | exact absurd (by lcpm h1 + h2) (u2.mul u2).ne_zero
  · rintro (rfl | rfl)
    · rfl
    · simp only [ladderSquare]
      rw [neg_neg, show -v + 2 = 2 - v by ring, show 2 - -v = v + 2 by ring]
      exact fourCycleEdges_swap _ _ _ _

/-- **Lemma M (d)**, shape. For `n` coprime to `15` (and `m ≥ 2`), the 4-cycles of `G_2` are
exactly the ladder squares `Q_v`, `v ∉ {0, 1, -1}` (`results/k3-workaround-spike.md`,
Lemma M (d)). -/
theorem fourCycles_two (h : Nat.Coprime (2 * m - 1) 15) (hm : 2 ≤ m) :
    fourCycles (tripleUnion m 2) =
      (({0, 1, -1} : Finset (ZMod (2 * m - 1)))ᶜ).image (ladderSquare m) := by
  have : Nontrivial (ZMod (2 * m - 1)) := ZMod.nontrivial_iff.2 (by omega)
  have u2 := isUnit_two' (m := m)
  have u3 := unit3 h (by norm_num)
  have h21 : (2 : ZMod (2 * m - 1)) ≠ 1 := fun h' ↦ one_ne_zero (by lcpm h')
  have hthrough := fourCyclesThrough_eq_empty_of_isAP h u2.ne_zero h21 (Or.inl rfl)
  ext s
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro hs
    obtain ⟨a, b, c, d, hsq, rfl⟩ := mem_fourCycles.1 hs
    by_cases hn : none = a ∨ none = b ∨ none = c ∨ none = d
    · have hmem : fourCycleEdges a b c d ∈ fourCyclesThrough (tripleUnion m 2) none :=
        Finset.mem_filter.2 ⟨hs, exists_mem_fourCycleEdges.2 hn⟩
      rw [hthrough] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inl h.symm)
    obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inl h.symm))
    obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inr (Or.inl h.symm)))
    obtain ⟨w, rfl⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hn (Or.inr (Or.inr (Or.inr h.symm)))
    obtain ⟨hab, hbc, hcd, hda, hac, hbd⟩ := hsq
    rcases ladder_classify u2 u3 (fun h ↦ hac (congrArg some h)) (fun h ↦ hbd (congrArg some h))
      (tripleUnion_adj_some.1 hab).2 (tripleUnion_adj_some.1 hbc).2 (tripleUnion_adj_some.1 hcd).2
      (tripleUnion_adj_some.1 hda).2 with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨x, isFourCycle_ladder_iff.1 ⟨hab, hbc, hcd, hda, hac, hbd⟩, rfl⟩
    · exact ⟨y, isFourCycle_ladder_iff.1 (IsFourCycle.rotate ⟨hab, hbc, hcd, hda, hac, hbd⟩),
        fourCycleEdges_rotate _ _ _ _⟩
    · exact ⟨z, isFourCycle_ladder_iff.1
        (IsFourCycle.rotate (IsFourCycle.rotate ⟨hab, hbc, hcd, hda, hac, hbd⟩)), by
        rw [ladderSquare, ← fourCycleEdges_rotate, ← fourCycleEdges_rotate]⟩
    · exact ⟨w, isFourCycle_ladder_iff.1 (IsFourCycle.rotate
        (IsFourCycle.rotate (IsFourCycle.rotate ⟨hab, hbc, hcd, hda, hac, hbd⟩))), by
        rw [ladderSquare, ← fourCycleEdges_rotate, ← fourCycleEdges_rotate,
          ← fourCycleEdges_rotate]⟩
  · rintro ⟨v, ⟨h0, h1, hm1⟩, rfl⟩
    exact mem_fourCycles.2 ⟨_, _, _, _, isFourCycle_ladder_iff.2 ⟨h0, h1, hm1⟩, rfl⟩

/-- **Lemma M (d)**, count. For `n` coprime to `15` (and `m ≥ 2`), `G_2` has exactly `m - 2`
4-cycles, the squares of the ladder. The file checks this only for prime `n ≤ 61`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem card_fourCycles_two (h : Nat.Coprime (2 * m - 1) 15) (hm : 2 ≤ m) :
    (fourCycles (tripleUnion m 2)).card = m - 2 := by
  have : Nontrivial (ZMod (2 * m - 1)) := ZMod.nontrivial_iff.2 (by omega)
  have u2 := isUnit_two' (m := m)
  rw [fourCycles_two h hm]
  set S := ({0, 1, -1} : Finset (ZMod (2 * m - 1)))ᶜ with hSdef
  have hS : S.card = 2 * m - 1 - 3 := by
    rw [hSdef, Finset.card_compl, ZMod.card, Finset.card_eq_three.2
      ⟨0, 1, -1, zero_ne_one, fun h' ↦ one_ne_zero (by lcpm h'), fun h' ↦ u2.ne_zero (by lcpm h'),
        rfl⟩]
  have hmemS : ∀ v, v ∈ S ↔ v ≠ 0 ∧ v ≠ 1 ∧ v ≠ -1 := fun v ↦ by
    simp [hSdef]
  have hconst : ∀ b ∈ S.image (ladderSquare m), ({a ∈ S | ladderSquare m a = b}).card = 2 := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨h0, h1, hm1⟩ := (hmemS v).1 hv
    have hneg : -v ∈ S := (hmemS _).2 ⟨neg_ne_zero.2 h0, fun h' ↦ hm1 (by lcpm h'),
      fun h' ↦ h1 (by lcpm h')⟩
    rw [Finset.card_eq_two]
    refine ⟨v, -v, fun h' ↦ h0 (u2.mul_right_eq_zero.1 (by lcpm h')), ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, ladderSquare_eq_iff]
    constructor
    · exact And.right
    · rintro (rfl | rfl)
      exacts [⟨hv, Or.inl rfl⟩, ⟨hneg, Or.inr rfl⟩]
  have hfib := Finset.card_eq_sum_card_image (ladderSquare m) S
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hfib
  omega


/-! ### Small cases -/

set_option maxRecDepth 100000 in
/-- Lemma M (a) at `n = 11`, `r = 3`, by `decide +kernel`: the only triangle is
`{1 - 3, 3 - 1, 3 + 1} = {9, 2, 4}` (`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem cliqueFinset_tripleUnion_six_three :
    (tripleUnion 6 3).cliqueFinset 3 = {{some 9, some 2, some 4}} := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Lemma M (c) at `n = 11`, `r = 3 ∈ A_3`, by `decide +kernel`: exactly one 4-cycle passes
through `∞` (`results/k3-workaround-spike.md`, Lemma M (c)). -/
theorem card_fourCyclesThrough_six_three :
    (fourCyclesThrough (tripleUnion 6 3) none).card = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Lemma M (d) at `n = 11`, by `decide +kernel`: `G_2` has `m - 2 = 4` 4-cycles
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem card_fourCycles_six_two : (fourCycles (tripleUnion 6 2)).card = 4 := by
  decide +kernel

end RoundRobin.Canonical

end Pairing
