import Repair.FactorCap.Scale
import Repair.TripleUnion

/-!
# Lemma M for progression triples

Put `n = 2m - 1`. This file completes Lemma M (a) and (d) for the progression (AP) triples
`{0, 1, r}`, `r ∈ {2, -1, 1/2}`.

* (a), AP half. `cliqueFinset_tripleUnion_of_isAP` : for `n ≥ 5` and `r` an AP, `G_r` has
  exactly the two triangles `T_r` and `apTriangle m r`, the triangle through `∞` formed by `∞`
  and the two ends of the progression. `card_cliqueFinset_tripleUnion_of_isAP` : there are two.
* (d), the other normalizations. `fourCycles_congr`, `card_fourCycles_congr` : the 4-cycles of
  isomorphic graphs correspond. `tripleUnionIsoNegOne : G_2 ≃g G_{-1}` is `x ↦ x - 1` and
  `tripleUnionIsoHalf : G_{1/2} ≃g G_2` is `x ↦ 2x`, both affine automorphisms of `𝓕`.
  `card_fourCycles_neg_one`, `card_fourCycles_of_two_mul_eq_one` and `card_fourCycles_of_isAP` :
  for `n` coprime to `15` every AP triple has exactly `m - 2` 4-cycles, the squares of its ladder.
* (d), the ladder of `{0, 1, 2}`. `ham_factor_two_zero` : `F_0 ∪ F_2` is one cycle.
  `chord_mem_ladderSquare` : `Q_v` and `Q_{v+2}` share the `F_1`-chord `{-v, v + 2}`.
  `ladder_ends` : the ladder closes through the two triangles, `Q_3` sharing the chord `{-1, 3}`
  with `T_2` and `Q_2` sharing the chord `{0, 2}` with the triangle `{∞, 0, 2}`.

Source: `results/k3-workaround-spike.md` §2.1, Lemma M.
-/

local macro "lcpm " e:term : tactic =>
  `(tactic| first | linear_combination (exp := 1) $e | linear_combination (exp := 1) -($e))

namespace Pairing

section FourCycleIso

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- The map on edge sets induced by a graph isomorphism (`results/k3-workaround-spike.md`,
Lemma M (d)). -/
def edgeSetMap (e : G ≃g G') : Finset (Sym2 V) ↪ Finset (Sym2 W) :=
  (Finset.mapEmbedding ⟨Sym2.map e, Sym2.map.injective e.injective⟩).toEmbedding

omit [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj] in
private theorem edgeSetMap_fourCycleEdges (e : G ≃g G') (a b c d : V) :
    edgeSetMap e (fourCycleEdges a b c d) = fourCycleEdges (e a) (e b) (e c) (e d) := by
  simp [edgeSetMap, fourCycleEdges, Finset.map_insert, Finset.map_singleton]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableRel G.Adj]
  [DecidableRel G'.Adj] in
private theorem isFourCycle_iso (e : G ≃g G') {a b c d : V} :
    IsFourCycle G' (e a) (e b) (e c) (e d) ↔ IsFourCycle G a b c d := by
  simp only [IsFourCycle, e.map_adj_iff, e.injective.ne_iff]

/-- A graph isomorphism carries the 4-cycles of `G` onto those of `G'`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem fourCycles_congr (e : G ≃g G') : fourCycles G' = (fourCycles G).map (edgeSetMap e) := by
  ext s
  rw [Finset.mem_map, mem_fourCycles]
  constructor
  · rintro ⟨a, b, c, d, h, rfl⟩
    refine ⟨fourCycleEdges (e.symm a) (e.symm b) (e.symm c) (e.symm d),
      mem_fourCycles.2 ⟨_, _, _, _, ?_, rfl⟩, ?_⟩
    · rw [← isFourCycle_iso e]
      simpa using h
    · simp [edgeSetMap_fourCycleEdges]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨a, b, c, d, h, rfl⟩ := mem_fourCycles.1 ht
    exact ⟨e a, e b, e c, e d, (isFourCycle_iso e).2 h, (edgeSetMap_fourCycleEdges e _ _ _ _).symm⟩

/-- Isomorphic graphs have equally many 4-cycles (`results/k3-workaround-spike.md`,
Lemma M (d)). -/
theorem card_fourCycles_congr (e : G ≃g G') : (fourCycles G').card = (fourCycles G).card := by
  rw [fourCycles_congr e, Finset.card_map]

end FourCycleIso

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-! ### (a) Triangles of an AP triple -/

private theorem tri_vertex' {x y z r : ZMod (2 * m - 1)} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (h1 : x + y = 0 ∨ x + y = 2 ∨ x + y = 2 * r)
    (h2 : x + z = 0 ∨ x + z = 2 ∨ x + z = 2 * r) (h3 : y + z = 0 ∨ y + z = 2 ∨ y + z = 2 * r) :
    x = 1 - r ∨ x = r - 1 ∨ x = r + 1 := by
  have u2 := isUnit_two' (m := m)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
    first
    | exact absurd (by lcpm h1 - h2) hyz
    | exact absurd (by lcpm h1 - h3) hxz
    | exact absurd (by lcpm h2 - h3) hxy
    | exact Or.inl (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3)))
    | exact Or.inr (Or.inl (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3))))
    | exact Or.inr (Or.inr (sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by lcpm h1 + h2 - h3))))

private theorem mem_rainbow_of_triangle' {r : ZMod (2 * m - 1)} {u v w : Vertex m}
    (hu : u ≠ none) (hv : v ≠ none) (hw : w ≠ none) (huv : (tripleUnion m r).Adj u v)
    (huw : (tripleUnion m r).Adj u w) (hvw : (tripleUnion m r).Adj v w) : u ∈ rainbow m r := by
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 hu
  obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hv
  obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 hw
  obtain ⟨hxy, h1⟩ := tripleUnion_adj_some.1 huv
  obtain ⟨hxz, h2⟩ := tripleUnion_adj_some.1 huw
  obtain ⟨hyz, h3⟩ := tripleUnion_adj_some.1 hvw
  rcases tri_vertex' hxy hxz hyz h1 h2 h3 with h | h | h <;> simp [rainbow, h]

private theorem eq_rainbow_of_triangle' {r : ZMod (2 * m - 1)} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    {a b c : Vertex m} (ha : a ≠ none) (hb : b ≠ none) (hc : c ≠ none)
    (hab : (tripleUnion m r).Adj a b) (hac : (tripleUnion m r).Adj a c)
    (hbc : (tripleUnion m r).Adj b c) : ({a, b, c} : Finset (Vertex m)) = rainbow m r := by
  refine Finset.eq_of_subset_of_card_le ?_ (by
    rw [(rainbow_isClique hr0 hr1).card_eq,
      (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩).card_eq])
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_rainbow_of_triangle' ha hb hc hab hac hbc
  · exact mem_rainbow_of_triangle' hb ha hc hab.symm hbc hac
  · exact mem_rainbow_of_triangle' hc ha hb hac.symm hbc.symm hab

/-- The triangle of an AP triple through `∞`: `∞` and the two ends of the progression, so
`{∞, 0, 2}` for `r = 2`, `{∞, 1, -1}` for `r = -1` and `{∞, 0, 1}` for `r = 1/2`
(`results/k3-workaround-spike.md`, Lemma M (a)). -/
def apTriangle (m : ℕ) (r : ZMod (2 * m - 1)) : Finset (Vertex m) :=
  if r = 2 then {none, some 0, some r} else if r = -1 then {none, some 1, some r}
  else {none, some 0, some 1}

omit [NeZero m] in
/-- `∞` lies on `apTriangle m r` (`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem none_mem_apTriangle (r : ZMod (2 * m - 1)) : none ∈ apTriangle m r := by
  unfold apTriangle
  split_ifs <;> simp

omit [NeZero m] in
private theorem three_ne_zero_of (hm : 3 ≤ m) : (3 : ZMod (2 * m - 1)) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod (2 * m - 1)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)

private theorem ne_zero_one_of_isAP (hm : 3 ≤ m) {r : ZMod (2 * m - 1)} (hAP : IsAP r) :
    r ≠ 0 ∧ r ≠ 1 := by
  have : Nontrivial (ZMod (2 * m - 1)) := ZMod.nontrivial_iff.2 (by omega)
  have u2 := isUnit_two' (m := m)
  have h1 : (1 : ZMod (2 * m - 1)) ≠ 0 := one_ne_zero
  rcases hAP with h | h | h
  · exact ⟨fun h' ↦ u2.ne_zero (by lcpm h - h'), fun h' ↦ h1 (by lcpm h - h')⟩
  · exact ⟨fun h' ↦ h1 (by lcpm h - h'), fun h' ↦ u2.ne_zero (by lcpm h - h')⟩
  · exact ⟨fun h' ↦ h1 (by lcpm h - 2 * h'), fun h' ↦ h1 (by lcpm h - 2 * h')⟩

private theorem triangle_through_none (hm : 3 ≤ m) {r : ZMod (2 * m - 1)} (hAP : IsAP r)
    {y z : ZMod (2 * m - 1)} (hy : (tripleUnion m r).Adj none (some y))
    (hz : (tripleUnion m r).Adj none (some z)) (hyz : (tripleUnion m r).Adj (some y) (some z)) :
    ({none, some y, some z} : Finset (Vertex m)) = apTriangle m r := by
  have h3 := three_ne_zero_of hm
  obtain ⟨hr0, hr1⟩ := ne_zero_one_of_isAP hm hAP
  rw [tripleUnion_adj_none] at hy hz
  obtain ⟨hne, hs⟩ := tripleUnion_adj_some.1 hyz
  have hpair : (r = 2 ∧ (y = 0 ∧ z = r ∨ y = r ∧ z = 0)) ∨ (r = -1 ∧ (y = 1 ∧ z = r ∨ y = r ∧ z = 1)) ∨
      (2 * r = 1 ∧ (y = 0 ∧ z = 1 ∨ y = 1 ∧ z = 0)) := by
    rcases hy with hy | hy | hy <;> subst y <;> rcases hz with hz | hz | hz <;> subst z <;>
      rcases hs with h | h | h <;>
      first
      | exact absurd rfl hne
      | exact absurd (by lcpm r * h) hr0
      | exact absurd (by lcpm h) hr0
      | exact absurd (by lcpm h) hr1
      | exact Or.inl ⟨by lcpm h, by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
      | exact Or.inr (Or.inl ⟨by lcpm h,
          by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩)
      | exact Or.inr (Or.inr ⟨by lcpm h,
          by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩)
  have hswap : ∀ a b : ZMod (2 * m - 1),
      ({none, some b, some a} : Finset (Vertex m)) = {none, some a, some b} :=
    fun a b ↦ by rw [Finset.pair_comm]
  unfold apTriangle
  rcases hpair with ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
    ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · rw [ite_eq_left h]
  · rw [ite_eq_left h, hswap]
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - h'), ite_eq_left h]
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - h'), ite_eq_left h, hswap]
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h'), ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h')]
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h'), ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h'), hswap]

/-- `apTriangle m r` is a triangle of `G_r` for every AP `r` and `n ≥ 5`
(`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem apTriangle_isClique (hm : 3 ≤ m) {r : ZMod (2 * m - 1)} (hAP : IsAP r) :
    (tripleUnion m r).IsNClique 3 (apTriangle m r) := by
  have h3 := three_ne_zero_of hm
  have : Nontrivial (ZMod (2 * m - 1)) := ZMod.nontrivial_iff.2 (by omega)
  obtain ⟨hr0, hr1⟩ := ne_zero_one_of_isAP hm hAP
  have h01 : (0 : ZMod (2 * m - 1)) ≠ 1 := zero_ne_one
  unfold apTriangle
  rcases hAP with h | h | h
  · rw [ite_eq_left h, SimpleGraph.is3Clique_triple_iff, tripleUnion_adj_none, tripleUnion_adj_none,
      tripleUnion_adj_some]
    exact ⟨Or.inl rfl, Or.inr (Or.inr rfl), hr0.symm, Or.inr (Or.inl (by lcpm h))⟩
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - h'), ite_eq_left h, SimpleGraph.is3Clique_triple_iff,
      tripleUnion_adj_none, tripleUnion_adj_none, tripleUnion_adj_some]
    exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hr1.symm, Or.inl (by lcpm h)⟩
  · rw [ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h'), ite_eq_right fun h' ↦ h3 (by lcpm h - 2 * h'),
      SimpleGraph.is3Clique_triple_iff, tripleUnion_adj_none, tripleUnion_adj_none,
      tripleUnion_adj_some]
    exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), h01, Or.inr (Or.inr (by lcpm h))⟩

/-- **Lemma M (a)**, AP case. If `{0, 1, r}` is a progression and `n ≥ 5`, `G_r` has exactly two
triangles, the rainbow triangle `T_r` and the triangle `apTriangle m r` through `∞`. For `n = 3`
the graph is `K_4`, which has four (`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem cliqueFinset_tripleUnion_of_isAP (hm : 3 ≤ m) {r : ZMod (2 * m - 1)} (hAP : IsAP r) :
    (tripleUnion m r).cliqueFinset 3 = {rainbow m r, apTriangle m r} := by
  obtain ⟨hr0, hr1⟩ := ne_zero_one_of_isAP hm hAP
  ext s
  rw [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hs
    by_cases ha : a = none
    · subst ha
      obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hab.ne.symm
      obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 hac.ne.symm
      exact Or.inr (triangle_through_none hm hAP hab hac hbc)
    by_cases hb : b = none
    · subst hb
      obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 ha
      obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 hbc.ne.symm
      rw [Finset.insert_comm]
      exact Or.inr (triangle_through_none hm hAP hab.symm hbc hac)
    by_cases hc : c = none
    · subst hc
      obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 ha
      obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.1 hb
      rw [Finset.pair_comm, Finset.insert_comm]
      exact Or.inr (triangle_through_none hm hAP hac.symm hbc.symm hab)
    exact Or.inl (eq_rainbow_of_triangle' hr0 hr1 ha hb hc hab hac hbc)
  · rcases hs with rfl | rfl
    exacts [rainbow_isClique hr0 hr1, apTriangle_isClique hm hAP]

/-- **Lemma M (a)**, AP case, count. An AP triple has exactly two triangles for `n ≥ 5`
(`results/k3-workaround-spike.md`, Lemma M (a)). -/
theorem card_cliqueFinset_tripleUnion_of_isAP (hm : 3 ≤ m) {r : ZMod (2 * m - 1)}
    (hAP : IsAP r) : ((tripleUnion m r).cliqueFinset 3).card = 2 := by
  rw [cliqueFinset_tripleUnion_of_isAP hm hAP, Finset.card_pair]
  intro h
  have := none_mem_apTriangle (m := m) r
  rw [← h] at this
  simp [rainbow] at this

/-! ### (d) The ladders of `{0, 1, -1}` and `{0, 1, 1/2}` -/

/-- A permutation `f` of `ℤ/n` that matches the sums and the neighbours of `∞` of `G_r` with
those of `G_{r'}` gives an isomorphism `G_r ≃g G_{r'}`, fixing `∞`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
def tripleUnionIso {r r' : ZMod (2 * m - 1)} (f : ZMod (2 * m - 1) ≃ ZMod (2 * m - 1))
    (hsome : ∀ x y, (f x + f y = 0 ∨ f x + f y = 2 ∨ f x + f y = 2 * r') ↔
      (x + y = 0 ∨ x + y = 2 ∨ x + y = 2 * r))
    (hnone : ∀ x, (f x = 0 ∨ f x = 1 ∨ f x = r') ↔ (x = 0 ∨ x = 1 ∨ x = r)) :
    tripleUnion m r ≃g tripleUnion m r' where
  toEquiv := Equiv.optionCongr f
  map_rel_iff' := by
    intro a b
    rcases a with _ | x <;> rcases b with _ | y
    · simp
    · simp only [Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        tripleUnion_adj_none]
      exact hnone y
    · simp only [Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        tripleUnion_adj_some_none]
      exact hnone x
    · simp only [Equiv.optionCongr_apply, Option.map_some, tripleUnion_adj_some,
        f.injective.ne_iff]
      rw [hsome]

/-- `x ↦ x - 1` is an isomorphism `G_2 ≃g G_{-1}`, since it maps `{0, 1, 2}` to `{-1, 0, 1}`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
def tripleUnionIsoNegOne (m : ℕ) [NeZero m] : tripleUnion m 2 ≃g tripleUnion m (-1) :=
  tripleUnionIso (Equiv.addRight (-1))
    (fun x y ↦ by
      simp only [Equiv.coe_addRight]
      constructor <;> rintro (h | h | h) <;>
        first
        | exact Or.inl (by lcpm h)
        | exact Or.inr (Or.inl (by lcpm h))
        | exact Or.inr (Or.inr (by lcpm h)))
    (fun x ↦ by
      simp only [Equiv.coe_addRight]
      constructor <;> rintro (h | h | h) <;>
        first
        | exact Or.inl (by lcpm h)
        | exact Or.inr (Or.inl (by lcpm h))
        | exact Or.inr (Or.inr (by lcpm h)))

/-- For `2 r = 1`, `x ↦ 2x` is an isomorphism `G_r ≃g G_2`, since it maps `{0, 1, 1/2}` to
`{0, 2, 1}` (`results/k3-workaround-spike.md`, Lemma M (d)). -/
noncomputable def tripleUnionIsoHalf {r : ZMod (2 * m - 1)} (hr : 2 * r = 1) :
    tripleUnion m r ≃g tripleUnion m 2 :=
  tripleUnionIso isUnit_two'.unit.mulLeft
    (fun x y ↦ by
      simp only [Units.mulLeft_apply, IsUnit.unit_spec]
      constructor <;> rintro (h | h | h)
      · exact Or.inl (by linear_combination r * h - (x + y) * hr)
      · exact Or.inr (Or.inr (by linear_combination r * h - (x + y) * hr))
      · exact Or.inr (Or.inl (by linear_combination r * h - (x + y - 2) * hr))
      · exact Or.inl (by linear_combination 2 * h)
      · exact Or.inr (Or.inr (by linear_combination 2 * h))
      · exact Or.inr (Or.inl (by linear_combination 2 * h + 2 * hr)))
    (fun x ↦ by
      simp only [Units.mulLeft_apply, IsUnit.unit_spec]
      constructor <;> rintro (h | h | h)
      · exact Or.inl (by linear_combination r * h - x * hr)
      · exact Or.inr (Or.inr (by linear_combination r * h - x * hr))
      · exact Or.inr (Or.inl (by linear_combination r * h - (x - 1) * hr))
      · exact Or.inl (by linear_combination 2 * h)
      · exact Or.inr (Or.inr (by linear_combination 2 * h))
      · exact Or.inr (Or.inl (by linear_combination 2 * h + hr)))

/-- **Lemma M (d)** for `r = -1`. For `n` coprime to `15` (and `m ≥ 2`), `G_{-1}` has exactly
`m - 2` 4-cycles, the squares of its ladder (`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem card_fourCycles_neg_one (h : Nat.Coprime (2 * m - 1) 15) (hm : 2 ≤ m) :
    (fourCycles (tripleUnion m (-1))).card = m - 2 := by
  rw [card_fourCycles_congr (tripleUnionIsoNegOne m), card_fourCycles_two h hm]

/-- **Lemma M (d)** for `r = 1/2`. For `2 r = 1` and `n` coprime to `15` (and `m ≥ 2`), `G_r` has
exactly `m - 2` 4-cycles, the squares of its ladder (`results/k3-workaround-spike.md`,
Lemma M (d)). -/
theorem card_fourCycles_of_two_mul_eq_one {r : ZMod (2 * m - 1)} (hr : 2 * r = 1)
    (h : Nat.Coprime (2 * m - 1) 15) (hm : 2 ≤ m) :
    (fourCycles (tripleUnion m r)).card = m - 2 := by
  rw [← card_fourCycles_congr (tripleUnionIsoHalf hr), card_fourCycles_two h hm]

/-- **Lemma M (d)**, all AP normalizations. For `n` coprime to `15` (and `m ≥ 2`), every AP triple
`G_r` has exactly `m - 2` 4-cycles (`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem card_fourCycles_of_isAP {r : ZMod (2 * m - 1)} (hAP : IsAP r)
    (h : Nat.Coprime (2 * m - 1) 15) (hm : 2 ≤ m) :
    (fourCycles (tripleUnion m r)).card = m - 2 := by
  rcases hAP with rfl | rfl | hr
  exacts [card_fourCycles_two h hm, card_fourCycles_neg_one h hm,
    card_fourCycles_of_two_mul_eq_one hr h hm]

/-- **Lemma M (d)**, the cycle. `F_0 ∪ F_2` is one cycle, the image of the cycle `F_0 ∪ F_1` under
the affine automorphism `x ↦ 2x` (`results/k3-workaround-spike.md`, Lemma M (d)). It is a case of
`ham_factor_of_isUnit_sub`. -/
theorem ham_factor_two_zero : Ham (factor m 2) (factor m 0) :=
  ham_factor_of_isUnit_sub m (by rw [sub_zero]; exact isUnit_two')

/-- **Lemma M (d)**, the chords. For `v ≠ -1`, `{-v, v + 2}` is an edge of `F_1` lying on both
`Q_v` and `Q_{v+2}`, so consecutive squares of the ladder are glued along `F_1`-chords
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem chord_mem_ladderSquare {v : ZMod (2 * m - 1)} (hv : v ≠ -1) :
    (factor m 1).toGraph.Adj (some (-v)) (some (v + 2)) ∧
      s(some (-v), some (v + 2)) ∈ ladderSquare m v ∧
      s(some (-v), some (v + 2)) ∈ ladderSquare m (v + 2) := by
  have u2 := isUnit_two' (m := m)
  refine ⟨factor_adj_some.2 ⟨fun h ↦ hv (eq_neg_of_add_eq_zero_left
    (u2.mul_right_eq_zero.1 (by lcpm h))), by ring⟩, by simp [ladderSquare, fourCycleEdges], ?_⟩
  simp only [ladderSquare, fourCycleEdges, Finset.mem_insert, Finset.mem_singleton]
  right; right; right
  rw [show (2 : ZMod (2 * m - 1)) - (v + 2) = -v by ring]

omit [NeZero m] in
/-- **Lemma M (d)**, the ends of the ladder. The ladder of `G_2` closes through the two triangles of
Lemma M (a): `Q_3` contains the `F_1`-chord `{-1, 3}` of the rainbow triangle `T_2 = {-1, 1, 3}`,
and `Q_2` contains the `F_1`-chord `{0, 2}` of the triangle `{∞, 0, 2}`
(`results/k3-workaround-spike.md`, Lemma M (d)). -/
theorem ladder_ends :
    s(some (-1), some 3) ∈ ladderSquare m 3 ∧ some (-1) ∈ rainbow m 2 ∧ some 3 ∈ rainbow m 2 ∧
      s(some 0, some 2) ∈ ladderSquare m 2 ∧ some 0 ∈ apTriangle m 2 ∧
      some 2 ∈ apTriangle m 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ladderSquare, fourCycleEdges, Finset.mem_insert, Finset.mem_singleton]
    right; right; right
    rw [show (2 : ZMod (2 * m - 1)) - 3 = -1 by ring]
  · simp only [rainbow, Finset.mem_insert, Finset.mem_singleton, Option.some_inj]
    left
    ring
  · simp only [rainbow, Finset.mem_insert, Finset.mem_singleton, Option.some_inj]
    right; right
    ring
  · simp only [ladderSquare, fourCycleEdges, Finset.mem_insert, Finset.mem_singleton]
    right; right; right
    rw [sub_self]
  · simp [apTriangle]
  · simp [apTriangle]

end RoundRobin.Canonical

end Pairing
