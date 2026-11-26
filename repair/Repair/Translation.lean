import Repair.Reflection

/-!
# Translation repairs of general tails (COD-205)

Source: `results/ulzd-general-extend.md` (organize-archive 6d8435d) §1 to §3, with the scope and
constants of its review `results/review-ulzd-general.md` (d6cc131). Everything here is stated for
any tail `T` of any gadget, through a completion `M` of `T` (a perfect matching of `V` that
extends `T`), and any shift `σ`. The reflection repair of `results/ulzd-rescue.md` (2f5b9d3),
formalized in `Repair/Reflection.lean` (main 2b0e563), is the case `T = F_0`.

General part, on `ℤ/n ∪ {∞}` for odd `n`.
* `translation_cycle` (Lemma 2′, the translation certificate) : a walk
  `a, q_1, T(q_1), …, q_k, T(q_k), b` that alternates `F_t` and `P`, whose shifted copy
  `a + σ, q_1 - σ, T(q_1) + σ, …, b - σ` also has its `P`-edges in `P`, and whose ends carry the
  `Q`-edges `{a, a + σ}` and `{b, b - σ}`, spans a vertex set `C ∌ ∞` closed under `P` and `F_t`
  with at most `4k + 4` vertices. `not_ham_of_translation_cycle` : so `¬Ham P F_t`.
  `translation_cycle_neg` is the case `T = F_0`, Lemma 2 of the rescue in orbit form.
* `ShiftSys n` : a set `W` (the `W`-parts of the units) and a shift `σ` with `W ∩ (W - σ) = ∅`.
  `ShiftSys.Q` pairs `w` with `w - σ`, a perfect matching of `V(W) = W ∪ (W - σ)`, and
  `ShiftSys.repair M` replaces the edges of `M` inside `V(W)` by `Q` (the swap of Lemma 2′).
  `ShiftSys.ofSeeds` is the system of the units `U(z) = {z, T(z), z - σ, T(z) + σ}` of a seed set,
  and `ShiftSys.ofSeeds_closed` : coherent seeds give an `M`-closed `V(W)`.
* `ShiftSys.spotRepair` : the repair followed by any rematching `Q_Y` of an `M`-closed set `Y`
  disjoint from `V(W)`, which holds the spots of Theorem B, Step 0.
* `IsTransCert`, `IsCleanCycle` : a Lemma 2′ certificate for `F_t` through two `W`-vertices with
  untouched coherent interior, and a cycle of `M ∪ F_t` missing some vertex and the touched set.
  `isTransCert_of_orbit` : the certificate read off one stretch of a `Φ_t = F_t ∘ M` orbit.
* `ShiftSys.isZeroState_spotRepair` (the deterministic core of Theorem B) : if every `t` has a
  spot, a certificate or a clean cycle, the repaired matching is a zero state.
  `ShiftSys.two_mul_tailDist_spotRepair_le` : its cost is `2|T ∖ P| ≤ 2|W| + |Y|`.

Round-robin part, on `V_m`.
* `Canonical.HasTransCover`, `Canonical.exists_zeroState_of_hasTransCover`,
  `Canonical.repairBound_of_hasTransCover` : a translation cover of cost `K` gives `ρ(T) ≤ K`, for
  every six-vertex gadget and every tail. The probabilistic choice of seeds, `σ` and `ℓ` in
  Theorem B stays a hypothesis.
* `Canonical.ReflSet.repair_eq_shiftRepair` : a one-centre reflection repair of
  `Repair/Reflection.lean` (main 2b0e563) is the translation repair of the same matching.

Corollary C2, deterministic part (normalized coordinates `a = 0`, `b = 1`, `σ = 2`; the affine
normalization itself is `isZeroState_affine_smul_iff` and is not redone here).
* `coherent_two` (arcs) : a vertex whose completion edges at `z`, `z - 2`, `2 - z` lie in
  `F_0 ∪ F_1` is `2`-coherent. `card_incoherent_two_le` : at most `3|X|` incoherent vertices, `X`
  the vertices off `F_0 ∪ F_1`.
* `orbit_drift`, `mul_eq_of_returns` : on such stretches `Φ_t^h(x) - x = 2th - 2S`, so a type-1
  return gives `t h = S + k`. `blindSet`, `mem_blindSet_of_returns`, `card_blindSet_le`,
  `two_mul_sum_Ico_le` : every type-1 blind factor lies in an explicit set of size
  `Σ_{h<ℓ} (h + 5) ≤ ℓ²/2 + 5ℓ`.
* `mirror_eq`, `mirrorSet`, `mem_mirrorSet`, `card_mirrorSet_le` : forward type-2 points of `F_t`
  lie in an explicit set of size `5ℓ(ℓ + 1)`.
* `Canonical.exists_zeroState_of_blindCover` : spots on `blindSet` and certificates elsewhere give
  `ρ(T) ≤ |W| + 2 Σ_{h<ℓ} (h + 5)`.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [DecidableEq V]

/-- A perfect matching `P` that agrees with a completion `M` of the tail `T` off a set `X` is
within `|X| / 2` of `T`, `2|T ∖ P| ≤ |X|` (`ulzd-general-extend.md` (6d8435d) §1, the cost of a
repair). -/
theorem two_mul_tailDist_le_card_of_agree {U : Finset V} (T : PerfectMatching U)
    {M P : PerfectMatching V} (hM : ∀ u : U, M.mate u = T.mate u) (X : Finset V)
    (hX : ∀ v ∉ X, P.mate v = M.mate v) : 2 * tailDist P T ≤ X.card := by
  rw [two_mul_tailDist]
  refine Finset.card_le_card_of_injOn (fun u : U ↦ (u : V)) (fun u hu ↦ ?_)
    (fun u _ w _ h ↦ Subtype.ext h)
  rw [Finset.mem_coe, Finset.mem_filter] at hu
  rw [Finset.mem_coe]
  by_contra h
  exact hu.2 ((hM u).symm.trans (hX (u : V) h).symm)

end PerfectMatching

namespace RoundRobin

open PerfectMatching

variable {n : ℕ}

/-! ### Lemma 2′, the translation certificate -/

/-- The shifted copy of a certificate walk, `y j + σ` at even and `y j - σ` at odd indices
(`ulzd-general-extend.md` (6d8435d) Lemma 2′, the walk `a + σ, q_1 - σ, T(q_1) + σ, …`). -/
def shiftedWalk (σ : ZMod n) (y : ℕ → ZMod n) (j : ℕ) : ZMod n :=
  if j % 2 = 0 then y j + σ else y j - σ

theorem shiftedWalk_even (σ : ZMod n) (y : ℕ → ZMod n) (i : ℕ) :
    shiftedWalk σ y (2 * i) = y (2 * i) + σ := by
  simp [shiftedWalk]

theorem shiftedWalk_odd (σ : ZMod n) (y : ℕ → ZMod n) (i : ℕ) :
    shiftedWalk σ y (2 * i + 1) = y (2 * i + 1) - σ := by
  simp [shiftedWalk, Nat.add_mod]

/-- The vertices of the closed walk of Lemma 2′, the walk `y 0, …, y (2k + 1)` and its shifted
copy. -/
def walkSet (σ : ZMod n) (y : ℕ → ZMod n) (k : ℕ) : Finset (Option (ZMod n)) :=
  (Finset.range (2 * k + 2)).image (fun j ↦ some (y j)) ∪
    (Finset.range (2 * k + 2)).image (fun j ↦ some (shiftedWalk σ y j))

theorem card_walkSet_le (σ : ZMod n) (y : ℕ → ZMod n) (k : ℕ) :
    (walkSet σ y k).card ≤ 4 * k + 4 := by
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.range (2 * k + 2)) (f := fun j ↦ some (y j))
  have h2 := Finset.card_image_le (s := Finset.range (2 * k + 2))
    (f := fun j ↦ some (shiftedWalk σ y j))
  rw [Finset.card_range] at h1 h2
  omega

/-- **Lemma 2′** of `ulzd-general-extend.md` (6d8435d) §2, the translation certificate, for any
perfect matching `P`. Write the walk as `y 0 = a`, `y (2l - 1) = q_l`, `y (2l) = T(q_l)` and
`y (2k + 1) = b`. Suppose its `F_t`-steps are reflections, `y (2i) + y (2i + 1) = 2t` with
`y (2i) ≠ t` and `y (2i) + σ ≠ t` (conditions (i) and (iii)), its `P`-steps
`{q_l, T(q_l)}` and the shifted `{q_l - σ, T(q_l) + σ}` are edges of `P` (condition (ii)), and
`P` holds the `Q`-edges `{a, a + σ}` and `{b, b - σ}`. Then the walk and its shifted copy span a
set `C ∌ ∞` that is closed under `P` and `F_t`, with `|C| ≤ 4k + 4`. So the cycle of `P ∪ F_t`
through `a` has at most `4k + 4` vertices. Since `∞ ∉ C`, the hypothesis `4k + 4 < 2m` of the
paper is not needed. The case `T = F_0` is `translation_cycle_neg`. -/
theorem translation_cycle (hn : Odd n) (P : PerfectMatching (Option (ZMod n))) {t σ : ZMod n}
    {k : ℕ} {y : ℕ → ZMod n} (hF : ∀ i ≤ k, y (2 * i) + y (2 * i + 1) = 2 * t)
    (ht : ∀ i ≤ k, y (2 * i) ≠ t ∧ y (2 * i) + σ ≠ t)
    (hP : ∀ i < k, P.mate (some (y (2 * i + 1))) = some (y (2 * i + 2)) ∧
      P.mate (some (y (2 * i + 1) - σ)) = some (y (2 * i + 2) + σ))
    (ha : P.mate (some (y 0)) = some (y 0 + σ))
    (hb : P.mate (some (y (2 * k + 1))) = some (y (2 * k + 1) - σ)) :
    ∃ C : Finset (Option (ZMod n)), some (y 0) ∈ C ∧ none ∉ C ∧ (∀ p ∈ C, P.mate p ∈ C) ∧
      (∀ p ∈ C, (factor hn t).mate p ∈ C) ∧ C.card ≤ 4 * k + 4 := by
  have hmem1 : ∀ j < 2 * k + 2, some (y j) ∈ walkSet σ y k := fun j hj ↦
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hj))
  have hmem2 : ∀ j < 2 * k + 2, some (shiftedWalk σ y j) ∈ walkSet σ y k := fun j hj ↦
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hj))
  have hFt : ∀ i ≤ k, (factor hn t).mate (some (y (2 * i))) = some (y (2 * i + 1)) := by
    intro i hi
    rw [factor_mate, mateFn_of_ne _ _ (ht i hi).1, ← hF i hi]
    congr 1
    ring
  have hFt' : ∀ i ≤ k, (factor hn t).mate (some (shiftedWalk σ y (2 * i))) =
      some (shiftedWalk σ y (2 * i + 1)) := by
    intro i hi
    rw [shiftedWalk_even, shiftedWalk_odd, factor_mate, mateFn_of_ne _ _ (ht i hi).2,
      ← hF i hi]
    congr 1
    ring
  have hPy : ∀ j < 2 * k + 2, P.mate (some (y j)) ∈ walkSet σ y k := by
    intro j hj
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · have h0 := shiftedWalk_even σ y 0
        rw [mul_zero] at h0
        rw [mul_zero, ha, ← h0]
        exact hmem2 0 (by omega)
      · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, ← (hP i (by omega)).1, mate_mate]
        exact hmem1 _ (by omega)
    · rcases eq_or_lt_of_le (show i ≤ k by omega) with rfl | hi
      · rw [hb, ← shiftedWalk_odd]
        exact hmem2 _ (by omega)
      · rw [(hP i hi).1]
        exact hmem1 _ (by omega)
  have hPy' : ∀ j < 2 * k + 2, P.mate (some (shiftedWalk σ y j)) ∈ walkSet σ y k := by
    intro j hj
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [shiftedWalk_even]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [mul_zero, ← ha, mate_mate]
        exact hmem1 0 (by omega)
      · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, ← (hP i (by omega)).2, mate_mate,
          ← shiftedWalk_odd]
        exact hmem2 _ (by omega)
    · rw [shiftedWalk_odd]
      rcases eq_or_lt_of_le (show i ≤ k by omega) with rfl | hi
      · rw [← hb, mate_mate]
        exact hmem1 _ (by omega)
      · rw [(hP i hi).2, show 2 * i + 2 = 2 * (i + 1) by ring, ← shiftedWalk_even]
        exact hmem2 _ (by omega)
  have hFy : ∀ j < 2 * k + 2, (factor hn t).mate (some (y j)) ∈ walkSet σ y k := by
    intro j hj
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [hFt i (by omega)]
      exact hmem1 _ (by omega)
    · rw [← hFt i (by omega), mate_mate]
      exact hmem1 _ (by omega)
  have hFy' : ∀ j < 2 * k + 2, (factor hn t).mate (some (shiftedWalk σ y j)) ∈ walkSet σ y k := by
    intro j hj
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [hFt' i (by omega)]
      exact hmem2 _ (by omega)
    · rw [← hFt' i (by omega), mate_mate]
      exact hmem2 _ (by omega)
  refine ⟨walkSet σ y k, hmem1 0 (by omega), by simp [walkSet], ?_, ?_, card_walkSet_le σ y k⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp <;> obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    · exact hPy j (Finset.mem_range.1 hj)
    · exact hPy' j (Finset.mem_range.1 hj)
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp <;> obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    · exact hFy j (Finset.mem_range.1 hj)
    · exact hFy' j (Finset.mem_range.1 hj)

/-- Lemma 2′ of `ulzd-general-extend.md` (6d8435d) §2: the certificate of `translation_cycle`
makes `t` dead in `P`, `¬Ham P F_t`. -/
theorem not_ham_of_translation_cycle (hn : Odd n) (P : PerfectMatching (Option (ZMod n)))
    {t σ : ZMod n} {k : ℕ} {y : ℕ → ZMod n} (hF : ∀ i ≤ k, y (2 * i) + y (2 * i + 1) = 2 * t)
    (ht : ∀ i ≤ k, y (2 * i) ≠ t ∧ y (2 * i) + σ ≠ t)
    (hP : ∀ i < k, P.mate (some (y (2 * i + 1))) = some (y (2 * i + 2)) ∧
      P.mate (some (y (2 * i + 1) - σ)) = some (y (2 * i + 2) + σ))
    (ha : P.mate (some (y 0)) = some (y 0 + σ))
    (hb : P.mate (some (y (2 * k + 1))) = some (y (2 * k + 1) - σ)) :
    ¬Ham P (factor hn t) := by
  obtain ⟨C, hyC, hnC, hPC, hFC, -⟩ := translation_cycle hn P hF ht hP ha hb
  exact not_ham_of_closed P (factor hn t) (C : Set (Option (ZMod n))) hPC hFC hyC hnC

/-- Lemma 2′ at `T = F_0`, which is Lemma 2 of `ulzd-rescue.md` (2f5b9d3) in orbit form. Let the
labels `x + 2lt` and `x + 2lt - σ` keep their `F_0`-edges in `P` for `1 ≤ l ≤ k`, and let `P`
hold the `Q_σ`-edges `{σ - x, -x}` and `{y, y - σ}` with `y = x + 2(k + 1)t`. Then some set
`C ∌ ∞` with `some (-x) ∈ C` is closed under `P` and `F_t`, with `|C| ≤ 4k + 4`. In the
positions `λ = (2t)⁻¹` of `Repair/Reflection.lean` (main 2b0e563) the label `x + 2lt` sits at
`v + l`, so condition (b) of `reflection_cycle` there, for same-sign positions `v < w = v + k + 1`,
supplies the kept edges here, and `δ = w - v = k + 1` matches `4δ = 4k + 4`. -/
theorem translation_cycle_neg (hn : Odd n) (P : PerfectMatching (Option (ZMod n)))
    {t σ x : ZMod n} {k : ℕ}
    (hint : ∀ l, 1 ≤ l → l ≤ k →
      P.mate (some (x + 2 * l * t)) = some (-(x + 2 * l * t)) ∧
        P.mate (some (x + 2 * l * t - σ)) = some (σ - (x + 2 * l * t)))
    (ht : ∀ l ≤ k, -(x + 2 * l * t) ≠ t ∧ σ - (x + 2 * l * t) ≠ t)
    (hx : P.mate (some (σ - x)) = some (-x))
    (hy : P.mate (some (x + 2 * (k + 1) * t)) = some (x + 2 * (k + 1) * t - σ)) :
    ∃ C : Finset (Option (ZMod n)), some (-x) ∈ C ∧ none ∉ C ∧ (∀ p ∈ C, P.mate p ∈ C) ∧
      (∀ p ∈ C, (factor hn t).mate p ∈ C) ∧ C.card ≤ 4 * k + 4 := by
  set y : ℕ → ZMod n := fun j ↦
    if j % 2 = 0 then -(x + 2 * ((j / 2 : ℕ) : ZMod n) * t)
    else x + 2 * ((j / 2 + 1 : ℕ) : ZMod n) * t with hy_def
  have hye : ∀ i : ℕ, y (2 * i) = -(x + 2 * (i : ZMod n) * t) := by
    intro i
    simp only [hy_def]
    rw [ite_eq_left (by omega), show 2 * i / 2 = i by omega]
  have hyo : ∀ i : ℕ, y (2 * i + 1) = x + 2 * ((i + 1 : ℕ) : ZMod n) * t := by
    intro i
    simp only [hy_def]
    rw [ite_eq_right (by omega), show (2 * i + 1) / 2 = i by omega]
  have h0 : y 0 = -x := by
    simpa using hye 0
  rw [← h0]
  refine translation_cycle hn P (k := k) (σ := σ) (fun i _ ↦ ?_) (fun i hi ↦ ?_)
    (fun i hi ↦ ?_) ?_ ?_
  · rw [hye, hyo]
    push_cast
    ring
  · rw [hye, show -(x + 2 * (i : ZMod n) * t) + σ = σ - (x + 2 * (i : ZMod n) * t) by ring]
    exact ht i hi
  · rw [hyo, show 2 * i + 2 = 2 * (i + 1) by ring, hye]
    obtain ⟨h1, h2⟩ := hint (i + 1) (by omega) (by omega)
    push_cast at h1 h2 ⊢
    refine ⟨h1, ?_⟩
    rw [h2]
    congr 1
    ring
  · rw [h0, ← hx, mate_mate]
    congr 1
    ring
  · rw [hyo]
    push_cast at hy ⊢
    exact hy

/-! ### Shift systems and the swap of Lemma 2′ -/

/-- A shift system (`ulzd-general-extend.md` (6d8435d) §1, units and repair): a set `W`, the union
of the `W`-parts `{z, T(z) + σ}` of disjoint units, and a shift `σ`, with `W ∩ (W - σ) = ∅`. The
`Q`-edges are `{w, w - σ}` for `w ∈ W`. For `T = F_0` one system `W = A ∪ (σ - A)` of
`Canonical.ReflSet` (`Repair/Reflection.lean`, main 2b0e563) is the case `r = -·` of `ofSeeds`. -/
structure ShiftSys (n : ℕ) where
  /-- The `W`-parts of the units. -/
  W : Finset (ZMod n)
  /-- The shift. -/
  σ : ZMod n
  sub_notMem : ∀ w ∈ W, w - σ ∉ W

namespace ShiftSys

variable (S : ShiftSys n)

/-- `V(W) = W ∪ (W - σ)`, the vertices of the units. -/
def verts : Finset (Option (ZMod n)) :=
  (S.W ∪ S.W.image (· - S.σ)).image some

theorem some_mem_verts {z : ZMod n} : some z ∈ S.verts ↔ z ∈ S.W ∨ z + S.σ ∈ S.W := by
  simp only [verts, Finset.mem_image, Finset.mem_union, Option.some.injEq]
  constructor
  · rintro ⟨a, ha | ⟨b, hb, rfl⟩, rfl⟩
    · exact Or.inl ha
    · right
      rwa [sub_add_cancel]
  · rintro (h | h)
    · exact ⟨z, Or.inl h, rfl⟩
    · exact ⟨z, Or.inr ⟨z + S.σ, h, add_sub_cancel_right _ _⟩, rfl⟩

theorem none_notMem_verts : none ∉ S.verts := by
  simp [verts]

/-- `|V(W)| ≤ 2|W|`. -/
theorem card_verts_le : S.verts.card ≤ 2 * S.W.card := by
  have h1 := Finset.card_image_le (s := S.W ∪ S.W.image (· - S.σ)) (f := some)
  have h2 := Finset.card_union_le S.W (S.W.image (· - S.σ))
  have h3 := Finset.card_image_le (s := S.W) (f := (· - S.σ))
  rw [verts]
  omega

/-- The partner in `Q`: `w ↦ w - σ` on `W` and `v ↦ v + σ` on `W - σ`. -/
def partner (z : ZMod n) : ZMod n :=
  if z ∈ S.W then z - S.σ else z + S.σ

theorem partner_of_mem {z : ZMod n} (h : z ∈ S.W) : S.partner z = z - S.σ :=
  ite_eq_left h

theorem notMem_of_add_mem {z : ZMod n} (h : z + S.σ ∈ S.W) : z ∉ S.W := fun hz ↦
  S.sub_notMem _ h (by rwa [add_sub_cancel_right])

theorem partner_of_add_mem {z : ZMod n} (h : z + S.σ ∈ S.W) : S.partner z = z + S.σ :=
  ite_eq_right (S.notMem_of_add_mem h)

theorem partner_mem {z : ZMod n} (h : z ∈ S.W ∨ z + S.σ ∈ S.W) :
    S.partner z ∈ S.W ∨ S.partner z + S.σ ∈ S.W := by
  rcases h with h | h
  · right
    rwa [S.partner_of_mem h, sub_add_cancel]
  · left
    rwa [S.partner_of_add_mem h]

theorem partner_partner {z : ZMod n} (h : z ∈ S.W ∨ z + S.σ ∈ S.W) :
    S.partner (S.partner z) = z := by
  rcases h with h | h
  · rw [S.partner_of_mem h, S.partner_of_add_mem (z := z - S.σ) (by rw [sub_add_cancel]; exact h),
      sub_add_cancel]
  · rw [S.partner_of_add_mem h, S.partner_of_mem h, add_sub_cancel_right]

theorem partner_ne {z : ZMod n} (h : z ∈ S.W ∨ z + S.σ ∈ S.W) : S.partner z ≠ z := by
  rcases h with h | h
  · rw [S.partner_of_mem h]
    intro h'
    exact S.sub_notMem z h (by rw [h']; exact h)
  · rw [S.partner_of_add_mem h]
    intro h'
    exact S.notMem_of_add_mem h (by rw [h'] at h; exact h)

/-- The partner of a vertex of `V(W)` in `Q`. -/
def qSub (p : S.verts) : S.verts :=
  ⟨Option.map S.partner p.1, by
    obtain ⟨_ | z, hp⟩ := p
    · exact absurd hp S.none_notMem_verts
    · exact S.some_mem_verts.2 (S.partner_mem (S.some_mem_verts.1 hp))⟩

theorem qSub_involutive : Function.Involutive S.qSub := by
  rintro ⟨_ | z, hp⟩
  · exact absurd hp S.none_notMem_verts
  · exact Subtype.ext (congrArg some (S.partner_partner (S.some_mem_verts.1 hp)))

/-- `Q = {{w, w - σ} : w ∈ W}`, a perfect matching of `V(W)` (`ulzd-general-extend.md` (6d8435d)
§1, the `Q`-edges of the units). -/
def Q : PerfectMatching S.verts where
  mate := Function.Involutive.toPerm _ S.qSub_involutive
  mate_mate := S.qSub_involutive
  mate_ne := by
    rintro ⟨_ | z, hp⟩ h
    · exact S.none_notMem_verts hp
    · exact S.partner_ne (S.some_mem_verts.1 hp) (Option.some.inj (congrArg Subtype.val h))

/-- The translation repair (`ulzd-general-extend.md` (6d8435d) §1, `P = (T ∖ D) ∪ Q ∪ M_G`):
replace the edges of the completion `M` inside the `M`-closed set `V(W)` by `Q`. Each unit trades
its two `D`-edges `{z, T(z)}`, `{z - σ, T(z) + σ}` for its two `Q`-edges `{z, z - σ}`,
`{T(z) + σ, T(z)}`, the swap of Lemma 2′. -/
def repair (M : PerfectMatching (Option (ZMod n))) (hM : ∀ p ∈ S.verts, M.mate p ∈ S.verts) :
    PerfectMatching (Option (ZMod n)) :=
  glue M S.verts hM S.Q

variable {M : PerfectMatching (Option (ZMod n))} (hM : ∀ p ∈ S.verts, M.mate p ∈ S.verts)

/-- On `V(W)` the repair is `Q`. -/
theorem repair_mate_of_mem {z : ZMod n} (hz : z ∈ S.W ∨ z + S.σ ∈ S.W) :
    (S.repair M hM).mate (some z) = some (S.partner z) := by
  rw [repair, glue_mate_of_mem _ _ _ _ (S.some_mem_verts.2 hz)]
  rfl

/-- The repair pairs `w ∈ W` with `w - σ`. -/
theorem repair_mate_of_W {w : ZMod n} (hw : w ∈ S.W) :
    (S.repair M hM).mate (some w) = some (w - S.σ) := by
  rw [S.repair_mate_of_mem hM (Or.inl hw), S.partner_of_mem hw]

/-- Off `V(W)` the repair is `M`. -/
theorem repair_mate_of_notMem {p : Option (ZMod n)} (hp : p ∉ S.verts) :
    (S.repair M hM).mate p = M.mate p :=
  glue_mate_of_notMem _ _ _ _ hp

/-- An `M`-closed set disjoint from `V(W)` is closed under the repair. -/
theorem repair_mate_mem_of_disjoint {Y : Finset (Option (ZMod n))}
    (hY : ∀ p ∈ Y, M.mate p ∈ Y) (hYS : Disjoint Y S.verts) :
    ∀ p ∈ Y, (S.repair M hM).mate p ∈ Y := fun p hp ↦ by
  rw [S.repair_mate_of_notMem hM (Finset.disjoint_left.1 hYS hp)]
  exact hY p hp

/-- The repair with spots (`ulzd-general-extend.md` (6d8435d) §3, Steps 0 and 1): after the
translation repair, rematch an `M`-closed set `Y` disjoint from `V(W)` by any perfect matching
`Q_Y` of `Y`. A spot for `t` is the case `Y ⊇ {x, T(x), y, T(y)}` with `{x, y} ∈ F_t` and
`Q_Y ∋ {x, y}, {T(x), T(y)}`. -/
def spotRepair {Y : Finset (Option (ZMod n))} (hY : ∀ p ∈ Y, M.mate p ∈ Y)
    (hYS : Disjoint Y S.verts) (QY : PerfectMatching Y) : PerfectMatching (Option (ZMod n)) :=
  glue (S.repair M hM) Y (S.repair_mate_mem_of_disjoint hM hY hYS) QY

variable {Y : Finset (Option (ZMod n))} (hY : ∀ p ∈ Y, M.mate p ∈ Y)
  (hYS : Disjoint Y S.verts) (QY : PerfectMatching Y)

/-- On `Y` the repair with spots is `Q_Y`. -/
theorem spotRepair_mate_of_mem (p : Y) : (S.spotRepair hM hY hYS QY).mate p = QY.mate p :=
  glue_mate_coe _ _ _ _ p

/-- The repair with spots pairs `w ∈ W` with `w - σ`. -/
theorem spotRepair_mate_of_W {w : ZMod n} (hw : w ∈ S.W) :
    (S.spotRepair hM hY hYS QY).mate (some w) = some (w - S.σ) := by
  have hv : some w ∈ S.verts := S.some_mem_verts.2 (Or.inl hw)
  rw [spotRepair, glue_mate_of_notMem _ _ _ _ (fun h ↦ Finset.disjoint_left.1 hYS h hv),
    S.repair_mate_of_W hM hw]

/-- Off `V(W) ∪ Y` the repair with spots is `M`. -/
theorem spotRepair_mate_of_notMem {p : Option (ZMod n)} (hp : p ∉ S.verts ∪ Y) :
    (S.spotRepair hM hY hYS QY).mate p = M.mate p := by
  rw [Finset.mem_union, not_or] at hp
  rw [spotRepair, glue_mate_of_notMem _ _ _ _ hp.2, S.repair_mate_of_notMem hM hp.1]

/-- The cost of the repair with spots (`ulzd-general-extend.md` (6d8435d) §3, Step 1,
`|T ∖ P| ≤ 2|𝒜| + 2|Bl|`): for any tail `T` that `M` completes, `2|T ∖ P| ≤ 2|W| + |Y|`. With
`|W| ≤ 2|𝒜|` kept units and four vertices per spot this is `|T ∖ P| ≤ 2|𝒜| + 2|Bl|`. -/
theorem two_mul_tailDist_spotRepair_le [NeZero n] {U : Finset (Option (ZMod n))}
    (T : PerfectMatching U) (hT : ∀ u : U, M.mate u = T.mate u) :
    2 * tailDist (S.spotRepair hM hY hYS QY) T ≤ 2 * S.W.card + Y.card := by
  refine (two_mul_tailDist_le_card_of_agree T hT (S.verts ∪ Y)
    (fun p hp ↦ S.spotRepair_mate_of_notMem hM hY hYS QY hp)).trans ?_
  have := Finset.card_union_le S.verts Y
  have := S.card_verts_le
  omega

end ShiftSys

/-! ### Units -/

/-- The `W`-part of the units of a seed set `A`, `W = A ∪ {T(z) + σ : z ∈ A}`, with `r = T` on
the seeds. -/
def seedW (A : Finset (ZMod n)) (r : ZMod n → ZMod n) (σ : ZMod n) : Finset (ZMod n) :=
  A ∪ A.image (fun z ↦ r z + σ)

/-- The shift system of the units `U(z) = {z, T(z), z - σ, T(z) + σ}` of a seed set `A`
(`ulzd-general-extend.md` (6d8435d) §1). The hypothesis `W ∩ (W - σ) = ∅` holds when the units
are pairwise disjoint and each has four distinct vertices. For `T = F_0` (`r = -·`) it is one
reflection system `W = A ∪ (σ - A)` of `ulzd-rescue.md` (2f5b9d3). -/
def ShiftSys.ofSeeds (A : Finset (ZMod n)) (r : ZMod n → ZMod n) (σ : ZMod n)
    (h : ∀ w ∈ seedW A r σ, w - σ ∉ seedW A r σ) : ShiftSys n where
  W := seedW A r σ
  σ := σ
  sub_notMem := h

/-- At most two `W`-vertices per seed, `|W| ≤ 2|A|`. -/
theorem ShiftSys.card_ofSeeds_W_le (A : Finset (ZMod n)) (r : ZMod n → ZMod n) (σ : ZMod n)
    (h : ∀ w ∈ seedW A r σ, w - σ ∉ seedW A r σ) :
    (ShiftSys.ofSeeds A r σ h).W.card ≤ 2 * A.card := by
  have h1 := Finset.card_union_le A (A.image (fun z ↦ r z + σ))
  have h2 := Finset.card_image_le (s := A) (f := fun z ↦ r z + σ)
  change (seedW A r σ).card ≤ _
  rw [seedW]
  omega

/-- **Lemma 2′, the swap** (`ulzd-general-extend.md` (6d8435d) §2). If every seed `z` is
`σ`-coherent for the completion `M`, that is `M z = r z` and `M (z - σ) = r z + σ`, so that
`{z, T(z)}` and `{z - σ, T(z) + σ}` are edges of one factor, then `V(W)` is closed under `M`, and
the two edges of each unit can be traded for `{z, z - σ}` and `{T(z) + σ, T(z)}`
(`ShiftSys.repair`). -/
theorem ShiftSys.ofSeeds_closed {M : PerfectMatching (Option (ZMod n))} (A : Finset (ZMod n))
    (r : ZMod n → ZMod n) (σ : ZMod n) (h : ∀ w ∈ seedW A r σ, w - σ ∉ seedW A r σ)
    (hr : ∀ z ∈ A, M.mate (some z) = some (r z) ∧ M.mate (some (z - σ)) = some (r z + σ)) :
    ∀ p ∈ (ShiftSys.ofSeeds A r σ h).verts, M.mate p ∈ (ShiftSys.ofSeeds A r σ h).verts := by
  set S := ShiftSys.ofSeeds A r σ h
  have hW : ∀ w, w ∈ S.W ↔ w ∈ A ∨ ∃ z ∈ A, r z + σ = w := by
    intro w
    change w ∈ seedW A r σ ↔ _
    simp [seedW]
  have hσ : S.σ = σ := rfl
  rintro (_ | z) hp
  · exact absurd hp S.none_notMem_verts
  rw [S.some_mem_verts, hσ, hW, hW] at hp
  rcases hp with (hz | ⟨a, ha, rfl⟩) | (hz | ⟨a, ha, hra⟩)
  · rw [(hr z hz).1, S.some_mem_verts, hσ]
    exact Or.inr ((hW _).2 (Or.inr ⟨z, hz, rfl⟩))
  · rw [← (hr a ha).2, mate_mate, S.some_mem_verts, hσ, sub_add_cancel]
    exact Or.inr ((hW _).2 (Or.inl ha))
  · rw [show z = z + σ - σ by ring, (hr _ hz).2, S.some_mem_verts, hσ]
    exact Or.inl ((hW _).2 (Or.inr ⟨_, hz, rfl⟩))
  · obtain rfl : r a = z := add_right_cancel hra
    rw [← (hr a ha).1, mate_mate, S.some_mem_verts, hσ]
    exact Or.inl ((hW _).2 (Or.inl ha))

/-! ### Certificates and the deterministic core of Theorem B -/

/-- A Lemma 2′ certificate for `F_t` in the repair of `(S, Y)` against the completion `M`
(`ulzd-general-extend.md` (6d8435d) §2 and §3, the Claim). `X` is the touched set, `V(W) ∪ Y`.
The walk `y` runs from `a = y 0` with `a + σ ∈ W` to `b = y (2k + 1) ∈ W`. Its `F_t`-steps are
reflections that avoid `t` (conditions (i), (iii)), and each interior pair `q_l = y (2l - 1)`,
`T(q_l) = y (2l)` is a `σ`-coherent edge of `M` whose two ends `q_l`, `q_l - σ` are untouched
(condition (ii)). -/
def IsTransCert (M : PerfectMatching (Option (ZMod n))) (S : ShiftSys n)
    (X : Finset (Option (ZMod n))) (t : ZMod n) : Prop :=
  ∃ (k : ℕ) (y : ℕ → ZMod n), y 0 + S.σ ∈ S.W ∧ y (2 * k + 1) ∈ S.W ∧
    (∀ i ≤ k, y (2 * i) + y (2 * i + 1) = 2 * t ∧ y (2 * i) ≠ t ∧ y (2 * i) + S.σ ≠ t) ∧
    ∀ i < k, M.mate (some (y (2 * i + 1))) = some (y (2 * i + 2)) ∧
      M.mate (some (y (2 * i + 1) - S.σ)) = some (y (2 * i + 2) + S.σ) ∧
      some (y (2 * i + 1)) ∉ X ∧ some (y (2 * i + 1) - S.σ) ∉ X

/-- A certificate kills `t` in any `P` that pairs `w ∈ W` with `w - σ` and agrees with `M` off
the touched set `X` (`ulzd-general-extend.md` (6d8435d) §3, the Claim, via Lemma 2′). -/
theorem not_ham_of_isTransCert (hn : Odd n) {M P : PerfectMatching (Option (ZMod n))}
    {S : ShiftSys n} {X : Finset (Option (ZMod n))} {t : ZMod n} (hc : IsTransCert M S X t)
    (hPW : ∀ w ∈ S.W, P.mate (some w) = some (w - S.σ))
    (hPX : ∀ p ∉ X, P.mate p = M.mate p) : ¬Ham P (factor hn t) := by
  obtain ⟨k, y, ha, hb, hF, hP⟩ := hc
  refine not_ham_of_translation_cycle hn P (k := k) (y := y) (σ := S.σ)
    (fun i hi ↦ (hF i hi).1) (fun i hi ↦ (hF i hi).2) (fun i hi ↦ ?_) ?_ (hPW _ hb)
  · obtain ⟨h1, h2, h3, h4⟩ := hP i hi
    rw [hPX _ h3, hPX _ h4]
    exact ⟨h1, h2⟩
  · have h := hPW _ ha
    rw [add_sub_cancel_right] at h
    rw [← h, mate_mate]

/-- **Certificate on an orbit** (`ulzd-general-extend.md` (6d8435d) §2, Remark). Let
`x 0, x 1, …, x (k + 1)` be a stretch of one orbit of `Φ_t = F_t ∘ M`, with `M (x l) = r l` and
`x (l + 1) + r l = 2t`, whose ends satisfy `T(x 0) + σ = r 0 + σ ∈ W` and `x (k + 1) ∈ W`. If
every interior point `x l` is `σ`-coherent and untouched, together with `x l - σ`, and no `r l`,
`r l + σ` is `t`, this is a certificate for `F_t`. -/
theorem isTransCert_of_orbit {M : PerfectMatching (Option (ZMod n))} {S : ShiftSys n}
    {X : Finset (Option (ZMod n))} {t : ZMod n} {k : ℕ} {x r : ℕ → ZMod n}
    (hstep : ∀ l ≤ k, x (l + 1) + r l = 2 * t ∧ r l ≠ t ∧ r l + S.σ ≠ t)
    (hint : ∀ l, 1 ≤ l → l ≤ k → M.mate (some (x l)) = some (r l) ∧
      M.mate (some (x l - S.σ)) = some (r l + S.σ) ∧ some (x l) ∉ X ∧ some (x l - S.σ) ∉ X)
    (h0 : r 0 + S.σ ∈ S.W) (hk : x (k + 1) ∈ S.W) : IsTransCert M S X t := by
  set y : ℕ → ZMod n := fun j ↦ if j % 2 = 0 then r (j / 2) else x (j / 2 + 1) with hy_def
  have hye : ∀ i : ℕ, y (2 * i) = r i := by
    intro i
    simp only [hy_def]
    rw [ite_eq_left (by omega), show 2 * i / 2 = i by omega]
  have hyo : ∀ i : ℕ, y (2 * i + 1) = x (i + 1) := by
    intro i
    simp only [hy_def]
    rw [ite_eq_right (by omega), show (2 * i + 1) / 2 = i by omega]
  refine ⟨k, y, ?_, ?_, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have h := hye 0
    rw [mul_zero] at h
    rw [h]
    exact h0
  · rw [hyo]
    exact hk
  · rw [hye, hyo]
    obtain ⟨h1, h2, h3⟩ := hstep i hi
    exact ⟨by rw [add_comm]; exact h1, h2, h3⟩
  · rw [hyo, show 2 * i + 2 = 2 * (i + 1) by ring, hye]
    exact hint (i + 1) (by omega) (by omega)

/-- A clean cycle for `F_t` (`ulzd-general-extend.md` (6d8435d) §3, Step 5(b)): a set `C` that is
closed under `M` and `F_t`, misses some vertex, and misses the touched set `X`. A short cycle of
`T ∪ F_t` that no unit or spot meets is one. -/
def IsCleanCycle (hn : Odd n) (M : PerfectMatching (Option (ZMod n)))
    (X : Finset (Option (ZMod n))) (t : ZMod n) : Prop :=
  ∃ C : Finset (Option (ZMod n)), (∃ u, u ∈ C) ∧ (∃ w, w ∉ C) ∧ Disjoint C X ∧
    (∀ p ∈ C, M.mate p ∈ C) ∧ ∀ p ∈ C, (factor hn t).mate p ∈ C

/-- An untouched cycle of `M ∪ F_t` stays a cycle of `P ∪ F_t`, so `t` is dead in `P`
(`ulzd-general-extend.md` (6d8435d) §3, Step 5(b)). -/
theorem not_ham_of_isCleanCycle (hn : Odd n) {M P : PerfectMatching (Option (ZMod n))}
    {X : Finset (Option (ZMod n))} {t : ZMod n} (hc : IsCleanCycle hn M X t)
    (hPX : ∀ p ∉ X, P.mate p = M.mate p) : ¬Ham P (factor hn t) := by
  obtain ⟨C, ⟨u, hu⟩, ⟨w, hw⟩, hCX, hM, hF⟩ := hc
  refine not_ham_of_closed P (factor hn t) (C : Set (Option (ZMod n))) (fun p hp ↦ ?_) hF hu hw
  rw [hPX p (Finset.disjoint_left.1 hCX hp)]
  exact hM p hp

/-- A spot kills `t`: an `F_t`-edge `{x, F_t x}` with `x ≠ t` in `P` closes a doubled `2`-cycle
that misses `∞` (`ulzd-general-extend.md` (6d8435d) §1, spots). -/
theorem not_ham_of_spot (hn : Odd n) {P : PerfectMatching (Option (ZMod n))} {t x : ZMod n}
    (hx : x ≠ t) (hp : P.mate (some x) = (factor hn t).mate (some x)) :
    ¬Ham P (factor hn t) := by
  refine not_ham_of_mate_eq hp (w := none) (by simp) ?_
  rw [factor_mate, mateFn_of_ne _ _ hx]
  simp

/-- **Theorem B, deterministic core** (`ulzd-general-extend.md` (6d8435d) §3, the Claim, Step 5(b)
and Step 6). Let `M` complete any tail, let `S` be a shift system whose `V(W)` is `M`-closed, and
let `Q_Y` rematch an `M`-closed set `Y` disjoint from `V(W)`. Suppose every `t` is handled: by a
spot (`Q_Y` holds an `F_t`-edge `{x, F_t x}` with `x ≠ t`, the blind factors of Step 0), by a
Lemma 2′ certificate with untouched interior (Step 3), or by an untouched cycle of `M ∪ F_t`
(Step 5(b)). Then the repair with spots is a zero state. Its cost is
`ShiftSys.two_mul_tailDist_spotRepair_le`. The probabilistic choice of seeds, `σ` and `ℓ` that
produces such a cover is not formalized. -/
theorem ShiftSys.isZeroState_spotRepair (hn : Odd n) (S : ShiftSys n)
    {M : PerfectMatching (Option (ZMod n))} (hM : ∀ p ∈ S.verts, M.mate p ∈ S.verts)
    {Y : Finset (Option (ZMod n))} (hY : ∀ p ∈ Y, M.mate p ∈ Y) (hYS : Disjoint Y S.verts)
    (QY : PerfectMatching Y)
    (hcov : ∀ t, (∃ x : ZMod n, ∃ hx : some x ∈ Y, x ≠ t ∧
        (QY.mate ⟨some x, hx⟩ : Option (ZMod n)) = (factor hn t).mate (some x)) ∨
      IsTransCert M S (S.verts ∪ Y) t ∨ IsCleanCycle hn M (S.verts ∪ Y) t) :
    IsZeroState (factor hn) (S.spotRepair hM hY hYS QY) := by
  intro t
  rcases hcov t with ⟨x, hx, hxt, hq⟩ | hc | hc
  · exact not_ham_of_spot hn hxt ((S.spotRepair_mate_of_mem hM hY hYS QY ⟨some x, hx⟩).trans hq)
  · exact not_ham_of_isTransCert hn hc (fun w hw ↦ S.spotRepair_mate_of_W hM hY hYS QY hw)
      (fun p hp ↦ S.spotRepair_mate_of_notMem hM hY hYS QY hp)
  · exact not_ham_of_isCleanCycle hn hc (fun p hp ↦ S.spotRepair_mate_of_notMem hM hY hYS QY hp)

/-! ### Two-factor tails, the deterministic part of Corollary C2 -/

/-- **Arcs of Corollary C2** (`ulzd-general-extend.md` (6d8435d) §4, "Arcs"), in the normalized
coordinates `a = 0`, `b = 1`, `σ = 2`. Along the cycle `F_0 ∪ F_1` the vertices `z` and `z - 2`
share the neighbour `2 - z`. If the completion edges at `z`, `z - 2` and `2 - z` are all edges of
`F_0 ∪ F_1`, then `z` is `2`-coherent, `M (z - 2) = M z + 2`. So `c(z) ≠ c(z - 2)` happens only
next to an edge off `F_0 ∪ F_1` (an arc end, a gadget vertex, the partner of `∞`). -/
theorem coherent_two (h2 : (2 : ZMod n) ≠ 0) {M : PerfectMatching (Option (ZMod n))}
    {z : ZMod n} (h0 : M.mate (some z) = some (-z) ∨ M.mate (some z) = some (2 - z))
    (h1 : M.mate (some (z - 2)) = some (-(z - 2)) ∨ M.mate (some (z - 2)) = some (2 - (z - 2)))
    (h3 : M.mate (some (2 - z)) = some (-(2 - z)) ∨
      M.mate (some (2 - z)) = some (2 - (2 - z))) :
    ∃ r, M.mate (some z) = some r ∧ M.mate (some (z - 2)) = some (r + 2) := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact ⟨-z, h0, by rw [h1]; congr 1; ring⟩
  · exfalso
    apply h2
    rcases h3 with h3 | h3
    · have e := congrArg M.mate h3
      rw [mate_mate, show -(2 - z) = z - 2 by ring, h1] at e
      linear_combination -Option.some.inj e
    · have e := congrArg M.mate h3
      rw [mate_mate, show 2 - (2 - z) = z by ring, h0] at e
      linear_combination Option.some.inj e
  · exfalso
    apply h2
    have e := Option.some.inj (M.mate.injective (h0.trans (by rw [h1]; congr 1; ring)))
    linear_combination e
  · exact ⟨2 - z, h0, by rw [h1]; congr 1; ring⟩

/-- **Drift on a two-factor stretch** (`ulzd-general-extend.md` (6d8435d) §4, "Blind factors").
If every step of an orbit stretch of `Φ_t = F_t ∘ M` uses an edge `M v = 2 c(v) - v` of
`F_0 ∪ F_1`, so `Φ_t(v) = v + 2t - 2c(v)`, then `Φ_t^h(x) - x = 2th - 2S`, `S = Σ c`. -/
theorem orbit_drift {t : ZMod n} {x : ℕ → ZMod n} {c : ℕ → ℕ} {h : ℕ}
    (hstep : ∀ l < h, x (l + 1) = 2 * t - (2 * (c l : ZMod n) - x l)) :
    x h = x 0 + 2 * t * h - 2 * ((∑ l ∈ Finset.range h, c l : ℕ) : ZMod n) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [hstep h (by omega), ih (fun l hl ↦ hstep l (by omega)), Finset.sum_range_succ]
    push_cast
    ring

/-- A type-1 return on a two-factor stretch (`ulzd-general-extend.md` (6d8435d) §3 and §4),
`Φ_t^h(x) = x + kσ` with `σ = 2`, forces `t h = S + k`. -/
theorem mul_eq_of_returns (hn : Odd n) {t : ZMod n} {x : ℕ → ZMod n} {c : ℕ → ℕ} {h : ℕ}
    {k : ℤ} (hstep : ∀ l < h, x (l + 1) = 2 * t - (2 * (c l : ZMod n) - x l))
    (hret : x h = x 0 + 2 * k) :
    t * h = ((∑ l ∈ Finset.range h, c l : ℕ) : ZMod n) + k := by
  rw [orbit_drift hstep] at hret
  apply (isUnit_two hn).mul_left_cancel
  linear_combination hret

/-- The blind set of Corollary C2 (`ulzd-general-extend.md` (6d8435d) §4): the `t` with
`t h ∈ [-2, h + 2]` for some `1 ≤ h < ℓ`, listed as `j h⁻¹`. -/
def blindSet (n ℓ : ℕ) : Finset (ZMod n) :=
  (Finset.Ico 1 ℓ).biUnion fun h ↦
    (Finset.Icc (-2 : ℤ) ((h : ℤ) + 2)).image fun j : ℤ ↦ (j : ZMod n) * (h : ZMod n)⁻¹

/-- `|Bl| ≤ Σ_{1 ≤ h < ℓ} (h + 5)` (`ulzd-general-extend.md` (6d8435d) §4, "at most `h + 5`
values of `t`" for each `h`). -/
theorem card_blindSet_le (n ℓ : ℕ) : (blindSet n ℓ).card ≤ ∑ h ∈ Finset.Ico 1 ℓ, (h + 5) := by
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun h _ ↦ ?_)
  refine Finset.card_image_le.trans ?_
  rw [Int.card_Icc]
  omega

/-- `2 Σ_{1 ≤ h < ℓ} (h + 5) ≤ ℓ² + 10ℓ`, that is `|Bl| ≤ ℓ²/2 + 5ℓ`
(`ulzd-general-extend.md` (6d8435d) §4). -/
theorem two_mul_sum_Ico_le (ℓ : ℕ) : 2 * ∑ h ∈ Finset.Ico 1 ℓ, (h + 5) ≤ ℓ ^ 2 + 10 * ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega)]
      nlinarith [ih]

/-- `t h = j` with `j ∈ [-2, h + 2]`, `1 ≤ h < ℓ` and `h` prime to `n` puts `t` in the blind
set. -/
theorem mem_blindSet {ℓ h : ℕ} {t : ZMod n} {j : ℤ} (h1 : 1 ≤ h) (hℓ : h < ℓ)
    (hcop : Nat.Coprime h n) (hj1 : -2 ≤ j) (hj2 : j ≤ h + 2) (ht : t * h = j) :
    t ∈ blindSet n ℓ := by
  have hu : IsUnit (h : ZMod n) := by
    simpa using (ZMod.unitOfCoprime h hcop).isUnit
  refine Finset.mem_biUnion.2 ⟨h, Finset.mem_Ico.2 ⟨h1, hℓ⟩,
    Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨hj1, hj2⟩, ?_⟩⟩
  rw [← ht, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]

/-- **Blind factors of Corollary C2** (`ulzd-general-extend.md` (6d8435d) §4, with
`review-ulzd-general.md` (d6cc131) §4). A type-1 coincidence `Φ_t^h(x) = x + 2k`, `k ∈ [-2, 2]`,
`1 ≤ h < ℓ`, on a stretch whose steps use edges of `F_0 ∪ F_1`, puts `t` in `blindSet n ℓ`
whenever `h` is prime to `n` (every `h < n` for prime `n`). -/
theorem mem_blindSet_of_returns (hn : Odd n) {ℓ h : ℕ} {t : ZMod n} {x : ℕ → ZMod n}
    {c : ℕ → ℕ} {k : ℤ} (hstep : ∀ l < h, x (l + 1) = 2 * t - (2 * (c l : ZMod n) - x l))
    (hc : ∀ l < h, c l ≤ 1) (hk1 : -2 ≤ k) (hk2 : k ≤ 2) (h1 : 1 ≤ h) (hℓ : h < ℓ)
    (hcop : Nat.Coprime h n) (hret : x h = x 0 + 2 * k) : t ∈ blindSet n ℓ := by
  have hS : ∑ l ∈ Finset.range h, c l ≤ h := by
    simpa using Finset.sum_le_card_nsmul (Finset.range h) c 1
      (fun l hl ↦ hc l (Finset.mem_range.1 hl))
  refine mem_blindSet (j := ((∑ l ∈ Finset.range h, c l : ℕ) : ℤ) + k) h1 hℓ hcop (by omega)
    (by omega) ?_
  rw [mul_eq_of_returns hn hstep hret]
  push_cast
  ring

/-- A type-2 coincidence on a two-factor stretch (`ulzd-general-extend.md` (6d8435d) §4,
"Mirror points"), `Φ_t^h(x) = T(x) + 2k` with `T(x) = 2c(x) - x`, pins
`x = c(x) + k + S - th`. -/
theorem mirror_eq (hn : Odd n) {t : ZMod n} {x : ℕ → ZMod n} {c : ℕ → ℕ} {h : ℕ} {k : ℤ}
    (hstep : ∀ l < h, x (l + 1) = 2 * t - (2 * (c l : ZMod n) - x l))
    (hret : x h = 2 * (c 0 : ZMod n) - x 0 + 2 * k) :
    x 0 = (c 0 : ZMod n) + k + ((∑ l ∈ Finset.range h, c l : ℕ) : ZMod n) - t * h := by
  rw [orbit_drift hstep] at hret
  apply (isUnit_two hn).mul_left_cancel
  linear_combination hret

/-- The candidate mirror points of `F_t` with `0 ≤ h < ℓ`, the values `c + k + S - th` with
`c ∈ {0, 1}`, `k ∈ [-1, 3]` and `S ∈ [0, h]`. -/
def mirrorSet (t : ZMod n) (ℓ : ℕ) : Finset (ZMod n) :=
  (Finset.range ℓ).biUnion fun h ↦
    ((Finset.range 2 ×ˢ Finset.Icc (-1 : ℤ) 3) ×ˢ Finset.range (h + 1)).image
      fun p ↦ (p.1.1 : ZMod n) + p.1.2 + p.2 - t * h

/-- `|M_t| ≤ Σ_{h < ℓ} 10(h + 1) = 5ℓ(ℓ + 1)` for the forward coincidences. The backward ones
(`h < 0`) are the forward ones of the partner orbit, which doubles this to the `10ℓ(ℓ + 1)` of
`ulzd-general-extend.md` (6d8435d) §4. -/
theorem card_mirrorSet_le (t : ZMod n) (ℓ : ℕ) :
    (mirrorSet t ℓ).card ≤ ∑ h ∈ Finset.range ℓ, 10 * (h + 1) := by
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun h _ ↦ ?_)
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
    Int.card_Icc]
  norm_num

/-- Every forward mirror point of a two-factor stretch lies in `mirrorSet t ℓ`
(`ulzd-general-extend.md` (6d8435d) §4, "one `x` per `(h, c(x), k, S)`"). -/
theorem mem_mirrorSet (hn : Odd n) {ℓ h : ℕ} {t : ZMod n} {x : ℕ → ZMod n} {c : ℕ → ℕ} {k : ℤ}
    (hstep : ∀ l < h, x (l + 1) = 2 * t - (2 * (c l : ZMod n) - x l))
    (hc : ∀ l < h, c l ≤ 1) (hc0 : c 0 ≤ 1) (hk1 : -1 ≤ k) (hk2 : k ≤ 3) (hℓ : h < ℓ)
    (hret : x h = 2 * (c 0 : ZMod n) - x 0 + 2 * k) : x 0 ∈ mirrorSet t ℓ := by
  have hS : ∑ l ∈ Finset.range h, c l ≤ h := by
    simpa using Finset.sum_le_card_nsmul (Finset.range h) c 1
      (fun l hl ↦ hc l (Finset.mem_range.1 hl))
  refine Finset.mem_biUnion.2 ⟨h, Finset.mem_range.2 hℓ, Finset.mem_image.2
    ⟨((c 0, k), ∑ l ∈ Finset.range h, c l), ?_, (mirror_eq hn hstep hret).symm⟩⟩
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
  omega

section Count

variable [NeZero n]

/-- The vertices `z` whose completion edge is not an edge of `F_0 ∪ F_1`, the set behind `β` in
Corollary C2 (`ulzd-general-extend.md` (6d8435d) §4): the ends of the extra edges `E_x`, the
gadget, and the partner of `∞`, so `|offTwo M| ≤ 2d + 7`. -/
def offTwo (M : PerfectMatching (Option (ZMod n))) : Finset (ZMod n) :=
  Finset.univ.filter fun z ↦ M.mate (some z) ≠ some (-z) ∧ M.mate (some z) ≠ some (2 - z)

/-- The `σ`-incoherent vertices of the completion `M`. -/
def incoherent (M : PerfectMatching (Option (ZMod n))) (σ : ZMod n) : Finset (ZMod n) :=
  Finset.univ.filter fun z ↦
    ¬∃ r, M.mate (some z) = some r ∧ M.mate (some (z - σ)) = some (r + σ)

theorem eq_or_eq_of_notMem_offTwo {M : PerfectMatching (Option (ZMod n))} {z : ZMod n}
    (h : z ∉ offTwo M) : M.mate (some z) = some (-z) ∨ M.mate (some z) = some (2 - z) := by
  simp only [offTwo, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at h
  exact h

/-- **`β` for two-factor tails** (`ulzd-general-extend.md` (6d8435d) §4, "Arcs"): every
`2`-incoherent vertex lies in `X ∪ (X + 2) ∪ (2 - X)` for `X = offTwo M`, so
`|incoherent M 2| ≤ 3|X|`, and also `|incoherent ∪ X ∪ (X + 2)| ≤ 3|X|`. Since `|X| ≤ 2d + 7`
(not formalized), this is `6d + 21`. The bad set of the paper also holds the at most six tail
points `z` with `z - 2` in the gadget, and stays inside its bound `β ≤ 16d + 40`. -/
theorem card_incoherent_two_le (h2 : (2 : ZMod n) ≠ 0) (M : PerfectMatching (Option (ZMod n))) :
    (incoherent M 2).card ≤ 3 * (offTwo M).card := by
  have hsub : incoherent M 2 ⊆
      offTwo M ∪ (offTwo M).image (· + 2) ∪ (offTwo M).image (2 - ·) := by
    intro z hz
    simp only [incoherent, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    by_contra hn
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hn
    obtain ⟨⟨h0, h1⟩, h3⟩ := hn
    exact hz (coherent_two h2 (eq_or_eq_of_notMem_offTwo h0)
      (eq_or_eq_of_notMem_offTwo fun h ↦ h1 _ h (sub_add_cancel z 2))
      (eq_or_eq_of_notMem_offTwo fun h ↦ h3 _ h (sub_sub_cancel 2 z)))
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hu' := Finset.card_union_le (offTwo M) ((offTwo M).image (· + 2))
  have i1 := Finset.card_image_le (s := offTwo M) (f := (· + 2))
  have i2 := Finset.card_image_le (s := offTwo M) (f := (2 - ·))
  omega

end Count

namespace Canonical

variable {m : ℕ} [NeZero m]

/-- A translation cover of the tail `T` of any gadget `G`, of cost `K`
(`ulzd-general-extend.md` (6d8435d) §3, the outcome of Steps 0 to 5): a completion `M` of `T`, a
shift system `S` with `M`-closed `V(W)`, spots `(Y, Q_Y)`, `2|W| + |Y| ≤ 2K`, and a spot, a
Lemma 2′ certificate or a clean cycle at every `t`. Theorem B produces one with
`K ≤ C √(m ln n / ℓ) + 2|Bl|` when `β + |Bl| + M ≤ m / (Cℓ)`, by a probabilistic choice of seeds
that is not formalized. -/
def HasTransCover {G : Finset (Vertex m)} (T : PerfectMatching (Gᶜ : Finset (Vertex m)))
    (K : ℕ) : Prop :=
  ∃ (M : PerfectMatching (Vertex m)) (_ : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u)
    (S : ShiftSys (2 * m - 1)) (_ : ∀ p ∈ S.verts, M.mate p ∈ S.verts)
    (Y : Finset (Vertex m)) (_ : ∀ p ∈ Y, M.mate p ∈ Y) (_ : Disjoint Y S.verts)
    (QY : PerfectMatching Y), 2 * S.W.card + Y.card ≤ 2 * K ∧
    ∀ t, (∃ x : ZMod (2 * m - 1), ∃ hx : some x ∈ Y, x ≠ t ∧
        (QY.mate ⟨some x, hx⟩ : Vertex m) = (factor m t).mate (some x)) ∨
      IsTransCert M S (S.verts ∪ Y) t ∨ IsCleanCycle (modulus_odd m) M (S.verts ∪ Y) t

/-- **Theorem B, deterministic part** (`ulzd-general-extend.md` (6d8435d) §3, with the scope of
`review-ulzd-general.md` (d6cc131)): a translation cover of cost `K` gives `ρ(T) ≤ K`, for every
six-vertex gadget and every tail. -/
theorem exists_zeroState_of_hasTransCover {G : Finset (Vertex m)}
    {T : PerfectMatching (Gᶜ : Finset (Vertex m))} {K : ℕ} (hT : HasTransCover T K) :
    ∃ P : ZeroState m, tailDist P.1 T ≤ K := by
  obtain ⟨M, hMT, S, hM, Y, hY, hYS, QY, hK, hcov⟩ := hT
  refine ⟨⟨S.spotRepair hM hY hYS QY,
    S.isZeroState_spotRepair (modulus_odd m) hM hY hYS QY hcov⟩, ?_⟩
  have := S.two_mul_tailDist_spotRepair_le hM hY hYS QY T hMT
  change tailDist (S.spotRepair hM hY hYS QY) T ≤ K
  omega

/-- If every tail of the gadget `G` has a translation cover of cost `K`, then `N_m ≤ K`
(`ulzd-general-extend.md` (6d8435d) Theorem B, deterministic part, as `RepairBound`). -/
theorem repairBound_of_hasTransCover {G : Finset (Vertex m)} {K : ℕ}
    (hT : ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), HasTransCover T K) :
    RepairBound m G K :=
  fun T ↦ exists_zeroState_of_hasTransCover (hT T)

/-- Theorem B in the window reduction of `hybwin-contra.md` (cd19551) §2
(`repairBound_of_window`, main 2b0e563). If every tail at distance below `d₁` from `T(n)` has a
translation cover of cost `K₀`, and every hybrid with `|E′| ≥ d₁` has `ρ ≤ K`, then
`N_m ≤ max(K, K₀)`. Theorem B gives such covers only for `d₁ ≤ m / C`
(`review-ulzd-general.md` (d6cc131) E1). -/
theorem repairBound_of_window_transCover (hm : 5 ≤ m) {d₁ K K₀ : ℕ}
    (hlow : ∀ T : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)),
      tailDist (factor m (FactorCap.capCenter m)) T < d₁ → HasTransCover T K₀)
    (hwin : ∀ (S : Finset ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
      (hS : ∀ v ∈ S, (FactorCap.factorTail m hm).mate v ∈ S) (R : PerfectMatching S),
      IsEdgeFree (FactorCap.factorTail m hm) R → 2 * d₁ ≤ S.card →
        ∃ P : ZeroState m, tailDist P.1 (glue (FactorCap.factorTail m hm) S hS R) ≤ K) :
    RepairBound m (FactorCap.gadget m) (max K K₀) :=
  repairBound_of_window hm (fun T hT ↦ exists_zeroState_of_hasTransCover (hlow T hT)) hwin

/-- **Corollary C2, deterministic reduction** (`ulzd-general-extend.md` (6d8435d) §4, with
`review-ulzd-general.md` (d6cc131) D4). Let `M` complete a tail of any gadget, let `S` be a shift
system with `M`-closed `V(W)`, and let the spots `(Y, Q_Y)`, at most four vertices per blind
factor, give each `t ∈ blindSet n ℓ` an `F_t`-edge. If every other `t` has a Lemma 2′ certificate
or a clean cycle, then `ρ(T) ≤ |W| + 2 Σ_{1 ≤ h < ℓ} (h + 5) ≤ |W| + ℓ² + 10ℓ`. Only the
window argument of Theorem B, which supplies the certificates for the non-blind `t` with
`|W| ≤ C √(m ln n / ℓ)`, stays probabilistic. -/
theorem exists_zeroState_of_blindCover {G : Finset (Vertex m)}
    {T : PerfectMatching (Gᶜ : Finset (Vertex m))} (M : PerfectMatching (Vertex m))
    (hMT : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u) (S : ShiftSys (2 * m - 1))
    (hM : ∀ p ∈ S.verts, M.mate p ∈ S.verts) {Y : Finset (Vertex m)}
    (hY : ∀ p ∈ Y, M.mate p ∈ Y) (hYS : Disjoint Y S.verts) (QY : PerfectMatching Y) {ℓ : ℕ}
    (hYc : Y.card ≤ 4 * (blindSet (2 * m - 1) ℓ).card)
    (hspot : ∀ t ∈ blindSet (2 * m - 1) ℓ, ∃ x : ZMod (2 * m - 1), ∃ hx : some x ∈ Y, x ≠ t ∧
      (QY.mate ⟨some x, hx⟩ : Vertex m) = (factor m t).mate (some x))
    (hcov : ∀ t ∉ blindSet (2 * m - 1) ℓ,
      IsTransCert M S (S.verts ∪ Y) t ∨ IsCleanCycle (modulus_odd m) M (S.verts ∪ Y) t) :
    ∃ P : ZeroState m, tailDist P.1 T ≤ S.W.card + 2 * ∑ h ∈ Finset.Ico 1 ℓ, (h + 5) := by
  refine exists_zeroState_of_hasTransCover ⟨M, hMT, S, hM, Y, hY, hYS, QY, ?_, fun t ↦ ?_⟩
  · have := card_blindSet_le (2 * m - 1) ℓ
    omega
  · by_cases ht : t ∈ blindSet (2 * m - 1) ℓ
    · exact Or.inl (hspot t ht)
    · exact Or.inr (hcov t ht)

/-! ### The reflection repair is a translation repair -/

/-- A union of reflection systems with one centre `σ` (`Repair/Reflection.lean`, main 2b0e563) as
a shift system: `W ∩ (W - σ) = ∅` follows from `W ∩ -W = ∅` and `σ - W = W`. -/
def ReflSet.toShiftSys (R : ReflSet m) (σ : ZMod (2 * m - 1))
    (hcen : ∀ w ∈ R.W, R.cen w = σ) : ShiftSys (2 * m - 1) where
  W := R.W
  σ := σ
  sub_notMem w hw h := R.neg_notMem (w - σ) h (by
    rw [neg_sub, ← hcen w hw]
    exact R.sub_mem w hw)

theorem ReflSet.verts_eq_toShiftSys (R : ReflSet m) (σ : ZMod (2 * m - 1))
    (hcen : ∀ w ∈ R.W, R.cen w = σ) : R.verts = (R.toShiftSys σ hcen).verts := by
  ext p
  rcases p with _ | z
  · simp only [R.none_notMem_verts, (R.toShiftSys σ hcen).none_notMem_verts]
  rw [R.some_mem_verts, ShiftSys.some_mem_verts]
  change z ∈ R.W ∨ -z ∈ R.W ↔ z ∈ R.W ∨ z + σ ∈ R.W
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · have h' := R.sub_mem _ h
      rw [hcen _ h, show σ - -z = z + σ by ring] at h'
      exact Or.inr h'
  · rintro (h | h)
    · exact Or.inl h
    · have h' := R.sub_mem _ h
      rw [hcen _ h, show σ - (z + σ) = -z by ring] at h'
      exact Or.inr h'

/-- **Lemma 2′, the swap, at `T = F_0`**: the reflection repair of one centre `σ`
(`ReflSet.repair`, `ulzd-rescue.md` (2f5b9d3) Proposition 3, main 2b0e563) equals the translation
repair `ShiftSys.repair` of the same matching for the shift system with the same `W` and shift
`σ`. -/
theorem ReflSet.repair_eq_shiftRepair (R : ReflSet m) (σ : ZMod (2 * m - 1))
    (hcen : ∀ w ∈ R.W, R.cen w = σ) {P₀ : PerfectMatching (Vertex m)}
    (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) :
    R.repair P₀ h = (R.toShiftSys σ hcen).repair P₀ (fun p hp ↦ by
      rw [← R.verts_eq_toShiftSys σ hcen] at hp ⊢
      exact R.mate_mem_verts h p hp) := by
  refine PerfectMatching.ext (Equiv.ext fun p ↦ ?_)
  have hv := R.verts_eq_toShiftSys σ hcen
  by_cases hp : p ∈ R.verts
  · rcases p with _ | z
    · exact absurd hp R.none_notMem_verts
    have hz := R.some_mem_verts.1 hp
    have hz' := (R.toShiftSys σ hcen).some_mem_verts.1 (hv ▸ hp)
    rw [R.repair_mate_of_mem h hz, ShiftSys.repair_mate_of_mem _ _ hz']
    congr 1
    rcases hz with hz | hz
    · rw [R.qFn_of_mem hz, hcen z hz]
      exact ((R.toShiftSys σ hcen).partner_of_mem (z := z) hz).symm
    · rw [R.qFn_of_neg_mem hz, hcen _ hz]
      rcases hz' with hz' | hz'
      · exact absurd hz (R.notMem_of_neg_mem (by rwa [neg_neg]))
      · exact ((R.toShiftSys σ hcen).partner_of_add_mem hz').symm
  · rw [R.repair_mate_of_notMem h hp, ShiftSys.repair_mate_of_notMem _ _ (hv ▸ hp)]

end Canonical

end RoundRobin

end Pairing
