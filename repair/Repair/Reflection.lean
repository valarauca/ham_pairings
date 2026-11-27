import Repair.FactorCap.Tail
import Repair.HybridPair.Contexts
import Repair.Cover.Hybrid

/-!
# Reflection repairs of hybrid tails (COD-205)

Put `n = 2m - 1` and work in the coordinate `x = 2v - 7` (`capAffine`), where the factor tail is
`F_0` minus the gadget labels `1, 3, 5`. Label `x` is the `F_0`-edge `{x, -x}`, and the signed
position of `z` in `F_0 ∪ F_t` is `valMinAbs (λ z)` with `λ = (2t)⁻¹`.

* `ReflSet m` : a valid union of reflection systems `(σ_i, W_i)`, encoded by the set `W` and the
  centre function `cen`. `ReflSet.ofSystem` is one system `W = A ∪ (σ - A)`, and
  `ReflSet.union` joins two unions with disjoint label sets.
* `ReflSet.Q` : `Q_σ(W) = {{w, w - σ}}`, a perfect matching of `V(W) = W ∪ -W`.
  `ReflSet.repair P₀` removes the `F_0`-edges of `P₀` at the labels of `W` and adds `Q_σ(W)`.
  `ReflSet.tailDist_inv_smul_repair` : the repair changes exactly `|W|` edges of a tail.
* `reflection_cycle` (Lemma 2) : two labels `x, y` of one system at same-sign zig-zag positions
  of `F_t`, with clean gaps between them and between their mirrors, give a vertex set closed under
  `P` and `F_t` with `4δ` vertices (`2δ` when `x = σ - y`), that is `2δ` edges of `P`.
  `not_ham_of_reflection` : hence `¬Ham P F_t`.
* `isZeroState_repair` (Proposition 3) : if every `t ≠ 0` has such a pair, the repair is a zero
  state.
* `reflection_repair_tail` (Proposition 3 for tails, the deterministic part of Theorem 4) : for a
  tail `H` of the default gadget and a valid `W` that avoids the gadget and the defects of `H` and
  certifies every factor, some zero state `P` has `|H ∖ P| = |W|`, so `ρ(H) ≤ |W|`.
* `exists_isReflCert_of_bucket` (the Claim of Theorem 4, Step 2, with the G1 fix) : an
  admissible bucket with two elements of one system in `R_0 ∪ R_1` in distinct orbits, and no
  defect or foreign element in its regions, yields a certifying pair at `F_t`.
* `HasReflCover`, `repairBound_of_window_reflCover` : the probabilistic Steps 0 to 3 of
  Theorem 4 stay a hypothesis (a reflection cover of size `K₀` for every tail below `d₁`), which
  feeds `repairBound_of_window`.

Source: `results/ulzd-rescue.md` (organize-archive 2f5b9d3) §1 to §3, with the fixes of
`results/review-ulzd-rescue.md` (c28a6ed).
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- A valid union of reflection systems in the coordinate `x = 2v - 7` (`ulzd-rescue.md`
(2f5b9d3) §1). `W` is the set of labels and `cen w` is the centre `σ_i` of the system that
contains `w`. Each system is symmetric under `w ↦ σ_i - w`, distinct elements have distinct
labels (`W ∩ -W = ∅`), and `2w ≠ σ_i`, so that `Q_σ(W)` has no `F_0`-edge. -/
structure ReflSet (m : ℕ) [NeZero m] where
  /-- The labels `W = ⋃ W_i`. -/
  W : Finset (ZMod (2 * m - 1))
  /-- The centre `σ_i` of the system of each element. -/
  cen : ZMod (2 * m - 1) → ZMod (2 * m - 1)
  sub_mem : ∀ w ∈ W, cen w - w ∈ W
  cen_sub : ∀ w ∈ W, cen (cen w - w) = cen w
  neg_notMem : ∀ w ∈ W, -w ∉ W
  two_mul_ne : ∀ w ∈ W, 2 * w ≠ cen w

namespace ReflSet

/-- One reflection system `W = A ∪ (σ - A)` with centre `σ` (`ulzd-rescue.md` (2f5b9d3) §1). It
is valid when `A` and `σ - A` are disjoint and `W ∩ -W = ∅`, that is when its `2|A|` elements
have distinct labels. -/
def ofSystem (σ : ZMod (2 * m - 1)) (A : Finset (ZMod (2 * m - 1)))
    (hdisj : Disjoint A (A.image (σ - ·)))
    (hneg : ∀ w ∈ A ∪ A.image (σ - ·), -w ∉ A ∪ A.image (σ - ·)) : ReflSet m where
  W := A ∪ A.image (σ - ·)
  cen _ := σ
  sub_mem w hw := by
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image_of_mem _ h))
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      rw [sub_sub_cancel]
      exact Finset.mem_union.2 (Or.inl ha)
  cen_sub _ _ := rfl
  neg_notMem := hneg
  two_mul_ne w hw h2 := by
    have hw' : σ - w = w := by linear_combination -h2
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.disjoint_left.1 hdisj h (hw' ▸ Finset.mem_image_of_mem (σ - ·) h)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      rw [sub_sub_cancel] at hw'
      exact Finset.disjoint_left.1 hdisj ha (hw' ▸ Finset.mem_image_of_mem (σ - ·) ha)

/-- One system has `|W| = 2|A|`. -/
theorem card_ofSystem (σ : ZMod (2 * m - 1)) (A : Finset (ZMod (2 * m - 1)))
    (hdisj : Disjoint A (A.image (σ - ·)))
    (hneg : ∀ w ∈ A ∪ A.image (σ - ·), -w ∉ A ∪ A.image (σ - ·)) :
    (ofSystem σ A hdisj hneg).W.card = 2 * A.card := by
  change (A ∪ A.image (σ - ·)).card = _
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ sub_right_injective]
  ring

/-- The union of two valid unions of systems with disjoint label sets is valid
(`ulzd-rescue.md` (2f5b9d3) §1). -/
def union (R S : ReflSet m) (hRS : ∀ w ∈ R.W, w ∉ S.W ∧ -w ∉ S.W) : ReflSet m where
  W := R.W ∪ S.W
  cen w := if w ∈ R.W then R.cen w else S.cen w
  sub_mem w hw := by
    by_cases h : w ∈ R.W
    · rw [ite_eq_left h]
      exact Finset.mem_union_left _ (R.sub_mem w h)
    · rw [ite_eq_right h]
      exact Finset.mem_union_right _ (S.sub_mem w ((Finset.mem_union.1 hw).resolve_left h))
  cen_sub w hw := by
    by_cases h : w ∈ R.W
    · rw [ite_eq_left h, ite_eq_left (R.sub_mem w h), R.cen_sub w h]
    · have hS := (Finset.mem_union.1 hw).resolve_left h
      have h' : S.cen w - w ∉ R.W := fun h' ↦ (hRS _ h').1 (S.sub_mem w hS)
      rw [ite_eq_right h, ite_eq_right h', S.cen_sub w hS]
  neg_notMem w hw h' := by
    rcases Finset.mem_union.1 hw with h | h
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact R.neg_notMem w h h'
      · exact (hRS w h).2 h'
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact (hRS _ h').2 (by rwa [neg_neg])
      · exact S.neg_notMem w h h'
  two_mul_ne w hw := by
    by_cases h : w ∈ R.W
    · rw [ite_eq_left h]
      exact R.two_mul_ne w h
    · rw [ite_eq_right h]
      exact S.two_mul_ne w ((Finset.mem_union.1 hw).resolve_left h)

/-- The union of two systems has `|W| = |W_1| + |W_2|`. -/
theorem card_union (R S : ReflSet m) (hRS : ∀ w ∈ R.W, w ∉ S.W ∧ -w ∉ S.W) :
    (union R S hRS).W.card = R.W.card + S.W.card :=
  Finset.card_union_of_disjoint (Finset.disjoint_left.2 fun w hw ↦ (hRS w hw).1)

variable (R : ReflSet m)

/-- `-z ∈ W` forces `z ∉ W`, since `W ∩ -W = ∅` (`ulzd-rescue.md` (2f5b9d3) §1). -/
theorem notMem_of_neg_mem {z : ZMod (2 * m - 1)} (h : -z ∈ R.W) : z ∉ R.W := by
  simpa using R.neg_notMem _ h

/-- Centres are nonzero, since `σ = 0` would put `-w` in `W`. -/
theorem cen_ne_zero {w : ZMod (2 * m - 1)} (hw : w ∈ R.W) : R.cen w ≠ 0 := by
  intro h
  have h' := R.sub_mem w hw
  rw [h, zero_sub] at h'
  exact R.neg_notMem w hw h'

/-- The partner of `z` in `Q_σ(W)`: `w ↦ w - σ` on `W` and `z ↦ z + σ` on `-W`. -/
def qFn (z : ZMod (2 * m - 1)) : ZMod (2 * m - 1) :=
  if z ∈ R.W then z - R.cen z else z + R.cen (-z)

/-- `Q_σ(W)` pairs `w ∈ W` with `w - σ`. -/
theorem qFn_of_mem {z : ZMod (2 * m - 1)} (h : z ∈ R.W) : R.qFn z = z - R.cen z :=
  ite_eq_left h

/-- `Q_σ(W)` pairs `z ∈ -W` with `z + σ`. -/
theorem qFn_of_neg_mem {z : ZMod (2 * m - 1)} (h : -z ∈ R.W) : R.qFn z = z + R.cen (-z) :=
  ite_eq_right (R.notMem_of_neg_mem h)

/-- `Q_σ(W)` maps `V(W)` into itself, `W` to `-W` and `-W` to `W`. -/
theorem qFn_mem {z : ZMod (2 * m - 1)} (h : z ∈ R.W ∨ -z ∈ R.W) :
    R.qFn z ∈ R.W ∨ -R.qFn z ∈ R.W := by
  rcases h with h | h
  · right
    rw [R.qFn_of_mem h, neg_sub]
    exact R.sub_mem z h
  · left
    rw [R.qFn_of_neg_mem h, show z + R.cen (-z) = R.cen (-z) - -z by ring]
    exact R.sub_mem _ h

/-- `Q_σ(W)` is an involution on `V(W)`. -/
theorem qFn_qFn {z : ZMod (2 * m - 1)} (h : z ∈ R.W ∨ -z ∈ R.W) : R.qFn (R.qFn z) = z := by
  rcases h with h | h
  · have h' : -(z - R.cen z) ∈ R.W := by
      rw [neg_sub]
      exact R.sub_mem z h
    rw [R.qFn_of_mem h, R.qFn_of_neg_mem h', neg_sub, R.cen_sub z h, sub_add_cancel]
  · have h' : R.cen (-z) - -z ∈ R.W := R.sub_mem _ h
    rw [R.qFn_of_neg_mem h, show z + R.cen (-z) = R.cen (-z) - -z by ring, R.qFn_of_mem h',
      R.cen_sub _ h]
    ring

/-- `Q_σ(W)` has no fixed point. -/
theorem qFn_ne {z : ZMod (2 * m - 1)} (h : z ∈ R.W ∨ -z ∈ R.W) : R.qFn z ≠ z := by
  rcases h with h | h
  · rw [R.qFn_of_mem h]
    intro h'
    exact R.cen_ne_zero h (by linear_combination -h')
  · rw [R.qFn_of_neg_mem h]
    intro h'
    exact R.cen_ne_zero h (by linear_combination h')

/-- `Q_σ(W)` has no `F_0`-edge. -/
theorem qFn_ne_neg {z : ZMod (2 * m - 1)} (h : z ∈ R.W ∨ -z ∈ R.W) : R.qFn z ≠ -z := by
  rcases h with h | h
  · rw [R.qFn_of_mem h]
    intro h'
    exact R.two_mul_ne z h (by linear_combination h')
  · rw [R.qFn_of_neg_mem h]
    intro h'
    exact R.two_mul_ne _ h (by linear_combination -h')

/-- `V(W) = W ∪ -W`, the vertices of the labels of `W`. -/
def verts : Finset (Vertex m) :=
  (R.W ∪ R.W.image Neg.neg).image some

/-- A finite vertex lies in `V(W)` iff its label is in `W`. -/
theorem some_mem_verts {z : ZMod (2 * m - 1)} : some z ∈ R.verts ↔ z ∈ R.W ∨ -z ∈ R.W := by
  simp only [verts, Finset.mem_image, Finset.mem_union, Option.some.injEq]
  constructor
  · rintro ⟨a, ha | ⟨b, hb, rfl⟩, rfl⟩
    · exact Or.inl ha
    · exact Or.inr (by rwa [neg_neg])
  · rintro (h | h)
    · exact ⟨z, Or.inl h, rfl⟩
    · exact ⟨z, Or.inr ⟨-z, h, neg_neg z⟩, rfl⟩

/-- `∞ ∉ V(W)`. -/
theorem none_notMem_verts : none ∉ R.verts := by
  simp [verts]

/-- `|V(W)| = 2|W|`. -/
theorem card_verts : R.verts.card = 2 * R.W.card := by
  have hd : Disjoint R.W (R.W.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
    exact R.neg_notMem c hc ha
  rw [verts, Finset.card_image_of_injective _ (Option.some_injective _),
    Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ neg_injective]
  ring

/-- The partner of a vertex of `V(W)` in `Q_σ(W)`. -/
def qSub (p : R.verts) : R.verts :=
  ⟨Option.map R.qFn p.1, by
    obtain ⟨_ | z, hp⟩ := p
    · exact absurd hp R.none_notMem_verts
    · exact R.some_mem_verts.2 (R.qFn_mem (R.some_mem_verts.1 hp))⟩

/-- The partner map of `Q_σ(W)` on `V(W)` is an involution. -/
theorem qSub_involutive : Function.Involutive R.qSub := by
  rintro ⟨_ | z, hp⟩
  · exact absurd hp R.none_notMem_verts
  · exact Subtype.ext (congrArg some (R.qFn_qFn (R.some_mem_verts.1 hp)))

/-- `Q_σ(W) = {{w, w - σ_i}}`, a perfect matching of `V(W)` (`ulzd-rescue.md` (2f5b9d3) §1). -/
def Q : PerfectMatching R.verts where
  mate := Function.Involutive.toPerm _ R.qSub_involutive
  mate_mate := R.qSub_involutive
  mate_ne := by
    rintro ⟨_ | z, hp⟩ h
    · exact R.none_notMem_verts hp
    · exact R.qFn_ne (R.some_mem_verts.1 hp) (Option.some.inj (congrArg Subtype.val h))

/-- A matching that keeps the `F_0`-edges at the labels of `W` maps `V(W)` into itself. -/
theorem mate_mem_verts {P₀ : PerfectMatching (Vertex m)}
    (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) : ∀ p ∈ R.verts, P₀.mate p ∈ R.verts := by
  rintro (_ | z) hp
  · exact absurd hp R.none_notMem_verts
  rcases R.some_mem_verts.1 hp with hz | hz
  · rw [h z hz, some_mem_verts, neg_neg]
    exact Or.inr hz
  · have h' := h _ hz
    rw [neg_neg] at h'
    rw [← h', P₀.mate_mate, some_mem_verts]
    exact Or.inl hz

/-- A matching that keeps the `F_0`-edges at the labels of `W` pairs each `z ∈ V(W)` with
`-z`. -/
theorem mate_eq_neg_of_mem {P₀ : PerfectMatching (Vertex m)}
    (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) {z : ZMod (2 * m - 1)}
    (hz : z ∈ R.W ∨ -z ∈ R.W) : P₀.mate (some z) = some (-z) := by
  rcases hz with hz | hz
  · exact h z hz
  · have h' := h _ hz
    rw [neg_neg] at h'
    rw [← h', P₀.mate_mate]

/-- The reflection repair (`ulzd-rescue.md` (2f5b9d3) §1 and Proposition 3): remove the
`F_0`-edges of `P₀` at the labels of `W` and add `Q_σ(W)`. It is a perfect matching of `V_m`,
equal to `Q_σ(W)` on `V(W)` and to `P₀` off `V(W)`. -/
def repair (P₀ : PerfectMatching (Vertex m)) (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) :
    PerfectMatching (Vertex m) :=
  glue P₀ R.verts (R.mate_mem_verts h) R.Q

variable {P₀ : PerfectMatching (Vertex m)} (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z))

/-- On `V(W)` the repair is `Q_σ(W)`. -/
theorem repair_mate_of_mem {z : ZMod (2 * m - 1)} (hz : z ∈ R.W ∨ -z ∈ R.W) :
    (R.repair P₀ h).mate (some z) = some (R.qFn z) := by
  rw [repair, glue_mate_of_mem _ _ _ _ (R.some_mem_verts.2 hz)]
  rfl

/-- Off `V(W)` the repair is `P₀`. -/
theorem repair_mate_of_notMem {p : Vertex m} (hp : p ∉ R.verts) :
    (R.repair P₀ h).mate p = P₀.mate p :=
  glue_mate_of_notMem _ _ _ _ hp

/-- The repair changes the partner of exactly the vertices of `V(W)`. -/
theorem repair_mate_ne_iff (p : Vertex m) :
    (R.repair P₀ h).mate p ≠ P₀.mate p ↔ p ∈ R.verts := by
  constructor
  · intro hp
    by_contra hp'
    exact hp (R.repair_mate_of_notMem h hp')
  · intro hp
    rcases p with _ | z
    · exact absurd hp R.none_notMem_verts
    have hz := R.some_mem_verts.1 hp
    rw [R.repair_mate_of_mem h hz, R.mate_eq_neg_of_mem h hz, Ne, Option.some.injEq]
    exact R.qFn_ne_neg hz

/-- The cost of the repair (`ulzd-rescue.md` (2f5b9d3) Proposition 3, `review-ulzd-rescue.md`
(c28a6ed) §1). Let `T` be a perfect matching of `U ⊆ V_m` that `g` carries to `P₀`, with
`g⁻¹ V(W) ⊆ U`. Then `|T ∖ g⁻¹ P| = |W|` for the repair `P`. With `g = 1` this is
`|T ∖ P| = |W|` for a tail `T` contained in `P₀`. -/
theorem tailDist_inv_smul_repair (g : Equiv.Perm (Vertex m)) {U : Finset (Vertex m)}
    (T : PerfectMatching U) (hT : ∀ u : U, g (T.mate u) = P₀.mate (g u))
    (hU : ∀ p ∈ R.verts, g⁻¹ p ∈ U) :
    tailDist (g⁻¹ • R.repair P₀ h) T = R.W.card := by
  have h2 := two_mul_tailDist (g⁻¹ • R.repair P₀ h) T
  have hiff : ∀ u : U, (T.mate u : Vertex m) ≠ (g⁻¹ • R.repair P₀ h).mate u ↔
      g u ∈ R.verts := by
    intro u
    rw [smul_mate, inv_inv, ← R.repair_mate_ne_iff h, ← hT u]
    constructor
    · intro h' h''
      apply h'
      rw [h'']
      exact (g.symm_apply_apply _).symm
    · intro h' h''
      apply h'
      rw [h'']
      exact (g.apply_symm_apply _).symm
  have hc : (Finset.univ.filter fun u : U ↦
      (T.mate u : Vertex m) ≠ (g⁻¹ • R.repair P₀ h).mate u).card = R.verts.card := by
    rw [Finset.filter_congr fun u _ ↦ hiff u]
    refine Finset.card_bij (fun u _ ↦ g u) (fun u hu ↦ (Finset.mem_filter.1 hu).2)
      (fun u _ v _ huv ↦ Subtype.ext (g.injective huv)) fun p hp ↦
        ⟨⟨g⁻¹ p, hU p hp⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa using hp
    · simp
  rw [hc, card_verts] at h2
  omega

end ReflSet

/-! ### Lemma 2, the reflection certificate -/

/-- The arc of `F_0 ∪ F_t` between the exit end of the label at position `a` and the entry end of
the label at position `b`, in the scaled coordinate `k = valMinAbs (λ z)`: the vertices with
`a < k ≤ b` or `-b < k ≤ -a` (`ulzd-rescue.md` (2f5b9d3) Lemma 2, the paths `π_1, π_2`). -/
def gapSeg (lam : (ZMod (2 * m - 1))ˣ) (a b : ℤ) : Finset (Vertex m) :=
  (Finset.univ.filter fun z : ZMod (2 * m - 1) ↦
    (a < (lam * z).valMinAbs ∧ (lam * z).valMinAbs ≤ b) ∨
      (-b < (lam * z).valMinAbs ∧ (lam * z).valMinAbs ≤ -a)).image some

/-- Membership in an arc, by the scaled position. -/
theorem some_mem_gapSeg {lam : (ZMod (2 * m - 1))ˣ} {a b : ℤ} {z : ZMod (2 * m - 1)} :
    some z ∈ gapSeg lam a b ↔ (a < (lam * z).valMinAbs ∧ (lam * z).valMinAbs ≤ b) ∨
      (-b < (lam * z).valMinAbs ∧ (lam * z).valMinAbs ≤ -a) := by
  simp [gapSeg]

/-- `∞` lies on no arc. -/
theorem none_notMem_gapSeg {lam : (ZMod (2 * m - 1))ˣ} {a b : ℤ} :
    (none : Vertex m) ∉ gapSeg lam a b := by
  simp [gapSeg]

omit [NeZero m] in
/-- The scaled position determines the vertex. -/
theorem eq_of_valMinAbs_mul_eq (lam : (ZMod (2 * m - 1))ˣ) {z y : ZMod (2 * m - 1)}
    (h : (lam * z).valMinAbs = (lam * y).valMinAbs) : z = y := by
  have h' := congrArg (fun k : ℤ ↦ (k : ZMod (2 * m - 1))) h
  simp only [ZMod.coe_valMinAbs] at h'
  exact lam.isUnit.mul_right_injective h'

/-- `F_t` maps each arc into itself (Lemma 1 of `ulzd-rescue.md` (2f5b9d3), the zig-zag
`k ↦ 1 - k`). -/
theorem factor_mate_mem_gapSeg {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)}
    (ht : 2 * t * lam = 1) {a b : ℤ} (ha : 0 ≤ a) (hb : 2 * b < 2 * m - 1) {p : Vertex m}
    (hp : p ∈ gapSeg lam a b) : (factor m t).mate p ∈ gapSeg lam a b := by
  rcases p with _ | z
  · exact absurd hp none_notMem_gapSeg
  rw [some_mem_gapSeg] at hp
  have hbd := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * z)
  have hzt : z ≠ t := by
    rintro rfl
    rw [mul_eq_half ht, valMinAbs_half] at hp
    omega
  have hval : (lam * (2 * t - z)).valMinAbs =
      1 - (lam * z).valMinAbs := by
    refine valMinAbs_eq_of_eq ?_ (by omega) (by omega)
    rw [Int.cast_sub, Int.cast_one, ZMod.coe_valMinAbs]
    linear_combination 2 * mul_eq_half ht + two_mul_natCast_self (m := m)
  rw [factor, factor_mate, mateFn_of_ne _ _ hzt, some_mem_gapSeg, hval]
  omega

/-- `P` maps an inner vertex of an arc into the arc when it keeps the `F_0`-edges strictly
inside the gap. -/
theorem mate_mem_gapSeg {P : PerfectMatching (Vertex m)} {lam : (ZMod (2 * m - 1))ˣ} {a b : ℤ}
    (ha : 0 ≤ a)
    (hint : ∀ z : ZMod (2 * m - 1), a < |(lam * z).valMinAbs| → |(lam * z).valMinAbs| < b →
      P.mate (some z) = some (-z))
    {z : ZMod (2 * m - 1)} (hz : some z ∈ gapSeg lam a b) (hzb : (lam * z).valMinAbs ≠ b)
    (hza : (lam * z).valMinAbs ≠ -a) : P.mate (some z) ∈ gapSeg lam a b := by
  rw [some_mem_gapSeg] at hz
  have hk : a < |(lam * z).valMinAbs| ∧
      |(lam * z).valMinAbs| < b := by
    rcases abs_cases (lam * z).valMinAbs with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [h] <;> omega
  rw [hint z hk.1 hk.2, some_mem_gapSeg, mul_neg, valMinAbs_neg']
  omega

/-- `|{v, w}|` sorted, for `v < w` of the same sign. -/
theorem minmax_of_sameSign {v w : ℤ} (h : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0)) :
    (0 < v ∧ v < w ∧ min |v| |w| = v ∧ max |v| |w| = w) ∨
      (v < w ∧ w < 0 ∧ min |v| |w| = -w ∧ max |v| |w| = -v) := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left
    rw [abs_of_pos h0, abs_of_pos (h0.trans h1), min_eq_left h1.le, max_eq_right h1.le]
    exact ⟨h0, h1, rfl, rfl⟩
  · right
    rw [abs_of_neg (h0.trans h1), abs_of_neg h1, min_eq_right (by omega), max_eq_left (by omega)]
    exact ⟨h0, h1, rfl, rfl⟩

/-- The arc of a same-sign pair `x, y` at positions `v < w` has ends `-x` (exit of `x`) and `y`
(entry of `y`), and no other vertex at its end positions (`ulzd-rescue.md` (2f5b9d3) Lemma 2). -/
theorem gapSeg_pair {lam : (ZMod (2 * m - 1))ˣ} {x y : ZMod (2 * m - 1)} {v w a b : ℤ}
    (hv : (lam * x).valMinAbs = v) (hw : (lam * y).valMinAbs = w)
    (hab : (0 < v ∧ v < w ∧ a = v ∧ b = w) ∨ (v < w ∧ w < 0 ∧ a = -w ∧ b = -v)) :
    0 ≤ a ∧ 2 * b < 2 * m - 1 ∧ some y ∈ gapSeg lam a b ∧ some (-x) ∈ gapSeg lam a b ∧
      ∀ z : ZMod (2 * m - 1), ((lam * z).valMinAbs = b ∨ (lam * z).valMinAbs = -a) →
        z = y ∨ z = -x := by
  have bv := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * x)
  have bw := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * y)
  rw [hv] at bv
  rw [hw] at bw
  have hnx : (lam * -x).valMinAbs = -v := by
    rw [mul_neg, valMinAbs_neg', hv]
  refine ⟨by omega, by omega, ?_, ?_, fun z hz ↦ ?_⟩
  · rw [some_mem_gapSeg, hw]
    omega
  · rw [some_mem_gapSeg, hnx]
    omega
  · rcases (show (lam * z).valMinAbs = w ∨
        (lam * z).valMinAbs = -v by omega) with h' | h'
    · exact Or.inl (eq_of_valMinAbs_mul_eq lam (h'.trans hw.symm))
    · exact Or.inr (eq_of_valMinAbs_mul_eq lam (h'.trans hnx.symm))

/-- An arc with `0 ≤ a ≤ b` and `2b < n` has `2(b - a)` vertices. -/
theorem card_gapSeg (lam : (ZMod (2 * m - 1))ˣ) {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 2 * b < 2 * m - 1) : ((gapSeg lam a b).card : ℤ) = 2 * (b - a) := by
  have hval : ∀ j : ℤ, -b < j → j ≤ b →
      (lam * ((↑lam⁻¹ : ZMod (2 * m - 1)) * j)).valMinAbs
        = j := by
    intro j h1 h2
    rw [Units.mul_inv_cancel_left]
    exact valMinAbs_eq_of_eq rfl (by omega) (by omega)
  have heq : gapSeg lam a b = (Finset.Ioc a b ∪ Finset.Ioc (-b) (-a)).image
      fun j : ℤ ↦ some ((↑lam⁻¹ : ZMod (2 * m - 1)) * j) := by
    ext p
    constructor
    · intro hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
      have hz' := (Finset.mem_filter.1 hz).2
      refine Finset.mem_image.2 ⟨(lam * z).valMinAbs, ?_, ?_⟩
      · rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc]
        exact hz'
      · simp only [ZMod.coe_valMinAbs, Units.inv_mul_cancel_left]
    · intro hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hj
      rw [some_mem_gapSeg, hval j (by omega) (by omega)]
      exact hj
  have hinj : Set.InjOn (fun j : ℤ ↦ some ((↑lam⁻¹ : ZMod (2 * m - 1)) * j))
      ↑(Finset.Ioc a b ∪ Finset.Ioc (-b) (-a)) := by
    intro j hj j' hj' hjj
    rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe, Finset.mem_Ioc,
      Finset.mem_Ioc] at hj hj'
    have h1 := hval j (by omega) (by omega)
    have h2 := hval j' (by omega) (by omega)
    simp only [Option.some.injEq] at hjj
    rw [hjj] at h1
    rw [← h1, h2]
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc (-b) (-a)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_Ioc] at hj hj'
    omega
  rw [heq, Finset.card_image_of_injOn hinj, Finset.card_union_of_disjoint hd, Int.card_Ioc,
    Int.card_Ioc]
  omega

/-- Lemma 2 of `ulzd-rescue.md` (2f5b9d3), the reflection certificate. Let `2tλ = 1`, and let
`x, y` be labels of one system with centre `σ`, at positions `v = valMinAbs (λ x)` and
`w = valMinAbs (λ y)` with `v < w` of the same sign (condition (a)), and likewise `v' < w'` for
the mirrors `σ - y, σ - x`. Suppose `P` keeps every `F_0`-edge whose position lies strictly
between `|v|` and `|w|`, or strictly between `|v'|` and `|w'|` (condition (b)), and contains the
two `Q_σ`-edges `{y, y - σ}` and `{σ - x, -x}`. Then the arcs `π_1` from `-x` to `y` and `π_2`
from `σ - y` to `σ - x`, joined by the two chords, form a vertex set `C ∌ ∞` that is closed under
`P` and `F_t`. It has `4δ` vertices, `δ = w - v`, or `2δ` in the anchor case `x = σ - y`. The
arcs are paths of `P ∪ F_t`, so `C` is one cycle with `2δ` edges of `P` (`δ` in the anchor case).
That connectivity is not formalized, since `not_ham_of_reflection` needs only the closed set.
Since `∞ ∉ C`, the bound `4δ < 2m` of `review-ulzd-rescue.md` (c28a6ed) §2 (D1) is not
needed. -/
theorem reflection_cycle (P : PerfectMatching (Vertex m)) {lam : (ZMod (2 * m - 1))ˣ}
    {t : ZMod (2 * m - 1)} (ht : 2 * t * lam = 1) {σ x y : ZMod (2 * m - 1)} {v w v' w' : ℤ}
    (hv : (lam * x).valMinAbs = v) (hw : (lam * y).valMinAbs = w)
    (hv' : (lam * (σ - y)).valMinAbs = v') (hw' : (lam * (σ - x)).valMinAbs = w')
    (ha : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0)) (ha' : (0 < v' ∧ v' < w') ∨ (v' < w' ∧ w' < 0))
    (hb : ∀ z : ZMod (2 * m - 1), min |v| |w| < |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| < max |v| |w| → P.mate (some z) = some (-z))
    (hb' : ∀ z : ZMod (2 * m - 1), min |v'| |w'| < |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| < max |v'| |w'| → P.mate (some z) = some (-z))
    (hy : P.mate (some y) = some (y - σ)) (hx : P.mate (some (σ - x)) = some (-x)) :
    ∃ C : Finset (Vertex m), some y ∈ C ∧ none ∉ C ∧ (∀ p ∈ C, P.mate p ∈ C) ∧
      (∀ p ∈ C, (factor m t).mate p ∈ C) ∧
      (C.card : ℤ) = (if x = σ - y then 2 else 4) * (w - v) := by
  obtain ⟨a, b, hab, hb⟩ : ∃ a b : ℤ,
      ((0 < v ∧ v < w ∧ a = v ∧ b = w) ∨ (v < w ∧ w < 0 ∧ a = -w ∧ b = -v)) ∧
      ∀ z : ZMod (2 * m - 1), a < |(lam * z).valMinAbs| → |(lam * z).valMinAbs| < b →
        P.mate (some z) = some (-z) := ⟨_, _, minmax_of_sameSign ha, hb⟩
  obtain ⟨a', b', hab', hb'⟩ : ∃ a b : ℤ,
      ((0 < v' ∧ v' < w' ∧ a = v' ∧ b = w') ∨ (v' < w' ∧ w' < 0 ∧ a = -w' ∧ b = -v')) ∧
      ∀ z : ZMod (2 * m - 1), a < |(lam * z).valMinAbs| → |(lam * z).valMinAbs| < b →
        P.mate (some z) = some (-z) := ⟨_, _, minmax_of_sameSign ha', hb'⟩
  obtain ⟨ha0, hbm, hy1, hx1, hend⟩ := gapSeg_pair hv hw hab
  obtain ⟨ha0', hbm', hy2, hx2, hend'⟩ := gapSeg_pair hv' hw' hab'
  have hPx : P.mate (some (-x)) = some (σ - x) := by
    rw [← hx, mate_mate]
  have hPy : P.mate (some (-(σ - y))) = some y := by
    rw [neg_sub, ← hy, mate_mate]
  have bv := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * x)
  have bw := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * y)
  have bv' := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * (σ - y))
  have bw' := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * (σ - x))
  rw [hv] at bv
  rw [hw] at bw
  rw [hv'] at bv'
  rw [hw'] at bw'
  have hδ : w' - v' = w - v := by
    have hc : ((w' - v' : ℤ) : ZMod (2 * m - 1)) = ((w - v : ℤ) : ZMod (2 * m - 1)) := by
      rw [← hv, ← hw, ← hv', ← hw']
      simp only [Int.cast_sub, ZMod.coe_valMinAbs]
      ring
    have e1 := valMinAbs_eq_of_eq (rfl : ((w' - v' : ℤ) : ZMod (2 * m - 1)) = _)
      (by omega) (by omega)
    have e2 := valMinAbs_eq_of_eq (rfl : ((w - v : ℤ) : ZMod (2 * m - 1)) = _)
      (by omega) (by omega)
    rw [hc] at e1
    rw [← e1, e2]
  have hP1 : ∀ p ∈ gapSeg lam a b, P.mate p ∈ gapSeg lam a b ∪ gapSeg lam a' b' := by
    intro p hp
    rcases p with _ | z
    · exact absurd hp none_notMem_gapSeg
    by_cases hz : (lam * z).valMinAbs = b ∨ (lam * z).valMinAbs = -a
    · rcases hend z hz with rfl | rfl
      · rw [hy, ← neg_sub]
        exact Finset.mem_union_right _ hx2
      · rw [hPx]
        exact Finset.mem_union_right _ hy2
    · rw [not_or] at hz
      exact Finset.mem_union_left _ (mate_mem_gapSeg ha0 hb hp hz.1 hz.2)
  have hP2 : ∀ p ∈ gapSeg lam a' b', P.mate p ∈ gapSeg lam a b ∪ gapSeg lam a' b' := by
    intro p hp
    rcases p with _ | z
    · exact absurd hp none_notMem_gapSeg
    by_cases hz : (lam * z).valMinAbs = b' ∨ (lam * z).valMinAbs = -a'
    · rcases hend' z hz with rfl | rfl
      · rw [hx]
        exact Finset.mem_union_left _ hx1
      · rw [hPy]
        exact Finset.mem_union_left _ hy1
    · rw [not_or] at hz
      exact Finset.mem_union_right _ (mate_mem_gapSeg ha0' hb' hp hz.1 hz.2)
  refine ⟨gapSeg lam a b ∪ gapSeg lam a' b', Finset.mem_union_left _ hy1, ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨none_notMem_gapSeg, none_notMem_gapSeg⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact hP1 p hp
    · exact hP2 p hp
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Finset.mem_union_left _ (factor_mate_mem_gapSeg ht ha0 hbm hp)
    · exact Finset.mem_union_right _ (factor_mate_mem_gapSeg ht ha0' hbm' hp)
  have hc1 := card_gapSeg lam ha0 (by omega) hbm
  have hc2 := card_gapSeg lam ha0' (by omega) hbm'
  split_ifs with hanc
  · have hv'' : v' = v := by rw [← hv', ← hanc, hv]
    have hw'' : w' = w := by
      rw [← hw', show σ - x = y by rw [hanc, sub_sub_cancel], hw]
    have haa : a' = a := by omega
    have hbb : b' = b := by omega
    rw [haa, hbb, Finset.union_self, hc1]
    omega
  · have hdisj : Disjoint (gapSeg lam a b) (gapSeg lam a' b') := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases p with _ | z
      · exact none_notMem_gapSeg hp1
      rw [some_mem_gapSeg] at hp1 hp2
      have hnx : (lam * -x).valMinAbs = -v := by
        rw [mul_neg, valMinAbs_neg', hv]
      have hny : (lam * -(σ - y)).valMinAbs = -v' := by
        rw [mul_neg, valMinAbs_neg', hv']
      have haa : a = a' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨e, he⟩ : ∃ e : ZMod (2 * m - 1), (lam * e).valMinAbs = -a' :=
            ⟨(↑lam⁻¹ : ZMod (2 * m - 1)) * ((-a' : ℤ) : ZMod (2 * m - 1)), by
              rw [Units.mul_inv_cancel_left]
              exact valMinAbs_eq_of_eq rfl (by omega) (by omega)⟩
          have hk : (lam * -e).valMinAbs = a' := by
            rw [mul_neg, valMinAbs_neg', he, neg_neg]
          have hPe := hb e (by rw [he, abs_neg, abs_of_nonneg (by omega)]; omega)
            (by rw [he, abs_neg, abs_of_nonneg (by omega)]; omega)
          have hfe : -e = -x ∨ -e = y := by
            rcases hend' e (Or.inr he) with rfl | rfl
            · exact Or.inl (Option.some.inj (hPe.symm.trans hx))
            · exact Or.inr (Option.some.inj (hPe.symm.trans hPy))
          rcases hfe with h | h <;> rw [h] at hk
          · rw [hnx] at hk
            omega
          · rw [hw] at hk
            omega
        · obtain ⟨e, he⟩ : ∃ e : ZMod (2 * m - 1), (lam * e).valMinAbs = -a :=
            ⟨(↑lam⁻¹ : ZMod (2 * m - 1)) * ((-a : ℤ) : ZMod (2 * m - 1)), by
              rw [Units.mul_inv_cancel_left]
              exact valMinAbs_eq_of_eq rfl (by omega) (by omega)⟩
          have hk : (lam * -e).valMinAbs = a := by
            rw [mul_neg, valMinAbs_neg', he, neg_neg]
          have hPe := hb' e (by rw [he, abs_neg, abs_of_nonneg (by omega)]; omega)
            (by rw [he, abs_neg, abs_of_nonneg (by omega)]; omega)
          have hfe : -e = -(σ - y) ∨ -e = σ - x := by
            rcases hend e (Or.inr he) with rfl | rfl
            · refine Or.inl (Option.some.inj (hPe.symm.trans ?_))
              rw [hy, neg_sub]
            · exact Or.inr (Option.some.inj (hPe.symm.trans hPx))
          rcases hfe with h | h <;> rw [h] at hk
          · rw [hny] at hk
            omega
          · rw [hw'] at hk
            omega
      have hbb : b = b' := by omega
      rcases hend' y (by rw [hw]; omega) with h | h
      · exact hanc (by rw [h, sub_sub_cancel])
      · have hσ : σ = 0 := by linear_combination h
        rw [hσ, sub_zero] at hy
        exact P.mate_ne _ hy
    rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    rw [hc1, hc2]
    omega

/-- Lemma 2 of `ulzd-rescue.md` (2f5b9d3), consequence: under the hypotheses of
`reflection_cycle`, `P ∪ F_t` is not one cycle. -/
theorem not_ham_of_reflection (P : PerfectMatching (Vertex m)) {lam : (ZMod (2 * m - 1))ˣ}
    {t : ZMod (2 * m - 1)} (ht : 2 * t * lam = 1) {σ x y : ZMod (2 * m - 1)} {v w v' w' : ℤ}
    (hv : (lam * x).valMinAbs = v) (hw : (lam * y).valMinAbs = w)
    (hv' : (lam * (σ - y)).valMinAbs = v') (hw' : (lam * (σ - x)).valMinAbs = w')
    (ha : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0)) (ha' : (0 < v' ∧ v' < w') ∨ (v' < w' ∧ w' < 0))
    (hb : ∀ z : ZMod (2 * m - 1), min |v| |w| < |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| < max |v| |w| → P.mate (some z) = some (-z))
    (hb' : ∀ z : ZMod (2 * m - 1), min |v'| |w'| < |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| < max |v'| |w'| → P.mate (some z) = some (-z))
    (hy : P.mate (some y) = some (y - σ)) (hx : P.mate (some (σ - x)) = some (-x)) :
    ¬Ham P (factor m t) := by
  obtain ⟨C, hyC, hnC, hP, hF, -⟩ :=
    reflection_cycle P ht hv hw hv' hw' ha ha' hb hb' hy hx
  exact not_ham_of_closed P (factor m t) (C : Set (Vertex m)) hP hF hyC hnC

/-! ### Proposition 3 -/

/-- Conditions (a) and (b) of Lemma 2 (`ulzd-rescue.md` (2f5b9d3) §2) for labels `x, y` of one
system of `R` at the factor `F_t`, `λ = (2t)⁻¹`, against the base matching `P₀`. With
`σ = cen x`, the positions of `x, y` and of `σ - y, σ - x` have the same sign, and every label
strictly inside either gap is outside `W` and keeps its `F_0`-edge in `P₀` (no defect of `E'`). -/
def IsReflCert (P₀ : PerfectMatching (Vertex m)) (R : ReflSet m) (lam : (ZMod (2 * m - 1))ˣ)
    (x y : ZMod (2 * m - 1)) : Prop :=
  x ∈ R.W ∧ y ∈ R.W ∧ R.cen y = R.cen x ∧
    ((0 < (lam * x).valMinAbs ∧ (lam * x).valMinAbs < (lam * y).valMinAbs) ∨
      ((lam * x).valMinAbs < (lam * y).valMinAbs ∧ (lam * y).valMinAbs < 0)) ∧
    ((0 < (lam * (R.cen x - y)).valMinAbs ∧
        (lam * (R.cen x - y)).valMinAbs < (lam * (R.cen x - x)).valMinAbs) ∨
      ((lam * (R.cen x - y)).valMinAbs < (lam * (R.cen x - x)).valMinAbs ∧
        (lam * (R.cen x - x)).valMinAbs < 0)) ∧
    (∀ z : ZMod (2 * m - 1),
      min |(lam * x).valMinAbs| |(lam * y).valMinAbs| < |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| < max |(lam * x).valMinAbs| |(lam * y).valMinAbs| →
      z ∉ R.W ∧ -z ∉ R.W ∧ P₀.mate (some z) = some (-z)) ∧
    (∀ z : ZMod (2 * m - 1),
      min |(lam * (R.cen x - y)).valMinAbs| |(lam * (R.cen x - x)).valMinAbs| <
        |(lam * z).valMinAbs| →
      |(lam * z).valMinAbs| <
        max |(lam * (R.cen x - y)).valMinAbs| |(lam * (R.cen x - x)).valMinAbs| →
      z ∉ R.W ∧ -z ∉ R.W ∧ P₀.mate (some z) = some (-z))

/-- Lemma 2 for the repair (`ulzd-rescue.md` (2f5b9d3) Lemma 2 with `A_core ⊆ P`): a pair meeting
(a) and (b) at `F_t` makes `P ∪ F_t` non-Hamiltonian for the repair `P`. -/
theorem not_ham_repair_of_isReflCert (R : ReflSet m) {P₀ : PerfectMatching (Vertex m)}
    (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) {lam : (ZMod (2 * m - 1))ˣ}
    {t : ZMod (2 * m - 1)} (ht : 2 * t * lam = 1) {x y : ZMod (2 * m - 1)}
    (hc : IsReflCert P₀ R lam x y) : ¬Ham (R.repair P₀ h) (factor m t) := by
  obtain ⟨hx, hy, hcen, ha, ha', hb, hb'⟩ := hc
  have hoff : ∀ z, z ∉ R.W → -z ∉ R.W → P₀.mate (some z) = some (-z) →
      (R.repair P₀ h).mate (some z) = some (-z) := by
    intro z h1 h2 h3
    rw [R.repair_mate_of_notMem h (fun h' ↦ (R.some_mem_verts.1 h').elim h1 h2), h3]
  have hm := R.sub_mem x hx
  refine not_ham_of_reflection _ ht rfl rfl rfl rfl ha ha'
    (fun z h1 h2 ↦ ?_) (fun z h1 h2 ↦ ?_) ?_ ?_
  · obtain ⟨h3, h4, h5⟩ := hb z h1 h2
    exact hoff z h3 h4 h5
  · obtain ⟨h3, h4, h5⟩ := hb' z h1 h2
    exact hoff z h3 h4 h5
  · rw [R.repair_mate_of_mem h (Or.inl hy), R.qFn_of_mem hy, hcen]
  · rw [R.repair_mate_of_mem h (Or.inl hm), R.qFn_of_mem hm, R.cen_sub x hx]
    congr 1
    ring

omit [NeZero m] in
/-- `1 ≠ 0` in `ℤ/(2m - 1)` for `m ≥ 2`. -/
theorem one_ne_zero_of_two_le (hm : 2 ≤ m) : (1 : ZMod (2 * m - 1)) ≠ 0 := by
  intro h
  have h' := natCast_injOn (m := m) (x := 1) (y := 0) (by omega) (by omega)
    (by rw [Nat.cast_one, Nat.cast_zero]; exact h)
  omega

/-- Proposition 3 of `ulzd-rescue.md` (2f5b9d3), in the coordinate `x = 2v - 7`. Let `P₀` keep the
`F_0`-edges at the labels of `W` and the gadget edge `{1, -1}`, and let every `t ≠ 0` have a pair
of one system meeting (a) and (b) of Lemma 2. Then the repair
`P = (P₀ ∖ F_0(W)) ∪ Q_σ(W)` is a zero state: `t = 0` is blocked by the kept edge `{1, -1}`, and
every other `t` by Lemma 2. -/
theorem isZeroState_repair (hm : 2 ≤ m) (R : ReflSet m) (P₀ : PerfectMatching (Vertex m))
    (h : ∀ z ∈ R.W, P₀.mate (some z) = some (-z)) (h1 : P₀.mate (some 1) = some (-1))
    (h1W : (1 : ZMod (2 * m - 1)) ∉ R.W ∧ (-1 : ZMod (2 * m - 1)) ∉ R.W)
    (hcov : ∀ t : ZMod (2 * m - 1), t ≠ 0 → ∃ lam : (ZMod (2 * m - 1))ˣ, 2 * t * lam = 1 ∧
      ∃ x y, IsReflCert P₀ R lam x y) :
    IsZeroState (factor m) (R.repair P₀ h) := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · have hne := one_ne_zero_of_two_le hm
    have hne' : (-1 : ZMod (2 * m - 1)) ≠ 0 := neg_ne_zero.2 hne
    have hP1 : (R.repair P₀ h).mate (some 1) = some (-1) := by
      rw [R.repair_mate_of_notMem h (fun h' ↦ (R.some_mem_verts.1 h').elim h1W.1 h1W.2), h1]
    have hP1' : (R.repair P₀ h).mate (some (-1)) = some 1 := by
      rw [← hP1, mate_mate]
    refine not_ham_of_closed _ _ {some 1, some (-1)} ?_ ?_ (u := some 1) (w := none)
      (Set.mem_insert _ _) (by simp)
    · intro p hp
      rcases hp with rfl | hp
      · rw [hP1]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        rw [hP1']
        exact Set.mem_insert _ _
    · intro p hp
      rcases hp with rfl | hp
      · rw [factor, factor_mate, mateFn_of_ne _ _ hne]
        simp
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        rw [factor, factor_mate, mateFn_of_ne _ _ hne']
        simp
  · obtain ⟨lam, hlam, x, y, hc⟩ := hcov t ht
    exact not_ham_repair_of_isReflCert R h hlam hc

/-! ### The bucket claim of Theorem 4 -/

/-- `z` has signed position in the bucket `b = [β, β + ℓ)` of `F_t`, `λ = (2t)⁻¹`, that is
`λ z ∈ R_0` in Step 2 of Theorem 4 of `ulzd-rescue.md` (2f5b9d3). With `τ = λσ` the other
regions are `R_1 = τ - R_0` (`InBucket (σ - z)`), `R_2 = -R_0` (`InBucket (-z)`) and
`R_4 = R_0 - τ` (`InBucket (z + σ)`). -/
def InBucket (lam : (ZMod (2 * m - 1))ˣ) (β ℓ : ℤ) (z : ZMod (2 * m - 1)) : Prop :=
  β ≤ (lam * z).valMinAbs ∧ (lam * z).valMinAbs < β + ℓ

/-- A position strictly inside the mirror gap `{c - j : v < j < w}`, up to sign. -/
theorem exists_mirror_of_gap {v w c k : ℤ}
    (h : (0 < c - w ∧ c - w < c - v) ∨ (c - w < c - v ∧ c - v < 0))
    (h1 : min |c - w| |c - v| < |k|) (h2 : |k| < max |c - w| |c - v|) :
    ∃ j, v < j ∧ j < w ∧ (k = c - j ∨ k = j - c) := by
  rcases minmax_of_sameSign h with ⟨_, _, hmin, hmax⟩ | ⟨_, _, hmin, hmax⟩ <;>
    rw [hmin] at h1 <;> rw [hmax] at h2 <;>
    rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] at h1 h2
  · exact ⟨c - k, by omega⟩
  · exact ⟨c + k, by omega⟩
  · exact ⟨c + k, by omega⟩
  · exact ⟨c - k, by omega⟩

/-- The Claim in Step 2 of Theorem 4 of `ulzd-rescue.md` (2f5b9d3), with the fix of gap G1 of
`review-ulzd-rescue.md` (c28a6ed). Fix `λ = (2t)⁻¹`, a centre `σ` with `λσ ≡ c`, and a bucket
`b = [β, β + ℓ) ⊆ [1, m - 1]` whose mirror `R_1 = τ - b` does not cross `0` or `±n/2`
(admissibility). Suppose (I_b, fixed) the system of `σ` has two elements in `R_0 ∪ R_1` in
distinct `σ`-orbits, and (D_b, on the final `W`) every vertex in `R_0 ∪ R_1` keeps its
`F_0`-edge in `P₀`, no element of `W` lies in `R_2 ∪ R_4`, and no element of another system lies
in `R_0 ∪ R_1`. Then two consecutive elements of the system in `R_0` meet (a) and (b) of
Lemma 2 at `F_t`. -/
theorem exists_isReflCert_of_bucket (R : ReflSet m) (P₀ : PerfectMatching (Vertex m))
    (lam : (ZMod (2 * m - 1))ˣ) (σ : ZMod (2 * m - 1)) {β ℓ c : ℤ} (hβ : 1 ≤ β)
    (hβℓ : β + ℓ ≤ m) (hc : ((c : ℤ) : ZMod (2 * m - 1)) = lam * σ)
    (hadm : (∀ j, β ≤ j → j < β + ℓ → 0 < c - j ∧ 2 * (c - j) < 2 * m - 1) ∨
      (∀ j, β ≤ j → j < β + ℓ → c - j < 0 ∧ -(2 * m - 1 : ℤ) < 2 * (c - j)))
    (hI : ∃ a ∈ R.W, ∃ a' ∈ R.W, R.cen a = σ ∧ R.cen a' = σ ∧ a' ≠ a ∧ a' ≠ σ - a ∧
      (InBucket lam β ℓ a ∨ InBucket lam β ℓ (σ - a)) ∧
      (InBucket lam β ℓ a' ∨ InBucket lam β ℓ (σ - a')))
    (hD1 : ∀ z, InBucket lam β ℓ z ∨ InBucket lam β ℓ (σ - z) → P₀.mate (some z) = some (-z))
    (hD2 : ∀ z ∈ R.W, ¬InBucket lam β ℓ (-z) ∧ ¬InBucket lam β ℓ (z + σ))
    (hD3 : ∀ z ∈ R.W, R.cen z ≠ σ → ¬InBucket lam β ℓ z ∧ ¬InBucket lam β ℓ (σ - z)) :
    ∃ x y, IsReflCert P₀ R lam x y := by
  classical
  obtain ⟨a, ha, a', ha', hca, hca', hne1, hne2, hba, hba'⟩ := hI
  have hmemS : ∀ z, z ∈ R.W.filter (fun z ↦ R.cen z = σ ∧ InBucket lam β ℓ z) ↔
      z ∈ R.W ∧ R.cen z = σ ∧ InBucket lam β ℓ z := fun z ↦ Finset.mem_filter
  have horb : ∀ z ∈ R.W, R.cen z = σ → InBucket lam β ℓ z ∨ InBucket lam β ℓ (σ - z) →
      ∃ p ∈ R.W.filter (fun z ↦ R.cen z = σ ∧ InBucket lam β ℓ z), p = z ∨ p = σ - z := by
    intro z hz hcz hb
    rcases hb with hb | hb
    · exact ⟨z, (hmemS z).2 ⟨hz, hcz, hb⟩, Or.inl rfl⟩
    · have hz' : σ - z ∈ R.W := by
        rw [← hcz]
        exact R.sub_mem z hz
      have hcz' : R.cen (σ - z) = σ := by
        rw [← hcz]
        exact R.cen_sub z hz
      exact ⟨σ - z, (hmemS _).2 ⟨hz', hcz', hb⟩, Or.inr rfl⟩
  obtain ⟨p, hp, hpa⟩ := horb a ha hca hba
  obtain ⟨q, hq, hqa⟩ := horb a' ha' hca' hba'
  have hpq : p ≠ q := by
    rintro rfl
    rcases hpa with h1 | h1 <;> rcases hqa with h2 | h2
    exacts [hne1 (by linear_combination h1 - h2), hne2 (by linear_combination h2 - h1),
      hne2 (by linear_combination h1 - h2), hne1 (by linear_combination h2 - h1)]
  obtain ⟨x, hx, hxmin⟩ := (R.W.filter fun z ↦ R.cen z = σ ∧ InBucket lam β ℓ z).exists_min_image
    (fun z : ZMod (2 * m - 1) ↦ (lam * z).valMinAbs) ⟨p, hp⟩
  have hT : ((R.W.filter fun z ↦ R.cen z = σ ∧ InBucket lam β ℓ z).filter
      fun z : ZMod (2 * m - 1) ↦ (lam * x).valMinAbs < (lam * z).valMinAbs).Nonempty := by
    by_cases hpx : p = x
    · refine ⟨q, Finset.mem_filter.2 ⟨hq, ?_⟩⟩
      have h1 := hxmin q hq
      have h2 : (lam * q).valMinAbs ≠ (lam * x).valMinAbs :=
        fun h ↦ hpq (hpx.trans (eq_of_valMinAbs_mul_eq lam h).symm)
      omega
    · refine ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩⟩
      have h1 := hxmin p hp
      have h2 : (lam * p).valMinAbs ≠ (lam * x).valMinAbs :=
        fun h ↦ hpx (eq_of_valMinAbs_mul_eq lam h)
      omega
  obtain ⟨y, hy, hymin⟩ := Finset.exists_min_image _
    (fun z : ZMod (2 * m - 1) ↦ (lam * z).valMinAbs) hT
  rw [Finset.mem_filter] at hy
  obtain ⟨hy, hxy⟩ := hy
  have hgap : ∀ z ∈ R.W.filter (fun z ↦ R.cen z = σ ∧ InBucket lam β ℓ z),
      (lam * x).valMinAbs < (lam * z).valMinAbs →
      (lam * y).valMinAbs ≤ (lam * z).valMinAbs :=
    fun z hz h ↦ hymin z (Finset.mem_filter.2 ⟨hz, h⟩)
  obtain ⟨hxW, hcx, hbx⟩ := (hmemS x).1 hx
  obtain ⟨hyW, hcy, hby⟩ := (hmemS y).1 hy
  have hmir : ∀ z : ZMod (2 * m - 1), InBucket lam β ℓ z →
      (lam * (σ - z)).valMinAbs = c - (lam * z).valMinAbs := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    refine valMinAbs_eq_of_eq ?_ ?_ ?_
    · rw [Int.cast_sub, hc, ZMod.coe_valMinAbs]
      ring
    · rcases hadm with h | h <;> have := h _ h1 h2 <;> omega
    · rcases hadm with h | h <;> have := h _ h1 h2 <;> omega
  have hmir' : ∀ (z : ZMod (2 * m - 1)) (j : ℤ), β ≤ j → j < β + ℓ → (lam * z).valMinAbs = c - j →
      (lam * (σ - z)).valMinAbs = j := by
    intro z j h1 h2 hz
    have hz' := congrArg (fun k : ℤ ↦ (k : ZMod (2 * m - 1))) hz
    simp only [ZMod.coe_valMinAbs, Int.cast_sub] at hz'
    refine valMinAbs_eq_of_eq ?_ (by omega) (by omega)
    rw [mul_sub, hz', ← hc]
    ring
  have hsymm : ∀ z : ZMod (2 * m - 1),
      (-z ∉ R.W ∧ -(-z) ∉ R.W ∧ P₀.mate (some (-z)) = some (-(-z))) →
      z ∉ R.W ∧ -z ∉ R.W ∧ P₀.mate (some z) = some (-z) := by
    intro z ⟨h1, h2, h3⟩
    rw [neg_neg] at h2 h3
    refine ⟨h2, h1, ?_⟩
    rw [← h3, mate_mate]
  have hcore1 : ∀ z : ZMod (2 * m - 1), (lam * x).valMinAbs < (lam * z).valMinAbs →
      (lam * z).valMinAbs < (lam * y).valMinAbs →
      z ∉ R.W ∧ -z ∉ R.W ∧ P₀.mate (some z) = some (-z) := by
    intro z h1 h2
    have hbz : InBucket lam β ℓ z := ⟨by have := hbx.1; omega, by have := hby.2; omega⟩
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hD2 _ hz).1 (by rwa [neg_neg]), hD1 z (Or.inl hbz)⟩
    by_cases hcz : R.cen z = σ
    · have := hgap z ((hmemS z).2 ⟨hz, hcz, hbz⟩) h1
      omega
    · exact (hD3 z hz hcz).1 hbz
  have hcore2 : ∀ z : ZMod (2 * m - 1), (lam * x).valMinAbs <
        (lam * (σ - z)).valMinAbs →
      (lam * (σ - z)).valMinAbs < (lam * y).valMinAbs →
      z ∉ R.W ∧ -z ∉ R.W ∧ P₀.mate (some z) = some (-z) := by
    intro z h1 h2
    have hbz : InBucket lam β ℓ (σ - z) := ⟨by have := hbx.1; omega, by have := hby.2; omega⟩
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hD2 _ hz).2 (by rwa [neg_add_eq_sub]), hD1 z (Or.inr hbz)⟩
    by_cases hcz : R.cen z = σ
    · have hz' : σ - z ∈ R.W := by
        rw [← hcz]
        exact R.sub_mem z hz
      have hcz' : R.cen (σ - z) = σ := by
        rw [← hcz]
        exact R.cen_sub z hz
      have := hgap _ ((hmemS _).2 ⟨hz', hcz', hbz⟩) h1
      omega
    · exact (hD3 z hz hcz).2 hbz
  have hx0 : 0 < (lam * x).valMinAbs := by
    have := hbx.1
    omega
  refine ⟨x, y, hxW, hyW, by rw [hcx, hcy], Or.inl ⟨hx0, hxy⟩, ?_, ?_, ?_⟩
  · rw [hcx, hmir y hby, hmir x hbx]
    rcases hadm with h | h
    · have := h _ hby.1 hby.2
      exact Or.inl ⟨by omega, by omega⟩
    · have := h _ hbx.1 hbx.2
      exact Or.inr ⟨by omega, by omega⟩
  · intro z h1 h2
    rw [abs_of_pos hx0, abs_of_pos (hx0.trans hxy)] at h1 h2
    rw [min_eq_left hxy.le] at h1
    rw [max_eq_right hxy.le] at h2
    rcases abs_cases (lam * z).valMinAbs with ⟨hk, _⟩ | ⟨hk, _⟩ <;>
      rw [hk] at h1 h2
    · exact hcore1 z h1 h2
    · refine hsymm z (hcore1 (-z) ?_ ?_) <;> rw [mul_neg, valMinAbs_neg'] <;> omega
  · intro z h1 h2
    rw [hcx, hmir y hby, hmir x hbx] at h1 h2
    have hsgn : (0 < c - (lam * y).valMinAbs ∧
        c - (lam * y).valMinAbs < c - (lam * x).valMinAbs) ∨
        (c - (lam * y).valMinAbs < c - (lam * x).valMinAbs ∧
          c - (lam * x).valMinAbs < 0) := by
      rcases hadm with h | h
      · have := h _ hby.1 hby.2
        exact Or.inl ⟨by omega, by omega⟩
      · have := h _ hbx.1 hbx.2
        exact Or.inr ⟨by omega, by omega⟩
    obtain ⟨j, hj1, hj2, hj⟩ := exists_mirror_of_gap hsgn h1 h2
    have hjb1 : β ≤ j := by have := hbx.1; omega
    have hjb2 : j < β + ℓ := by have := hby.2; omega
    rcases hj with hj | hj
    · have := hmir' z j hjb1 hjb2 hj
      exact hcore2 z (by omega) (by omega)
    · have hj' : (lam * -z).valMinAbs = c - j := by
        rw [mul_neg, valMinAbs_neg', hj]
        ring
      have := hmir' (-z) j hjb1 hjb2 hj'
      exact hsymm z (hcore2 (-z) (by omega) (by omega))

/-! ### Tails of the default gadget -/

open FactorCap

/-- A tail `H` of the default gadget completed by the gadget edges of `F_{s0}`, in the coordinate
`x = 2v - 7` (`ulzd-rescue.md` (2f5b9d3) §1). A hybrid `(T_0 ∖ E') ∪ R'` is the case where `H`
differs from `T(n)` exactly at the labels of `E'`, and these are the `z` with
`(tailCoord hm H).mate (some z) ≠ some (-z)`. -/
noncomputable def tailCoord (hm : 5 ≤ m) (H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m))) :
    PerfectMatching (Vertex m) :=
  capAffine m • glue (factor m (capCenter m)) (gadget m)ᶜ (factor_capCenter_mem_compl hm) H

/-- `capAffine` carries `H` to `tailCoord hm H`. -/
theorem capAffine_tail_mate (hm : 5 ≤ m) (H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m)))
    (u : ((gadget m)ᶜ : Finset (Vertex m))) :
    capAffine m (H.mate u) = (tailCoord hm H).mate (capAffine m u) := by
  rw [tailCoord, smul_mate,
    show (capAffine m)⁻¹ (capAffine m u) = u from (capAffine m).symm_apply_apply _, glue_mate_coe]

/-- The gadget edge `{4, 3}` of `F_{s0}` is the `F_0`-edge `{1, -1}` of `tailCoord hm H`. -/
theorem tailCoord_mate_one (hm : 5 ≤ m) (H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m))) :
    (tailCoord hm H).mate (some 1) = some (-1) := by
  have h4 : capAffine m (some 4) = some 1 := by
    rw [capAffine_some]
    norm_num
  have hg : some (4 : ZMod (2 * m - 1)) ∈ gadget m :=
    Finset.mem_image.2 ⟨4, by simp, by simp⟩
  have hinv : (capAffine m)⁻¹ (some 1) = some 4 := by
    rw [Equiv.Perm.inv_eq_iff_eq, h4]
  rw [tailCoord, smul_mate, hinv,
    glue_mate_of_notMem _ _ _ _ (fun h ↦ Finset.mem_compl.1 h hg),
    capAffine_factor_capCenter_mate, h4, factor, factor_mate,
    mateFn_of_ne _ _ (one_ne_zero_of_two_le (by omega))]
  congr 1
  ring

/-- The gadget `{1, …, 6}` maps to `±1, ±3, ±5`, so a vertex `x` with label outside `1, 3, 5`
comes from a tail vertex. -/
theorem capAffine_inv_notMem_gadget {z : ZMod (2 * m - 1)}
    (hz : z ≠ 1 ∧ z ≠ -1 ∧ z ≠ 3 ∧ z ≠ -3 ∧ z ≠ 5 ∧ z ≠ -5) :
    (capAffine m)⁻¹ (some z) ∉ gadget m := by
  intro hg
  obtain ⟨k, hk, hkz⟩ := Finset.mem_image.1 hg
  rw [Equiv.Perm.eq_inv_iff_eq, capAffine_some, Option.some.injEq] at hkz
  rw [Finset.mem_Icc] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
  obtain ⟨hk1, hk2⟩ := hk
  interval_cases k <;> norm_num at hkz <;> rw [← hkz] at h1 h2 h3 h4 h5 h6 <;> simp_all

/-- Proposition 3 of `ulzd-rescue.md` (2f5b9d3) for a tail `H` of the default gadget, which is the
deterministic part of Theorem 4. Let `W` be a valid union of systems in the coordinate
`x = 2v - 7`, whose labels avoid `1, 3, 5` and the defects of `H`, and let every `t ≠ 0` have a
pair meeting (a) and (b) of Lemma 2. Then some zero state `P` has `|H ∖ P| = |W|`, so
`ρ(H) ≤ |W|`. Theorem 4 supplies such a `W` with `|W| ≤ C_0 (√(d' ln n) + n^{1/4} √(ln n))`
by a probabilistic construction, which is not formalized here. -/
theorem reflection_repair_tail (hm : 5 ≤ m)
    (H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m))) (R : ReflSet m)
    (hG : ∀ z ∈ R.W, z ≠ 1 ∧ z ≠ -1 ∧ z ≠ 3 ∧ z ≠ -3 ∧ z ≠ 5 ∧ z ≠ -5)
    (h : ∀ z ∈ R.W, (tailCoord hm H).mate (some z) = some (-z))
    (hcov : ∀ t : ZMod (2 * m - 1), t ≠ 0 → ∃ lam : (ZMod (2 * m - 1))ˣ, 2 * t * lam = 1 ∧
      ∃ x y, IsReflCert (tailCoord hm H) R lam x y) :
    ∃ P : ZeroState m, tailDist P.1 H = R.W.card := by
  have hZ := isZeroState_repair (by omega) R _ h (tailCoord_mate_one hm H)
    ⟨fun h1 ↦ (hG 1 h1).1 rfl, fun h1 ↦ (hG _ h1).2.1 rfl⟩ hcov
  refine ⟨⟨(capAffine m)⁻¹ • R.repair (tailCoord hm H) h, ?_⟩, ?_⟩
  · refine (isZeroState_affine_smul_iff m (isUnit_two (modulus_odd m)).unit (-7) _).1 ?_
    rw [show shift m (-7) * scale m (isUnit_two (modulus_odd m)).unit = capAffine m from rfl,
      smul_inv_smul]
    exact hZ
  · refine R.tailDist_inv_smul_repair h (capAffine m) H (capAffine_tail_mate hm H) ?_
    rintro (_ | z) hp
    · exact absurd hp R.none_notMem_verts
    refine Finset.mem_compl.2 (capAffine_inv_notMem_gadget ?_)
    rcases R.some_mem_verts.1 hp with hz | hz
    · exact hG z hz
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG _ hz
      exact ⟨fun e ↦ h2 (by rw [e]), fun e ↦ h1 (by rw [e, neg_neg]), fun e ↦ h4 (by rw [e]),
        fun e ↦ h3 (by rw [e, neg_neg]), fun e ↦ h6 (by rw [e]), fun e ↦ h5 (by rw [e, neg_neg])⟩

/-- A reflection cover of a tail `H` of size at most `K`: a valid union of systems with
`|W| ≤ K`, labels avoiding `1, 3, 5` and the defects of `H`, and a pair meeting (a) and (b) of
Lemma 2 at every `t ≠ 0` (`ulzd-rescue.md` (2f5b9d3) Theorem 4, the outcome of Steps 0 to 3). -/
def HasReflCover (hm : 5 ≤ m) (H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m))) (K : ℕ) :
    Prop :=
  ∃ R : ReflSet m, R.W.card ≤ K ∧
    (∀ z ∈ R.W, z ≠ 1 ∧ z ≠ -1 ∧ z ≠ 3 ∧ z ≠ -3 ∧ z ≠ 5 ∧ z ≠ -5) ∧
    (∀ z ∈ R.W, (tailCoord hm H).mate (some z) = some (-z)) ∧
    ∀ t : ZMod (2 * m - 1), t ≠ 0 → ∃ lam : (ZMod (2 * m - 1))ˣ, 2 * t * lam = 1 ∧
      ∃ x y, IsReflCert (tailCoord hm H) R lam x y

/-- The deterministic part of Theorem 4 of `ulzd-rescue.md` (2f5b9d3): a reflection cover of size
`K` gives `ρ(H) ≤ K`. -/
theorem exists_zeroState_of_hasReflCover (hm : 5 ≤ m)
    {H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m))} {K : ℕ} (hH : HasReflCover hm H K) :
    ∃ P : ZeroState m, tailDist P.1 H ≤ K := by
  obtain ⟨R, hK, hG, h, hcov⟩ := hH
  obtain ⟨P, hP⟩ := reflection_repair_tail hm H R hG h hcov
  exact ⟨P, hP ▸ hK⟩

/-- If every tail of the default gadget has a reflection cover of size `K`, then `N_m ≤ K`
(`ulzd-rescue.md` (2f5b9d3) Theorem 4, deterministic part, in the form of `RepairBound`). -/
theorem repairBound_of_hasReflCover (hm : 5 ≤ m)
    (hH : ∀ H : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m)), HasReflCover hm H K) :
    RepairBound m (gadget m) K :=
  fun H ↦ exists_zeroState_of_hasReflCover hm (hH H)

/-- Theorem 4 of `ulzd-rescue.md` (2f5b9d3) in the window reduction of `hybwin-contra.md`
(cd19551) §2 (`repairBound_of_window`). If every tail at distance below `d₁` from `T(n)` has a
reflection cover of size `K₀` (the probabilistic Steps 0 to 3 of Theorem 4, assumed), and every
hybrid with `|E′| ≥ d₁` has `ρ ≤ K`, then `N_m ≤ max(K, K₀)`. -/
theorem repairBound_of_window_reflCover (hm : 5 ≤ m) {d₁ K K₀ : ℕ}
    (hlow : ∀ T : PerfectMatching ((gadget m)ᶜ : Finset (Vertex m)),
      tailDist (factor m (capCenter m)) T < d₁ → HasReflCover hm T K₀)
    (hwin : ∀ (S : Finset ((gadget m)ᶜ : Finset (Vertex m)))
      (hS : ∀ v ∈ S, (factorTail m hm).mate v ∈ S) (R : PerfectMatching S),
      IsEdgeFree (factorTail m hm) R → 2 * d₁ ≤ S.card →
        ∃ P : ZeroState m, tailDist P.1 (glue (factorTail m hm) S hS R) ≤ K) :
    RepairBound m (gadget m) (max K K₀) :=
  repairBound_of_window hm (fun T hT ↦ exists_zeroState_of_hasReflCover hm (hlow T hT)) hwin

end RoundRobin.Canonical

end Pairing
