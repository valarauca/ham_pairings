import Repair.HybridPair.Ratio

/-!
# Several common edges (Lemma 2 of pair incoherence, product form)

Iterating the common-edge contraction of `CommonEdge.lean` over `l` common edges. The restrictions
to a set `U` closed under both matchings are compared directly, and the contracted vertex sets are
identified with `U ∖ {a, b}` by `jointCount_congr`.

* `jointCount_restrict_eq_of_mate_eq` : one common edge, for restrictions to `U`.
* `jointCount_restrict_eq_prod` : `l` common edges forming a set `T ⊆ U`,
  `jointCount(U) = ∏_{i < l} (|U| - 2 - 2i) · jointCount(U ∖ T)`.
* `jointCount_eq_prod` : the same on `V` with `|V| = 2e`, the counting form of the factor
  `∏_{i < l} (1 + 1/(2(e - i) - 2))`.

Source: `results/hybrid-pair-incoherence.md` (organize-archive 0dca0a5), §2, Lemma 2.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- `jointCount` of the restrictions to `U` depends only on the set `U`. -/
theorem jointCount_restrict_congr (A B : PerfectMatching V) {U₁ U₂ : Finset V} (h : U₁ = U₂)
    (hA₁ : ∀ v ∈ U₁, A.mate v ∈ U₁) (hB₁ : ∀ v ∈ U₁, B.mate v ∈ U₁)
    (hA₂ : ∀ v ∈ U₂, A.mate v ∈ U₂) (hB₂ : ∀ v ∈ U₂, B.mate v ∈ U₂) :
    jointCount (restrict A U₁ hA₁) (restrict B U₁ hB₁) =
      jointCount (restrict A U₂ hA₂) (restrict B U₂ hB₂) := by
  subst h
  rfl

/-- `jointCount` of the restrictions to `univ` is `jointCount`. -/
theorem jointCount_restrict_univ (A B : PerfectMatching V) :
    jointCount (restrict A univ fun _ _ ↦ mem_univ _) (restrict B univ fun _ _ ↦ mem_univ _) =
      jointCount A B := by
  rw [← jointCount_congr (Equiv.subtypeUnivEquiv mem_univ)]
  rfl

omit [Fintype V] in
/-- Lemma 2 of `results/hybrid-pair-incoherence.md` for restrictions. If `A` and `B` map `U` into
itself, share the edge `{a, b}` with `a ∈ U`, and `|U| > 2`, then the joint count on `U` is
`|U| - 2` times the joint count on `U ∖ {a, b}`. -/
theorem jointCount_restrict_eq_of_mate_eq {A B : PerfectMatching V} {U : Finset V}
    (hAU : ∀ v ∈ U, A.mate v ∈ U) (hBU : ∀ v ∈ U, B.mate v ∈ U) {a b : V} (ha : a ∈ U)
    (hA : A.mate a = b) (hB : B.mate a = b) (hU : 2 < U.card)
    (hAU' : ∀ v ∈ U \ {a, b}, A.mate v ∈ U \ {a, b})
    (hBU' : ∀ v ∈ U \ {a, b}, B.mate v ∈ U \ {a, b}) :
    jointCount (restrict A U hAU) (restrict B U hBU) =
      (U.card - 2) * jointCount (restrict A (U \ {a, b}) hAU') (restrict B (U \ {a, b}) hBU') := by
  have hb : b ∈ U := hA ▸ hAU a ha
  have hA₀ : (restrict A U hAU).mate ⟨a, ha⟩ = ⟨b, hb⟩ := Subtype.ext hA
  have hB₀ : (restrict B U hBU).mate ⟨a, ha⟩ = ⟨b, hb⟩ := Subtype.ext hB
  rw [jointCount_eq_of_mate_eq hA₀ hB₀ (by rwa [Fintype.card_coe]), Fintype.card_coe]
  congr 1
  let e : pairCompl (⟨a, ha⟩ : U) ⟨b, hb⟩ ≃ (U \ {a, b} : Finset V) :=
    { toFun x := ⟨x.1.1, by
        have hx := mem_pairCompl.mp x.2
        simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
        exact ⟨x.1.2, fun h ↦ hx.1 (Subtype.ext h), fun h ↦ hx.2 (Subtype.ext h)⟩⟩
      invFun y := ⟨⟨y.1, (mem_sdiff.mp y.2).1⟩, by
        have hy := y.2
        simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hy
        exact mem_pairCompl.mpr ⟨fun h ↦ hy.2.1 (congrArg Subtype.val h),
          fun h ↦ hy.2.2 (congrArg Subtype.val h)⟩⟩
      left_inv x := rfl
      right_inv y := rfl }
  rw [← jointCount_congr e]
  rfl

omit [Fintype V] in
/-- Lemma 2 of `results/hybrid-pair-incoherence.md` with `l` common edges, counting form. If `A`
and `B` map `U` into itself and agree on a set `T ⊆ U` of `2l` vertices closed under `A`, with
`2l < |U|`, then
`jointCount(U) = ∏_{i < l} (|U| - 2 - 2i) · jointCount(U ∖ T)`.
With `|U| = 2e` the factor `2(e - i) - 2` is the counting form of `1 + 1/(2(e - i) - 2)`. -/
theorem jointCount_restrict_eq_prod (A B : PerfectMatching V) (l : ℕ) :
    ∀ (U T : Finset V) (hAU : ∀ v ∈ U, A.mate v ∈ U) (hBU : ∀ v ∈ U, B.mate v ∈ U)
      (hAT' : ∀ v ∈ U \ T, A.mate v ∈ U \ T) (hBT' : ∀ v ∈ U \ T, B.mate v ∈ U \ T),
      T ⊆ U → (∀ v ∈ T, A.mate v ∈ T) → (∀ v ∈ T, B.mate v = A.mate v) → T.card = 2 * l →
      2 * l < U.card →
      jointCount (restrict A U hAU) (restrict B U hBU) =
        (∏ i ∈ range l, (U.card - 2 - 2 * i)) *
          jointCount (restrict A (U \ T) hAT') (restrict B (U \ T) hBT') := by
  induction l with
  | zero =>
    intro U T hAU hBU hAT' hBT' _ _ _ hT _
    rw [range_zero, prod_empty, one_mul]
    have hT0 : T = ∅ := card_eq_zero.mp (by simpa using hT)
    exact jointCount_restrict_congr A B (by rw [hT0, sdiff_empty] : U = U \ T) _ _ _ _
  | succ l ih =>
    intro U T hAU hBU hAT' hBT' hTU hAT hBT hT hlU
    obtain ⟨a, ha⟩ : T.Nonempty := by
      rw [← card_pos, hT]
      omega
    set b := A.mate a with hbdef
    have hab : a ≠ b := fun h ↦ A.mate_ne a h.symm
    have hbT : b ∈ T := hAT a ha
    have hB : B.mate a = b := hBT a ha
    have hpair : ({a, b} : Finset V) ⊆ T := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact ha
      · rw [mem_singleton.mp hv]
        exact hbT
    have hclose : ∀ X : PerfectMatching V, X.mate a = b → ∀ S : Finset V,
        (∀ v ∈ S, X.mate v ∈ S) → ∀ v ∈ S \ {a, b}, X.mate v ∈ S \ {a, b} := by
      intro X hX S hS v hv
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hv ⊢
      refine ⟨hS v hv.1, fun h ↦ hv.2.2 ?_, fun h ↦ hv.2.1 ?_⟩
      · rw [← X.mate_mate v, h, hX]
      · rw [← X.mate_mate v, h, ← hX, X.mate_mate]
    have hBT₀ : ∀ v ∈ T, B.mate v ∈ T := fun v hv ↦ hBT v hv ▸ hAT v hv
    have hU' : (U \ {a, b}).card = U.card - 2 := by
      rw [card_sdiff_of_subset (hpair.trans hTU), card_pair hab]
    have hT' : (T \ {a, b}).card = 2 * l := by
      rw [card_sdiff_of_subset hpair, card_pair hab, hT]
      omega
    have hsd : (U \ {a, b}) \ (T \ {a, b}) = U \ T := by
      rw [sdiff_sdiff_sdiff_cancel_right hpair]
    rw [jointCount_restrict_eq_of_mate_eq hAU hBU (hTU ha) rfl hB (by omega)
      (hclose A rfl U hAU) (hclose B hB U hBU)]
    have hAT'' : ∀ v ∈ (U \ {a, b}) \ (T \ {a, b}), A.mate v ∈ (U \ {a, b}) \ (T \ {a, b}) := by
      rw [hsd]
      exact hAT'
    have hBT'' : ∀ v ∈ (U \ {a, b}) \ (T \ {a, b}), B.mate v ∈ (U \ {a, b}) \ (T \ {a, b}) := by
      rw [hsd]
      exact hBT'
    rw [ih (U \ {a, b}) (T \ {a, b}) _ _ hAT'' hBT'' (sdiff_subset_sdiff hTU le_rfl)
      (hclose A rfl T hAT) (fun v hv ↦ hBT v (mem_sdiff.mp hv).1) hT' (by omega),
      jointCount_restrict_congr A B hsd hAT'' hBT'' hAT' hBT', prod_range_succ', hU',
      prod_congr rfl fun i _ ↦ (show U.card - 2 - 2 - 2 * i = U.card - 2 - 2 * (i + 1) by omega),
      Nat.mul_zero, Nat.sub_zero]
    ring

/-- Lemma 2 of `results/hybrid-pair-incoherence.md` with `l` common edges, on `V` with `|V| = 2e`.
If `A` and `B` agree on a set `T` of `2l` vertices closed under `A`, with `l < e`, then
`jointCount A B = ∏_{i < l} (2e - 2 - 2i) · jointCount A' B'`, with `A'`, `B'` the restrictions to
`V ∖ T`. -/
theorem jointCount_eq_prod (A B : PerfectMatching V) {T : Finset V}
    (hAT : ∀ v ∈ T, A.mate v ∈ T) (hBT : ∀ v ∈ T, B.mate v = A.mate v) {l : ℕ}
    (hT : T.card = 2 * l) (hl : 2 * l < Fintype.card V) (hA' : ∀ v ∈ Tᶜ, A.mate v ∈ Tᶜ)
    (hB' : ∀ v ∈ Tᶜ, B.mate v ∈ Tᶜ) :
    jointCount A B = (∏ i ∈ range l, (Fintype.card V - 2 - 2 * i)) *
      jointCount (restrict A Tᶜ hA') (restrict B Tᶜ hB') := by
  have hc : univ \ T = Tᶜ := (compl_eq_univ_sdiff T).symm
  have hA'' : ∀ v ∈ univ \ T, A.mate v ∈ univ \ T := by
    rw [hc]
    exact hA'
  have hB'' : ∀ v ∈ univ \ T, B.mate v ∈ univ \ T := by
    rw [hc]
    exact hB'
  rw [← jointCount_restrict_univ A B, jointCount_restrict_eq_prod A B l univ T _ _ hA'' hB''
    (subset_univ _) hAT hBT hT (by rwa [card_univ]), card_univ,
    jointCount_restrict_congr A B hc hA'' hB'' hA' hB']

end PerfectMatching

end Pairing
