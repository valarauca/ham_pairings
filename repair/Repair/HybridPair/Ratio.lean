import Repair.HybridPair.Contexts

/-!
# The joint law of two contexts depends only on the ratio (Theorem 1 of pair incoherence)

For a unit `w` of `ℤ/n`, `n = 2m - 1`, the scaling `μ_w = scale m w` fixes `F_0` and `∞`, sends
`F_t` to `F_{wt}` and permutes the unions `A = V(E)` of `F_0`-edges. Contraction commutes with
relabelling, so `C_{wt}(wE) = μ_w(C_t(E))`. Summing over the label sets of a given size, the pair
statistics of `(C_s(E), C_t(E))` depend on `(s, t)` only through `λ = s/t`.

* `walk_smul`, `contract_smul` : the contraction walk and `κ_Q` commute with relabelling by any
  permutation `σ`, `κ_{σQ}(σA) = σ κ_Q(A)`.
* `RoundRobin.Canonical.context_scale` (Theorem 1, pointwise) : `C_{wt}(wE) = μ_w(C_t(E))`.
* `jointCount_congr`, `commonCount_congr` : `h` and the number of common edges are invariant
  under relabelling. `commonCount A B = #{v | A v = B v}` is `2 l(A, B)`.
* `RoundRobin.Canonical.labelSets m e` : the unions of `e` edges of `F_0` avoiding `∞`, that is
  the `V(E)` for `E` an `e`-subset of the labels `L`.
* `RoundRobin.Canonical.sum_pairJoint_eq_of_mul_eq`, `sum_pairCommon_eq_of_mul_eq` (Theorem 1) :
  `∑_E h(C_s(E), C_t(E))` and `∑_E l(C_s(E), C_t(E))` are equal for `(s, t)` and `(s', t')`
  whenever `s t' = s' t` with `t, t'` units, so `R_2` and `l̄` depend only on `λ = s/t`.
* `sum_pairJoint_normal_form` : the normal form `(s, t) ↦ (1/2, 1/(2λ))`, `λ = s/t`.
* `sum_pairJoint_comm`, `sum_pairCommon_comm` : `R_2(λ) = R_2(λ⁻¹)` and `l̄(λ) = l̄(λ⁻¹)`.

Source: `results/hybrid-pair-incoherence.md` (organize-archive 0dca0a5), §2, Theorem 1.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The contraction walk commutes with relabelling (`results/hybrid-pair-incoherence.md`,
Theorem 1): the walk of `σP, σQ` from `σa` is the image under `σ` of the walk of `P, Q` from
`a`. -/
theorem walk_smul (σ : Equiv.Perm V) (P Q : PerfectMatching V) (a : V) (i : ℕ) :
    evenPt (σ • P) (σ • Q) (σ a) i = σ (evenPt P Q a i) ∧
      oddPt (σ • P) (σ • Q) (σ a) i = σ (oddPt P Q a i) := by
  induction i with
  | zero => simp [oddPt]
  | succ i ih =>
    have he : evenPt (σ • P) (σ • Q) (σ a) (i + 1) = σ (evenPt P Q a (i + 1)) := by
      rw [evenPt_succ, ih.2, smul_mate, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, evenPt_succ]
    exact ⟨he, by rw [oddPt, he, smul_mate, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, oddPt]⟩

/-- The relabelling `A ≃ σ A` induced by a permutation `σ` (`results/hybrid-pair-incoherence.md`,
Theorem 1, the map `μ_w`). -/
def mapEquiv (σ : Equiv.Perm V) (A : Finset V) : A ≃ A.map σ.toEmbedding :=
  Equiv.subtypeEquiv σ fun a ↦ by simp

/-- Contraction commutes with relabelling (`results/hybrid-pair-incoherence.md`, Theorem 1):
`κ_{σQ}(σA)`, taken with respect to `σP`, is `σ κ_Q(A)`. -/
theorem contract_smul (σ : Equiv.Perm V) (P Q : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) {P' Q' : PerfectMatching V} (hP : σ • P = P')
    (hQ : σ • Q = Q') (hA' : ∀ v ∈ A.map σ.toEmbedding, P'.mate v ∈ A.map σ.toEmbedding) :
    contract P' Q' (A.map σ.toEmbedding) hA' = congr (mapEquiv σ A) (contract P Q A hA) := by
  subst hP hQ
  refine PerfectMatching.ext (Equiv.ext fun s ↦ Subtype.ext ?_)
  have ha : σ.symm s ∈ A := by
    have := s.2
    rwa [Finset.mem_map_equiv] at this
  have hs' : (s : V) = σ (σ.symm s) := (σ.apply_symm_apply s).symm
  have hmem : ∀ i, oddPt (σ • P) (σ • Q) s i ∈ A.map σ.toEmbedding ↔
      oddPt P Q (σ.symm s) i ∈ A := by
    intro i
    rw [hs', (walk_smul σ P Q _ i).2]
    simp
  have hidx : exitIdx (σ • P) (σ • Q) (A.map σ.toEmbedding) hA' s =
      exitIdx P Q A hA ⟨σ.symm s, ha⟩ := by
    rw [exitIdx, Nat.find_eq_iff]
    exact ⟨(hmem _).mpr (oddPt_exitIdx_mem P Q A hA ⟨σ.symm s, ha⟩),
      fun i hi h ↦ oddPt_notMem P Q A hA ⟨σ.symm s, ha⟩ hi ((hmem i).mp h)⟩
  have hsymm : (mapEquiv σ A).symm s = ⟨σ.symm s, ha⟩ := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hs'
  rw [congr_mate, hsymm]
  change _ = σ (((contract P Q A hA).mate ⟨σ.symm s, ha⟩ : A) : V)
  rw [contract_mate, contract_mate, coe_contractFun, coe_contractFun, hidx]
  have hw := (walk_smul σ P Q (σ.symm s) (exitIdx P Q A hA ⟨σ.symm s, ha⟩)).2
  rw [σ.apply_symm_apply] at hw
  exact hw

/-- `jointCount` is invariant under relabelling (`results/hybrid-pair-incoherence.md`,
Theorem 1). -/
theorem jointCount_congr {V' : Type*} [Fintype V'] [DecidableEq V'] (e : V ≃ V')
    (X Y : PerfectMatching V) : jointCount (congr e X) (congr e Y) = jointCount X Y := by
  refine Finset.card_equiv (congr e).symm fun R ↦ ?_
  simp only [mem_filter, mem_univ, true_and]
  conv_lhs => rw [← (congr e).apply_symm_apply R]
  rw [ham_congr, ham_congr]

/-- `jointCount` is symmetric. -/
theorem jointCount_comm (X Y : PerfectMatching V) : jointCount X Y = jointCount Y X := by
  rw [jointCount, jointCount]
  exact congrArg card (filter_congr fun R _ ↦ and_comm)

/-- `#{v | A v = B v}`, twice the number `l(A, B)` of common edges
(`results/hybrid-pair-incoherence.md` §1). -/
def commonCount (A B : PerfectMatching V) : ℕ :=
  (univ.filter fun v ↦ A.mate v = B.mate v).card

/-- `commonCount` is invariant under relabelling (`results/hybrid-pair-incoherence.md`,
Theorem 1). -/
theorem commonCount_congr {V' : Type*} [Fintype V'] [DecidableEq V'] (e : V ≃ V')
    (X Y : PerfectMatching V) : commonCount (congr e X) (congr e Y) = commonCount X Y := by
  refine Finset.card_equiv e.symm fun v ↦ ?_
  simp only [mem_filter, mem_univ, true_and, congr_mate, e.apply_eq_iff_eq]

/-- `commonCount` is symmetric. -/
theorem commonCount_comm (X Y : PerfectMatching V) : commonCount X Y = commonCount Y X := by
  rw [commonCount, commonCount]
  exact congrArg card (filter_congr fun v _ ↦ eq_comm)

end PerfectMatching

namespace RoundRobin.Canonical

open Finset PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `μ_w` maps unions of `F_0`-edges to unions of `F_0`-edges, and back
(`results/hybrid-pair-incoherence.md`, Theorem 1). -/
theorem closed_map_scale_iff (w : (ZMod (2 * m - 1))ˣ) (A : Finset (Vertex m)) :
    (∀ v ∈ A.map (scale m w).toEmbedding, (factor m 0).mate v ∈ A.map (scale m w).toEmbedding) ↔
      ∀ v ∈ A, (factor m 0).mate v ∈ A := by
  have key : ∀ a, (factor m 0).mate (scale m w a) = scale m w ((factor m 0).mate a) := by
    intro a
    rw [scale_mate_factor, mul_zero]
  constructor
  · intro h v hv
    have := h _ (Finset.mem_map_of_mem _ hv)
    rw [Equiv.coe_toEmbedding, key] at this
    simpa using this
  · intro h v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    rw [Equiv.coe_toEmbedding, key]
    exact Finset.mem_map_of_mem _ (h a ha)

/-- Theorem 1 of `results/hybrid-pair-incoherence.md`, pointwise. For a unit `w`,
`C_{wt}(wE) = μ_w(C_t(E))`, where `μ_w = scale m w` and `wE` is the image of `A = V(E)`. -/
theorem context_scale (w : (ZMod (2 * m - 1))ˣ) (t : ZMod (2 * m - 1)) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A)
    (hA' : ∀ v ∈ A.map (scale m w).toEmbedding,
      (factor m 0).mate v ∈ A.map (scale m w).toEmbedding) :
    context m ((w : ZMod (2 * m - 1)) * t) (A.map (scale m w).toEmbedding) hA' =
      congr (mapEquiv (scale m w) A) (context m t A hA) :=
  contract_smul _ _ _ A hA (by rw [scale_smul_factor, mul_zero]) (scale_smul_factor m w t) hA'

/-- The label sets of size `e`: the unions `A = V(E)` of `e` edges of `F_0` avoiding `∞`, with
`E` an `e`-subset of `L = {1, …, m - 1}` (`results/hybrid-pair-incoherence.md` §1). -/
def labelSets (m : ℕ) [NeZero m] (e : ℕ) : Finset (Finset (Vertex m)) :=
  univ.filter fun A ↦ (∀ v ∈ A, (factor m 0).mate v ∈ A) ∧ none ∉ A ∧ A.card = 2 * e

/-- `μ_w` permutes the label sets of each size (`results/hybrid-pair-incoherence.md`,
Theorem 1). -/
theorem map_scale_mem_labelSets_iff (w : (ZMod (2 * m - 1))ˣ) (e : ℕ) (A : Finset (Vertex m)) :
    A.map (scale m w).toEmbedding ∈ labelSets m e ↔ A ∈ labelSets m e := by
  simp only [labelSets, mem_filter, mem_univ, true_and, closed_map_scale_iff, card_map]
  have : none ∈ A.map (scale m w).toEmbedding ↔ none ∈ A := by
    rw [Finset.mem_map_equiv, ← Equiv.Perm.inv_def, scale_inv_none]
  rw [this]

/-- `h(C_s(E), C_t(E))` in counting form, `0` off unions of `F_0`-edges
(`results/hybrid-pair-incoherence.md` §1). -/
def pairJoint (s t : ZMod (2 * m - 1)) (A : Finset (Vertex m)) : ℕ :=
  if h : ∀ v ∈ A, (factor m 0).mate v ∈ A then jointCount (context m s A h) (context m t A h)
  else 0

/-- `2 l(C_s(E), C_t(E))`, `0` off unions of `F_0`-edges (`results/hybrid-pair-incoherence.md`
§1). -/
def pairCommon (s t : ZMod (2 * m - 1)) (A : Finset (Vertex m)) : ℕ :=
  if h : ∀ v ∈ A, (factor m 0).mate v ∈ A then commonCount (context m s A h) (context m t A h)
  else 0

/-- `h(C_{ws}(wE), C_{wt}(wE)) = h(C_s(E), C_t(E))` (`results/hybrid-pair-incoherence.md`,
Theorem 1). -/
theorem pairJoint_map_scale (w : (ZMod (2 * m - 1))ˣ) (s t : ZMod (2 * m - 1))
    (A : Finset (Vertex m)) :
    pairJoint ((w : ZMod (2 * m - 1)) * s) (w * t) (A.map (scale m w).toEmbedding) =
      pairJoint s t A := by
  by_cases h : ∀ v ∈ A, (factor m 0).mate v ∈ A
  · have h' := (closed_map_scale_iff w A).mpr h
    rw [pairJoint, dite_eq_left h', pairJoint, dite_eq_left h,
      context_scale w s A h h',
      context_scale w t A h h', jointCount_congr]
  · rw [pairJoint, dite_eq_right fun h' ↦ h ((closed_map_scale_iff w A).mp h'),
      pairJoint, dite_eq_right h]

/-- `l(C_{ws}(wE), C_{wt}(wE)) = l(C_s(E), C_t(E))` (`results/hybrid-pair-incoherence.md`,
Theorem 1). -/
theorem pairCommon_map_scale (w : (ZMod (2 * m - 1))ˣ) (s t : ZMod (2 * m - 1))
    (A : Finset (Vertex m)) :
    pairCommon ((w : ZMod (2 * m - 1)) * s) (w * t) (A.map (scale m w).toEmbedding) =
      pairCommon s t A := by
  by_cases h : ∀ v ∈ A, (factor m 0).mate v ∈ A
  · have h' := (closed_map_scale_iff w A).mpr h
    rw [pairCommon, dite_eq_left h', pairCommon, dite_eq_left h,
      context_scale w s A h h',
      context_scale w t A h h', commonCount_congr]
  · rw [pairCommon, dite_eq_right fun h' ↦ h ((closed_map_scale_iff w A).mp h'),
      pairCommon, dite_eq_right h]

/-- Theorem 1 of `results/hybrid-pair-incoherence.md` for `h`: for a unit `w`,
`∑_E h(C_{ws}(E), C_{wt}(E)) = ∑_E h(C_s(E), C_t(E))` over the label sets of size `e`. -/
theorem sum_pairJoint_scale (w : (ZMod (2 * m - 1))ˣ) (s t : ZMod (2 * m - 1)) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairJoint ((w : ZMod (2 * m - 1)) * s) (w * t) A =
      ∑ A ∈ labelSets m e, pairJoint s t A :=
  (Finset.sum_equiv (Equiv.finsetCongr (scale m w))
    (fun A ↦ by rw [Equiv.finsetCongr_apply, map_scale_mem_labelSets_iff])
    fun A _ ↦ by rw [Equiv.finsetCongr_apply, pairJoint_map_scale]).symm

/-- Theorem 1 of `results/hybrid-pair-incoherence.md` for `l`: for a unit `w`,
`∑_E l(C_{ws}(E), C_{wt}(E)) = ∑_E l(C_s(E), C_t(E))` over the label sets of size `e`. -/
theorem sum_pairCommon_scale (w : (ZMod (2 * m - 1))ˣ) (s t : ZMod (2 * m - 1)) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairCommon ((w : ZMod (2 * m - 1)) * s) (w * t) A =
      ∑ A ∈ labelSets m e, pairCommon s t A :=
  (Finset.sum_equiv (Equiv.finsetCongr (scale m w))
    (fun A ↦ by rw [Equiv.finsetCongr_apply, map_scale_mem_labelSets_iff])
    fun A _ ↦ by rw [Equiv.finsetCongr_apply, pairCommon_map_scale]).symm

omit [NeZero m] in
/-- The unit `w = t' / t` carries `(s, t)` to `(s', t')` when `s t' = s' t`. -/
theorem exists_unit_of_mul_eq {s t s' t' : ZMod (2 * m - 1)} (ht : IsUnit t) (ht' : IsUnit t')
    (h : s * t' = s' * t) : ∃ w : (ZMod (2 * m - 1))ˣ, (w : ZMod (2 * m - 1)) * s = s' ∧
      (w : ZMod (2 * m - 1)) * t = t' := by
  obtain ⟨u, rfl⟩ := ht
  obtain ⟨u', rfl⟩ := ht'
  refine ⟨u' * u⁻¹, ?_, ?_⟩
  · calc ((u' * u⁻¹ : (ZMod (2 * m - 1))ˣ) : ZMod (2 * m - 1)) * s
        = ((u⁻¹ : (ZMod (2 * m - 1))ˣ) : ZMod (2 * m - 1)) * (s * u') := by
          rw [Units.val_mul]
          ring
      _ = s' := by rw [h, mul_comm s', ← mul_assoc, Units.inv_mul, one_mul]
  · rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

/-- Theorem 1 of `results/hybrid-pair-incoherence.md` for `h` (so for `R_2`): if `s t' = s' t`
with `t, t'` units, then `∑_E h(C_s(E), C_t(E)) = ∑_E h(C_{s'}(E), C_{t'}(E))`. So the sum
depends on `(s, t)` only through `λ = s/t`. -/
theorem sum_pairJoint_eq_of_mul_eq {s t s' t' : ZMod (2 * m - 1)} (ht : IsUnit t)
    (ht' : IsUnit t') (h : s * t' = s' * t) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairJoint s t A = ∑ A ∈ labelSets m e, pairJoint s' t' A := by
  obtain ⟨w, hs, hts⟩ := exists_unit_of_mul_eq ht ht' h
  rw [← sum_pairJoint_scale w s t e, hs, hts]

/-- Theorem 1 of `results/hybrid-pair-incoherence.md` for `l` (so for `l̄`): if `s t' = s' t`
with `t, t'` units, then `∑_E l(C_s(E), C_t(E)) = ∑_E l(C_{s'}(E), C_{t'}(E))`. -/
theorem sum_pairCommon_eq_of_mul_eq {s t s' t' : ZMod (2 * m - 1)} (ht : IsUnit t)
    (ht' : IsUnit t') (h : s * t' = s' * t) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairCommon s t A = ∑ A ∈ labelSets m e, pairCommon s' t' A := by
  obtain ⟨w, hs, hts⟩ := exists_unit_of_mul_eq ht ht' h
  rw [← sum_pairCommon_scale w s t e, hs, hts]

/-- The normal form of Theorem 1 (`results/hybrid-pair-incoherence.md`): for a unit `t`,
`s = λ t` and `2 t₀ λ = 1`, `∑_E h(C_s(E), C_t(E)) = ∑_E h(C_{1/2}(E), C_{t₀}(E))`, with
`1/2 = m` and `t₀ = 1/(2λ)`. -/
theorem sum_pairJoint_normal_form {s t t₀ : ZMod (2 * m - 1)} {lam : (ZMod (2 * m - 1))ˣ}
    (ht : IsUnit t) (hs : s = lam * t) (ht₀ : 2 * t₀ * lam = 1) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairJoint s t A = ∑ A ∈ labelSets m e, pairJoint (m : ZMod _) t₀ A := by
  refine sum_pairJoint_eq_of_mul_eq ht (IsUnit.of_mul_eq_one (2 * (lam : ZMod (2 * m - 1))) ?_)
    ?_ e
  · rw [show t₀ * (2 * (lam : ZMod (2 * m - 1))) = 2 * t₀ * lam by ring]
    exact ht₀
  · rw [hs]
    linear_combination t * mul_eq_half ht₀

/-- `R_2(λ) = R_2(λ⁻¹)` (`results/hybrid-pair-incoherence.md`, Theorem 1). -/
theorem sum_pairJoint_comm (s t : ZMod (2 * m - 1)) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairJoint s t A = ∑ A ∈ labelSets m e, pairJoint t s A := by
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [pairJoint, pairJoint]
  split_ifs
  · exact jointCount_comm _ _
  · rfl

/-- `l̄(λ) = l̄(λ⁻¹)` (`results/hybrid-pair-incoherence.md`, Theorem 1). -/
theorem sum_pairCommon_comm (s t : ZMod (2 * m - 1)) (e : ℕ) :
    ∑ A ∈ labelSets m e, pairCommon s t A = ∑ A ∈ labelSets m e, pairCommon t s A := by
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [pairCommon, pairCommon]
  split_ifs
  · exact commonCount_comm _ _
  · rfl

end RoundRobin.Canonical

end Pairing
