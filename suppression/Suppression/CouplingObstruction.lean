import Pairing.Basic
import Suppression.Prob

/-!
# One step of the coupling obstruction for the reduction chain (COD-211)

**A warning sign.** This file is the reason a labelled coupling of two `k = 3` reduction chains
cannot coalesce. Under every causal coupling, the mismatch of each colour under the tracked
identification is conserved up to `O(1/j²)` per step, plus a charge of at most `5` for every
vertex the coupling relabels. A coupling that keeps a stable identification therefore never turns
it into an isomorphism, and a successful coupling must relabel a positive density of vertices.
The source is `results/coupling-obstruction.md` (organize-archive commit 17471a7, COD-211),
Lemmas 1 and 2 of §3.1, which are the deterministic core of its Theorem A. Read that file before
attempting such a coupling.

**Setting.** A step of the reduction chain at `(x, y)`, with `y ≠ x, M x` for each colour `M`,
contracts every colour along `xy`: it deletes `x` and `y` and joins `M x` to `M y`
(`contractEdge`). Two chains on `V` and `V'` are tracked by a bijection `φ : V ≃ V'`, and the
mismatch of one colour is `D = #{v | φ (M v) ≠ M' (φ v)}` (`mismatch`). Chain 1 steps at
`(x, y)` and chain 2 at `(x', y')`, with new identification `φ_{t+1}`. This is recorded by the
single bijection `ψ = φ_{t+1} ∪ {x ↦ x', y ↦ y'}`, the paper's `φ̂_t`, so that `x' = ψ x`,
`y' = ψ y` and `φ_{t+1}` is `ψ` restricted (`restrictPair`). The relabelling count is
`b = #{v | ψ v ≠ φ v}` (`reidCount`), and the step is common when `b = 0`. The mismatch after the
step is `contractMismatch ψ M M' x y`, which `mismatch_contractEdge` identifies with the mismatch
of the contracted matchings. On one vertex set, `N = φ⁻¹ M' φ`.

* `card_mismatch_eq_add`, `mismatch_eq_contractMismatch_add` (Lemma 1, exact) : a common step
  loses exactly `stepLoss = 2·[x and y mismatched] + 2 κ(y)`, where
  `κ(y) = [y = N M x ∧ M y = N x] + [y = M N M x] + [y = N M N x]` (`created`). The paper's table
  by cycle positions becomes this local formula, with no cycle decomposition.
* `stepLoss_le_six`, `sum_stepDec_le` : one step loses at most `6`, and
  `∑_{y ∈ A} dec(y) ≤ 2 D` for every `A` avoiding `x` and `M x`, where `dec = stepDec` is
  `stepLoss` off `y = N x`.
* `mismatch_le_mismatch_add_reidCount`, `reidCount_ne_one` : relabelling `b` vertices changes
  `D` by at most `2 b`, and `b ≠ 1`.
* `mismatch_le_contractMismatch_add` (Lemma 2, pointwise) :
  `D_t ≤ D_{t+1} + dec(y)·[b = 0] + 5 b`.
* `expect_mismatch_sub_le` (Lemma 2) : if `y` is uniform on `A`,
  `E[D_t - D_{t+1}] ≤ 2 D_t / |A| + 5 E[b]`.
* `expect_rho_ge` : with `|V| = 2j`, `|A| ≥ 2j - 4` and `j ≥ 3`,
  `E[ρ_{t+1}] ≥ ρ_t (1 - δ_j) - (5/2) E[b] / (j - 1)` with `δ_j = 8 / ((2j - 2)(2j - 4))`.
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V V' : Type*}

/-- `v = M w` iff `M v = w`. -/
theorem eq_mate_iff (M : PerfectMatching V) {v w : V} : v = M.mate w ↔ M.mate v = w :=
  ⟨fun h ↦ by rw [h, mate_mate], fun h ↦ by rw [← h, mate_mate]⟩

section Contract

variable [DecidableEq V] (M : PerfectMatching V) (x y : V)

/-- The vertex map of the contraction of `M` along `xy`: `M x ↦ M y`, `M y ↦ M x` and
`v ↦ M v` otherwise. -/
def edgeContractFun (v : V) : V :=
  if v = M.mate x then M.mate y else if v = M.mate y then M.mate x else M.mate v

variable {M x y}

/-- `M / xy` maps every vertex away from `x` and `y`. -/
theorem edgeContractFun_mem (hy : y ≠ M.mate x) (v : V) :
    edgeContractFun M x y v ≠ x ∧ edgeContractFun M x y v ≠ y := by
  unfold edgeContractFun
  split_ifs with h1 h2
  · exact ⟨fun h ↦ hy (by rw [← h, mate_mate]), M.mate_ne y⟩
  · exact ⟨M.mate_ne x, fun h ↦ hy h.symm⟩
  · exact ⟨fun h ↦ h1 (by rw [← h, mate_mate]), fun h ↦ h2 (by rw [← h, mate_mate])⟩

/-- `M / xy` sends `M x` to `M y`. -/
@[simp]
theorem edgeContractFun_mate_left : edgeContractFun M x y (M.mate x) = M.mate y := by
  simp [edgeContractFun]

/-- `M / xy` sends `M y` to `M x`. -/
theorem edgeContractFun_mate_right (hxy : x ≠ y) :
    edgeContractFun M x y (M.mate y) = M.mate x := by
  simp [edgeContractFun, M.mate.injective.ne (Ne.symm hxy)]

/-- `M / xy` agrees with `M` away from `M x` and `M y`. -/
theorem edgeContractFun_of_ne {v : V} (h1 : v ≠ M.mate x) (h2 : v ≠ M.mate y) :
    edgeContractFun M x y v = M.mate v := by
  simp [edgeContractFun, h1, h2]

/-- `M / xy` is an involution on `V ∖ {x, y}`. -/
theorem edgeContractFun_edgeContractFun (hxy : x ≠ y) {v : V} (hv : v ≠ x ∧ v ≠ y) :
    edgeContractFun M x y (edgeContractFun M x y v) = v := by
  have hab : M.mate y ≠ M.mate x := M.mate.injective.ne (Ne.symm hxy)
  by_cases h1 : v = M.mate x
  · subst h1
    simp [edgeContractFun, hab]
  by_cases h2 : v = M.mate y
  · subst h2
    simp [edgeContractFun]
  have h3 : M.mate v ≠ M.mate x := M.mate.injective.ne hv.1
  have h4 : M.mate v ≠ M.mate y := M.mate.injective.ne hv.2
  simp [edgeContractFun, h1, h2, h3, h4]

/-- `M / xy` has no fixed point. -/
theorem edgeContractFun_ne (hxy : x ≠ y) (v : V) : edgeContractFun M x y v ≠ v := by
  have hab : M.mate y ≠ M.mate x := M.mate.injective.ne (Ne.symm hxy)
  unfold edgeContractFun
  split_ifs with h1 h2
  · exact h1 ▸ hab
  · exact h2 ▸ hab.symm
  · exact M.mate_ne v

variable (M)

/-- `M / xy`, the contraction of `M` along `xy` for `y ≠ x, M x`. It deletes `x` and `y` and
joins `M x` to `M y`. Applied to every colour, this is one step of the reduction chain. -/
def contractEdge (hxy : x ≠ y) (hy : y ≠ M.mate x) : PerfectMatching {v // v ≠ x ∧ v ≠ y} where
  mate := Function.Involutive.toPerm
    (fun v ↦ ⟨edgeContractFun M x y v, edgeContractFun_mem hy v.1⟩)
    fun v ↦ Subtype.ext (edgeContractFun_edgeContractFun hxy v.2)
  mate_mate v := Subtype.ext (edgeContractFun_edgeContractFun hxy v.2)
  mate_ne v h := edgeContractFun_ne hxy v.1 (congrArg Subtype.val h)

/-- The partner of `v` in `M / xy` is `edgeContractFun M x y v`. -/
@[simp]
theorem coe_contractEdge_mate (hxy : x ≠ y) (hy : y ≠ M.mate x) (v : {v // v ≠ x ∧ v ≠ y}) :
    ((contractEdge M hxy hy).mate v : V) = edgeContractFun M x y v :=
  rfl

end Contract

/-- `ψ : V ≃ V'` restricted to `V ∖ {x, y} ≃ V' ∖ {ψ x, ψ y}`. For the paper's `ψ = φ̂_t` this is
the new identification `φ_{t+1}`. -/
def restrictPair (ψ : V ≃ V') (x y : V) : {v // v ≠ x ∧ v ≠ y} ≃ {w // w ≠ ψ x ∧ w ≠ ψ y} :=
  ψ.subtypeEquiv fun v ↦ by simp

/-- `restrictPair ψ x y` acts as `ψ`. -/
@[simp]
theorem coe_restrictPair (ψ : V ≃ V') (x y : V) (v : {v // v ≠ x ∧ v ≠ y}) :
    (restrictPair ψ x y v : V') = ψ v :=
  rfl

section Mismatch

variable [Fintype V] [DecidableEq V']

/-- `D(φ; M, M') = #{v | φ (M v) ≠ M' (φ v)}`. It is twice the number of edges of `M` that `φ`
does not carry to edges of `M'`, and it vanishes iff `φ` carries `M` onto `M'`. -/
def mismatch (φ : V ≃ V') (M : PerfectMatching V) (M' : PerfectMatching V') : ℕ :=
  #{v | φ (M.mate v) ≠ M'.mate (φ v)}

/-- The relabelling count `b = #{v | ψ v ≠ φ v}` of a step whose identification `ψ` (the paper's
`φ̂_t`) replaces `φ`. -/
def reidCount (φ ψ : V ≃ V') : ℕ :=
  #{v | ψ v ≠ φ v}

variable [DecidableEq V]

/-- The mismatch after chain 1 steps at `(x, y)` and chain 2 at `(ψ x, ψ y)`, under the new
identification `ψ` restricted to `V ∖ {x, y}`, counted on `V`. -/
def contractMismatch (ψ : V ≃ V') (M : PerfectMatching V) (M' : PerfectMatching V') (x y : V) :
    ℕ :=
  #{v | v ≠ x ∧ v ≠ y ∧ ψ (edgeContractFun M x y v) ≠ edgeContractFun M' (ψ x) (ψ y) (ψ v)}

/-- `contractMismatch` is the mismatch of the contracted matchings `M / xy` and
`M' / (ψ x)(ψ y)` under the restricted identification. -/
theorem mismatch_contractEdge (ψ : V ≃ V') (M : PerfectMatching V) (M' : PerfectMatching V')
    {x y : V} (hxy : x ≠ y) (hy : y ≠ M.mate x) (hy' : ψ y ≠ M'.mate (ψ x)) :
    mismatch (restrictPair ψ x y) (contractEdge M hxy hy)
      (contractEdge M' (ψ.injective.ne hxy) hy') = contractMismatch ψ M M' x y := by
  rw [mismatch, contractMismatch]
  refine Finset.card_bij (fun v _ ↦ v.1) (fun v hv ↦ ?_) (fun v _ w _ h ↦ Subtype.ext h)
    (fun v hv ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and, ne_eq, Subtype.ext_iff, coe_restrictPair,
      coe_contractEdge_mate] at hv ⊢
    exact ⟨v.2.1, v.2.2, hv⟩
  · simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨⟨v, hv.1, hv.2.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and, ne_eq, Subtype.ext_iff, coe_restrictPair,
      coe_contractEdge_mate]
    exact hv.2.2

end Mismatch

section Step

variable [DecidableEq V]

/-- `κ(y)`, the number of common edges that a common step at `(x, y)` creates in the pair
`(M, N)`. Along the alternating cycle of `M ∪ N` through `x`, starting with the `M`-edge, the
three terms are position `2` on a `4`-cycle, position `3`, and position `2σ - 3` on a
`2σ`-cycle. On a `6`-cycle the last two coincide and `κ = 2`. -/
def created (M N : PerfectMatching V) (x y : V) : ℕ :=
  (if y = N.mate (M.mate x) ∧ M.mate y = N.mate x then 1 else 0) +
    (if y = M.mate (N.mate (M.mate x)) then 1 else 0) +
    (if y = N.mate (M.mate (N.mate x)) then 1 else 0)

/-- The mismatch that a common step at `(x, y)` loses in the pair `(M, N)`: `2` if `x` and `y`
are both mismatched, plus `2 κ(y)`. -/
def stepLoss (M N : PerfectMatching V) (x y : V) : ℕ :=
  2 * (if M.mate x ≠ N.mate x ∧ M.mate y ≠ N.mate y then 1 else 0) + 2 * created M N x y

/-- The paper's `dec(y)`: `stepLoss` for `y ≠ N x`, and `0` at `y = N x`, where no common step
exists. -/
def stepDec (M N : PerfectMatching V) (x y : V) : ℕ :=
  if y = N.mate x then 0 else stepLoss M N x y

/-- `κ(y)` in terms of partners: `[N y = M x ∧ M y = N x] + [M y = N M x] + [N y = M N x]`. -/
theorem created_eq (M N : PerfectMatching V) (x y : V) :
    created M N x y =
      (if N.mate y = M.mate x ∧ M.mate y = N.mate x then 1 else 0) +
        (if M.mate y = N.mate (M.mate x) then 1 else 0) +
        (if N.mate y = M.mate (N.mate x) then 1 else 0) := by
  simp only [created, N.eq_mate_iff, M.eq_mate_iff]

variable [Fintype V] {x y : V}

/-- **Lemma 1 of `results/coupling-obstruction.md` (COD-211), exact form.** A common step at
`(x, y)`, with `y ≠ x, M x, N x`, contracts both `M` and `N` along `xy` and loses exactly
`stepLoss M N x y` mismatched vertices. This is why a uniform partner cannot lower the mismatch
density: the loss is `2` only when `y` is mismatched, plus at most `4` from created common
edges. -/
theorem card_mismatch_eq_add (M N : PerfectMatching V) (hxy : x ≠ y) (hyM : y ≠ M.mate x)
    (hyN : y ≠ N.mate x) :
    #{v | M.mate v ≠ N.mate v} =
      #{v | v ≠ x ∧ v ≠ y ∧ edgeContractFun M x y v ≠ edgeContractFun N x y v} +
        stepLoss M N x y := by
  set g : V → ℤ := fun v ↦ (if M.mate v ≠ N.mate v then 1 else 0) -
    (if v ≠ x ∧ v ≠ y ∧ edgeContractFun M x y v ≠ edgeContractFun N x y v then 1 else 0) with hg
  have hT : ∀ T : Finset V, x ∈ T → y ∈ T → M.mate x ∈ T → M.mate y ∈ T → N.mate x ∈ T →
      N.mate y ∈ T → (#{v | M.mate v ≠ N.mate v} : ℤ) =
        #{v | v ≠ x ∧ v ≠ y ∧ edgeContractFun M x y v ≠ edgeContractFun N x y v} +
          ∑ v ∈ T, g v := by
    intro T h1 h2 h3 h4 h5 h6
    have hzero : ∀ v ∈ univ, v ∉ T → g v = 0 := by
      intro v _ hv
      have e1 : v ≠ x := fun h ↦ hv (h ▸ h1)
      have e2 : v ≠ y := fun h ↦ hv (h ▸ h2)
      have e3 : v ≠ M.mate x := fun h ↦ hv (h ▸ h3)
      have e4 : v ≠ M.mate y := fun h ↦ hv (h ▸ h4)
      have e5 : v ≠ N.mate x := fun h ↦ hv (h ▸ h5)
      have e6 : v ≠ N.mate y := fun h ↦ hv (h ▸ h6)
      simp [hg, edgeContractFun_of_ne e3 e4, edgeContractFun_of_ne e5 e6, e1, e2]
    rw [sum_subset (subset_univ T) hzero, hg, sum_sub_distrib, natCast_card_filter,
      natCast_card_filter]
    ring
  have hax : M.mate x ≠ x := M.mate_ne x
  have hcx : N.mate x ≠ x := N.mate_ne x
  have hby : M.mate y ≠ y := M.mate_ne y
  have hdy : N.mate y ≠ y := N.mate_ne y
  have hay : M.mate x ≠ y := fun h ↦ hyM h.symm
  have hcy : N.mate x ≠ y := fun h ↦ hyN h.symm
  have hbx : M.mate y ≠ x := fun h ↦ hyM (M.eq_mate_iff.2 h)
  have hdx : N.mate y ≠ x := fun h ↦ hyN (N.eq_mate_iff.2 h)
  have hab : M.mate x ≠ M.mate y := M.mate.injective.ne hxy
  have hcd : N.mate x ≠ N.mate y := N.mate.injective.ne hxy
  have gx : g x = if M.mate x ≠ N.mate x then 1 else 0 := by simp [hg]
  have gy : g y = if M.mate y ≠ N.mate y then 1 else 0 := by simp [hg]
  have ga : g (M.mate x) = (if M.mate x ≠ N.mate x then 1 else 0) -
      (if M.mate y ≠ edgeContractFun N x y (M.mate x) then 1 else 0) := by
    have e : x = N.mate (M.mate x) ↔ M.mate x = N.mate x := by rw [N.eq_mate_iff, eq_comm]
    simp [hg, e, hax, hay]
  have gb : g (M.mate y) = (if M.mate y ≠ N.mate y then 1 else 0) -
      (if M.mate x ≠ edgeContractFun N x y (M.mate y) then 1 else 0) := by
    have e : y = N.mate (M.mate y) ↔ M.mate y = N.mate y := by rw [N.eq_mate_iff, eq_comm]
    simp [hg, e, hbx, hby, edgeContractFun_mate_right hxy]
  have gc : g (N.mate x) = (if M.mate x ≠ N.mate x then 1 else 0) -
      (if edgeContractFun M x y (N.mate x) ≠ N.mate y then 1 else 0) := by
    have e : M.mate (N.mate x) = x ↔ M.mate x = N.mate x := by rw [← M.eq_mate_iff, eq_comm]
    simp [hg, e, hcx, hcy]
  have gd : g (N.mate y) = (if M.mate y ≠ N.mate y then 1 else 0) -
      (if edgeContractFun M x y (N.mate y) ≠ N.mate x then 1 else 0) := by
    have e : M.mate (N.mate y) = y ↔ M.mate y = N.mate y := by rw [← M.eq_mate_iff, eq_comm]
    simp [hg, e, hdx, hdy, edgeContractFun_mate_right hxy]
  zify
  rw [stepLoss, created_eq]
  by_cases hac : M.mate x = N.mate x
  · have hMNx : M.mate (N.mate x) = x := by rw [← hac, mate_mate]
    by_cases hbd : M.mate y = N.mate y
    · rw [hT {x, y, M.mate x, M.mate y} (by simp) (by simp) (by simp) (by simp) (by simp [← hac])
        (by simp [← hbd])]
      rw [sum_insert (by simp [hxy, hax.symm, hbx.symm]), sum_insert (by simp [hay.symm, hby.symm]),
        sum_insert (by simp [hab]), sum_singleton, gx, gy, ga, gb]
      simp [edgeContractFun, hac, hbd, hMNx, hxy.symm, hdx]
    · have hbc : M.mate y ≠ N.mate x := fun h ↦ hab (hac.trans h.symm)
      have had : M.mate x ≠ N.mate y := fun h ↦ hcd (hac.symm.trans h)
      have f2 : M.mate (N.mate y) ≠ N.mate x := fun h ↦ hdx (by rw [← hMNx, ← h, mate_mate])
      rw [hT {x, y, M.mate x, M.mate y, N.mate y} (by simp) (by simp) (by simp) (by simp)
        (by simp [← hac]) (by simp)]
      rw [sum_insert (by simp [hxy, hax.symm, hbx.symm, hdx.symm]),
        sum_insert (by simp [hay.symm, hby.symm, hdy.symm]), sum_insert (by simp [hab, had]),
        sum_insert (by simp [hbd]), sum_singleton, gx, gy, ga, gb, gd]
      simp [edgeContractFun, hac, hbd, hbc, f2, hMNx, hcd.symm, hdx, hbx, hbx.symm, Ne.symm hbd]
  · by_cases hbd : M.mate y = N.mate y
    · have hbc : M.mate y ≠ N.mate x := fun h ↦ hcd (h.symm.trans hbd)
      have had : M.mate x ≠ N.mate y := fun h ↦ hab (h.trans hbd.symm)
      have f2 : M.mate (N.mate x) ≠ N.mate y := fun h ↦ hcy (by rw [← M.mate_mate (N.mate x), h,
        ← hbd, mate_mate])
      rw [hT {x, y, M.mate x, M.mate y, N.mate x} (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp [← hbd])]
      rw [sum_insert (by simp [hxy, hax.symm, hbx.symm, hcx.symm]),
        sum_insert (by simp [hay.symm, hby.symm, hcy.symm]), sum_insert (by simp [hab, hac]),
        sum_insert (by simp [hbc]), sum_singleton, gx, gy, ga, gb, gc]
      simp [edgeContractFun, hac, hbd, had, had.symm, Ne.symm hac, f2, f2.symm, hxy, hxy.symm, hyM]
    · by_cases had : M.mate x = N.mate y
      · by_cases hbc : M.mate y = N.mate x
        · have hMNx : M.mate (N.mate x) = y := by rw [← hbc, mate_mate]
          rw [hT {x, y, M.mate x, M.mate y} (by simp) (by simp) (by simp) (by simp)
            (by simp [← hbc]) (by simp [← had])]
          rw [sum_insert (by simp [hxy, hax.symm, hbx.symm]),
            sum_insert (by simp [hay.symm, hby.symm]), sum_insert (by simp [hab]), sum_singleton,
            gx, gy, ga, gb]
          simp [edgeContractFun, hbc, had, hMNx, hxy, hxy.symm, hcy, hdy]
        · have f2 : M.mate (N.mate x) ≠ N.mate y := fun h ↦ hcx (by
            rw [← M.mate_mate (N.mate x), h, ← had, mate_mate])
          rw [hT {x, y, M.mate x, M.mate y, N.mate x} (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp [← had])]
          rw [sum_insert (by simp [hxy, hax.symm, hbx.symm, hcx.symm]),
            sum_insert (by simp [hay.symm, hby.symm, hcy.symm]), sum_insert (by simp [hab, hac]),
            sum_insert (by simp [hbc]), sum_singleton, gx, gy, ga, gb, gc]
          simp [edgeContractFun, hbd, hbc, had, Ne.symm hbc, f2, f2.symm, hby.symm, hxy, hxy.symm,
            hby]
      · by_cases hbc : M.mate y = N.mate x
        · have hMNx : M.mate (N.mate x) = y := by rw [← hbc, mate_mate]
          have f2 : M.mate (N.mate y) ≠ N.mate x := fun h ↦ hdy (by
            rw [← M.mate_mate (N.mate y), h, ← hbc, mate_mate])
          rw [hT {x, y, M.mate x, M.mate y, N.mate y} (by simp) (by simp) (by simp) (by simp)
            (by simp [← hbc]) (by simp)]
          rw [sum_insert (by simp [hxy, hax.symm, hbx.symm, hdx.symm]),
            sum_insert (by simp [hay.symm, hby.symm, hdy.symm]), sum_insert (by simp [hab, had]),
            sum_insert (by simp [hbd]), sum_singleton, gx, gy, ga, gb, gd]
          simp [edgeContractFun, hac, hbc, had, Ne.symm had, f2, hMNx, hxy, hxy.symm, hax.symm,
            hdy]
        · have e1 : M.mate x = N.mate (M.mate y) ↔ M.mate y = N.mate (M.mate x) := by
            rw [N.eq_mate_iff, eq_comm]
          have e2 : M.mate (N.mate y) = N.mate x ↔ N.mate y = M.mate (N.mate x) :=
            M.eq_mate_iff.symm
          rw [hT {x, y, M.mate x, M.mate y, N.mate x, N.mate y} (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp)]
          rw [sum_insert (by simp [hxy, hax.symm, hbx.symm, hcx.symm, hdx.symm]),
            sum_insert (by simp [hay.symm, hby.symm, hcy.symm, hdy.symm]),
            sum_insert (by simp [hab, hac, had]), sum_insert (by simp [hbc, hbd]),
            sum_insert (by simp [hcd]), sum_singleton, gx, gy, ga, gb, gc, gd]
          have e3 : M.mate (N.mate x) = N.mate y ↔ N.mate y = M.mate (N.mate x) := eq_comm
          simp only [edgeContractFun, hac, hbd, hbc, had, Ne.symm hac, Ne.symm had, Ne.symm hbd,
            Ne.symm hbc, ↓reduceIte, ne_eq, not_false_eq_true, e1, e2, e3, false_and]
          by_cases hP : M.mate y = N.mate (M.mate x) <;>
            by_cases hQ : N.mate y = M.mate (N.mate x) <;> simp [hP, hQ]

omit [Fintype V] in
/-- A step loses at most `6` mismatched vertices, since `κ(y) ≤ 2`. -/
theorem stepLoss_le_six (M N : PerfectMatching V) (x y : V) : stepLoss M N x y ≤ 6 := by
  have hk : created M N x y ≤ 2 := by
    unfold created
    by_cases h : y = N.mate (M.mate x)
    · have h2 : y ≠ M.mate (N.mate (M.mate x)) := by
        rw [← h]
        exact (M.mate_ne y).symm
      have h3 : y ≠ N.mate (M.mate (N.mate x)) := fun h3 ↦ N.mate_ne x
        (M.mate.injective (N.mate.injective (h.symm.trans h3))).symm
      simp [h2, h3]
      split_ifs <;> omega
    · simp only [h, false_and, ↓reduceIte, zero_add]
      split_ifs <;> omega
  unfold stepLoss
  split_ifs <;> omega

/-- **The counting half of Lemma 2 of `results/coupling-obstruction.md` (COD-211).** For every set
`A` of admissible partners avoiding `x` and `M x`, `∑_{y ∈ A} dec(y) ≤ 2 D`. A uniform partner
therefore loses on average at most `2 D / |A|`, about the fraction `1 / j` of `D` that matches the
`2` of `2j` vertices a step removes, so the mismatch density does not fall. -/
theorem sum_stepDec_le (M N : PerfectMatching V) (A : Finset V) (hxA : x ∉ A)
    (hMxA : M.mate x ∉ A) : ∑ y ∈ A, stepDec M N x y ≤ 2 * #{v | M.mate v ≠ N.mate v} := by
  by_cases hac : M.mate x = N.mate x
  · have hMNx : M.mate (N.mate x) = x := by rw [← hac, mate_mate]
    rw [sum_eq_zero fun y hy ↦ ?_]
    · exact Nat.zero_le _
    have hyx : y ≠ x := fun h ↦ hxA (h ▸ hy)
    have hyc : y ≠ N.mate x := fun h ↦ hMxA (hac ▸ h ▸ hy)
    simp [stepDec, stepLoss, created, hac, hMNx, hyx, hyc]
  have hpt : ∀ y ∈ A, stepDec M N x y ≤
      2 * (if M.mate y ≠ N.mate y ∧ y ≠ N.mate x then 1 else 0) +
        2 * ((if y = N.mate (M.mate x) then 1 else 0) +
          (if y = M.mate (N.mate (M.mate x)) then 1 else 0) +
          (if y = N.mate (M.mate (N.mate x)) then 1 else 0)) := by
    intro y _
    by_cases hyc : y = N.mate x
    · simp [stepDec, hyc]
    simp only [stepDec, hyc, ↓reduceIte, stepLoss, created]
    have h1 : (if y = N.mate (M.mate x) ∧ M.mate y = N.mate x then 1 else 0) ≤
        (if y = N.mate (M.mate x) then 1 else 0) := by
      split_ifs <;> simp_all
    simp only [hac, hyc, ne_eq, not_false_eq_true, true_and, and_true]
    omega
  have hcard : #{y ∈ A | M.mate y ≠ N.mate y ∧ y ≠ N.mate x} + 3 ≤
      #{v | M.mate v ≠ N.mate v} := by
    have hax : M.mate x ≠ x := M.mate_ne x
    have hcx : N.mate x ≠ x := N.mate_ne x
    have h3 : #({x, M.mate x, N.mate x} : Finset V) = 3 := by
      rw [card_insert_of_notMem (by simp [hax.symm, hcx.symm]), card_pair hac]
    rw [← h3, ← card_union_of_disjoint]
    · refine card_le_card fun v hv ↦ ?_
      simp only [mem_union, mem_filter, mem_insert, mem_singleton, mem_univ, true_and] at hv ⊢
      rcases hv with ⟨_, h, _⟩ | rfl | rfl | rfl
      · exact h
      · exact hac
      · rw [mate_mate]
        exact fun h ↦ hac (by rw [N.eq_mate_iff.1 h])
      · rw [mate_mate]
        exact fun h ↦ hac (M.eq_mate_iff.2 h).symm
    · rw [disjoint_left]
      intro v hv
      simp only [mem_filter, mem_insert, mem_singleton] at hv ⊢
      rintro (rfl | rfl | rfl)
      · exact hxA hv.1
      · exact hMxA hv.1
      · exact hv.2.2 rfl
  calc ∑ y ∈ A, stepDec M N x y
      ≤ ∑ y ∈ A, (2 * (if M.mate y ≠ N.mate y ∧ y ≠ N.mate x then 1 else 0) +
          2 * ((if y = N.mate (M.mate x) then 1 else 0) +
            (if y = M.mate (N.mate (M.mate x)) then 1 else 0) +
            (if y = N.mate (M.mate (N.mate x)) then 1 else 0))) := sum_le_sum hpt
    _ ≤ 2 * #{y ∈ A | M.mate y ≠ N.mate y ∧ y ≠ N.mate x} + 2 * (1 + 1 + 1) := by
      simp only [sum_add_distrib, ← mul_sum, card_filter, sum_ite_eq']
      gcongr <;> split_ifs <;> simp
    _ ≤ 2 * #{v | M.mate v ≠ N.mate v} := by omega

end Step

section Relabel

variable [Fintype V] [DecidableEq V']

/-- Relabelling `b` vertices changes the mismatch by at most `2 b`: the status of `v` depends only
on the images of `v` and `M v`. -/
theorem mismatch_le_mismatch_add_reidCount (φ ψ : V ≃ V') (M : PerfectMatching V)
    (M' : PerfectMatching V') : mismatch φ M M' ≤ mismatch ψ M M' + 2 * reidCount φ ψ := by
  classical
  have hsub : ({v | φ (M.mate v) ≠ M'.mate (φ v)} : Finset V) ⊆
      ({v | ψ (M.mate v) ≠ M'.mate (ψ v)} : Finset V) ∪
        (({v | ψ v ≠ φ v} : Finset V) ∪ ({v | ψ (M.mate v) ≠ φ (M.mate v)} : Finset V)) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hv (by rw [← h.2.2, ← h.2.1]; exact h.1)
  have hB : #({v | ψ (M.mate v) ≠ φ (M.mate v)} : Finset V) = reidCount φ ψ :=
    card_equiv M.mate fun v ↦ by simp
  rw [mismatch, mismatch, reidCount]
  rw [reidCount] at hB
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (card_union_le _ _) _
    _ = _ := by rw [hB]; ring

/-- `b = 0` exactly for a common step. -/
theorem reidCount_eq_zero_iff (φ ψ : V ≃ V') : reidCount φ ψ = 0 ↔ ψ = φ := by
  simp [reidCount, Equiv.ext_iff, filter_eq_empty_iff]

/-- `b ≠ 1`: two bijections cannot differ at exactly one point. -/
theorem reidCount_ne_one (φ ψ : V ≃ V') : reidCount φ ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := card_eq_one.mp h
  have hmem : ∀ u, ψ u ≠ φ u ↔ u = v := fun u ↦ by
    simpa using congrArg (u ∈ ·) hv
  have hv' := (hmem v).2 rfl
  have hu : φ (φ.symm (ψ v)) = ψ v := φ.apply_symm_apply _
  by_cases huv : φ.symm (ψ v) = v
  · exact hv' (by rw [← hu, huv])
  · have h' : ψ (φ.symm (ψ v)) = φ (φ.symm (ψ v)) := by
      by_contra h''
      exact huv ((hmem _).1 h'')
    exact huv (ψ.injective (h'.trans hu))

variable [DecidableEq V]

/-- On one vertex set, `D(φ; M, M')` counts the disagreements of `M` and `N = φ⁻¹ M' φ`. -/
theorem mismatch_eq_card (φ : V ≃ V') (M : PerfectMatching V) (M' : PerfectMatching V') :
    mismatch φ M M' = #{v | M.mate v ≠ (congr φ.symm M').mate v} := by
  simp [mismatch, Equiv.eq_symm_apply]

omit [Fintype V] in
/-- Contraction commutes with transport: `(φ⁻¹ M' φ) / xy = φ⁻¹ (M' / (φ x)(φ y)) φ`. -/
theorem edgeContractFun_congr (ψ : V ≃ V') (M' : PerfectMatching V')
    (x y v : V) :
    edgeContractFun (congr ψ.symm M') x y v = ψ.symm (edgeContractFun M' (ψ x) (ψ y) (ψ v)) := by
  have e : ∀ w, v = ψ.symm w ↔ ψ v = w := fun w ↦ Equiv.eq_symm_apply ψ
  simp only [edgeContractFun, congr_mate, Equiv.symm_symm, e]
  split_ifs <;> rfl

/-- On one vertex set, `contractMismatch` counts the disagreements of `M / xy` and `N / xy`. -/
theorem contractMismatch_eq_card (ψ : V ≃ V') (M : PerfectMatching V) (M' : PerfectMatching V')
    (x y : V) :
    contractMismatch ψ M M' x y = #{v | v ≠ x ∧ v ≠ y ∧
      edgeContractFun M x y v ≠ edgeContractFun (congr ψ.symm M') x y v} := by
  simp [contractMismatch, edgeContractFun_congr, Equiv.eq_symm_apply]

/-- **Lemma 1 of `results/coupling-obstruction.md` (COD-211), with the identification.** In a
common step, chain 1 at `(x, y)` and chain 2 at `(φ x, φ y)` with `φ_{t+1}` the restriction of
`φ`, the mismatch falls by exactly `stepLoss M N x y` with `N = φ⁻¹ M' φ`. -/
theorem mismatch_eq_contractMismatch_add (φ : V ≃ V') (M : PerfectMatching V)
    (M' : PerfectMatching V') {x y : V} (hxy : x ≠ y) (hyM : y ≠ M.mate x)
    (hy' : φ y ≠ M'.mate (φ x)) :
    mismatch φ M M' = contractMismatch φ M M' x y + stepLoss M (congr φ.symm M') x y := by
  rw [mismatch_eq_card, contractMismatch_eq_card]
  refine card_mismatch_eq_add M _ hxy hyM ?_
  rw [congr_mate, Equiv.symm_symm, ne_eq, Equiv.eq_symm_apply]
  exact hy'

/-- **Lemma 2 of `results/coupling-obstruction.md` (COD-211), pointwise.** Chain 1 steps at
`(x, y)` with `y ≠ x, M x`, chain 2 at `(ψ x, ψ y)` with `ψ y ≠ M' (ψ x)`, and the new
identification is `ψ` restricted, so `b = reidCount φ ψ`. Then
`D_t ≤ D_{t+1} + dec(y)·[b = 0] + 5 b`. A common step loses `dec(y)`, and any other step
loses at most `6 + 2 b ≤ 5 b`. This is the reason a labelled coupling of two `k = 3` reduction
chains cannot coalesce without paying for relabelling. -/
theorem mismatch_le_contractMismatch_add (φ ψ : V ≃ V') (M : PerfectMatching V)
    (M' : PerfectMatching V') {x y : V} (hxy : x ≠ y) (hyM : y ≠ M.mate x)
    (hy' : ψ y ≠ M'.mate (ψ x)) :
    mismatch φ M M' ≤ contractMismatch ψ M M' x y +
      (if reidCount φ ψ = 0 then stepDec M (congr φ.symm M') x y else 0) + 5 * reidCount φ ψ := by
  by_cases hb : reidCount φ ψ = 0
  · have hψ : ψ = φ := (reidCount_eq_zero_iff φ ψ).1 hb
    subst hψ
    have hyN : y ≠ (congr ψ.symm M').mate x := by
      rw [congr_mate, Equiv.symm_symm, ne_eq, Equiv.eq_symm_apply]
      exact hy'
    rw [mismatch_eq_contractMismatch_add ψ M M' hxy hyM hy']
    simp only [hb, ↓reduceIte, stepDec, hyN]
    omega
  · simp only [hb, ↓reduceIte]
    have h2 := reidCount_ne_one φ ψ
    have h1 := mismatch_le_mismatch_add_reidCount φ ψ M M'
    have h0 := mismatch_eq_contractMismatch_add ψ M M' hxy hyM hy'
    have h6 := stepLoss_le_six M (congr ψ.symm M') x y
    omega

end Relabel

section Expectation

variable [Fintype V] [DecidableEq V] [DecidableEq V'] {Ω : Type*} [Fintype Ω]

/-- **Lemma 2 of `results/coupling-obstruction.md` (COD-211).** This is the warning sign for
labelled couplings of `k = 3` reduction chains. Fix the state at time `t` and chain 1's vertex `x`.
Let `P` be the conditional law of the rest of the step on a finite outcome space `Ω`: chain 1's
partner `y ω`, uniform on a set `A` that avoids `x` and `M x` (the coupling is causal), and the
identification `ψ ω = φ_{t+1} ∪ {x ↦ x', y ↦ y'}`, with chain 2's step `(ψ ω x, ψ ω (y ω))`
admissible for `M'`. Then `E[D_t - D_{t+1}] ≤ 2 D_t / |A| + 5 E[b]`. The x-rules are arbitrary
and need not agree, so no choice of `x` lowers the mismatch except by relabelling. -/
theorem expect_mismatch_sub_le {P : Ω → ℝ} (hP : ChainRule.IsProb P) (φ : V ≃ V')
    (M : PerfectMatching V) (M' : PerfectMatching V') {x : V} {A : Finset V} (hxA : x ∉ A)
    (hMxA : M.mate x ∉ A) (y : Ω → V) (ψ : Ω → V ≃ V') (hyA : ∀ ω, y ω ∈ A)
    (hunif : ∀ a ∈ A, ChainRule.prob P {ω | y ω = a} = 1 / #A)
    (hψ : ∀ ω, ψ ω (y ω) ≠ M'.mate (ψ ω x)) :
    ∑ ω, P ω * ((mismatch φ M M' : ℝ) - contractMismatch (ψ ω) M M' x (y ω)) ≤
      2 * mismatch φ M M' / #A + 5 * ∑ ω, P ω * (reidCount φ (ψ ω) : ℝ) := by
  have hpt : ∀ ω, (mismatch φ M M' : ℝ) - contractMismatch (ψ ω) M M' x (y ω) ≤
      stepDec M (congr φ.symm M') x (y ω) + 5 * (reidCount φ (ψ ω) : ℝ) := by
    intro ω
    have hxy : x ≠ y ω := fun h ↦ hxA (h ▸ hyA ω)
    have hyM : y ω ≠ M.mate x := fun h ↦ hMxA (h ▸ hyA ω)
    have h := mismatch_le_contractMismatch_add φ (ψ ω) M M' hxy hyM (hψ ω)
    have hif : (if reidCount φ (ψ ω) = 0 then stepDec M (congr φ.symm M') x (y ω) else 0) ≤
        stepDec M (congr φ.symm M') x (y ω) := by
      split_ifs <;> simp
    have hle : mismatch φ M M' ≤ contractMismatch (ψ ω) M M' x (y ω) +
        stepDec M (congr φ.symm M') x (y ω) + 5 * reidCount φ (ψ ω) := by
      omega
    have hcast := (Nat.cast_le (α := ℝ)).2 hle
    push_cast at hcast
    linarith
  have hfib : ∀ a ∈ A, ∑ ω ∈ univ.filter (fun ω ↦ y ω = a),
      P ω * (stepDec M (congr φ.symm M') x (y ω) : ℝ) =
        1 / #A * stepDec M (congr φ.symm M') x a := by
    intro a ha
    have hprob : ChainRule.prob P {ω | y ω = a} = ∑ ω ∈ univ.filter (fun ω ↦ y ω = a), P ω := by
      rw [ChainRule.prob, sum_filter]
      exact sum_congr rfl fun ω _ ↦ Set.indicator_apply _ _ _
    rw [← hunif a ha, hprob, sum_mul]
    exact sum_congr rfl fun ω hω ↦ by rw [(mem_filter.mp hω).2]
  have hsum : ∑ ω, P ω * (stepDec M (congr φ.symm M') x (y ω) : ℝ) =
      1 / #A * ∑ a ∈ A, (stepDec M (congr φ.symm M') x a : ℝ) := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := A) (g := y) (fun ω _ ↦ hyA ω), mul_sum]
    exact sum_congr rfl hfib
  have hdec : ∑ a ∈ A, (stepDec M (congr φ.symm M') x a : ℝ) ≤ 2 * mismatch φ M M' := by
    have h := sum_stepDec_le M (congr φ.symm M') A hxA hMxA
    rw [← mismatch_eq_card] at h
    exact_mod_cast h
  calc ∑ ω, P ω * ((mismatch φ M M' : ℝ) - contractMismatch (ψ ω) M M' x (y ω))
      ≤ ∑ ω, P ω * ((stepDec M (congr φ.symm M') x (y ω) : ℝ) + 5 * reidCount φ (ψ ω)) :=
        sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt ω) (hP.nonneg ω)
    _ = ∑ ω, P ω * (stepDec M (congr φ.symm M') x (y ω) : ℝ) +
          5 * ∑ ω, P ω * (reidCount φ (ψ ω) : ℝ) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun ω _ ↦ by ring
    _ ≤ 2 * mismatch φ M M' / #A + 5 * ∑ ω, P ω * (reidCount φ (ψ ω) : ℝ) := by
        rw [hsum, one_div_mul_eq_div]
        gcongr

/-- **Lemma 2 of `results/coupling-obstruction.md` (COD-211), in densities.** Under the
hypotheses of `expect_mismatch_sub_le`, with `|V| = 2j`, `j ≥ 3` and `|A| ≥ 2j - 4`, the mismatch
density `ρ = D / |V|` satisfies
`E[ρ_{t+1}] ≥ ρ_t (1 - δ_j) - (5/2) E[b] / (j - 1)` with `δ_j = 8 / ((2j - 2)(2j - 4))`.
Summing `δ_j` over the run gives Theorem A: a labelled causal coupling of two `k = 3` reduction
chains keeps `E[ρ]` near its start unless it relabels a positive density of vertices. -/
theorem expect_rho_ge {P : Ω → ℝ} (hP : ChainRule.IsProb P) (φ : V ≃ V')
    (M : PerfectMatching V) (M' : PerfectMatching V') {x : V} {A : Finset V} (hxA : x ∉ A)
    (hMxA : M.mate x ∉ A) (y : Ω → V) (ψ : Ω → V ≃ V') (hyA : ∀ ω, y ω ∈ A)
    (hunif : ∀ a ∈ A, ChainRule.prob P {ω | y ω = a} = 1 / #A)
    (hψ : ∀ ω, ψ ω (y ω) ≠ M'.mate (ψ ω x)) {j : ℕ} (hj : 3 ≤ j)
    (hV : Fintype.card V = 2 * j) (hA : 2 * j - 4 ≤ #A) :
    (mismatch φ M M' / Fintype.card V : ℝ) * (1 - 8 / ((2 * j - 2) * (2 * j - 4))) -
        5 / 2 * (∑ ω, P ω * (reidCount φ (ψ ω) : ℝ)) / (j - 1) ≤
      ∑ ω, P ω * (contractMismatch (ψ ω) M M' x (y ω) / (Fintype.card V - 2 : ℝ)) := by
  have h := expect_mismatch_sub_le hP φ M M' hxA hMxA y ψ hyA hunif hψ
  set D : ℝ := (mismatch φ M M' : ℝ)
  set B : ℝ := ∑ ω, P ω * (reidCount φ (ψ ω) : ℝ)
  set E : ℝ := ∑ ω, P ω * (contractMismatch (ψ ω) M M' x (y ω) : ℝ) with hEdef
  have hDE : ∑ ω, P ω * (D - contractMismatch (ψ ω) M M' x (y ω)) = D - E := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP.sum_eq_one, one_mul, E]
  rw [hDE] at h
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hA' : (2 * j - 4 : ℝ) ≤ #A := by
    have h1 : 2 * j ≤ #A + 4 := by omega
    have h2 : (2 * j : ℝ) ≤ #A + 4 := by exact_mod_cast h1
    linarith
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have h2 : 2 * D / #A ≤ 2 * D / (2 * j - 4) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hA'
  have hE : ∑ ω, P ω * (contractMismatch (ψ ω) M M' x (y ω) / (Fintype.card V - 2 : ℝ)) =
      E / (2 * j - 2) := by
    rw [hV, hEdef, div_eq_mul_inv, sum_mul]
    push_cast
    exact sum_congr rfl fun ω _ ↦ by ring
  have key : D / (2 * j) * (1 - 8 / ((2 * j - 2) * (2 * j - 4))) - 5 / 2 * B / (j - 1) =
      (D - 2 * D / (2 * j - 4) - 5 * B) / (2 * j - 2) := by
    have h4 : (2 * j - 4 : ℝ) ≠ 0 := by linarith
    have h3 : (j - 1 : ℝ) ≠ 0 := by linarith
    have h5 : (2 * j - 2 : ℝ) ≠ 0 := by linarith
    have h6 : (j : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [hE, hV]
  push_cast
  rw [key]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

end Expectation

end PerfectMatching

end Pairing
