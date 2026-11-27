import Repair.ExceptionalSix
import Clifford.PolarSection
import Clifford.PolarSectionAGL

/-!
# The Witt bridge at `m = 6` (COD-259)

On `V_6 = ℤ/11 ∪ {∞}`, let `W` be the CKN fingerprint module with its nondegenerate form
`fpForm`, `⟨φ(P), φ(Q)⟩ = H[P, Q]` (`clifford/Clifford/PolarSection.lean`, ham-spin 55c17eb).

* `Z_6` is the set of 22 zero states `PSL211.zeroState` (`repair/Repair/ExceptionalSix.lean`,
  main 8f9dbf0), and `R = span φ(Z_6) = fpSpan zeroState`.
* `P_c = {0 ∞} ∪ {{x, c x} : x a nonzero square}` for a nonsquare `c` (`pTwo`, `pSix`, `pSeven`,
  `pEight`, `pBase_mate`). `O_7` is the `AGL(1, 11)`-orbit of `P_7`, the Bamberg–Klawuhn orbit.
  `oSeven (b, s) = P_7 + s` or `P_8 + s`, with `range_oSeven` (it is the orbit) and
  `oSeven_injective` (it has 22 members). `L = span φ(O_7) = fpSpan oSeven`.

Main results (`results/witt-z11-extend.md` §4 and §6, `results/witt-z11-contra.md` §4 and §7,
both 54a0efc; the dimensions of `results/autgroup-side-effects.md` check [7], d7b3fa2).
* `finrank_zeroSpan : dim R = 10` and `finrank_oSevenSpan : dim L = 22`.
* `zeroSpan_eq_orthogonal : R = L^⊥`, `oSevenSpan_eq_orthogonal : L = R^⊥` and
  `zeroSpan_le_oSevenSpan : R ≤ L`. `zeroSpan_le_orthogonal` : `R` is totally isotropic.
* `rrSpan_le_oSevenSpan : span φ(GK_12) ≤ L`, so `rrSpan_sup_oSevenSpan` : adding `GK_12` to
  `O_7` does not change `L`.
* `wittBridge_six` : all of these together.

The certificate (`results/witt-z11-extend.md` §6, with new test data). It is translation
symmetric. `Z_6` is the two `ℤ/11`-orbits of `P_2` and `P_6 = -P_2` (`range_zSix`), and `O_7` the
two orbits of `P_7` and `P_8 = -P_7`. With `H[P + k, Q + s] = H[P, Q + (s - k)]`
(`H_shift_smul`) and `H[-P, Q + e] = H[P, -Q - e]` (`H_mu_smul_shift`), every pairing reduces to
one of 77 walk checks, each the alternating walk of `P ∪ Q` from `∞` (`walkH`, `H_eq_of_walkH`).
* `walkH_pTwo_oBase`, `walkH_pTwo_zBase` : `H[P_2, O_7] = 0` and `H[P_2, Z_6] = 0`, 22 + 22
  checks. Hence `H[Z_6, O_7] = 0` and `H[Z_6, Z_6] = 0`.
* `walkH_pTwo_testY` : `H[P_2, y + d]` for the test matching `y = testY`, 11 checks. The
  `10 × 10` block `H[P_2 + i, y + l] = c(l - i)` has the explicit inverse `rInv`, so `dim R ≥ 10`
  (`card_le_finrank_fpSpan_of_dual`).
* `walkH_pSeven_yBase` : `H[P_7, y + d]` and `H[P_7, -y + d]`, 22 checks. The `22 × 22`
  block-circulant matrix `H[P_c + s, ±y + t]` has a block-circulant inverse `lInv`, so
  `dim L ≥ 22` (`card_mul_le_finrank_of_circulant`).
* Then `dim L + dim L^⊥ = 32` (`finrank_fpSpan_add_finrank_orthogonal`) forces equality.

The test matching `y = {0 7, 1 4, 2 3, 5 10, 6 9, 8 ∞}` replaces the pair `y, y2` of
`results/witt-z11-extend.md` §6, so that `-y` serves as the second test orbit and the `P_8` rows
come from the `P_7` rows. That halves the 44 checks for `L`.
-/

namespace Pairing.RoundRobin.Canonical.WittSix

open PerfectMatching PSL211

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `⟨Σ_i c_i φ(P_i), φ(Q)⟩ = Σ_i c_i H[P_i, Q]` for the fingerprint form `fpForm` (ham-spin
55c17eb). Used for the rank certificates of `results/witt-z11-extend.md` §6 (54a0efc), whose
dimensions are those of `results/autgroup-side-effects.md` [7] (d7b3fa2). -/
theorem fpForm_sum_smul_rowW {ι : Type*} [Fintype ι] (P : ι → PerfectMatching V) (c : ι → F₂)
    (Q : PerfectMatching V) :
    fpForm (∑ i, c i • rowW (P i)) (rowW Q) = ∑ i, c i * H (P i) Q := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fpForm_rowW,
    smul_eq_mul]

/-- **Rank certificate by a dual basis.** If `A H[P, Q] = I` for a coefficient matrix `A`, then
the vectors `Σ_i A_(j i) φ(P_i)` are dual to the `φ(Q_l)`, so `dim span φ(P) ≥ |κ|`
(`fpSpan`, ham-spin 55c17eb; `results/witt-z11-extend.md` §6, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem card_le_finrank_fpSpan_of_dual {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : ι → PerfectMatching V) (Q : κ → PerfectMatching V) (A : κ → ι → F₂)
    (h : ∀ j l, ∑ i, A j i * H (P i) (Q l) = if j = l then 1 else 0) :
    Fintype.card κ ≤ Module.finrank F₂ (fpSpan P) := by
  set v : κ → W V := fun j ↦ ∑ i, A j i • rowW (P i) with hv
  have hind : LinearIndependent F₂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun x ↦ fpForm x (rowW (Q l))) hg
    simp only [hv, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fpForm_rowW, h,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      map_zero, LinearMap.zero_apply] at h1
    exact h1
  have hle : Submodule.span F₂ (Set.range v) ≤ fpSpan P := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← finrank_span_eq_card hind]
  exact Submodule.finrank_mono hle

/-- If `H[P_i, Q_j] = 0` for all `i, j`, then `span φ(P) ≤ (span φ(Q))^⊥` under `fpForm`
(ham-spin 55c17eb). This turns the checks `H[Z_6, O_7] = 0` and `H[Z_6, Z_6] = 0` of
`results/witt-z11-extend.md` §6 (54a0efc) into `R ≤ L^⊥` and `R ≤ R^⊥`, with the dimensions of
`results/autgroup-side-effects.md` [7] (d7b3fa2). -/
theorem fpSpan_le_orthogonal_of_H {ι κ : Type*} (P : ι → PerfectMatching V)
    (Q : κ → PerfectMatching V) (h : ∀ i j, H (P i) (Q j) = 0) :
    fpSpan P ≤ fpForm.orthogonal (fpSpan Q) := by
  rw [fpSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_orthogonal_fpSpan_iff]
  exact fun j ↦ h i j

/-- Two families with the same set of matchings have the same fingerprint span (`fpSpan`,
ham-spin 55c17eb). Used for `Z_6` as two translation orbits (`results/witt-z11-extend.md` §6,
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem fpSpan_eq_of_range_eq {ι κ : Type*} {P : ι → PerfectMatching V}
    {Q : κ → PerfectMatching V} (h : Set.range P = Set.range Q) : fpSpan P = fpSpan Q := by
  change Submodule.span F₂ (Set.range (rowW ∘ P)) = Submodule.span F₂ (Set.range (rowW ∘ Q))
  rw [Set.range_comp, Set.range_comp, h]

end General

section Symmetry

/-- `(v ↦ v + k)⁻¹ (v ↦ v + s) = (v ↦ v + (s - k))` on `V_6` (`shift`, ham-spin 55c17eb;
`results/witt-z11-extend.md` §6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem shift_inv_mul_shift (k s : ZMod (2 * 6 - 1)) :
    (shift 6 k)⁻¹ * shift 6 s = shift 6 (s - k) := by
  refine Equiv.ext fun v ↦ ?_
  rcases v with _ | x
  · rfl
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, shift_some, shift_inv_some]
    congr 1
    ring

/-- **Translation invariance.** `H[P + k, Q + s] = H[P, Q + (s - k)]` (`H_smul`, `shift`,
ham-spin 55c17eb; `results/witt-z11-extend.md` §6, 54a0efc; `results/autgroup-side-effects.md`
[7], d7b3fa2). -/
theorem H_shift_smul (k s : ZMod (2 * 6 - 1)) (P Q : PerfectMatching (Vertex 6)) :
    H (shift 6 k • P) (shift 6 s • Q) = H P (shift 6 (s - k) • Q) := by
  rw [← H_smul (shift 6 k)⁻¹, inv_smul_smul, smul_smul, shift_inv_mul_shift]

/-- `a (v + s) = a v + a s`, as permutations of `V_6` (`scale`, `shift`, ham-spin 55c17eb;
`results/witt-z11-extend.md` §3, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem scale_mul_shift (a : (ZMod (2 * 6 - 1))ˣ) (s : ZMod (2 * 6 - 1)) :
    scale 6 a * shift 6 s = shift 6 (a * s) * scale 6 a := by
  refine Equiv.ext fun v ↦ ?_
  rcases v with _ | x
  · rfl
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, shift_some, scale_some]
    congr 1
    ring

/-- The scaling by `1` is the identity (`scale`, ham-spin 55c17eb; `results/witt-z11-extend.md`
§3, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem scale_one : scale 6 1 = 1 := by
  refine Equiv.ext fun v ↦ ?_
  rcases v with _ | x
  · rfl
  · rw [Equiv.Perm.one_apply, scale_some, Units.val_one, one_mul]

/-- The multiplier `m_(-1) : v ↦ -v` of `V_6`, fixing `∞` (`scale`, ham-spin 55c17eb;
`results/witt-z11-extend.md` §3, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def mu : Equiv.Perm (Vertex 6) :=
  scale 6 (-1)

/-- `m_(-1)` is an involution (`results/witt-z11-extend.md` §3, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem mu_mul_mu : mu * mu = 1 := by
  refine Equiv.ext fun v ↦ ?_
  rcases v with _ | x
  · rfl
  · rw [Equiv.Perm.one_apply, Equiv.Perm.mul_apply, mu, scale_some, scale_some, ← mul_assoc,
      ← Units.val_mul, neg_one_mul, neg_neg, Units.val_one, one_mul]

/-- `-(v + s) = -v - s`, as permutations of `V_6` (`results/witt-z11-extend.md` §3, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem mu_mul_shift (s : ZMod (2 * 6 - 1)) : mu * shift 6 s = shift 6 (-s) * mu := by
  rw [mu, scale_mul_shift, Units.val_neg, Units.val_one, neg_one_mul]

/-- **The multiplier `m_(-1)`.** `H[-P, Q + e] = H[P, -Q - e]` (`H_smul`, ham-spin 55c17eb;
`results/witt-z11-extend.md` §3 and §6, 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
theorem H_mu_smul_shift (P Q : PerfectMatching (Vertex 6)) (e : ZMod (2 * 6 - 1)) :
    H (mu • P) (shift 6 e • Q) = H P (shift 6 (-e) • mu • Q) := by
  conv_lhs => rw [← H_smul mu (mu • P), smul_smul mu mu, mu_mul_mu, one_smul, smul_smul,
    mu_mul_shift, mul_smul]

end Symmetry

section Walk

/-- `H[P, Q]` read off the alternating walk of `P ∪ Q` from `∞` with `6` steps of each matching:
`1` if it visits every vertex, `0` if it closes early, and `none` otherwise (`altWalk`,
`ClosedMiss`, `repair/Repair/Covering/Witness.lean`, main 8f9dbf0). One evaluation is one walk
check of `results/witt-z11-extend.md` §6 (54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
def walkH (p q : Vertex 6 → Vertex 6) : Option F₂ :=
  if ∀ w, w ∈ Covering.altWalk p q 6 none then some 1
  else if Covering.ClosedMiss p q (Covering.altWalk p q 6 none) then some 0 else none

/-- A walk check is sound: `walkH P Q = some b` gives `H[P, Q] = b` (`ham_of_altWalk`,
`not_ham_of_closedMiss`, main 8f9dbf0; `results/witt-z11-extend.md` §6, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem H_eq_of_walkH {P Q : PerfectMatching (Vertex 6)} {b : F₂}
    (h : walkH P.mate Q.mate = some b) : H P Q = b := by
  unfold walkH at h
  split_ifs at h with h1 h2
  · cases h
    simp [H_apply, Covering.ham_of_altWalk P Q 6 none h1]
  · cases h
    simp [H_apply, Covering.not_ham_of_closedMiss P Q (Covering.mem_altWalk_self _ _ _ _) h2]

end Walk

section Matchings

/-- The partner function of `P_c = {0 ∞} ∪ {{x, c x} : x ∈ {1, 3, 4, 5, 9}}`, with label `11 = ∞`
(`natPairs`, main 8f9dbf0; `results/witt-z11-contra.md` §1, 54a0efc; `scripts/agse-m6.py` and
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def pcMate (c : ℕ) : Vertex 6 → Vertex 6 :=
  Covering.Witness.natPairs 6 ((0, 11) :: [1, 3, 4, 5, 9].map fun x ↦ (x, c * x % 11))

/-- `P_2`, the base point of `Z_6` (`results/witt-z11-extend.md` §2, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def pTwo : PerfectMatching (Vertex 6) :=
  Covering.mkMatching (pcMate 2) (by decide +kernel) (by decide +kernel)

/-- `P_6 = -P_2`, the base point of the second `ℤ/11`-orbit of `Z_6`
(`results/witt-z11-extend.md` §2, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def pSix : PerfectMatching (Vertex 6) :=
  Covering.mkMatching (pcMate 6) (by decide +kernel) (by decide +kernel)

/-- `P_7`, the base point of the Bamberg–Klawuhn orbit `O_7` (`results/witt-z11-contra.md` §1,
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def pSeven : PerfectMatching (Vertex 6) :=
  Covering.mkMatching (pcMate 7) (by decide +kernel) (by decide +kernel)

/-- `P_8 = -P_7`, the base point of the second `ℤ/11`-orbit of `O_7`
(`results/witt-z11-contra.md` §1, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def pEight : PerfectMatching (Vertex 6) :=
  Covering.mkMatching (pcMate 8) (by decide +kernel) (by decide +kernel)

/-- `{1, 3, 4, 5, 9}` are the nonzero squares mod `11`, and `P_c` pairs `∞` with `0` and each
nonzero square `x` with `c x`, for `c = 2, 6, 7, 8` (`results/witt-z11-contra.md` §1, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem pBase_mate :
    (∀ x : ZMod (2 * 6 - 1), (∃ r, r ≠ 0 ∧ r * r = x) ↔ x ∈ ({1, 3, 4, 5, 9} : Finset _)) ∧
      pTwo.mate none = some 0 ∧ pSix.mate none = some 0 ∧ pSeven.mate none = some 0 ∧
      pEight.mate none = some 0 ∧ ∀ x ∈ ({1, 3, 4, 5, 9} : Finset (ZMod (2 * 6 - 1))),
        pTwo.mate (some x) = some (2 * x) ∧ pSix.mate (some x) = some (6 * x) ∧
          pSeven.mate (some x) = some (7 * x) ∧ pEight.mate (some x) = some (8 * x) := by
  decide +kernel

/-- `P_2` is the listed zero state `zeroState 20` and `P_6` is `zeroState 21`
(`repair/Repair/ExceptionalSix.lean`, main 8f9dbf0; `results/witt-z11-extend.md` §2, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem pTwo_eq_zeroState : pTwo = zeroState 20 ∧ pSix = zeroState 21 := by
  decide +kernel

/-- The base points `P_2` (`false`) and `P_6` (`true`) of `Z_6` (`results/witt-z11-extend.md`
§6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def zBase (b : Bool) : PerfectMatching (Vertex 6) :=
  bif b then pSix else pTwo

/-- The base points `P_7` (`false`) and `P_8` (`true`) of `O_7` (`results/witt-z11-extend.md`
§6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def oBase (b : Bool) : PerfectMatching (Vertex 6) :=
  bif b then pEight else pSeven

/-- `Z_6` as two translation orbits, `zSix (b, s) = zBase b + s` (`results/witt-z11-extend.md`
§6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def zSix (i : Bool × ZMod (2 * 6 - 1)) : PerfectMatching (Vertex 6) :=
  shift 6 i.2 • zBase i.1

/-- **`O_7`**, the Bamberg–Klawuhn orbit, `oSeven (b, s) = oBase b + s`. By `range_oSeven` it is
the `AGL(1, 11)`-orbit of `P_7` (`results/witt-z11-contra.md` §1, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def oSeven (i : Bool × ZMod (2 * 6 - 1)) : PerfectMatching (Vertex 6) :=
  shift 6 i.2 • oBase i.1

/-- `m_(-1)` swaps `P_2` and `P_6` (`results/witt-z11-extend.md` §2, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem mu_smul_zBase : ∀ b, mu • zBase b = zBase (!b) := by
  decide +kernel

/-- `m_(-1)` swaps `P_7` and `P_8` (`results/witt-z11-contra.md` §1, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem mu_smul_oBase : ∀ b, mu • oBase b = oBase (!b) := by
  decide +kernel

/-- **`Z_6` is two translation orbits.** The 22 listed zero states are the translates of `P_2`
and of `P_6` (`repair/Repair/ExceptionalSix.lean`, main 8f9dbf0; `results/witt-z11-extend.md`
Setup, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem range_zSix : Set.range zSix = Set.range zeroState := by
  have h1 : ∀ i, ∃ j, zSix i = zeroState j := by
    decide +kernel
  have h2 : ∀ j, ∃ i, zSix i = zeroState j := by
    decide +kernel
  ext P
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := h1 i
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    exact h2 j

/-- Every member of `zSix` is a zero state (`isZeroState_zeroState`, main 8f9dbf0;
`results/witt-z11-extend.md` §6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem isZeroState_zSix (i : Bool × ZMod (2 * 6 - 1)) : IsZeroState (factor 6) (zSix i) := by
  obtain ⟨j, hj⟩ : zSix i ∈ Set.range zeroState := range_zSix ▸ Set.mem_range_self i
  rw [← hj]
  exact isZeroState_zeroState j

/-- **`O_7` is the `AGL(1, 11)`-orbit of `P_7`**: the matchings `oSeven i` are exactly the images
of `P_7` under `v ↦ a v + b`. Squares fix `P_7` and nonsquares send it to `P_8`
(`results/witt-z11-contra.md` §1, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem range_oSeven : Set.range oSeven =
    Set.range fun g : (ZMod (2 * 6 - 1))ˣ × ZMod (2 * 6 - 1) ↦
      (shift 6 g.2 * scale 6 g.1) • pSeven := by
  have hs : ∀ a : (ZMod (2 * 6 - 1))ˣ,
      scale 6 a • pSeven = oBase false ∨ scale 6 a • pSeven = oBase true := by
    decide +kernel
  ext P
  constructor
  · rintro ⟨⟨b, k⟩, rfl⟩
    cases b
    · refine ⟨(1, k), ?_⟩
      change (shift 6 k * scale 6 1) • pSeven = shift 6 k • pSeven
      rw [scale_one, mul_one]
    · refine ⟨(-1, k), ?_⟩
      change (shift 6 k * mu) • oBase false = shift 6 k • oBase true
      rw [mul_smul, mu_smul_oBase]
      rfl
  · rintro ⟨⟨a, k⟩, rfl⟩
    rcases hs a with h | h
    · refine ⟨(false, k), ?_⟩
      change shift 6 k • oBase false = (shift 6 k * scale 6 a) • pSeven
      rw [mul_smul, h]
    · refine ⟨(true, k), ?_⟩
      change shift 6 k • oBase true = (shift 6 k * scale 6 a) • pSeven
      rw [mul_smul, h]

/-- **`|O_7| = 22`**: the 22 matchings `oSeven i` are distinct (`results/witt-z11-contra.md` §1,
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem oSeven_injective : Function.Injective oSeven := by
  have h : ∀ i j, (∀ v, (oSeven i).mate v = (oSeven j).mate v) → i = j := by
    decide +kernel
  exact fun i j hij ↦ h i j fun v ↦ by rw [hij]

end Matchings

section Orthogonality

/-- **Walk checks, `H[P_2, O_7] = 0`**: 22 walks (`results/witt-z11-extend.md` §6 (c), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem walkH_pTwo_oBase :
    ∀ b (d : ZMod (2 * 6 - 1)), walkH pTwo.mate (shift 6 d • oBase b).mate = some 0 := by
  decide +kernel

/-- **Walk checks, `H[P_2, Z_6] = 0`**: 22 walks (`results/witt-z11-extend.md` §6 (d), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem walkH_pTwo_zBase :
    ∀ b (d : ZMod (2 * 6 - 1)), walkH pTwo.mate (shift 6 d • zBase b).mate = some 0 := by
  decide +kernel

/-- `H[P_2 or P_6, X + d] = 0` for `X` a base point of `O_7` or of `Z_6`, from the `P_2` walks
and `m_(-1)` (`results/witt-z11-extend.md` §6, 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
theorem H_zBase_shift (b c : Bool) (d : ZMod (2 * 6 - 1)) :
    H (zBase b) (shift 6 d • oBase c) = 0 ∧ H (zBase b) (shift 6 d • zBase c) = 0 := by
  cases b
  · exact ⟨H_eq_of_walkH (walkH_pTwo_oBase c d), H_eq_of_walkH (walkH_pTwo_zBase c d)⟩
  · have e : zBase true = mu • zBase false := (mu_smul_zBase false).symm
    rw [e, H_mu_smul_shift, H_mu_smul_shift, mu_smul_oBase, mu_smul_zBase]
    exact ⟨H_eq_of_walkH (walkH_pTwo_oBase _ _), H_eq_of_walkH (walkH_pTwo_zBase _ _)⟩

/-- **`H[Z_6, O_7] = 0`** (`results/witt-z11-extend.md` §2 (ii), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem H_zSix_oSeven (i j : Bool × ZMod (2 * 6 - 1)) : H (zSix i) (oSeven j) = 0 := by
  change H (shift 6 i.2 • zBase i.1) (shift 6 j.2 • oBase j.1) = 0
  rw [H_shift_smul]
  exact (H_zBase_shift _ _ _).1

/-- **`H[Z_6, Z_6] = 0`** (`results/witt-z11-extend.md` §2 (i), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem H_zSix_zSix (i j : Bool × ZMod (2 * 6 - 1)) : H (zSix i) (zSix j) = 0 := by
  change H (shift 6 i.2 • zBase i.1) (shift 6 j.2 • zBase j.1) = 0
  rw [H_shift_smul]
  exact (H_zBase_shift _ _ _).2

end Orthogonality

section RankR

/-- The test matching `y = {0 7, 1 4, 2 3, 5 10, 6 9, 8 ∞}` of both rank certificates
(`results/witt-z11-extend.md` §6, 54a0efc, with new data; `results/autgroup-side-effects.md`
[7], d7b3fa2). -/
def testY : PerfectMatching (Vertex 6) :=
  Covering.mkMatching
    (Covering.Witness.natPairs 6 [(0, 7), (1, 4), (2, 3), (5, 10), (6, 9), (8, 11)])
    (by decide +kernel) (by decide +kernel)

/-- The value at `d` of a list of `11` bits (`results/witt-z11-extend.md` §6, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def bitsAt (l : List F₂) (d : ZMod (2 * 6 - 1)) : F₂ :=
  l.getD d.val 0

/-- `c(d) = H[P_2, y + d]` (`results/witt-z11-extend.md` §6 (a), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def rRow : ZMod (2 * 6 - 1) → F₂ :=
  bitsAt [0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0]

/-- **Walk checks, `H[P_2, y + d] = c(d)`**: 11 walks (`results/witt-z11-extend.md` §6 (a),
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem walkH_pTwo_testY :
    ∀ d : ZMod (2 * 6 - 1), walkH pTwo.mate (shift 6 d • testY).mate = some (rRow d) := by
  decide +kernel

/-- The inverse of the `10 × 10` block `(c(l - i))_(i, l < 10)` over `𝔽₂`
(`results/witt-z11-extend.md` §6 (a), 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
def rInv (j i : Fin 10) : F₂ :=
  (([[1, 1, 0, 1, 0, 0, 1, 1, 0, 0], [1, 0, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 0, 0, 0, 1, 1, 1, 0, 0, 1], [0, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [0, 0, 0, 1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 1, 1, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 1, 0, 0, 1, 1], [0, 1, 1, 1, 0, 0, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 1, 1, 1]] : List (List F₂)).getD j
    []).getD i 0

/-- **Arithmetic check.** `rInv` is a left inverse of the block `(c(l - i))_(i, l < 10)`
(`results/witt-z11-extend.md` §6 (a), 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
theorem rInv_mul_rRow : ∀ j l : Fin 10,
    ∑ i : Fin 10, rInv j i * rRow ((l : ℕ) - (i : ℕ)) = if j = l then 1 else 0 := by
  decide +kernel

/-- **`dim R ≥ 10`**, from the `10 × 10` circulant block of `H[P_2 + i, y + l]` and its inverse
(`results/witt-z11-extend.md` §6 (a), 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
theorem le_finrank_zSixSpan : 10 ≤ Module.finrank F₂ (fpSpan zSix) := by
  have h := card_le_finrank_fpSpan_of_dual (fun i : Fin 10 ↦ zSix (false, (i : ℕ)))
    (fun l : Fin 10 ↦ shift 6 (l : ℕ) • testY) rInv ?_
  · rw [Fintype.card_fin] at h
    refine h.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨(false, (i : ℕ)), rfl⟩
  intro j l
  rw [← rInv_mul_rRow j l]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change rInv j i * H (shift 6 (i : ℕ) • pTwo) (shift 6 (l : ℕ) • testY) = _
  rw [H_shift_smul, H_eq_of_walkH (walkH_pTwo_testY _)]

end RankR

section RankL

/-- The second test matching `-y` (`results/witt-z11-extend.md` §6, 54a0efc, with new data;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def yBase (b : Bool) : PerfectMatching (Vertex 6) :=
  bif b then mu • testY else testY

/-- `m_(-1)` swaps `y` and `-y` (`results/witt-z11-extend.md` §6, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem mu_smul_yBase (b : Bool) : mu • yBase b = yBase (!b) := by
  cases b
  · rfl
  · change mu • mu • testY = testY
    rw [smul_smul, mu_mul_mu, one_smul]

/-- `H[P_7, y + d]` (`false`) and `H[P_7, -y + d]` (`true`) (`results/witt-z11-extend.md` §6 (b),
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
def sevenRow (c : Bool) : ZMod (2 * 6 - 1) → F₂ :=
  bif c then bitsAt [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0] else bitsAt [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1]

/-- **Walk checks, `H[P_7, ±y + d]`**: 22 walks (`results/witt-z11-extend.md` §6 (b), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem walkH_pSeven_yBase :
    ∀ c (d : ZMod (2 * 6 - 1)),
      walkH pSeven.mate (shift 6 d • yBase c).mate = some (sevenRow c d) := by
  decide +kernel

/-- The block `g(b, c, e) = H[oBase b, yBase c + e]`, with the `P_8` rows read from the `P_7`
rows through `m_(-1)` (`results/witt-z11-extend.md` §6 (b), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
def lRow (b c : Bool) (e : ZMod (2 * 6 - 1)) : F₂ :=
  bif b then sevenRow (!c) (-e) else sevenRow c e

/-- `H[oBase b, yBase c + e] = g(b, c, e)` (`results/witt-z11-extend.md` §6 (b), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem H_oBase_shift_yBase (b c : Bool) (e : ZMod (2 * 6 - 1)) :
    H (oBase b) (shift 6 e • yBase c) = lRow b c e := by
  cases b
  · exact H_eq_of_walkH (walkH_pSeven_yBase c e)
  · have e : oBase true = mu • oBase false := (mu_smul_oBase false).symm
    rw [e, H_mu_smul_shift, mu_smul_yBase]
    exact H_eq_of_walkH (walkH_pSeven_yBase _ _)

/-- **Rank certificate, translation-symmetric form.** For families `P_b + s` and `Q_c + t`, a
block-circulant `A` with `Σ_b Σ_u a(c, b, u) H[P_b, Q_c' + (d - u)] = [c = c' ∧ d = 0]` gives
`dim span φ(P_b + s) ≥ 11 |γ|` (`results/witt-z11-extend.md` §6 (b), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem card_mul_le_finrank_of_circulant {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (P : β → PerfectMatching (Vertex 6)) (Q : γ → PerfectMatching (Vertex 6))
    (a : γ → β → ZMod (2 * 6 - 1) → F₂)
    (h : ∀ c c' d, ∑ b, ∑ u, a c b u * H (P b) (shift 6 (d - u) • Q c') =
      if c = c' ∧ d = 0 then 1 else 0) :
    Fintype.card γ * 11 ≤
      Module.finrank F₂ (fpSpan fun i : β × ZMod (2 * 6 - 1) ↦ shift 6 i.2 • P i.1) := by
  have key := card_le_finrank_fpSpan_of_dual (fun i : β × ZMod (2 * 6 - 1) ↦ shift 6 i.2 • P i.1)
    (fun l : γ × ZMod (2 * 6 - 1) ↦ shift 6 l.2 • Q l.1) (fun j i ↦ a j.1 i.1 (i.2 - j.2)) ?_
  · rwa [Fintype.card_prod, ZMod.card] at key
  rintro ⟨c, s'⟩ ⟨c', t⟩
  rw [Fintype.sum_prod_type]
  simp only [H_shift_smul]
  have hre : ∀ b, ∑ s, a c b (s - s') * H (P b) (shift 6 (t - s) • Q c') =
      ∑ u, a c b u * H (P b) (shift 6 (t - s' - u) • Q c') := fun b ↦ by
    rw [← Equiv.sum_comp (Equiv.addRight s')]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Equiv.coe_addRight, add_sub_cancel_right, show t - (u + s') = t - s' - u by ring]
  simp only [hre, h, Prod.mk.injEq, sub_eq_zero, eq_comm (a := t)]

/-- The block-circulant inverse `a(c, b, u)` of `H[P_c + s, ±y + t]`
(`results/witt-z11-extend.md` §6 (b), 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
def lInv (c b : Bool) : ZMod (2 * 6 - 1) → F₂ :=
  bif c then
    (bif b then bitsAt [1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0]
      else bitsAt [0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1])
  else
    (bif b then bitsAt [0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0]
      else bitsAt [1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1])

/-- **Arithmetic check.** `lInv` is a block-circulant inverse of `lRow`:
`Σ_b Σ_u a(c, b, u) g(b, c', d - u) = [c = c' ∧ d = 0]` (`results/witt-z11-extend.md` §6 (b),
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem lInv_mul_lRow : ∀ (c c' : Bool) (d : ZMod (2 * 6 - 1)),
    ∑ b, ∑ u, lInv c b u * lRow b c' (d - u) = if c = c' ∧ d = 0 then 1 else 0 := by
  decide +kernel

/-- **`dim L ≥ 22`**, from the block-circulant `22 × 22` matrix `H[P_c + s, ±y + t]` and its
inverse (`results/witt-z11-extend.md` §6 (b), 54a0efc; `results/autgroup-side-effects.md` [7],
d7b3fa2). -/
theorem le_finrank_oSevenSpan : 22 ≤ Module.finrank F₂ (fpSpan oSeven) := by
  have h : Fintype.card Bool * 11 ≤ Module.finrank F₂ (fpSpan oSeven) :=
    card_mul_le_finrank_of_circulant oBase yBase lInv fun c c' d ↦ by
      simp only [H_oBase_shift_yBase]
      exact lInv_mul_lRow c c' d
  rwa [Fintype.card_bool] at h

end RankL

section Bridge

/-- `dim X + dim X^⊥ = 32` for the span of any family of matchings of `V_6`
(`finrank_fpSpan_add_finrank_orthogonal`, ham-spin 55c17eb; `results/witt-z11-extend.md` §6 (e),
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem finrank_add_finrank_orthogonal_six {ι : Type*} (F : ι → PerfectMatching (Vertex 6)) :
    Module.finrank F₂ (fpSpan F) + Module.finrank F₂ (fpForm.orthogonal (fpSpan F)) = 32 :=
  finrank_fpSpan_add_finrank_orthogonal F (card_vertex 6) (by norm_num)

/-- `R = span φ(Z_6)` is the span of the two translation orbits of `P_2` and `P_6`
(`results/witt-z11-extend.md` §6, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem fpSpan_zSix : fpSpan zSix = fpSpan zeroState :=
  fpSpan_eq_of_range_eq range_zSix

/-- **`R` is totally isotropic**, `R ≤ R^⊥` (`results/witt-z11-extend.md` §2 (i), 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem zeroSpan_le_orthogonal :
    fpSpan zeroState ≤ fpForm.orthogonal (fpSpan zeroState) := by
  rw [← fpSpan_zSix]
  exact fpSpan_le_orthogonal_of_H zSix zSix H_zSix_zSix

/-- **`span φ(GK_12) ≤ R^⊥`**, since every zero state is orthogonal to every factor
(`isZeroState_iff_rowW_mem_orthogonal`, ham-spin 55c17eb; `results/witt-z11-extend.md` §6 (e),
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem rrSpan_le_orthogonal_zeroSpan :
    rrSpan 6 ≤ fpForm.orthogonal (fpSpan zeroState) := by
  rw [← fpSpan_zSix]
  refine fpSpan_le_orthogonal_of_H (factor 6) zSix fun t j ↦ ?_
  rw [H_comm, H_apply]
  simp [isZeroState_zSix j t]

/-- **The Witt bridge at `m = 6`.** `dim R = 10`, `dim L = 22`, `R = L^⊥`, `L = R^⊥`, `R ≤ L` and
`span φ(GK_12) ≤ L`, for `R = span φ(Z_6)` and `L = span φ(O_7)` under `fpForm`
(`results/witt-z11-extend.md` §4 and §6, `results/witt-z11-contra.md` §4 and §7, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem wittBridge_six :
    Module.finrank F₂ (fpSpan zeroState) = 10 ∧ Module.finrank F₂ (fpSpan oSeven) = 22 ∧
      fpSpan zeroState = fpForm.orthogonal (fpSpan oSeven) ∧
      fpSpan oSeven = fpForm.orthogonal (fpSpan zeroState) ∧
      fpSpan zeroState ≤ fpSpan oSeven ∧ rrSpan 6 ≤ fpSpan oSeven := by
  have hRR := zeroSpan_le_orthogonal
  have hGR := rrSpan_le_orthogonal_zeroSpan
  rw [← fpSpan_zSix] at hRR hGR ⊢
  have hRL := fpSpan_le_orthogonal_of_H zSix oSeven H_zSix_oSeven
  have hLR := fpSpan_le_orthogonal_of_H oSeven zSix fun i j ↦ by
    rw [H_comm]
    exact H_zSix_oSeven j i
  have hR := le_finrank_zSixSpan
  have hL := le_finrank_oSevenSpan
  have hsL := finrank_add_finrank_orthogonal_six oSeven
  have hsR := finrank_add_finrank_orthogonal_six zSix
  have h1 := Submodule.finrank_mono hRL
  have h2 := Submodule.finrank_mono hLR
  have eR : fpSpan zSix = fpForm.orthogonal (fpSpan oSeven) :=
    Submodule.eq_of_le_of_finrank_eq hRL (by omega)
  have eL : fpSpan oSeven = fpForm.orthogonal (fpSpan zSix) :=
    Submodule.eq_of_le_of_finrank_eq hLR (by omega)
  exact ⟨by omega, by omega, eR, eL, hRR.trans eL.ge, hGR.trans eL.ge⟩

/-- **`dim span φ(Z_6) = 10`** (`results/witt-z11-extend.md` §2, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem finrank_zeroSpan : Module.finrank F₂ (fpSpan zeroState) = 10 :=
  wittBridge_six.1

/-- **`dim span φ(O_7) = 22`**, so the 22 fingerprints of `O_7` are independent
(`results/witt-z11-extend.md` §4, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem finrank_oSevenSpan : Module.finrank F₂ (fpSpan oSeven) = 22 :=
  wittBridge_six.2.1

/-- **`R = L^⊥`**: `span φ(Z_6) = (span φ(O_7))^⊥` (`results/witt-z11-extend.md` §4, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem zeroSpan_eq_orthogonal : fpSpan zeroState = fpForm.orthogonal (fpSpan oSeven) :=
  wittBridge_six.2.2.1

/-- **`L = R^⊥`**: `span φ(O_7) = (span φ(Z_6))^⊥` (`results/witt-z11-extend.md` §4, 54a0efc;
`results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem oSevenSpan_eq_orthogonal : fpSpan oSeven = fpForm.orthogonal (fpSpan zeroState) :=
  wittBridge_six.2.2.2.1

/-- **`R ≤ L`** (`results/witt-z11-extend.md` §4, 54a0efc; `results/autgroup-side-effects.md`
[7], d7b3fa2). -/
theorem zeroSpan_le_oSevenSpan : fpSpan zeroState ≤ fpSpan oSeven :=
  wittBridge_six.2.2.2.2.1

/-- **`span φ(GK_12) ≤ L`** (`results/witt-z11-extend.md` §4, `results/witt-z11-contra.md` §4,
54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem rrSpan_le_oSevenSpan : rrSpan 6 ≤ fpSpan oSeven :=
  wittBridge_six.2.2.2.2.2

/-- **`GK_12` is redundant**: `span φ(GK_12 ∪ O_7) = span φ(O_7)` (`results/witt-z11-contra.md`
§4 and verdict 14, 54a0efc; `results/autgroup-side-effects.md` [7], d7b3fa2). -/
theorem rrSpan_sup_oSevenSpan : rrSpan 6 ⊔ fpSpan oSeven = fpSpan oSeven :=
  sup_eq_right.2 rrSpan_le_oSevenSpan

end Bridge

end Pairing.RoundRobin.Canonical.WittSix
