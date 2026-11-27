import Clifford.PolarSection
import Repair.Covering.Witness
import Repair.SqrtObstructions.CertLength
import Repair.DualOrbit

/-!
# The dimension of the round-robin fingerprint span (COD-259, COD-262)

Let `F : ι → 𝓜(V)` be a family of perfect matchings, `φ(P) = r_P` its fingerprints (`rowW`,
ham-spin 55c17eb) and `R(F) = span{φ(F_t)}` (`fpSpan`, ham-spin 55c17eb). The rank of `R(F)` is
read off by pairing `F` against a dual family `Q`. A relation `Σ_t c_t φ(F_t) = 0`, evaluated at
`Q_s`, gives `Σ_t H[Q_s, F_t] c_t = 0`, so the pairing matrix bounds the relations. For the
round-robin factors the dual families are the translates of `P*` and `Q` (`Repair.DualOrbit`,
`results/one-factor-q-review.md`, organize-archive not committed yet).

* `fpCoeff F` : the coefficient map `c ↦ Σ_t c_t φ(F_t)`, with range `R(F)` (`range_fpCoeff`).
  `fpSum F = Σ_t φ(F_t)` is the image of the all-ones vector, and `coe_fpSum_apply` : its value
  at `P` is `#{t | Ham P F_t}` mod 2.
* The ladder. `pairingMatrix Q F = (H[Q_s, F_t])` and `rank_pairingMatrix_le` : its rank bounds
  `dim R(F)` from below. `finrank_fpSpan_eq_card_of_triangular` : a unit upper-triangular pairing
  gives `dim R(F) = |ι|`, and `finrank_fpSpan_eq_card_of_biorthogonal` : so does a biorthogonal
  one, `H[Q_s, F_t] = [t = σ s]`. `ker_fpCoeff_le_of_ladder` : a bidiagonal pairing over
  `ℤ/n`, `H[Q_s, F_t] = [t ∈ {s, s + 1}]` (the circulant `1 + x`), leaves only constant
  relations, so `card_sub_one_le_finrank_fpSpan_of_ladder` : `dim R(F) ≥ n - 1`, and
  `rank_pairingMatrix_of_ladder` : the circulant has rank `n - 1`.
* The kernel layer. If every relation has constant `c` (`LinearMap.ker (fpCoeff F) ≤ span{1}`),
  then `card_sub_one_le_finrank_fpSpan_of_ker_le` : `dim R(F) ≥ |ι| - 1`,
  `finrank_fpSpan_eq_card_iff_of_ker_le` : `dim R(F) = |ι|` iff `Σ_t φ(F_t) ≠ 0`,
  `finrank_fpSpan_eq_card_iff_exists_odd_of_ker_le` : iff some `P` closes one cycle with an odd
  number of the `F_t`, and `finrank_fpSpan_eq_card_sub_one_iff_of_ker_le`.
* Hamiltonian cliques, `F_s ∪ F_t` one cycle exactly for `s ≠ t`, Gram matrix `J + I`.
  `eq_sum_of_fpCoeff_eq_zero`, `ker_fpCoeff_le` : every relation has constant `c`, which feeds the
  kernel layer as `card_sub_one_le_finrank_fpSpan`, `finrank_fpSpan_eq_card_iff`,
  `finrank_fpSpan_eq_card_iff_exists_odd` and `finrank_fpSpan_eq_card_sub_one_iff`.
  `fpSum_mem_inf_orthogonal` : for odd `|ι|`, `Σ_t φ(F_t) ∈ R(F) ∩ R(F)^⊥`.
* The radical of a Hamiltonian clique, Proposition 5 of `results/audit-manuscript-extend.md`
  (organize-archive 313d6ea). `eq_sum_of_fpCoeff_mem_orthogonal` : `Σ_t c_t φ(F_t) ∈ R(F)^⊥`
  forces `c_s = Σ_t c_t`, so `fpSpan_inf_orthogonal_le` : `R(F) ∩ R(F)^⊥ ≤ F₂ · Σ_t φ(F_t)`.
  `fpSpan_inf_orthogonal_eq_of_odd` : equality for odd `|ι|`, and
  `fpSpan_inf_orthogonal_eq_bot_of_even`, `finrank_fpSpan_of_even` : the radical is `0` and
  `dim R(F) = |ι|` for even `|ι|`. None of these assumes independence.
* `RoundRobin.Canonical`, `n = 2m - 1`. `ham_shift_pStar_ladder` : the translates of `P*` pair
  bidiagonally with the factors, for every `m ≥ 2`. Hence `ker_fpCoeff_factor_le` and
  `finrank_rrSpan_of_two_le` : `2m - 2 ≤ dim R_rr ≤ 2m - 1`, prime or composite `n`
  (`results/f2-slice-extend.md`, cd0ed47, Theorem 2).
  `finrank_rrSpan_eq_iff_exists_odd_hamCount_of_two_le` : `dim R_rr = 2m - 1` iff some `P` has
  odd `X(P)` (`hamCount`, ham_pairings main 978559a), and
  `finrank_rrSpan_eq_sub_two_iff_of_two_le`. The prime-only `finrank_rrSpan_of_prime`,
  `finrank_rrSpan_eq_iff_exists_odd_hamCount` and `finrank_rrSpan_eq_sub_two_iff` are their
  specialisations. `ham_factor_iff_ne` (the clique at prime `n`) remains for
  `fpSum_factor_mem_inf_orthogonal`.
* `ham_shift_oneQ_biorthogonal` : the translates of `Q` pair biorthogonally with the factors for
  `m ≥ 5`, so `finrank_rrSpan_of_five_le` : `dim R_rr = 2m - 1` for every `m ≥ 5`, and
  `finrank_rrSpan_of_four_le` with `finrank_rrSpan_four`.
* `finrank_rrSpan_two`, `finrank_rrSpan_three` : `dim R_rr = 2m - 2` at `m = 2, 3`, where
  `dim W = 2^(m-1)` leaves no room for more. `finrank_rrSpan_four` and `finrank_rrSpan_six` :
  `dim R_rr = 2m - 1` at `m = 4, 6`. The first is witnessed by `X(Q_3) = 3`, and the second is
  now a case of `finrank_rrSpan_of_five_le` (its witness `X(Q_2) = 7` is kept).
* Corollary 6 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea).
  `rrSpan_inf_orthogonal_eq` : at prime `n`, `R_rr ∩ R_rr^⊥ = F₂ · Σ_t φ(F_t)`.
  `fpSum_factor_ne_zero` : `Σ_t φ(F_t) ≠ 0` for `m ≥ 4`, so `finrank_rrSpan_inf_orthogonal` : the
  radical is a line at prime `n ≥ 7`.
-/

namespace Pairing.PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- The coefficient map `c ↦ Σ_t c_t φ(F_t)` into the fingerprint module `W V` (`rowW`, ham-spin
fd082bf). Its range is `R(F)` (`range_fpCoeff`). -/
noncomputable def fpCoeff (F : ι → PerfectMatching V) : (ι → F₂) →ₗ[F₂] W V :=
  Fintype.linearCombination F₂ fun t ↦ rowW (F t)

/-- The range of `fpCoeff F` is `R(F)` (`fpSpan`, ham-spin fd082bf). -/
theorem range_fpCoeff (F : ι → PerfectMatching V) : LinearMap.range (fpCoeff F) = fpSpan F :=
  Fintype.range_linearCombination _ _

/-- `Σ_t c_t φ(F_t)` evaluated at `P` is `Σ_t c_t H[F_t, P]` (`H`, `rowW`, ham-spin fd082bf). -/
theorem coe_fpCoeff_apply (F : ι → PerfectMatching V) (c : ι → F₂) (P : PerfectMatching V) :
    (fpCoeff F c : PerfectMatching V → F₂) P = ∑ t, c t * H (F t) P := by
  simp [fpCoeff, Fintype.linearCombination_apply, Finset.sum_apply, coe_rowW]

/-- The fingerprint sum `Σ_t φ(F_t)` in `W V` (`rowW`, ham-spin fd082bf). -/
noncomputable def fpSum (F : ι → PerfectMatching V) : W V :=
  ∑ t, rowW (F t)

/-- `fpSum F` is the image of the all-ones vector under `fpCoeff F`. -/
theorem fpCoeff_one (F : ι → PerfectMatching V) : fpCoeff F 1 = fpSum F := by
  simp [fpCoeff, Fintype.linearCombination_apply, fpSum]

/-- `Σ_t φ(F_t)` evaluated at `P` is `#{t | Ham P F_t}` mod 2 (`Ham`, ham-spin fd082bf). -/
theorem coe_fpSum_apply (F : ι → PerfectMatching V) (P : PerfectMatching V) :
    (fpSum F : PerfectMatching V → F₂) P = ((univ.filter fun t ↦ Ham P (F t)).card : F₂) := by
  rw [← fpCoeff_one, coe_fpCoeff_apply]
  simp_rw [Pi.one_apply, one_mul, H_apply, ham_comm (F _) P]
  rw [Finset.sum_boole]

/-- `Σ_t φ(F_t) = 0` iff every `P` closes one cycle with an even number of the `F_t` (`Ham`,
ham-spin fd082bf). -/
theorem fpSum_eq_zero_iff (F : ι → PerfectMatching V) :
    fpSum F = 0 ↔ ∀ P, Even (univ.filter fun t ↦ Ham P (F t)).card := by
  simp_rw [← ZMod.natCast_eq_zero_iff_even, ← coe_fpSum_apply]
  constructor
  · intro h P
    simp [h]
  · intro h
    exact Subtype.ext (funext h)

private theorem finrank_range_add_finrank_ker_fpCoeff (F : ι → PerfectMatching V) :
    Module.finrank F₂ (fpSpan F) + Module.finrank F₂ (LinearMap.ker (fpCoeff F)) =
      Fintype.card ι := by
  rw [← range_fpCoeff, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

section Ladder

variable {κ : Type*}

/-- Evaluation of `W V` at a family `Q` of matchings, `f ↦ (f(Q_s))_s` (`W`, ham-spin 55c17eb;
`results/one-factor-q-review.md`, organize-archive not committed yet, step 5). -/
noncomputable def pairingEval (Q : κ → PerfectMatching V) : W V →ₗ[F₂] (κ → F₂) :=
  LinearMap.pi fun s ↦ (LinearMap.proj (Q s)).comp (W V).subtype

/-- The pairing matrix `H[Q_s, F_t]` of a dual family `Q` against `F` (`H`, ham-spin 55c17eb). -/
def pairingMatrix (Q : κ → PerfectMatching V) (F : ι → PerfectMatching V) : Matrix κ ι F₂ :=
  Matrix.of fun s t ↦ H (Q s) (F t)

/-- The pairing matrix acts as evaluation at `Q` after the coefficient map: `H[Q, F] c` is
`Σ_t c_t φ(F_t)` evaluated at the `Q_s`. -/
theorem mulVecLin_pairingMatrix (Q : κ → PerfectMatching V) (F : ι → PerfectMatching V) :
    (pairingMatrix Q F).mulVecLin = (pairingEval Q).comp (fpCoeff F) := by
  refine LinearMap.ext fun c ↦ funext fun s ↦ ?_
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, pairingMatrix, Matrix.of_apply,
    LinearMap.comp_apply, pairingEval, LinearMap.pi_apply, Submodule.coe_subtype,
    LinearMap.coe_proj, Function.eval, coe_fpCoeff_apply]
  exact Finset.sum_congr rfl fun t _ ↦ by rw [H_comm, mul_comm]

/-- The ladder bound: `rank H[Q, F] ≤ dim R(F)` for every dual family `Q` (`fpSpan`, ham-spin
55c17eb; `results/one-factor-q-review.md`, organize-archive not committed yet). -/
theorem rank_pairingMatrix_le (Q : κ → PerfectMatching V) (F : ι → PerfectMatching V) :
    (pairingMatrix Q F).rank ≤ Module.finrank F₂ (fpSpan F) := by
  rw [Matrix.rank, mulVecLin_pairingMatrix, LinearMap.range_comp, range_fpCoeff]
  exact Submodule.finrank_map_le _ _

/-- A unit upper-triangular pairing, `Ham (Q s) (F s)` and `¬Ham (Q s) (F t)` for `t < s`, gives
`dim R(F) = |ι|` (`fpSpan`, `Ham`, ham-spin 55c17eb; `results/one-factor-q-review.md`,
organize-archive not committed yet). -/
theorem finrank_fpSpan_eq_card_of_triangular [LinearOrder ι] {F : ι → PerfectMatching V}
    (Q : ι → PerfectMatching V) (hdiag : ∀ s, Ham (Q s) (F s))
    (hlow : ∀ s t, t < s → ¬Ham (Q s) (F t)) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι := by
  have htri : (pairingMatrix Q F).IsUpperTriangular := fun s t hts ↦ by
    simp [pairingMatrix, H_apply, hlow s t hts]
  have hdet : (pairingMatrix Q F).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_eq_one fun s _ ↦ by simp [pairingMatrix, H_apply, hdiag s]
  have hrk := Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one))
  have h1 := rank_pairingMatrix_le Q F
  have h2 := finrank_fpSpan_le F
  omega

/-- A biorthogonal dual family, `Ham (Q s) (F t) ↔ t = σ s` for a bijection `σ`, makes the
`φ(F_t)` independent: `dim R(F) = |ι|` (`fpSpan`, `Ham`, ham-spin 55c17eb). Evaluating a relation
`Σ_t c_t φ(F_t) = 0` at `Q_s` gives `c_(σ s) = 0` (`results/one-factor-q-review.md`,
organize-archive not committed yet, step 5). -/
theorem finrank_fpSpan_eq_card_of_biorthogonal {F : ι → PerfectMatching V}
    (Q : κ → PerfectMatching V) (σ : κ ≃ ι) (h : ∀ s t, Ham (Q s) (F t) ↔ t = σ s) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι := by
  have hinj : Function.Injective (fpCoeff F) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ funext fun s ↦ ?_
    have hH : ∀ t, Ham (F t) (Q (σ.symm s)) ↔ t = s := fun t ↦
      (ham_comm _ _).trans ((h _ t).trans (by rw [Equiv.apply_symm_apply]))
    have h0 : ∑ t, c t * H (F t) (Q (σ.symm s)) = 0 := by
      rw [← coe_fpCoeff_apply, hc]
      rfl
    rw [Finset.sum_eq_single s (fun t _ hts ↦ by
      rw [H_apply, ite_eq_right fun h' ↦ hts ((hH t).mp h'), mul_zero])
      (fun hs ↦ absurd (Finset.mem_univ s) hs), H_apply, ite_eq_left ((hH s).mpr rfl),
      mul_one] at h0
    exact h0
  rw [← range_fpCoeff, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]

/-- Against a bidiagonal dual family over `ℤ/n`, `Ham (Q s) (F t) ↔ t ∈ {s, s + 1}`, a vector `c`
evaluates at `Q_s` to `c_s + c_(s+1)`. -/
theorem sum_mul_H_of_ladder {n : ℕ} [NeZero n] (hn : 1 < n) {F : ZMod n → PerfectMatching V}
    (Q : ZMod n → PerfectMatching V) (h : ∀ s t, Ham (Q s) (F t) ↔ t = s ∨ t = s + 1)
    (c : ZMod n → F₂) (s : ZMod n) : ∑ t, c t * H (F t) (Q s) = c s + c (s + 1) := by
  have hne : s ≠ s + 1 := fun h' ↦ by
    have h1 : (1 : ZMod n) = 0 := by linear_combination -h'
    have := ZMod.val_one'' (n := n) (by omega)
    rw [h1, ZMod.val_zero] at this
    exact zero_ne_one this
  have hH : ∀ t, c t * H (F t) (Q s) =
      (if t = s then c t else 0) + (if t = s + 1 then c t else 0) := fun t ↦ by
    have hiff : Ham (F t) (Q s) ↔ t = s ∨ t = s + 1 := (ham_comm _ _).trans (h s t)
    rw [H_apply]
    by_cases h1 : t = s
    · subst h1
      rw [ite_eq_left (hiff.mpr (Or.inl rfl)), mul_one, ite_eq_left rfl, ite_eq_right hne, add_zero]
    · by_cases h2 : t = s + 1
      · rw [ite_eq_left (hiff.mpr (Or.inr h2)), mul_one, ite_eq_right h1, ite_eq_left h2,
          zero_add]
      · rw [ite_eq_right fun h' ↦ (hiff.mp h').elim h1 h2, mul_zero, ite_eq_right h1,
          ite_eq_right h2, add_zero]
  rw [Finset.sum_congr rfl fun t _ ↦ hH t, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]

/-- Against a bidiagonal dual family over `ℤ/n` (the circulant `1 + x`), every relation among the
`φ(F_t)` is constant, `ker (fpCoeff F) ≤ span{1}` (`results/one-factor-q-review.md`,
organize-archive not committed yet; `results/f2-slice-extend.md`, cd0ed47, Theorem 2). -/
theorem ker_fpCoeff_le_of_ladder {n : ℕ} [NeZero n] (hn : 1 < n) {F : ZMod n → PerfectMatching V}
    (Q : ZMod n → PerfectMatching V) (h : ∀ s t, Ham (Q s) (F t) ↔ t = s ∨ t = s + 1) :
    LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1} := by
  intro c hc
  have hstep : ∀ s, c (s + 1) = c s := fun s ↦ by
    have h0 : ∑ t, c t * H (F t) (Q s) = 0 := by
      rw [← coe_fpCoeff_apply, LinearMap.mem_ker.mp hc]
      rfl
    rw [sum_mul_H_of_ladder hn Q h] at h0
    generalize c s = a at h0
    generalize c (s + 1) = b at h0
    revert a b
    decide
  have hconst : ∀ k : ℕ, c (k : ZMod n) = c 0 := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero]
    | succ k ih => rw [Nat.cast_succ, hstep, ih]
  refine Submodule.mem_span_singleton.mpr ⟨c 0, funext fun t ↦ ?_⟩
  rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← ZMod.natCast_zmod_val t, hconst]

/-- The circulant `1 + x` has rank `n - 1` over `𝔽₂`: a bidiagonal dual family over `ℤ/n` has
pairing matrix of rank `n - 1` (`results/one-factor-q-review.md`, organize-archive not committed
yet). -/
theorem rank_pairingMatrix_of_ladder {n : ℕ} [NeZero n] (hn : 1 < n)
    {F : ZMod n → PerfectMatching V} (Q : ZMod n → PerfectMatching V)
    (h : ∀ s t, Ham (Q s) (F t) ↔ t = s ∨ t = s + 1) :
    (pairingMatrix Q F).rank = n - 1 := by
  have hmv : ∀ c s, (pairingMatrix Q F).mulVecLin c s = c s + c (s + 1) := fun c s ↦ by
    rw [mulVecLin_pairingMatrix, LinearMap.comp_apply, ← sum_mul_H_of_ladder hn Q h c s,
      ← coe_fpCoeff_apply]
    rfl
  have hker : LinearMap.ker (pairingMatrix Q F).mulVecLin = Submodule.span F₂ {1} := by
    refine le_antisymm (fun c hc ↦ ?_) ((Submodule.span_le).mpr ?_)
    · have hstep : ∀ s, c (s + 1) = c s := fun s ↦ by
        have h0 : c s + c (s + 1) = 0 := by
          have := congrFun (LinearMap.mem_ker.mp hc) s
          rwa [hmv, Pi.zero_apply] at this
        generalize c s = a at h0
        generalize c (s + 1) = b at h0
        revert a b
        decide
      have hconst : ∀ k : ℕ, c (k : ZMod n) = c 0 := by
        intro k
        induction k with
        | zero => rw [Nat.cast_zero]
        | succ k ih => rw [Nat.cast_succ, hstep, ih]
      refine Submodule.mem_span_singleton.mpr ⟨c 0, funext fun t ↦ ?_⟩
      rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← ZMod.natCast_zmod_val t, hconst]
    · rintro _ rfl
      exact LinearMap.mem_ker.mpr (funext fun s ↦ by
        rw [hmv, Pi.one_apply, Pi.one_apply, Pi.zero_apply]
        rfl)
  have hrk := LinearMap.finrank_range_add_finrank_ker (pairingMatrix Q F).mulVecLin
  rw [hker, finrank_span_singleton (one_ne_zero), Module.finrank_fintype_fun_eq_card,
    ZMod.card] at hrk
  rw [Matrix.rank]
  omega

end Ladder

section KernelLayer

variable {F : ι → PerfectMatching V}

/-- If every relation among the `φ(F_t)` is constant, `ker (fpCoeff F) ≤ span{1}`, then
`dim R(F) ≥ |ι| - 1` (`fpSpan`, ham-spin 55c17eb). -/
theorem card_sub_one_le_finrank_fpSpan_of_ker_le
    (hk : LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1}) :
    Fintype.card ι - 1 ≤ Module.finrank F₂ (fpSpan F) := by
  have hrk := finrank_range_add_finrank_ker_fpCoeff F
  have hker : Module.finrank F₂ (LinearMap.ker (fpCoeff F)) ≤ 1 :=
    (Submodule.finrank_mono hk).trans ((finrank_span_le_card _).trans (by simp))
  omega

/-- If every relation is constant, `dim R(F) = |ι|` iff `Σ_t φ(F_t) ≠ 0` (`fpSpan`, ham-spin
55c17eb). -/
theorem finrank_fpSpan_eq_card_iff_of_ker_le [Nonempty ι]
    (hk : LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1}) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔ fpSum F ≠ 0 := by
  have hrk := finrank_range_add_finrank_ker_fpCoeff F
  constructor
  · intro h h0
    have hk0 : LinearMap.ker (fpCoeff F) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      omega
    have h1 : (1 : ι → F₂) ∈ LinearMap.ker (fpCoeff F) := by
      rw [LinearMap.mem_ker, fpCoeff_one, h0]
    rw [hk0, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · intro h
    have hk0 : LinearMap.ker (fpCoeff F) = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hk hc)
      rw [LinearMap.mem_ker, map_smul, fpCoeff_one, smul_eq_zero] at hc
      rw [Submodule.mem_bot]
      rcases hc with rfl | h0
      · exact zero_smul _ _
      · exact absurd h0 h
    rw [hk0, finrank_bot] at hrk
    omega

/-- If every relation is constant, `dim R(F) = |ι|` iff some `P` closes one cycle with an odd
number of the `F_t` (`fpSpan`, `Ham`, ham-spin 55c17eb). -/
theorem finrank_fpSpan_eq_card_iff_exists_odd_of_ker_le [Nonempty ι]
    (hk : LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1}) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔
      ∃ P, Odd (univ.filter fun t ↦ Ham P (F t)).card := by
  rw [finrank_fpSpan_eq_card_iff_of_ker_le hk, Ne, fpSum_eq_zero_iff]
  simp only [not_forall, Nat.not_even_iff_odd]

/-- If every relation is constant, `dim R(F) = |ι| - 1` iff `Σ_t φ(F_t) = 0` (`fpSpan`, ham-spin
55c17eb). -/
theorem finrank_fpSpan_eq_card_sub_one_iff_of_ker_le [Nonempty ι]
    (hk : LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1}) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι - 1 ↔ fpSum F = 0 := by
  have h1 := finrank_fpSpan_le F
  have h3 := finrank_fpSpan_eq_card_iff_of_ker_le hk
  have hpos := Fintype.card_pos (α := ι)
  constructor
  · intro h
    by_contra h0
    have := h3.mpr h0
    omega
  · intro h0
    have h2 := card_sub_one_le_finrank_fpSpan_of_ker_le hk
    have : Module.finrank F₂ (fpSpan F) ≠ Fintype.card ι := fun h ↦ h3.mp h h0
    omega

/-- A bidiagonal dual family over `ℤ/n` gives `dim R(F) ≥ n - 1` (`fpSpan`, ham-spin 55c17eb;
`results/one-factor-q-review.md`, organize-archive not committed yet). -/
theorem card_sub_one_le_finrank_fpSpan_of_ladder {n : ℕ} [NeZero n] (hn : 1 < n)
    {F : ZMod n → PerfectMatching V} (Q : ZMod n → PerfectMatching V)
    (h : ∀ s t, Ham (Q s) (F t) ↔ t = s ∨ t = s + 1) :
    n - 1 ≤ Module.finrank F₂ (fpSpan F) := by
  have := card_sub_one_le_finrank_fpSpan_of_ker_le (ker_fpCoeff_le_of_ladder hn Q h)
  rwa [ZMod.card] at this

end KernelLayer

variable {F : ι → PerfectMatching V}

/-- For a Hamiltonian clique, `F_s ∪ F_t` one cycle iff `s ≠ t` (`Ham`, ham-spin fd082bf), every
`c` with `Σ_t c_t φ(F_t) = 0` is constant: `c_s = Σ_t c_t`. This is the kernel of `J + I`. -/
theorem eq_sum_of_fpCoeff_eq_zero (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) {c : ι → F₂}
    (hc : fpCoeff F c = 0) (s : ι) : c s = ∑ t, c t := by
  classical
  have h0 : ∑ t, c t * H (F t) (F s) = 0 := by
    rw [← coe_fpCoeff_apply, hc]
    rfl
  have h1 : ∀ t, c t * H (F t) (F s) + (if t = s then c t else 0) = c t := by
    intro t
    rw [H_apply]
    by_cases hts : t = s
    · subst hts
      simp [hF]
    · simp [hF, hts]
  calc c s = ∑ t, c t * H (F t) (F s) + ∑ t, (if t = s then c t else 0) := by
        rw [h0, zero_add, Finset.sum_ite_eq']
        simp
    _ = ∑ t, c t := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ ↦ h1 t

/-- For a Hamiltonian clique (`Ham`, ham-spin fd082bf), the relations among the `φ(F_t)` lie in
the span of the all-ones vector. -/
theorem ker_fpCoeff_le (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1} := by
  intro c hc
  rw [Submodule.mem_span_singleton]
  refine ⟨∑ t, c t, funext fun s ↦ ?_⟩
  rw [eq_sum_of_fpCoeff_eq_zero hF (LinearMap.mem_ker.mp hc) s]
  simp

/-- `dim R(F) ≥ |ι| - 1` for a Hamiltonian clique (`fpSpan`, `Ham`, ham-spin fd082bf), since its
Gram matrix `J + I` has rank at least `|ι| - 1`. -/
theorem card_sub_one_le_finrank_fpSpan (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Fintype.card ι - 1 ≤ Module.finrank F₂ (fpSpan F) :=
  card_sub_one_le_finrank_fpSpan_of_ker_le (ker_fpCoeff_le hF)

/-- For a nonempty Hamiltonian clique (`Ham`, ham-spin 55c17eb), the `φ(F_t)` are independent,
`dim R(F) = |ι|`, iff `Σ_t φ(F_t) ≠ 0` (`fpSpan`, ham-spin 55c17eb). -/
theorem finrank_fpSpan_eq_card_iff [Nonempty ι] (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔ fpSum F ≠ 0 :=
  finrank_fpSpan_eq_card_iff_of_ker_le (ker_fpCoeff_le hF)

/-- For a nonempty Hamiltonian clique, `dim R(F) = |ι|` iff some `P` closes one cycle with an odd
number of the `F_t` (`fpSpan`, `Ham`, ham-spin 55c17eb). -/
theorem finrank_fpSpan_eq_card_iff_exists_odd [Nonempty ι]
    (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔
      ∃ P, Odd (univ.filter fun t ↦ Ham P (F t)).card :=
  finrank_fpSpan_eq_card_iff_exists_odd_of_ker_le (ker_fpCoeff_le hF)

/-- For a nonempty Hamiltonian clique, `dim R(F) = |ι| - 1` iff `Σ_t φ(F_t) = 0` (`fpSpan`, `Ham`,
ham-spin 55c17eb). -/
theorem finrank_fpSpan_eq_card_sub_one_iff [Nonempty ι] (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι - 1 ↔ fpSum F = 0 :=
  finrank_fpSpan_eq_card_sub_one_iff_of_ker_le (ker_fpCoeff_le hF)

/-- For a Hamiltonian clique of odd size, `Σ_t φ(F_t)` lies in `R(F) ∩ R(F)^⊥`: each `F_s` is
Hamiltonian with the `|ι| - 1` others, an even number (`fpSpan`, `fpForm`, ham-spin fd082bf). -/
theorem fpSum_mem_inf_orthogonal (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hodd : Odd (Fintype.card ι)) :
    fpSum F ∈ fpSpan F ⊓ fpForm.orthogonal (fpSpan F) := by
  classical
  refine Submodule.mem_inf.mpr ⟨Submodule.sum_mem _ fun t _ ↦ Submodule.subset_span ⟨t, rfl⟩, ?_⟩
  rw [mem_orthogonal_fpSpan_iff]
  intro s
  rw [coe_fpSum_apply, ZMod.natCast_eq_zero_iff_even]
  have he : (univ.filter fun t ↦ Ham (F s) (F t)) = univ.erase s := by
    ext t
    simp [hF, eq_comm]
  rw [he, card_erase_of_mem (mem_univ s), card_univ]
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

/-- Proposition 5(1) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). For a
Hamiltonian clique, `F_s ∪ F_t` one cycle iff `s ≠ t` (`Ham`, ham-spin fd082bf), every `c` with
`Σ_t c_t φ(F_t) ∈ R(F)^⊥` is constant, `c_s = Σ_t c_t` (`fpSpan`, `fpForm`, ham-spin fd082bf).
No independence of the `φ(F_t)` is assumed. -/
theorem eq_sum_of_fpCoeff_mem_orthogonal (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) {c : ι → F₂}
    (hc : fpCoeff F c ∈ fpForm.orthogonal (fpSpan F)) (s : ι) : c s = ∑ t, c t := by
  classical
  have h0 : ∑ t, c t * H (F t) (F s) = 0 := by
    rw [← coe_fpCoeff_apply]
    exact (mem_orthogonal_fpSpan_iff F _).mp hc s
  have h1 : ∀ t, c t * H (F t) (F s) + (if t = s then c t else 0) = c t := by
    intro t
    rw [H_apply]
    by_cases hts : t = s
    · subst hts
      simp [hF]
    · simp [hF, hts]
  calc c s = ∑ t, c t * H (F t) (F s) + ∑ t, (if t = s then c t else 0) := by
        rw [h0, zero_add, Finset.sum_ite_eq']
        simp
    _ = ∑ t, c t := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ ↦ h1 t

/-- Proposition 5(2) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). For a
Hamiltonian clique of even size (`Ham`, ham-spin fd082bf), `Σ_t c_t φ(F_t) ∈ R(F)^⊥` forces
`c = 0` (`fpSpan`, `fpForm`, ham-spin fd082bf). -/
theorem eq_zero_of_fpCoeff_mem_orthogonal_of_even (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (heven : Even (Fintype.card ι)) {c : ι → F₂}
    (hc : fpCoeff F c ∈ fpForm.orthogonal (fpSpan F)) : c = 0 := by
  have hs := eq_sum_of_fpCoeff_mem_orthogonal hF hc
  have hsum : ∑ t, c t = 0 := by
    have h : ∑ t, c t = ∑ _t : ι, ∑ s, c s := Finset.sum_congr rfl fun t _ ↦ hs t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      (ZMod.natCast_eq_zero_iff_even).mpr heven, zero_mul] at h
    exact h
  exact funext fun s ↦ by rw [hs s, hsum, Pi.zero_apply]

/-- Proposition 5 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). For a
Hamiltonian clique (`Ham`, ham-spin fd082bf), the radical of `R(F)` lies on the line of
`Σ_t φ(F_t)`: `R(F) ∩ R(F)^⊥ ≤ F₂ · Σ_t φ(F_t)` (`fpSpan`, `fpForm`, ham-spin fd082bf). No
independence of the `φ(F_t)` is assumed. -/
theorem fpSpan_inf_orthogonal_le (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    fpSpan F ⊓ fpForm.orthogonal (fpSpan F) ≤ Submodule.span F₂ {fpSum F} := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  rw [← range_fpCoeff] at hv1
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hv1
  have hc : c = (∑ t, c t) • (1 : ι → F₂) := funext fun s ↦ by
    rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, eq_sum_of_fpCoeff_mem_orthogonal hF hv2]
  rw [hc, map_smul, fpCoeff_one]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Proposition 5(2) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). A
Hamiltonian clique of even size (`Ham`, ham-spin fd082bf) has `R(F) ∩ R(F)^⊥ = 0` (`fpSpan`,
`fpForm`, ham-spin fd082bf). -/
theorem fpSpan_inf_orthogonal_eq_bot_of_even (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (heven : Even (Fintype.card ι)) : fpSpan F ⊓ fpForm.orthogonal (fpSpan F) = ⊥ := by
  refine eq_bot_iff.mpr fun v hv ↦ ?_
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  rw [← range_fpCoeff] at hv1
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hv1
  rw [eq_zero_of_fpCoeff_mem_orthogonal_of_even hF heven hv2, map_zero]
  exact Submodule.zero_mem _

/-- Proposition 5(2) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). A
Hamiltonian clique of even size (`Ham`, ham-spin fd082bf) has independent fingerprints,
`dim R(F) = |ι|` (`fpSpan`, ham-spin fd082bf). -/
theorem finrank_fpSpan_of_even (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (heven : Even (Fintype.card ι)) : Module.finrank F₂ (fpSpan F) = Fintype.card ι := by
  have hinj : Function.Injective (fpCoeff F) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
    refine eq_zero_of_fpCoeff_mem_orthogonal_of_even hF heven ?_
    rw [hc]
    exact Submodule.zero_mem _
  rw [← range_fpCoeff, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]

/-- Proposition 5(3) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). A
Hamiltonian clique of odd size (`Ham`, ham-spin fd082bf) has `R(F) ∩ R(F)^⊥ = F₂ · Σ_t φ(F_t)`
(`fpSpan`, `fpForm`, ham-spin fd082bf), with no independence hypothesis. -/
theorem fpSpan_inf_orthogonal_eq_of_odd (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hodd : Odd (Fintype.card ι)) :
    fpSpan F ⊓ fpForm.orthogonal (fpSpan F) = Submodule.span F₂ {fpSum F} :=
  le_antisymm (fpSpan_inf_orthogonal_le hF)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (fpSum_mem_inf_orthogonal hF hodd))

end Pairing.PerfectMatching

namespace Pairing.RoundRobin.Canonical

open PerfectMatching Finset

variable {m : ℕ} [NeZero m]

/-- At prime `n = 2m - 1` the canonical factors (`factor`, ham-spin fd082bf) form a Hamiltonian
clique, `F_s ∪ F_t` is one cycle iff `s ≠ t`. The "if" half is the gcd law `ham_factor_of_ne`
(ham_pairings main d1cda40), and `F_t ∪ F_t` has a doubled edge. -/
theorem ham_factor_iff_ne (hp : (2 * m - 1).Prime) (s t : ZMod (2 * m - 1)) :
    Ham (factor m s) (factor m t) ↔ s ≠ t := by
  refine ⟨?_, ham_factor_of_ne hp⟩
  rintro h rfl
  have hm : 2 < Fintype.card (Vertex m) := by
    have := hp.two_le
    rw [card_vertex]
    omega
  exact not_ham_of_mate_eq_of_two_lt hm (v := none) rfl h

/-- The translates `P* + (s - (m - 1))` of `pStar` form a bidiagonal dual family: the one indexed
by `s` closes one cycle with `F_t` exactly for `t ∈ {s, s + 1}`, for every `m ≥ 2`
(`ham_shift_pStar_iff`; `results/f2-slice-extend.md`, organize-archive cd0ed47, Lemma 1 and
Theorem 2). -/
theorem ham_shift_pStar_ladder (hm : 2 ≤ m) (s t : ZMod (2 * m - 1)) :
    Ham (shift m (s - ((m : ZMod (2 * m - 1)) - 1)) • pStar m) (factor m t) ↔
      t = s ∨ t = s + 1 := by
  rw [ham_shift_pStar_iff hm, show (m : ZMod (2 * m - 1)) - 1 + (s - (m - 1)) = s by ring,
    show (m : ZMod (2 * m - 1)) + (s - (m - 1)) = s + 1 by ring]

/-- Every relation among the `φ(F_t)` is constant, for every `m ≥ 2`, prime or composite
`n = 2m - 1`, by the `P*` ladder (`fpCoeff`; `results/f2-slice-extend.md`, organize-archive
cd0ed47, Theorem 2). This replaces the clique argument `ker_fpCoeff_le (ham_factor_iff_ne hp)`. -/
theorem ker_fpCoeff_factor_le (hm : 2 ≤ m) :
    LinearMap.ker (fpCoeff (factor m)) ≤ Submodule.span F₂ {1} :=
  ker_fpCoeff_le_of_ladder (by omega) _ (ham_shift_pStar_ladder hm)

/-- `2m - 2 ≤ dim R_rr ≤ 2m - 1` for every `m ≥ 2`, prime or composite `n` (`rrSpan`, ham-spin
55c17eb), from the `P*` ladder (`results/f2-slice-extend.md`, organize-archive cd0ed47,
Theorem 2.1). -/
theorem finrank_rrSpan_of_two_le (hm : 2 ≤ m) :
    2 * m - 2 ≤ Module.finrank F₂ (rrSpan m) ∧ Module.finrank F₂ (rrSpan m) ≤ 2 * m - 1 := by
  have h := card_sub_one_le_finrank_fpSpan_of_ker_le (ker_fpCoeff_factor_le hm)
  rw [ZMod.card] at h
  exact ⟨by omega, (finrank_rrSpan (m := m)).1⟩

/-- `2m - 2 ≤ dim R_rr ≤ 2m - 1` at prime `n = 2m - 1` (`rrSpan`, ham-spin 55c17eb). Now a case
of `finrank_rrSpan_of_two_le`, through the `P*` ladder rather than the Gram matrix `J + I`. -/
theorem finrank_rrSpan_of_prime (hp : (2 * m - 1).Prime) :
    2 * m - 2 ≤ Module.finrank F₂ (rrSpan m) ∧ Module.finrank F₂ (rrSpan m) ≤ 2 * m - 1 :=
  finrank_rrSpan_of_two_le (by have := hp.two_le; omega)

/-- For every `m ≥ 2`, `dim R_rr = 2m - 1` iff some `P` has odd `X(P)` (`rrSpan`, ham-spin
55c17eb; `hamCount`, ham_pairings main 978559a; `results/f2-slice-extend.md`, organize-archive
cd0ed47, Theorem 2.3). -/
theorem finrank_rrSpan_eq_iff_exists_odd_hamCount_of_two_le (hm : 2 ≤ m) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 1 ↔ ∃ P, Odd (hamCount m P) := by
  have h := finrank_fpSpan_eq_card_iff_exists_odd_of_ker_le (ker_fpCoeff_factor_le hm)
  rw [ZMod.card] at h
  exact h

/-- At prime `n = 2m - 1`, `dim R_rr = 2m - 1` iff some `P` has odd `X(P)` (`rrSpan`, ham-spin
55c17eb; `hamCount`, ham_pairings main 978559a). A case of
`finrank_rrSpan_eq_iff_exists_odd_hamCount_of_two_le`. -/
theorem finrank_rrSpan_eq_iff_exists_odd_hamCount (hp : (2 * m - 1).Prime) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 1 ↔ ∃ P, Odd (hamCount m P) :=
  finrank_rrSpan_eq_iff_exists_odd_hamCount_of_two_le (by have := hp.two_le; omega)

/-- For every `m ≥ 2`, `dim R_rr = 2m - 2` iff every `X(P)` is even, iff `Σ_t φ(F_t) = 0`
(`rrSpan`, ham-spin 55c17eb; `hamCount`, ham_pairings main 978559a; `results/f2-slice-extend.md`,
organize-archive cd0ed47, Theorem 2.2). -/
theorem finrank_rrSpan_eq_sub_two_iff_of_two_le (hm : 2 ≤ m) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 2 ↔ ∀ P, Even (hamCount m P) := by
  have h := finrank_fpSpan_eq_card_sub_one_iff_of_ker_le (ker_fpCoeff_factor_le hm)
  rw [ZMod.card, fpSum_eq_zero_iff, show 2 * m - 1 - 1 = 2 * m - 2 by omega] at h
  exact h

/-- At prime `n = 2m - 1`, `dim R_rr = 2m - 2` iff every `X(P)` is even, iff `Σ_t φ(F_t) = 0`
(`rrSpan`, ham-spin 55c17eb; `hamCount`, ham_pairings main 978559a). A case of
`finrank_rrSpan_eq_sub_two_iff_of_two_le`. -/
theorem finrank_rrSpan_eq_sub_two_iff (hp : (2 * m - 1).Prime) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 2 ↔ ∀ P, Even (hamCount m P) :=
  finrank_rrSpan_eq_sub_two_iff_of_two_le (by have := hp.two_le; omega)

/-- At prime `n = 2m - 1`, `Σ_t φ(F_t) ∈ R_rr ∩ R_rr^⊥` (`rrSpan`, `fpForm`, ham-spin fd082bf). -/
theorem fpSum_factor_mem_inf_orthogonal (hp : (2 * m - 1).Prime) :
    fpSum (factor m) ∈ rrSpan m ⊓ fpForm.orthogonal (rrSpan m) :=
  fpSum_mem_inf_orthogonal (ham_factor_iff_ne hp) (by rw [ZMod.card]; exact modulus_odd m)

/-- `dim R_rr = 2 = 2m - 2` at `m = 2`, since `dim W = 2^(m-1) = 2` (`rrSpan`, ham-spin
fd082bf). -/
theorem finrank_rrSpan_two : Module.finrank F₂ (rrSpan 2) = 2 := by
  have h1 := (finrank_rrSpan_of_prime (m := 2) Nat.prime_three).1
  have h2 := (finrank_rrSpan (m := 2)).2
  norm_num at h1 h2
  omega

/-- `dim R_rr = 4 = 2m - 2` at `m = 3`, since `dim W = 2^(m-1) = 4` (`rrSpan`, ham-spin
fd082bf). -/
theorem finrank_rrSpan_three : Module.finrank F₂ (rrSpan 3) = 4 := by
  have h1 := (finrank_rrSpan_of_prime (m := 3) Nat.prime_five).1
  have h2 := (finrank_rrSpan (m := 3)).2
  norm_num at h1 h2
  omega

/-- If, for every `t`, the alternating walk of `P ∪ F_t` from `∞` either visits every vertex or
closes up early, then `X(P)` counts the `t` of the first kind (`hamCount`, ham_pairings main
d1cda40; `altWalk`, `ClosedMiss`, ham_pairings main d1cda40). -/
theorem hamCount_eq_card_walk {P : PerfectMatching (Vertex m)} {j : ℕ}
    (h : ∀ t, (∀ w, w ∈ Covering.altWalk P.mate (mateFn t) j none) ∨
      Covering.ClosedMiss P.mate (mateFn t) (Covering.altWalk P.mate (mateFn t) j none)) :
    hamCount m P =
      (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk P.mate (mateFn t) j none).card := by
  rw [hamCount]
  congr 1
  refine Finset.filter_congr fun t _ ↦ ⟨fun hH ↦ ?_, Covering.ham_of_altWalk P (factor m t) j none⟩
  rcases h t with hw | hc
  · exact hw
  · exact absurd hH
      (Covering.not_ham_of_closedMiss P (factor m t) (Covering.mem_altWalk_self _ _ _ _) hc)

/-- The three-switch `Q_3 = F_0 - {∞0, 16, 34} + {∞1, 03, 64}` at `m = 4`, `n = 7`, as label pairs
with `7 = ∞` (`natPairs`, ham_pairings main d1cda40). `3` is a nonresidue mod `7`. -/
def switchSevenMate : Vertex 4 → Vertex 4 :=
  Covering.Witness.natPairs 4 [(7, 1), (0, 3), (6, 4), (2, 5)]

/-- `switchSevenMate` is an involution. -/
theorem switchSevenMate_mate : ∀ v, switchSevenMate (switchSevenMate v) = v := by
  decide +kernel

/-- `switchSevenMate` has no fixed point. -/
theorem switchSevenMate_ne : ∀ v, switchSevenMate v ≠ v := by
  decide +kernel

/-- The perfect matching `Q_3` of `V_4` (`mkMatching`, ham_pairings main d1cda40). -/
def switchSeven : PerfectMatching (Vertex 4) :=
  Covering.mkMatching switchSevenMate switchSevenMate_mate switchSevenMate_ne

/-- `Q_3 ∪ F_t` is one cycle for exactly `t = 2, 3, 4`, so `X(Q_3) = 3` (`hamCount`, ham_pairings
main d1cda40). -/
theorem hamCount_switchSeven : hamCount 4 switchSeven = 3 := by
  rw [hamCount_eq_card_walk (j := 4)]
  · change (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk switchSevenMate (mateFn t) 4 none).card =
      3
    decide +kernel
  · change ∀ t, (∀ w, w ∈ Covering.altWalk switchSevenMate (mateFn t) 4 none) ∨
      Covering.ClosedMiss switchSevenMate (mateFn t)
        (Covering.altWalk switchSevenMate (mateFn t) 4 none)
    decide +kernel

/-- `dim R_rr = 7 = 2m - 1` at `m = 4` (`rrSpan`, ham-spin fd082bf), witnessed by `X(Q_3) = 3`. -/
theorem finrank_rrSpan_four : Module.finrank F₂ (rrSpan 4) = 7 :=
  (finrank_rrSpan_eq_iff_exists_odd_hamCount (m := 4) (by decide)).mpr
    ⟨switchSeven, by rw [hamCount_switchSeven]; decide⟩

/-- The translates `Q + (s - (m + 2))` of `oneQ` form a biorthogonal dual family: the one indexed
by `s` closes one cycle with `F_t` exactly for `t = s`, for every `m ≥ 5` (`ham_shift_oneQ_iff`;
Proposition Q of `results/f2-slice-factcheck-extend.md`, organize-archive cd0ed47, §2, reviewed in
`results/one-factor-q-review.md`, organize-archive not committed yet, step 4). -/
theorem ham_shift_oneQ_biorthogonal (hm : 5 ≤ m) (s t : ZMod (2 * m - 1)) :
    Ham (shift m (s - ((m : ZMod (2 * m - 1)) + 2)) • oneQ m hm) (factor m t) ↔ t = s := by
  rw [ham_shift_oneQ_iff hm, add_sub_cancel]

/-- `dim R_rr = 2m - 1` for every `m ≥ 5`, prime or composite `n = 2m - 1` (`rrSpan`, ham-spin
55c17eb). The translates of `Q` are biorthogonal to the factors, so the `φ(F_t)` are independent.
This extends `finrank_rrSpan_of_prime` to composite `n` (`results/one-factor-q-review.md`,
organize-archive not committed yet, step 5; `results/f2-slice-factcheck-extend.md` and
`results/f2-slice-extend.md`, cd0ed47). -/
theorem finrank_rrSpan_of_five_le (hm : 5 ≤ m) : Module.finrank F₂ (rrSpan m) = 2 * m - 1 := by
  rw [rrSpan, finrank_fpSpan_eq_card_of_biorthogonal (fun s ↦ shift m
    (s - ((m : ZMod (2 * m - 1)) + 2)) • oneQ m hm) (Equiv.refl _)
    (ham_shift_oneQ_biorthogonal hm), ZMod.card]

/-- `dim R_rr = 2m - 1` for every `m ≥ 4` (`rrSpan`, ham-spin 55c17eb), from
`finrank_rrSpan_four` and `finrank_rrSpan_of_five_le` (`results/one-factor-q-review.md`,
organize-archive not committed yet). -/
theorem finrank_rrSpan_of_four_le (hm : 4 ≤ m) : Module.finrank F₂ (rrSpan m) = 2 * m - 1 := by
  rcases (by omega : m = 4 ∨ 5 ≤ m) with rfl | h5
  · exact finrank_rrSpan_four
  · exact finrank_rrSpan_of_five_le h5

/-- The three-switch `Q_2 = F_0 - {∞0, 1 10, 29} + {∞1, 02, 10 9}` at `m = 6`, `n = 11`, as label
pairs with `11 = ∞` (`natPairs`, ham_pairings main d1cda40). `2` is a nonresidue mod `11`. -/
def switchElevenMate : Vertex 6 → Vertex 6 :=
  Covering.Witness.natPairs 6 [(11, 1), (0, 2), (10, 9), (3, 8), (4, 7), (5, 6)]

/-- `switchElevenMate` is an involution. -/
theorem switchElevenMate_mate : ∀ v, switchElevenMate (switchElevenMate v) = v := by
  decide +kernel

/-- `switchElevenMate` has no fixed point. -/
theorem switchElevenMate_ne : ∀ v, switchElevenMate v ≠ v := by
  decide +kernel

/-- The perfect matching `Q_2` of `V_6` (`mkMatching`, ham_pairings main d1cda40). -/
def switchEleven : PerfectMatching (Vertex 6) :=
  Covering.mkMatching switchElevenMate switchElevenMate_mate switchElevenMate_ne

/-- `Q_2 ∪ F_t` is one cycle for exactly `t = 3, 5, 6, 7, 8, 9, 10`, so `X(Q_2) = 7` (`hamCount`,
ham_pairings main d1cda40). -/
theorem hamCount_switchEleven : hamCount 6 switchEleven = 7 := by
  rw [hamCount_eq_card_walk (j := 6)]
  · change (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk switchElevenMate (mateFn t) 6 none).card =
      7
    decide +kernel
  · change ∀ t, (∀ w, w ∈ Covering.altWalk switchElevenMate (mateFn t) 6 none) ∨
      Covering.ClosedMiss switchElevenMate (mateFn t)
        (Covering.altWalk switchElevenMate (mateFn t) 6 none)
    decide +kernel

/-- `dim R_rr = 11 = 2m - 1` at `m = 6` (`rrSpan`, ham-spin 55c17eb), a case of
`finrank_rrSpan_of_five_le`. `X(Q_2) = 7` (`hamCount_switchEleven`) is an independent odd
witness. This is the rank in `results/autgroup-side-effects.md` (d7b3fa2) [7]. -/
theorem finrank_rrSpan_six : Module.finrank F₂ (rrSpan 6) = 11 :=
  finrank_rrSpan_of_five_le (m := 6) (by norm_num)

/-- Corollary 6 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea). At prime
`n = 2m - 1`, `R_rr ∩ R_rr^⊥ = F₂ · Σ_t φ(F_t)` (`rrSpan`, `fpForm`, ham-spin fd082bf). This
upgrades `fpSum_factor_mem_inf_orthogonal` from membership to equality. -/
theorem rrSpan_inf_orthogonal_eq (hp : (2 * m - 1).Prime) :
    rrSpan m ⊓ fpForm.orthogonal (rrSpan m) = Submodule.span F₂ {fpSum (factor m)} :=
  fpSpan_inf_orthogonal_eq_of_odd (ham_factor_iff_ne hp) (by rw [ZMod.card]; exact modulus_odd m)

/-- `Σ_t φ(F_t) ≠ 0` for every `m ≥ 4`, prime or composite `n = 2m - 1` (`fpSum`, `factor`,
ham-spin fd082bf), from `finrank_rrSpan_of_four_le` and the `P*` ladder. -/
theorem fpSum_factor_ne_zero (hm : 4 ≤ m) : fpSum (factor m) ≠ 0 :=
  (finrank_fpSpan_eq_card_iff_of_ker_le (ker_fpCoeff_factor_le (by omega))).mp
    (by rw [ZMod.card]; exact finrank_rrSpan_of_four_le hm)

/-- Corollary 6 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea), prime case.
At prime `n = 2m - 1 ≥ 7` the radical `R_rr ∩ R_rr^⊥` is the line `F₂ · Σ_t φ(F_t)`, of dimension
`1` (`rrSpan`, `fpForm`, ham-spin fd082bf). -/
theorem finrank_rrSpan_inf_orthogonal (hp : (2 * m - 1).Prime) (hm : 4 ≤ m) :
    Module.finrank F₂ (rrSpan m ⊓ fpForm.orthogonal (rrSpan m) : Submodule F₂ (W (Vertex m))) =
      1 := by
  rw [rrSpan_inf_orthogonal_eq hp]
  exact finrank_span_singleton (fpSum_factor_ne_zero hm)

end Pairing.RoundRobin.Canonical
