import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Repair.PairRecursion

/-!
# The exact variance identity for a fixed context family (Theorem 2)

Source: `results/hybrid-pair-averaged.md` (aed6f2d), §3, Theorem 2.

`B` is a perfect matching of a finite set `W`, and `C : ι → PM(W)` is a family of contexts with
every `C_t ∪ B` one cycle. `R` is uniform on `PM(W)` and `X(R) = #{t : R ∪ C_t one cycle}`.
`h(A, C) = 1` iff `A ∪ C` is one cycle, and `H` is the matrix of `h`, the adjacency matrix of the
Hamiltonian relation `(e)`.

* `f_E = Σ_t δ_{C_t}` is `ctxMeasure`, `u_B = 1_{Ham(B)} / |Ham(B)|` is `hamUnif`, and
  `g_E = f_E - (n - 1) u_B` is `ctxDefect`, with `n - 1 = |ι|`.
* `p = |Ham(B)| / |PM|` is `hamProbOf`, the probability that `R ∪ B` is one cycle, and
  `hamProbOf_eq_hamProb` : it equals the closed form `hamProb e = 2^(e-1)(e-1)!/(2e-1)!!`.
* `Γ(E) = |PM| · ‖H g_E‖² / |Ham(B)|²` is `coherence`, and
  `c_gen(e) = |PM| · Σ_R #{A : R ∪ A, A ∪ B one cycle}² / |Ham(B)|⁴ - 1` is `cGen`.
* `HamSpectral` : a spectral resolution of `H` by symmetric orthogonal idempotents `E_ν` with
  `H E_ν = λ_ν E_ν`, constant diagonal and `E_{(e)} = J / |PM|`. For the Gelfand pair
  `(S_{2e}, H_e)` these are the projections onto the `V_ν`, with `λ_ν = |Ham(B)| ω_ν((e))` by the
  proof of Theorem 1. That identification is an input, not formalized here.
* `spectral_coherence`, `spectral_cGen` : for every such resolution,
  `Γ(E) = |PM| Σ_{ν ≠ (e)} ω_ν((e))² ‖E_ν g_E‖²` and `c_gen(e) = Σ_{ν ≠ (e)} d_ν ω_ν((e))⁴` with
  `ω_ν((e)) = λ_ν / |Ham(B)|` and `d_ν = tr E_ν`, the source's definitions.
* `mean_ctxCount` : `E_R X = (n - 1) p`.
* `var_ctxCount` : `Var_R X = p² [(n - 1)² c_gen + Γ(E)]`, and `coherence_nonneg` : `Γ ≥ 0`.
* `exists_smul_eq_of_ham` : the stabiliser of `B` acts transitively on `Ham(B)`. This is the
  fact behind the vanishing cross term `⟨E_ν u_B, E_ν g_E⟩ = 0`.
-/

open Finset

namespace Pairing

namespace PerfectMatching

section Transitive

variable {V : Type*} [Fintype V] [DecidableEq V] {F0 F1 : PerfectMatching V}

/-- `F_{(k+1) mod 2}(c_k) = c_{k + 2a - 1}`, the backward step of the alternating walk
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem stepMatching_succ_mate_alt (v : V) (k : ℕ) :
    (stepMatching F0 F1 (k + 1)).mate (alt F0 F1 v k) =
      alt F0 F1 v (k + cycLen F0 F1 v - 1) := by
  rw [← alt_add_cycLen v k]
  obtain ⟨L, hL⟩ : ∃ L, cycLen F0 F1 v = L + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (cycLen_pos v)).symm⟩
  have he := cycLen_even (F0 := F0) (F1 := F1) v
  rw [hL, ← add_assoc, stepMatching_congr (l := k + L) (by omega), mate_alt_succ,
    Nat.add_sub_cancel]

/-- `F₀(c_k)` is `c_{k+1}` for even `k` and `c_{k + 2a - 1}` for odd `k`
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem mate_zero_alt (v : V) (k : ℕ) :
    F0.mate (alt F0 F1 v k) =
      if k % 2 = 0 then alt F0 F1 v (k + 1) else alt F0 F1 v (k + cycLen F0 F1 v - 1) := by
  split_ifs with hk
  · rw [alt_succ, stepMatching_of_even hk]
  · rw [← stepMatching_succ_mate_alt, stepMatching_of_even (by omega)]

/-- `F₁(c_k)` is `c_{k + 2a - 1}` for even `k` and `c_{k+1}` for odd `k`
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem mate_one_alt (v : V) (k : ℕ) :
    F1.mate (alt F0 F1 v k) =
      if k % 2 = 0 then alt F0 F1 v (k + cycLen F0 F1 v - 1) else alt F0 F1 v (k + 1) := by
  split_ifs with hk
  · rw [← stepMatching_succ_mate_alt, stepMatching_of_odd (by omega)]
  · rw [alt_succ, stepMatching_of_odd (by omega)]

/-- For a Hamiltonian pair the cycle through `v` is all of `V`
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem cycLen_of_ham (h : Ham F0 F1) (v : V) : cycLen F0 F1 v = Fintype.card V := by
  rw [← card_cycleOf, ← card_univ]
  congr 1
  ext x
  simp only [mem_cycleOf, mem_univ, iff_true]
  exact h.preconnected v x

omit [Fintype V] [DecidableEq V] in
/-- The stabiliser of `B` acts transitively on the matchings `C` with `B ∪ C` one cycle
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem exists_smul_eq_of_ham [Finite V] {B C C' : PerfectMatching V} (hC : Ham B C)
    (hC' : Ham B C') : ∃ σ : Equiv.Perm V, σ • B = B ∧ σ • C = C' := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨v⟩ := hC.nonempty
  have hL := cycLen_of_ham hC v
  have hL' := cycLen_of_ham hC' v
  have hex : ∀ x, ∃ k, alt B C v k = x := fun x ↦ mem_cyc.mp (by
    rw [← cycleOf_eq_cyc, mem_cycleOf]
    exact hC.preconnected v x)
  have hex' : ∀ x, ∃ k, alt B C' v k = x := fun x ↦ mem_cyc.mp (by
    rw [← cycleOf_eq_cyc, mem_cycleOf]
    exact hC'.preconnected v x)
  let φ : V → V := fun x ↦ alt B C' v (Nat.find (hex x))
  have hφ : ∀ k, φ (alt B C v k) = alt B C' v k := by
    intro k
    have hs := Nat.find_spec (hex (alt B C v k))
    have hm : Nat.find (hex (alt B C v k)) % Fintype.card V = k % Fintype.card V := by
      have h1 := alt_mod (F0 := B) (F1 := C) v (Nat.find (hex (alt B C v k)))
      have h2 := alt_mod (F0 := B) (F1 := C) v k
      rw [hL] at h1 h2
      have hpos : 0 < Fintype.card V := hL ▸ cycLen_pos v
      exact alt_injOn (by rw [hL]; exact Nat.mod_lt _ hpos) (by rw [hL]; exact Nat.mod_lt _ hpos)
        (by rw [h1, h2, hs])
    change alt B C' v (Nat.find (hex (alt B C v k))) = alt B C' v k
    rw [← alt_mod (F0 := B) (F1 := C') v (Nat.find _), ← alt_mod (F0 := B) (F1 := C') v k, hL',
      hm]
  have hsurj : Function.Surjective φ := fun y ↦ by
    obtain ⟨k, rfl⟩ := hex' y
    exact ⟨_, hφ k⟩
  let σ : Equiv.Perm V := Equiv.ofBijective φ (Finite.surjective_iff_bijective.mp hsurj)
  have hσ : ∀ k, σ (alt B C v k) = alt B C' v k := hφ
  have hsmul : ∀ (P Q : PerfectMatching V) (hPQ : ∀ k, σ (P.mate (alt B C v k)) =
      Q.mate (alt B C' v k)), σ • P = Q := by
    intro P Q hPQ
    ext y
    obtain ⟨k, rfl⟩ := hex' y
    rw [smul_mate, ← hσ, show σ⁻¹ (σ (alt B C v k)) = alt B C v k from
      Equiv.Perm.inv_eq_iff_eq.mpr rfl, hPQ, hσ]
  refine ⟨σ, hsmul B B fun k ↦ ?_, hsmul C C' fun k ↦ ?_⟩
  · rw [mate_zero_alt, mate_zero_alt, hL, hL']
    split_ifs <;> exact hσ _
  · rw [mate_one_alt, mate_one_alt, hL, hL']
    split_ifs <;> exact hσ _

end Transitive

section Variance

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `h(A, C) = 1` if `A ∪ C` is one cycle and `0` otherwise, the entries of `H`
(`results/hybrid-pair-averaged.md`, §1). -/
def hamInd (A C : PerfectMatching W) : ℝ :=
  if Ham A C then 1 else 0

/-- `|Ham(B)|`, the number of `C` with `C ∪ B` one cycle (`results/hybrid-pair-averaged.md`,
§1). -/
def hamDeg (B : PerfectMatching W) : ℕ :=
  #{C : PerfectMatching W | Ham C B}

/-- `p = P_R(R ∪ B one cycle) = |Ham(B)| / |PM|` (`results/hybrid-pair-averaged.md`, §1). -/
noncomputable def hamProbOf (B : PerfectMatching W) : ℝ :=
  hamDeg B / Fintype.card (PerfectMatching W)

/-- The mean of `Y` under the uniform `R ∈ PM` (`results/hybrid-pair-averaged.md`, §1). -/
noncomputable def pmMean (Y : PerfectMatching W → ℝ) : ℝ :=
  (∑ R, Y R) / Fintype.card (PerfectMatching W)

/-- The variance of `Y` under the uniform `R ∈ PM` (`results/hybrid-pair-averaged.md`, §1). -/
noncomputable def pmVar (Y : PerfectMatching W → ℝ) : ℝ :=
  (∑ R, (Y R - pmMean Y) ^ 2) / Fintype.card (PerfectMatching W)

variable {ι : Type*} [Fintype ι]

/-- `X(R) = #{t : R ∪ C_t one cycle}` (`results/hybrid-pair-averaged.md`, §1). -/
def ctxCount (C : ι → PerfectMatching W) (R : PerfectMatching W) : ℕ :=
  #{t | Ham R (C t)}

/-- `f_E = Σ_t δ_{C_t}` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
def ctxMeasure (C : ι → PerfectMatching W) (A : PerfectMatching W) : ℝ :=
  #{t | C t = A}

/-- `u_B = 1_{Ham(B)} / |Ham(B)|` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
noncomputable def hamUnif (B A : PerfectMatching W) : ℝ :=
  hamInd A B / hamDeg B

/-- `g_E = f_E - (n - 1) u_B` with `n - 1 = |ι|` (`results/hybrid-pair-averaged.md`,
Theorem 2). -/
noncomputable def ctxDefect (B : PerfectMatching W) (C : ι → PerfectMatching W)
    (A : PerfectMatching W) : ℝ :=
  ctxMeasure C A - Fintype.card ι * hamUnif B A

/-- `(H g)(R) = Σ_A h(R, A) g(A)` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
def hamApply (g : PerfectMatching W → ℝ) (R : PerfectMatching W) : ℝ :=
  ∑ A, hamInd R A * g A

/-- `Γ(E) = |PM| ‖H g_E‖² / |Ham(B)|²`, which is `|PM| Σ_{ν ≠ (e)} ω_ν((e))² ‖E_ν g_E‖²` by
`spectral_coherence` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
noncomputable def coherence (B : PerfectMatching W) (C : ι → PerfectMatching W) : ℝ :=
  Fintype.card (PerfectMatching W) / (hamDeg B : ℝ) ^ 2 * ∑ R, hamApply (ctxDefect B C) R ^ 2

/-- `c_gen(e) = |PM| ‖H² δ_B‖² / |Ham(B)|⁴ - 1`, which is `Σ_{ν ≠ (e)} d_ν ω_ν((e))⁴` by
`spectral_cGen` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
noncomputable def cGen (B : PerfectMatching W) : ℝ :=
  Fintype.card (PerfectMatching W) / (hamDeg B : ℝ) ^ 4 *
    ∑ R, (∑ A, hamInd R A * hamInd A B) ^ 2 - 1

/-- `h(σA, σC) = h(A, C)`: relabelling preserves one-cycle unions
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem hamInd_smul (σ : Equiv.Perm W) (A C : PerfectMatching W) :
    hamInd (σ • A) (σ • C) = hamInd A C := by
  simp [hamInd, ham_smul]

/-- `Σ_R h(R, A) = |Ham(A)|` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem sum_hamInd (A : PerfectMatching W) : ∑ R, hamInd R A = hamDeg A := by
  simp [hamInd, hamDeg, sum_boole]

/-- `|Ham(A)| = |Ham(B)|` for all `A`, `B`, since `S_W` acts transitively on `PM`
(`results/hybrid-pair-averaged.md`, §1). -/
theorem hamDeg_eq (A B : PerfectMatching W) : hamDeg A = hamDeg B := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq (two_mul_sum_pairType B B).symm B A
  have h : ∑ R, hamInd R B = ∑ R, hamInd R (σ • B) :=
    Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun R ↦ (hamInd_smul σ R B).symm
  rw [sum_hamInd, sum_hamInd] at h
  exact_mod_cast h.symm

/-- `D(R) = (H² δ_B)(R) = #{A : R ∪ A, A ∪ B one cycle}` (`results/hybrid-pair-averaged.md`,
Theorem 2). -/
def hamTwo (B R : PerfectMatching W) : ℝ :=
  ∑ A, hamInd R A * hamInd A B

/-- `(H³ δ_B)(C) = Σ_R h(R, C) D(R)` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
def hamThree (B C : PerfectMatching W) : ℝ :=
  ∑ R, hamInd R C * hamTwo B R

/-- `H³(C, B)` takes one value on `Ham(B)`, by `exists_smul_eq_of_ham`. This is the cross-term
cancellation of the source (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem hamThree_eq {B C C' : PerfectMatching W} (hC : Ham C B) (hC' : Ham C' B) :
    hamThree B C = hamThree B C' := by
  obtain ⟨σ, hB, rfl⟩ := exists_smul_eq_of_ham ((ham_comm _ _).mp hC) ((ham_comm _ _).mp hC')
  have hD : ∀ R, hamTwo B R = hamTwo B (σ • R) := by
    intro R
    refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun A ↦ ?_
    simp only [MulAction.toPerm_apply]
    conv_rhs => rw [← hB]
    rw [hamInd_smul, hamInd_smul]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun R ↦ ?_
  simp only [MulAction.toPerm_apply]
  rw [hamInd_smul, ← hD]

/-- `X(R) = Σ_t h(R, C_t)` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem cast_ctxCount (C : ι → PerfectMatching W) (R : PerfectMatching W) :
    (ctxCount C R : ℝ) = ∑ t, hamInd R (C t) := by
  simp [ctxCount, hamInd, sum_boole]

/-- `(H g_E)(R) = X(R) - (n - 1) D(R) / |Ham(B)|` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem hamApply_ctxDefect (B : PerfectMatching W) (C : ι → PerfectMatching W)
    (R : PerfectMatching W) :
    hamApply (ctxDefect B C) R = ctxCount C R - Fintype.card ι * hamTwo B R / hamDeg B := by
  have h1 : ∑ A, hamInd R A * ctxMeasure C A = ∑ t, hamInd R (C t) := by
    simp only [ctxMeasure, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum, mul_one]
    exact sum_fiberwise' univ C (fun A ↦ hamInd R A)
  rw [hamApply, cast_ctxCount, ← h1, hamTwo, mul_sum, sum_div, ← sum_sub_distrib]
  refine sum_congr rfl fun A _ ↦ ?_
  rw [ctxDefect, hamUnif]
  ring

/-- `E_R X = (n - 1) p` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem mean_ctxCount (B : PerfectMatching W) (C : ι → PerfectMatching W) :
    pmMean (fun R ↦ (ctxCount C R : ℝ)) = Fintype.card ι * hamProbOf B := by
  rw [pmMean, hamProbOf]
  simp only [cast_ctxCount]
  rw [sum_comm]
  simp only [sum_hamInd, hamDeg_eq _ B, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- `Γ(E) ≥ 0` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem coherence_nonneg (B : PerfectMatching W) (C : ι → PerfectMatching W) :
    0 ≤ coherence B C := by
  unfold coherence
  positivity

/-- Theorem 2, the exact variance identity `Var_R(X | E) = p² [(n - 1)² c_gen(e) + Γ(E)]`, for
any family of contexts `C_t` with every `C_t ∪ B` one cycle
(`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem var_ctxCount [Nonempty ι] (B : PerfectMatching W) (C : ι → PerfectMatching W)
    (hC : ∀ t, Ham (C t) B) :
    pmVar (fun R ↦ (ctxCount C R : ℝ)) =
      hamProbOf B ^ 2 * ((Fintype.card ι : ℝ) ^ 2 * cGen B + coherence B C) := by
  obtain ⟨t₀⟩ := ‹Nonempty ι›
  set N : ℝ := (Fintype.card (PerfectMatching W) : ℝ) with hN
  set k : ℝ := (hamDeg B : ℝ) with hk
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set c₃ := hamThree B (C t₀) with hc₃
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨B⟩
  have hkpos : 0 < k := by
    rw [hk]
    exact_mod_cast card_pos.mpr ⟨C t₀, mem_filter.mpr ⟨mem_univ _, hC t₀⟩⟩
  set X : PerfectMatching W → ℝ := fun R ↦ (ctxCount C R : ℝ) with hX
  set D : PerfectMatching W → ℝ := fun R ↦ hamTwo B R with hD
  have hmean : pmMean X = n * k / N := by
    rw [mean_ctxCount B C, hamProbOf]
    ring
  have hXD : ∑ R, X R * D R = n * c₃ := by
    have e : ∀ t, ∑ R, hamInd R (C t) * hamTwo B R = c₃ := fun t ↦ hamThree_eq (hC t) (hC t₀)
    simp only [hX, hD, cast_ctxCount, sum_mul]
    rw [sum_comm, sum_congr rfl fun t _ ↦ e t, sum_const, card_univ, nsmul_eq_mul]
  have hDD : ∑ R, D R ^ 2 = k * c₃ := by
    have h1 : ∑ R, D R ^ 2 = ∑ A, hamInd A B * hamThree B A := by
      have e : ∀ R, D R ^ 2 = ∑ A, hamInd A B * (hamInd R A * hamTwo B R) := by
        intro R
        have h' : ∑ A, hamInd A B * (hamInd R A * hamTwo B R) =
            (∑ A, hamInd R A * hamInd A B) * hamTwo B R := by
          rw [sum_mul]
          exact sum_congr rfl fun A _ ↦ by ring
        rw [h', hD, sq]
        rfl
      rw [sum_congr rfl fun R _ ↦ e R, sum_comm]
      simp only [hamThree, mul_sum]
    rw [h1]
    have h2 : ∀ A, hamInd A B * hamThree B A = hamInd A B * c₃ := by
      intro A
      by_cases hA : Ham A B
      · rw [hamThree_eq hA (hC t₀)]
      · simp [hamInd, hA]
    rw [sum_congr rfl fun A _ ↦ h2 A, ← sum_mul, sum_hamInd]
  have hvar : pmVar X = (∑ R, X R ^ 2) / N - (n * k / N) ^ 2 := by
    rw [pmVar, ← hmean]
    have hs : ∑ R, X R = N * pmMean X := by
      rw [pmMean, ← hN]
      field_simp
    have : ∑ R, (X R - pmMean X) ^ 2 = ∑ R, X R ^ 2 - N * pmMean X ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← sum_mul, ← mul_sum, hs, ← hN]
      ring
    rw [this, ← hN]
    field_simp
  have hG : coherence B C = N / k ^ 2 * (∑ R, X R ^ 2 - 2 * (n / k) * (n * c₃) +
      (n / k) ^ 2 * (k * c₃)) := by
    have e : ∀ R, hamApply (ctxDefect B C) R ^ 2 =
        X R ^ 2 - 2 * (n / k) * (X R * D R) + (n / k) ^ 2 * D R ^ 2 := by
      intro R
      rw [hamApply_ctxDefect]
      simp only [hX, hD, hn, hk]
      ring
    rw [coherence, ← hN, ← hk, sum_congr rfl fun R _ ↦ e R, sum_add_distrib, sum_sub_distrib,
      ← mul_sum, ← mul_sum, hXD, hDD]
  have hc : cGen B = N / k ^ 4 * (k * c₃) - 1 := by
    rw [cGen, ← hN, ← hk, ← hDD]
    rfl
  rw [hvar, hG, hc, hamProbOf, ← hN, ← hk]
  field_simp
  ring

end Variance

section ClosedForm

universe u

/-- `|Ham(A)| = 2^(e-1) (e-1)!` on `2e` points, by the reduction of Lemma K2
(`results/hybrid-pair-averaged.md`, §1). -/
theorem hamDeg_eq_closed (e : ℕ) : ∀ (W : Type u) [Fintype W] [DecidableEq W],
    Fintype.card W = 2 * (e + 1) → ∀ A : PerfectMatching W,
      hamDeg A = 2 ^ e * e.factorial := by
  induction e with
  | zero =>
    intro W _ _ hW A
    have h := jointCount_of_card_eq_two A A hW
    simp only [jointCount, and_self] at h
    simpa [hamDeg] using h
  | succ e ih =>
    intro W _ _ hW A
    obtain ⟨x⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    have h1 : hamDeg A = jointCount A A := by
      simp only [hamDeg, jointCount, and_self]
    have h2 : ∀ u ∈ ((univ.erase x).erase (A.mate x)).erase (A.mate x),
        redCount A A x u = 2 ^ e * e.factorial := by
      intro u hu
      simp only [mem_erase, mem_univ, and_true] at hu
      have hxu : x ≠ u := Ne.symm hu.2.2
      rw [redCount, dite_eq_right hxu]
      have h3 := ih (redSet x u) (by rw [Fintype.card_coe, card_redSet hxu, hW]; ring_nf; omega)
        (red A hxu)
      simpa [hamDeg, jointCount] using h3
    rw [h1, jointCount_eq_sum_redCount A A x (by omega), sum_congr rfl h2, sum_const, smul_eq_mul,
      erase_idem, card_erase_of_mem (mem_erase.mpr ⟨A.mate_ne x, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ, hW, pow_succ, Nat.factorial_succ]
    rw [show 2 * (e + 1 + 1) - 1 - 1 = 2 * (e + 1) by omega]
    ring

/-- `p = |Ham(B)| / |PM| = 2^(e-1)(e-1)!/(2e-1)!!`, main's closed form `hamProb e`
(`results/hybrid-pair-averaged.md`, §1). -/
theorem hamProbOf_eq_hamProb {W : Type u} [Fintype W] [DecidableEq W] {e : ℕ}
    (hW : Fintype.card W = 2 * e) (he : 1 ≤ e) (B : PerfectMatching W) :
    hamProbOf B = hamProb e := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  rw [hamProbOf, hamProb, hamDeg_eq_closed f W hW B, card_eq_doubleFactorial hW,
    Nat.add_sub_cancel]
  push_cast
  rfl

end ClosedForm

section Spectral

open scoped Matrix

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `H`, the real matrix of the Hamiltonian relation `(e)` on `PM`
(`results/hybrid-pair-averaged.md`, Theorem 1). -/
def hamMat : Matrix (PerfectMatching W) (PerfectMatching W) ℝ :=
  Matrix.of hamInd

/-- A spectral resolution of `H`: symmetric orthogonal idempotents `E_ν` with `Σ_ν E_ν = 1`,
`H E_ν = λ_ν E_ν`, constant diagonal, and `E_{(e)} = J / |PM|`. For the Gelfand pair
`(S_{2e}, H_e)`, `E_ν` is the projection onto `V_ν` and `λ_ν = |Ham(B)| ω_ν((e))` by the proof of
Theorem 1; these facts about spherical functions are the inputs here, not proved
(`results/hybrid-pair-averaged.md`, Theorems 1 and 2). -/
structure HamSpectral (W : Type*) [Fintype W] [DecidableEq W] (I : Type*) [Fintype I]
    [DecidableEq I] where
  /-- The projection `E_ν` onto `V_ν`. -/
  E : I → Matrix (PerfectMatching W) (PerfectMatching W) ℝ
  /-- The eigenvalue `λ_ν` of `H` on `V_ν`. -/
  eig : I → ℝ
  /-- The trivial index `ν = (e)`. -/
  triv : I
  sum_E : ∑ ν, E ν = 1
  transpose_E : ∀ ν, (E ν)ᵀ = E ν
  mul_E : ∀ ν ν', E ν * E ν' = if ν = ν' then E ν else 0
  ham_mul_E : ∀ ν, hamMat * E ν = eig ν • E ν
  diag_E : ∀ ν A A', E ν A A = E ν A' A'
  E_triv : E triv = (Fintype.card (PerfectMatching W) : ℝ)⁻¹ • Matrix.of fun _ _ ↦ 1

/-- `H` is symmetric (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem hamMat_symm (A C : PerfectMatching W) : (hamMat : Matrix _ _ ℝ) A C = hamMat C A := by
  simp [hamMat, hamInd, ham_comm A C]

/-- `h(A, C) = h(C, A)` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem hamInd_comm (A C : PerfectMatching W) : hamInd A C = hamInd C A := by
  simp [hamInd, ham_comm A C]

/-- `Hᵀ = H` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem transpose_hamMat : (hamMat : Matrix (PerfectMatching W) (PerfectMatching W) ℝ)ᵀ =
    hamMat := by
  ext A C
  exact hamMat_symm C A

/-- `Σ_R ((M x)(R))² = x · M² x` for a symmetric `M` (`results/hybrid-pair-averaged.md`,
Theorem 2). -/
theorem sum_sq_mulVec (M : Matrix (PerfectMatching W) (PerfectMatching W) ℝ) (hM : Mᵀ = M)
    (x : PerfectMatching W → ℝ) : ∑ R, (M *ᵥ x) R ^ 2 = x ⬝ᵥ ((M * M) *ᵥ x) := by
  have h : ∑ R, (M *ᵥ x) R ^ 2 = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
    simp only [dotProduct, sq]
  rw [h]
  nth_rw 1 [← Matrix.vecMul_transpose]
  rw [hM, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

namespace HamSpectral

variable {I : Type*} [Fintype I] [DecidableEq I] (S : HamSpectral W I)

/-- `(Σ_ν a_ν E_ν)(Σ_ν b_ν E_ν) = Σ_ν a_ν b_ν E_ν` (`results/hybrid-pair-averaged.md`,
Theorem 1). -/
theorem sum_smul_mul_sum_smul (a b : I → ℝ) :
    (∑ ν, a ν • S.E ν) * (∑ ν, b ν • S.E ν) = ∑ ν, (a ν * b ν) • S.E ν := by
  rw [Matrix.sum_mul]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [Matrix.mul_sum, sum_eq_single ν]
  · rw [Matrix.smul_mul, Matrix.mul_smul, S.mul_E, ite_eq_left rfl, smul_smul, mul_comm]
  · intro ν' _ hne
    rw [Matrix.smul_mul, Matrix.mul_smul, S.mul_E, ite_eq_right (Ne.symm hne), smul_zero, smul_zero]
  · intro h
    exact absurd (mem_univ ν) h

/-- `H = Σ_ν λ_ν E_ν` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem hamMat_eq : (hamMat : Matrix (PerfectMatching W) (PerfectMatching W) ℝ) =
    ∑ ν, S.eig ν • S.E ν := by
  rw [← Matrix.mul_one hamMat, ← S.sum_E, Matrix.mul_sum]
  exact sum_congr rfl fun ν _ ↦ S.ham_mul_E ν

/-- `λ_{(e)} = |Ham(B)|` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem eig_triv (B : PerfectMatching W) : S.eig S.triv = hamDeg B := by
  have hNinv : (Fintype.card (PerfectMatching W) : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne')
  have hrow : ∑ R, (hamMat : Matrix _ _ ℝ) B R = hamDeg B := by
    simp_rw [hamMat_symm B]
    exact sum_hamInd B
  have h := congrFun (congrFun (S.ham_mul_E S.triv) B) B
  simp only [S.E_triv, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul,
    mul_one] at h
  rw [← sum_mul, hrow] at h
  exact mul_right_cancel₀ hNinv h.symm

/-- `tr E_{(e)} = 1` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem trace_triv (B : PerfectMatching W) : (S.E S.triv).trace = 1 := by
  rw [S.E_triv, Matrix.trace_smul, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.of_apply, sum_const, card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne')

/-- `d_ν = tr E_ν = |PM| E_ν(B, B)` (`results/hybrid-pair-averaged.md`, Theorem 1). -/
theorem trace_eq (ν : I) (B : PerfectMatching W) :
    (S.E ν).trace = Fintype.card (PerfectMatching W) * S.E ν B B := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, S.diag_E ν _ B, sum_const, card_univ, nsmul_eq_mul]

/-- `x · (Σ_ν c_ν E_ν) x = Σ_ν c_ν (x · E_ν x)` (`results/hybrid-pair-averaged.md`,
Theorem 2). -/
theorem dotProduct_sum_smul_mulVec (c : I → ℝ) (x : PerfectMatching W → ℝ) :
    x ⬝ᵥ ((∑ ν, c ν • S.E ν) *ᵥ x) = ∑ ν, c ν * (x ⬝ᵥ (S.E ν *ᵥ x)) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- `‖E_ν x‖² = x · E_ν x` (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem sum_sq_E_mulVec (ν : I) (x : PerfectMatching W → ℝ) :
    ∑ R, (S.E ν *ᵥ x) R ^ 2 = x ⬝ᵥ (S.E ν *ᵥ x) := by
  rw [sum_sq_mulVec _ (S.transpose_E ν), S.mul_E, ite_eq_left rfl]

/-- `c_gen(e) = Σ_{ν ≠ (e)} d_ν ω_ν((e))⁴` with `d_ν = tr E_ν` and `ω_ν((e)) = λ_ν / |Ham(B)|`,
the source's definition (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem spectral_cGen (B : PerfectMatching W) (hk : hamDeg B ≠ 0) :
    cGen B = ∑ ν ∈ univ.erase S.triv, (S.E ν).trace * (S.eig ν / hamDeg B) ^ 4 := by
  have hN : (Fintype.card (PerfectMatching W) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne'
  have hk' : (hamDeg B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hD : ∑ R, (∑ A, hamInd R A * hamInd A B) ^ 2 =
      ((hamMat * hamMat) * (hamMat * hamMat) : Matrix _ _ ℝ) B B := by
    rw [Matrix.mul_apply]
    refine sum_congr rfl fun R _ ↦ ?_
    rw [sq, Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    refine sum_congr rfl fun A _ ↦ ?_
    simp only [hamMat, Matrix.of_apply]
    rw [hamInd_comm B A, hamInd_comm A R, mul_comm]
  have h2 : ∀ ν, (Fintype.card (PerfectMatching W) : ℝ) / (hamDeg B : ℝ) ^ 4 *
      (((S.eig ν * S.eig ν) * (S.eig ν * S.eig ν)) • S.E ν) B B =
        (S.E ν).trace * (S.eig ν / hamDeg B) ^ 4 := by
    intro ν
    rw [Matrix.smul_apply, smul_eq_mul, S.trace_eq ν B]
    field_simp
  rw [cGen, hD, S.hamMat_eq, S.sum_smul_mul_sum_smul, S.sum_smul_mul_sum_smul, Matrix.sum_apply,
    mul_sum, sum_congr rfl fun ν _ ↦ h2 ν, ← add_sum_erase _ _ (mem_univ S.triv), S.trace_triv B,
    S.eig_triv B, div_self hk']
  ring

/-- `Γ(E) = |PM| Σ_{ν ≠ (e)} ω_ν((e))² ‖E_ν g_E‖²` with `ω_ν((e)) = λ_ν / |Ham(B)|`, the
source's definition (`results/hybrid-pair-averaged.md`, Theorem 2). -/
theorem spectral_coherence {ι : Type*} [Fintype ι] (B : PerfectMatching W)
    (C : ι → PerfectMatching W) (hk : hamDeg B ≠ 0) :
    coherence B C = Fintype.card (PerfectMatching W) * ∑ ν ∈ univ.erase S.triv,
      (S.eig ν / hamDeg B) ^ 2 * ∑ R, (S.E ν *ᵥ ctxDefect B C) R ^ 2 := by
  have hk' : (hamDeg B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  set g := ctxDefect B C with hg
  have hsum : ∑ A, g A = 0 := by
    have h1 : ∑ A, ctxMeasure C A = Fintype.card ι := by
      simp only [ctxMeasure]
      rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun t _ ↦ mem_univ (C t)), card_univ]
    have h2 : ∑ A, hamUnif B A = 1 := by
      simp only [hamUnif, ← sum_div, sum_hamInd]
      exact div_self hk'
    simp only [hg, ctxDefect, sum_sub_distrib, ← mul_sum, h1, h2, mul_one, sub_self]
  have htriv : g ⬝ᵥ (S.E S.triv *ᵥ g) = 0 := by
    have : S.E S.triv *ᵥ g = 0 := by
      ext R
      rw [S.E_triv, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, hsum, mul_zero]
    rw [this, dotProduct_zero]
  have hH : ∑ R, hamApply g R ^ 2 = ∑ ν, S.eig ν ^ 2 * (g ⬝ᵥ (S.E ν *ᵥ g)) := by
    have e : ∀ R, hamApply g R = (hamMat *ᵥ g) R := fun R ↦ rfl
    simp only [e]
    rw [sum_sq_mulVec _ transpose_hamMat, S.hamMat_eq, S.sum_smul_mul_sum_smul,
      S.dotProduct_sum_smul_mulVec]
    simp only [sq]
  rw [coherence, ← hg, hH, ← add_sum_erase _ _ (mem_univ S.triv), htriv, mul_zero, zero_add,
    mul_sum, mul_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [S.sum_sq_E_mulVec]
  field_simp

end HamSpectral

end Spectral

end PerfectMatching

end Pairing
