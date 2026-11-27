import Repair.PairLevelOne
import Repair.RandomFamily.Nonvacuity

/-!
# The level reduction of `cGen` (COD-291)

Source: `results/q-second-moment-extend.md` §3, Lemma 2 (organize-archive af8925f). `|W| = 2e`
with `e ≥ 2`, `N = |PM|`, `D = |Ham(B)|`, `H` is the Hamiltonian adjacency of
`repair/Repair/PairVariance.lean` (`hamApply`) and `E₁ = levelOneKer e` is the level-1 kernel of
`repair/Repair/PairLevelOne.lean`, with `H E₁ = λ₁ E₁`, `λ₁ = -D/(2(e - 1))`, `tr E₁ = d₁ =
e(2e - 3)`. So `w₁ = λ₁/D = -1/(2(e - 1))` and `c₁ = d₁ w₁⁴ = e(2e - 3)/(16(e - 1)⁴)`.

No spectral theorem and no `HamSpectral` resolution is used. The delta `δ_B` is split as
`δ_B = 1/N + E₁(·, B) + r_B` (`restVec`). Then `r_B` is orthogonal to the constants and killed
by `E₁`, and so are `H r_B` and `H² r_B`. The two Pythagoras identities for `H δ_B` and
`H² δ_B` give Lemma 2 of the extend with the level-`≥ 2` mass `‖H r_B‖²` made explicit.

* `LevelTwoBound W e β` : `‖H g‖ ≤ β D ‖g‖` for every `g` orthogonal to the constants with
  `E₁ g = 0`. It is the eigenvalue bound `|λ_ν| ≤ β D` on the levels `≥ 2`. The extend proves it
  with `β = 1/(2(e - 1)(e - 2))` for `e ≥ 12`, from the Diaconis–Lander values `ω_ν((e))` of the
  zonal spherical functions of `(S_2e, H_e)`. That input is not formalized.
* `levelTwoBound_one` : `LevelTwoBound W e 1`, from `sum_hamApply_sq_le`, the Schur bound
  `‖H g‖ ≤ D ‖g‖`.
* `cGen_eq_levelOne_add` : `cGen B = c₁ + N ‖H² r_B‖² / D⁴` and `sum_hamApply_restVec_sq` :
  `‖H r_B‖² = D - D²/N - λ₁² d₁/N`. So `levelOne_le_cGen` : `c₁ ≤ cGen B` unconditionally.
* `cGen_le_of_levelTwo` (Lemma 2, upper half) : under `LevelTwoBound W e β`,
  `cGen B ≤ c₁ + β² (N/D - 1 - d₁ w₁²)`.
* `card_pm_le_mul_hamDeg` : `N ≤ e D`, that is `1/p ≤ e`.
* `cGen_le_of_levelTwoBound` : on `V_m` with `m ≥ 12`, if `β² m³ ≤ κ` then
  `cGen B ≤ (1/6 + κ)/m²`, and `cGen_le_quarter_of_levelTwo` : at the Diaconis–Lander value
  `β = 1/(2(m - 1)(m - 2))`, `cGen B ≤ (1/4)/m²`.
* `card_emptyFamilies_le_of_levelTwoBound`, `card_emptyFamilies_le_hundred_of_levelTwo`,
  `nonvacuity_corollaryAPrime_of_levelTwoBound`, `nonvacuity_corollaryAPrime_of_levelTwo` :
  the COD-288 endpoints of `repair/Repair/RandomFamily/Nonvacuity.lean` with the hypothesis
  `cGen B ≤ c/m²` replaced by the level-`≥ 2` eigenvalue bound. At the Diaconis–Lander value the
  failure fraction is `(44/25)/m²` for `m ≥ 100`.
-/

open Finset

namespace Pairing

namespace PerfectMatching

/-- The level-`≥ 2` eigenvalue bound with ratio `β`: `‖H g‖² ≤ (β |Ham(B)|)² ‖g‖²` for every
`g` orthogonal to the constants with `E₁ g = 0`, `E₁ = levelOneKer e`. This subspace is
`H`-invariant (`sum_hamApply`, `levelOneKer_hamApply`) and `H` is symmetric, so the bound says
`|λ| ≤ β |Ham(B)|` for every eigenvalue of `H` on it. It is the sum of the levels `≥ 2` once the
range of `E₁` is identified with `V_{(e-1,1)}`, which `repair/Repair/PairLevelOne.lean` does not
formalize (`results/q-second-moment-extend.md` §3, Lemma 2, af8925f). -/
def LevelTwoBound (W : Type*) [Fintype W] [DecidableEq W] (e : ℕ) (β : ℝ) : Prop :=
  ∀ (B : PerfectMatching W) (g : PerfectMatching W → ℝ), ∑ A, g A = 0 →
    (∀ C, ∑ A, levelOneKer e C A * g A = 0) →
      ∑ R, hamApply g R ^ 2 ≤ (β * hamDeg B) ^ 2 * ∑ R, g R ^ 2

section Reduction

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `h(R, A)² = h(R, A)` (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem hamInd_sq (R A : PerfectMatching W) : hamInd R A ^ 2 = hamInd R A := by
  unfold hamInd
  split_ifs <;> norm_num

/-- `Σ_R (H g)(R) = |Ham(B)| Σ_A g(A)` (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem sum_hamApply (B : PerfectMatching W) (g : PerfectMatching W → ℝ) :
    ∑ R, hamApply g R = hamDeg B * ∑ A, g A := by
  simp only [hamApply]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun A _ ↦ ?_
  rw [← sum_mul, sum_hamInd, hamDeg_eq A B]

/-- The Schur bound `‖H g‖² ≤ |Ham(B)|² ‖g‖²` (`results/q-second-moment-extend.md` §3,
af8925f). -/
theorem sum_hamApply_sq_le (B : PerfectMatching W) (g : PerfectMatching W → ℝ) :
    ∑ R, hamApply g R ^ 2 ≤ (hamDeg B : ℝ) ^ 2 * ∑ R, g R ^ 2 := by
  have h1 : ∀ R, hamApply g R ^ 2 ≤ (hamDeg B : ℝ) * ∑ A, hamInd R A * g A ^ 2 := by
    intro R
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun A ↦ hamInd R A) (fun A ↦ hamInd R A * g A)
    have e1 : ∑ A, hamInd R A * (hamInd R A * g A) = hamApply g R := by
      refine sum_congr rfl fun A _ ↦ ?_
      rw [← mul_assoc, ← sq, hamInd_sq]
    have e2 : ∑ A, hamInd R A ^ 2 = hamDeg B := by
      simp_rw [hamInd_sq, hamInd_comm R]
      rw [sum_hamInd, hamDeg_eq R B]
    have e3 : ∑ A, (hamInd R A * g A) ^ 2 = ∑ A, hamInd R A * g A ^ 2 := by
      refine sum_congr rfl fun A _ ↦ ?_
      rw [mul_pow, hamInd_sq]
    rw [e1, e2, e3] at hcs
    exact hcs
  calc ∑ R, hamApply g R ^ 2 ≤ ∑ R, (hamDeg B : ℝ) * ∑ A, hamInd R A * g A ^ 2 :=
        sum_le_sum fun R _ ↦ h1 R
    _ = (hamDeg B : ℝ) * ∑ A, (∑ R, hamInd R A) * g A ^ 2 := by
        rw [← mul_sum, sum_comm]
        simp only [sum_mul]
    _ = (hamDeg B : ℝ) ^ 2 * ∑ R, g R ^ 2 := by
        simp_rw [sum_hamInd, hamDeg_eq _ B]
        rw [← mul_sum, ← mul_assoc, sq]

/-- `LevelTwoBound W e 1` holds for every `W` and `e`, by the Schur bound
(`results/q-second-moment-extend.md` §3, af8925f). -/
theorem levelTwoBound_one (e : ℕ) : LevelTwoBound W e 1 := fun B g _ _ ↦ by
  rw [one_mul]
  exact sum_hamApply_sq_le B g

/-- `Σ_i (a + b u_i + v_i)² = n a² + b² Σ u_i² + Σ v_i²` when `Σ u = Σ v = Σ u v = 0`
(`results/q-second-moment-extend.md` §3, af8925f). -/
theorem sum_sq_add_add {ι : Type*} [Fintype ι] (a b : ℝ) (u v : ι → ℝ) (hu : ∑ i, u i = 0)
    (hv : ∑ i, v i = 0) (huv : ∑ i, u i * v i = 0) :
    ∑ i, (a + b * u i + v i) ^ 2 =
      Fintype.card ι * a ^ 2 + b ^ 2 * ∑ i, u i ^ 2 + ∑ i, v i ^ 2 := by
  have e : ∀ i, (a + b * u i + v i) ^ 2 = a ^ 2 + b ^ 2 * u i ^ 2 + v i ^ 2 +
      (2 * a * b) * u i + (2 * a) * v i + (2 * b) * (u i * v i) := fun i ↦ by ring
  simp only [e, sum_add_distrib, ← mul_sum, hu, hv, huv, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The level-`≥ 2` part `r_B = δ_B - 1/N - E₁(·, B)` of the delta at `B`
(`results/q-second-moment-extend.md` §3, af8925f). -/
noncomputable def restVec (e : ℕ) (B A : PerfectMatching W) : ℝ :=
  (if A = B then 1 else 0) - 1 / (Fintype.card (PerfectMatching W) : ℝ) - levelOneKer e A B

variable {e : ℕ} (hW : Fintype.card W = 2 * e) (he : 2 ≤ e)
include hW he

/-- `Σ_R E₁(C, R) (H g)(R) = λ₁ Σ_A E₁(C, A) g(A)` with `λ₁ = -|Ham(B)|/(2(e - 1))`, since `H`
is symmetric and `H E₁ = λ₁ E₁` (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem levelOneKer_hamApply (B C : PerfectMatching W) (g : PerfectMatching W → ℝ) :
    ∑ R, levelOneKer e C R * hamApply g R =
      -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) * ∑ A, levelOneKer e C A * g A := by
  simp only [hamApply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun A _ ↦ ?_
  have h := hamMat_levelOneKer hW he A C
  rw [hamDeg_eq A B] at h
  calc ∑ R, levelOneKer e C R * (hamInd R A * g A) =
        (∑ R, hamInd A R * levelOneKer e R C) * g A := by
        rw [sum_mul]
        refine sum_congr rfl fun R _ ↦ ?_
        rw [hamInd_comm R A, levelOneKer_comm e C R]
        ring
    _ = -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) * (levelOneKer e C A * g A) := by
        rw [h, levelOneKer_comm e A C]
        ring

/-- `Σ_A r_B(A) = 0` (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem sum_restVec (B : PerfectMatching W) : ∑ A, restVec e B A = 0 := by
  have hN : (Fintype.card (PerfectMatching W) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne'
  have h1 : ∑ A, levelOneKer e A B = 0 := by
    simp_rw [levelOneKer_comm e _ B]
    exact sum_levelOneKer hW he B
  simp only [restVec, sum_sub_distrib, h1, sum_const, card_univ, nsmul_eq_mul]
  rw [Fintype.sum_ite_eq']
  field_simp
  ring

/-- `E₁ r_B = 0` (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem levelOneKer_restVec (B C : PerfectMatching W) :
    ∑ A, levelOneKer e C A * restVec e B A = 0 := by
  have h0 := sum_levelOneKer hW he C
  have h1 := levelOneKer_mul_self hW he C B
  simp only [restVec, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq', ← sum_mul, h0, h1]
  ring

/-- `(H r_B)(R) = h(R, B) - D/N - λ₁ E₁(R, B)` (`results/q-second-moment-extend.md` §3,
af8925f). -/
theorem hamApply_restVec (B R : PerfectMatching W) :
    hamApply (restVec e B) R = hamInd R B - (hamDeg B : ℝ) / Fintype.card (PerfectMatching W) -
      -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) * levelOneKer e R B := by
  have h := hamMat_levelOneKer hW he R B
  rw [hamDeg_eq R B] at h
  have h2 : ∑ A, hamInd R A = hamDeg B := by
    simp_rw [hamInd_comm R]
    rw [sum_hamInd, hamDeg_eq R B]
  simp only [hamApply, restVec, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq', ← sum_mul, h2, h]
  ring

/-- `(H² δ_B)(R) - D²/N - λ₁² E₁(R, B) = (H² r_B)(R)` (`results/q-second-moment-extend.md` §3,
af8925f). -/
theorem hamApply_hamApply_restVec (B R : PerfectMatching W) :
    hamApply (hamApply (restVec e B)) R = hamTwo B R - (hamDeg B : ℝ) ^ 2 /
      Fintype.card (PerfectMatching W) -
        (-((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1)))) ^ 2 * levelOneKer e R B := by
  have h := hamMat_levelOneKer hW he R B
  rw [hamDeg_eq R B] at h
  have h2 : ∑ A, hamInd R A = hamDeg B := by
    simp_rw [hamInd_comm R]
    rw [sum_hamInd, hamDeg_eq R B]
  set lam : ℝ := -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) with hlam
  set N : ℝ := ((Fintype.card (PerfectMatching W) : ℕ) : ℝ) with hN
  have e1 : hamApply (hamApply (restVec e B)) R =
      ∑ A, (hamInd R A * hamInd A B - hamInd R A * ((hamDeg B : ℝ) / N) -
        hamInd R A * (lam * levelOneKer e A B)) := by
    change ∑ A, hamInd R A * hamApply (restVec e B) A = _
    refine sum_congr rfl fun A _ ↦ ?_
    rw [hamApply_restVec hW he B A]
    ring
  have h3 : ∑ A, hamInd R A * ((hamDeg B : ℝ) / N) = (hamDeg B : ℝ) ^ 2 / N := by
    rw [← sum_mul, h2]
    ring
  have h4 : ∑ A, hamInd R A * (lam * levelOneKer e A B) = lam ^ 2 * levelOneKer e R B := by
    rw [sq, mul_assoc, ← h, mul_sum]
    refine sum_congr rfl fun A _ ↦ ?_
    ring
  rw [e1, sum_sub_distrib, sum_sub_distrib, h3, h4]
  rfl

/-- `‖E₁(·, B)‖² = E₁(B, B) = e(2e - 3)/N` (`results/q-second-moment-extend.md` §3,
af8925f). -/
theorem sum_levelOneKer_sq (B : PerfectMatching W) :
    ∑ R, levelOneKer e R B ^ 2 = e * (2 * e - 3) / Fintype.card (PerfectMatching W) := by
  rw [← levelOneKer_self hW he B, ← levelOneKer_mul_self hW he B B]
  refine sum_congr rfl fun R _ ↦ ?_
  rw [sq, levelOneKer_comm e R B]

/-- `‖H r_B‖² = D - D²/N - λ₁² e(2e - 3)/N`, the level-`≥ 2` mass of `H δ_B`. This is the
Plancherel identity of Lemma 2 (`results/q-second-moment-extend.md` §3, af8925f). -/
theorem sum_hamApply_restVec_sq (B : PerfectMatching W) :
    ∑ R, hamApply (restVec e B) R ^ 2 = hamDeg B - (hamDeg B : ℝ) ^ 2 /
      Fintype.card (PerfectMatching W) -
        (-((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1)))) ^ 2 *
          (e * (2 * e - 3) / Fintype.card (PerfectMatching W)) := by
  set N : ℝ := ((Fintype.card (PerfectMatching W) : ℕ) : ℝ) with hN
  set D : ℝ := ((hamDeg B : ℕ) : ℝ) with hD
  set lam : ℝ := -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) with hlam
  set s := hamApply (restVec e B) with hs
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne'
  have hu : ∑ R, levelOneKer e R B = 0 := by
    simp_rw [levelOneKer_comm e _ B]
    exact sum_levelOneKer hW he B
  have hv : ∑ R, s R = 0 := by
    rw [hs, sum_hamApply B, sum_restVec hW he B, mul_zero]
  have huv : ∑ R, levelOneKer e R B * s R = 0 := by
    simp_rw [levelOneKer_comm e _ B]
    rw [hs, levelOneKer_hamApply hW he B B, levelOneKer_restVec hW he B B, mul_zero]
  have hdec : ∀ R, hamInd R B = D / N + lam * levelOneKer e R B + s R := by
    intro R
    rw [hs, hamApply_restVec hW he B R]
    ring
  have hsq := sum_sq_add_add (D / N) lam (fun R ↦ levelOneKer e R B) s hu hv huv
  simp only [← hdec] at hsq
  have hL : ∑ R, hamInd R B ^ 2 = D := by
    simp_rw [hamInd_sq]
    exact sum_hamInd B
  rw [hL, sum_levelOneKer_sq hW he B, ← hN] at hsq
  have : N * (D / N) ^ 2 = D ^ 2 / N := by
    field_simp
  rw [this] at hsq
  linarith

/-- `cGen B = c₁ + N ‖H² r_B‖² / D⁴` with `c₁ = e(2e - 3)/(16(e - 1)⁴)`, the exact split of
`c_gen = Σ_{ν ≠ (e)} d_ν w_ν⁴` into level 1 and the levels `≥ 2`
(`results/q-second-moment-extend.md` §3, Lemma 2, af8925f). -/
theorem cGen_eq_levelOne_add (B : PerfectMatching W) :
    cGen B = e * (2 * e - 3) / (16 * ((e : ℝ) - 1) ^ 4) +
      Fintype.card (PerfectMatching W) / (hamDeg B : ℝ) ^ 4 *
        ∑ R, hamApply (hamApply (restVec e B)) R ^ 2 := by
  set N : ℝ := ((Fintype.card (PerfectMatching W) : ℕ) : ℝ) with hN
  set D : ℝ := ((hamDeg B : ℕ) : ℝ) with hD
  set lam : ℝ := -((hamDeg B : ℝ) / (2 * ((e : ℝ) - 1))) with hlam
  set s := hamApply (restVec e B) with hs
  set t := hamApply s with ht
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨B⟩).ne'
  have hD0 : D ≠ 0 := by
    have hk := hamDeg_eq_closed (e - 1) W (by rw [hW]; omega) B
    rw [hD, hk]
    exact_mod_cast (Nat.mul_pos (by positivity) (Nat.factorial_pos _)).ne'
  have he1 : ((e : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ e := by exact_mod_cast he
    linarith
  have hu : ∑ R, levelOneKer e R B = 0 := by
    simp_rw [levelOneKer_comm e _ B]
    exact sum_levelOneKer hW he B
  have hs0 : ∑ R, s R = 0 := by
    rw [hs, sum_hamApply B, sum_restVec hW he B, mul_zero]
  have hv : ∑ R, t R = 0 := by
    rw [ht, sum_hamApply B, hs0, mul_zero]
  have huv : ∑ R, levelOneKer e R B * t R = 0 := by
    simp_rw [levelOneKer_comm e _ B]
    rw [ht, levelOneKer_hamApply hW he B B, hs, levelOneKer_hamApply hW he B B,
      levelOneKer_restVec hW he B B, mul_zero, mul_zero]
  have hdec : ∀ R, hamTwo B R = D ^ 2 / N + lam ^ 2 * levelOneKer e R B + t R := by
    intro R
    rw [ht, hs, hamApply_hamApply_restVec hW he B R]
    ring
  have hsq := sum_sq_add_add (D ^ 2 / N) (lam ^ 2) (fun R ↦ levelOneKer e R B) t hu hv huv
  simp only [← hdec] at hsq
  rw [sum_levelOneKer_sq hW he B, ← hN] at hsq
  have hc : cGen B = N / D ^ 4 * ∑ R, hamTwo B R ^ 2 - 1 := rfl
  rw [hc, hsq, hlam]
  field_simp
  ring

/-- **Lemma 2, lower half** (`results/q-second-moment-extend.md` §3, af8925f):
`c₁ = e(2e - 3)/(16(e - 1)⁴) ≤ cGen B`, unconditionally. -/
theorem levelOne_le_cGen (B : PerfectMatching W) :
    e * (2 * e - 3) / (16 * ((e : ℝ) - 1) ^ 4) ≤ cGen B := by
  rw [cGen_eq_levelOne_add hW he B]
  have : 0 ≤ (Fintype.card (PerfectMatching W) : ℝ) / (hamDeg B : ℝ) ^ 4 *
      ∑ R, hamApply (hamApply (restVec e B)) R ^ 2 := by positivity
  linarith

/-- **Lemma 2, upper half, reduced to an eigenvalue bound** (`results/q-second-moment-extend.md`
§3, af8925f). Under the level-`≥ 2` bound `LevelTwoBound W e β`,
`cGen B ≤ c₁ + β² (N/D - 1 - d₁ w₁²)` with `c₁ = d₁ w₁⁴ = e(2e - 3)/(16(e - 1)⁴)` and
`d₁ w₁² = e(2e - 3)/(4(e - 1)²)`. -/
theorem cGen_le_of_levelTwo {β : ℝ} (hβ : LevelTwoBound W e β) (B : PerfectMatching W) :
    cGen B ≤ e * (2 * e - 3) / (16 * ((e : ℝ) - 1) ^ 4) +
      β ^ 2 * ((Fintype.card (PerfectMatching W) : ℝ) / hamDeg B - 1 -
        e * (2 * e - 3) / (4 * ((e : ℝ) - 1) ^ 2)) := by
  set N : ℝ := ((Fintype.card (PerfectMatching W) : ℕ) : ℝ) with hN
  set D : ℝ := ((hamDeg B : ℕ) : ℝ) with hD
  have hN0 : 0 < N := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨B⟩)
  have hD0 : 0 < D := by
    have hk := hamDeg_eq_closed (e - 1) W (by rw [hW]; omega) B
    rw [hD, hk]
    exact_mod_cast Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have he1 : ((e : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ e := by exact_mod_cast he
    linarith
  set s := hamApply (restVec e B) with hs
  have hs0 : ∑ R, s R = 0 := by
    rw [hs, sum_hamApply B, sum_restVec hW he B, mul_zero]
  have hsE : ∀ C, ∑ A, levelOneKer e C A * s A = 0 := fun C ↦ by
    rw [hs, levelOneKer_hamApply hW he B C, levelOneKer_restVec hW he B C, mul_zero]
  have hb := hβ B s hs0 hsE
  have hmass := sum_hamApply_restVec_sq hW he B
  rw [← hs, ← hN, ← hD] at hmass
  rw [cGen_eq_levelOne_add hW he B, ← hs, ← hN, ← hD]
  have hND : 0 ≤ N / D ^ 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hb hND
  have h2 : N / D ^ 4 * ((β * D) ^ 2 * ∑ R, s R ^ 2) = β ^ 2 * (N / D - 1 -
      e * (2 * e - 3) / (4 * ((e : ℝ) - 1) ^ 2)) := by
    rw [hmass]
    field_simp
    ring
  linarith

end Reduction

section Count

/-- `(2f + 1)!! ≤ (f + 1) 2^f f!`, that is `N ≤ e D` at `e = f + 1`
(`results/q-second-moment-extend.md` §3, af8925f). -/
theorem doubleFactorial_le_succ_mul : ∀ f : ℕ,
    (2 * f + 1).doubleFactorial ≤ (f + 1) * (2 ^ f * f.factorial)
  | 0 => by simp
  | f + 1 => by
    have ih := doubleFactorial_le_succ_mul f
    rw [show 2 * (f + 1) + 1 = (2 * f + 1) + 2 by ring, Nat.doubleFactorial_add_two, pow_succ,
      Nat.factorial_succ]
    calc (2 * f + 1 + 2) * (2 * f + 1).doubleFactorial ≤
          (2 * f + 1 + 2) * ((f + 1) * (2 ^ f * f.factorial)) := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * f + 4) * ((f + 1) * (2 ^ f * f.factorial)) := Nat.mul_le_mul_right _ (by omega)
      _ = (f + 1 + 1) * (2 ^ f * 2 * ((f + 1) * f.factorial)) := by ring

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `N ≤ e |Ham(B)|`, that is `1/p ≤ e`, for `|W| = 2e`, `e ≥ 1`
(`results/q-second-moment-extend.md` §3, af8925f). -/
theorem card_pm_le_mul_hamDeg {e : ℕ} (hW : Fintype.card W = 2 * e) (he : 1 ≤ e)
    (B : PerfectMatching W) :
    (Fintype.card (PerfectMatching W) : ℝ) ≤ e * hamDeg B := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  rw [card_eq_doubleFactorial hW, hamDeg_eq_closed f W hW B,
    show 2 * (f + 1) - 1 = 2 * f + 1 by omega]
  exact_mod_cast doubleFactorial_le_succ_mul f

end Count

end PerfectMatching

namespace RoundRobin.Canonical.RandomFamily

open PerfectMatching Real

variable {m : ℕ} [NeZero m]

/-- **Lemma 2 on `V_m` from an eigenvalue bound** (`results/q-second-moment-extend.md` §3,
af8925f). For `m ≥ 12`, if `LevelTwoBound (Vertex m) m β` and `β² m³ ≤ κ`, then
`cGen B ≤ (1/6 + κ)/m²` for every `B`. The `1/6` bounds `m² c₁`, which tends to `1/8`, and
`β² m` bounds the level-`≥ 2` term through `1/p ≤ m`. -/
theorem cGen_le_of_levelTwoBound (hm : 12 ≤ m) {β κ : ℝ} (hβ : LevelTwoBound (Vertex m) m β)
    (hκ : β ^ 2 * m ^ 3 ≤ κ) (B : PerfectMatching (Vertex m)) :
    cGen B ≤ (1 / 6 + κ) / m ^ 2 := by
  have hW := card_vertex m
  have hm' : (12 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h := cGen_le_of_levelTwo hW (by omega) hβ B
  have hD0 : (0 : ℝ) < hamDeg B := by
    rw [hamDeg_eq_ham]
    exact_mod_cast Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have hND : (Fintype.card (PerfectMatching (Vertex m)) : ℝ) / hamDeg B ≤ m := by
    rw [div_le_iff₀ hD0]
    exact card_pm_le_mul_hamDeg hW (by omega) B
  have hd1 : 0 ≤ (m : ℝ) * (2 * m - 3) / (4 * ((m : ℝ) - 1) ^ 2) := by
    have : (0 : ℝ) ≤ 2 * m - 3 := by linarith
    positivity
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
  have hlev : β ^ 2 * ((Fintype.card (PerfectMatching (Vertex m)) : ℝ) / hamDeg B - 1 -
      m * (2 * m - 3) / (4 * ((m : ℝ) - 1) ^ 2)) ≤ κ / m ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : β ^ 2 * ((Fintype.card (PerfectMatching (Vertex m)) : ℝ) / hamDeg B - 1 -
        m * (2 * m - 3) / (4 * ((m : ℝ) - 1) ^ 2)) ≤ β ^ 2 * m :=
      mul_le_mul_of_nonneg_left (by linarith) hβ2
    nlinarith
  have hc1 : (m : ℝ) * (2 * m - 3) / (16 * ((m : ℝ) - 1) ^ 4) ≤ 1 / 6 / m ^ 2 := by
    have h1 : (0 : ℝ) < 16 * ((m : ℝ) - 1) ^ 4 := by
      have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      positivity
    rw [div_le_div_iff₀ h1 (by positivity)]
    have ht : (0 : ℝ) ≤ (m : ℝ) - 12 := by linarith
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, mul_nonneg ht hm0.le]
  calc cGen B ≤ _ := h
    _ ≤ 1 / 6 / m ^ 2 + κ / m ^ 2 := add_le_add hc1 hlev
    _ = (1 / 6 + κ) / m ^ 2 := by ring

/-- **Lemma 2 on `V_m` at the Diaconis–Lander value** (`results/q-second-moment-extend.md` §3,
af8925f). For `m ≥ 12`, if every eigenvalue of `H` on the levels `≥ 2` has
`|λ_ν| ≤ D/(2(m - 1)(m - 2))`, the bound the extend derives from the Diaconis–Lander formula,
then `cGen B ≤ (1/4)/m²` for every `B`. -/
theorem cGen_le_quarter_of_levelTwo (hm : 12 ≤ m)
    (hβ : LevelTwoBound (Vertex m) m (1 / (2 * ((m : ℝ) - 1) * ((m : ℝ) - 2))))
    (B : PerfectMatching (Vertex m)) : cGen B ≤ 1 / 4 / m ^ 2 := by
  have hm' : (12 : ℝ) ≤ m := by exact_mod_cast hm
  have hκ : (1 / (2 * ((m : ℝ) - 1) * ((m : ℝ) - 2))) ^ 2 * m ^ 3 ≤ 1 / 12 := by
    have h1 : (0 : ℝ) < 2 * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
      have : (0 : ℝ) < (m : ℝ) - 2 := by linarith
      have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      positivity
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    have ht : (0 : ℝ) ≤ (m : ℝ) - 12 := by linarith
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
  have h := cGen_le_of_levelTwoBound hm hβ hκ B
  calc cGen B ≤ _ := h
    _ = 1 / 4 / m ^ 2 := by ring

/-- **Theorem 1 from an eigenvalue bound** (`results/q-second-moment-extend.md` §6 and §8, C1,
af8925f). For `m ≥ 100`, `|ι| = 2m - 1`, `LevelTwoBound (Vertex m) m β` and `β² m³ ≤ κ`, at
most a fraction `(7(1/6 + κ) + 1/100)/m²` of the families `M : ι → PerfectMatching (Vertex m)`
have no zero state. This is `card_emptyFamilies_le_hundred` with `c = 1/6 + κ` from
`cGen_le_of_levelTwoBound`. -/
theorem card_emptyFamilies_le_of_levelTwoBound (hm : 100 ≤ m) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 2 * m - 1) {β κ : ℝ}
    (hβ : LevelTwoBound (Vertex m) m β) (hκ : β ^ 2 * m ^ 3 ≤ κ) :
    (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        ((7 * (1 / 6 + κ) + 1 / 100) / m ^ 2) :=
  card_emptyFamilies_le_hundred hm ι hι fun B ↦ cGen_le_of_levelTwoBound (by omega) hβ hκ B

/-- **Theorem 1 at the Diaconis–Lander value** (`results/q-second-moment-extend.md` §6 and §8,
C1, af8925f). For `m ≥ 100` and `|ι| = 2m - 1`, if every eigenvalue of `H` on the levels `≥ 2`
has `|λ_ν| ≤ D/(2(m - 1)(m - 2))`, then at most a fraction `(44/25)/m²` of the families
`M : ι → PerfectMatching (Vertex m)` have no zero state. -/
theorem card_emptyFamilies_le_hundred_of_levelTwo (hm : 100 ≤ m) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 2 * m - 1)
    (hβ : LevelTwoBound (Vertex m) m (1 / (2 * ((m : ℝ) - 1) * ((m : ℝ) - 2)))) :
    (#{M : ι → PerfectMatching (Vertex m) | zeroStates M = ∅} : ℝ) ≤
      (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) * (44 / 25 / m ^ 2) := by
  have h := card_emptyFamilies_le_hundred hm ι hι fun B ↦
    cGen_le_quarter_of_levelTwo (by omega) hβ B
  calc _ ≤ _ := h
    _ = _ := by norm_num

open Classical in
/-- **C2 with Theorem A′ from an eigenvalue bound** (`results/q-second-moment-extend.md` §8,
C2, af8925f). For `m ≥ 100`, `|ι| = 2m - 1`, `K ≤ K_m`, `LevelTwoBound (Vertex m) m β` and
`β² m³ ≤ κ`, at least a fraction `1 - m^(-3/2) - (7(1/6 + κ) + 1/100)/m²` of the families have
`Z(M) ≠ ∅` and `¬RepairBoundFor (zeroStates M) G K` at every six-vertex gadget `G`. -/
theorem nonvacuity_corollaryAPrime_of_levelTwoBound (hm : 100 ≤ m) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 2 * m - 1) {β κ : ℝ}
    (hβ : LevelTwoBound (Vertex m) m β) (hκ : β ^ 2 * m ^ 3 ≤ κ) {K : ℕ}
    (hK : (K : ℤ) ≤ kAPrime m) :
    (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        (1 - (m : ℝ) ^ (-(3 / 2 : ℝ)) - (7 * (1 / 6 + κ) + 1 / 100) / m ^ 2) ≤
      (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅ ∧
        ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K} : ℝ) :=
  nonvacuity_corollaryAPrime hm ι hι (fun B ↦ cGen_le_of_levelTwoBound (by omega) hβ hκ B) hK

open Classical in
/-- **C2 with Theorem A′ at the Diaconis–Lander value** (`results/q-second-moment-extend.md`
§8, C2, af8925f). For `m ≥ 100`, `|ι| = 2m - 1` and `K ≤ K_m`, if every eigenvalue of `H` on the
levels `≥ 2` has `|λ_ν| ≤ D/(2(m - 1)(m - 2))`, then at least a fraction
`1 - m^(-3/2) - (44/25)/m²` of the families have `Z(M) ≠ ∅` and
`¬RepairBoundFor (zeroStates M) G K` at every six-vertex gadget `G`. -/
theorem nonvacuity_corollaryAPrime_of_levelTwo (hm : 100 ≤ m) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 2 * m - 1)
    (hβ : LevelTwoBound (Vertex m) m (1 / (2 * ((m : ℝ) - 1) * ((m : ℝ) - 2)))) {K : ℕ}
    (hK : (K : ℤ) ≤ kAPrime m) :
    (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        (1 - (m : ℝ) ^ (-(3 / 2 : ℝ)) - 44 / 25 / m ^ 2) ≤
      (#{M : ι → PerfectMatching (Vertex m) | zeroStates M ≠ ∅ ∧
        ∀ G : Finset (Vertex m), G.card = 6 → ¬RepairBoundFor (zeroStates M) G K} : ℝ) := by
  have h := nonvacuity_corollaryAPrime hm ι hι (fun B ↦ cGen_le_quarter_of_levelTwo (by omega) hβ B)
    hK
  calc _ = (Fintype.card (ι → PerfectMatching (Vertex m)) : ℝ) *
        (1 - (m : ℝ) ^ (-(3 / 2 : ℝ)) - (7 * (1 / 4) + 1 / 100) / m ^ 2) := by norm_num
    _ ≤ _ := h

end RoundRobin.Canonical.RandomFamily

end Pairing
