import Repair.PairRecursion

/-!
# The edge-disjoint pair ratio is at most `9/8` (COD-288)

Source: `results/q-second-moment-extend.md` §4, Lemma 3 (organize-archive af8925f), checked in
`results/q-second-moment-factcheck-extend.md`, row L3 (af8925f). `K(μ) = k2Count μ` is the Lemma
K2 count of `PairRecursion.lean`, `j = |μ|`, `N_j = (2j - 1)!!`, `D_j = 2^(j-1)(j-1)!` and
`ψ_j = D_j² / N_j`, so that `g(μ) = h/p² = K(μ) / ψ_j`.

* `k2Count_eq_k2Step` : `K(μ) = k2Step K μ a` at the largest part `a`, for `|μ| ≥ 2`.
* `k2Count_cons_one` : the shared-edge rule `K(1 ∪ ν) = 2|ν| K(ν)` for `|ν| ≥ 1` and positive
  parts, proved from the recursion alone. It is the multiset form of
  `jointCount_eq_of_mate_eq`.
* `k2Count_le_betaK` (Lemma 3, upper half) : for every type `μ` with all parts `≥ 2` and
  `|μ| = j ≥ 2`, `K(μ) ≤ T_j ψ_j` with `T_j = 9/8 - 1/(2j)`. So `g(μ) ≤ 9/8` on edge-disjoint
  types. The extend proves `g ≤ 1.0794` through the window maxima. Here a closed potential
  `T_j` replaces the window, and the three window inequalities of the extend (largest part
  `a ≥ 4`, `a = 3`, `a = 2`) become `betaK_step_four`, `betaK_step_three`, `betaK_step_two`.
-/

open Finset

namespace Pairing

namespace PerfectMatching

section Recursion

/-- Every part is at most the largest part (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem le_maxPart {μ : Multiset ℕ} {x : ℕ} (hx : x ∈ μ) : x ≤ maxPart μ :=
  Finset.le_sup (f := id) (Multiset.mem_toFinset.mpr hx)

/-- A type of positive size has a positive largest part. -/
theorem one_le_maxPart {μ : Multiset ℕ} (h : 1 ≤ μ.sum) : 1 ≤ maxPart μ := by
  by_contra h0
  have hz : ∀ x ∈ μ, x = 0 := fun x hx ↦ by have := le_maxPart hx; omega
  rw [Multiset.sum_eq_zero hz] at h
  omega

/-- `k2Step` only reads `g` on types of size `|μ| - 1` (`results/k3-counterexample-hunt.md`,
Lemma K2). -/
theorem k2Step_congr {g₁ g₂ : Multiset ℕ → ℕ} {μ : Multiset ℕ} {a : ℕ} (ha : a ∈ μ)
    (ha1 : 1 ≤ a) (hg : ∀ ν : Multiset ℕ, ν.sum + 1 = μ.sum → g₁ ν = g₂ ν) :
    k2Step g₁ μ a = k2Step g₂ μ a := by
  have hs := Multiset.sum_erase ha
  unfold k2Step
  congr 1
  · congr 1
    · rw [hg]
      simp only [Multiset.sum_cons]
      omega
    · refine Finset.sum_congr rfl fun x hx ↦ hg _ ?_
      rw [Finset.mem_Icc] at hx
      simp only [Multiset.sum_cons]
      omega
  · refine congrArg Multiset.sum (Multiset.map_congr rfl fun b hb ↦ ?_)
    have hb' := Multiset.sum_erase hb
    rw [hg]
    simp only [Multiset.sum_cons]
    omega

/-- Lemma K2 at the largest part: `K(μ) = k2Step K μ a` with `a = maxPart μ`, for `|μ| ≥ 2`
(`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem k2Count_eq_k2Step {μ : Multiset ℕ} (h : 2 ≤ μ.sum) :
    k2Count μ = k2Step k2Count μ (maxPart μ) := by
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨j, hj⟩ : ∃ j, μ.sum = j + 2 := ⟨μ.sum - 2, by omega⟩
  rw [k2Count, hj, k2Aux]
  refine k2Step_congr (maxPart_mem hne) (one_le_maxPart (by omega)) fun ν hν ↦ ?_
  rw [k2Count, show ν.sum = j + 1 by omega]

/-- `K((1)) = 1`. -/
theorem k2Count_one : k2Count {1} = 1 :=
  rfl

/-- Erasing a part of `X` from `c ∪ X` keeps `c`. -/
theorem erase_cons_of_mem {X : Multiset ℕ} {b : ℕ} (c : ℕ) (hb : b ∈ X) :
    (c ::ₘ X).erase b = c ::ₘ X.erase b := by
  by_cases h : c = b
  · subst h
    rw [Multiset.erase_cons_head, Multiset.cons_erase hb]
  · exact Multiset.erase_cons_tail X h

/-- Adding a part `1` does not change the largest part of a type of positive size. -/
theorem maxPart_cons_one {ν : Multiset ℕ} (h : 1 ≤ ν.sum) : maxPart (1 ::ₘ ν) = maxPart ν := by
  have h1 := one_le_maxPart h
  unfold maxPart at h1 ⊢
  rw [Multiset.toFinset_cons, Finset.sup_insert]
  exact max_eq_right h1

/-- The shared-edge rule `K(1 ∪ ν) = 2|ν| K(ν)` for `|ν| ≥ 1` with positive parts
(`results/q-second-moment-extend.md` §4, af8925f; `results/hybrid-pair-incoherence.md`,
Lemma 2). It is proved from the recursion alone, by induction on `|ν|`. -/
theorem k2Count_cons_one : ∀ (s : ℕ) (ν : Multiset ℕ), ν.sum = s → (∀ x ∈ ν, 0 < x) → 1 ≤ s →
    k2Count (1 ::ₘ ν) = 2 * s * k2Count ν := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro ν hs hpos h1
  have hne : ν ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have haν : maxPart ν ∈ ν := maxPart_mem hne
  have ha1 : 1 ≤ maxPart ν := hpos _ haν
  have hsum : (1 ::ₘ ν).sum = s + 1 := by rw [Multiset.sum_cons, hs]; omega
  rw [k2Count_eq_k2Step (by omega), maxPart_cons_one (by omega)]
  have herase := Multiset.sum_erase haν
  rcases Nat.lt_or_ge (maxPart ν) 2 with ha2 | ha2
  · have hall : ∀ b ∈ ν, b = 1 := fun b hb ↦ by
      have := le_maxPart hb
      have := hpos b hb
      omega
    have ha : maxPart ν = 1 := by omega
    rw [ha]
    unfold k2Step
    rw [Multiset.erase_cons_head]
    have hmap : (ν.map fun b ↦ 2 * b * k2Count ((1 + b - 1) ::ₘ ν.erase b)) =
        ν.map fun b ↦ 2 * k2Count ν * b := by
      refine Multiset.map_congr rfl fun b hb ↦ ?_
      rw [show 1 + b - 1 = b by omega, Multiset.cons_erase hb]
      ring
    rw [hmap, Multiset.sum_map_mul_left, Multiset.map_id', hs]
    simp
    ring
  · have has : maxPart ν ≤ s := by omega
    have hs2 : 2 ≤ s := by omega
    set a := maxPart ν with ha_def
    set X := ν.erase a with hX
    have hXpos : ∀ x ∈ X, 0 < x := fun x hx ↦ hpos x (Multiset.mem_of_mem_erase hx)
    have key : ∀ ρ : Multiset ℕ, ρ.sum = s - 1 → (∀ x ∈ ρ, 0 < x) →
        k2Count (1 ::ₘ ρ) = 2 * (s - 1) * k2Count ρ := fun ρ hρ hρp ↦
      ih (s - 1) (by omega) ρ hρ hρp (by omega)
    have hK : k2Count ν = k2Step k2Count ν a := k2Count_eq_k2Step (by omega)
    have e1 : k2Count ((a - 1) ::ₘ 1 ::ₘ X) = 2 * (s - 1) * k2Count ((a - 1) ::ₘ X) := by
      rw [Multiset.cons_swap]
      refine key _ (by rw [Multiset.sum_cons]; omega) fun x hx ↦ ?_
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · omega
      · exact hXpos x hx
    have e2 : ∀ x ∈ Icc 1 (a - 2), k2Count (x ::ₘ (a - 1 - x) ::ₘ 1 ::ₘ X) =
        2 * (s - 1) * k2Count (x ::ₘ (a - 1 - x) ::ₘ X) := by
      intro x hx
      rw [Finset.mem_Icc] at hx
      rw [Multiset.cons_swap (a - 1 - x), Multiset.cons_swap x]
      refine key _ (by simp only [Multiset.sum_cons]; omega) fun y hy ↦ ?_
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · omega
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · omega
      · exact hXpos y hy
    have e3 : ∀ b ∈ X, 2 * b * k2Count ((a + b - 1) ::ₘ (1 ::ₘ X).erase b) =
        2 * (s - 1) * (2 * b * k2Count ((a + b - 1) ::ₘ X.erase b)) := by
      intro b hb
      have hb' := Multiset.sum_erase hb
      rw [erase_cons_of_mem 1 hb, Multiset.cons_swap]
      rw [key _ (by simp only [Multiset.sum_cons]; omega) fun y hy ↦ ?_]
      · ring
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · omega
      · exact hXpos y (Multiset.mem_of_mem_erase hy)
    have e4 : 2 * 1 * k2Count ((a + 1 - 1) ::ₘ (1 ::ₘ X).erase 1) = 2 * k2Count ν := by
      rw [Multiset.erase_cons_head, show a + 1 - 1 = a by omega, hX, Multiset.cons_erase haν,
        mul_one]
    have hstep : k2Step k2Count (1 ::ₘ ν) a = 2 * (s - 1) * k2Step k2Count ν a + 2 * k2Count ν := by
      unfold k2Step
      rw [Multiset.erase_cons_tail _ (by omega : (1 : ℕ) ≠ a), ← hX, e1,
        Finset.sum_congr rfl e2, ← Finset.mul_sum, Multiset.map_cons, Multiset.sum_cons, e4,
        Multiset.map_congr rfl e3, Multiset.sum_map_mul_left]
      ring
    rw [hstep, ← hK]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

end Recursion

section Potential

/-- `ψ_j = D_j² / N_j` with `D_j = 2^(j-1)(j-1)!` and `N_j = (2j - 1)!!`, so that the pair ratio
of a type `μ ⊢ j` is `g(μ) = K(μ) / ψ_j` (`results/q-second-moment-extend.md` §4, af8925f). -/
noncomputable def psiK (j : ℕ) : ℝ :=
  ((2 ^ (j - 1) * (j - 1).factorial : ℕ) : ℝ) ^ 2 / (Nat.doubleFactorial (2 * j - 1) : ℝ)

/-- `ψ_j > 0`. -/
theorem psiK_pos (j : ℕ) : 0 < psiK j := by
  unfold psiK
  have h1 : (0 : ℝ) < ((2 ^ (j - 1) * (j - 1).factorial : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by positivity) (Nat.factorial_pos _))
  have h2 : (0 : ℝ) < (Nat.doubleFactorial (2 * j - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  positivity

/-- `ψ_(j+1) = (2j)² / (2j + 1) · ψ_j` for `j ≥ 1`, from `D_(j+1) = 2j D_j` and
`N_(j+1) = (2j + 1) N_j`. -/
theorem psiK_succ {j : ℕ} (hj : 1 ≤ j) :
    psiK (j + 1) = (2 * j : ℝ) ^ 2 / (2 * j + 1) * psiK j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold psiK
  rw [show i + 1 + 1 - 1 = i + 1 by omega, show i + 1 - 1 = i by omega,
    show 2 * (i + 1 + 1) - 1 = (2 * i + 1) + 2 by omega, show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
    Nat.doubleFactorial_add_two, Nat.factorial_succ, pow_succ]
  have h2 : (0 : ℝ) < (Nat.doubleFactorial (2 * i + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  push_cast
  field_simp
  ring

/-- The potential `T_j = 9/8 - 1/(2j)` that replaces the window maxima of Lemma 3
(`results/q-second-moment-extend.md` §4, af8925f). -/
noncomputable def potT (j : ℕ) : ℝ :=
  9 / 8 - 1 / (2 * j)

/-- `β_j = T_j ψ_j`, the bound on `K(μ)` for edge-disjoint `μ ⊢ j`. -/
noncomputable def betaK (j : ℕ) : ℝ :=
  potT j * psiK j

/-- `β_2 = 7/6 ≥ 1 = K((2))`. -/
theorem one_le_betaK_two : 1 ≤ betaK 2 := by
  norm_num [betaK, potT, psiK, Nat.doubleFactorial]

/-- `β_3 = 1472/360 ≥ 4 = K((3))`. -/
theorem four_le_betaK_three : 4 ≤ betaK 3 := by
  norm_num [betaK, potT, psiK, Nat.doubleFactorial, Nat.factorial]

/-- `β_j ≥ 0` for `j ≥ 1`. -/
theorem betaK_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ betaK j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hT : 0 ≤ potT j := by
    unfold potT
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  exact mul_nonneg hT (psiK_pos j).le

/-- The window inequality for a largest part `a ≥ 4` at `j = i + 4`:
`(2j - 5) β_(j-1) + 4(j - 2) β_(j-2) ≤ β_j` (`results/q-second-moment-extend.md` §4, case
`a ≥ 4`, af8925f). -/
theorem betaK_step_four (i : ℕ) :
    (2 * i + 3 : ℝ) * betaK (i + 3) + 4 * (i + 2) * betaK (i + 2) ≤ betaK (i + 4) := by
  have hX := psiK_pos (i + 2)
  have h3 := psiK_succ (j := i + 2) (by omega)
  have h4 := psiK_succ (j := i + 3) (by omega)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have key : (2 * i + 3 : ℝ) * ((9 / 8 - 1 / (2 * ((i : ℝ) + 3))) *
      ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1))) +
      4 * ((i : ℝ) + 2) * (9 / 8 - 1 / (2 * ((i : ℝ) + 2))) ≤
      (9 / 8 - 1 / (2 * ((i : ℝ) + 4))) * ((2 * ((i : ℝ) + 3)) ^ 2 / (2 * ((i : ℝ) + 3) + 1) *
        ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1))) := by
    have h1 : (0 : ℝ) < 2 * ((i : ℝ) + 3) := by positivity
    have h2 : (0 : ℝ) < 2 * ((i : ℝ) + 2) := by positivity
    have h3 : (0 : ℝ) < 2 * ((i : ℝ) + 4) := by positivity
    have h4 : (0 : ℝ) < 2 * ((i : ℝ) + 2) + 1 := by positivity
    have h5 : (0 : ℝ) < 2 * ((i : ℝ) + 3) + 1 := by positivity
    field_simp
    ring_nf
    nlinarith [pow_nonneg hi 2, pow_nonneg hi 3, pow_nonneg hi 4, pow_nonneg hi 5, pow_nonneg hi 6,
      pow_nonneg hi 7, pow_nonneg hi 8, pow_nonneg hi 9]
  unfold betaK potT
  rw [h4, h3]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right key hX.le]

/-- The window inequality for a largest part `a = 3` with other parts, at `j = i + 5`:
`(2j - 4) β_(j-1) + 4(j - 2)(j - 3) β_(j-3) ≤ β_j` (`results/q-second-moment-extend.md` §4,
case `a = 3`, af8925f). -/
theorem betaK_step_three (i : ℕ) :
    (2 * i + 6 : ℝ) * betaK (i + 4) + 4 * (i + 3) * (i + 2) * betaK (i + 2) ≤ betaK (i + 5) := by
  have hX := psiK_pos (i + 2)
  have e3 := psiK_succ (j := i + 2) (by omega)
  have e4 := psiK_succ (j := i + 3) (by omega)
  have e5 := psiK_succ (j := i + 4) (by omega)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have key : (2 * i + 6 : ℝ) * ((9 / 8 - 1 / (2 * ((i : ℝ) + 4))) *
      ((2 * ((i : ℝ) + 3)) ^ 2 / (2 * ((i : ℝ) + 3) + 1) *
        ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1)))) +
      4 * ((i : ℝ) + 3) * ((i : ℝ) + 2) * (9 / 8 - 1 / (2 * ((i : ℝ) + 2))) ≤
      (9 / 8 - 1 / (2 * ((i : ℝ) + 5))) * ((2 * ((i : ℝ) + 4)) ^ 2 / (2 * ((i : ℝ) + 4) + 1) *
        ((2 * ((i : ℝ) + 3)) ^ 2 / (2 * ((i : ℝ) + 3) + 1) *
          ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1)))) := by
    have h1 : (0 : ℝ) < 2 * ((i : ℝ) + 4) := by positivity
    have h2 : (0 : ℝ) < 2 * ((i : ℝ) + 2) := by positivity
    have h3 : (0 : ℝ) < 2 * ((i : ℝ) + 5) := by positivity
    have h4 : (0 : ℝ) < 2 * ((i : ℝ) + 2) + 1 := by positivity
    have h5 : (0 : ℝ) < 2 * ((i : ℝ) + 3) + 1 := by positivity
    have h6 : (0 : ℝ) < 2 * ((i : ℝ) + 4) + 1 := by positivity
    field_simp
    ring_nf
    nlinarith [pow_nonneg hi 2, pow_nonneg hi 3, pow_nonneg hi 4, pow_nonneg hi 5, pow_nonneg hi 6,
      pow_nonneg hi 7, pow_nonneg hi 8, pow_nonneg hi 9, pow_nonneg hi 10, pow_nonneg hi 11]
  unfold betaK potT
  rw [e5, e4, e3]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right key hX.le]

/-- The window inequality for a largest part `a = 2` with other parts, at `j = i + 4`:
`2(j - 2) β_(j-1) + 2(j - 2) β_(j-2) ≤ β_j` (`results/q-second-moment-extend.md` §4, case
`a = 2`, af8925f). -/
theorem betaK_step_two (i : ℕ) :
    (2 * i + 4 : ℝ) * betaK (i + 3) + (2 * i + 4) * betaK (i + 2) ≤ betaK (i + 4) := by
  have hX := psiK_pos (i + 2)
  have h3 := psiK_succ (j := i + 2) (by omega)
  have h4 := psiK_succ (j := i + 3) (by omega)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have key : (2 * i + 4 : ℝ) * ((9 / 8 - 1 / (2 * ((i : ℝ) + 3))) *
      ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1))) +
      (2 * i + 4) * (9 / 8 - 1 / (2 * ((i : ℝ) + 2))) ≤
      (9 / 8 - 1 / (2 * ((i : ℝ) + 4))) * ((2 * ((i : ℝ) + 3)) ^ 2 / (2 * ((i : ℝ) + 3) + 1) *
        ((2 * ((i : ℝ) + 2)) ^ 2 / (2 * ((i : ℝ) + 2) + 1))) := by
    have h1 : (0 : ℝ) < 2 * ((i : ℝ) + 3) := by positivity
    have h2 : (0 : ℝ) < 2 * ((i : ℝ) + 2) := by positivity
    have h3 : (0 : ℝ) < 2 * ((i : ℝ) + 4) := by positivity
    have h4 : (0 : ℝ) < 2 * ((i : ℝ) + 2) + 1 := by positivity
    have h5 : (0 : ℝ) < 2 * ((i : ℝ) + 3) + 1 := by positivity
    field_simp
    ring_nf
    nlinarith [pow_nonneg hi 2, pow_nonneg hi 3, pow_nonneg hi 4, pow_nonneg hi 5, pow_nonneg hi 6,
      pow_nonneg hi 7, pow_nonneg hi 8, pow_nonneg hi 9]
  unfold betaK potT
  rw [h4, h3]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right key hX.le]

end Potential

section LemmaThree

/-- `k2Step` in `ℝ` (`results/k3-counterexample-hunt.md`, Lemma K2). -/
theorem cast_k2Step (g : Multiset ℕ → ℕ) (μ : Multiset ℕ) {a : ℕ} (ha : 1 ≤ a) :
    (k2Step g μ a : ℝ) = ((a : ℝ) - 1) * g ((a - 1) ::ₘ μ.erase a) +
      ∑ x ∈ Icc 1 (a - 2), (g (x ::ₘ (a - 1 - x) ::ₘ μ.erase a) : ℝ) +
      ((μ.erase a).map fun b : ℕ ↦ 2 * (b : ℝ) * g ((a + b - 1) ::ₘ (μ.erase a).erase b)).sum := by
  unfold k2Step
  push_cast [Nat.cast_sub ha, Nat.cast_multiset_sum, Multiset.map_map]
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun b _ ↦ ?_)
  simp

/-- The shared-edge rule for an edge-disjoint `ν ⊢ s`, `s ≥ 1`, in `ℝ`. -/
theorem cast_k2Count_cons_one {ν : Multiset ℕ} (hν : ∀ x ∈ ν, 2 ≤ x) (h1 : 1 ≤ ν.sum) :
    (k2Count (1 ::ₘ ν) : ℝ) = 2 * ν.sum * k2Count ν := by
  rw [k2Count_cons_one ν.sum ν rfl (fun x hx ↦ by have := hν x hx; omega) h1]
  push_cast
  ring

/-- **Lemma 3, upper half** (`results/q-second-moment-extend.md` §4, af8925f; checked in
`results/q-second-moment-factcheck-extend.md`, row L3, af8925f). For every type `μ ⊢ j`,
`j ≥ 2`, with all parts `≥ 2` (an edge-disjoint pair), `K(μ) ≤ (9/8 - 1/(2j)) ψ_j`. That is,
`h/p² ≤ 9/8 - 1/(2j)`. The induction is the window induction of the extend at the largest part,
with the potential `T_j` in place of the window maximum. -/
theorem k2Count_le_betaK : ∀ (j : ℕ) (μ : Multiset ℕ), μ.sum = j → (∀ x ∈ μ, 2 ≤ x) → 2 ≤ j →
    (k2Count μ : ℝ) ≤ betaK j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro μ hs hμ hj
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have haμ : maxPart μ ∈ μ := maxPart_mem hne
  have hK : k2Count μ = k2Step k2Count μ (maxPart μ) := k2Count_eq_k2Step (by omega)
  set a := maxPart μ with ha_def
  have ha2 : 2 ≤ a := hμ a haμ
  have hXs : a + (μ.erase a).sum = j := by rw [Multiset.sum_erase haμ, hs]
  have hμX : μ = a ::ₘ μ.erase a := (Multiset.cons_erase haμ).symm
  set X := μ.erase a with hX
  have hX2 : ∀ x ∈ X, 2 ≤ x := fun x hx ↦ hμ x (Multiset.mem_of_mem_erase hx)
  have hX0 : X = 0 ∨ 2 ≤ X.sum := by
    rcases Multiset.empty_or_exists_mem X with h | ⟨x, hx⟩
    · exact Or.inl h
    · exact Or.inr ((hX2 x hx).trans (Multiset.le_sum_of_mem hx))
  have hed : ∀ ν : Multiset ℕ, ν.sum + 1 = j → (∀ y ∈ ν, 2 ≤ y) → 3 ≤ j →
      (k2Count ν : ℝ) ≤ betaK (j - 1) := fun ν h1 h2 h3 ↦ ih (j - 1) (by omega) ν (by omega) h2
        (by omega)
  have hmerge : 3 ≤ j → (X.map fun b : ℕ ↦ 2 * (b : ℝ) *
      k2Count ((a + b - 1) ::ₘ X.erase b)).sum ≤ 2 * X.sum * betaK (j - 1) := by
    intro hj3
    calc (X.map fun b : ℕ ↦ 2 * (b : ℝ) * k2Count ((a + b - 1) ::ₘ X.erase b)).sum
        ≤ (X.map fun b : ℕ ↦ 2 * (b : ℝ) * betaK (j - 1)).sum := by
          refine Multiset.sum_map_le_sum_map _ _ fun b hb ↦ ?_
          have hb' := Multiset.sum_erase hb
          have hcs : ((a + b - 1) ::ₘ X.erase b).sum + 1 = j := by
            rw [Multiset.sum_cons]
            have := hX2 b hb
            omega
          refine mul_le_mul_of_nonneg_left (hed _ hcs (fun y hy ↦ ?_) hj3) (by positivity)
          rcases Multiset.mem_cons.mp hy with h | hy
          · have := hX2 b hb
            omega
          · exact hX2 y (Multiset.mem_of_mem_erase hy)
      _ = 2 * X.sum * betaK (j - 1) := by
          rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Nat.cast_multiset_sum]
  rw [hK, cast_k2Step _ _ (by omega)]
  rcases Nat.lt_or_ge a 4 with ha4 | ha4
  · rcases Nat.lt_or_ge a 3 with ha3 | ha3
    · have ha : a = 2 := by omega
      rcases hX0 with hX0 | hX0
      · have hμ2 : μ = {2} := by rw [hμX, hX0, ha]; rfl
        have hj2 : j = 2 := by rw [← hs, hμ2]; rfl
        rw [← cast_k2Step _ _ (by omega), ← hK, hμ2, hj2, show k2Count {2} = 1 by decide]
        exact_mod_cast one_le_betaK_two
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
        have hsh : (k2Count (1 ::ₘ X) : ℝ) ≤ 2 * X.sum * betaK (i + 2) := by
          rw [cast_k2Count_cons_one hX2 (by omega)]
          exact mul_le_mul_of_nonneg_left (ih (i + 2) (by omega) X (by omega) hX2 (by omega))
            (by positivity)
        have hm := hmerge (by omega)
        rw [show i + 4 - 1 = i + 3 by omega] at hm
        have hXs' : (X.sum : ℝ) = i + 2 := by exact_mod_cast (by omega : X.sum = i + 2)
        rw [hXs'] at hsh hm
        rw [show a - 2 = 0 by omega, show a - 1 = 1 by omega, Finset.Icc_eq_empty (by omega),
          Finset.sum_empty]
        have hstep := betaK_step_two i
        have har : (a : ℝ) = 2 := by exact_mod_cast ha
        rw [har]
        linarith
    · have ha : a = 3 := by omega
      rcases hX0 with hX0 | hX0
      · have hμ3 : μ = {3} := by rw [hμX, hX0, ha]; rfl
        have hj3 : j = 3 := by rw [← hs, hμ3]; rfl
        rw [← cast_k2Step _ _ (by omega), ← hK, hμ3, hj3, show k2Count {3} = 4 by decide]
        exact_mod_cast four_le_betaK_three
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 5 := ⟨j - 5, by omega⟩
        have hXs' : X.sum = i + 2 := by omega
        have hsh : (k2Count (1 ::ₘ 1 ::ₘ X) : ℝ) ≤ 4 * (i + 3) * (i + 2) * betaK (i + 2) := by
          have h1 : ∀ x ∈ 1 ::ₘ X, 0 < x := fun x hx ↦ by
            rcases Multiset.mem_cons.mp hx with rfl | hx
            · omega
            · have := hX2 x hx
              omega
          rw [k2Count_cons_one (i + 3) (1 ::ₘ X) (by rw [Multiset.sum_cons]; omega) h1 (by omega)]
          push_cast
          rw [cast_k2Count_cons_one hX2 (by omega), hXs']
          have hb := ih (i + 2) (by omega) X hXs' hX2 (by omega)
          push_cast
          nlinarith [hb, (by positivity : (0 : ℝ) ≤ 4 * (i + 3) * (i + 2))]
        have hshr : (k2Count (2 ::ₘ X) : ℝ) ≤ betaK (i + 4) := by
          have := hed (2 ::ₘ X) (by rw [Multiset.sum_cons]; omega) (fun y hy ↦ by
            rcases Multiset.mem_cons.mp hy with rfl | hy
            · omega
            · exact hX2 y hy) (by omega)
          rwa [show i + 5 - 1 = i + 4 by omega] at this
        have hm := hmerge (by omega)
        rw [show i + 5 - 1 = i + 4 by omega] at hm
        have hXr : (X.sum : ℝ) = i + 2 := by exact_mod_cast hXs'
        rw [hXr] at hm
        rw [show a - 2 = 1 by omega, Finset.Icc_self, Finset.sum_singleton,
          show a - 1 = 2 by omega, show 2 - 1 = 1 by rfl]
        have hstep := betaK_step_three i
        have har : (a : ℝ) = 3 := by exact_mod_cast ha
        rw [har]
        nlinarith
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
    have hXs' : X.sum = i + 4 - a := by omega
    have hcore : (k2Count ((a - 2) ::ₘ X) : ℝ) ≤ betaK (i + 2) :=
      ih (i + 2) (by omega) _ (by rw [Multiset.sum_cons]; omega) (fun y hy ↦ by
        rcases Multiset.mem_cons.mp hy with rfl | hy
        · omega
        · exact hX2 y hy) (by omega)
    have hcore2 : ∀ y ∈ (a - 2) ::ₘ X, 2 ≤ y := fun y hy ↦ by
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · omega
      · exact hX2 y hy
    have hshare : (k2Count (1 ::ₘ (a - 2) ::ₘ X) : ℝ) ≤ 2 * (i + 2) * betaK (i + 2) := by
      rw [cast_k2Count_cons_one hcore2 (by rw [Multiset.sum_cons]; omega)]
      have : (((a - 2) ::ₘ X).sum : ℝ) = i + 2 := by
        rw [Multiset.sum_cons]
        exact_mod_cast (by omega : a - 2 + X.sum = i + 2)
      rw [this]
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    have hIcc : Icc 1 (a - 2) = insert 1 (insert (a - 2) (Icc 2 (a - 3))) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmid : ∑ x ∈ Icc 2 (a - 3), (k2Count (x ::ₘ (a - 1 - x) ::ₘ X) : ℝ) ≤
        (a - 4 : ℝ) * betaK (i + 3) := by
      calc ∑ x ∈ Icc 2 (a - 3), (k2Count (x ::ₘ (a - 1 - x) ::ₘ X) : ℝ)
          ≤ ∑ x ∈ Icc 2 (a - 3), betaK (i + 3) := by
            refine Finset.sum_le_sum fun x hx ↦ ?_
            rw [Finset.mem_Icc] at hx
            have := hed (x ::ₘ (a - 1 - x) ::ₘ X) (by simp only [Multiset.sum_cons]; omega)
              (fun y hy ↦ by
                rcases Multiset.mem_cons.mp hy with rfl | hy
                · omega
                rcases Multiset.mem_cons.mp hy with rfl | hy
                · omega
                · exact hX2 y hy) (by omega)
            rwa [show i + 4 - 1 = i + 3 by omega] at this
        _ = (a - 4 : ℝ) * betaK (i + 3) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
              show a - 3 + 1 - 2 = a - 4 by omega, Nat.cast_sub (by omega)]
            push_cast
            ring
    have hshr : (k2Count ((a - 1) ::ₘ X) : ℝ) ≤ betaK (i + 3) := by
      have := hed ((a - 1) ::ₘ X) (by rw [Multiset.sum_cons]; omega) (fun y hy ↦ by
        rcases Multiset.mem_cons.mp hy with rfl | hy
        · omega
        · exact hX2 y hy) (by omega)
      rwa [show i + 4 - 1 = i + 3 by omega] at this
    have hm := hmerge (by omega)
    rw [show i + 4 - 1 = i + 3 by omega] at hm
    have hXr : (X.sum : ℝ) = i + 4 - a := by
      rw [hXs', Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hXr] at hm
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [show a - 1 - 1 = a - 2 by omega, show a - 1 - (a - 2) = 1 by omega,
      Multiset.cons_swap (a - 2) 1]
    have hstep := betaK_step_four i
    have ha' : (4 : ℝ) ≤ a := by exact_mod_cast ha4
    have hb3 := betaK_nonneg (j := i + 3) (by omega)
    have hb2 := betaK_nonneg (j := i + 2) (by omega)
    have h1 : ((a : ℝ) - 1) * k2Count ((a - 1) ::ₘ X) ≤ ((a : ℝ) - 1) * betaK (i + 3) :=
      mul_le_mul_of_nonneg_left hshr (by linarith)
    nlinarith

end LemmaThree

section Matching

universe u

/-- With no shared edge, every cycle of `F₀ ∪ F₁` has length at least `4`, so every part of the
type is at least `2` (`results/q-second-moment-extend.md` §4, af8925f). -/
theorem two_le_of_mem_pairType {W : Type*} [Fintype W] [DecidableEq W]
    {F0 F1 : PerfectMatching W} (h : ∀ x, F0.mate x ≠ F1.mate x) :
    ∀ k ∈ pairType F0 F1, 2 ≤ k := by
  intro k hk
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hk
  obtain ⟨w, -, rfl⟩ := mem_image.mp (Finset.mem_val.mp hS)
  rw [card_cycleOf]
  have hpos := cycLen_pos (F0 := F0) (F1 := F1) w
  have hev := cycLen_even (F0 := F0) (F1 := F1) w
  by_contra hlt
  have h2 : cycLen F0 F1 w = 2 := by omega
  apply h w
  have hc := alt_cycLen (F0 := F0) (F1 := F1) w
  rw [h2] at hc
  change (stepMatching F0 F1 1).mate ((stepMatching F0 F1 0).mate w) = w at hc
  rw [stepMatching_of_even (k := 0) rfl, stepMatching_of_odd (k := 1) rfl] at hc
  calc F0.mate w = F1.mate (F1.mate (F0.mate w)) := (F1.mate_mate _).symm
    _ = F1.mate w := by rw [hc]

/-- Restricting to `V ∖ {a, b}` along a shared edge `{a, b}` removes at least the two vertices
`a`, `b` from the agreement set `{x : F₀(x) = F₁(x)}`. -/
theorem card_agree_restrict_add_two_le {W : Type*} [Fintype W] [DecidableEq W]
    {F0 F1 : PerfectMatching W} {a b : W} (hA : F0.mate a = b) (hB : F1.mate a = b) :
    #{x | (restrict F0 (pairCompl a b) (mate_mem_pairCompl hA)).mate x =
        (restrict F1 (pairCompl a b) (mate_mem_pairCompl hB)).mate x} + 2 ≤
      #{x | F0.mate x = F1.mate x} := by
  have hab : a ≠ b := fun h ↦ F0.mate_ne a (by rw [hA, h])
  set S := pairCompl a b
  have hmap : (Finset.univ.filter fun x : S ↦
      (restrict F0 S (mate_mem_pairCompl hA)).mate x =
        (restrict F1 S (mate_mem_pairCompl hB)).mate x).map (Function.Embedding.subtype _) =
      S.filter fun x ↦ F0.mate x = F1.mate x := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxe⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxe, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), hmap]
  have hbB : F1.mate b = a := by rw [← hB, F1.mate_mate]
  have haS : a ∉ S.filter fun x ↦ F0.mate x = F1.mate x := by simp [S, mem_pairCompl]
  have hbS : b ∉ insert a (S.filter fun x ↦ F0.mate x = F1.mate x) := by
    simp [S, mem_pairCompl, Ne.symm hab]
  have h1 := Finset.card_insert_of_notMem haS
  have h2 := Finset.card_insert_of_notMem hbS
  have h3 : insert b (insert a (S.filter fun x ↦ F0.mate x = F1.mate x)) ⊆
      Finset.univ.filter fun x ↦ F0.mate x = F1.mate x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · rw [hbB, ← hA, F0.mate_mate]
    · rw [hA, hB]
    · exact hx
  have := Finset.card_le_card h3
  omega

/-- **Lemma 3 with Lemma 4(a)**, matching form (`results/q-second-moment-extend.md` §4 and §5,
af8925f). For perfect matchings `F₀, F₁` of a set of size `2e`, `e ≥ 1`, with
`s = #{x : F₀(x) = F₁(x)}` (twice the number of shared edges), the ratio
`G = jointCount / ψ_e = h/p²` satisfies `G² (2e - 1 - s) ≤ (9/8)² (2e - 1)`. The shared-edge
factor `(2e - 1)/(2e - 2)` enters squared and is absorbed by
`((2e - 1)/(2e - 2))² ≤ (2e - 1)/(2e - 3)`, and the edge-disjoint core is `k2Count_le_betaK`. -/
theorem jointCount_div_psiK_sq_le : ∀ (e : ℕ) (W : Type u) [Fintype W] [DecidableEq W],
    1 ≤ e → Fintype.card W = 2 * e → ∀ F0 F1 : PerfectMatching W,
      ((jointCount F0 F1 : ℝ) / psiK e) ^ 2 *
          (2 * e - 1 - (#{x | F0.mate x = F1.mate x} : ℕ)) ≤ (9 / 8) ^ 2 * (2 * e - 1) := by
  intro e
  induction e with
  | zero => intro W _ _ h; omega
  | succ e ih =>
  intro W _ _ _ hW F0 F1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [jointCount_of_card_eq_two F0 F1 (by rw [hW])]
    have hψ : psiK (0 + 1) = 1 := by norm_num [psiK]
    rw [hψ]
    have : (0 : ℝ) ≤ ((#{x | F0.mate x = F1.mate x} : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hψ := psiK_succ (j := e) he
  have hψ0 := psiK_pos e
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  by_cases h : ∃ a, F0.mate a = F1.mate a
  · obtain ⟨a, ha⟩ := h
    have hA : F0.mate a = F0.mate a := rfl
    have hB : F1.mate a = F0.mate a := ha.symm
    have hab : a ≠ F0.mate a := fun h' ↦ F0.mate_ne a h'.symm
    have hJ := jointCount_eq_of_mate_eq hA hB (by rw [hW]; omega)
    have hS : Fintype.card (pairCompl a (F0.mate a)) = 2 * e := by
      rw [Fintype.card_coe, card_pairCompl hab, hW]
      omega
    have hih := ih (pairCompl a (F0.mate a)) he hS (restrict F0 _ (mate_mem_pairCompl hA))
      (restrict F1 _ (mate_mem_pairCompl hB))
    have hs := card_agree_restrict_add_two_le hA hB
    set J' := jointCount (restrict F0 _ (mate_mem_pairCompl hA))
      (restrict F1 _ (mate_mem_pairCompl hB))
    set s' := #{x | (restrict F0 (pairCompl a (F0.mate a)) (mate_mem_pairCompl hA)).mate x =
        (restrict F1 (pairCompl a (F0.mate a)) (mate_mem_pairCompl hB)).mate x}
    set s := #{x | F0.mate x = F1.mate x}
    have hs' : (s' : ℝ) + 2 ≤ s := by exact_mod_cast hs
    rw [hJ, hW, show 2 * (e + 1) - 2 = 2 * e by omega, hψ]
    have hG : ((2 * e * J' : ℕ) : ℝ) / ((2 * e : ℝ) ^ 2 / (2 * e + 1) * psiK e) =
        (2 * e + 1) / (2 * e) * ((J' : ℝ) / psiK e) := by
      push_cast
      field_simp
    rw [hG, mul_pow]
    set G := (J' : ℝ) / psiK e
    have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
    have hr : ((2 * (e : ℝ) + 1) / (2 * e)) ^ 2 * (2 * e - 1) ≤ 2 * e + 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hr0 : 0 ≤ ((2 * (e : ℝ) + 1) / (2 * e)) ^ 2 := sq_nonneg _
    push_cast
    calc ((2 * (e : ℝ) + 1) / (2 * e)) ^ 2 * G ^ 2 * (2 * (e + 1) - 1 - s)
        ≤ ((2 * (e : ℝ) + 1) / (2 * e)) ^ 2 * (G ^ 2 * (2 * e - 1 - s')) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hG2) hr0
      _ ≤ ((2 * (e : ℝ) + 1) / (2 * e)) ^ 2 * ((9 / 8) ^ 2 * (2 * e - 1)) :=
          mul_le_mul_of_nonneg_left hih hr0
      _ ≤ (9 / 8) ^ 2 * (2 * (e + 1) - 1) := by nlinarith
  · simp only [not_exists] at h
    have hs0 : #{x | F0.mate x = F1.mate x} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun x _ ↦ h x
    rw [hs0, jointCount_eq_k2Count]
    have hsum : (pairType F0 F1).sum = e + 1 := by
      have := two_mul_sum_pairType F0 F1
      omega
    have hK := k2Count_le_betaK (e + 1) (pairType F0 F1) hsum (two_le_of_mem_pairType h)
      (by omega)
    have hψ1 := psiK_pos (e + 1)
    have hT : potT (e + 1) ≤ 9 / 8 := by
      unfold potT
      have : (0 : ℝ) ≤ 1 / (2 * ((e + 1 : ℕ) : ℝ)) := by positivity
      linarith
    have hG : (k2Count (pairType F0 F1) : ℝ) / psiK (e + 1) ≤ 9 / 8 := by
      rw [div_le_iff₀ hψ1]
      unfold betaK at hK
      nlinarith
    have hG0 : 0 ≤ (k2Count (pairType F0 F1) : ℝ) / psiK (e + 1) := by positivity
    have hsq : ((k2Count (pairType F0 F1) : ℝ) / psiK (e + 1)) ^ 2 ≤ (9 / 8) ^ 2 :=
      pow_le_pow_left₀ hG0 hG 2
    push_cast
    have h0 : (0 : ℝ) ≤ 2 * ((e : ℝ) + 1) - 1 := by linarith
    nlinarith

end Matching

end PerfectMatching

end Pairing
