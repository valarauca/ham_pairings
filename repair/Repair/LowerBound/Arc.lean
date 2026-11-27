import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Ring

/-!
# A translation with finitely many jumps is one cycle

This is the walk argument behind the `K = 1` lower bound of `results/struct-lb-contra.md`
Theorem 1 and `results/struct-lb-extend.md` Theorem A (organize-archive b5cb45e).

A permutation `σ` of `α` is read through a parametrisation `e : ℤ → α` of period `n`. Off the
`r + 1` points `e (q i)`, with `q` strictly increasing and `q last < q 0 + n`, the map `σ` steps
`e v ↦ e (v + 1)`. At `e (q i)` it jumps to `e (q (ρ i) + 1)`.

The arc `i` is the run `e (q i + 1), …, e (q (i + 1))`, with `q (last + 1)` read as `q 0 + n`.
`σ` walks along it and then jumps to the start of arc `ρ (i + 1)`.

* `sameCycle_of_arcs` : if every arc is reached from arc `0` by iterating `i ↦ ρ (i + 1)`, then
  `σ` is a single cycle through every point of `α`.
-/

namespace Pairing

namespace LowerBound

open Equiv

variable {α : Type*}

/-- **The arc walk** (`results/struct-lb-contra.md` Theorem 1 and `results/struct-lb-extend.md`
Theorem A, organize-archive b5cb45e). Let `e : ℤ → α` be onto, of period `n`, and injective
modulo `n`. Let `q` be strictly increasing with `q last < q 0 + n`. If `σ (e v) = e (v + 1)`
whenever `e v` is none of the `e (q i)`, and `σ (e (q i)) = e (q (ρ i) + 1)`, and every index is
reached from `0` by iterating `i ↦ ρ (i + 1)`, then any two points share a `σ`-cycle. -/
theorem sameCycle_of_arcs {n r : ℕ} (σ : Perm α) (e : ℤ → α)
    (hper : ∀ v k : ℤ, e (v + k * n) = e v) (hsurj : Function.Surjective e)
    (hinj : ∀ v w, e v = e w → (n : ℤ) ∣ v - w)
    (q : Fin (r + 1) → ℤ) (hq : StrictMono q) (hqn : q (Fin.last r) < q 0 + n)
    (ρ : Fin (r + 1) → Fin (r + 1))
    (hstep : ∀ v, (∀ i, e v ≠ e (q i)) → σ (e v) = e (v + 1))
    (hjump : ∀ i, σ (e (q i)) = e (q (ρ i) + 1))
    (hcyc : ∀ j, ∃ k : ℕ, (fun i ↦ ρ (i + 1))^[k] 0 = j) (x y : α) :
    σ.SameCycle x y := by
  set Q : Fin (r + 1) → ℤ := fun i ↦ if i = Fin.last r then q 0 + n else q (i + 1) with hQ
  have hle0 : ∀ l, q 0 ≤ q l := fun l ↦ hq.monotone (Fin.zero_le l)
  have hlel : ∀ l, q l ≤ q (Fin.last r) := fun l ↦ hq.monotone (Fin.le_last l)
  have hQle : ∀ i, Q i ≤ q 0 + n := by
    intro i
    by_cases hi : i = Fin.last r
    · simp [hQ, hi]
    · simp only [hQ, hi, ↓reduceIte]
      exact (hlel _).trans hqn.le
  have hlt : ∀ i, q i < Q i := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi
      simp only [hQ, ↓reduceIte]
      exact hqn
    · simp only [hQ, hi, ↓reduceIte]
      exact hq (Fin.lt_add_one_iff.mpr (lt_of_le_of_ne (Fin.le_last i) hi))
  have heQ : ∀ i, e (Q i) = e (q (i + 1)) := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi
      simp only [hQ, ↓reduceIte, Fin.last_add_one]
      simpa using hper (q 0) 1
    · simp [hQ, hi]
  have hfree : ∀ i z, q i < z → z < Q i → ∀ l, e z ≠ e (q l) := by
    intro i z hz1 hz2 l hzl
    have hd := hinj _ _ hzl
    have hz0 : z = q l := by
      have h1 := hle0 i
      have h2 := hQle i
      have h3 := hle0 l
      have h4 := hlel l
      have habs : |z - q l| < n := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd habs
      omega
    subst hz0
    have hil : i < l := hq.lt_iff_lt.mp hz1
    by_cases hi : i = Fin.last r
    · exact absurd (hi ▸ hil) (not_lt.mpr (Fin.le_last l))
    · simp only [hQ, hi, ↓reduceIte] at hz2
      have hl : l < i + 1 := hq.lt_iff_lt.mp hz2
      have hval : ((i + 1 : Fin (r + 1)) : ℕ) = i + 1 :=
        Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last i) hi)
      rw [Fin.lt_def, hval] at hl
      rw [Fin.lt_def] at hil
      omega
  have hwalk : ∀ i (k : ℕ), q i + 1 + k ≤ Q i → (σ ^ k) (e (q i + 1)) = e (q i + 1 + k) := by
    intro i k
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by push_cast at hk; omega),
        hstep _ (hfree i _ (by omega) (by push_cast at hk; omega))]
      push_cast
      ring_nf
  have htrans : ∀ i, σ.SameCycle (e (q i + 1)) (e (q (ρ (i + 1)) + 1)) := by
    intro i
    have h1 := hwalk i (Q i - q i - 1).toNat (by have := hlt i; omega)
    have h2 : q i + 1 + ((Q i - q i - 1).toNat : ℤ) = Q i := by have := hlt i; omega
    rw [h2, heQ] at h1
    rw [← hjump, Perm.sameCycle_apply_right, ← h1]
    exact Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _)
  have hchain : ∀ k : ℕ, σ.SameCycle (e (q 0 + 1)) (e (q ((fun i ↦ ρ (i + 1))^[k] 0) + 1)) := by
    intro k
    induction k with
    | zero => exact Perm.SameCycle.refl _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (htrans _)
  have hn : (0 : ℤ) < n := by have := hle0 (Fin.last r); omega
  have hcover : ∀ z, σ.SameCycle (e (q 0 + 1)) z := by
    intro z
    obtain ⟨v, rfl⟩ := hsurj z
    set w := q 0 + 1 + (v - q 0 - 1) % n with hw
    have hew : e w = e v := by
      have h := hper v (-((v - q 0 - 1) / n))
      rw [← h]
      congr 1
      rw [hw, Int.emod_def]
      ring
    have hw1 : q 0 < w := by have := Int.emod_nonneg (v - q 0 - 1) hn.ne'; omega
    have hw2 : w ≤ q 0 + n := by have := Int.emod_lt_of_pos (v - q 0 - 1) hn; omega
    set s := Finset.univ.filter fun i ↦ q i < w with hs
    have hsne : s.Nonempty := ⟨0, by simp [hs, hw1]⟩
    set i₀ := s.max' hsne with hi₀
    have hi₀s : q i₀ < w := by
      have := s.max'_mem hsne
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hwQ : w ≤ Q i₀ := by
      by_cases hi : i₀ = Fin.last r
      · simp only [hQ, hi, ↓reduceIte]
        exact hw2
      · simp only [hQ, hi, ↓reduceIte]
        by_contra hcon
        have hmem : i₀ + 1 ∈ s := by simp [hs]; omega
        have h1 := s.le_max' _ hmem
        rw [← hi₀] at h1
        exact absurd h1 (not_le.mpr (Fin.lt_add_one_iff.mpr (lt_of_le_of_ne (Fin.le_last _) hi)))
    obtain ⟨k, hk⟩ := hcyc i₀
    have h1 := hwalk i₀ (w - q i₀ - 1).toNat (by omega)
    have h2 : q i₀ + 1 + ((w - q i₀ - 1).toNat : ℤ) = w := by omega
    rw [h2, hew] at h1
    rw [← h1]
    refine (hchain k).trans ?_
    rw [hk]
    exact Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _)
  exact (hcover x).symm.trans (hcover y)

end LowerBound

end Pairing
