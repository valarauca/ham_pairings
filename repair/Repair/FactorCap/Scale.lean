import Suppression.HamCount

/-!
# Scaling of round-robin factors (P9, task T1)

For a unit `a` of `ℤ/(2m-1)`, `scale m a` is the relabelling `v ↦ a v` of `V_m`, fixing `∞`. It is
the multiplicative twin of `shift`.

* `scale_smul_factor` : `scale m a` maps `F_t` to `F_{a t}`, the twin of `shift_smul_factor`.
* `scale_mate_factor` : the pointwise form `a F_t(v) = F_{a t}(a v)`.
* `affine_smul_factor` : the affine map `v ↦ a v + b` maps `F_t` to `F_{a t + b}`.
* `isZeroState_affine_smul_iff` : affine maps preserve zero states.

Source: `results/cod-186-direct-construction-spike.md`, Lemma 1 (the coordinate `y = λ(v - s)`)
and Lemma 4 (affine maps permute the factors), and the scaling step of
`results/lean-scope-p9-p10.md` §1.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- The scaling `v ↦ a v` of `V_m` by a unit `a`, fixing `∞`. -/
def scale (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) : Equiv.Perm (Vertex m) :=
  Equiv.optionCongr a.mulLeft

/-- The scaling fixes `∞`. -/
@[simp]
theorem scale_none (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) : scale m a none = none :=
  rfl

/-- The scaling sends `x` to `a x`. -/
@[simp]
theorem scale_some (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (x : ZMod (2 * m - 1)) :
    scale m a (some x) = some (a * x) :=
  rfl

/-- The inverse scaling fixes `∞`. -/
@[simp]
theorem scale_inv_none (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) :
    (scale m a)⁻¹ none = none := by
  rw [Equiv.Perm.inv_eq_iff_eq, scale_none]

/-- The inverse scaling sends `x` to `a⁻¹ x`. -/
@[simp]
theorem scale_inv_some (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (x : ZMod (2 * m - 1)) :
    (scale m a)⁻¹ (some x) = some (↑a⁻¹ * x) := by
  rw [Equiv.Perm.inv_eq_iff_eq, scale_some, ← mul_assoc, Units.mul_inv, one_mul]

/-- The scaling by `a` maps `F_t` to `F_{a t}` (Lemma 1 of
`cod-186-direct-construction-spike.md`). -/
theorem scale_smul_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (t : ZMod (2 * m - 1)) :
    scale m a • factor m t = factor m (a * t) := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rcases v with _ | y
  · simp [factor]
  rcases eq_or_ne y (a * t) with rfl | hy
  · simp [factor]
  have h : ↑a⁻¹ * y ≠ t := fun h ↦ hy (by rw [← h, ← mul_assoc, Units.mul_inv, one_mul])
  simp only [smul_mate, scale_inv_some, factor, factor_mate, mateFn_of_ne _ _ h,
    mateFn_of_ne _ _ hy, scale_some, Option.some_inj]
  linear_combination (-y) * Units.mul_inv a

/-- The pointwise form of `scale_smul_factor`, `a F_t(v) = F_{a t}(a v)`. -/
theorem scale_mate_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (t : ZMod (2 * m - 1))
    (v : Vertex m) : scale m a ((factor m t).mate v) = (factor m (a * t)).mate (scale m a v) := by
  rw [← scale_smul_factor, smul_mate]
  simp

/-- The affine map `v ↦ a v + b` maps `F_t` to `F_{a t + b}`. -/
theorem affine_smul_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (b t : ZMod (2 * m - 1)) :
    (shift m b * scale m a) • factor m t = factor m (a * t + b) := by
  rw [mul_smul, scale_smul_factor, shift_smul_factor]

/-- Affine maps preserve zero states, `IsZeroState F (σ • P) ↔ IsZeroState F P` for
`σ = (v ↦ a v + b)`. -/
theorem isZeroState_affine_smul_iff (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ)
    (b : ZMod (2 * m - 1)) (P : PerfectMatching (Vertex m)) :
    IsZeroState (factor m) ((shift m b * scale m a) • P) ↔ IsZeroState (factor m) P := by
  have hs : Function.Surjective fun t : ZMod (2 * m - 1) ↦ ↑a * t + b := fun s ↦
    ⟨↑a⁻¹ * (s - b), by
      simp only
      rw [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]⟩
  constructor
  · intro h t
    rw [← ham_smul (shift m b * scale m a), affine_smul_factor]
    exact h _
  · intro h s
    obtain ⟨t, rfl⟩ := hs s
    rw [← affine_smul_factor, ham_smul]
    exact h t

end RoundRobin.Canonical

end Pairing
