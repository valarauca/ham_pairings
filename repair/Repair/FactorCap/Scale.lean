import Suppression.HamCount

/-!
# Scaling of round-robin factors (P9, task T1)

For a unit `a` of `ℤ/(2m-1)`, `scale m a` is the relabelling `v ↦ a v` of `V_m`, fixing `∞`. It is
the multiplicative twin of `shift`. `scale`, `scale_smul_factor`, `scale_mate_factor`,
`affine_smul_factor` and `isZeroState_affine_smul_iff` are in ham-spin `core/Pairing/Affine.lean`
(ham-spin c1941cf), with the same names.

* `ham_factor_of_isUnit_sub` : `F_s ∪ F_t` is one cycle whenever `s - t` is a unit.

Source: `results/cod-186-direct-construction-spike.md`, Lemma 1 (the coordinate `y = λ(v - s)`)
and Lemma 4 (affine maps permute the factors), and the scaling step of
`results/lean-scope-p9-p10.md` §1.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- `F_s ∪ F_t` is one cycle whenever `s - t` is a unit, the "if" half of the gcd law of
`cod-149-core-sharpening.md`, Theorem B(i). The "only if" half is `isUnit_sub_of_ham`. -/
theorem ham_factor_of_isUnit_sub (m : ℕ) [NeZero m] {s t : ZMod (2 * m - 1)}
    (hu : IsUnit (s - t)) : Ham (factor m s) (factor m t) := by
  have h1 := affine_smul_factor m hu.unit t 1
  have h0 := affine_smul_factor m hu.unit t 0
  rw [IsUnit.unit_spec, mul_one, sub_add_cancel] at h1
  rw [mul_zero, zero_add] at h0
  rw [← h1, ← h0, ham_smul]
  exact ham_factor_one m

end RoundRobin.Canonical

end Pairing
