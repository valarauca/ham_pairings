import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic

/-!
# Farey neighbour arithmetic for P9

Farey neighbours `p/q < p'/q'` satisfy `p' q - p q' = 1`. Every lattice point `(μ, n)` with
`p/q < μ/n < p'/q'` is then `u (p', q') + w (p, q)` with integers `u, w ≥ 1`, and every linear
form satisfies `A μ - B n = (A p' - B q') u + (A p - B q) w`. So the sign of a form on a whole
open cell follows from its two integer values at the endpoints. That is the sign lemma behind
the cell checker.

`not_farey_hit` is the other half of the covering argument. For a prime `n > 16` and
`0 < μ < n`, `μ/n` is never a fraction of denominator at most 16, so it lies strictly inside
one cell. `not_farey_hit_of_coprime` needs only `n > 16` coprime to `μ`.
-/

namespace Pairing

namespace FactorCap

/-- Neighbour parametrization. If `p' q - p q' = 1` and `p/q < μ/n < p'/q'` (cross-multiplied),
then `(μ, n) = u (p', q') + w (p, q)` for some integers `u, w ≥ 1`. -/
theorem farey_param {p q p' q' μ n : ℤ} (hdet : p' * q - p * q' = 1)
    (hl : p * n < q * μ) (hr : q' * μ < p' * n) :
    ∃ u w : ℤ, 1 ≤ u ∧ 1 ≤ w ∧ μ = u * p' + w * p ∧ n = u * q' + w * q :=
  ⟨q * μ - p * n, p' * n - q' * μ, by linarith, by linarith,
    by linear_combination (-μ) * hdet, by linear_combination (-n) * hdet⟩

/-- The linear form `A μ - B n` at `(μ, n) = u (p', q') + w (p, q)`. -/
theorem form_param (A B u w p q p' q' : ℤ) :
    A * (u * p' + w * p) - B * (u * q' + w * q) =
      (A * p' - B * q') * u + (A * p - B * q) * w := by
  ring

/-- Sign lemma. If the form `A μ - B n` is nonnegative at both endpoints of a Farey cell and
positive at one of them, it is positive at every lattice point strictly inside the cell. -/
theorem form_pos_of_endpoints {p q p' q' μ n A B : ℤ} (hdet : p' * q - p * q' = 1)
    (hl : p * n < q * μ) (hr : q' * μ < p' * n)
    (hX : 0 ≤ A * p' - B * q') (hY : 0 ≤ A * p - B * q)
    (hXY : 0 < A * p' - B * q' + (A * p - B * q)) :
    0 < A * μ - B * n := by
  obtain ⟨u, w, hu, hw, rfl, rfl⟩ := farey_param hdet hl hr
  rw [form_param]
  nlinarith [mul_nonneg hX (sub_nonneg.2 hu), mul_nonneg hY (sub_nonneg.2 hw)]

/-- For `n > 16` coprime to `μ`, `μ/n` is not a fraction with denominator `1 ≤ q ≤ 16`. -/
theorem not_farey_hit_of_coprime {n μ p q : ℕ} (hcop : Nat.Coprime n μ) (h16 : 16 < n)
    (hq0 : 0 < q) (hq : q ≤ 16) : p * n ≠ q * μ := by
  intro h
  have hdvd : n ∣ q * μ := ⟨p, by rw [← h, Nat.mul_comm]⟩
  have := Nat.le_of_dvd hq0 (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-- For a prime `n > 16` and `0 < μ < n`, `μ/n` is not a fraction with denominator
`1 ≤ q ≤ 16`. It is `not_farey_hit_of_coprime` at a prime. -/
theorem not_farey_hit {n μ p q : ℕ} (hn : n.Prime) (h16 : 16 < n) (hμ0 : 0 < μ) (hμn : μ < n)
    (hq0 : 0 < q) (hq : q ≤ 16) : p * n ≠ q * μ :=
  not_farey_hit_of_coprime ((Nat.Prime.coprime_iff_not_dvd hn).2 fun hd ↦
    absurd (Nat.le_of_dvd hμ0 hd) (by omega)) h16 hq0 hq

end FactorCap

end Pairing
