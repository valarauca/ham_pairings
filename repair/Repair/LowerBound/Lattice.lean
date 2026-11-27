import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemmas L and D of the `K = 2` argument

Source: `results/struct-lb-extend.md` §3.1 (Lemma L, Lemma D) and §3.3 (Theorem B, case 2), with
`results/struct-lb-factcheck-extend.md` §3, claims 4, 5 and 7 (organize-archive b5cb45e). The
contra form is `results/struct-lb-contra.md` §3.2, Theorem 2 (b5cb45e).

For a prime `n` and a label `X`, the samples `p_μ = (μ, Xμ)/n mod ℤ²` of a 1-core `{e_{X/2}}`
are the points of `Λ_X / n` mod `ℤ²`, where `Λ_X = {(c, a) ∈ ℤ² : a ≡ X c mod n}` has
determinant `n`.

* `exists_shortVector` : **Lemma L (i), (ii)**. `Λ_X` has a shortest nonzero vector `(c, a)`,
  with `L² = c² + a²`, `3 L⁴ ≤ 4 n²` (Hermite's `γ₂ = 2/√3`), `gcd(c, a) = 1` and `n ∤ c`.
* `exists_eq_smul_add_of_inLattice` : **Lemma L (iii)**. `Λ_X = ℤ(c, a) + nℤ²`, so every sample
  is `ν(c, a)/n mod ℤ²`.
* `dvd_cross_of_inLattice` : **Lemma L (iv)**. Every point of `Λ_X / n` lies on a line
  `a q₁ - c q₂ ∈ ℤ`.
* `exists_inLattice_dist_lt` : **Lemma D**. If `r² > 1/(4L²) + L²/(4n²)`, every open disk of
  radius `r` contains a point of `Λ_X / n`. This is the source's pair of conditions
  `1/(2L) < r` and `2√(r² - 1/(4L²)) > L/n`, squared.
* `threshold_two_one_three_seven` : the numerical step of Theorem B case 2. For `n ≥ 2137`,
  `L² ≥ 901` and `3 L⁴ ≤ 4 n²`, the certificate radius `r = 13/640` satisfies Lemma D.

The certificate disks, the 844-line table and the cell contexts of Theorem B are not formalized
here.
-/

namespace Pairing

namespace LowerBound

/-- `(c, a) ∈ Λ_X`, that is `a ≡ X c (mod n)` (`results/struct-lb-extend.md` Lemma L,
organize-archive b5cb45e). -/
def InLattice (n : ℕ) (X c a : ℤ) : Prop :=
  (n : ℤ) ∣ a - X * c

/-- `Λ_X` is closed under `ℤ`-combinations (`results/struct-lb-extend.md` Lemma L,
organize-archive b5cb45e). -/
theorem inLattice_add_smul {n : ℕ} {X c a c' a' : ℤ} (k l : ℤ) (h : InLattice n X c a)
    (h' : InLattice n X c' a') : InLattice n X (k * c + l * c') (k * a + l * a') := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := h'
  exact ⟨k * x + l * y, by linear_combination k * hx + l * hy⟩

/-- `n ℤ² ⊆ Λ_X` (`results/struct-lb-extend.md` Lemma L, organize-archive b5cb45e). -/
theorem inLattice_nsmul (n : ℕ) (X u v : ℤ) : InLattice n X (n * u) (n * v) :=
  ⟨v - X * u, by ring⟩

/-- **Lemma L (iv)** (`results/struct-lb-extend.md` §3.1, organize-archive b5cb45e). For
`(c, a), (c', a') ∈ Λ_X`, `n ∣ a c' - c a'`, so `(c', a')/n` lies on a line `a q₁ - c q₂ ∈ ℤ`. -/
theorem dvd_cross_of_inLattice {n : ℕ} {X c a c' a' : ℤ} (h : InLattice n X c a)
    (h' : InLattice n X c' a') : (n : ℤ) ∣ a * c' - c * a' := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := h'
  exact ⟨x * c' - c * y, by linear_combination c' * hx - c * hy⟩

/-- `(c² + a²)(x² + y²) = (c x + a y)² + (c y - a x)²`, Lagrange's identity in dimension 2
(`results/struct-lb-extend.md` Lemma L (i), organize-archive b5cb45e). -/
theorem lagrange_two {R : Type*} [CommRing R] (c a x y : R) :
    (c ^ 2 + a ^ 2) * (x ^ 2 + y ^ 2) = (c * x + a * y) ^ 2 + (c * y - a * x) ^ 2 := by
  ring

/-- **Lemma L (i), (ii)** (`results/struct-lb-extend.md` §3.1, organize-archive b5cb45e). For a
prime `n` and any `X`, the lattice `Λ_X` has a nonzero vector `(c, a)` of least norm
`L² = c² + a²`. It satisfies Hermite's bound `3 L⁴ ≤ 4 n²`, that is `L² ≤ 2n/√3`, and
`gcd(c, a) = 1` and `n ∤ c`. -/
theorem exists_shortVector {n : ℕ} (hn : n.Prime) (X : ℤ) :
    ∃ c a : ℤ, InLattice n X c a ∧ (c ≠ 0 ∨ a ≠ 0) ∧
      (∀ c' a', InLattice n X c' a' → (c' ≠ 0 ∨ a' ≠ 0) → c ^ 2 + a ^ 2 ≤ c' ^ 2 + a' ^ 2) ∧
      3 * (c ^ 2 + a ^ 2) ^ 2 ≤ 4 * (n : ℤ) ^ 2 ∧ Int.gcd c a = 1 ∧ ¬(n : ℤ) ∣ c := by
  have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn.two_le
  have hex : ∃ N : ℕ, ∃ c a : ℤ, InLattice n X c a ∧ (c ≠ 0 ∨ a ≠ 0) ∧ c ^ 2 + a ^ 2 = N :=
    ⟨1 + (X % n).toNat ^ 2, 1, X % n, ⟨-(X / n), by rw [Int.emod_def]; ring⟩, Or.inl one_ne_zero,
      by rw [Nat.cast_add, Nat.cast_pow, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))];
         ring⟩
  classical
  obtain ⟨c, a, hlat, hne, hN⟩ := Nat.find_spec hex
  have hmin : ∀ c' a', InLattice n X c' a' → (c' ≠ 0 ∨ a' ≠ 0) →
      c ^ 2 + a ^ 2 ≤ c' ^ 2 + a' ^ 2 := by
    intro c' a' h' hne'
    rw [hN, ← Int.toNat_of_nonneg (by positivity : 0 ≤ c' ^ 2 + a' ^ 2)]
    exact_mod_cast Nat.find_min' hex ⟨c', a', h', hne', (Int.toNat_of_nonneg (by positivity)).symm⟩
  clear hN
  have hpos : 0 < c ^ 2 + a ^ 2 := by
    rcases hne with h | h
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      positivity
  have hsmall : c ^ 2 + a ^ 2 < (n : ℤ) ^ 2 := by
    have h1 := hmin 1 (X % n) ⟨-(X / n), by rw [Int.emod_def]; ring⟩ (Or.inl one_ne_zero)
    have h2 := Int.emod_nonneg X (by omega : (n : ℤ) ≠ 0)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < n)
    nlinarith
  have hbig : ∀ c' a' : ℤ, (n : ℤ) ∣ c' → (n : ℤ) ∣ a' → (c' ≠ 0 ∨ a' ≠ 0) →
      (n : ℤ) ^ 2 ≤ c' ^ 2 + a' ^ 2 := by
    rintro c' a' ⟨x, rfl⟩ ⟨y, rfl⟩ hne'
    have hxy : x ≠ 0 ∨ y ≠ 0 := by
      rcases hne' with h | h
      · exact Or.inl (right_ne_zero_of_mul h)
      · exact Or.inr (right_ne_zero_of_mul h)
    have : 1 ≤ x ^ 2 + y ^ 2 := by
      rcases hxy with h | h
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg y]
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg x]
    nlinarith
  have hnc : ¬(n : ℤ) ∣ c := by
    intro hc
    have ha : (n : ℤ) ∣ a := by
      obtain ⟨x, hx⟩ := hlat
      obtain ⟨y, hy⟩ := hc
      exact ⟨x + X * y, by linear_combination hx + X * hy⟩
    exact absurd (hbig c a hc ha hne) (not_le.mpr hsmall)
  have hgcd : Int.gcd c a = 1 := by
    by_contra hg
    set g := Int.gcd c a with hgdef
    have hg0 : g ≠ 0 := fun h ↦ by
      rcases hne with h' | h'
      · exact h' (Int.gcd_eq_zero_iff.mp h).1
      · exact h' (Int.gcd_eq_zero_iff.mp h).2
    have hg2 : (2 : ℤ) ≤ g := by omega
    obtain ⟨c₁, hc₁⟩ := Int.gcd_dvd_left (a := c) (b := a)
    obtain ⟨a₁, ha₁⟩ := Int.gcd_dvd_right (a := c) (b := a)
    rw [← hgdef] at hc₁ ha₁
    have hng : ¬(n : ℤ) ∣ (g : ℤ) := fun h ↦ hnc (h.trans ⟨c₁, hc₁⟩)
    have hcop : IsCoprime (n : ℤ) (g : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hn.coprime_iff_not_dvd.mpr fun h ↦ hng (Int.natCast_dvd_natCast.mpr h)
    have hlat₁ : InLattice n X c₁ a₁ := by
      apply hcop.dvd_of_dvd_mul_left
      rw [show (g : ℤ) * (a₁ - X * c₁) = a - X * c by rw [hc₁, ha₁]; ring]
      exact hlat
    have hne₁ : c₁ ≠ 0 ∨ a₁ ≠ 0 := by
      rcases hne with h | h
      · exact Or.inl fun h' ↦ h (by rw [hc₁, h', mul_zero])
      · exact Or.inr fun h' ↦ h (by rw [ha₁, h', mul_zero])
    have h1 := hmin c₁ a₁ hlat₁ hne₁
    rw [hc₁, ha₁] at h1 hpos
    have hp₁ : 0 < c₁ ^ 2 + a₁ ^ 2 := by nlinarith
    have h4 : 4 * (c₁ ^ 2 + a₁ ^ 2) ≤ (g : ℤ) ^ 2 * (c₁ ^ 2 + a₁ ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hp₁.le
    nlinarith
  refine ⟨c, a, hlat, hne, hmin, ?_, hgcd, hnc⟩
  have hbez := Int.gcd_eq_gcd_ab c a
  rw [hgcd, Nat.cast_one] at hbez
  set A := Int.gcdA c a
  set B := Int.gcdB c a
  set N := c ^ 2 + a ^ 2 with hNdef
  set s := c * (-(n * B)) + a * (n * A) with hs
  set k := (2 * s + N) / (2 * N) with hk
  have hk1 : 2 * N * k ≤ 2 * s + N := Int.mul_ediv_self_le (by omega)
  have hk2 : 2 * s + N < 2 * N * (k + 1) := by
    have := Int.lt_mul_ediv_self_add (x := 2 * s + N) (by omega : 0 < 2 * N)
    linarith
  set x := -(n * B) - k * c
  set y := n * A - k * a
  have hlat₂ : InLattice n X x y := by
    have := inLattice_add_smul (-k) 1 hlat (inLattice_nsmul n X (-B) A)
    convert this using 1 <;> ring
  have hcross : c * y - a * x = n := by
    simp only [x, y]
    linear_combination (-(n : ℤ)) * hbez
  have hne₂ : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2] at hcross
    omega
  have h1 := hmin x y hlat₂ hne₂
  have hdot : c * x + a * y = s - k * N := by
    simp only [x, y, hs, hNdef]
    ring
  have hL := lagrange_two c a x y
  rw [hdot, hcross] at hL
  nlinarith

/-- **Lemma L (iii)** (`results/struct-lb-extend.md` §3.1, organize-archive b5cb45e). For a prime
`n` and `(c, a) ∈ Λ_X` with `n ∤ c`, every `(c', a') ∈ Λ_X` is `ν (c, a) + n (u, v)`. So the
samples `p_μ` are the points `ν (c, a)/n mod ℤ²`. -/
theorem exists_eq_smul_add_of_inLattice {n : ℕ} (hn : n.Prime) {X c a c' a' : ℤ}
    (h : InLattice n X c a) (hc : ¬(n : ℤ) ∣ c) (h' : InLattice n X c' a') :
    ∃ ν u v : ℤ, c' = ν * c + n * u ∧ a' = ν * a + n * v := by
  have hcop : IsCoprime c (n : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime n c.natAbs :=
      hn.coprime_iff_not_dvd.mpr fun h1 ↦ hc (Int.natCast_dvd.mpr h1)
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using h1
  obtain ⟨x, y, hxy⟩ := hcop
  obtain ⟨xh, hx⟩ := h
  obtain ⟨yh, hy⟩ := h'
  exact ⟨c' * x, c' * y, yh - c' * x * xh + X * c' * y, by linear_combination (-c') * hxy,
    by linear_combination hy - c' * x * hx - X * c' * hxy⟩

/-- **Lemma D** (`results/struct-lb-extend.md` §3.1, organize-archive b5cb45e). Let
`(c, a) ∈ Λ_X` be primitive, with `L² = c² + a²`. If `r² > 1/(4L²) + L²/(4n²)`, then every open
disk of radius `r`, centred at `(z₁, z₂)`, contains a point `(c', a')/n` with `(c', a') ∈ Λ_X`.
Some line `a q₁ - c q₂ = j` passes within `1/(2L)` of the centre, and along it the points of
`Λ_X / n` have step `L/n`. -/
theorem exists_inLattice_dist_lt {n : ℕ} (hn : 0 < n) {X c a : ℤ} (h : InLattice n X c a)
    (hca : Int.gcd c a = 1) (z₁ z₂ r : ℝ)
    (hr : 1 / (4 * ((c : ℝ) ^ 2 + (a : ℝ) ^ 2)) + ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / (4 * (n : ℝ) ^ 2) <
      r ^ 2) :
    ∃ c' a' : ℤ, InLattice n X c' a' ∧
      ((c' : ℝ) / n - z₁) ^ 2 + ((a' : ℝ) / n - z₂) ^ 2 < r ^ 2 := by
  have hbez := Int.gcd_eq_gcd_ab c a
  rw [hca, Nat.cast_one] at hbez
  set A := Int.gcdA c a
  set B := Int.gcdB c a
  have hL : (0 : ℝ) < (c : ℝ) ^ 2 + (a : ℝ) ^ 2 := by
    rcases eq_or_ne c 0 with hc | hc
    · have ha : a ≠ 0 := fun ha ↦ by rw [hc, ha] at hbez; simp at hbez
      have : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
      positivity
    · have : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
      positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set j : ℤ := round ((a : ℝ) * z₁ - c * z₂) with hj
  set u : ℤ := j * B
  set v : ℤ := -(j * A)
  have huv : (a : ℝ) * u - c * v = j := by
    have := congrArg (fun z : ℤ ↦ (z : ℝ)) hbez
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul] at this
    simp only [u, v, Int.cast_mul, Int.cast_neg]
    linear_combination (-(j : ℝ)) * this
  set s : ℝ := (u - z₁) * c + (v - z₂) * a
  set k : ℤ := round (-(s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2))) with hk
  refine ⟨n * u + k * c, n * v + k * a, ?_, ?_⟩
  · have := inLattice_add_smul k 1 h (inLattice_nsmul n X u v)
    convert this using 1 <;> ring
  · have hk' : |s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) + k| ≤ 1 / 2 := by
      have := abs_sub_round (-(s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2)))
      rw [← hk, abs_sub_comm] at this
      rwa [show (k : ℝ) - -(s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2)) =
        s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) + k by ring] at this
    have hj' : |(a : ℝ) * z₁ - c * z₂ - j| ≤ 1 / 2 := abs_sub_round _
    set D₁ : ℝ := ((n * u + k * c : ℤ) : ℝ) / n - z₁
    set D₂ : ℝ := ((n * v + k * a : ℤ) : ℝ) / n - z₂
    have h1 : (c : ℝ) * D₁ + a * D₂ = ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / n *
        (s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) + k) := by
      simp only [D₁, D₂, s]
      push_cast
      field_simp
      ring
    have h2 : (a : ℝ) * D₁ - c * D₂ = -((a : ℝ) * z₁ - c * z₂ - j) := by
      simp only [D₁, D₂]
      push_cast
      field_simp
      linear_combination (n : ℝ) * huv
    have h3 : ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) * (D₁ ^ 2 + D₂ ^ 2) =
        (c * D₁ + a * D₂) ^ 2 + (a * D₁ - c * D₂) ^ 2 := by
      ring
    have h4 : (s * n / ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) + k) ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp hk'
      nlinarith
    have h5 : ((a : ℝ) * z₁ - c * z₂ - j) ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp hj'
      nlinarith
    have h6 : ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) * (D₁ ^ 2 + D₂ ^ 2) ≤
        (((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / n) ^ 2 * (1 / 4) + 1 / 4 := by
      rw [h3, h1, h2, mul_pow, neg_sq]
      have := mul_le_mul_of_nonneg_left h4 (sq_nonneg (((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / n))
      linarith
    have h7 : D₁ ^ 2 + D₂ ^ 2 ≤
        1 / (4 * ((c : ℝ) ^ 2 + (a : ℝ) ^ 2)) +
          ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / (4 * (n : ℝ) ^ 2) := by
      rw [show 1 / (4 * ((c : ℝ) ^ 2 + (a : ℝ) ^ 2)) +
          ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / (4 * (n : ℝ) ^ 2) =
          ((((c : ℝ) ^ 2 + (a : ℝ) ^ 2) / n) ^ 2 * (1 / 4) + 1 / 4) /
            ((c : ℝ) ^ 2 + (a : ℝ) ^ 2) by
        field_simp
        ring, le_div_iff₀ hL]
      linarith
    exact h7.trans_lt hr

/-- **The threshold `n ≥ 2137`** (`results/struct-lb-extend.md` §3.3, Theorem B case 2, and
`scripts/struct-lb-e-bounds.out`, organize-archive b5cb45e). If `L² ≥ 901` and `3 L⁴ ≤ 4 n²`
(Lemma L (i)), then `1/(4L²) + L²/(4n²) < (13/640)²` once `n ≥ 2137`, so Lemma D applies to the
certificate disks of radius `13/640`. The bound is exact: `struct-lb-factcheck-extend.md` §3
finds it fails at `n = 2136`. -/
theorem threshold_two_one_three_seven {n L2 : ℝ} (hn : 2137 ≤ n) (hL : 901 ≤ L2)
    (hH : 3 * L2 ^ 2 ≤ 4 * n ^ 2) : 1 / (4 * L2) + L2 / (4 * n ^ 2) < (13 / 640) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have h1 : 1 / (4 * L2) ≤ 1 / 3604 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  set δ : ℝ := (13 / 640) ^ 2 - 1 / 3604 with hδ
  have hδ0 : 0 < δ := by norm_num [hδ]
  have h2 : L2 / (4 * n ^ 2) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    by_contra hcon
    push Not at hcon
    have h3 : (δ * (4 * n ^ 2)) ^ 2 ≤ L2 ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcon 2
    have h4 : 12 * δ ^ 2 * n ^ 2 ≤ 1 := by
      have hn2 : 0 < n ^ 2 := by positivity
      nlinarith
    have h5 : 1 < 12 * δ ^ 2 * 2137 ^ 2 := by norm_num [hδ]
    have h6 : (2137 : ℝ) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by norm_num) hn 2
    nlinarith [sq_nonneg δ]
  linarith

/-- **Theorem B, case 2, the dichotomy** (`results/struct-lb-extend.md` §3.3, organize-archive
b5cb45e). For a prime `n ≥ 2137` and any label `X`, either `Λ_X` has a nonzero vector with
`c² + a² ≤ 900` (the line case, closed by the 844-line table), or every open disk of radius
`13/640` contains a point of `Λ_X / n` (the generic case, closed by the 105 certificate disks).
-/
theorem shortVector_or_forall_disk {n : ℕ} (hn : n.Prime) (h2137 : 2137 ≤ n) (X : ℤ) :
    (∃ c a : ℤ, InLattice n X c a ∧ (c ≠ 0 ∨ a ≠ 0) ∧ c ^ 2 + a ^ 2 ≤ 900 ∧ Int.gcd c a = 1 ∧
        ¬(n : ℤ) ∣ c) ∨
      ∀ z₁ z₂ : ℝ, ∃ c' a' : ℤ, InLattice n X c' a' ∧
        ((c' : ℝ) / n - z₁) ^ 2 + ((a' : ℝ) / n - z₂) ^ 2 < (13 / 640) ^ 2 := by
  obtain ⟨c, a, hlat, hne, -, hH, hgcd, hnc⟩ := exists_shortVector hn X
  rcases le_or_gt (c ^ 2 + a ^ 2) 900 with hle | hgt
  · exact Or.inl ⟨c, a, hlat, hne, hle, hgcd, hnc⟩
  · refine Or.inr fun z₁ z₂ ↦ exists_inLattice_dist_lt hn.pos hlat hgcd z₁ z₂ _ ?_
    apply threshold_two_one_three_seven (by exact_mod_cast h2137)
    · have : (901 : ℤ) ≤ c ^ 2 + a ^ 2 := hgt
      exact_mod_cast this
    · exact_mod_cast hH

end LowerBound

end Pairing
