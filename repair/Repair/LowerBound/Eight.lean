import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Repair.LowerBound.Chart
import Repair.LowerBound.ZeroCore

/-!
# The eight-point walk of a finite 1-core

Source: `results/struct-lb-extend.md` §1 (torus form, Lemma 0) and §3.3, Theorem B case 2
(organize-archive b5cb45e).

The 1-core `J = J_0 ∪ {e_{X/2}}` has eight ends. Point `j : Fin 8` has slot `j % 4`, with label
`1, 3, 5, X`, and sign `+` for `j < 4`. It is the vertex `s0 ± λ/2`, so the gadget points are
`4, 5, 6, 3, 2, 1` and the tail edge is `{s0 + x, s0 - x}` with `X = 2x`. `F_{s0}` swaps `j` and
`j + 4`.

A context is a cyclic order `o` of the eight points, given as a list. At a point `(x, y)` of the
plane, with integer shifts `k`, point `j` has the value `± (λ x - k)` (slots `0, 1, 2`) or
`± (y - k)` (slot `3`). `RealCell8 o k x y` says that these values increase strictly along `o`,
with the last below the first plus `1`. Every linear form involved has a normal in the list of
`results/struct-lb-extend.md` §3.2, so this is the open cell of Lemma 0.

* `ham_of_realCell8` : if the lift `(μ', a')/n` of a sample, with `a' ≡ X μ'`, lies in the cell
  of `o`, and `o` covers the gadget matching `r`, then some `P ∪ F_t` is one cycle.
* `exists_index_rTable8` : every fixed-point-free involution of `Fin 8` is in `rTable8`.
* `diskOK_spec` and `lineOK_spec` : Boolean certificates that a disk, or a segment of a line
  `θ ↦ θ (c, a)`, lies in a cell.
-/

namespace Pairing

namespace LowerBound

open PerfectMatching RoundRobin

variable {n : ℕ}

/-- Entry `i` of a list, reduced mod `8`. -/
def oN (o : List ℕ) (i : ℕ) : ℕ :=
  o.getD i 0 % 8

/-- A list read as a map `Fin 8 → Fin 8`. -/
def fin8 (o : List ℕ) (i : Fin 8) : Fin 8 :=
  ⟨oN o i, Nat.mod_lt _ (by norm_num)⟩

/-- `F_{s0}` swaps the two ends `j` and `j + 4` of each core edge. -/
def tau8 (j : Fin 8) : Fin 8 :=
  j + 4

/-- The eight ends `4, 5, 6, s0 + x, 3, 2, 1, s0 - x` of the 1-core `J_0 ∪ {e_x}`
(`results/struct-lb-extend.md` §1, organize-archive b5cb45e). -/
def pt8 (n : ℕ) (s0 x : ZMod n) : Fin 8 → ZMod n :=
  ![4, 5, 6, s0 + x, 3, 2, 1, s0 - x]

/-- `F_{s0}` maps end `j` to end `j + 4` (`results/struct-lb-extend.md` §1, organize-archive
b5cb45e). -/
theorem pt8_tau8 {s0 : ZMod n} (hs0 : 2 * s0 = 7) (x : ZMod n) (j : Fin 8) :
    pt8 n s0 x (tau8 j) = 2 * s0 - pt8 n s0 x j := by
  fin_cases j <;>
    simp only [pt8, tau8, Fin.zero_eta, Fin.isValue, zero_add, Matrix.cons_val,
      Matrix.cons_val_zero, Fin.mk_one, Fin.reduceAdd, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    first | ring1 | linear_combination -hs0

/-- The coefficient of `u` in slot `s`: the forms are `u, 3u, 5u, w`. -/
def slotA (s : ℕ) : ℤ :=
  if s = 0 then 1 else if s = 1 then 3 else if s = 2 then 5 else 0

/-- The coefficient of `w` in slot `s`. -/
def slotB (s : ℕ) : ℤ :=
  if s = 3 then 1 else 0

/-- The sign of end `j`: `+` for `j < 4`. -/
def sgn8 (j : ℕ) : ℤ :=
  if j < 4 then 1 else -1

/-- The value of end `j` at `(x, y)`, as the linear form `A x + B y + C`, with shifts `k`. -/
def ptForm (k : List ℤ) (j : ℕ) : ℤ × ℤ × ℤ :=
  (sgn8 j * slotA (j % 4), sgn8 j * slotB (j % 4), -(sgn8 j * k.getD (j % 4) 0))

/-- The `i`-th gap of the context `o`: the step from the `i`-th to the `(i + 1)`-th end for
`i < 7`, and the window `first + 1 - last` for `i = 7`. -/
def gapForm (o : List ℕ) (k : List ℤ) (i : ℕ) : ℤ × ℤ × ℤ :=
  if i < 7 then ptForm k (oN o (i + 1)) - ptForm k (oN o i)
  else ptForm k (oN o 0) - ptForm k (oN o 7) + (0, 0, 1)

/-- The value `A x + B y + C` of a linear form. -/
def evalF (f : ℤ × ℤ × ℤ) (x y : ℝ) : ℝ :=
  f.1 * x + f.2.1 * y + f.2.2

/-- `(x, y)` lies in the open cell of the context `o` with shifts `k`
(`results/struct-lb-extend.md` §1, Lemma 0, organize-archive b5cb45e). -/
def RealCell8 (o : List ℕ) (k : List ℤ) (x y : ℝ) : Prop :=
  ∀ i < 8, 0 < evalF (gapForm o k i) x y

/-- The integer position `n · (value of end j)` at the lift `(μ', a')/n`. -/
def posZ8 (n : ℕ) (k : List ℤ) (μ' a' : ℤ) (j : ℕ) : ℤ :=
  (ptForm k j).1 * μ' + (ptForm k j).2.1 * a' + n * (ptForm k j).2.2

/-- `evalF` of a difference. -/
theorem evalF_sub (f g : ℤ × ℤ × ℤ) (x y : ℝ) : evalF (f - g) x y = evalF f x y - evalF g x y := by
  simp only [evalF, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

/-- `evalF` of a form plus `1`. -/
theorem evalF_add_one (f : ℤ × ℤ × ℤ) (x y : ℝ) :
    evalF (f + (0, 0, 1)) x y = evalF f x y + 1 := by
  simp only [evalF, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_zero, Int.cast_one]
  ring

/-- `posZ8` is `n` times the value at `(μ'/n, a'/n)`. -/
theorem posZ8_eq (hn : 0 < n) (k : List ℤ) (μ' a' : ℤ) (j : ℕ) :
    (posZ8 n k μ' a' j : ℝ) = n * evalF (ptForm k j) (μ' / n) (a' / n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [posZ8, evalF]
  push_cast
  field_simp

/-- The cell condition at the lift `(μ', a')/n`, in integers. -/
theorem posZ8_lt_of_realCell8 (hn : 0 < n) {o : List ℕ} {k : List ℤ} {μ' a' : ℤ}
    (h : RealCell8 o k (μ' / n) (a' / n)) :
    (∀ i < 7, posZ8 n k μ' a' (oN o i) < posZ8 n k μ' a' (oN o (i + 1))) ∧
      posZ8 n k μ' a' (oN o 7) < posZ8 n k μ' a' (oN o 0) + n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro i hi
    have h1 := h i (by omega)
    simp only [gapForm, hi, ite_true, evalF_sub] at h1
    have h2 : (posZ8 n k μ' a' (oN o i) : ℝ) < posZ8 n k μ' a' (oN o (i + 1)) := by
      rw [posZ8_eq hn, posZ8_eq hn]
      nlinarith
    exact_mod_cast h2
  · have h1 := h 7 (by omega)
    simp only [gapForm, lt_irrefl, ite_false, evalF_add_one, evalF_sub] at h1
    have h2 : (posZ8 n k μ' a' (oN o 7) : ℝ) < posZ8 n k μ' a' (oN o 0) + n := by
      rw [posZ8_eq hn, posZ8_eq hn]
      nlinarith
    exact_mod_cast h2

/-- End `j` sits at `posZ8 ≡ 2 (pt8 j - s0) μ'` (`results/struct-lb-extend.md` §1, COD-186
Lemma 1, organize-archive b5cb45e). -/
theorem posZ8_cast {s0 x : ZMod n} (hs0 : 2 * s0 = 7) {X : ℤ} (hX : (X : ZMod n) = 2 * x)
    (k : List ℤ) {μ' a' : ℤ} (ha : (a' : ZMod n) = X * μ') (j : Fin 8) :
    ((posZ8 n k μ' a' j : ℤ) : ZMod n) = 2 * (pt8 n s0 x j - s0) * μ' := by
  fin_cases j <;>
    simp only [posZ8, ptForm, sgn8, Nat.ofNat_pos, ↓reduceIte, slotA, Nat.zero_mod, mul_one, slotB,
      OfNat.zero_ne_ofNat, mul_zero, List.getD_eq_getElem?_getD, one_mul, zero_mul, add_zero,
      mul_neg, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero,
      neg_zero, pt8, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Nat.one_lt_ofNat, Nat.one_mod,
      one_ne_zero, OfNat.one_ne_ofNat, Int.cast_ofNat, Fin.mk_one, Matrix.cons_val_one,
      Nat.reduceLT, Nat.reduceMod, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
      Fin.reduceFinMk, Matrix.cons_val, Nat.lt_add_one, Nat.mod_succ, Nat.succ_ne_self, zero_add,
      add_sub_cancel_left, lt_self_iff_false, Int.reduceNeg, Nat.mod_self, neg_mul, neg_neg,
      sub_sub_cancel_left, neg_inj] <;>
    first
    | linear_combination (μ' : ZMod n) * hs0
    | linear_combination ha + (μ' : ZMod n) * hX

/-- **The cell walk for a finite 1-core** (`results/struct-lb-extend.md` §3.3, Theorem B case 2,
organize-archive b5cb45e). Let `P̃ y = 2 s0 - y` off the eight ends and `P̃ (pt8 j) = pt8 (r j)`.
Let `a' ≡ X μ' (mod n)` with `X = 2x`, `n` prime. If `(μ'/n, a'/n)` lies in the cell of the
context `o`, `oi` inverts `o`, and `o` covers `r`, then some `P ∪ F_t` is one cycle. -/
theorem ham_of_realCell8 (hn : Odd n) (hp : n.Prime) {s0 x : ZMod n} (hs0 : 2 * s0 = 7)
    {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ y, (∀ j, y ≠ pt8 n s0 x j) → pinned P y = 2 * s0 - y)
    {r : Fin 8 → Fin 8} (hr : ∀ j, pinned P (pt8 n s0 x j) = pt8 n s0 x (r j))
    {X : ℤ} (hX : (X : ZMod n) = 2 * x) {o oi : List ℕ} (hoi : ∀ j, fin8 o (fin8 oi j) = j)
    {k : List ℤ} {μ' a' : ℤ} (ha : (n : ℤ) ∣ a' - X * μ')
    (hcell : RealCell8 o k (μ' / n) (a' / n)) (hcov : ArcCovers (fin8 o) (fin8 oi) tau8 r) :
    ∃ t, Ham P (factor hn t) := by
  have : NeZero n := ⟨hp.ne_zero⟩
  have : Fact n.Prime := ⟨hp⟩
  have ha' : (a' : ZMod n) = X * μ' := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr ha
    push_cast at this
    linear_combination this
  obtain ⟨hlt, hwin⟩ := posZ8_lt_of_realCell8 hp.pos hcell
  set z : Fin 8 → ℤ := fun j ↦ posZ8 n k μ' a' j with hzdef
  have hmono : StrictMono fun i ↦ z (fin8 o i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact hlt i i.2
  have hwin' : z (fin8 o (Fin.last 7)) < z (fin8 o 0) + n := hwin
  have hz : ∀ j, (z j : ZMod n) = 2 * (pt8 n s0 x j - s0) * (μ' : ZMod n) :=
    posZ8_cast hs0 hX k ha'
  have hμ : IsUnit (μ' : ZMod n) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hle : ∀ i, z (fin8 o 0) ≤ z (fin8 o i) ∧ z (fin8 o i) ≤ z (fin8 o (Fin.last 7)) :=
      fun i ↦ ⟨hmono.monotone (Fin.zero_le i), hmono.monotone (Fin.le_last i)⟩
    have h0' := hle (fin8 oi 0)
    have h4' := hle (fin8 oi 4)
    rw [hoi] at h0' h4'
    have hne : z 0 ≠ z 4 := by
      intro h
      have h' := hmono.injective (a₁ := fin8 oi 0) (a₂ := fin8 oi 4) (by rw [hoi, hoi]; exact h)
      have := congrArg (fin8 o) h'
      rw [hoi, hoi] at this
      exact absurd this (by decide)
    have hc0 := hz 0
    have hc4 := hz 4
    rw [h0, mul_zero] at hc0 hc4
    have hd : (n : ℤ) ∣ z 0 - z 4 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc0, hc4, sub_zero]
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  exact ham_of_positions hn (pt8 n s0 x) tau8 (pt8_tau8 hs0 x) hP r hr (fin8 o) (fin8 oi) hoi
    hμ z hz hmono hwin' hcov

/-- The 105 fixed-point-free involutions of `Fin 8`, the matchings `R` of the eight ends of a
finite 1-core (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
def rTable8 : List (List ℕ) :=
  [[1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 6, 7, 4, 5], [1, 0, 3, 2, 7, 6, 5, 4],
    [1, 0, 4, 5, 2, 3, 7, 6], [1, 0, 4, 6, 2, 7, 3, 5], [1, 0, 4, 7, 2, 6, 5, 3],
    [1, 0, 5, 4, 3, 2, 7, 6], [1, 0, 5, 6, 7, 2, 3, 4], [1, 0, 5, 7, 6, 2, 4, 3],
    [1, 0, 6, 4, 3, 7, 2, 5], [1, 0, 6, 5, 7, 3, 2, 4], [1, 0, 6, 7, 5, 4, 2, 3],
    [1, 0, 7, 4, 3, 6, 5, 2], [1, 0, 7, 5, 6, 3, 4, 2], [1, 0, 7, 6, 5, 4, 3, 2],
    [2, 3, 0, 1, 5, 4, 7, 6], [2, 3, 0, 1, 6, 7, 4, 5], [2, 3, 0, 1, 7, 6, 5, 4],
    [2, 4, 0, 5, 1, 3, 7, 6], [2, 4, 0, 6, 1, 7, 3, 5], [2, 4, 0, 7, 1, 6, 5, 3],
    [2, 5, 0, 4, 3, 1, 7, 6], [2, 5, 0, 6, 7, 1, 3, 4], [2, 5, 0, 7, 6, 1, 4, 3],
    [2, 6, 0, 4, 3, 7, 1, 5], [2, 6, 0, 5, 7, 3, 1, 4], [2, 6, 0, 7, 5, 4, 1, 3],
    [2, 7, 0, 4, 3, 6, 5, 1], [2, 7, 0, 5, 6, 3, 4, 1], [2, 7, 0, 6, 5, 4, 3, 1],
    [3, 2, 1, 0, 5, 4, 7, 6], [3, 2, 1, 0, 6, 7, 4, 5], [3, 2, 1, 0, 7, 6, 5, 4],
    [3, 4, 5, 0, 1, 2, 7, 6], [3, 4, 6, 0, 1, 7, 2, 5], [3, 4, 7, 0, 1, 6, 5, 2],
    [3, 5, 4, 0, 2, 1, 7, 6], [3, 5, 6, 0, 7, 1, 2, 4], [3, 5, 7, 0, 6, 1, 4, 2],
    [3, 6, 4, 0, 2, 7, 1, 5], [3, 6, 5, 0, 7, 2, 1, 4], [3, 6, 7, 0, 5, 4, 1, 2],
    [3, 7, 4, 0, 2, 6, 5, 1], [3, 7, 5, 0, 6, 2, 4, 1], [3, 7, 6, 0, 5, 4, 2, 1],
    [4, 2, 1, 5, 0, 3, 7, 6], [4, 2, 1, 6, 0, 7, 3, 5], [4, 2, 1, 7, 0, 6, 5, 3],
    [4, 3, 5, 1, 0, 2, 7, 6], [4, 3, 6, 1, 0, 7, 2, 5], [4, 3, 7, 1, 0, 6, 5, 2],
    [4, 5, 3, 2, 0, 1, 7, 6], [4, 5, 6, 7, 0, 1, 2, 3], [4, 5, 7, 6, 0, 1, 3, 2],
    [4, 6, 3, 2, 0, 7, 1, 5], [4, 6, 5, 7, 0, 2, 1, 3], [4, 6, 7, 5, 0, 3, 1, 2],
    [4, 7, 3, 2, 0, 6, 5, 1], [4, 7, 5, 6, 0, 2, 3, 1], [4, 7, 6, 5, 0, 3, 2, 1],
    [5, 2, 1, 4, 3, 0, 7, 6], [5, 2, 1, 6, 7, 0, 3, 4], [5, 2, 1, 7, 6, 0, 4, 3],
    [5, 3, 4, 1, 2, 0, 7, 6], [5, 3, 6, 1, 7, 0, 2, 4], [5, 3, 7, 1, 6, 0, 4, 2],
    [5, 4, 3, 2, 1, 0, 7, 6], [5, 4, 6, 7, 1, 0, 2, 3], [5, 4, 7, 6, 1, 0, 3, 2],
    [5, 6, 3, 2, 7, 0, 1, 4], [5, 6, 4, 7, 2, 0, 1, 3], [5, 6, 7, 4, 3, 0, 1, 2],
    [5, 7, 3, 2, 6, 0, 4, 1], [5, 7, 4, 6, 2, 0, 3, 1], [5, 7, 6, 4, 3, 0, 2, 1],
    [6, 2, 1, 4, 3, 7, 0, 5], [6, 2, 1, 5, 7, 3, 0, 4], [6, 2, 1, 7, 5, 4, 0, 3],
    [6, 3, 4, 1, 2, 7, 0, 5], [6, 3, 5, 1, 7, 2, 0, 4], [6, 3, 7, 1, 5, 4, 0, 2],
    [6, 4, 3, 2, 1, 7, 0, 5], [6, 4, 5, 7, 1, 2, 0, 3], [6, 4, 7, 5, 1, 3, 0, 2],
    [6, 5, 3, 2, 7, 1, 0, 4], [6, 5, 4, 7, 2, 1, 0, 3], [6, 5, 7, 4, 3, 1, 0, 2],
    [6, 7, 3, 2, 5, 4, 0, 1], [6, 7, 4, 5, 2, 3, 0, 1], [6, 7, 5, 4, 3, 2, 0, 1],
    [7, 2, 1, 4, 3, 6, 5, 0], [7, 2, 1, 5, 6, 3, 4, 0], [7, 2, 1, 6, 5, 4, 3, 0],
    [7, 3, 4, 1, 2, 6, 5, 0], [7, 3, 5, 1, 6, 2, 4, 0], [7, 3, 6, 1, 5, 4, 2, 0],
    [7, 4, 3, 2, 1, 6, 5, 0], [7, 4, 5, 6, 1, 2, 3, 0], [7, 4, 6, 5, 1, 3, 2, 0],
    [7, 5, 3, 2, 6, 1, 4, 0], [7, 5, 4, 6, 2, 1, 3, 0], [7, 5, 6, 4, 3, 1, 2, 0],
    [7, 6, 3, 2, 5, 4, 1, 0], [7, 6, 4, 5, 2, 3, 1, 0], [7, 6, 5, 4, 3, 2, 1, 0]]

set_option synthInstance.maxSize 1000000 in
/-- **The matchings of eight ends** (`results/struct-lb-extend.md` §3.2, organize-archive
b5cb45e). The hypotheses enumerate the involutions of `Fin 8` without fixed points:
`a_i ≠ i` and `a_i = j ↔ a_j = i`. -/
theorem mem_rTable8 : ∀ a0 : Fin 8, a0 ≠ 0 → ∀ a1 : Fin 8, a1 ≠ 1 → (a0 = 1 ↔ a1 = 0) →
    ∀ a2 : Fin 8, a2 ≠ 2 → (a0 = 2 ↔ a2 = 0) → (a1 = 2 ↔ a2 = 1) →
    ∀ a3 : Fin 8, a3 ≠ 3 → (a0 = 3 ↔ a3 = 0) → (a1 = 3 ↔ a3 = 1) → (a2 = 3 ↔ a3 = 2) →
    ∀ a4 : Fin 8, a4 ≠ 4 → (a0 = 4 ↔ a4 = 0) → (a1 = 4 ↔ a4 = 1) → (a2 = 4 ↔ a4 = 2) →
    (a3 = 4 ↔ a4 = 3) →
    ∀ a5 : Fin 8, a5 ≠ 5 → (a0 = 5 ↔ a5 = 0) → (a1 = 5 ↔ a5 = 1) → (a2 = 5 ↔ a5 = 2) →
    (a3 = 5 ↔ a5 = 3) → (a4 = 5 ↔ a5 = 4) →
    ∀ a6 : Fin 8, a6 ≠ 6 → (a0 = 6 ↔ a6 = 0) → (a1 = 6 ↔ a6 = 1) → (a2 = 6 ↔ a6 = 2) →
    (a3 = 6 ↔ a6 = 3) → (a4 = 6 ↔ a6 = 4) → (a5 = 6 ↔ a6 = 5) →
    ∀ a7 : Fin 8, a7 ≠ 7 → (a0 = 7 ↔ a7 = 0) → (a1 = 7 ↔ a7 = 1) → (a2 = 7 ↔ a7 = 2) →
    (a3 = 7 ↔ a7 = 3) → (a4 = 7 ↔ a7 = 4) → (a5 = 7 ↔ a7 = 5) → (a6 = 7 ↔ a7 = 6) →
    [(a0 : ℕ), a1, a2, a3, a4, a5, a6, a7] ∈ rTable8 := by
  decide +kernel

/-- Every fixed-point-free involution `r` of `Fin 8` is `fin8` of an entry of `rTable8`
(`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
theorem exists_index_rTable8 {r : Fin 8 → Fin 8} (h1 : ∀ j, r (r j) = j) (h2 : ∀ j, r j ≠ j) :
    ∃ i < 105, r = fin8 (rTable8.getD i []) := by
  have hi : ∀ i j, r i = j ↔ r j = i :=
    fun i j ↦ ⟨fun h ↦ by rw [← h, h1], fun h ↦ by rw [← h, h1]⟩
  have hm := mem_rTable8 _ (h2 0) _ (h2 1) (hi 0 1) _ (h2 2) (hi 0 2) (hi 1 2) _ (h2 3) (hi 0 3)
    (hi 1 3) (hi 2 3) _ (h2 4) (hi 0 4) (hi 1 4) (hi 2 4) (hi 3 4) _ (h2 5) (hi 0 5) (hi 1 5)
    (hi 2 5) (hi 3 5) (hi 4 5) _ (h2 6) (hi 0 6) (hi 1 6) (hi 2 6) (hi 3 6) (hi 4 6) (hi 5 6)
    _ (h2 7) (hi 0 7) (hi 1 7) (hi 2 7) (hi 3 7) (hi 4 7) (hi 5 7) (hi 6 7)
  obtain ⟨i, hi', hget⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by simpa [rTable8] using hi', ?_⟩
  rw [← List.getElem_eq_getD (h := hi'), hget]
  funext j
  apply Fin.ext
  fin_cases j <;> simp [fin8, oN, Nat.mod_eq_of_lt (r _).2]

/-- `m` is a correct cover mask for the context `(o, oi)`: `oi` inverts `o`, and bit `i` of `m`
is set only if `o` covers the `i`-th matching of `rTable8`. -/
def maskOK (o oi : List ℕ) (m : ℕ) : Bool :=
  allBelow (fun j ↦ oN o (oN oi j) == j) 8 &&
    allBelow (fun i ↦ !m.testBit i || coversB (fin8 o) (fin8 oi) tau8 (fin8 (rTable8.getD i [])))
      105

/-- A checked context `o` is inverted by `oi`. -/
theorem maskOK_inv {o oi : List ℕ} {m : ℕ} (h : maskOK o oi m = true) (j : Fin 8) :
    fin8 o (fin8 oi j) = j := by
  simp only [maskOK, Bool.and_eq_true] at h
  have := allBelow_spec h.1 j j.2
  simp only [beq_iff_eq] at this
  exact Fin.ext (by simpa [fin8, oN] using this)

/-- A set bit of a checked mask gives the arc condition for that matching. -/
theorem maskOK_covers {o oi : List ℕ} {m : ℕ} (h : maskOK o oi m = true) {i : ℕ} (hi : i < 105)
    (hb : m.testBit i = true) :
    ArcCovers (fin8 o) (fin8 oi) tau8 (fin8 (rTable8.getD i [])) := by
  simp only [maskOK, Bool.and_eq_true] at h
  have := allBelow_spec h.2 i hi
  simp only [hb, Bool.not_true, Bool.false_or] at this
  exact coversB_spec this

/-- A disk catches no hyperplane: a linear form positive at the centre, with
`ρ (A² + B²) ≤ value²`, stays positive on the open disk `|p - centre|² < ρ`
(`results/struct-lb-extend.md` §3.3, Theorem B case 2, organize-archive b5cb45e). -/
theorem pos_of_disk {A B C u w x y ρ : ℝ} (hL : 0 < A * u + B * w + C)
    (hm : ρ * (A ^ 2 + B ^ 2) ≤ (A * u + B * w + C) ^ 2) (hd : (x - u) ^ 2 + (y - w) ^ 2 < ρ) :
    0 < A * x + B * y + C := by
  set L := A * u + B * w + C
  set S := A * (x - u) + B * (y - w)
  have hxy : A * x + B * y + C = L + S := by simp only [L, S]; ring
  have hcs : S ^ 2 ≤ (A ^ 2 + B ^ 2) * ((x - u) ^ 2 + (y - w) ^ 2) := by
    simp only [S]
    nlinarith [sq_nonneg (A * (y - w) - B * (x - u))]
  rw [hxy]
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg A) (sq_nonneg B)) with h0 | h0
  · have hS : S ^ 2 ≤ 0 := by rw [← h0, zero_mul] at hcs; exact hcs
    have : S = 0 := by nlinarith [sq_nonneg S]
    rw [this, add_zero]
    exact hL
  · have h1 : S ^ 2 < L ^ 2 := by
      calc S ^ 2 ≤ (A ^ 2 + B ^ 2) * ((x - u) ^ 2 + (y - w) ^ 2) := hcs
        _ < (A ^ 2 + B ^ 2) * ρ := mul_lt_mul_of_pos_left hd h0
        _ = ρ * (A ^ 2 + B ^ 2) := mul_comm _ _
        _ ≤ L ^ 2 := hm
    nlinarith

/-- The certificate check for a disk: every gap form of `o` is positive at the centre
`(U/Q, W/Q)` with clearance `√(rn/rd)` (`results/struct-lb-extend.md` §3.2, table `𝒯_2`,
organize-archive b5cb45e). -/
def diskOK (o : List ℕ) (k : List ℤ) (U W Q rn rd : ℤ) : Bool :=
  allBelow (fun i ↦
    let f := gapForm o k i
    let F := f.1 * U + f.2.1 * W + f.2.2 * Q
    decide (0 < F) && decide (rn * (f.1 ^ 2 + f.2.1 ^ 2) * Q ^ 2 ≤ rd * F ^ 2)) 8

/-- **Soundness of `diskOK`** (`results/struct-lb-extend.md` §1, Lemma 0, organize-archive
b5cb45e): every point of the open disk lies in the cell of `o`. -/
theorem diskOK_spec {o : List ℕ} {k : List ℤ} {U W Q rn rd : ℤ}
    (h : diskOK o k U W Q rn rd = true) (hQ : 0 < Q) (hrd : 0 < rd) {x y : ℝ}
    (hd : (x - U / Q) ^ 2 + (y - W / Q) ^ 2 < (rn : ℝ) / rd) : RealCell8 o k x y := by
  intro i hi
  have h1 := allBelow_spec h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hF, hm⟩ := h1
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrdR : (0 : ℝ) < rd := by exact_mod_cast hrd
  set f := gapForm o k i
  have hval : (f.1 : ℝ) * (U / Q) + f.2.1 * (W / Q) + f.2.2 =
      ((f.1 * U + f.2.1 * W + f.2.2 * Q : ℤ) : ℝ) / Q := by
    push_cast
    field_simp
  refine pos_of_disk (u := U / Q) (w := W / Q) ?_ ?_ hd
  · rw [hval]
    exact div_pos (by exact_mod_cast hF) hQR
  · rw [hval, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ hrdR (by positivity)]
    have hm' : ((rn * (f.1 ^ 2 + f.2.1 ^ 2) * Q ^ 2 : ℤ) : ℝ) ≤
        ((rd * (f.1 * U + f.2.1 * W + f.2.2 * Q) ^ 2 : ℤ) : ℝ) := by exact_mod_cast hm
    push_cast at hm' ⊢
    linarith

/-- The certificate check for a segment `lo/den < θ < hi/den` of the line `θ ↦ θ (c, a)`: every
gap form of `o` is nonnegative at both ends and positive at one (`results/struct-lb-extend.md`
§3.2, the line table, organize-archive b5cb45e). -/
def lineWitOK (c a : ℤ) (o : List ℕ) (k : List ℤ) (lo hi den : ℤ) : Bool :=
  decide (0 < den) && decide (lo < hi) && allBelow (fun i ↦
    let f := gapForm o k i
    let s := f.1 * c + f.2.1 * a
    let fl := s * lo + f.2.2 * den
    let fh := s * hi + f.2.2 * den
    decide (0 ≤ fl) && decide (0 ≤ fh) && decide (0 < fl + fh)) 8

/-- **Soundness of `lineWitOK`** (`results/struct-lb-extend.md` §1, Lemma 0, organize-archive
b5cb45e): every point `θ (c, a)` of the open segment lies in the cell of `o`. -/
theorem lineWitOK_spec {c a : ℤ} {o : List ℕ} {k : List ℤ} {lo hi den : ℤ}
    (h : lineWitOK c a o k lo hi den = true) {θ : ℝ} (h1 : (lo : ℝ) / den < θ)
    (h2 : θ < (hi : ℝ) / den) : RealCell8 o k (c * θ) (a * θ) := by
  simp only [lineWitOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hden, -⟩, hall⟩ := h
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [div_lt_iff₀ hdR] at h1
  rw [lt_div_iff₀ hdR] at h2
  intro i hi'
  have h3 := allBelow_spec hall i hi'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  obtain ⟨⟨hl, hh⟩, hs⟩ := h3
  set f := gapForm o k i
  have hl' : (0 : ℝ) ≤ ((f.1 * c + f.2.1 * a) * lo + f.2.2 * den : ℤ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ ((f.1 * c + f.2.1 * a) * hi + f.2.2 * den : ℤ) := by exact_mod_cast hh
  have hs' : (0 : ℝ) < ((f.1 * c + f.2.1 * a) * lo + f.2.2 * den : ℤ) +
      ((f.1 * c + f.2.1 * a) * hi + f.2.2 * den : ℤ) := by exact_mod_cast hs
  push_cast at hl' hh' hs'
  set sl : ℝ := ((f.1 : ℝ) * c + f.2.1 * a)
  have hid : (sl * (θ * den) + f.2.2 * den) * ((hi : ℝ) - lo) =
      ((hi : ℝ) - θ * den) * (sl * lo + f.2.2 * den) +
        (θ * den - lo) * (sl * hi + f.2.2 * den) := by ring
  have hpos : 0 < (sl * (θ * den) + f.2.2 * den) * ((hi : ℝ) - lo) := by
    rw [hid]
    rcases lt_or_eq_of_le hl' with hl'' | hl''
    · have := mul_pos (sub_pos.mpr h2) hl''
      have := mul_nonneg (sub_nonneg.mpr h1.le) hh'
      linarith
    · have hh'' : 0 < sl * hi + f.2.2 * den := by linarith
      have := mul_pos (sub_pos.mpr h1) hh''
      have := mul_nonneg (sub_nonneg.mpr h2.le) hl'
      linarith
  have hhl : (0 : ℝ) < hi - lo := by linarith
  have hpos' : 0 < (sl * θ + f.2.2) * den := by
    have := (mul_pos_iff_of_pos_right hhl).mp hpos
    linarith
  have := (mul_pos_iff_of_pos_right hdR).mp hpos'
  simp only [evalF, sl] at this ⊢
  linarith

/-- The bitwise or of a list of masks. -/
def orAll : List ℕ → ℕ
  | [] => 0
  | m :: l => m ||| orAll l

/-- A bit of `orAll l` is a bit of some member of `l`. -/
theorem exists_mem_testBit_of_orAll : ∀ {l : List ℕ} {i : ℕ}, (orAll l).testBit i = true →
    ∃ m ∈ l, m.testBit i = true
  | [], i, h => by simp [orAll] at h
  | m :: l, i, h => by
    rw [orAll, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨m, List.mem_cons_self, h⟩
    · obtain ⟨m', hm', h'⟩ := exists_mem_testBit_of_orAll h
      exact ⟨m', List.mem_cons_of_mem _ hm', h'⟩

/-- A full mask `2^105 - 1` covers every fixed-point-free involution: some member of the list of
masks has the bit of `r` (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
theorem exists_mask_of_orAll {l : List ℕ} (h : orAll l = 2 ^ 105 - 1) {r : Fin 8 → Fin 8}
    (h1 : ∀ j, r (r j) = j) (h2 : ∀ j, r j ≠ j) :
    ∃ i < 105, r = fin8 (rTable8.getD i []) ∧ ∃ m ∈ l, m.testBit i = true := by
  obtain ⟨i, hi, rfl⟩ := exists_index_rTable8 h1 h2
  refine ⟨i, hi, rfl, exists_mem_testBit_of_orAll ?_⟩
  rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hi

end LowerBound

end Pairing
