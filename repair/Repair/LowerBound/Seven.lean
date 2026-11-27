import Repair.LowerBound.Eight

/-!
# The seven-point walk of the core `{e_∞}`

Source: `results/struct-lb-extend.md` §2 (the `k1` table for `(1, 3, 5, ∞)`) and §3.3,
Theorem B case 1, with `results/struct-lb-contra.md` §3.1, Lemma 2a (organize-archive b5cb45e).

The 1-core `J_0 ∪ {e_∞}` meets `ℤ/n` in seven points: the gadget points `4, 5, 6, 3, 2, 1` (point
`j < 6` has slot `j % 3`, label `1, 3, 5`, and sign `+` for `j < 3`) and the centre `s0`, point
`6`. The partner of `∞` in `P` is one of them, and `P̃` fixes it. So `P̃` restricts to an
involution `r` of `Fin 7` with exactly one fixed point. The centre sits at position `0`.

A context is a cyclic order `o` of the seven points. At `θ ∈ ℝ` with shifts `k`, point `j < 6` has
the value `± (λ θ - k)`, and `RealCell7 o k θ` says that these values and `0` increase strictly
along `o`, with the last below the first plus `1`. These are the cells of the 19 points of
`𝒜_0` on the circle.

* `ham_of_realCell7` : if `μ'/n` lies in the cell of `o`, and `o` covers `r`, then some
  `P ∪ F_t` is one cycle.
* `exists_cell7` : every such `r` is covered on a cell of length at least `1/24`.
-/

namespace Pairing

namespace LowerBound

open PerfectMatching RoundRobin

variable {n : ℕ}

/-- Entry `i` of a list, reduced mod `7`. -/
def oN7 (o : List ℕ) (i : ℕ) : ℕ :=
  o.getD i 0 % 7

/-- A list read as a map `Fin 7 → Fin 7`. -/
def fin7 (o : List ℕ) (i : Fin 7) : Fin 7 :=
  ⟨oN7 o i, Nat.mod_lt _ (by norm_num)⟩

/-- `F_{s0}` swaps `j` and `j + 3` for `j < 3` and fixes the centre. -/
def tau7 : Fin 7 → Fin 7 :=
  ![3, 4, 5, 0, 1, 2, 6]

/-- The seven points `4, 5, 6, 3, 2, 1, s0` of the 1-core `J_0 ∪ {e_∞}` in `ℤ/n`
(`results/struct-lb-extend.md` §1, organize-archive b5cb45e). -/
def pt7 (n : ℕ) (s0 : ZMod n) : Fin 7 → ZMod n :=
  ![4, 5, 6, 3, 2, 1, s0]

/-- `F_{s0}` maps point `j` to point `tau7 j` (`results/struct-lb-extend.md` §1,
organize-archive b5cb45e). -/
theorem pt7_tau7 {s0 : ZMod n} (hs0 : 2 * s0 = 7) (j : Fin 7) :
    pt7 n s0 (tau7 j) = 2 * s0 - pt7 n s0 j := by
  fin_cases j <;>
    simp only [pt7, tau7, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val,
      Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    first | ring1 | linear_combination -hs0

/-- The sign of point `j < 6`: `+` for `j < 3`. -/
def sgn7 (j : ℕ) : ℤ :=
  if j < 3 then 1 else -1

/-- The value of point `j` at `θ`, as the linear form `A θ + C`, with shifts `k`. The centre has
the value `0`. -/
def ptForm7 (k : List ℤ) (j : ℕ) : ℤ × ℤ :=
  if j < 6 then (sgn7 j * slotA (j % 3), -(sgn7 j * k.getD (j % 3) 0)) else (0, 0)

/-- The `i`-th gap of the context `o`, with the window `first + 1 - last` for `i = 6`. -/
def gapForm7 (o : List ℕ) (k : List ℤ) (i : ℕ) : ℤ × ℤ :=
  if i < 6 then ptForm7 k (oN7 o (i + 1)) - ptForm7 k (oN7 o i)
  else ptForm7 k (oN7 o 0) - ptForm7 k (oN7 o 6) + (0, 1)

/-- The value `A θ + C` of a linear form. -/
def evalF1 (f : ℤ × ℤ) (θ : ℝ) : ℝ :=
  f.1 * θ + f.2

/-- `θ` lies in the open cell of the context `o` with shifts `k`
(`results/struct-lb-extend.md` §1, Lemma 0, organize-archive b5cb45e). -/
def RealCell7 (o : List ℕ) (k : List ℤ) (θ : ℝ) : Prop :=
  ∀ i < 7, 0 < evalF1 (gapForm7 o k i) θ

/-- The integer position `n · (value of point j)` at `μ'/n`. -/
def posZ7 (n : ℕ) (k : List ℤ) (μ' : ℤ) (j : ℕ) : ℤ :=
  (ptForm7 k j).1 * μ' + n * (ptForm7 k j).2

/-- `evalF1` of a difference. -/
theorem evalF1_sub (f g : ℤ × ℤ) (θ : ℝ) : evalF1 (f - g) θ = evalF1 f θ - evalF1 g θ := by
  simp only [evalF1, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

/-- `evalF1` of a form plus `1`. -/
theorem evalF1_add_one (f : ℤ × ℤ) (θ : ℝ) : evalF1 (f + (0, 1)) θ = evalF1 f θ + 1 := by
  simp only [evalF1, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_zero, Int.cast_one]
  ring

/-- `posZ7` is `n` times the value at `μ'/n`. -/
theorem posZ7_eq (hn : 0 < n) (k : List ℤ) (μ' : ℤ) (j : ℕ) :
    (posZ7 n k μ' j : ℝ) = n * evalF1 (ptForm7 k j) (μ' / n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [posZ7, evalF1]
  push_cast
  field_simp

/-- The cell condition at `μ'/n`, in integers. -/
theorem posZ7_lt_of_realCell7 (hn : 0 < n) {o : List ℕ} {k : List ℤ} {μ' : ℤ}
    (h : RealCell7 o k (μ' / n)) :
    (∀ i < 6, posZ7 n k μ' (oN7 o i) < posZ7 n k μ' (oN7 o (i + 1))) ∧
      posZ7 n k μ' (oN7 o 6) < posZ7 n k μ' (oN7 o 0) + n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro i hi
    have h1 := h i (by omega)
    simp only [gapForm7, hi, ite_true, evalF1_sub] at h1
    have h2 : (posZ7 n k μ' (oN7 o i) : ℝ) < posZ7 n k μ' (oN7 o (i + 1)) := by
      rw [posZ7_eq hn, posZ7_eq hn]
      nlinarith
    exact_mod_cast h2
  · have h1 := h 6 (by omega)
    simp only [gapForm7, lt_irrefl, ite_false, evalF1_add_one, evalF1_sub] at h1
    have h2 : (posZ7 n k μ' (oN7 o 6) : ℝ) < posZ7 n k μ' (oN7 o 0) + n := by
      rw [posZ7_eq hn, posZ7_eq hn]
      nlinarith
    exact_mod_cast h2

/-- Point `j` sits at `posZ7 ≡ 2 (pt7 j - s0) μ'` (`results/struct-lb-extend.md` §1, COD-186
Lemma 1, organize-archive b5cb45e). -/
theorem posZ7_cast {s0 : ZMod n} (hs0 : 2 * s0 = 7) (k : List ℤ) (μ' : ℤ) (j : Fin 7) :
    ((posZ7 n k μ' j : ℤ) : ZMod n) = 2 * (pt7 n s0 j - s0) * μ' := by
  fin_cases j <;> simp [posZ7, ptForm7, sgn7, slotA, pt7] <;>
    linear_combination (μ' : ZMod n) * hs0

/-- **The cell walk for the core `{e_∞}`** (`results/struct-lb-extend.md` §3.3, Theorem B case 1,
organize-archive b5cb45e). Let `P̃ y = 2 s0 - y` off the seven points and
`P̃ (pt7 j) = pt7 (r j)`, `n` prime. If `μ'/n` lies in the cell of the context `o`, `oi` inverts
`o`, and `o` covers `r`, then some `P ∪ F_t` is one cycle. -/
theorem ham_of_realCell7 (hn : Odd n) (hp : n.Prime) {s0 : ZMod n} (hs0 : 2 * s0 = 7)
    {P : PerfectMatching (Option (ZMod n))}
    (hP : ∀ y, (∀ j, y ≠ pt7 n s0 j) → pinned P y = 2 * s0 - y)
    {r : Fin 7 → Fin 7} (hr : ∀ j, pinned P (pt7 n s0 j) = pt7 n s0 (r j))
    {o oi : List ℕ} (hoi : ∀ j, fin7 o (fin7 oi j) = j) {k : List ℤ} {μ' : ℤ}
    (hcell : RealCell7 o k (μ' / n)) (hcov : ArcCovers (fin7 o) (fin7 oi) tau7 r) :
    ∃ t, Ham P (factor hn t) := by
  have : NeZero n := ⟨hp.ne_zero⟩
  have : Fact n.Prime := ⟨hp⟩
  obtain ⟨hlt, hwin⟩ := posZ7_lt_of_realCell7 hp.pos hcell
  set z : Fin 7 → ℤ := fun j ↦ posZ7 n k μ' j with hzdef
  have hmono : StrictMono fun i ↦ z (fin7 o i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact hlt i i.2
  have hwin' : z (fin7 o (Fin.last 6)) < z (fin7 o 0) + n := hwin
  have hz : ∀ j, (z j : ZMod n) = 2 * (pt7 n s0 j - s0) * (μ' : ZMod n) :=
    posZ7_cast hs0 k μ'
  have hμ : IsUnit (μ' : ZMod n) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hle : ∀ i, z (fin7 o 0) ≤ z (fin7 o i) ∧ z (fin7 o i) ≤ z (fin7 o (Fin.last 6)) :=
      fun i ↦ ⟨hmono.monotone (Fin.zero_le i), hmono.monotone (Fin.le_last i)⟩
    have h0' := hle (fin7 oi 0)
    have h3' := hle (fin7 oi 3)
    rw [hoi] at h0' h3'
    have hne : z 0 ≠ z 3 := by
      intro h
      have h' := hmono.injective (a₁ := fin7 oi 0) (a₂ := fin7 oi 3) (by rw [hoi, hoi]; exact h)
      have := congrArg (fin7 o) h'
      rw [hoi, hoi] at this
      exact absurd this (by decide)
    have hc0 := hz 0
    have hc3 := hz 3
    rw [h0, mul_zero] at hc0 hc3
    have hd : (n : ℤ) ∣ z 0 - z 3 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc0, hc3, sub_zero]
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  exact ham_of_positions hn (pt7 n s0) tau7 (pt7_tau7 hs0) hP r hr (fin7 o) (fin7 oi) hoi
    hμ z hz hmono hwin' hcov

/-- The 105 involutions of `Fin 7` with exactly one fixed point, the matchings of the eight ends
of `J_0 ∪ {e_∞}` read through `P̃` (`results/struct-lb-extend.md` §2, organize-archive
b5cb45e). -/
def rTable7 : List (List ℕ) :=
  [[0, 2, 1, 4, 3, 6, 5], [0, 2, 1, 5, 6, 3, 4], [0, 2, 1, 6, 5, 4, 3],
    [0, 3, 4, 1, 2, 6, 5], [0, 3, 5, 1, 6, 2, 4], [0, 3, 6, 1, 5, 4, 2],
    [0, 4, 3, 2, 1, 6, 5], [0, 4, 5, 6, 1, 2, 3], [0, 4, 6, 5, 1, 3, 2],
    [0, 5, 3, 2, 6, 1, 4], [0, 5, 4, 6, 2, 1, 3], [0, 5, 6, 4, 3, 1, 2],
    [0, 6, 3, 2, 5, 4, 1], [0, 6, 4, 5, 2, 3, 1], [0, 6, 5, 4, 3, 2, 1],
    [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 5, 6, 3, 4], [1, 0, 2, 6, 5, 4, 3],
    [1, 0, 3, 2, 4, 6, 5], [1, 0, 3, 2, 5, 4, 6], [1, 0, 3, 2, 6, 5, 4],
    [1, 0, 4, 3, 2, 6, 5], [1, 0, 4, 5, 2, 3, 6], [1, 0, 4, 6, 2, 5, 3],
    [1, 0, 5, 3, 6, 2, 4], [1, 0, 5, 4, 3, 2, 6], [1, 0, 5, 6, 4, 2, 3],
    [1, 0, 6, 3, 5, 4, 2], [1, 0, 6, 4, 3, 5, 2], [1, 0, 6, 5, 4, 3, 2],
    [2, 1, 0, 4, 3, 6, 5], [2, 1, 0, 5, 6, 3, 4], [2, 1, 0, 6, 5, 4, 3],
    [2, 3, 0, 1, 4, 6, 5], [2, 3, 0, 1, 5, 4, 6], [2, 3, 0, 1, 6, 5, 4],
    [2, 4, 0, 3, 1, 6, 5], [2, 4, 0, 5, 1, 3, 6], [2, 4, 0, 6, 1, 5, 3],
    [2, 5, 0, 3, 6, 1, 4], [2, 5, 0, 4, 3, 1, 6], [2, 5, 0, 6, 4, 1, 3],
    [2, 6, 0, 3, 5, 4, 1], [2, 6, 0, 4, 3, 5, 1], [2, 6, 0, 5, 4, 3, 1],
    [3, 1, 4, 0, 2, 6, 5], [3, 1, 5, 0, 6, 2, 4], [3, 1, 6, 0, 5, 4, 2],
    [3, 2, 1, 0, 4, 6, 5], [3, 2, 1, 0, 5, 4, 6], [3, 2, 1, 0, 6, 5, 4],
    [3, 4, 2, 0, 1, 6, 5], [3, 4, 5, 0, 1, 2, 6], [3, 4, 6, 0, 1, 5, 2],
    [3, 5, 2, 0, 6, 1, 4], [3, 5, 4, 0, 2, 1, 6], [3, 5, 6, 0, 4, 1, 2],
    [3, 6, 2, 0, 5, 4, 1], [3, 6, 4, 0, 2, 5, 1], [3, 6, 5, 0, 4, 2, 1],
    [4, 1, 3, 2, 0, 6, 5], [4, 1, 5, 6, 0, 2, 3], [4, 1, 6, 5, 0, 3, 2],
    [4, 2, 1, 3, 0, 6, 5], [4, 2, 1, 5, 0, 3, 6], [4, 2, 1, 6, 0, 5, 3],
    [4, 3, 2, 1, 0, 6, 5], [4, 3, 5, 1, 0, 2, 6], [4, 3, 6, 1, 0, 5, 2],
    [4, 5, 2, 6, 0, 1, 3], [4, 5, 3, 2, 0, 1, 6], [4, 5, 6, 3, 0, 1, 2],
    [4, 6, 2, 5, 0, 3, 1], [4, 6, 3, 2, 0, 5, 1], [4, 6, 5, 3, 0, 2, 1],
    [5, 1, 3, 2, 6, 0, 4], [5, 1, 4, 6, 2, 0, 3], [5, 1, 6, 4, 3, 0, 2],
    [5, 2, 1, 3, 6, 0, 4], [5, 2, 1, 4, 3, 0, 6], [5, 2, 1, 6, 4, 0, 3],
    [5, 3, 2, 1, 6, 0, 4], [5, 3, 4, 1, 2, 0, 6], [5, 3, 6, 1, 4, 0, 2],
    [5, 4, 2, 6, 1, 0, 3], [5, 4, 3, 2, 1, 0, 6], [5, 4, 6, 3, 1, 0, 2],
    [5, 6, 2, 4, 3, 0, 1], [5, 6, 3, 2, 4, 0, 1], [5, 6, 4, 3, 2, 0, 1],
    [6, 1, 3, 2, 5, 4, 0], [6, 1, 4, 5, 2, 3, 0], [6, 1, 5, 4, 3, 2, 0],
    [6, 2, 1, 3, 5, 4, 0], [6, 2, 1, 4, 3, 5, 0], [6, 2, 1, 5, 4, 3, 0],
    [6, 3, 2, 1, 5, 4, 0], [6, 3, 4, 1, 2, 5, 0], [6, 3, 5, 1, 4, 2, 0],
    [6, 4, 2, 5, 1, 3, 0], [6, 4, 3, 2, 1, 5, 0], [6, 4, 5, 3, 1, 2, 0],
    [6, 5, 2, 4, 3, 1, 0], [6, 5, 3, 2, 4, 1, 0], [6, 5, 4, 3, 2, 1, 0]]

set_option synthInstance.maxSize 1000000 in
/-- **The involutions of `Fin 7` with one fixed point** (`results/struct-lb-extend.md` §2,
organize-archive b5cb45e). The hypotheses enumerate the involutions with at most one fixed
point: `a_i = j ↔ a_j = i`, and `a_i = i → a_j ≠ j` for `i < j`. -/
theorem mem_rTable7 : ∀ a0 : Fin 7,
    ∀ a1 : Fin 7, (a0 = 1 ↔ a1 = 0) → (a0 = 0 → a1 ≠ 1) →
    ∀ a2 : Fin 7, (a0 = 2 ↔ a2 = 0) → (a1 = 2 ↔ a2 = 1) → (a0 = 0 → a2 ≠ 2) →
    (a1 = 1 → a2 ≠ 2) →
    ∀ a3 : Fin 7, (a0 = 3 ↔ a3 = 0) → (a1 = 3 ↔ a3 = 1) → (a2 = 3 ↔ a3 = 2) →
    (a0 = 0 → a3 ≠ 3) → (a1 = 1 → a3 ≠ 3) → (a2 = 2 → a3 ≠ 3) →
    ∀ a4 : Fin 7, (a0 = 4 ↔ a4 = 0) → (a1 = 4 ↔ a4 = 1) → (a2 = 4 ↔ a4 = 2) →
    (a3 = 4 ↔ a4 = 3) → (a0 = 0 → a4 ≠ 4) → (a1 = 1 → a4 ≠ 4) → (a2 = 2 → a4 ≠ 4) →
    (a3 = 3 → a4 ≠ 4) →
    ∀ a5 : Fin 7, (a0 = 5 ↔ a5 = 0) → (a1 = 5 ↔ a5 = 1) → (a2 = 5 ↔ a5 = 2) →
    (a3 = 5 ↔ a5 = 3) → (a4 = 5 ↔ a5 = 4) → (a0 = 0 → a5 ≠ 5) → (a1 = 1 → a5 ≠ 5) →
    (a2 = 2 → a5 ≠ 5) → (a3 = 3 → a5 ≠ 5) → (a4 = 4 → a5 ≠ 5) →
    ∀ a6 : Fin 7, (a0 = 6 ↔ a6 = 0) → (a1 = 6 ↔ a6 = 1) → (a2 = 6 ↔ a6 = 2) →
    (a3 = 6 ↔ a6 = 3) → (a4 = 6 ↔ a6 = 4) → (a5 = 6 ↔ a6 = 5) → (a0 = 0 → a6 ≠ 6) →
    (a1 = 1 → a6 ≠ 6) → (a2 = 2 → a6 ≠ 6) → (a3 = 3 → a6 ≠ 6) → (a4 = 4 → a6 ≠ 6) →
    (a5 = 5 → a6 ≠ 6) →
    [(a0 : ℕ), a1, a2, a3, a4, a5, a6] ∈ rTable7 := by
  decide +kernel

/-- Every involution `r` of `Fin 7` with at most one fixed point is `fin7` of an entry of
`rTable7` (`results/struct-lb-extend.md` §2, organize-archive b5cb45e). -/
theorem exists_index_rTable7 {r : Fin 7 → Fin 7} (h1 : ∀ j, r (r j) = j)
    (h2 : ∀ i j, r i = i → r j = j → i = j) : ∃ i < 105, r = fin7 (rTable7.getD i []) := by
  have hi : ∀ i j, r i = j ↔ r j = i :=
    fun i j ↦ ⟨fun h ↦ by rw [← h, h1], fun h ↦ by rw [← h, h1]⟩
  have hf : ∀ i j, i ≠ j → r i = i → r j ≠ j := fun i j hij h h' ↦ hij (h2 i j h h')
  have hm := mem_rTable7 _ _ (hi 0 1) (hf 0 1 (by decide)) _ (hi 0 2) (hi 1 2)
    (hf 0 2 (by decide)) (hf 1 2 (by decide)) _ (hi 0 3) (hi 1 3) (hi 2 3) (hf 0 3 (by decide))
    (hf 1 3 (by decide)) (hf 2 3 (by decide)) _ (hi 0 4) (hi 1 4) (hi 2 4) (hi 3 4)
    (hf 0 4 (by decide)) (hf 1 4 (by decide)) (hf 2 4 (by decide)) (hf 3 4 (by decide)) _
    (hi 0 5) (hi 1 5) (hi 2 5) (hi 3 5) (hi 4 5) (hf 0 5 (by decide)) (hf 1 5 (by decide))
    (hf 2 5 (by decide)) (hf 3 5 (by decide)) (hf 4 5 (by decide)) _ (hi 0 6) (hi 1 6) (hi 2 6)
    (hi 3 6) (hi 4 6) (hi 5 6) (hf 0 6 (by decide)) (hf 1 6 (by decide)) (hf 2 6 (by decide))
    (hf 3 6 (by decide)) (hf 4 6 (by decide)) (hf 5 6 (by decide))
  obtain ⟨i, hi', hget⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by simpa [rTable7] using hi', ?_⟩
  rw [← List.getElem_eq_getD (h := hi'), hget]
  funext j
  apply Fin.ext
  fin_cases j <;> simp [fin7, oN7, Nat.mod_eq_of_lt (r _).2]

/-- `m` is a correct cover mask for the context `(o, oi)` of the seven points. -/
def maskOK7 (o oi : List ℕ) (m : ℕ) : Bool :=
  allBelow (fun j ↦ oN7 o (oN7 oi j) == j) 7 &&
    allBelow (fun i ↦ !m.testBit i || coversB (fin7 o) (fin7 oi) tau7 (fin7 (rTable7.getD i [])))
      105

/-- The certificate check for a segment `lo/den < θ < hi/den` of the circle. -/
def cellWitOK7 (o : List ℕ) (k : List ℤ) (lo hi den : ℤ) : Bool :=
  decide (0 < den) && decide (lo < hi) && allBelow (fun i ↦
    let f := gapForm7 o k i
    let fl := f.1 * lo + f.2 * den
    let fh := f.1 * hi + f.2 * den
    decide (0 ≤ fl) && decide (0 ≤ fh) && decide (0 < fl + fh)) 7

/-- **Soundness of `cellWitOK7`** (`results/struct-lb-extend.md` §1, Lemma 0, organize-archive
b5cb45e): every point of the open segment lies in the cell of `o`. -/
theorem cellWitOK7_spec {o : List ℕ} {k : List ℤ} {lo hi den : ℤ}
    (h : cellWitOK7 o k lo hi den = true) {θ : ℝ} (h1 : (lo : ℝ) / den < θ)
    (h2 : θ < (hi : ℝ) / den) : RealCell7 o k θ := by
  simp only [cellWitOK7, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hden, -⟩, hall⟩ := h
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [div_lt_iff₀ hdR] at h1
  rw [lt_div_iff₀ hdR] at h2
  intro i hi'
  have h3 := allBelow_spec hall i hi'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  obtain ⟨⟨hl, hh⟩, hs⟩ := h3
  set f := gapForm7 o k i
  have hl' : (0 : ℝ) ≤ (f.1 * lo + f.2 * den : ℤ) := by exact_mod_cast hl
  have hh' : (0 : ℝ) ≤ (f.1 * hi + f.2 * den : ℤ) := by exact_mod_cast hh
  have hs' : (0 : ℝ) < (f.1 * lo + f.2 * den : ℤ) + (f.1 * hi + f.2 * den : ℤ) := by
    exact_mod_cast hs
  push_cast at hl' hh' hs'
  have hid : ((f.1 : ℝ) * (θ * den) + f.2 * den) * ((hi : ℝ) - lo) =
      ((hi : ℝ) - θ * den) * (f.1 * lo + f.2 * den) +
        (θ * den - lo) * (f.1 * hi + f.2 * den) := by ring
  have hpos : 0 < ((f.1 : ℝ) * (θ * den) + f.2 * den) * ((hi : ℝ) - lo) := by
    rw [hid]
    rcases lt_or_eq_of_le hl' with hl'' | hl''
    · have := mul_pos (sub_pos.mpr h2) hl''
      have := mul_nonneg (sub_nonneg.mpr h1.le) hh'
      linarith
    · have hh'' : 0 < (f.1 : ℝ) * hi + f.2 * den := by linarith
      have := mul_pos (sub_pos.mpr h1) hh''
      have := mul_nonneg (sub_nonneg.mpr h2.le) hl'
      linarith
  have hhl : (0 : ℝ) < hi - lo := by linarith
  have hpos' : 0 < ((f.1 : ℝ) * θ + f.2) * den := by
    have := (mul_pos_iff_of_pos_right hhl).mp hpos
    linarith
  have := (mul_pos_iff_of_pos_right hdR).mp hpos'
  simp only [evalF1] at this ⊢
  linarith

/-- A cell of the circle: the context `o`, its inverse `oi`, its cover mask `m`, the shifts `k`
and the segment `lo/den < θ < hi/den`. -/
structure Cell7 where
  o : List ℕ
  oi : List ℕ
  m : ℕ
  k : List ℤ
  lo : ℤ
  hi : ℤ
  den : ℤ

/-- Six cells of the 20 cells of `(1, 3, 5, ∞)` on the circle, each of length at least `1/24`,
whose contexts cover all 105 matchings (`scripts/struct-lb-e-k1.out`, organize-archive
b5cb45e). -/
def cellT7 : List Cell7 :=
  [⟨[5, 4, 3, 6, 0, 1, 2], [4, 5, 6, 2, 1, 0, 3], 562667046181655482236525446,
      [0, 0, 0], 0, 1, 10⟩,
    ⟨[3, 4, 5, 6, 2, 1, 0], [6, 5, 4, 0, 1, 2, 3], 2363700942791406583174305001694,
      [0, 1, 2], 4, 5, 10⟩,
    ⟨[0, 1, 2, 6, 5, 4, 3], [0, 1, 2, 6, 5, 4, 3], 18437203678648460838545615683584,
      [1, 2, 3], 5, 6, 10⟩,
    ⟨[5, 3, 1, 6, 4, 0, 2], [5, 2, 6, 1, 4, 0, 3], 25806984809239987786016071115181,
      [0, 1, 1], 5, 6, 20⟩,
    ⟨[4, 2, 3, 6, 0, 5, 1], [4, 6, 1, 2, 0, 5, 3], 897243511385077347558022376,
      [0, 0, 1], 3, 4, 24⟩,
    ⟨[2, 1, 0, 6, 3, 4, 5], [2, 1, 0, 4, 5, 6, 3], 4332496255188748254116045934963,
      [1, 3, 5], 9, 10, 10⟩]

/-- The check of one cell, with length at least `1/24`. -/
def cellOK7 (e : Cell7) : Bool :=
  maskOK7 e.o e.oi e.m && cellWitOK7 e.o e.k e.lo e.hi e.den && decide (e.den ≤ (e.hi - e.lo) * 24)

/-- Every cell of `cellT7` checks (`results/struct-lb-extend.md` §2, organize-archive b5cb45e). -/
theorem cellT7_ok : cellT7.all cellOK7 = true := by
  decide +kernel

/-- The six cells cover all 105 matchings (`results/struct-lb-extend.md` §2, organize-archive
b5cb45e). -/
theorem cellT7_full : orAll (cellT7.map Cell7.m) = 2 ^ 105 - 1 := by
  decide +kernel

/-- **The cells of `(1, 3, 5, ∞)`** (`results/struct-lb-extend.md` §2 and Theorem B case 1,
organize-archive b5cb45e). Every involution `r` of `Fin 7` with at most one fixed point is covered
by the context of a segment of length at least `1/24` that lies in its cell. -/
theorem exists_cell7 {r : Fin 7 → Fin 7} (h1 : ∀ j, r (r j) = j)
    (h2 : ∀ i j, r i = i → r j = j → i = j) :
    ∃ (o oi : List ℕ) (k : List ℤ) (lo hi den : ℤ), (∀ j, fin7 o (fin7 oi j) = j) ∧
      ArcCovers (fin7 o) (fin7 oi) tau7 r ∧ cellWitOK7 o k lo hi den = true ∧
      den ≤ (hi - lo) * 24 := by
  obtain ⟨i, hi, rfl⟩ := exists_index_rTable7 h1 h2
  have hb : (orAll (cellT7.map Cell7.m)).testBit i = true := by
    rw [cellT7_full, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hi
  obtain ⟨m, hm, hb'⟩ := exists_mem_testBit_of_orAll hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have hok := List.all_eq_true.mp cellT7_ok e he
  simp only [cellOK7, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hmask, hcell⟩, hlen⟩ := hok
  simp only [maskOK7, Bool.and_eq_true] at hmask
  refine ⟨e.o, e.oi, e.k, e.lo, e.hi, e.den, fun j ↦ ?_, ?_, hcell, hlen⟩
  · have := allBelow_spec hmask.1 j j.2
    simp only [beq_iff_eq] at this
    exact Fin.ext (by simpa [fin7, oN7] using this)
  · have := allBelow_spec hmask.2 i hi
    simp only [hb', Bool.not_true, Bool.false_or] at this
    exact coversB_spec this

end LowerBound

end Pairing
