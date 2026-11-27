import Repair.LowerBound.Eight

/-!
# Checking a table of short lines

Source: `results/struct-lb-extend.md` §3.2, the line table, and §3.3, Theorem B case 2, with
`results/struct-lb-factcheck-extend.md` §3, claim 6 (organize-archive b5cb45e).

When the lattice `Λ_X` has a short primitive vector `(c, a)`, the samples of a finite 1-core are
the points `ν (c, a)/n` of the line `θ ↦ θ (c, a)`. A line is *good* with constant `L` if every
matching `R` of the eight ends is covered by the context of some segment of the line of length at
least `1/L`, given as a witness.

A witness names a context by its index in a table `T` of contexts with cover masks, the shifts
`k`, and the segment `lo/den < θ < hi/den`. `lineOK` checks the witnesses of one line and that
their masks cover all 105 matchings. `rowOK` checks every admissible line `(c, a)` with a fixed
`c`, `|a| ≤ B` and `c² + a² ≤ H`, in a row indexed by `a + B`.

* `rowOK_spec` : a checked row makes each of its lines good.
-/

namespace Pairing

namespace LowerBound

/-- A context with its inverse and cover mask (`results/struct-lb-extend.md` §3.2,
organize-archive b5cb45e). -/
structure Ctx8 where
  o : List ℕ
  oi : List ℕ
  m : ℕ

/-- A witness segment `lo/den < θ < hi/den` with the context `ctx` of a table and shifts `k`
(`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
structure LineWit where
  ctx : ℕ
  k : List ℤ
  lo : ℤ
  hi : ℤ
  den : ℤ

/-- The identity context with the empty mask, the default of a table lookup. -/
def ctxId8 : Ctx8 :=
  ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], 0⟩

/-- Entry `i` of a context table, or `ctxId8`. -/
def ctxOf (T : List Ctx8) (i : ℕ) : Ctx8 :=
  T.getD i ctxId8

/-- Every entry of the context table has a correct mask. -/
abbrev TableOK (T : List Ctx8) : Prop :=
  T.all (fun e ↦ maskOK e.o e.oi e.m) = true

/-- Every lookup in a checked context table has a correct mask. -/
theorem maskOK_ctxOf {T : List Ctx8} (hT : TableOK T) (i : ℕ) :
    maskOK (ctxOf T i).o (ctxOf T i).oi (ctxOf T i).m = true := by
  rw [ctxOf, List.getD_eq_getElem?_getD]
  rcases h : T[i]? with _ | e
  · decide
  · exact List.all_eq_true.mp hT e (List.mem_of_getElem? h)

/-- One witness of the line `(c, a)`: the segment lies in the cell of its context and has length
at least `1/L`. -/
def witOK (T : List Ctx8) (c a L : ℤ) (w : LineWit) : Bool :=
  lineWitOK c a (ctxOf T w.ctx).o w.k w.lo w.hi w.den && decide (w.den ≤ (w.hi - w.lo) * L)

/-- The line `(c, a)` with witnesses `ws`: every witness checks and the masks cover all 105
matchings. -/
def lineOK (T : List Ctx8) (c a L : ℤ) (ws : List LineWit) : Bool :=
  ws.all (witOK T c a L) && orAll (ws.map fun w ↦ (ctxOf T w.ctx).m) == 2 ^ 105 - 1

/-- `(c, a)` is an admissible direction: `c ≥ 1`, `gcd(c, a) = 1`, `a ≠ 0` and
`|a| ∉ {c, 3c, 5c}` (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
def admB (c a : ℤ) : Bool :=
  decide (1 ≤ c) && decide (a ≠ 0) && decide (Int.gcd c a = 1) && decide (a ≠ c) &&
    decide (a ≠ -c) && decide (a ≠ 3 * c) && decide (a ≠ -(3 * c)) && decide (a ≠ 5 * c) &&
    decide (a ≠ -(5 * c))

/-- The row `c` of a line table: every admissible `(c, a)` with `|a| ≤ B` and `c² + a² ≤ H`
has witnesses at index `a + B` that check. -/
def rowOK (T : List Ctx8) (H L : ℤ) (B c : ℕ) (row : List (List LineWit)) : Bool :=
  allBelow (fun j ↦
    !(admB c ((j : ℤ) - B) && decide ((c : ℤ) ^ 2 + ((j : ℤ) - B) ^ 2 ≤ H)) ||
      lineOK T c ((j : ℤ) - B) L (row.getD j [])) (2 * B + 1)

/-- The line `(c, a)` is good with constant `L` (`results/struct-lb-extend.md` §3.2,
organize-archive b5cb45e): every matching `r` of the eight ends is covered by the context of a
segment `lo/den < θ < hi/den` of length at least `1/L` that lies in the cell of that context. -/
def LineGood (c a L : ℤ) : Prop :=
  ∀ r : Fin 8 → Fin 8, (∀ j, r (r j) = j) → (∀ j, r j ≠ j) →
    ∃ (o oi : List ℕ) (k : List ℤ) (lo hi den : ℤ), (∀ j, fin8 o (fin8 oi j) = j) ∧
      ArcCovers (fin8 o) (fin8 oi) tau8 r ∧ lineWitOK c a o k lo hi den = true ∧
      den ≤ (hi - lo) * L

/-- **Soundness of `lineOK`** (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
theorem lineOK_spec {T : List Ctx8} (hT : TableOK T) {c a L : ℤ} {ws : List LineWit}
    (h : lineOK T c a L ws = true) : LineGood c a L := by
  intro r h1 h2
  simp only [lineOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hall, hor⟩ := h
  obtain ⟨i, hi, rfl, m, hm, hb⟩ := exists_mask_of_orAll hor h1 h2
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  have hwok := List.all_eq_true.mp hall w hw
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq] at hwok
  have hmask := maskOK_ctxOf hT w.ctx
  exact ⟨_, _, w.k, w.lo, w.hi, w.den, maskOK_inv hmask, maskOK_covers hmask hi hb, hwok.1,
    hwok.2⟩

/-- **Soundness of `rowOK`** (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). A
checked row makes every admissible line `(c, a)` with `|a| ≤ B` and `c² + a² ≤ H` good. -/
theorem rowOK_spec {T : List Ctx8} (hT : TableOK T) {H L : ℤ} {B c : ℕ}
    {row : List (List LineWit)} (h : rowOK T H L B c row = true) {a : ℤ}
    (hadm : admB c a = true) (hH : (c : ℤ) ^ 2 + a ^ 2 ≤ H) (ha : |a| ≤ B) :
    LineGood c a L := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have h1 := allBelow_spec h (a + B).toNat (by omega)
  have hj : (((a + B).toNat : ℕ) : ℤ) - B = a := by omega
  rw [hj, hadm, Bool.true_and, decide_eq_true hH, Bool.not_true, Bool.false_or] at h1
  exact lineOK_spec hT h1

end LowerBound

end Pairing
