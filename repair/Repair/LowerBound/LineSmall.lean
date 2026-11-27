import Repair.LowerBound.KTwo

/-!
# Short lines at a fixed small prime

Source: `results/struct-lb-extend.md` §3.2, the line table, and §3.3, Theorem B case 3, with
`results/struct-lb-factcheck-extend.md` §3 (organize-archive b5cb45e).

Below `n = 1177` a shortest vector `(c, a)` of `Λ_X` still has `3 L⁴ ≤ 4 n²`, so `L² ≤ 1358`, and
the samples are the points `ν (c, a)/n`. The long line table gives each such line segments of
length at least `1/L_line`, with a bound `L_line` of its own. For `n > L_line` a segment holds a
point `ν/n`. For the finitely many primes `n ≤ L_line` a table names the points `ν` directly.

* `LineGoodAt c a n` : every matching of the eight ends is covered by the context of some
  sample `ν (c, a)/n`.
* `lineGoodAt_of_lineGood` : a line good with constant `L < n` is good at `n`.
* `ptsOK_spec` : a checked list of points `ν` makes a line good at `n`.
* `walkOK_spec` : a checked walk over `n₀ ≤ n < n₀ + f` names points at every `n` that needs
  them.
* `lineGoodAt_of_smallOK` : the check of one line of the small table.
-/

namespace Pairing

namespace LowerBound

variable {n : ℕ}

/-- The line `(c, a)` is good at `n` (`results/struct-lb-extend.md` §3.3, Theorem B case 3,
organize-archive b5cb45e): every matching `r` of the eight ends is covered by the context of a
sample `ν (c, a)/n` that lies in the cell of that context. -/
def LineGoodAt (c a : ℤ) (n : ℕ) : Prop :=
  ∀ r : Fin 8 → Fin 8, (∀ j, r (r j) = j) → (∀ j, r j ≠ j) →
    ∃ (o oi : List ℕ) (k : List ℤ) (ν : ℤ), (∀ j, fin8 o (fin8 oi j) = j) ∧
      ArcCovers (fin8 o) (fin8 oi) tau8 r ∧
      RealCell8 o k (((c * ν : ℤ) : ℝ) / n) (((a * ν : ℤ) : ℝ) / n)

/-- A line good with constant `L < n` is good at `n` (`results/struct-lb-extend.md` §3.3,
Theorem B case 2, organize-archive b5cb45e). -/
theorem lineGoodAt_of_lineGood {c a L : ℤ} (h : LineGood c a L) (hL0 : 0 < L) (hLn : L < n) :
    LineGoodAt c a n := by
  intro r h1 h2
  obtain ⟨o, oi, k, lo, hi, den, hoi, hcov, hwit, hlen⟩ := h r h1 h2
  have hden : 0 < den := by
    simp only [lineWitOK, Bool.and_eq_true, decide_eq_true_eq] at hwit
    exact hwit.1.1
  obtain ⟨ν, hν1, hν2⟩ := exists_int_div_between (n := n) hden hL0 hlen hLn
  refine ⟨o, oi, k, ν, hoi, hcov, ?_⟩
  convert lineWitOK_spec hwit hν1 hν2 using 2 <;> push_cast <;> ring

/-- A checked line witness is good with any constant `L'` that bounds the lengths of its
segments. -/
theorem lineOK_len_spec {T : List Ctx8} (hT : TableOK T) {c a L L' : ℤ} {ws : List LineWit}
    (h : lineOK T c a L ws = true)
    (hlen : ws.all (fun w ↦ decide (w.den ≤ (w.hi - w.lo) * L')) = true) : LineGood c a L' := by
  intro r h1 h2
  simp only [lineOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hall, hor⟩ := h
  obtain ⟨i, hi, rfl, m, hm, hb⟩ := exists_mask_of_orAll hor h1 h2
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  have hwok := List.all_eq_true.mp hall w hw
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq] at hwok
  have hl := List.all_eq_true.mp hlen w hw
  simp only [decide_eq_true_eq] at hl
  have hmask := maskOK_ctxOf hT w.ctx
  exact ⟨_, _, w.k, w.lo, w.hi, w.den, maskOK_inv hmask, maskOK_covers hmask hi hb, hwok.1, hl⟩

/-- A checked row gives the line check of each of its admissible lines. -/
theorem lineOK_of_rowOK {T : List Ctx8} {H L : ℤ} {B c : ℕ} {row : List (List LineWit)}
    (h : rowOK T H L B c row = true) {a : ℤ} (hadm : admB c a = true)
    (hH : (c : ℤ) ^ 2 + a ^ 2 ≤ H) (ha : |a| ≤ B) :
    lineOK T c a L (row.getD (a + B).toNat []) = true := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have h1 := allBelow_spec h (a + B).toNat (by omega)
  have hj : (((a + B).toNat : ℕ) : ℤ) - B = a := by omega
  rw [hj, hadm, Bool.true_and, decide_eq_true hH, Bool.not_true, Bool.false_or] at h1
  exact h1

/-- A point witness: the context `ctx` of a table and the sample index `ν`. -/
structure PtWit where
  ctx : ℕ
  ν : ℤ

/-- The shift `⌊α ν / n⌉`, the integer nearest to `α ν / n`. -/
def rdK (α ν : ℤ) (n : ℕ) : ℤ :=
  (2 * α * ν + n) / (2 * n)

/-- The shifts of the four slots at the sample `ν (c, a)/n`. -/
def ptK (c a ν : ℤ) (n : ℕ) : List ℤ :=
  [rdK c ν n, rdK (3 * c) ν n, rdK (5 * c) ν n, rdK a ν n]

/-- The sample `ν (c, a)/n` lies in the cell of the context `ctx` of the table `T`: every gap
form is positive there. -/
def ptWitOK (T : List Ctx8) (c a : ℤ) (n : ℕ) (w : PtWit) : Bool :=
  allBelow (fun i ↦ decide (0 < ((gapForm (ctxOf T w.ctx).o (ptK c a w.ν n) i).1 * c +
    (gapForm (ctxOf T w.ctx).o (ptK c a w.ν n) i).2.1 * a) * w.ν +
      (gapForm (ctxOf T w.ctx).o (ptK c a w.ν n) i).2.2 * n)) 8

/-- **Soundness of `ptWitOK`** (`results/struct-lb-extend.md` §1, Lemma 0, organize-archive
b5cb45e). -/
theorem ptWitOK_spec {T : List Ctx8} {c a : ℤ} {w : PtWit} (hn : 0 < n)
    (h : ptWitOK T c a n w = true) :
    RealCell8 (ctxOf T w.ctx).o (ptK c a w.ν n) (((c * w.ν : ℤ) : ℝ) / n)
      (((a * w.ν : ℤ) : ℝ) / n) := by
  intro i hi
  have h1 := allBelow_spec h i hi
  simp only [decide_eq_true_eq] at h1
  set f := gapForm (ctxOf T w.ctx).o (ptK c a w.ν n) i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (((f.1 * c + f.2.1 * a) * w.ν + f.2.2 * n : ℤ) : ℝ) := by
    exact_mod_cast h1
  have h3 : evalF f (((c * w.ν : ℤ) : ℝ) / n) (((a * w.ν : ℤ) : ℝ) / n) =
      (((f.1 * c + f.2.1 * a) * w.ν + f.2.2 * n : ℤ) : ℝ) / n := by
    simp only [evalF]
    push_cast
    field_simp
  rw [h3]
  exact div_pos h2 hnR

/-- The points `ws` of the line `(c, a)` at `n`: each lies in the cell of its context, and the
masks cover all 105 matchings. -/
def ptsOK (T : List Ctx8) (c a : ℤ) (n : ℕ) (ws : List PtWit) : Bool :=
  ws.all (ptWitOK T c a n) && orAll (ws.map fun w ↦ (ctxOf T w.ctx).m) == 2 ^ 105 - 1

/-- **Soundness of `ptsOK`** (`results/struct-lb-extend.md` §3.3, Theorem B case 3,
organize-archive b5cb45e). -/
theorem ptsOK_spec {T : List Ctx8} (hT : TableOK T) {c a : ℤ} {ws : List PtWit} (hn : 0 < n)
    (h : ptsOK T c a n ws = true) : LineGoodAt c a n := by
  intro r h1 h2
  simp only [ptsOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hall, hor⟩ := h
  obtain ⟨i, hi, rfl, m, hm, hb⟩ := exists_mask_of_orAll hor h1 h2
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  have hmask := maskOK_ctxOf hT w.ctx
  exact ⟨_, _, _, w.ν, maskOK_inv hmask, maskOK_covers hmask hi hb,
    ptWitOK_spec hn (List.all_eq_true.mp hall w hw)⟩

/-- Trial division: some `d' ∈ [d, d + f)` divides `n`. -/
def hasDivFrom (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, f + 1 => n % d == 0 || hasDivFrom n (d + 1) f

/-- A divisor found by `hasDivFrom` shows that `n` is not prime. -/
theorem not_prime_of_hasDivFrom : ∀ {d f : ℕ}, 2 ≤ d → d + f ≤ n → hasDivFrom n d f = true →
    ¬n.Prime
  | _, 0, _, _, h => by simp [hasDivFrom] at h
  | d, f + 1, hd, hdf, h => by
    simp only [hasDivFrom, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · intro hp
      have := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h)
      omega
    · exact not_prime_of_hasDivFrom (by omega) (by omega) h

/-- `X ≡ a/c` is a tail label at `n`: `a ≢ l c (mod n)` for the gadget labels `l = ±1, ±3, ±5`
and for `l = 0` (`results/struct-lb-extend.md` §1, organize-archive b5cb45e). -/
def labelB (c a : ℤ) (n : ℕ) : Bool :=
  [0, 1, -1, 3, -3, 5, -5].all fun l : ℤ ↦ (a - l * c) % (n : ℤ) != 0

/-- The pair `(line, n)` needs points of its own: `(c, a)` can be a shortest vector at the prime
`n ≥ 11`, `n ≠ 13`, with a tail label. -/
def neededB (c a : ℤ) (n : ℕ) : Bool :=
  decide (3 * (c ^ 2 + a ^ 2) ^ 2 ≤ 4 * (n : ℤ) ^ 2) && decide (11 ≤ n) && decide (n ≠ 13) &&
    !hasDivFrom n 2 (n - 2) && labelB c a n

/-- The walk over `n₀ ≤ n < n₀ + f`: each `n` with an entry of `es` has checked points, and
every other `n` does not need any. The entries are sorted by `n`. -/
def walkOK (T : List Ctx8) (c a : ℤ) : ℕ → ℕ → List (ℕ × List PtWit) → Bool
  | _, 0, _ => true
  | n, f + 1, [] => !neededB c a n && walkOK T c a (n + 1) f []
  | n, f + 1, (m, ws) :: es =>
    if m = n then ptsOK T c a n ws && walkOK T c a (n + 1) f es
    else !neededB c a n && walkOK T c a (n + 1) f ((m, ws) :: es)

/-- **Soundness of `walkOK`**: every `n` of the range that needs points has them. -/
theorem walkOK_spec {T : List Ctx8} {c a : ℤ} : ∀ {n₀ f : ℕ} {es : List (ℕ × List PtWit)},
    walkOK T c a n₀ f es = true → ∀ n, n₀ ≤ n → n < n₀ + f → neededB c a n = true →
      ∃ ws, ptsOK T c a n ws = true
  | _, 0, _, _, _, _, h2, _ => absurd h2 (by omega)
  | n₀, f + 1, [], h, n, h1, h2, hn => by
    simp only [walkOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact absurd (h.1.symm.trans hn) (by decide)
    · exact walkOK_spec h.2 n h1 (by omega) hn
  | n₀, f + 1, (m, ws) :: es, h, n, h1, h2, hn => by
    simp only [walkOK] at h
    split_ifs at h with hm
    · simp only [Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ⟨ws, h.1⟩
      · exact walkOK_spec h.2 n h1 (by omega) hn
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact absurd (h.1.symm.trans hn) (by decide)
      · exact walkOK_spec h.2 n h1 (by omega) hn

/-- One line of the small table: its own bound `L`, the least `n₀` that it can serve, and the
points at each `n ∈ [n₀, L]` that needs them. -/
structure SmallLine where
  L : ℤ
  nlo : ℕ
  es : List (ℕ × List PtWit)

/-- The check of one line `(c, a)` with its segments `old` from the long line table. -/
def smallOK (T : List Ctx8) (c a : ℤ) (s : SmallLine) (old : List LineWit) : Bool :=
  decide (0 < s.L) && old.all (fun w ↦ decide (w.den ≤ (w.hi - w.lo) * s.L)) &&
    decide (4 * ((s.nlo : ℤ) - 1) ^ 2 < 3 * (c ^ 2 + a ^ 2) ^ 2) &&
      walkOK T c a s.nlo (s.L.toNat + 1 - s.nlo) s.es

/-- **A checked line of the small table is good at every prime it can serve**
(`results/struct-lb-extend.md` §3.3, Theorem B cases 2 and 3, organize-archive b5cb45e). -/
theorem lineGoodAt_of_smallOK {T : List Ctx8} (hT : TableOK T) {c a : ℤ} {s : SmallLine}
    {old : List LineWit} (hs : smallOK T c a s old = true)
    (hold : lineOK ctxT8b c a 1176 old = true) (hp : n.Prime) (h11 : 11 ≤ n) (h13 : n ≠ 13)
    (hH : 3 * (c ^ 2 + a ^ 2) ^ 2 ≤ 4 * (n : ℤ) ^ 2) (hlab : labelB c a n = true) :
    LineGoodAt c a n := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hL0, hlen⟩, hlo⟩, hwalk⟩ := hs
  by_cases hLn : s.L < n
  · exact lineGoodAt_of_lineGood (lineOK_len_spec ctxT8b_ok hold hlen) hL0 hLn
  · have hneed : neededB c a n = true := by
      simp only [neededB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨⟨⟨⟨hH, h11⟩, h13⟩, ?_⟩, hlab⟩
      cases h : hasDivFrom n 2 (n - 2)
      · rfl
      · exact absurd hp (not_prime_of_hasDivFrom le_rfl (by omega) h)
    have hlo' : s.nlo ≤ n := by
      by_contra hc
      have h1 : (n : ℤ) ≤ (s.nlo : ℤ) - 1 := by omega
      have h2 : (n : ℤ) ^ 2 ≤ ((s.nlo : ℤ) - 1) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      linarith
    have hLn' : n ≤ s.L.toNat := by omega
    obtain ⟨ws, hws⟩ := walkOK_spec hwalk n hlo' (by omega) hneed
    exact ptsOK_spec hT hp.pos hws

/-- The row `c` of the small table, indexed by `a + 36`: every admissible `(c, a)` with
`c² + a² ≤ 1358` has a checked entry. -/
def smallRowOK (T : List Ctx8) (c : ℕ) (row : List SmallLine) : Bool :=
  allBelow (fun j ↦ !(admB c ((j : ℤ) - 36) && decide ((c : ℤ) ^ 2 + ((j : ℤ) - 36) ^ 2 ≤ 1358)) ||
    smallOK T c ((j : ℤ) - 36) (row.getD j ⟨0, 0, []⟩)
      ((lineRowB c).getD (((j : ℤ) - 36) + ((49 : ℕ) : ℤ)).toNat [])) 73

/-- A checked row gives the check of each of its admissible lines. -/
theorem smallOK_of_rowOK {T : List Ctx8} {c : ℕ} {row : List SmallLine}
    (h : smallRowOK T c row = true) {a : ℤ} (hadm : admB c a = true)
    (hH : (c : ℤ) ^ 2 + a ^ 2 ≤ 1358) (ha : |a| ≤ 36) :
    smallOK T c a (row.getD (a + 36).toNat ⟨0, 0, []⟩)
      ((lineRowB c).getD (a + ((49 : ℕ) : ℤ)).toNat []) = true := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have h1 := allBelow_spec h (a + 36).toNat (by omega)
  have hj : (((a + 36).toNat : ℕ) : ℤ) - 36 = a := by omega
  rw [hj, hadm, Bool.true_and, decide_eq_true hH, Bool.not_true, Bool.false_or] at h1
  exact h1

end LowerBound

end Pairing
