import Repair.FactorCap.Farey

/-!
# The P9 cell checker

The configuration is `a = (1,3,5,2,4,6,7,8)` with `R = Q` (COD-186, archive cap check). A cell
is an open interval `p/q < θ < p'/q'` between Farey neighbours of order 16. For `θ = μ/n` in
the cell, entry `i` has floor `k_i = ⌊θ a_i⌋`, side `[{θ a_i} < 1/2]` and level
`ℓ_i = n ‖θ a_i‖`. In integers the level is the linear form

* `ℓ_i = a_i μ - k_i n` on the plus side,
* `ℓ_i = (k_i + 1) n - a_i μ` on the minus side.

A `Cell` stores the eight entries in increasing level order, each as `⟨i, side, k_i⟩`, and a
set `z` of ends. End `2i` is `+a_i` and end `2i + 1` is `-a_i`.

`Cell.check` is a `Bool` on `List`, `ℕ` and `ℤ` only, with no `Finset` and no `ℚ`. It checks

* the Farey determinant `p' q - p q' = 1`,
* that the entry indices are a permutation of `0, …, 7`,
* `0 < ℓ_i` and `2 ℓ_i < n` for every entry,
* `ℓ_e < ℓ_f` for every consecutive pair of entries,
* that `z` is a nonempty proper set of ends, closed under `Q` and under the context `∂`.

Each of the linear facts is checked by `Cell.posOn` at the two cell endpoints only, and
`form_pos_of_endpoints` lifts it to every `μ/n` strictly inside the cell. `Cell.check_sound`
collects the result.
-/

namespace Pairing

namespace FactorCap

/-- The configuration `a = (1,3,5,2,4,6,7,8)`. -/
def cfg : List ℕ := [1, 3, 5, 2, 4, 6, 7, 8]

/-- One entry of a cell's level order. -/
structure Entry where
  /-- The index `i` into `cfg`. -/
  idx : ℕ
  /-- The side bit `[{θ a_i} < 1/2]`. -/
  plus : Bool
  /-- The floor `⌊θ a_i⌋`. -/
  fl : ℕ

/-- An open Farey cell `p/q < θ < p'/q'` with its level order and a closed end set. -/
structure Cell where
  /-- Numerator of the left endpoint. -/
  p : ℕ
  /-- Denominator of the left endpoint. -/
  q : ℕ
  /-- Numerator of the right endpoint. -/
  p' : ℕ
  /-- Denominator of the right endpoint. -/
  q' : ℕ
  /-- The eight entries in increasing level order. -/
  order : List Entry
  /-- A set of ends closed under `Q` and the context. -/
  z : List ℕ

/-- The configuration value `a_i` of an entry. -/
def Entry.a (e : Entry) : ℤ := cfg.getD e.idx 0

/-- The coefficient of `μ` in the level form `ℓ = A μ - B n`. -/
def Entry.coefA (e : Entry) : ℤ := if e.plus then e.a else -e.a

/-- The coefficient of `n` in the level form `ℓ = A μ - B n`. -/
def Entry.coefB (e : Entry) : ℤ := if e.plus then (e.fl : ℤ) else -((e.fl : ℤ) + 1)

/-- The level `ℓ = A μ - B n` of an entry at `θ = μ/n`. -/
def Entry.level (e : Entry) (μ n : ℤ) : ℤ := e.coefA * μ - e.coefB * n

/-- The end at which the zig-zag enters the entry's edge. -/
def Entry.entryEnd (e : Entry) : ℕ := if e.plus then 2 * e.idx else 2 * e.idx + 1

/-- The end at which the zig-zag leaves the entry's edge. -/
def Entry.exitEnd (e : Entry) : ℕ := if e.plus then 2 * e.idx + 1 else 2 * e.idx

/-- `μ/n` lies strictly inside the cell. -/
def Cell.Contains (c : Cell) (μ n : ℤ) : Prop :=
  (c.p : ℤ) * n < c.q * μ ∧ (c.q' : ℤ) * μ < c.p' * n

/-- The endpoint test for `0 < A μ - B n` on the cell. -/
def Cell.posOn (c : Cell) (A B : ℤ) : Bool :=
  decide (0 ≤ A * c.p' - B * c.q') && decide (0 ≤ A * c.p - B * c.q) &&
    decide (0 < A * c.p' - B * c.q' + (A * c.p - B * c.q))

/-- The matching `Q` on the 16 ends. -/
def qPairs : List (ℕ × ℕ) :=
  [(0, 14), (1, 7), (2, 6), (3, 9), (4, 8), (5, 11), (10, 12), (13, 15)]

/-- The context `∂`: the exit end of each entry joined to the entry end of the next,
cyclically. -/
def Cell.ctxPairs (c : Cell) : List (ℕ × ℕ) :=
  (c.order.zip (c.order.tail ++ c.order.take 1)).map fun ef => (ef.1.exitEnd, ef.2.entryEnd)

/-- Every entry has `0 < ℓ` and `2 ℓ < n` on the cell. -/
def Cell.levelsOK (c : Cell) : Bool :=
  c.order.all fun e => c.posOn e.coefA e.coefB && c.posOn (-2 * e.coefA) (-(2 * e.coefB + 1))

/-- Consecutive entries have strictly increasing levels on the cell. -/
def Cell.orderOK (c : Cell) : Bool :=
  (c.order.zip c.order.tail).all fun ef =>
    c.posOn (ef.2.coefA - ef.1.coefA) (ef.2.coefB - ef.1.coefB)

/-- `z` is a nonempty proper set of ends, closed under `Q` and `∂`. -/
def Cell.zOK (c : Cell) : Bool :=
  !c.z.isEmpty && c.z.all (· < 16) && (List.range 16).any (fun x => !c.z.contains x) &&
    (c.ctxPairs ++ qPairs).all fun xy => c.z.contains xy.1 == c.z.contains xy.2

/-- The cell checker. -/
def Cell.check (c : Cell) : Bool :=
  c.p' * c.q == c.p * c.q' + 1 && (c.order.map Entry.idx).isPerm (List.range 8) &&
    c.levelsOK && c.orderOK && c.zOK

/-- A checked cell has Farey determinant `p' q - p q' = 1`. -/
theorem Cell.det_of_check {c : Cell} (h : c.check = true) : c.p' * c.q = c.p * c.q' + 1 := by
  simp only [Cell.check, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

/-- Soundness of the endpoint test, from the sign lemma `form_pos_of_endpoints`. -/
theorem Cell.posOn_sound {c : Cell} (hdet : c.p' * c.q = c.p * c.q' + 1) {A B : ℤ}
    (h : c.posOn A B = true) {μ n : ℤ} (hμ : c.Contains μ n) : 0 < A * μ - B * n := by
  simp only [Cell.posOn, Bool.and_eq_true, decide_eq_true_eq] at h
  have hdet' : (c.p' : ℤ) * c.q - c.p * c.q' = 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hdet
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
    linarith
  exact form_pos_of_endpoints hdet' hμ.1 hμ.2 h.1.1 h.1.2 h.2

/-- The entry indices of a checked cell are a permutation of `0, …, 7`. -/
theorem Cell.idx_perm {c : Cell} (h : c.check = true) :
    (c.order.map Entry.idx).Perm (List.range 8) := by
  simp only [Cell.check, Bool.and_eq_true] at h
  exact List.isPerm_iff.1 h.1.1.1.2

/-- Every level of a checked cell satisfies `0 < ℓ` and `2 ℓ < n` at each `μ/n` inside it. -/
theorem Cell.level_bounds {c : Cell} (h : c.check = true) {μ n : ℤ} (hμ : c.Contains μ n)
    {e : Entry} (he : e ∈ c.order) : 0 < e.level μ n ∧ 2 * e.level μ n < n := by
  have hdet := Cell.det_of_check h
  simp only [Cell.check, Cell.levelsOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h.1.1.2 e he
  have k1 := Cell.posOn_sound hdet h1 hμ
  have k2 := Cell.posOn_sound hdet h2 hμ
  unfold Entry.level
  constructor <;> linarith

/-- Consecutive levels of a checked cell increase strictly at each `μ/n` inside it. -/
theorem Cell.level_lt_of_consecutive {c : Cell} (h : c.check = true) {μ n : ℤ}
    (hμ : c.Contains μ n) {e f : Entry} (hef : (e, f) ∈ c.order.zip c.order.tail) :
    e.level μ n < f.level μ n := by
  have hdet := Cell.det_of_check h
  simp only [Cell.check, Cell.orderOK, Bool.and_eq_true, List.all_eq_true] at h
  have k := Cell.posOn_sound hdet (h.1.2 (e, f) hef) hμ
  unfold Entry.level
  linarith

/-- The end set `z` of a checked cell is nonempty, proper and closed under `Q` and `∂`. -/
theorem Cell.z_sound {c : Cell} (h : c.check = true) :
    c.z ≠ [] ∧ (∀ x ∈ c.z, x < 16) ∧ (∃ x < 16, x ∉ c.z) ∧
      ∀ xy ∈ c.ctxPairs ++ qPairs, (xy.1 ∈ c.z ↔ xy.2 ∈ c.z) := by
  simp only [Cell.check, Cell.zOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.any_eq_true, decide_eq_true_eq, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hne, hlt⟩, x, hx, hxz⟩, hcl⟩ := h.2
  refine ⟨hne, hlt, ⟨x, hx, fun hm => Bool.false_ne_true
    (hxz.symm.trans (List.contains_iff_mem.2 hm))⟩, fun xy hxy => ?_⟩
  rw [← List.contains_iff_mem, ← List.contains_iff_mem, hcl xy hxy]

/-- From the level and side of an entry, `⌊a_i μ / n⌋ = k_i` and the residue `a_i μ mod n` is
`ℓ` on the plus side and `n - ℓ` on the minus side. -/
theorem Entry.ediv_emod {e : Entry} {μ n : ℤ} (h0 : 0 < e.level μ n) (h2 : 2 * e.level μ n < n) :
    e.a * μ / n = e.fl ∧ e.a * μ % n = if e.plus then e.level μ n else n - e.level μ n := by
  obtain ⟨idx, plus, fl⟩ := e
  rw [Int.ediv_emod_unique (by linarith)]
  cases plus <;>
    simp only [Entry.level, Entry.coefA, Entry.coefB, Bool.false_eq_true, ↓reduceIte] at * <;>
    refine ⟨by ring, by linarith, by linarith⟩

/-- Soundness of the cell checker. At every `μ/n` strictly inside a checked cell, the entry
indices are a permutation of `0, …, 7`, each level satisfies `0 < ℓ` and `2 ℓ < n` and fixes
`⌊a_i μ / n⌋` and `a_i μ mod n`, consecutive levels increase strictly, and `z` is a nonempty
proper set of ends closed under `Q` and `∂`. -/
theorem Cell.check_sound {c : Cell} (h : c.check = true) {μ n : ℤ} (hμ : c.Contains μ n) :
    (c.order.map Entry.idx).Perm (List.range 8) ∧
      (∀ e ∈ c.order, 0 < e.level μ n ∧ 2 * e.level μ n < n ∧ e.a * μ / n = e.fl ∧
        e.a * μ % n = if e.plus then e.level μ n else n - e.level μ n) ∧
      (∀ ef ∈ c.order.zip c.order.tail, ef.1.level μ n < ef.2.level μ n) ∧
      c.z ≠ [] ∧ (∀ x ∈ c.z, x < 16) ∧ (∃ x < 16, x ∉ c.z) ∧
      ∀ xy ∈ c.ctxPairs ++ qPairs, (xy.1 ∈ c.z ↔ xy.2 ∈ c.z) := by
  refine ⟨Cell.idx_perm h, fun e he => ?_, fun ef hef => Cell.level_lt_of_consecutive h hμ hef,
    Cell.z_sound h⟩
  obtain ⟨h0, h2⟩ := Cell.level_bounds h hμ he
  exact ⟨h0, h2, Entry.ediv_emod h0 h2⟩

/-- A list of cells walks from its first left endpoint to `1/1`, each right endpoint being the
next left endpoint. -/
def walkOK : List Cell → Bool
  | [] => false
  | [c] => c.p' == 1 && c.q' == 1
  | c :: d :: cs => c.p' == d.p && c.q' == d.q && walkOK (d :: cs)

/-- Every left denominator lies in `[1, 16]`. -/
def denomOK (cs : List Cell) : Bool :=
  cs.all fun c => decide (0 < c.q) && decide (c.q ≤ 16)

/-- Walking a chain of cells. If `μ/n` is right of the first left endpoint, below `1`, and on no
later left endpoint, it lies strictly inside some cell. -/
theorem exists_contains {μ n : ℤ} (hμn : μ < n) :
    ∀ (c : Cell) (cs : List Cell), walkOK (c :: cs) = true → (c.p : ℤ) * n < c.q * μ →
      (∀ d ∈ cs, (d.p : ℤ) * n ≠ d.q * μ) → ∃ d ∈ c :: cs, d.Contains μ n
  | c, [], h, hl, _ => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      refine ⟨c, List.mem_singleton_self c, hl, ?_⟩
      rw [h.1, h.2]
      push_cast
      linarith
  | c, d :: cs, h, hl, hne => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hp, hq⟩, hrest⟩ := h
      by_cases hr : (c.q' : ℤ) * μ < c.p' * n
      · exact ⟨c, List.mem_cons_self, hl, hr⟩
      · have hd := hne d List.mem_cons_self
        rw [← hp, ← hq] at hd
        have hd' : (d.p : ℤ) * n < d.q * μ := by
          rw [← hp, ← hq]
          exact lt_of_le_of_ne (not_lt.1 hr) hd
        obtain ⟨e, he, hc⟩ :=
          exists_contains hμn d cs hrest hd' fun e he => hne e (List.mem_cons_of_mem _ he)
        exact ⟨e, List.mem_cons_of_mem _ he, hc⟩

/-- Covering. For a chain of cells from `0/1` to `1/1` with left denominators in `[1, 16]`,
every `μ/n` with `n > 16` prime and `0 < μ < n` lies strictly inside one of the cells. -/
theorem exists_contains_of_prime {c : Cell} {cs : List Cell} (hw : walkOK (c :: cs) = true)
    (hp : c.p = 0) (hq : c.q = 1) (hd : denomOK (c :: cs) = true) {n μ : ℕ} (hn : n.Prime)
    (h16 : 16 < n) (hμ0 : 0 < μ) (hμn : μ < n) : ∃ d ∈ c :: cs, d.Contains μ n := by
  simp only [denomOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  refine exists_contains (by exact_mod_cast hμn) c cs hw (by rw [hp, hq]; push_cast; omega) ?_
  intro d hdm
  have h := not_farey_hit (p := d.p) hn h16 hμ0 hμn (hd d (List.mem_cons_of_mem _ hdm)).1
    (hd d (List.mem_cons_of_mem _ hdm)).2
  exact_mod_cast h

end FactorCap

end Pairing
