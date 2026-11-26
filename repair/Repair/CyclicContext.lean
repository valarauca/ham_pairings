import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Insert

/-!
# Cyclic successors of positions (the slot of Lemma 5)

A context `C_t(E)` pairs the exit end of each defect with the entry end of the next defect in
`π_t`-order, cyclically. With positions recorded as natural numbers, the next defect after
position `x` in `E` is `cnext E x`: the least position of `E` above `x`, or the least position of
`E` when `x` is the largest.

* `isNext_cnext`, `IsNext.unique` : `cnext E x` is the unique cyclic successor of `x ∈ E`.
* `exists_slot` : a new position `y ∉ E⁻` falls in exactly the slot `(p, cnext E⁻ p)` of some
  `p ∈ E⁻`, cyclically between `p` and its successor.
* `cnext_insert_slot`, `cnext_insert_of_not_between` : positions do not depend on `E`, so
  inserting `y` changes only the successor of `p`, which becomes `y`, and `y` takes over the old
  successor of `p`. In context terms `C_t(E)` is `C_t(E⁻)` with `f = {exit(p), entry(q)}`
  replaced by `exit(p)–entry(y)` and `exit(y)–entry(q)`, `q = cnext E⁻ p`.

Source: `results/hybrid-joint-incoherence.md` (organize-archive 4f82c7d), Lemma 5 and the first
sentence of its proof. Positions are `π_t(x) = |x u_t|` from
`results/hybrid-pair-incoherence.md` §1.
-/

namespace Pairing

namespace CyclicContext

variable (E : Finset ℕ)

/-- The next position after `x` in `E`, cyclically (`results/hybrid-pair-incoherence.md` §1,
contexts). -/
def cnext (x : ℕ) : ℕ :=
  if h : (E.filter (x < ·)).Nonempty then (E.filter (x < ·)).min' h
  else if h' : E.Nonempty then E.min' h' else x

/-- `z` is the cyclic successor of `x` in `E`: the least element above `x`, or the least element
of `E` when nothing lies above `x`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def IsNext (x z : ℕ) : Prop :=
  z ∈ E ∧ ((x < z ∧ ∀ w ∈ E, x < w → z ≤ w) ∨ ((∀ w ∈ E, w ≤ x) ∧ ∀ w ∈ E, z ≤ w))

/-- `cnext E x` is a cyclic successor of `x ∈ E`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem isNext_cnext {x : ℕ} (hx : x ∈ E) : IsNext E x (cnext E x) := by
  unfold cnext
  split_ifs with h h'
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hm
    refine ⟨hm.1, Or.inl ⟨hm.2, fun w hw hxw ↦ Finset.min'_le _ _ ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hw, hxw⟩
  · refine ⟨Finset.min'_mem _ _, Or.inr ⟨fun w hw ↦ ?_, fun w hw ↦ Finset.min'_le _ _ hw⟩⟩
    by_contra hlt
    exact h ⟨w, Finset.mem_filter.mpr ⟨hw, by omega⟩⟩
  · exact absurd ⟨x, hx⟩ h'

variable {E}

/-- The cyclic successor is unique.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem IsNext.unique {x z z' : ℕ} (h : IsNext E x z) (h' : IsNext E x z') : z = z' := by
  obtain ⟨hz, h1 | h1⟩ := h <;> obtain ⟨hz', h2 | h2⟩ := h'
  · exact le_antisymm (h1.2 z' hz' h2.1) (h2.2 z hz h1.1)
  · exact absurd (h2.1 z hz) (by omega)
  · exact absurd (h1.1 z' hz') (by omega)
  · exact le_antisymm (h1.2 z' hz') (h2.2 z hz)

/-- `y` lies cyclically strictly between `x` and `z`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def Between (x y z : ℕ) : Prop :=
  (x < y ∧ y < z) ∨ (z ≤ x ∧ (x < y ∨ y < z))

/-- **The slot of Lemma 5.** Inserting a new position `y` that lies between `p` and its
successor `q` makes `y` the successor of `p` and `q` the successor of `y`
(`results/hybrid-joint-incoherence.md`, proof of Lemma 5). -/
theorem cnext_insert_slot {y p : ℕ} (hy : y ∉ E) (hp : p ∈ E)
    (hb : Between p y (cnext E p)) :
    IsNext (insert y E) p y ∧ IsNext (insert y E) y (cnext E p) := by
  obtain ⟨hz, ha | hb'⟩ := isNext_cnext E hp
  · have hxz := ha.1
    rcases hb with ⟨h1, h2⟩ | ⟨h1, -⟩
    · refine ⟨⟨Finset.mem_insert_self _ _, Or.inl ⟨h1, fun w hw hpw ↦ ?_⟩⟩,
        ⟨Finset.mem_insert_of_mem hz, Or.inl ⟨h2, fun w hw hyw ↦ ?_⟩⟩⟩
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact le_rfl
        · exact h2.le.trans (ha.2 w hw hpw)
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · omega
        · exact ha.2 w hw (by omega)
    · omega
  · have hzp : cnext E p ≤ p := hb'.1 _ hz
    rcases hb with ⟨h1, h2⟩ | ⟨-, h1 | h1⟩
    · omega
    · refine ⟨⟨Finset.mem_insert_self _ _, Or.inl ⟨h1, fun w hw hpw ↦ ?_⟩⟩,
        ⟨Finset.mem_insert_of_mem hz, Or.inr ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩⟩
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact le_rfl
        · exact absurd (hb'.1 w hw) (by omega)
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact le_rfl
        · exact (hb'.1 w hw).trans h1.le
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · omega
        · exact hb'.2 w hw
    · refine ⟨⟨Finset.mem_insert_self _ _, Or.inr ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩,
        ⟨Finset.mem_insert_of_mem hz, Or.inl ⟨h1, fun w hw hyw ↦ ?_⟩⟩⟩
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · omega
        · exact hb'.1 w hw
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact le_rfl
        · exact h1.le.trans (hb'.2 w hw)
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · omega
        · exact hb'.2 w hw

/-- Inserting `y` outside the slot of `x` keeps the successor of `x`
(`results/hybrid-joint-incoherence.md`, proof of Lemma 5). -/
theorem cnext_insert_of_not_between {x y : ℕ} (hy : y ∉ E) (hx : x ∈ E)
    (hb : ¬Between x y (cnext E x)) : IsNext (insert y E) x (cnext E x) := by
  have hne : y ≠ cnext E x := fun h ↦ hy (h ▸ (isNext_cnext E hx).1)
  obtain ⟨hz, ha | hb'⟩ := isNext_cnext E hx
  · refine ⟨Finset.mem_insert_of_mem hz, Or.inl ⟨ha.1, fun w hw hxw ↦ ?_⟩⟩
    rcases Finset.mem_insert.mp hw with rfl | hw
    · by_contra hlt
      exact hb (Or.inl ⟨hxw, by omega⟩)
    · exact ha.2 w hw hxw
  · have hzx : cnext E x ≤ x := hb'.1 _ hz
    refine ⟨Finset.mem_insert_of_mem hz, Or.inr ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · by_contra hlt
        exact hb (Or.inr ⟨hzx, Or.inl (by omega)⟩)
      · exact hb'.1 w hw
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · by_contra hlt
        exact hb (Or.inr ⟨hzx, Or.inr (by omega)⟩)
      · exact hb'.2 w hw

/-- Every new position `y` falls in the slot of some `p ∈ E⁻`: the two labels adjacent to `y` in
`π_t`-order are `p` and `cnext E⁻ p` (`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem exists_slot {y : ℕ} (hy : y ∉ E) (hE : E.Nonempty) :
    ∃ p ∈ E, Between p y (cnext E p) := by
  by_cases hS : (E.filter (· < y)).Nonempty
  · set p := (E.filter (· < y)).max' hS with hp
    have hpm := Finset.max'_mem _ hS
    rw [← hp, Finset.mem_filter] at hpm
    refine ⟨p, hpm.1, ?_⟩
    obtain ⟨hz, ha | hb'⟩ := isNext_cnext E hpm.1
    · left
      refine ⟨hpm.2, ?_⟩
      by_contra hle
      have hzy : cnext E p < y := by
        rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
        · exact h
        · exact absurd (h ▸ hz) hy
      have := Finset.le_max' (E.filter (· < y)) _ (Finset.mem_filter.mpr ⟨hz, hzy⟩)
      rw [← hp] at this
      omega
    · exact Or.inr ⟨hb'.1 _ hz, Or.inl hpm.2⟩
  · set p := E.max' hE with hp
    have hpm := Finset.max'_mem _ hE
    rw [← hp] at hpm
    have hall : ∀ w ∈ E, y < w := fun w hw ↦ by
      by_contra hle
      rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
      · exact hS ⟨w, Finset.mem_filter.mpr ⟨hw, h⟩⟩
      · exact hy (h ▸ hw)
    refine ⟨p, hpm, Or.inr ⟨?_, Or.inr (hall _ (isNext_cnext E hpm).1)⟩⟩
    rw [hp]
    exact Finset.le_max' _ _ (isNext_cnext E hpm).1

variable (E) in
/-- The previous position before `x` in `E`, cyclically.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def cprev (x : ℕ) : ℕ :=
  if h : (E.filter (· < x)).Nonempty then (E.filter (· < x)).max' h
  else if h' : E.Nonempty then E.max' h' else x

/-- The successor of a position of `E` lies in `E`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem cnext_mem {x : ℕ} (hx : x ∈ E) : cnext E x ∈ E := (isNext_cnext E hx).1

/-- The predecessor of a position of `E` lies in `E`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem cprev_mem {x : ℕ} (hx : x ∈ E) : cprev E x ∈ E := by
  unfold cprev
  split_ifs with h h'
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ h)).1
  · exact Finset.max'_mem _ _
  · exact absurd ⟨x, hx⟩ h'

/-- `x` is the successor of its predecessor.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem isNext_cprev {x : ℕ} (hx : x ∈ E) : IsNext E (cprev E x) x := by
  unfold cprev
  split_ifs with h h'
  · have hm := Finset.max'_mem _ h
    rw [Finset.mem_filter] at hm
    refine ⟨hx, Or.inl ⟨hm.2, fun w hw hlt ↦ ?_⟩⟩
    by_contra hwx
    have := Finset.le_max' (E.filter (· < x)) w (Finset.mem_filter.mpr ⟨hw, by omega⟩)
    omega
  · refine ⟨hx, Or.inr ⟨fun w hw ↦ Finset.le_max' _ _ hw, fun w hw ↦ ?_⟩⟩
    by_contra hlt
    exact h ⟨w, Finset.mem_filter.mpr ⟨hw, by omega⟩⟩
  · exact absurd ⟨x, hx⟩ h'

/-- Two positions of `E` with the same successor are equal.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem IsNext.inj {w x z : ℕ} (hw : w ∈ E) (hx : x ∈ E) (h : IsNext E w z) (h' : IsNext E x z) :
    w = x := by
  obtain ⟨hz, h1 | h1⟩ := h <;> obtain ⟨-, h2 | h2⟩ := h'
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (h1.2 x hx hlt) (by omega)
    · exact absurd (h2.2 w hw hlt) (by omega)
  · exact absurd (h2.2 w hw) (by omega)
  · exact absurd (h1.2 x hx) (by omega)
  · exact le_antisymm (h2.1 w hw) (h1.1 x hx)

/-- `cnext` undoes `cprev` on `E`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem cnext_cprev {x : ℕ} (hx : x ∈ E) : cnext E (cprev E x) = x :=
  (isNext_cnext E (cprev_mem hx)).unique (isNext_cprev hx)

/-- `cprev` undoes `cnext` on `E`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem cprev_cnext {x : ℕ} (hx : x ∈ E) : cprev E (cnext E x) = x :=
  IsNext.inj (cprev_mem (cnext_mem hx)) hx (isNext_cprev (cnext_mem hx)) (isNext_cnext E hx)

/-- The slot of a new position is unique.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem slot_unique {y p x : ℕ} (hy : y ∉ E) (hp : p ∈ E) (hx : x ∈ E)
    (hbp : Between p y (cnext E p)) (hbx : Between x y (cnext E x)) : x = p :=
  IsNext.inj (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hp)
    (cnext_insert_slot hy hx hbx).1 (cnext_insert_slot hy hp hbp).1

/-- **Insertion of one position.** With `p` the slot of `y`, `cnext (E⁻ ∪ {y})` agrees with
`cnext E⁻` except that `p ↦ y` and `y ↦ cnext E⁻ p`, and `cprev (E⁻ ∪ {y})` agrees with
`cprev E⁻` except at `y` and `cnext E⁻ p`. This is the statement that `C_t(E)` is `C_t(E⁻)`
with the slot `f` replaced by `p–entry(y)`, `exit(y)–q` (`results/hybrid-joint-incoherence.md`,
proof of Lemma 5). -/
theorem insert_context {y p : ℕ} (hy : y ∉ E) (hp : p ∈ E) (hb : Between p y (cnext E p)) :
    cnext (insert y E) p = y ∧ cnext (insert y E) y = cnext E p ∧
      cprev (insert y E) y = p ∧ cprev (insert y E) (cnext E p) = y ∧
      (∀ x ∈ E, x ≠ p → cnext (insert y E) x = cnext E x) ∧
      (∀ x ∈ E, x ≠ cnext E p → cprev (insert y E) x = cprev E x) := by
  obtain ⟨h1, h2⟩ := cnext_insert_slot hy hp hb
  have hyE : y ∈ insert y E := Finset.mem_insert_self _ _
  have hpE : p ∈ insert y E := Finset.mem_insert_of_mem hp
  have e1 : cnext (insert y E) p = y := (isNext_cnext _ hpE).unique h1
  have e2 : cnext (insert y E) y = cnext E p := (isNext_cnext _ hyE).unique h2
  refine ⟨e1, e2, ?_, ?_, fun x hx hxp ↦ ?_, fun x hx hxq ↦ ?_⟩
  · have h := cprev_cnext hpE
    rwa [e1] at h
  · have h := cprev_cnext hyE
    rwa [e2] at h
  · have hnb : ¬Between x y (cnext E x) := fun h ↦ hxp (slot_unique hy hp hx hb h)
    exact (isNext_cnext _ (Finset.mem_insert_of_mem hx)).unique
      (cnext_insert_of_not_between hy hx hnb)
  · have hw := cprev_mem hx
    have hwp : cprev E x ≠ p := fun h ↦ hxq (by rw [← h, cnext_cprev hx])
    have hnb : ¬Between (cprev E x) y (cnext E (cprev E x)) := fun h ↦
      hwp (slot_unique hy hp hw hb h)
    have hn := cnext_insert_of_not_between hy hw hnb
    rw [cnext_cprev hx] at hn
    exact IsNext.inj (cprev_mem (Finset.mem_insert_of_mem hx)) (Finset.mem_insert_of_mem hw)
      (isNext_cprev (Finset.mem_insert_of_mem hx)) hn

end CyclicContext

end Pairing
