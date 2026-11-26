import Repair.FactorCap.Cover
import Repair.FactorCap.Scale
import Repair.FactorCap.ZigZag

/-!
# From the cell facts to the zig-zag (P9, rest of task T4)

`cell_facts` and `Cell.check_sound` state the cell data in `ℤ`, for `θ = μ/n` with `μ` and `n`
naturals. This file turns them into the form the segment lemma `not_ham_of_segments` consumes.

* `endInt ε` is the integer label of end `ε` in the coordinate `x = 2v - 7`: end `2i` is `+a_i`
  and end `2i + 1` is `-a_i`. The entry end of an entry is labelled `coefA` (`endInt_entryEnd`)
  and its exit end `-coefA` (`endInt_exitEnd`).
* `Cell.ent c r` is the `r`-th entry of the level order. `Cell.ent_facts` lists what the segment
  lemma needs from a checked cell: the entries are in the order, every end `ε < 16` is the entry or
  exit end of one of them, consecutive levels increase, and the context pairs the exit end of
  entry `r` with the entry end of entry `r + 1 mod 8`.
* `zigPos_entry`, `zigPos_exit` : the `ZMod.val` bridge. For `λ ∈ ℤ/(2m-1)` with `λ.val = μ`, the
  scaled entry end `λ · coefA` sits at position `2ℓ` and the scaled exit end at `2ℓ + 1`, where
  `ℓ = coefA μ - coefB n` is the level of the entry.

Source: `results/lean-scope-p9-p10.md` §1, steps 2 to 5, and §3, task T4.
-/

namespace Pairing

namespace FactorCap

open RoundRobin.Canonical

/-- The integer label of end `ε` in the coordinate `x = 2v - 7`: end `2i` is `+a_i` and end
`2i + 1` is `-a_i`. -/
def endInt (ε : ℕ) : ℤ :=
  if ε % 2 = 0 then (cfg.getD (ε / 2) 0 : ℤ) else -(cfg.getD (ε / 2) 0 : ℤ)

/-- The entry end of an entry is labelled `coefA`. -/
theorem endInt_entryEnd (e : Entry) : endInt e.entryEnd = e.coefA := by
  obtain ⟨i, plus, k⟩ := e
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  have h3 : (2 * i + 1) % 2 = 1 := by omega
  have h4 : (2 * i + 1) / 2 = i := by omega
  cases plus <;> simp [endInt, Entry.entryEnd, Entry.coefA, Entry.a, h1, h2, h3, h4]

/-- The exit end of an entry is labelled `-coefA`. -/
theorem endInt_exitEnd (e : Entry) : endInt e.exitEnd = -e.coefA := by
  obtain ⟨i, plus, k⟩ := e
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  have h3 : (2 * i + 1) % 2 = 1 := by omega
  have h4 : (2 * i + 1) / 2 = i := by omega
  cases plus <;> simp [endInt, Entry.exitEnd, Entry.coefA, Entry.a, h1, h2, h3, h4]

/-- The entry at position `r` of a cell's level order. -/
def Cell.ent (c : Cell) (r : ℕ) : Entry :=
  c.order.getD r ⟨0, true, 0⟩

private theorem exists_eq_of_length_eight {α : Type*} {l : List α} (h : l.length = 8) :
    ∃ e0 e1 e2 e3 e4 e5 e6 e7, l = [e0, e1, e2, e3, e4, e5, e6, e7] := by
  match l, h with
  | [e0, e1, e2, e3, e4, e5, e6, e7], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩

/-- What the segment lemma needs from a checked cell at `μ/n` inside it. The eight entries
`ent r` lie in the order, consecutive levels increase strictly, every end `ε < 16` is the entry
or exit end of some entry, the entry and exit ends are below `16`, and the context pairs the exit
end of entry `r` with the entry end of entry `r + 1 mod 8`. -/
theorem Cell.ent_facts {c : Cell} (h : c.check = true) {μ n : ℤ} (hμ : c.Contains μ n) :
    (∀ r < 8, c.ent r ∈ c.order) ∧
      StrictMono (fun r : Fin 8 ↦ (c.ent r).level μ n) ∧
      (∀ ε < 16, ∃ r < 8, ε = (c.ent r).entryEnd ∨ ε = (c.ent r).exitEnd) ∧
      (∀ r < 8, (c.ent r).entryEnd < 16 ∧ (c.ent r).exitEnd < 16) ∧
      ∀ r < 8, ((c.ent r).exitEnd, (c.ent ((r + 1) % 8)).entryEnd) ∈ c.ctxPairs := by
  have hperm := Cell.idx_perm h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, hl⟩ :=
    exists_eq_of_length_eight (by simpa using hperm.length_eq)
  have hent : ∀ r < 8, c.ent r ∈ c.order := by
    intro r hr
    rw [Cell.ent, hl]
    interval_cases r <;> simp
  have hidx : ∀ r < 8, (c.ent r).idx < 8 := fun r hr ↦
    List.mem_range.1 (hperm.subset (List.mem_map_of_mem (hent r hr)))
  refine ⟨hent, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    apply Cell.level_lt_of_consecutive h hμ
    rw [hl]
    fin_cases i <;> simp [Cell.ent, hl]
  · intro ε hε
    have hi : ε / 2 ∈ c.order.map Entry.idx := hperm.mem_iff.2 (List.mem_range.2 (by omega))
    obtain ⟨r, hr, hr'⟩ : ∃ r < 8, (c.ent r).idx = ε / 2 := by
      rw [hl] at hi
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
      · exact ⟨0, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨1, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨2, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨3, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨4, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨5, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨6, by norm_num, by simp [Cell.ent, hl, hi]⟩
      · exact ⟨7, by norm_num, by simp [Cell.ent, hl, hi]⟩
    refine ⟨r, hr, ?_⟩
    unfold Entry.entryEnd Entry.exitEnd
    split_ifs <;> omega
  · intro r hr
    have := hidx r hr
    unfold Entry.entryEnd Entry.exitEnd
    split_ifs <;> omega
  · intro r hr
    rw [Cell.ctxPairs, hl]
    interval_cases r <;> simp [Cell.ent, hl]

/-- The level form at `θ = μ/n` is `coefA μ` mod `n`. -/
theorem natCast_mul_coefA (e : Entry) (μ n : ℕ) :
    ((μ : ℤ) : ZMod n) * (e.coefA : ZMod n) = ((e.level μ n : ℤ) : ZMod n) := by
  rw [Entry.level]
  push_cast
  rw [ZMod.natCast_self]
  ring

variable {m : ℕ} [NeZero m]

/-- The `ZMod.val` bridge at an entry end. If `λ.val = μ` and the level `ℓ` of `e` at `μ/n`
satisfies `0 < ℓ` and `2ℓ < n`, the scaled entry end `λ · coefA` sits at position `2ℓ`. -/
theorem zigPos_entry (lam : ZMod (2 * m - 1)) (e : Entry)
    (h0 : 0 < e.level lam.val ↑(2 * m - 1)) (h2 : 2 * e.level lam.val ↑(2 * m - 1) < ↑(2 * m - 1)) :
    zigPos m (some (lam * (e.coefA : ZMod (2 * m - 1)))) = 2 * e.level lam.val ↑(2 * m - 1) := by
  have hm := NeZero.pos m
  have hc : (↑(2 * m - 1) : ℤ) = 2 * m - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    ring
  rw [zigPos_some_of_eq (k := e.level lam.val ↑(2 * m - 1)) _ (by omega) (by omega), ite_eq_left h0]
  rw [← natCast_mul_coefA, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The `ZMod.val` bridge at an exit end: the scaled exit end `-λ · coefA` sits at position
`2ℓ + 1`. -/
theorem zigPos_exit (lam : ZMod (2 * m - 1)) (e : Entry)
    (h0 : 0 < e.level lam.val ↑(2 * m - 1)) (h2 : 2 * e.level lam.val ↑(2 * m - 1) < ↑(2 * m - 1)) :
    zigPos m (some (lam * ((-e.coefA : ℤ) : ZMod (2 * m - 1)))) =
      2 * e.level lam.val ↑(2 * m - 1) + 1 := by
  have hm := NeZero.pos m
  have hc : (↑(2 * m - 1) : ℤ) = 2 * m - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    ring
  rw [zigPos_some_of_eq (k := -e.level lam.val ↑(2 * m - 1)) _ (by omega) (by omega),
    ite_eq_right (by omega)]
  · ring
  rw [Int.cast_neg, mul_neg, Int.cast_neg, ← natCast_mul_coefA, Int.cast_natCast,
    ZMod.natCast_zmod_val]

end FactorCap

end Pairing
