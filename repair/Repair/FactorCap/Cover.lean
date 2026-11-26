import Repair.FactorCap.Cells

/-!
# Covering by the 80 checked cells

`exists_checked_cell` is the arithmetic core of tasks T3 and T4 of the P9 plan
(`lean-scope-p9-p10.md`). For a prime `n > 16` and `0 < μ < n`, `μ/n` lies strictly inside one
of the 80 Farey cells, and that cell passes `Cell.check` (`cells_check_of_lemmas`, one kernel
check per cell in `Cells.lean`). `cell_facts` unpacks the checker's soundness at that `μ/n`.
-/

namespace Pairing

namespace FactorCap

/-- The cells walk from `0/1` to `1/1` through consecutive Farey neighbours. -/
theorem cells_walk : walkOK cells = true := by decide +kernel

/-- Every left denominator of a cell lies in `[1, 16]`. -/
theorem cells_denom : denomOK cells = true := by decide +kernel

/-- For a prime `n > 16` and `0 < μ < n`, `μ/n` lies strictly inside a cell that passes the
checker. -/
theorem exists_checked_cell {n μ : ℕ} (hn : n.Prime) (h16 : 16 < n) (hμ0 : 0 < μ)
    (hμn : μ < n) : ∃ c ∈ cells, c.check = true ∧ c.Contains μ n := by
  obtain ⟨c, hc, hcont⟩ := exists_contains_of_prime (c := cell0) (cs := cells.tail) cells_walk
    rfl rfl cells_denom hn h16 hμ0 hμn
  exact ⟨c, hc, List.all_eq_true.1 cells_check_of_lemmas c hc, hcont⟩

/-- The cell facts at `μ/n` for a prime `n > 16` and `0 < μ < n`: the level order with its
sides and residues, and a nonempty proper end set closed under `Q` and the context. -/
theorem cell_facts {n μ : ℕ} (hn : n.Prime) (h16 : 16 < n) (hμ0 : 0 < μ) (hμn : μ < n) :
    ∃ c ∈ cells, (c.order.map Entry.idx).Perm (List.range 8) ∧
      (∀ e ∈ c.order, 0 < e.level μ n ∧ 2 * e.level μ n < n ∧ e.a * μ / n = e.fl ∧
        e.a * μ % n = if e.plus then e.level μ n else n - e.level μ n) ∧
      (∀ ef ∈ c.order.zip c.order.tail, ef.1.level μ n < ef.2.level μ n) ∧
      c.z ≠ [] ∧ (∀ x ∈ c.z, x < 16) ∧ (∃ x < 16, x ∉ c.z) ∧
      ∀ xy ∈ c.ctxPairs ++ qPairs, (xy.1 ∈ c.z ↔ xy.2 ∈ c.z) := by
  obtain ⟨c, hc, hchk, hcont⟩ := exists_checked_cell hn h16 hμ0 hμn
  exact ⟨c, hc, Cell.check_sound hchk hcont⟩

end FactorCap

end Pairing
