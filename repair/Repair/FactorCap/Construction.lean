import Repair.FactorCap.Bridge

/-!
# The zero state `P_q` (P9, task T6)

Work in the coordinate `x = 2v - 7`, where the factor `F_{7/2}` of the default gadget becomes
`F_0 : x ↔ -x, ∞ ↔ 0`. The archive construction removes the eight edges `{-x, x}`, `1 ≤ x ≤ 8`,
of `F_0` and rematches their ends by

  `Q = {-8, -7}, {-6, -5}, {-4, -3}, {-2, -1}, {1, 8}, {2, 3}, {4, 5}, {6, 7}`.

`capInt` is this rematching on integer labels, extended by `k ↦ -k` off `±1, …, ±8`, and
`capMatching m` is `P_q = (F_0 ∖ D) ∪ Q` on `V_m`, read through least absolute residues, for
`m ≥ 9` (so `n = 2m - 1 ≥ 17` and the sixteen ends are distinct).

* `capMatching_endVtx` : `P_q` maps each end `ε` to its `Q`-partner, an end `ε'` with
  `(ε, ε')` or `(ε', ε)` in `qPairs`.
* `capMatching_of_ne_endVtx` : off the sixteen ends `P_q` agrees with `F_0`.
* `isZeroState_capMatching_of_coprime` : for `n = 2m - 1 ≥ 17` coprime to `105`, `P_q ∪ F_u`
  is never one cycle. For a unit `u` (`not_ham_capMatching`) the scaling by `λ = (2u)⁻¹` sends
  `F_0` to itself and `F_u` to `F_{1/2}`, the cell containing `λ.val / n` gives the level order
  of the scaled ends and a proper end set `Z` closed under `Q` and the context, and
  `not_ham_of_segments` turns `Z` into a closed union of zig-zag segments. For a non-unit `u`
  (`not_ham_capMatching_of_not_isUnit`) put `g = gcd(u, n) > 1`. Every prime factor of `g` is at
  least `11`, so `∞` and the multiples of `g` form a proper set that avoids the sixteen ends and
  is closed under `P_q` and `F_u`. `isZeroState_capMatching` is the case of prime `n`.

Source: `results/cod-186-archive-cap-check.md` (the construction of `P_q`, the 80-cell check
and the gcd ≥ 9 argument) and `results/lean-scope-p9-p10.md` §1, steps 1 to 6.
-/

namespace Pairing

namespace FactorCap

open RoundRobin hiding factor
open RoundRobin.Canonical PerfectMatching

/-- The rematching `Q` of the labels `±1, …, ±8`, extended by `k ↦ -k` off them. On `[-8, 8]` it
is the table `-8 ↔ -7, -6 ↔ -5, -4 ↔ -3, -2 ↔ -1, 0 ↔ 0, 1 ↔ 8, 2 ↔ 3, 4 ↔ 5, 6 ↔ 7`. -/
def capInt (k : ℤ) : ℤ :=
  if -8 ≤ k ∧ k ≤ 8 then
    [-7, -8, -5, -6, -3, -4, -1, -2, 0, 8, 3, 2, 5, 4, 7, 6, 1].getD (k + 8).toNat 0
  else -k

/-- Off `[-8, 8]`, `capInt` is `k ↦ -k`. -/
theorem capInt_of_not_mem {k : ℤ} (h : ¬(-8 ≤ k ∧ k ≤ 8)) : capInt k = -k :=
  ite_eq_right h

/-- `capInt` is an involution. -/
theorem capInt_capInt (k : ℤ) : capInt (capInt k) = k := by
  by_cases h : -8 ≤ k ∧ k ≤ 8
  · obtain ⟨h1, h2⟩ := h
    interval_cases k <;> decide
  · rw [capInt_of_not_mem h, capInt_of_not_mem (by omega), neg_neg]

/-- `capInt` fixes `0` and nothing else. -/
theorem capInt_eq_self_iff (k : ℤ) : capInt k = k ↔ k = 0 := by
  by_cases h : -8 ≤ k ∧ k ≤ 8
  · obtain ⟨h1, h2⟩ := h
    interval_cases k <;> decide
  · rw [capInt_of_not_mem h]
    omega

/-- `capInt k = 0` only for `k = 0`. -/
theorem capInt_eq_zero_iff (k : ℤ) : capInt k = 0 ↔ k = 0 := by
  by_cases h : -8 ≤ k ∧ k ≤ 8
  · obtain ⟨h1, h2⟩ := h
    interval_cases k <;> decide
  · rw [capInt_of_not_mem h]
    omega

/-- `capInt` keeps `-N < 2k < N` for `N ≥ 17`. -/
theorem capInt_bounds {N k : ℤ} (hN : 17 ≤ N) (h1 : -N < 2 * k) (h2 : 2 * k < N) :
    -N < 2 * capInt k ∧ 2 * capInt k < N := by
  by_cases h : -8 ≤ k ∧ k ≤ 8
  · have hk : -8 ≤ capInt k ∧ capInt k ≤ 8 := by
      obtain ⟨h1, h2⟩ := h
      interval_cases k <;> decide
    omega
  · rw [capInt_of_not_mem h]
    omega

/-- Off the sixteen end labels `capInt` is `k ↦ -k`. -/
theorem capInt_eq_neg_or (k : ℤ) : capInt k = -k ∨ ∃ ε < 16, endInt ε = k := by
  by_cases h : -8 ≤ k ∧ k ≤ 8
  · obtain ⟨h1, h2⟩ := h
    interval_cases k <;> first | (left; decide) | (right; decide)
  · exact Or.inl (capInt_of_not_mem h)

/-- The end labels are nonzero and lie in `[-8, 8]`. -/
theorem endInt_bounds : ∀ ε < 16, endInt ε ≠ 0 ∧ -8 ≤ endInt ε ∧ endInt ε ≤ 8 := by
  decide

/-- `capInt` is `Q` on the end labels. -/
theorem capInt_endInt : ∀ ε < 16, ∃ ε' < 16,
    capInt (endInt ε) = endInt ε' ∧ ((ε, ε') ∈ qPairs ∨ (ε', ε) ∈ qPairs) := by
  decide

/-- End `ε` as a vertex of `V_m`, in the coordinate `x = 2v - 7`. -/
def endVtx (m : ℕ) (ε : ℕ) : Vertex m :=
  some ((endInt ε : ℤ) : ZMod (2 * m - 1))

/-- The partner of a vertex in `P_q`, in the coordinate `x = 2v - 7`. -/
def capFn (m : ℕ) : Vertex m → Vertex m
  | none => some 0
  | some x => if x = 0 then none else some ((capInt x.valMinAbs : ℤ) : ZMod (2 * m - 1))

variable {m : ℕ} [NeZero m]

/-- For `m ≥ 9`, `capInt` of a least absolute residue is again a least absolute residue. -/
theorem valMinAbs_capInt (hm : 9 ≤ m) (x : ZMod (2 * m - 1)) :
    ((capInt x.valMinAbs : ℤ) : ZMod (2 * m - 1)).valMinAbs = capInt x.valMinAbs := by
  have hb := valMinAbs_bounds x
  have h := capInt_bounds (N := 2 * m - 1) (k := x.valMinAbs) (by omega) (by omega) (by omega)
  exact valMinAbs_eq_of_eq rfl (by omega) (by omega)

/-- The partner map of `P_q` is an involution for `m ≥ 9`. -/
theorem capFn_involutive (hm : 9 ≤ m) : Function.Involutive (capFn m) := by
  rintro (_ | x)
  · simp [capFn]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capFn]
  have hk : x.valMinAbs ≠ 0 := by rwa [Ne, ZMod.valMinAbs_eq_zero]
  have hy : ((capInt x.valMinAbs : ℤ) : ZMod (2 * m - 1)) ≠ 0 := by
    rw [Ne, ← ZMod.valMinAbs_eq_zero, valMinAbs_capInt hm, capInt_eq_zero_iff]
    exact hk
  simp only [capFn, hx, hy, ite_false, valMinAbs_capInt hm, capInt_capInt, ZMod.coe_valMinAbs]

/-- The partner map of `P_q` has no fixed point for `m ≥ 9`. -/
theorem capFn_ne (hm : 9 ≤ m) (v : Vertex m) : capFn m v ≠ v := by
  rcases v with _ | x
  · simp [capFn]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capFn]
  simp only [capFn, hx, ite_false, ne_eq, Option.some.injEq]
  intro h
  have h' := congrArg ZMod.valMinAbs h
  rw [valMinAbs_capInt hm, capInt_eq_self_iff, ZMod.valMinAbs_eq_zero] at h'
  exact hx h'

/-- `P_q = (F_0 ∖ D) ∪ Q` in the coordinate `x = 2v - 7`, a perfect matching of `V_m` for
`m ≥ 9`. -/
def capMatching (m : ℕ) [NeZero m] (hm : 9 ≤ m) : PerfectMatching (Vertex m) where
  mate := Function.Involutive.toPerm _ (capFn_involutive hm)
  mate_mate := capFn_involutive hm
  mate_ne := capFn_ne hm

/-- The partner map of `P_q`. -/
@[simp]
theorem capMatching_mate (hm : 9 ≤ m) (v : Vertex m) : (capMatching m hm).mate v = capFn m v :=
  rfl

/-- `P_q` maps end `ε` to its `Q`-partner `ε'`. -/
theorem capMatching_endVtx (hm : 9 ≤ m) {ε : ℕ} (hε : ε < 16) : ∃ ε' < 16,
    (capMatching m hm).mate (endVtx m ε) = endVtx m ε' ∧
      ((ε, ε') ∈ qPairs ∨ (ε', ε) ∈ qPairs) := by
  obtain ⟨ε', hε', hq, hpair⟩ := capInt_endInt ε hε
  obtain ⟨h0, h1, h2⟩ := endInt_bounds ε hε
  have hv : ((endInt ε : ℤ) : ZMod (2 * m - 1)).valMinAbs = endInt ε :=
    valMinAbs_eq_of_eq rfl (by omega) (by omega)
  have hne : ((endInt ε : ℤ) : ZMod (2 * m - 1)) ≠ 0 := by
    rw [Ne, ← ZMod.valMinAbs_eq_zero, hv]
    exact h0
  refine ⟨ε', hε', ?_, hpair⟩
  simp only [capMatching_mate, endVtx, capFn, hne, ite_false, hv, hq]

/-- Off the sixteen ends `P_q` agrees with `F_0`. -/
theorem capMatching_of_ne_endVtx (hm : 9 ≤ m) {v : Vertex m}
    (hv : ∀ ε < 16, v ≠ endVtx m ε) : (capMatching m hm).mate v = (factor m 0).mate v := by
  rcases v with _ | x
  · simp [capFn, factor]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capFn, factor]
  rcases capInt_eq_neg_or x.valMinAbs with h | ⟨ε, hε, h⟩
  · simp only [capMatching_mate, capFn, hx, ite_false, h, Int.cast_neg, ZMod.coe_valMinAbs]
    simp only [factor, factor_mate, mateFn_of_ne _ _ hx, Option.some.injEq]
    ring
  · exact absurd (by rw [endVtx, h, ZMod.coe_valMinAbs]) (hv ε hε)

/-- `P_q` blocks `F_0`, since the edge `∞0` lies in both and closes a `2`-cycle (step 1 of
`lean-scope-p9-p10.md` §1). -/
theorem not_ham_capMatching_zero (hm : 9 ≤ m) : ¬Ham (capMatching m hm) (factor m 0) := by
  have h1 : (1 : ZMod (2 * m - 1)) ≠ 0 := fun h ↦ absurd
    (natCast_injOn (m := m) (x := 1) (y := 0) (by omega) (by omega) (by simpa using h))
    (by norm_num)
  refine not_ham_of_closed _ _ {none, some 0} ?_ ?_ (u := none) (w := some 1) (by simp) ?_
  · rintro v (rfl | rfl) <;> simp [capFn]
  · rintro v (rfl | rfl) <;> simp [factor]
  · simp [h1]

/-- `P_q` blocks `F_u` for every unit `u`, for every `n = 2m - 1 ≥ 17`. With `λ = (2u)⁻¹` the
scaled positions `zigPos (λ v)` put `F_u` on the zig-zag as `F_{1/2}` (`scale_mate_factor`), the
cell containing `λ.val / n` orders the levels of the sixteen scaled ends, and its end set `Z`
selects a proper union of segments closed under `P_q` and `F_u` (steps 2 to 6 of
`lean-scope-p9-p10.md` §1). Since `λ` is a unit, `λ.val` is coprime to `n`, which is all that the
covering by the 80 cells needs. -/
theorem not_ham_capMatching (hm : 9 ≤ m) {u : ZMod (2 * m - 1)} (hu : IsUnit u) :
    ¬Ham (capMatching m hm) (factor m u) := by
  have h2 : IsUnit (2 : ZMod (2 * m - 1)) := isUnit_two (modulus_odd m)
  obtain ⟨a, hau⟩ : ∃ a : (ZMod (2 * m - 1))ˣ, (a : ZMod (2 * m - 1)) * u = m :=
    ⟨(h2.mul hu).unit⁻¹, h2.mul_left_cancel (by
      rw [two_mul_natCast_self, ← (h2.mul hu).val_inv_mul]
      ring)⟩
  obtain ⟨c, -, hchk, hcont⟩ := exists_checked_cell (ZMod.val_coe_unit_coprime a).symm
    (by omega) (ZMod.val_lt (a : ZMod (2 * m - 1)))
  generalize hlam : (a : ZMod (2 * m - 1)) = lam at hau hchk hcont
  obtain ⟨hent, hmono, hcov, hlt16, hctx⟩ := Cell.ent_facts hchk hcont
  obtain ⟨hz0, hz16, ⟨εo, hεo, hεoz⟩, hzcl⟩ := Cell.z_sound hchk
  have hN : ((2 * m - 1 : ℕ) : ℤ) = 2 * m - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    ring
  set L : Fin 8 → ℤ := fun r ↦ (c.ent r).level lam.val ↑(2 * m - 1) with hL
  have hbd : ∀ r < 8, 0 < (c.ent r).level lam.val ↑(2 * m - 1) ∧
      2 * (c.ent r).level lam.val ↑(2 * m - 1) < ↑(2 * m - 1) :=
    fun r hr ↦ Cell.level_bounds hchk hcont (hent r hr)
  have hbdL : ∀ r : Fin 8, 0 ≤ L r ∧ 2 * L r < 2 * m - 1 := fun r ↦ by
    have := hbd r r.2
    simp only [hL]
    omega
  set pos : Vertex m → ℤ := fun v ↦ zigPos m (scale m a v) with hpos
  have hposEntry : ∀ r (hr : r < 8), pos (endVtx m (c.ent r).entryEnd) = 2 * L ⟨r, hr⟩ := by
    intro r hr
    simp only [hpos, endVtx, scale_some, hlam, endInt_entryEnd]
    exact zigPos_entry lam _ (hbd r hr).1 (hbd r hr).2
  have hposExit : ∀ r (hr : r < 8), pos (endVtx m (c.ent r).exitEnd) = 2 * L ⟨r, hr⟩ + 1 := by
    intro r hr
    simp only [hpos, endVtx, scale_some, hlam, endInt_exitEnd]
    exact zigPos_exit lam _ (hbd r hr).1 (hbd r hr).2
  have hinj : ∀ v w, pos v = pos w → v = w := fun v w h ↦
    (scale m a).injective (zigPos_injective h)
  set S : ℕ → Prop := fun k ↦ (c.ent ((k + 7) % 8)).exitEnd ∈ c.z with hS
  have hkey : ∀ ε < 16, (S (zigCount L (pos (endVtx m ε)) % 8) ↔ ε ∈ c.z) := by
    intro ε hε
    obtain ⟨r, hr, rfl | rfl⟩ := hcov ε hε
    · rw [hposEntry r hr, zigCount_entry hmono ⟨r, hr⟩]
      have hq := hctx ((r + 7) % 8) (by omega)
      rw [show ((r + 7) % 8 + 1) % 8 = r by omega] at hq
      simp only [hS, show (r % 8 + 7) % 8 = (r + 7) % 8 by omega]
      exact hzcl _ (List.mem_append_left _ hq)
    · rw [hposExit r hr, zigCount_exit hmono ⟨r, hr⟩]
      simp only [hS, show ((r + 1) % 8 + 7) % 8 = r by omega]
  have hclose : ∀ ε < 16, ε ∈ c.z →
      S (zigCount L (pos ((capMatching m hm).mate (endVtx m ε))) % 8) := by
    intro ε hε hεz
    obtain ⟨ε', hε', hmate, hpair⟩ := capMatching_endVtx hm hε
    rw [hmate, hkey ε' hε']
    rcases hpair with hq | hq
    · exact (hzcl _ (List.mem_append_right _ hq)).1 hεz
    · exact (hzcl _ (List.mem_append_right _ hq)).2 hεz
  obtain ⟨ε1, hε1⟩ := List.exists_mem_of_ne_nil c.z hz0
  refine not_ham_of_segments (capMatching m hm) (factor m u) pos L m (fun r ↦ (hbdL r).1)
    (fun r ↦ (hbdL r).2) ?_ ?_ S ?_ (u := endVtx m ε1) (w := endVtx m εo)
    ((hkey ε1 (hz16 ε1 hε1)).2 hε1) fun h ↦ hεoz ((hkey εo hεo).1 h)
  · intro v
    simp only [hpos]
    rw [scale_mate_factor, hlam, hau]
    exact zigPos_factor_half (by omega) _
  · intro v hv
    have hne : ∀ ε < 16, v ≠ endVtx m ε := by
      rintro ε hε rfl
      obtain ⟨r, hr, rfl | rfl⟩ := hcov ε hε
      · exact (hv ⟨r, hr⟩).1 (hposEntry r hr).symm
      · exact (hv ⟨r, hr⟩).2 (hposExit r hr).symm
    rw [capMatching_of_ne_endVtx hm hne]
    simp only [hpos]
    rw [scale_mate_factor, mul_zero]
    exact zigPos_factor_zero _
  · rintro v ⟨r, hr | hr⟩ hSv
    · obtain rfl : v = endVtx m (c.ent r).entryEnd :=
        hinj _ _ (by rw [hposEntry r r.2]; exact hr.symm)
      have hε := (hlt16 r r.2).1
      exact hclose _ hε ((hkey _ hε).1 hSv)
    · obtain rfl : v = endVtx m (c.ent r).exitEnd :=
        hinj _ _ (by rw [hposExit r r.2]; exact hr.symm)
      have hε := (hlt16 r r.2).2
      exact hclose _ hε ((hkey _ hε).1 hSv)

/-- If `n = 2m - 1` is coprime to `105` and `g ≠ 1` divides `n`, no end label `±1, …, ±8` is a
multiple of `g`. A divisor `g ≤ 8` of `n` other than `1` would be even or divisible by `3`, `5`
or `7`. -/
theorem not_dvd_endInt (hcop : Nat.Coprime (2 * m - 1) 105) {g : ℕ} (hg : g ∣ 2 * m - 1)
    (hg1 : g ≠ 1) {ε : ℕ} (hε : ε < 16) : ¬(g : ℤ) ∣ endInt ε := by
  intro h
  obtain ⟨h0, h1, h2⟩ := endInt_bounds ε hε
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by have := NeZero.pos m; omega)
  have hle : (g : ℤ) ≤ 8 :=
    (Int.le_of_dvd (abs_pos.2 h0) ((dvd_abs _ _).2 h)).trans (abs_le.2 ⟨h1, h2⟩)
  have hodd : Odd g := Odd.of_dvd_nat (modulus_odd m) hg
  have hc : Nat.Coprime g 105 := Nat.Coprime.coprime_dvd_left hg hcop
  have hg8 : g ≤ 8 := by exact_mod_cast hle
  interval_cases g
  all_goals first | exact hg1 rfl | exact absurd hodd (by decide) | exact absurd hc (by decide)

/-- `P_q` blocks `F_u` for every non-unit `u`, including `u = 0`, when `n = 2m - 1 ≥ 17` is
coprime to `105`. Put `g = gcd(u, n)`, so `g ≠ 1`. No end is a multiple of `g`
(`not_dvd_endInt`), so `P_q` agrees with `F_0` on the multiples of `g`. The set of `∞` and the
multiples of `g` is then closed under `P_q` and `F_u`, and it misses `1`. This is the gcd ≥ 9 case
of `cod-186-archive-cap-check.md`: the component of `∞` meets no vertex of `D`. -/
theorem not_ham_capMatching_of_not_isUnit (hcop : Nat.Coprime (2 * m - 1) 105) (hm : 9 ≤ m)
    {u : ZMod (2 * m - 1)} (hu : ¬IsUnit u) : ¬Ham (capMatching m hm) (factor m u) := by
  have hgn : Nat.gcd u.val (2 * m - 1) ∣ 2 * m - 1 := Nat.gcd_dvd_right _ _
  have hg1 : Nat.gcd u.val (2 * m - 1) ≠ 1 := fun h ↦ hu (by
    rw [← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]
    exact h)
  set g := Nat.gcd u.val (2 * m - 1) with hg
  set π := ZMod.castHom hgn (ZMod g) with hπ
  have hπu : π u = 0 := by
    rw [← ZMod.natCast_zmod_val u, map_natCast, CharP.cast_eq_zero_iff (ZMod g) g]
    exact Nat.gcd_dvd_left _ _
  set B : Set (Vertex m) := {v | ∀ x, v = some x → π x = 0} with hB_def
  have hB : ∀ x, some x ∈ B ↔ π x = 0 := fun x ↦
    ⟨fun h ↦ h x rfl, fun h y hy ↦ Option.some_inj.1 hy ▸ h⟩
  have hB0 : none ∈ B := fun _ h ↦ (Option.some_ne_none _ h.symm).elim
  refine not_ham_of_closed _ _ B ?_ ?_ (u := none) (w := some 1) hB0 ?_
  · rintro (_ | x) hx
    · rw [capMatching_mate]
      exact (hB 0).2 (map_zero π)
    have hx' := (hB x).1 hx
    have hne : ∀ ε < 16, some x ≠ endVtx m ε := by
      rintro ε hε h
      rw [endVtx, Option.some_inj] at h
      rw [h, map_intCast, CharP.intCast_eq_zero_iff (ZMod g) g] at hx'
      exact not_dvd_endInt hcop hgn hg1 hε hx'
    rw [capMatching_of_ne_endVtx hm hne, factor, factor_mate]
    by_cases h0 : x = 0
    · rw [h0, mateFn_self]
      exact hB0
    · rw [mateFn_of_ne _ _ h0]
      exact (hB _).2 (by simp [hx'])
  · rintro (_ | x) hx
    · rw [factor, factor_mate, mateFn_none]
      exact (hB u).2 hπu
    have hx' := (hB x).1 hx
    rw [factor, factor_mate]
    by_cases hxu : x = u
    · rw [hxu, mateFn_self]
      exact hB0
    · rw [mateFn_of_ne _ _ hxu]
      exact (hB _).2 (by simp [hx', hπu])
  · intro h
    have h1 : ((1 : ℕ) : ZMod g) = 0 := by
      rw [Nat.cast_one, ← map_one π]
      exact (hB 1).1 h
    exact hg1 (Nat.dvd_one.1 ((CharP.cast_eq_zero_iff (ZMod g) g 1).1 h1))

/-- P9 in the coordinate `x = 2v - 7`. For `n = 2m - 1 ≥ 17` coprime to `105`, `P_q` is a zero
state: no `P_q ∪ F_u` is one cycle. Units `u` are handled by the 80 cells
(`not_ham_capMatching`) and the other `u` by the gcd argument
(`not_ham_capMatching_of_not_isUnit`). This is the zero-state half of claim C1 of
`cod-186-archive-cap-check.md` beyond prime `n`. -/
theorem isZeroState_capMatching_of_coprime (hcop : Nat.Coprime (2 * m - 1) 105) (hm : 9 ≤ m) :
    IsZeroState (factor m) (capMatching m hm) := fun u ↦
  if hu : IsUnit u then not_ham_capMatching hm hu
  else not_ham_capMatching_of_not_isUnit hcop hm hu

/-- A prime `n ≥ 17` is coprime to `105 = 3 · 5 · 7`. -/
theorem coprime_105_of_prime {n : ℕ} (hp : n.Prime) (hn : 17 ≤ n) : Nat.Coprime n 105 := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ ?_
  rw [show 105 = 3 * 5 * 7 by norm_num] at h
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)

/-- P9 in the coordinate `x = 2v - 7`. For prime `n = 2m - 1 ≥ 17`, `P_q` is a zero state:
no `P_q ∪ F_u` is one cycle. This is the zero-state half of claim C1 of
`cod-186-archive-cap-check.md`. It is `isZeroState_capMatching_of_coprime` at a prime. -/
theorem isZeroState_capMatching (hp : (2 * m - 1).Prime) (hm : 9 ≤ m) :
    IsZeroState (factor m) (capMatching m hm) :=
  isZeroState_capMatching_of_coprime (coprime_105_of_prime hp (by omega)) hm

end FactorCap

end Pairing
