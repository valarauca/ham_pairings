import Mathlib.Algebra.BigOperators.Field
import Pairing.RoundRobin
import Suppression.SizeBias
import Suppression.Prob

/-!
# The size-bias identity for the round-robin count (COD-183)

For a perfect matching `P` of `V_m`, `hamCount m P = X(P)` is the number of canonical factors
`F_t` for which `P ∪ F_t` is one cycle, and `A_t` is the event `Ham P F_t`. Put `n = 2m - 1`.

* `shift m b` : the translation `v ↦ v + b` of `V_m`, fixing `∞`. `shift_smul_factor` : it maps
  `F_t` to `F_{t + b}`, and `hamCount_shift_smul` : it preserves `X`.
* `card_ham_and_eq` : `#{P | A_t ∧ q (X P)}` does not depend on `t`, for any predicate `q`.
* `card_ham_and` : `n · #{P | A_0 ∧ q (X P)} = ∑_{P | q (X P)} X P`, by double counting the
  pairs `(P, t)` with `A_t`.
* `card_ham_and_eq_mul` (C) : `n · #{P | A_0 ∧ X P = k} = k · #{P | X P = k}`.
* `card_ham_and_le` : `n · #{P | A_0 ∧ X P ≤ j} = ∑_{k ≤ j} k · #{P | X P = k}`.
* `hamLaw m`, the law of `X` under the uniform perfect matching. `hamLaw_zero` :
  `P(X = 0) = Z_m / (2m - 1)!! = q_m`.
* `card_perfectMatching_pos` : `V_m` has a perfect matching.
* `unifWeight m`, the uniform weight on the perfect matchings of `V_m`. `isProb_unifWeight` : it is
  a probability weight (`Prob.lean`), and `prob_unifWeight` : `U(S) = |S| / (2m - 1)!!`.
* `hamLaw_eq_lawOf` : `hamLaw m` is the pushforward of `unifWeight m` along `X`, so
  `isLaw_hamLaw` (it is a law on `[0, n]`) is a special case of `ChainRule.isLaw_lawOf`.
* `ham_factor_one` : `F_1 ∪ F_0` is one cycle, so `exists_ham_factor_zero` : `A_0` is nonempty,
  and `exists_pos_hamLaw` : `P(X = k) > 0` for some `k ≥ 1`. These hold for every `m ≥ 1`.
* `partialMean_hamLaw` : `∑_{k ≤ j} k P(X = k) = n P(A_0 ∧ X ≤ j)`.
* `cond_hamLaw` : `P(X - 1 ≤ j | A_0) = (∑_{k ≤ j + 1} k P(X = k)) / μ`, the corrected formula
  of COD-183. So `ρ_j = P(X - 1 ≤ j | A_0) / P(X ≤ j)` depends on the law of `X` alone.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- The translation `v ↦ v + b` of `V_m`, fixing `∞`. -/
def shift (m : ℕ) [NeZero m] (b : ZMod (2 * m - 1)) : Equiv.Perm (Vertex m) :=
  Equiv.optionCongr (Equiv.addRight b)

/-- The translation fixes `∞`. -/
@[simp]
theorem shift_none (m : ℕ) [NeZero m] (b : ZMod (2 * m - 1)) : shift m b none = none :=
  rfl

/-- The translation sends `x` to `x + b`. -/
@[simp]
theorem shift_some (m : ℕ) [NeZero m] (b x : ZMod (2 * m - 1)) :
    shift m b (some x) = some (x + b) :=
  rfl

/-- The inverse translation fixes `∞`. -/
@[simp]
theorem shift_inv_none (m : ℕ) [NeZero m] (b : ZMod (2 * m - 1)) : (shift m b)⁻¹ none = none := by
  rw [Equiv.Perm.inv_eq_iff_eq, shift_none]

/-- The inverse translation sends `x` to `x - b`. -/
@[simp]
theorem shift_inv_some (m : ℕ) [NeZero m] (b x : ZMod (2 * m - 1)) :
    (shift m b)⁻¹ (some x) = some (x - b) := by
  rw [Equiv.Perm.inv_eq_iff_eq, shift_some, sub_add_cancel]

/-- The translation by `b` maps `F_t` to `F_{t + b}`. -/
theorem shift_smul_factor (m : ℕ) [NeZero m] (b t : ZMod (2 * m - 1)) :
    shift m b • factor m t = factor m (t + b) := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rcases v with _ | y
  · simp [factor]
  rcases eq_or_ne y (t + b) with rfl | hy
  · simp [factor]
  have h : y - b ≠ t := fun h ↦ hy (by rw [← h, sub_add_cancel])
  simp only [smul_mate, shift_inv_some, factor, factor_mate, mateFn_of_ne _ _ h,
    mateFn_of_ne _ _ hy, shift_some, Option.some_inj]
  ring

/-- `X(P) = #{t | Ham P F_t}`, the number of canonical factors that close one cycle with `P`. -/
def hamCount (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) : ℕ :=
  (Finset.univ.filter fun t ↦ Ham P (factor m t)).card

/-- `X(P) ≤ n`. -/
theorem hamCount_le (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) :
    hamCount m P ≤ 2 * m - 1 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, ZMod.card])

/-- Translations preserve `X`. -/
theorem hamCount_shift_smul (m : ℕ) [NeZero m] (b : ZMod (2 * m - 1))
    (P : PerfectMatching (Vertex m)) : hamCount m (shift m b • P) = hamCount m P := by
  refine Finset.card_equiv (Equiv.addRight (-b)) fun t ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
  rw [← ham_smul (shift m b) P, shift_smul_factor, neg_add_cancel_right]

/-- `#{P | A_t ∧ q (X P)}` does not depend on `t`. -/
theorem card_ham_and_eq (m : ℕ) [NeZero m] (q : ℕ → Prop) [DecidablePred q]
    (t : ZMod (2 * m - 1)) :
    (Finset.univ.filter fun P ↦ Ham P (factor m t) ∧ q (hamCount m P)).card =
      (Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ q (hamCount m P)).card := by
  refine Finset.card_equiv (MulAction.toPerm (shift m (-t))) fun P ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.toPerm_apply,
    hamCount_shift_smul]
  rw [← ham_smul (shift m (-t)) P (factor m t), shift_smul_factor, add_neg_cancel]

/-- Double counting of the pairs `(P, t)` with `A_t`,
`∑_t #{P | A_t ∧ q (X P)} = ∑_{P | q (X P)} X P`. -/
theorem sum_card_ham_and (m : ℕ) [NeZero m] (q : ℕ → Prop) [DecidablePred q] :
    ∑ t, (Finset.univ.filter fun P ↦ Ham P (factor m t) ∧ q (hamCount m P)).card =
      ∑ P ∈ Finset.univ.filter fun P ↦ q (hamCount m P), hamCount m P := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  by_cases h : q (hamCount m P)
  · simp only [h, and_true, ite_true]
    rw [hamCount, Finset.card_filter]
  · simp [h]

/-- `n · #{P | A_0 ∧ q (X P)} = ∑_{P | q (X P)} X P` for every predicate `q`. -/
theorem card_ham_and (m : ℕ) [NeZero m] (q : ℕ → Prop) [DecidablePred q] :
    (2 * m - 1) * (Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ q (hamCount m P)).card =
      ∑ P ∈ Finset.univ.filter fun P ↦ q (hamCount m P), hamCount m P := by
  rw [← sum_card_ham_and, Finset.sum_congr rfl fun t _ ↦ card_ham_and_eq m q t,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]

/-- (C) The size-bias identity, `n · #{P | A_0 ∧ X P = k} = k · #{P | X P = k}`. -/
theorem card_ham_and_eq_mul (m : ℕ) [NeZero m] (k : ℕ) :
    (2 * m - 1) * (Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ hamCount m P = k).card =
      k * (Finset.univ.filter fun P ↦ hamCount m P = k).card := by
  rw [card_ham_and m (· = k), Finset.sum_const_nat fun P hP ↦ (Finset.mem_filter.mp hP).2,
    mul_comm]

/-- `n · #{P | A_0 ∧ X P ≤ j} = ∑_{k ≤ j} k · #{P | X P = k}`. -/
theorem card_ham_and_le (m : ℕ) [NeZero m] (j : ℕ) :
    (2 * m - 1) * (Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ hamCount m P ≤ j).card =
      ∑ k ∈ Finset.range (j + 1), k * (Finset.univ.filter fun P ↦ hamCount m P = k).card := by
  rw [card_ham_and m (· ≤ j), ← Finset.sum_fiberwise_of_maps_to' (g := hamCount m)
    (t := Finset.range (j + 1)) (fun P hP ↦ Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hP).2)) fun k ↦ k]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm, Finset.filter_filter]
  congr 2
  exact Finset.filter_congr fun P _ ↦
    ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), h⟩⟩

/-- The law of `X` under the uniform perfect matching of `V_m`,
`P(X = k) = #{P | X P = k} / |PM(V_m)|`. -/
noncomputable def hamLaw (m : ℕ) [NeZero m] (k : ℕ) : ℝ :=
  (Finset.univ.filter fun P : PerfectMatching (Vertex m) ↦ hamCount m P = k).card /
    Fintype.card (PerfectMatching (Vertex m))

/-- There is a perfect matching of `V_m`. -/
theorem card_perfectMatching_pos (m : ℕ) [NeZero m] :
    0 < Fintype.card (PerfectMatching (Vertex m)) :=
  Fintype.card_pos_iff.mpr ⟨factor m 0⟩

/-- `|PM(V_m)| ≠ 0` in `ℝ`. -/
theorem cast_card_perfectMatching_ne_zero (m : ℕ) [NeZero m] :
    (Fintype.card (PerfectMatching (Vertex m)) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (card_perfectMatching_pos m).ne'

/-- The uniform weight on the perfect matchings of `V_m`, the law `U`. -/
noncomputable def unifWeight (m : ℕ) [NeZero m] (_ : PerfectMatching (Vertex m)) : ℝ :=
  1 / Fintype.card (PerfectMatching (Vertex m))

/-- The uniform law on the perfect matchings of `V_m` is a probability weight. -/
theorem isProb_unifWeight (m : ℕ) [NeZero m] : ChainRule.IsProb (unifWeight m) where
  nonneg _ := by
    unfold unifWeight
    positivity
  sum_eq_one := by
    simp [unifWeight, cast_card_perfectMatching_ne_zero m]

/-- `U(S) = |S| / (2m - 1)!!` under the uniform law. -/
theorem prob_unifWeight (m : ℕ) [NeZero m] (S : Set (PerfectMatching (Vertex m)))
    [DecidablePred (· ∈ S)] :
    ChainRule.prob (unifWeight m) S =
      (Finset.univ.filter (· ∈ S)).card / Fintype.card (PerfectMatching (Vertex m)) := by
  rw [ChainRule.prob, Finset.sum_congr rfl fun P _ ↦ Set.indicator_apply S (unifWeight m) P,
    ← Finset.sum_filter]
  simp only [unifWeight, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- `hamLaw m` is the law of `X` under the uniform weight. -/
theorem hamLaw_eq_lawOf (m : ℕ) [NeZero m] :
    hamLaw m = ChainRule.lawOf (unifWeight m) (hamCount m) := by
  funext k
  rw [ChainRule.lawOf, prob_unifWeight, hamLaw]
  rfl

/-- `F_1 ∪ F_0` is one cycle on `V_m`. Off `{0, -1}` the composite `F_1 F_0` is `x ↦ x + 2`, and
`2` generates `ℤ/(2m - 1)`. For `m = 1` the two factors agree and their doubled edge is the
cycle. -/
theorem ham_factor_one (m : ℕ) [NeZero m] : Ham (factor m 1) (factor m 0) := by
  let G := (factor m 1).toGraph ⊔ (factor m 0).toGraph
  have h1 : ∀ v, G.Reachable v (mateFn 1 v) :=
    fun v ↦ SimpleGraph.Adj.reachable (G := G) (Or.inl rfl)
  have h0 : ∀ v, G.Reachable v (mateFn 0 v) :=
    fun v ↦ SimpleGraph.Adj.reachable (G := G) (Or.inr rfl)
  have h2 : ∀ x : ZMod (2 * m - 1), G.Reachable (some x) (some (x + 2)) := by
    intro x
    rcases subsingleton_or_nontrivial (ZMod (2 * m - 1)) with hs | hs
    · rw [Subsingleton.elim (x + 2) x]
    rcases eq_or_ne x 0 with rfl | hx0
    · have h := h1 (some 0)
      rw [mateFn_of_ne 1 0 zero_ne_one] at h
      convert h using 2
      ring
    rcases eq_or_ne x (-1) with rfl | hx1
    · have h := h0 (some (-1))
      rw [mateFn_of_ne 0 (-1) (neg_ne_zero.mpr one_ne_zero)] at h
      convert h using 2
      ring
    have h := h0 (some x)
    rw [mateFn_of_ne 0 x hx0] at h
    have h' := h1 (some (2 * 0 - x))
    rw [mateFn_of_ne 1 _ fun h ↦ hx1 (by linear_combination -h)] at h'
    convert h.trans h' using 2
    ring
  have hk : ∀ k : ℕ, G.Reachable (some 0) (some (2 * k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      convert ih.trans (h2 _) using 2
      push_cast
      ring
  have hr : ∀ v, G.Reachable none v := by
    rintro (_ | y)
    · exact SimpleGraph.Reachable.refl _
    obtain ⟨u, hu⟩ := (RoundRobin.isUnit_two (modulus_odd m)).exists_right_inv
    convert (h0 none).trans (hk (u * y).val) using 2
    rw [ZMod.natCast_zmod_val, ← mul_assoc, hu, one_mul]
  exact (⟨fun v w ↦ (hr v).symm.trans (hr w)⟩ : G.Connected)

/-- `A_0` is nonempty for every `m ≥ 1`, since `F_1 ∪ F_0` is one cycle. -/
theorem exists_ham_factor_zero (m : ℕ) [NeZero m] : ∃ P, Ham P (factor m 0) :=
  ⟨factor m 1, ham_factor_one m⟩

/-- The law of `X` is a probability law on `[0, n]`. -/
theorem isLaw_hamLaw (m : ℕ) [NeZero m] : SizeBias.IsLaw (hamLaw m) (2 * m - 1) := by
  rw [hamLaw_eq_lawOf]
  exact ChainRule.isLaw_lawOf (isProb_unifWeight m) (hamCount_le m)

/-- `P(X = k) > 0` for some `k ≥ 1`, with `k = X(F_1)`. This is the hypothesis `hk` of the
tilted-law reductions for `p = hamLaw m`. -/
theorem exists_pos_hamLaw (m : ℕ) [NeZero m] : ∃ k, 0 < k ∧ 0 < hamLaw m k :=
  ⟨hamCount m (factor m 1), Finset.card_pos.mpr ⟨0, by simpa using ham_factor_one m⟩,
    div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨factor m 1, by simp⟩))
      (Nat.cast_pos.mpr (card_perfectMatching_pos m))⟩

/-- `P(X = 0) = Z_m / (2m - 1)!! = q_m`. -/
theorem hamLaw_zero (m : ℕ) [NeZero m] :
    hamLaw m 0 = (zeroCount m : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  rw [hamLaw, card_eq_doubleFactorial (card_vertex m), zeroCount, Fintype.card_subtype]
  congr 3
  exact Finset.filter_congr fun P _ ↦ by
    simp [hamCount, IsZeroState, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- `∑_{k ≤ j} k P(X = k) = n P(A_0 ∧ X ≤ j)`. -/
theorem partialMean_hamLaw (m : ℕ) [NeZero m] (j : ℕ) :
    SizeBias.partialMean (hamLaw m) j =
      (2 * m - 1 : ℕ) *
          ((Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ hamCount m P ≤ j).card : ℝ) /
        Fintype.card (PerfectMatching (Vertex m)) := by
  simp only [SizeBias.partialMean, hamLaw, mul_div_assoc', ← Finset.sum_div]
  congr 1
  exact_mod_cast (card_ham_and_le m j).symm

/-- The conditional law of `X` given `A_0`,
`P(X - 1 ≤ j | A_0) = (∑_{k ≤ j + 1} k P(X = k)) / μ` with `μ = E X`. -/
theorem cond_hamLaw (m : ℕ) [NeZero m] (j : ℕ) :
    ((Finset.univ.filter fun P ↦ Ham P (factor m 0) ∧ hamCount m P - 1 ≤ j).card : ℝ) /
        (Finset.univ.filter fun P ↦ Ham P (factor m 0)).card =
      SizeBias.partialMean (hamLaw m) (j + 1) / SizeBias.partialMean (hamLaw m) (2 * m - 1) := by
  rw [partialMean_hamLaw, partialMean_hamLaw,
    div_div_div_cancel_right₀ (cast_card_perfectMatching_ne_zero m),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (NeZero.ne _))]
  congr 3
  · exact Finset.filter_congr fun P _ ↦ and_congr_right' Nat.sub_le_iff_le_add
  · exact Finset.filter_congr fun P _ ↦ (and_iff_left (hamCount_le m P)).symm

end RoundRobin.Canonical

end Pairing
