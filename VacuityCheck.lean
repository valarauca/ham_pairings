import Suppression
import Repair
import Spin
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Satisfiability checks for the review (REVIEW.md, section 2)

Each `example` builds a concrete instance of the hypotheses of a conditional endpoint, so that
the endpoint is not vacuous in Lean. Run it like `AxiomCheck.lean`, with
`lake env lean VacuityCheck.lean`. It is not part of any library.
-/

namespace VacuityCheck.RepairA

open Pairing PerfectMatching RoundRobin.Canonical

-- X1 P9 cap at n = 17
example : True := by
  have := FactorCap.factorTail_cap (m := 9) (by decide) (by norm_num)
  trivial

-- X1b P9 cap at the composite n = 121 = 11²
example : True := by
  have := FactorCap.factorTail_cap_of_coprime (m := 61) (by decide) (by norm_num)
  trivial

-- X2 FamilyRepairBound of the true family is RepairBound
example (m : ℕ) [NeZero m] (G : Finset (Vertex m)) (K : ℕ) :
    FamilyRepairBound (hamEvent m) G K ↔ RepairBound m G K :=
  ⟨fun h T ↦ let ⟨P, hP, hd⟩ := h T; ⟨⟨P, hP⟩, hd⟩, fun h T ↦ let ⟨P, hd⟩ := h T; ⟨P.1, P.2, hd⟩⟩

-- X3 not_ham_self is not_ham_of_mate_eq
example {V : Type*} (X : PerfectMatching V) {u w : V} (hwu : w ≠ u) (hwX : w ≠ X.mate u) :
    ¬Ham X X :=
  not_ham_of_mate_eq (R := X) (P := X) rfl hwu hwX

-- X4 gcd law "if" half without primality
example (m : ℕ) [NeZero m] {s t : ZMod (2 * m - 1)} (hu : IsUnit (s - t)) :
    Ham (factor m s) (factor m t) := by
  have h1 := affine_smul_factor m hu.unit t 1
  have h0 := affine_smul_factor m hu.unit t 0
  rw [IsUnit.unit_spec, mul_one, sub_add_cancel] at h1
  rw [mul_zero, zero_add] at h0
  rw [← h1, ← h0, ham_smul]
  exact ham_factor_one m

-- X5 not_farey_hit from coprimality only
example {n μ p q : ℕ} (hcop : Nat.Coprime n μ) (h16 : 16 < n) (hq0 : 0 < q) (hq : q ≤ 16) :
    p * n ≠ q * μ := by
  intro h
  have hdvd : n ∣ q * μ := ⟨p, by rw [← h, Nat.mul_comm]⟩
  have := Nat.le_of_dvd hq0 (hcop.dvd_of_dvd_mul_right hdvd)
  omega

-- X6 repair_bound hypotheses at m = 6
example : True := by
  have := repair_bound (m := 6) le_rfl (RoundRobin.Covering.Witness.gadget 6) (by decide)
    (tailEdges RoundRobin.Covering.Witness.baseTail) (isPartialMatching_tailEdges _)
    (by rw [uncovered_tailEdges, compl_compl])
  trivial

-- X9 Proposition NC hypotheses at m = 9
example (H : PerfectMatching ((FactorCap.gadget 9)ᶜ : Finset (Vertex 9))) : True := by
  have := exists_nearHybrid (m := 9) (by decide) (by norm_num)
    (repairBound (m := 9) (by norm_num) (card_gadget (m := 9) (by norm_num))) H
  trivial

end VacuityCheck.RepairA

namespace VacuityCheck.Suppression

open Pairing SizeBias Tilt in
example : True := by
  set p : ℕ → ℝ := fun k ↦ if k ≤ 1 then 1 / 2 else 0 with hp_def
  have hp : IsLaw p 1 :=
    { nonneg := fun k ↦ by simp only [hp_def]; split_ifs <;> norm_num
      eq_zero := fun k hk ↦ by simp only [hp_def]; split_ifs <;> first | omega | rfl
      sum_eq_one := by simp only [hp_def]; norm_num [Finset.sum_range_succ] }
  have hD : ∀ w ∈ Set.Ioc (0 : ℝ) 1, pairDeficit p 1 w ≤ 1 / 2 := by
    intro w _
    simp only [hp_def]
    norm_num [pairDeficit, tiltPair, tiltMean, tiltSum, genFun, partialMean,
      Finset.sum_range_succ]
  have h := exp_neg_mul_log_le_of_pairDeficit_le hp (c := 1 / 2) (by norm_num) (by norm_num) hD
  have hk : ∃ k, 0 < k ∧ 0 < p k := ⟨1, one_pos, by simp only [hp_def]; norm_num⟩
  have hΔ : ∀ w ∈ Set.Ioc (0 : ℝ) 1, (1 / 2 : ℝ) ≤ tiltMean p 1 w → fano p 1 w ≤ 1 / 2 :=
    fun w hw _ ↦ fano_le_of_pairDeficit_le hp hk (by norm_num) hD hw
  have h4 := exp_neg_div_le_of_fano_le hp (δ := 1 / 2) (by norm_num) hΔ
  have hρ : ∀ j ≤ 1, partialMean p 1 * cdf p j ≤ partialMean p (j + 1) := by
    intro j hj
    interval_cases j <;>
      simp only [hp_def, partialMean, cdf, Finset.sum_range_succ, Finset.sum_range_zero] <;>
      norm_num
  have h5 := upper_reduction_sqrt_of_le_add_two hp rfl (ε := 1) one_pos (J := 1)
    (by simp only [hp_def, partialMean, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) hρ
  trivial

open Pairing ChainRule in
example : True := by
  let P : Bool → ℝ := fun _ ↦ 1 / 2
  let A : Unit → Set Bool := fun _ ↦ {true}
  have hP : IsProb P := ⟨fun _ ↦ by norm_num [P], by norm_num [P, Fintype.sum_bool]⟩
  have hA : ∀ (T : Finset Unit) (t : Unit), t ∉ T → condProb P A T t ≤ 1 / 2 := by
    intro T t ht
    have hT : T = ∅ :=
      Finset.eq_empty_of_forall_notMem fun u hu ↦ ht (Subsingleton.elim u t ▸ hu)
    subst hT
    norm_num [condProb, prob, avoid, A, P, Fintype.sum_bool, Set.indicator_apply]
  have hB : ∀ T : Finset Unit, 0 + 2 ≤ Tᶜ.card →
      ∑ s ∈ Tᶜ, ∑ t ∈ Tᶜ.erase s, |condCov P A T s t| ≤
        2 * √(0 : ℝ) * condMean P A T + 4 * 0 := by
    intro T hT
    have h1 := Finset.card_le_univ Tᶜ
    rw [Fintype.card_unit] at h1
    omega
  have h := div_le_neg_log_prob_avoid (A := A) hP (φ := 1 / 2) (J := 0) (K := 0)
    (by norm_num) (by norm_num) le_rfl hA hB
  trivial

open Pairing RoundRobin.Canonical in
example {m : ℕ} [NeZero m] (hm : 6 ≤ m) {G : Finset (Vertex m)} (hG : G.card = 6) :
    Nat.doubleFactorial (2 * m - 7) ≤
      zeroCount m * ballCount (m - 3) (min (m - 3) (8 * ⌈Real.sqrt (2 * m - 1)⌉₊)) 0 :=
  doubleFactorial_le_zeroCount_mul_ballCount hG (repairBound hm hG)

end VacuityCheck.Suppression

namespace VacuityCheck.Hybrid

open Pairing HybridConditional CumulantTail ChainRule SizeBias

/-- Point-mass witness for `HJIStar`: every pattern space is `Unit`, `X ≡ N`, `B = ∅`. -/
theorem hjiStar_pointMass (N d K k : ℕ) (δ H : ℝ) (hδ : 0 ≤ δ) (hH : 0 ≤ H) :
    HJIStar (Ω := fun _ _ _ ↦ Unit) (fun _ _ _ _ ↦ (1 : ℝ)) (fun _ _ _ _ ↦ N)
      (fun _ _ _ ↦ (∅ : Set Unit)) N d K k δ H := by
  have hc : ∀ j, condLaw (fun _ : Unit ↦ (1 : ℝ)) ∅ (fun _ ↦ N) j = if j = N then 1 else 0 := by
    intro j
    by_cases h : j = N
    · subst h; simp [condLaw, lawOf, prob]
    · simp [condLaw, lawOf, prob, h, Ne.symm h]
  have hμ : partialMean (condLaw (fun _ : Unit ↦ (1 : ℝ)) ∅ (fun _ ↦ N)) N = N := by
    rw [partialMean, Finset.sum_eq_single N (fun j _ hj ↦ by simp [hc, hj])
      (fun h ↦ absurd (Finset.self_mem_range_succ N) h)]
    simp [hc]
  have hm : centralMoment (condLaw (fun _ : Unit ↦ (1 : ℝ)) ∅ (fun _ ↦ N)) N (2 * k) =
      ((0 : ℝ) ^ 2) ^ k := by
    rw [centralMoment, hμ, Finset.sum_eq_single N (fun j _ hj ↦ by simp [hc, hj])
      (fun h ↦ absurd (Finset.self_mem_range_succ N) h), hc]
    simp [pow_mul]
  refine ⟨fun _ _ _ _ ↦ ?_, fun _ _ _ _ ↦ ?_⟩
  · simp only [prob, Set.indicator_empty, Finset.sum_const_zero]
    exact div_nonneg (mul_nonneg Real.pi_pos.le hδ) (by positivity)
  · rw [hm, hμ, zero_pow two_ne_zero]
    exact pow_le_pow_left₀ le_rfl (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num) (Real.exp_pos 1).le) hH) (Nat.cast_nonneg k)) (Nat.cast_nonneg N)) k

/-- The inner implication of `hybrid_theorem1` has satisfiable hypotheses at every `m ≥ m₀`. -/
example {ε δ η θ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hθ : 0 < θ)
    (hθ4 : θ < 1 / 4) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      (0 : ℝ) ≤ Real.pi * δ / (80 * Real.sqrt (defectSize ε m)) +
        (m : ℝ) ^ (-(η * radius ε δ m / 2)) := by
  obtain ⟨m₀, h⟩ := hybrid_theorem1 hε hδ hδ1 hη hθ hθ4
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have hmean : ∀ a b (F : Finset (Fin (3 + b))), a + b ≤ radius ε δ m →
      Real.pi * δ * ((2 * m - 2 : ℕ) : ℝ) / (40 * Real.sqrt (defectSize ε m)) ≤
        ∑ ω : Unit, (fun _ _ _ _ ↦ (1 : ℝ)) a b F ω *
          ((fun _ _ _ _ ↦ 2 * m - 2) a b F ω : ℕ) := by
    intro a b F _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
    rcases Nat.eq_zero_or_pos (defectSize ε m) with hd | hd
    · simp [hd]
    · have hs : 1 ≤ Real.sqrt (defectSize ε m) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
      have hN : (0 : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : Real.pi * δ ≤ 40 * Real.sqrt (defectSize ε m) := by
        nlinarith [Real.pi_le_four, Real.pi_pos]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h1 hN]
  refine (h m hm).2 (fun _ _ _ ↦ Unit) (fun _ _ _ _ ↦ 1) (fun _ _ _ _ ↦ 2 * m - 2)
    (fun _ _ _ ↦ ∅) 0 0 (fun _ _ _ ↦ ⟨fun _ ↦ zero_le_one, by simp⟩) (fun _ _ _ _ ↦ le_rfl)
    (hjiStar_pointMass _ _ _ _ _ _ hδ.le (Real.rpow_nonneg (Nat.cast_nonneg m) _)) hmean
    (div_nonneg (mul_nonneg Real.pi_pos.le hδ.le) (by positivity)) ?_
  rw [zero_add]
  refine Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) ?_
  unfold lawOf prob
  exact Finset.sum_nonneg fun _ _ ↦ Set.indicator_nonneg
    (fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) _

end VacuityCheck.Hybrid

namespace VacuityCheck.Spin

open Pairing PerfectMatching TensorProduct

-- E1 cod105 at n = 2 over ℂ
example := cod105 ℂ 2 (by norm_num)

-- E2 reduction_basicSpin hypotheses are jointly satisfiable
example : True := by
  obtain ⟨N, ρ, hN, hs, b, R, hR, k, instF, instA, ψ, -⟩ := cod105 ℂ 2 (by norm_num)
  have := hN
  let := instF
  let := instA
  obtain ⟨e, he, hg⟩ := reduction_basicSpin (by norm_num : 1 ≤ 2) ρ b R hR k ψ hs
  trivial

-- E4 exists_lattice with a proper valuation subring
example : True := by
  obtain ⟨V, hV⟩ := exists_valuationSubring_two (K := ℂ)
  obtain ⟨b, hb⟩ := exists_lattice V 3 (Algebra.lmul ℂ (CliffordAlgebra (schurQ ℂ 3)))
  trivial

-- E5 finrank_le_of_jSystem, p = 0, K = Y = ZMod 5, I = 2
theorem two_mul_two_zmod_five : (2 : ZMod 5) * 2 = -1 := by decide

theorem two_ne_zero_zmod_five : (2 : ZMod 5) ≠ 0 := by decide

example : Module.finrank (ZMod 5) (ZMod 5) ≤ 2 ^ 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact finrank_le_of_jSystem (K := ZMod 5) (Y := ZMod 5) (p := 0) (J := fun _ ↦ 1) (I := 2)
    ⟨fun _ ↦ mul_one 1, fun i j hij ↦
      absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij⟩
    two_mul_two_zmod_five two_ne_zero_zmod_five
    (fun N _ ↦ Ideal.eq_bot_or_top N)

-- E6 exists_injective_intertwiner with M = W (Fin 4), k = ZMod 2
example : True := by
  have h : 1 ≤ 2 := by norm_num
  have := nontrivial_W 2 h
  obtain ⟨φ, hinj, hφ⟩ :=
    exists_injective_intertwiner 2 (ZMod 2) h (cliffordRep (base 2 h)).toRingHom
  trivial

-- E7 exists_intertwining_equiv with the same data
example : True := by
  have h : 1 ≤ 2 := by norm_num
  obtain ⟨e, he⟩ := exists_intertwining_equiv 2 (ZMod 2) h
    (cliffordRep (base 2 h)).toRingHom (finrank_W_eq 2 h)
  trivial

-- E8 minpoly over GaloisField 2 2, where x^2+x+1 splits
example : minpoly (GaloisField 2 2)
      (ρK 2 (GaloisField 2 2) (Equiv.swap (0 : Fin (2 * 2)) 1 * Equiv.swap 0 2)) =
    Polynomial.X ^ 2 + Polynomial.X + 1 :=
  minpoly_ρK_threeCycle 2 (GaloisField 2 2) (by norm_num)
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))

-- E9 finrank_W_eq sanity at n = 3
example : Module.finrank (ZMod 2) (W (Fin (2 * 3))) = 4 :=
  (finrank_W_eq 3 (by norm_num)).trans (by norm_num)

end VacuityCheck.Spin

namespace VacuityCheck.Ladder

open Pairing PerfectMatching RoundRobin.Canonical

-- L1 finrank_rrSpan_of_five_le at the composite n = 15
example : Module.finrank F₂ (rrSpan 8) = 15 :=
  finrank_rrSpan_of_five_le (m := 8) (by norm_num)

-- L2 the ladder hypotheses of ker_fpCoeff_le_of_ladder hold for the P* translates at n = 15
example : 14 ≤ Module.finrank F₂ (rrSpan 8) :=
  card_sub_one_le_finrank_fpSpan_of_ladder (n := 15) (by norm_num) _
    (ham_shift_pStar_ladder (m := 8) (by norm_num))

-- L3 rank_pairingMatrix_of_ladder for the P* translates at n = 15
example : (pairingMatrix (fun s : ZMod (2 * 8 - 1) ↦ shift 8 (s - ((8 : ℕ) - 1)) • pStar 8)
    (factor 8)).rank = 14 :=
  rank_pairingMatrix_of_ladder (n := 15) (by norm_num) _
    (ham_shift_pStar_ladder (m := 8) (by norm_num))

-- L4 the biorthogonal hypothesis holds for the Q translates at n = 15
example : Module.finrank F₂ (rrSpan 8) = 15 := by
  have h := finrank_fpSpan_eq_card_of_biorthogonal (F := factor 8)
    (fun s : ZMod (2 * 8 - 1) ↦ shift 8 (s - ((8 : ℕ) + 2)) • oneQ 8 (by norm_num)) (Equiv.refl _)
    (ham_shift_oneQ_biorthogonal (m := 8) (by norm_num))
  rwa [ZMod.card] at h

-- L5 the triangular hypotheses hold on Fin 15 for the Q translates
example : Module.finrank F₂ (fpSpan fun t : Fin 15 ↦ factor 8 ((t : ℕ) : ZMod (2 * 8 - 1))) =
    15 := by
  have hQ := ham_shift_oneQ_biorthogonal (m := 8) (by norm_num)
  have hinj : ∀ s t : Fin 15,
      ((t : ℕ) : ZMod (2 * 8 - 1)) = ((s : ℕ) : ZMod (2 * 8 - 1)) → t = s := fun s t h ↦
    Fin.ext (natCast_injOn (m := 8) (by have := t.isLt; omega) (by have := s.isLt; omega) h)
  have h := finrank_fpSpan_eq_card_of_triangular
    (F := fun t : Fin 15 ↦ factor 8 ((t : ℕ) : ZMod (2 * 8 - 1)))
    (fun s ↦ shift 8 (((s : ℕ) : ZMod (2 * 8 - 1)) - ((8 : ℕ) + 2)) • oneQ 8 (by norm_num))
    (fun s ↦ (hQ _ _).mpr rfl) (fun s t hts h' ↦ hts.ne (hinj s t ((hQ _ _).mp h')))
  rwa [Fintype.card_fin] at h

-- L6 the P* and Q Hamiltonian sets at m = 5, the smallest m covered by Proposition Q
example : hamCount 5 (oneQ 5 le_rfl) = 1 := hamCount_oneQ le_rfl

end VacuityCheck.Ladder

namespace VacuityCheck.LowerBound

open Pairing PerfectMatching RoundRobin.Canonical

-- B1 sameCycle_of_arcs for the translation `y ↦ y + 1` of ℤ/5 with one jump point
example : (Equiv.addRight (1 : ZMod 5)).SameCycle 0 3 :=
  LowerBound.sameCycle_of_arcs (n := 5) (r := 0) _ (fun v ↦ (v : ZMod 5))
    (fun v k ↦ by simp [show (5 : ZMod 5) = 0 from rfl]) (fun y ↦ ⟨y.val, by simp⟩)
    (fun v w h ↦ (ZMod.intCast_eq_intCast_iff_dvd_sub w v 5).mp h.symm) ![0]
    (fun a b h ↦ absurd h (by rw [Fin.lt_def]; omega)) (by simp) id (fun v _ ↦ by simp)
    (fun i ↦ by simp) (fun j ↦ ⟨0, Fin.ext (by omega)⟩) 0 3

-- B2 coverGoal_of_involution for the gadget matching {1, 2}, {3, 4}, {5, 6}
example : LowerBound.CoverGoal 0 ![1, 0, 3, 2, 5, 4] :=
  LowerBound.coverGoal_of_involution 0 (by decide) (by decide)

-- B3 exists_ham_of_agree at n = 11 with P = F_{s0}, s0 = 9
example : ∃ t, Ham (RoundRobin.factor (n := 11) ⟨5, rfl⟩ 9) (RoundRobin.factor ⟨5, rfl⟩ t) :=
  LowerBound.exists_ham_of_agree ⟨5, rfl⟩ le_rfl (by decide) fun _ _ ↦ rfl

-- B4 one_le_tailDist_factorTail at m = 6, where a zero state exists
example : ∃ P : ZeroState 6, 1 ≤ tailDist P.1 (FactorCap.factorTail 6 (by norm_num)) :=
  let ⟨P⟩ := nonempty_zeroState (m := 6) le_rfl
  ⟨P, one_le_tailDist_factorTail le_rfl P⟩

-- B5 not_repairBound_zero at m = 6 and at the composite n = 15
example : ¬RepairBound 6 (FactorCap.gadget 6) 0 := not_repairBound_zero le_rfl
example : ¬RepairBound 8 (FactorCap.gadget 8) 0 := not_repairBound_zero (by norm_num)

end VacuityCheck.LowerBound
