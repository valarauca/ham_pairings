import Repair.Cover.Hybrid
import Repair.PairLevelOne

/-!
# The uniform tail law as a mixture of random hybrids (Corollary 2, counting form)

Source: `results/hybwin-contra.md` (organize-archive cd19551) §2, Corollary 2. The source states
it for probabilities. Here every statement is a counting identity or inequality over all
perfect matchings of `W`, with `|W| = 2M`, against a fixed perfect matching `T₀`. The number of
vertices that `T₀` and `T` pair alike is `shared2 T₀ T = 2J` (`Repair.PairLevelOne`), with
`J = |T ∩ T₀|`.

* `hybridEquiv` (Corollary 2(a)) : for a `T₀`-closed `S`, the matchings `T` with
  `defect T₀ T = S` (that is `T ∩ T₀ = T₀ ∖ E′` with `V(E′) = S`) correspond to the perfect
  matchings of `S` with no `T₀`-edge. So, given `T ∩ T₀`, `T` is uniform over the hybrids with that
  `E′`, the random hybrid law.
* Corollary 2(b), the mean: `∑_T 2J(T) = 2M (2M - 3)!!`, so `E[J] = M/(2M - 1)`. This is
  `sum_shared2` of `Repair.PairLevelOne`, reused here.
* `shared2_add_card_defect` : `2J + |defect T₀ T| = 2M`, so `shared2 T₀ T` is even.
* `card_le_two_mul_card_shared2_le_two` (Corollary 2(b), Markov) : at least half of all `T` have
  `J ≤ 1`.
* `RoundRobin.Canonical.card_filter_repair_le` : the P5 count for a set of tails. At most
  `Z_m (K + 1)(2m)^K` tails of a six-vertex gadget have a zero state within `K`.
* `RoundRobin.Canonical.half_mul_le_of_hybrid_rescue` (Corollary 2(c)) : if, for `j = 0` and
  `j = 1`, a fraction `η` of the tails with `J = j` (the random hybrid `H(M - j)`, read as
  `shared2 T₀ T = 2j`) have `ρ ≤ K`, then `(η/2)(2m - 7)!! ≤ Z_m (K + 1)(2m)^K`.
-/

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Corollary 2(a)** (`hybwin-contra.md` (cd19551) §2). For a `T₀`-closed set `S`, the
matchings with `defect T₀ T = S` are the hybrids `(T₀ ∖ E′) ∪ R′` with `V(E′) = S`, and these
correspond to the perfect matchings `R′` of `S` with no `T₀`-edge. -/
def hybridEquiv (T₀ : PerfectMatching W) (S : Finset W) (hS : ∀ v ∈ S, T₀.mate v ∈ S) :
    {R : PerfectMatching S // IsEdgeFree T₀ R} ≃ {T : PerfectMatching W // defect T₀ T = S} where
  toFun R := ⟨glue T₀ S hS R.1, defect_glue T₀ hS R.2⟩
  invFun T := ⟨restrict T.1 S (fun v hv ↦ by
      have hv' : v ∈ defect T₀ T.1 := by rw [T.2]; exact hv
      have h := mate_mem_defect T₀ T.1 hv'
      rwa [T.2] at h), fun a ↦ by
      have ha : (a : W) ∈ defect T₀ T.1 := by rw [T.2]; exact a.2
      exact mem_defect.mp ha⟩
  left_inv R := Subtype.ext (restrict_glue T₀ S hS R.1)
  right_inv T := Subtype.ext (glue_restrict_of_agree T₀ S hS fun v hv ↦ by
    rw [← T.2, mem_defect, not_not] at hv
    exact hv)

/-- `2J + |defect T₀ T| = |W|`, so `shared2 T₀ T` is even (`hybwin-contra.md` (cd19551) §2,
Corollary 2). -/
theorem shared2_add_card_defect (T₀ T : PerfectMatching W) :
    shared2 T₀ T + (defect T₀ T).card = Fintype.card W := by
  rw [shared2, defect, ← Finset.card_univ]
  simp only [eq_comm (a := T₀.mate _)]
  exact Finset.card_filter_add_card_filter_not _

/-- **Corollary 2(b), Markov** (`hybwin-contra.md` (cd19551) §2). At least half of all perfect
matchings `T` of `W` have `J = |T ∩ T₀| ≤ 1`. -/
theorem card_le_two_mul_card_shared2_le_two {M : ℕ} (hW : Fintype.card W = 2 * M) (hM : 2 ≤ M)
    (T₀ : PerfectMatching W) :
    Fintype.card (PerfectMatching W) ≤
      2 * (Finset.univ.filter fun T : PerfectMatching W ↦ shared2 T₀ T ≤ 2).card := by
  set D := Nat.doubleFactorial (2 * M - 3)
  set S := Finset.univ.filter fun T : PerfectMatching W ↦ ¬shared2 T₀ T ≤ 2
  have htot : Fintype.card (PerfectMatching W) = (2 * M - 1) * D := by
    rw [card_eq_doubleFactorial hW, show 2 * M - 1 = 2 * M - 3 + 2 by omega,
      Nat.doubleFactorial_add_two]
  have hsplit : (Finset.univ.filter fun T : PerfectMatching W ↦ shared2 T₀ T ≤ 2).card + S.card =
      (Finset.univ : Finset (PerfectMatching W)).card :=
    Finset.card_filter_add_card_filter_not _
  have h4 : ∀ T ∈ S, 4 ≤ shared2 T₀ T := by
    intro T hT
    have h1 := (Finset.mem_filter.mp hT).2
    have h2 := shared2_add_card_defect T₀ T
    have h3 := two_mul_card_edgesOutside T₀ T
    omega
  have hS : 4 * S.card ≤ 2 * M * D := by
    rw [← sum_shared2 hW hM T₀]
    calc 4 * S.card = ∑ _T ∈ S, 4 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ T ∈ S, shared2 T₀ T := Finset.sum_le_sum h4
      _ ≤ ∑ T, shared2 T₀ T := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hMD : M * D ≤ (2 * M - 1) * D := Nat.mul_le_mul_right _ (by omega)
  rw [Finset.card_univ] at hsplit
  have : 2 * M * D = 2 * (M * D) := by ring
  omega

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The P5 count for a set of tails (`hybwin-contra.md` (cd19551) §2, Corollary 2(c), "the
counting argument of P5 applied to these tails"). For a six-vertex gadget `G`, at most
`Z_m (K + 1)(2m)^K` tails have a zero state within `K`. -/
theorem card_filter_repair_le {G : Finset (Vertex m)} (hG : G.card = 6) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
      ∃ P : ZeroState m, tailDist P.1 T ≤ K).card ≤ zeroCount m * ((K + 1) * (2 * m) ^ K) := by
  classical
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  set 𝒯 := Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
    ∃ P : ZeroState m, tailDist P.1 T ≤ K
  have h := card_le_card_mul_of_cover (α := 𝒯) (β := ZeroState m)
    (fun T P ↦ tailDist P.1 T.1) K
    (∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1))
    (fun T ↦ (Finset.mem_filter.mp T.2).2) (fun P ↦ by
      refine le_trans ?_ (card_tailDist_le P.1 hU K)
      refine Finset.card_le_card_of_injOn (fun T ↦ T.1) (fun T hT ↦ ?_)
        (fun T _ T' _ h ↦ Subtype.ext h)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2⟩)
  rw [Fintype.card_coe] at h
  exact h.trans (Nat.mul_le_mul_left _
    (sum_choose_mul_doubleFactorial_le (Nat.sub_le m 3) (NeZero.pos m) K))

/-- **Corollary 2(c)** (`hybwin-contra.md` (cd19551) §2). Let `T₀` be any tail of a six-vertex
gadget and `0 ≤ η`. If, for `j = 0` and `j = 1`, at least a fraction `η` of the tails with
`|T ∩ T₀| = j` have a zero state within `K` (by Corollary 2(a) these are the random hybrids
`H(M - j)`), then `(η/2)(2m - 7)!! ≤ Z_m (K + 1)(2m)^K`. -/
theorem half_mul_le_of_hybrid_rescue {G : Finset (Vertex m)} (hG : G.card = 6) (hm : 5 ≤ m)
    (T₀ : PerfectMatching (Gᶜ : Finset (Vertex m))) {η : ℝ} (hη : 0 ≤ η) (K : ℕ)
    (hres : ∀ j ∈ ({0, 2} : Finset ℕ),
      η * ((Finset.univ.filter fun T ↦ shared2 T₀ T = j).card : ℝ) ≤
        ((Finset.univ.filter fun T ↦ shared2 T₀ T = j ∧
          ∃ P : ZeroState m, tailDist P.1 T ≤ K).card : ℝ)) :
    η / 2 * (Nat.doubleFactorial (2 * m - 7) : ℝ) ≤
      (zeroCount m * ((K + 1) * (2 * m) ^ K) : ℕ) := by
  classical
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  have hW : Fintype.card (Gᶜ : Finset (Vertex m)) = 2 * (m - 3) := by rw [Fintype.card_coe, hU]
  have hhalf := card_le_two_mul_card_shared2_le_two hW (by omega) T₀
  rw [card_tail hG] at hhalf
  set A := Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦ shared2 T₀ T ≤ 2
  set B := Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
    ∃ P : ZeroState m, tailDist P.1 T ≤ K
  set A0 := Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦ shared2 T₀ T = 0
  set A2 := Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦ shared2 T₀ T = 2
  have hodd : ∀ T, shared2 T₀ T ≠ 1 := by
    intro T h
    have h2 := shared2_add_card_defect T₀ T
    have h3 := two_mul_card_edgesOutside T₀ T
    rw [hW] at h2
    omega
  have hA : A = A0 ∪ A2 := by
    ext T
    simp only [A, A0, A2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    have := hodd T
    omega
  have hdisj : Disjoint A0 A2 := Finset.disjoint_filter.mpr fun T _ h0 h2 ↦ by omega
  have hB0 := hres 0 (by simp)
  have hB2 := hres 2 (by simp)
  have hsub : (Finset.univ.filter fun T ↦ shared2 T₀ T = 0 ∧ ∃ P : ZeroState m,
      tailDist P.1 T ≤ K) ∪ (Finset.univ.filter fun T ↦ shared2 T₀ T = 2 ∧ ∃ P : ZeroState m,
      tailDist P.1 T ≤ K) ⊆ B := by
    intro T hT
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT.elim (·.2) (·.2)⟩
  have hdisj' : Disjoint (Finset.univ.filter fun T ↦ shared2 T₀ T = 0 ∧ ∃ P : ZeroState m,
      tailDist P.1 T ≤ K) (Finset.univ.filter fun T ↦ shared2 T₀ T = 2 ∧ ∃ P : ZeroState m,
      tailDist P.1 T ≤ K) := Finset.disjoint_filter.mpr fun T _ h0 h2 ↦ by omega
  have hBcard := (Finset.card_le_card hsub).trans (card_filter_repair_le hG K)
  rw [Finset.card_union_of_disjoint hdisj'] at hBcard
  have hAcard : A.card = A0.card + A2.card := by rw [hA, Finset.card_union_of_disjoint hdisj]
  have hhalf' : (Nat.doubleFactorial (2 * m - 7) : ℝ) ≤ 2 * ((A0.card : ℝ) + A2.card) := by
    have : Nat.doubleFactorial (2 * m - 7) ≤ 2 * (A0.card + A2.card) := by
      rw [← hAcard]
      exact hhalf
    exact_mod_cast this
  calc η / 2 * (Nat.doubleFactorial (2 * m - 7) : ℝ)
      ≤ η / 2 * (2 * ((A0.card : ℝ) + A2.card)) := mul_le_mul_of_nonneg_left hhalf' (by positivity)
    _ = η * A0.card + η * A2.card := by ring
    _ ≤ _ := add_le_add hB0 hB2
    _ ≤ _ := by exact_mod_cast hBcard

end RoundRobin.Canonical

end Pairing
