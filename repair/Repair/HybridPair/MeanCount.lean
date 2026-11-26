import Repair.DensityGlue
import Repair.FactorCap.Scale

/-!
# The contracted mean count (ULZD Lemma 3, frontier identity I10)

`P` is a perfect matching of `V` and the boundary `A ⊆ V`, with `|A| = 2N`, is a union of edges of
`P`. For a factor `Q`, either `Q ∪ P'` closes a cycle off `A` (the factor is dead) or `Q` has the
context `κ_Q = contract P Q A hA` (the factor is live). The live set is `L(D)`.

* `card_ham_glue_of_not_hasClosedCycle` : a live factor is Hamiltonian with `X ∪ P'` for exactly
  `2^(N-1) (N-1)!` matchings `X` of `A`. This is the count of ULZD Lemma 3,
  `PerfectMatching.card_ham_eq`, read through `ham_glue_iff`.
* `card_ham_glue_of_hasClosedCycle` : a dead factor is Hamiltonian with none of them.
* `sum_card_ham_glue` : `∑_X #{t | Ham (X ∪ P') (F t)} = |L(D)| 2^(N-1) (N-1)!`, the mean
  identity `E_R X((T ∖ D) ∪ R) = |L(D)| p_N` in counting form.
* `RoundRobin.Canonical.sum_hamCount_glue`, `RoundRobin.Canonical.expect_hamCount_glue` : the
  same on `V_m` for the round-robin factors, with `p_N = 2^(N-1) (N-1)! / (2N-1)!!`.
* `RoundRobin.Canonical.ham_factor_factor_zero` : `F_t ∪ F_0` is one cycle for every unit `t`.
* `RoundRobin.Canonical.sum_hamCount_glue_factor_zero` (hybrid mean count) : for prime
  `n = 2m - 1` and a proper nonempty union `A` of edges of `F_0`, every `t ≠ 0` is live and
  `t = 0` is dead, so `E X = (n - 1) p_N`.

Source: `results/ulzd-longcycle-spike.md` (organize-archive dfef22c), Lemma 3 and the paragraph
"Mean count (Lemma 3 with Lemma P)".
-/

namespace Pairing

namespace PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- ULZD Lemma 3 for one live factor (`results/ulzd-longcycle-spike.md`). If `|A| = 2N`, `N ≥ 1`,
and `Q ∪ P'` closes no cycle off `A`, then exactly `2^(N-1) (N-1)!` matchings `X` of `A` make
`(X ∪ P') ∪ Q` one cycle. -/
theorem card_ham_glue_of_not_hasClosedCycle {N : ℕ} (hN : 0 < N) (P Q : PerfectMatching V)
    (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A) (hcard : A.card = 2 * N)
    (hC : ¬HasClosedCycle P Q A) :
    (univ.filter fun X : PerfectMatching A ↦ Ham (glue P A hA X) Q).card =
      2 ^ (N - 1) * (N - 1).factorial := by
  rw [← card_ham_eq hN (by rw [Fintype.card_coe, hcard]) (contract P Q A hA)]
  exact congrArg card (filter_congr fun X _ ↦ ham_glue_iff P Q A hA hC X)

/-- ULZD Lemma 3 for one dead factor (`results/ulzd-longcycle-spike.md`, Lemma 1). If `Q ∪ P'`
closes a cycle off a nonempty `A`, no matching `X` of `A` makes `(X ∪ P') ∪ Q` one cycle. -/
theorem card_ham_glue_of_hasClosedCycle (P Q : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) (hA0 : A.Nonempty) (hC : HasClosedCycle P Q A) :
    (univ.filter fun X : PerfectMatching A ↦ Ham (glue P A hA X) Q).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  exact fun X _ ↦ not_ham_glue P Q A hA hC hA0 X

open Classical in
/-- ULZD Lemma 3, the contracted mean identity in counting form
(`results/ulzd-longcycle-spike.md`). For a family `F` of matchings and a boundary `A` with
`|A| = 2N`, `N ≥ 1`, summing the number of Hamiltonian members of `F` over all completions
`X ∪ P'` gives `|L(D)| 2^(N-1) (N-1)!`, where `L(D)` is the set of live `t`. -/
theorem sum_card_ham_glue {ι : Type*} [Fintype ι] (F : ι → PerfectMatching V)
    (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A) {N : ℕ} (hN : 0 < N)
    (hcard : A.card = 2 * N) :
    ∑ X : PerfectMatching A, (univ.filter fun t ↦ Ham (glue P A hA X) (F t)).card =
      (univ.filter fun t ↦ ¬HasClosedCycle P (F t) A).card *
        (2 ^ (N - 1) * (N - 1).factorial) := by
  have hA0 : A.Nonempty := by
    rw [← card_pos, hcard]
    omega
  calc ∑ X : PerfectMatching A, (univ.filter fun t ↦ Ham (glue P A hA X) (F t)).card
      = ∑ t, (univ.filter fun X : PerfectMatching A ↦ Ham (glue P A hA X) (F t)).card := by
        simp only [card_filter]
        exact sum_comm
    _ = ∑ t, if HasClosedCycle P (F t) A then 0 else 2 ^ (N - 1) * (N - 1).factorial := by
        refine sum_congr rfl fun t _ ↦ ?_
        split_ifs with hC
        · exact card_ham_glue_of_hasClosedCycle P (F t) A hA hA0 hC
        · exact card_ham_glue_of_not_hasClosedCycle hN P (F t) A hA hcard hC
    _ = _ := by
        rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul]

omit [Fintype V] in
/-- A factor that is one cycle with `P` closes no cycle with `P'` off a nonempty boundary `A`
(`results/ulzd-longcycle-spike.md`, Lemma 1). -/
theorem not_hasClosedCycle_of_ham {P Q : PerfectMatching V} (h : Ham P Q)
    (A : Finset V) (hA0 : A.Nonempty) : ¬HasClosedCycle P Q A := by
  rintro ⟨C, ⟨v, hv⟩, hdisj, hP, hQ⟩
  obtain ⟨a, ha⟩ := hA0
  exact not_ham_of_closed P Q (C : Set V) hP hQ (u := v) (w := a) hv
    (Finset.disjoint_right.mp hdisj ha) h

omit [Fintype V] in
/-- `F_0 ∪ F_0'` closes the `2`-cycle of any `F_0`-edge off a proper boundary `A`
(`results/ulzd-longcycle-spike.md`, the factor `t = 0` is dead for a hybrid). -/
theorem hasClosedCycle_self (P : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) {v : V} (hv : v ∉ A) : HasClosedCycle P P A := by
  have hv' : P.mate v ∉ A := fun h ↦ hv (by simpa using hA _ h)
  refine ⟨{v, P.mate v}, ⟨v, mem_insert_self _ _⟩, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hv
    · rw [Finset.mem_singleton.mp hu]
      exact hv'
  all_goals
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hu, mate_mate]
      exact Finset.mem_insert_self _ _

end PerfectMatching

namespace RoundRobin.Canonical

open Finset PerfectMatching

variable {m : ℕ} [NeZero m]

open Classical in
/-- ULZD Lemma 3 on `V_m` (`results/ulzd-longcycle-spike.md`). For a boundary `A` of `P` with
`|A| = 2N`, `N ≥ 1`, `∑_X X(X ∪ P') = |L(D)| 2^(N-1) (N-1)!`, where `X(·)` is `hamCount` and
`L(D)` is the set of `t` for which `F_t ∪ P'` closes no cycle off `A`. -/
theorem sum_hamCount_glue (P : PerfectMatching (Vertex m)) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, P.mate v ∈ A) {N : ℕ} (hN : 0 < N) (hcard : A.card = 2 * N) :
    ∑ X : PerfectMatching A, hamCount m (glue P A hA X) =
      (univ.filter fun t ↦ ¬HasClosedCycle P (factor m t) A).card *
        (2 ^ (N - 1) * (N - 1).factorial) :=
  sum_card_ham_glue (factor m) P A hA hN hcard

open Classical in
/-- ULZD Lemma 3 on `V_m`, expectation form (`results/ulzd-longcycle-spike.md`):
`E_R X((T ∖ D) ∪ R) = |L(D)| p_N` with `p_N = 2^(N-1) (N-1)! / (2N-1)!!`, for `R` uniform on the
perfect matchings of the boundary `A`, `|A| = 2N`, `N ≥ 1`. -/
theorem expect_hamCount_glue (P : PerfectMatching (Vertex m)) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, P.mate v ∈ A) {N : ℕ} (hN : 0 < N) (hcard : A.card = 2 * N) :
    (∑ X : PerfectMatching A, (hamCount m (glue P A hA X) : ℝ)) /
        (Fintype.card (PerfectMatching A) : ℝ) =
      ((univ.filter fun t ↦ ¬HasClosedCycle P (factor m t) A).card : ℝ) *
        ((2 ^ (N - 1) * (N - 1).factorial : ℝ) / (Nat.doubleFactorial (2 * N - 1) : ℝ)) := by
  rw [card_eq_doubleFactorial (by rw [Fintype.card_coe, hcard]), ← Nat.cast_sum,
    sum_hamCount_glue P A hA hN hcard, mul_div_assoc]
  push_cast
  ring

/-- `F_t ∪ F_0` is one cycle for every unit `t`: the scaling by `t` maps `F_1 ∪ F_0` onto it.
This is the "if" half of the gcd law, used in `results/ulzd-longcycle-spike.md` ("at prime `n`
every `t ≠ 0` is live for `F_0 ∖ E`, since `F_0 ∪ F_t` is one cycle"). -/
theorem ham_factor_factor_zero (u : (ZMod (2 * m - 1))ˣ) :
    Ham (factor m u) (factor m 0) := by
  have h := (ham_smul (scale m u) (factor m 1) (factor m 0)).mpr (ham_factor_one m)
  rwa [scale_smul_factor, scale_smul_factor, mul_one, mul_zero] at h

open Classical in
/-- At prime `n = 2m - 1`, the live set of a proper nonempty union `A` of `F_0`-edges is
`{t ≠ 0}` (`results/ulzd-longcycle-spike.md`, "Mean count (Lemma 3 with Lemma P)"). -/
theorem filter_not_hasClosedCycle_factor_zero (hp : (2 * m - 1).Prime) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A) (hA0 : A.Nonempty) (hAu : A ≠ univ) :
    (univ.filter fun t ↦ ¬HasClosedCycle (factor m 0) (factor m t) A) = univ.erase 0 := by
  have := Fact.mk hp
  obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
    by_contra h
    push Not at h
    exact hAu (eq_univ_iff_forall.mpr h)
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
  constructor
  · rintro h rfl
    exact h (hasClosedCycle_self _ A hA hv)
  · intro ht
    refine not_hasClosedCycle_of_ham ?_ A hA0
    rw [ham_comm, show t = ((Units.mk0 t ht : (ZMod (2 * m - 1))ˣ) : ZMod (2 * m - 1)) from rfl]
    exact ham_factor_factor_zero _

/-- Hybrid mean count (`results/ulzd-longcycle-spike.md`, "Mean count (Lemma 3 with Lemma P)").
At prime `n = 2m - 1`, for a proper union `A` of `F_0`-edges with `|A| = 2N`, `N ≥ 1`,
`∑_R X((F_0 ∖ E) ∪ R) = (n - 1) 2^(N-1) (N-1)!` over the perfect matchings `R` of `A`. So
`E X = (n - 1) p_N`. -/
theorem sum_hamCount_glue_factor_zero (hp : (2 * m - 1).Prime) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A) (hAu : A ≠ univ) {N : ℕ} (hN : 0 < N)
    (hcard : A.card = 2 * N) :
    ∑ X : PerfectMatching A, hamCount m (glue (factor m 0) A hA X) =
      (2 * m - 2) * (2 ^ (N - 1) * (N - 1).factorial) := by
  classical
  have hA0 : A.Nonempty := by
    rw [← card_pos, hcard]
    omega
  rw [sum_hamCount_glue _ A hA hN hcard]
  congr 1
  convert congrArg card (filter_not_hasClosedCycle_factor_zero hp A hA hA0 hAu) using 1
  rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  omega

end RoundRobin.Canonical

end Pairing
