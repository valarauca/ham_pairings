import Repair.Insertion
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

/-!
# The combinatorial steps of Theorem 3 (the fixed-`e` limit)

Theorem 3 of the joint-incoherence spike says that for fixed `e` and `k`, averaging over the
defect set `E` sends `R̄_k` to `G_k(e) = E_R[(g(R)/p_e)^k]` at rate `n^(-1/(2e²))`. This file
formalizes the counting and inequality steps of its proof. The equidistribution step (2)–(3),
the Erdős–Turán–Koksma bound `TV(ρ_E, U(Ham B)) ≤ C'_e H^(-1/e)` for `H`-generic `E`, is not
formalized.

* `pow_le_descFactorial_add`, `sum_pow_le_sum_descFactorial_add` : step (1),
  `x^k ≤ (x)_k + C(k, 2) x^(k-1)`, so `E X^k` and `E (X)_k` differ by at most
  `C(k, 2) E X^(k-1)`.
* `card_relation_le`, `card_not_generic_le` : step (4). A linear relation with a unit
  coefficient pins one coordinate, so at most `(N)_(e-1)` of the `(N)_e` ordered defect tuples
  satisfy it, and at most `(2H + 1)^e (N)_(e-1)` are not `H`-generic.
* `abs_pow_sub_pow_le_of_mem`, `abs_sum_pow_sub_le` : step (5), `|a^k - b^k| ≤ k M^(k-1) |a - b|`
  on `[0, M]`, averaged over `R`.
* `sum_abs_sum_le` : step (5), `E_R |ρ(S_R) - U(S_R)| ≤ 2 p TV(ρ, U)`. Every matching has the
  same number `2^(e-1) (e-1)!` of Hamiltonian partners (`PerfectMatching.card_ham_eq` in
  `Repair.DensityGlue`), so the double count applies with `d = p_e (2e-1)!!`.

Source: `results/hybrid-joint-incoherence.md` (organize-archive 4f82c7d), Theorem 3.
-/

namespace Pairing

open Finset

section Moments

/-- Step (1) of Theorem 3: `x^k ≤ (x)_k + C(k, 2) x^(k-1)`
(`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem pow_le_descFactorial_add (x : ℕ) :
    ∀ k : ℕ, x ^ k ≤ x.descFactorial k + k.choose 2 * x ^ (k - 1)
  | 0 => by simp
  | k + 1 => by
    have ih := pow_le_descFactorial_add x k
    have hd := Nat.descFactorial_le_pow x k
    have hsplit : x * x.descFactorial k ≤ x.descFactorial (k + 1) + k * x ^ k := by
      rw [Nat.descFactorial_succ]
      rcases le_or_gt k x with hkx | hkx
      · calc x * x.descFactorial k = (x - k) * x.descFactorial k + k * x.descFactorial k := by
              rw [← add_mul, Nat.sub_add_cancel hkx]
          _ ≤ (x - k) * x.descFactorial k + k * x ^ k := by gcongr
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkx]
        simp
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel] at ih ⊢
      calc x ^ (k + 1 + 1) = x * x ^ (k + 1) := by ring
        _ ≤ x * (x.descFactorial (k + 1) + (k + 1).choose 2 * x ^ k) := by gcongr
        _ = x * x.descFactorial (k + 1) + (k + 1).choose 2 * x ^ (k + 1) := by ring
        _ ≤ x.descFactorial (k + 1 + 1) + (k + 1) * x ^ (k + 1) +
              (k + 1).choose 2 * x ^ (k + 1) := by gcongr
        _ = x.descFactorial (k + 1 + 1) + (k + 1 + 1).choose 2 * x ^ (k + 1) := by
              rw [hc]
              ring

/-- Step (1) of Theorem 3, averaged: for nonnegative weights `w` and a count `X`,
`E X^k ≤ E (X)_k + C(k, 2) E X^(k-1)` and `E (X)_k ≤ E X^k`
(`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem sum_pow_le_sum_descFactorial_add {Ω : Type*} (s : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (X : Ω → ℕ) (k : ℕ) :
    ∑ ω ∈ s, w ω * ((X ω).descFactorial k : ℝ) ≤ ∑ ω ∈ s, w ω * ((X ω : ℝ) ^ k) ∧
      ∑ ω ∈ s, w ω * ((X ω : ℝ) ^ k) ≤ ∑ ω ∈ s, w ω * ((X ω).descFactorial k : ℝ) +
        (k.choose 2 : ℝ) * ∑ ω ∈ s, w ω * ((X ω : ℝ) ^ (k - 1)) := by
  constructor
  · refine Finset.sum_le_sum fun ω hω ↦ mul_le_mul_of_nonneg_left ?_ (hw ω hω)
    exact_mod_cast Nat.descFactorial_le_pow (X ω) k
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω hω ↦ ?_
    have h := pow_le_descFactorial_add (X ω) k
    have h' : ((X ω : ℝ) ^ k) ≤
        ((X ω).descFactorial k : ℝ) + (k.choose 2 : ℝ) * (X ω : ℝ) ^ (k - 1) := by
      exact_mod_cast h
    nlinarith [hw ω hω]

end Moments

section Lipschitz

/-- Step (5) of Theorem 3: `|a^k - b^k| ≤ k M^(k-1) |a - b|` for `a, b ∈ [0, M]`
(`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem abs_pow_sub_pow_le_of_mem {a b M : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hb : 0 ≤ b)
    (hbM : b ≤ M) (k : ℕ) : |a ^ k - b ^ k| ≤ k * M ^ (k - 1) * |a - b| := by
  have h := abs_pow_sub_pow_le a b k
  have hmax : max |a| |b| ≤ M := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    exact max_le haM hbM
  have hp : max |a| |b| ^ (k - 1) ≤ M ^ (k - 1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hmax _
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := h
    _ ≤ |a - b| * k * M ^ (k - 1) := by gcongr
    _ = k * M ^ (k - 1) * |a - b| := by ring

/-- Step (5) of Theorem 3, averaged over `R`: for weights `w ≥ 0` and `a_R, b_R ∈ [0, M]`,
`|E a^k - E b^k| ≤ k M^(k-1) E |a - b|` (`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem abs_sum_pow_sub_le {Ω : Type*} (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω)
    (a b : Ω → ℝ) {M : ℝ} (ha : ∀ ω ∈ s, 0 ≤ a ω ∧ a ω ≤ M) (hb : ∀ ω ∈ s, 0 ≤ b ω ∧ b ω ≤ M)
    (k : ℕ) :
    |∑ ω ∈ s, w ω * a ω ^ k - ∑ ω ∈ s, w ω * b ω ^ k| ≤
      k * M ^ (k - 1) * ∑ ω ∈ s, w ω * |a ω - b ω| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω hω ↦ ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw ω hω)]
  have h := abs_pow_sub_pow_le_of_mem (ha ω hω).1 (ha ω hω).2 (hb ω hω).1 (hb ω hω).2 k
  calc w ω * |a ω ^ k - b ω ^ k| ≤ w ω * (k * M ^ (k - 1) * |a ω - b ω|) :=
        mul_le_mul_of_nonneg_left h (hw ω hω)
    _ = k * M ^ (k - 1) * (w ω * |a ω - b ω|) := by ring

end Lipschitz

section Generic

variable {n : ℕ} [Fact n.Prime]

/-- Step (4) of Theorem 3: a linear relation `∑ c_a x_a ≡ 0 (mod n)` with a unit coefficient
`c_b` pins `x_b`, so at most `(N)_e` of the `(N)_(e+1)` ordered tuples of distinct labels from
`S` satisfy it (`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem card_relation_le {e : ℕ} (S : Finset (ZMod n)) (c : Fin (e + 1) → ZMod n)
    (b : Fin (e + 1)) (hb : c b ≠ 0) :
    Fintype.card {x : Fin (e + 1) ↪ S // ∑ a, c a * (x a : ZMod n) = 0} ≤
      S.card.descFactorial e := by
  classical
  let r : {x : Fin (e + 1) ↪ S // ∑ a, c a * (x a : ZMod n) = 0} →
      ({a : Fin (e + 1) // a ≠ b} ↪ S) :=
    fun x ↦ (Function.Embedding.subtype _).trans x.1
  have hr : Function.Injective r := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hoff : ∀ a, a ≠ b → x a = y a := fun a ha ↦ DFunLike.congr_fun hxy ⟨a, ha⟩
    have hb' : x b = y b := by
      have hsum : ∑ a, c a * (x a : ZMod n) = ∑ a, c a * (y a : ZMod n) := hx.trans hy.symm
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at hsum
      have hrest : ∑ a ∈ univ.erase b, c a * (x a : ZMod n) =
          ∑ a ∈ univ.erase b, c a * (y a : ZMod n) :=
        Finset.sum_congr rfl fun a ha ↦ by rw [hoff a (Finset.ne_of_mem_erase ha)]
      rw [hrest, add_left_inj] at hsum
      exact Subtype.ext (mul_left_cancel₀ hb hsum)
    apply Subtype.ext
    apply Function.Embedding.ext
    intro a
    by_cases ha : a = b
    · rw [ha, hb']
    · exact hoff a ha
  have h := Fintype.card_le_of_injective r hr
  rw [Fintype.card_embedding_eq, Fintype.card_coe] at h
  have hc : Fintype.card {a : Fin (e + 1) // a ≠ b} = e := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    rfl
  rwa [hc] at h

/-- `x` is `H`-generic when no nonzero integer vector `c` with `|c|_∞ ≤ H` has
`∑ c_a x_a ≡ 0 (mod n)`. The box is symmetric, so the sign choices of the source are absorbed
(`results/hybrid-joint-incoherence.md`, Theorem 3, step (3)). -/
def IsGeneric {e : ℕ} (H : ℕ) (x : Fin e → ZMod n) : Prop :=
  ∀ c : Fin e → ℤ, c ≠ 0 → (∀ a, |c a| ≤ H) → ∑ a, (c a : ZMod n) * x a ≠ 0

open Classical in
/-- Step (4) of Theorem 3: for `H < n`, at most `(2H + 1)^(e+1) (N)_e` ordered tuples of `e + 1`
distinct labels from `S` are not `H`-generic, so `P(E not H-generic) ≤ (2H + 1)^(e+1)/(N − e)`.
The source bound is `2^e (2H + 1)^e/(N − e)` for `e` labels
(`results/hybrid-joint-incoherence.md`, Theorem 3). -/
theorem card_not_generic_le {e : ℕ} (S : Finset (ZMod n)) (H : ℕ) (hH : H < n) :
    (univ.filter fun x : Fin (e + 1) ↪ S ↦ ¬IsGeneric H (fun a ↦ (x a : ZMod n))).card ≤
      (2 * H + 1) ^ (e + 1) * S.card.descFactorial e := by
  classical
  let box : Finset (Fin (e + 1) → ℤ) := Fintype.piFinset fun _ ↦ Finset.Icc (-(H : ℤ)) H
  have hbox : box.card = (2 * H + 1) ^ (e + 1) := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    omega
  have hsub : (univ.filter fun x : Fin (e + 1) ↪ S ↦ ¬IsGeneric H (fun a ↦ (x a : ZMod n))) ⊆
      box.biUnion fun c ↦ univ.filter fun x : Fin (e + 1) ↪ S ↦
        c ≠ 0 ∧ ∑ a, (c a : ZMod n) * (x a : ZMod n) = 0 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsGeneric, not_forall,
      not_not] at hx
    obtain ⟨c, hc0, hcH, hsum⟩ := hx
    refine Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0, hsum⟩⟩
    simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun a ↦ abs_le.mp (hcH a)
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  rw [← hbox, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun c hc ↦ ?_
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨b, hb⟩ : ∃ b, c b ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  have hbn : ((c b : ℤ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have hcb : |c b| ≤ H := by
      simp only [box, Fintype.mem_piFinset, Finset.mem_Icc] at hc
      exact abs_le.mpr (hc b)
    have := Int.le_of_dvd (abs_pos.mpr hb) ((dvd_abs _ _).mpr hdvd)
    omega
  have h := card_relation_le S (fun a ↦ ((c a : ℤ) : ZMod n)) b hbn
  refine le_trans ?_ h
  rw [← Fintype.card_subtype]
  refine Fintype.card_le_of_injective (fun x ↦ ⟨x.1, x.2.2⟩) ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [Subtype.mk.injEq] at hxy
  exact Subtype.ext hxy

end Generic

section DoubleCount

/-- Step (5) of Theorem 3: if every `σ` lies in at most `d` of the sets `S_R`, then
`∑_R |∑_{σ ∈ S_R} f σ| ≤ d ∑_σ |f σ|`. With `f = ρ_E − U` on `Ham(B)` and `S_R = Ham(B) ∩ Ham(R)`
this is `E_R |ρ_E(S_R) − U(S_R)| ≤ 2 p TV(ρ_E, U)` (`results/hybrid-joint-incoherence.md`,
Theorem 3). -/
theorem sum_abs_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ] (rel : ι → κ → Prop)
    [∀ i j, Decidable (rel i j)] (f : κ → ℝ) (d : ℕ)
    (hd : ∀ j, (univ.filter fun i ↦ rel i j).card ≤ d) :
    ∑ i, |∑ j ∈ univ.filter (rel i), f j| ≤ d * ∑ j, |f j| := by
  calc ∑ i, |∑ j ∈ univ.filter (rel i), f j|
      ≤ ∑ i, ∑ j ∈ univ.filter (rel i), |f j| :=
        Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ((univ.filter fun i ↦ rel i j).card : ℝ) * |f j| := by
        simp only [Finset.sum_filter, Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
    _ ≤ ∑ j, (d : ℝ) * |f j| :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast hd j)
          (abs_nonneg _)
    _ = d * ∑ j, |f j| := by rw [Finset.mul_sum]

end DoubleCount

end Pairing
