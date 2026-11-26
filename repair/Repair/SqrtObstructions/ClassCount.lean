import Suppression.Density

/-!
# NG-A(a), the class counting lemma

Source: `results/sqrt-m-obstructions.md` §1.2, Theorem NG-A(a) (counting duality). Fix a class
`𝒵` of perfect matchings of `V_m`, a six-vertex gadget `G` and `M = m - 3`. Put
`β_K(M) = ∑_{j ≤ K} C(M, j)(2j - 1)!!` and `D3 = (2m - 1)(2m - 3)(2m - 5)`.

* `PerfectMatching.card_near_class_le` : at most `|𝒵| β_K(M)` tails `T` have
  `ρ_𝒵(T) = min_{P ∈ 𝒵} |T ∖ P| ≤ K`. It is `card_tailDist_le` summed over `𝒵`.
* `RoundRobin.Canonical.class_count` : if `N(𝒵) ≤ K`, then
  `(2m - 7)!! ≤ |𝒵| β_K(M) ≤ |𝒵| (K + 1)(2m)^K`. With `𝒵 = Z` this is `repair_count`.
* `RoundRobin.Canonical.class_density_ge` : if `N(𝒵) ≤ K`, then
  `U(𝒵) = |𝒵| / (2m - 1)!! ≥ 1 / (D3 (K + 1)(2m)^K)`.
* `RoundRobin.Canonical.near_class_fraction_le` : the fraction of tails with `ρ_𝒵(T) ≤ K` is at
  most `U(𝒵) D3 (K + 1)(2m)^K`. This is the finite form of the last clause of NG-A(a). At
  `U(𝒵) ≤ e^(-a√m ln m)` and `K = ⌊(a - ε)√m⌋` the right side is
  `e^(-(ε - o(1))√m ln m)`, which is arithmetic and is not formalized.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [DecidableEq V]

/-- **NG-A(a), counting duality** (`sqrt-m-obstructions.md` §1.2). For a finite class `𝒵` of
perfect matchings of `V` and `U ⊆ V` with `|U| = 2M`, at most `|𝒵| ∑_{j ≤ K} C(M, j)(2j - 1)!!`
perfect matchings `T` of `U` are within `K` edges of some member of `𝒵`. -/
theorem card_near_class_le (𝒵 : Finset (PerfectMatching V)) {U : Finset V} {M : ℕ}
    (hU : U.card = 2 * M) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching U ↦ ∃ P ∈ 𝒵, tailDist P T ≤ K).card ≤
      𝒵.card * ∑ j ∈ Finset.range (K + 1), M.choose j * Nat.doubleFactorial (2 * j - 1) := by
  calc (Finset.univ.filter fun T : PerfectMatching U ↦ ∃ P ∈ 𝒵, tailDist P T ≤ K).card
      ≤ (𝒵.biUnion fun P ↦
          Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T ≤ K).card := by
        refine Finset.card_le_card fun T hT ↦ ?_
        obtain ⟨P, hP, hd⟩ := (Finset.mem_filter.mp hT).2
        exact Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩
    _ ≤ ∑ P ∈ 𝒵, (Finset.univ.filter fun T : PerfectMatching U ↦ tailDist P T ≤ K).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ 𝒵, ∑ j ∈ Finset.range (K + 1), M.choose j * Nat.doubleFactorial (2 * j - 1) :=
        Finset.sum_le_sum fun P _ ↦ card_tailDist_le P hU K
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- **NG-A(a)**, ball form (`sqrt-m-obstructions.md` §1.2). For a six-vertex gadget `G`, at most
`|𝒵| (K + 1)(2m)^K` tails `T` have `ρ_𝒵(T) ≤ K`. -/
theorem card_near_class_le_pow {G : Finset (Vertex m)} (hG : G.card = 6)
    (𝒵 : Finset (PerfectMatching (Vertex m))) (K : ℕ) :
    (Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ 𝒵, tailDist P T ≤ K).card ≤ 𝒵.card * ((K + 1) * (2 * m) ^ K) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  exact (card_near_class_le 𝒵 hU K).trans (Nat.mul_le_mul_left _
    (sum_choose_mul_doubleFactorial_le (Nat.sub_le m 3) (NeZero.pos m) K))

/-- **NG-A(a)**, class form of the COD-155 counting lemma (`sqrt-m-obstructions.md` §1.2). If
every tail is within `K` edges of a member of the class `𝒵`, so `N(𝒵) ≤ K`, then
`(2m - 7)!! ≤ |𝒵| ∑_{j ≤ K} C(m - 3, j)(2j - 1)!! ≤ |𝒵| (K + 1)(2m)^K`. -/
theorem class_count {G : Finset (Vertex m)} (hG : G.card = 6)
    {𝒵 : Finset (PerfectMatching (Vertex m))} {K : ℕ}
    (hK : ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), ∃ P ∈ 𝒵, tailDist P T ≤ K) :
    Nat.doubleFactorial (2 * m - 7) ≤ 𝒵.card *
        ∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) ∧
      𝒵.card * ∑ j ∈ Finset.range (K + 1), (m - 3).choose j * Nat.doubleFactorial (2 * j - 1) ≤
        𝒵.card * ((K + 1) * (2 * m) ^ K) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  refine ⟨?_, Nat.mul_le_mul_left _
    (sum_choose_mul_doubleFactorial_le (Nat.sub_le m 3) (NeZero.pos m) K)⟩
  rw [← card_tail hG]
  refine le_trans (le_of_eq ?_) (card_near_class_le 𝒵 hU K)
  rw [Finset.filter_true_of_mem fun T _ ↦ hK T, Finset.card_univ]

/-- **NG-A(a)**, density form (`sqrt-m-obstructions.md` §1.2). If `N(𝒵) ≤ K` for the class `𝒵`,
then `U(𝒵) = |𝒵| / (2m - 1)!! ≥ 1 / ((2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K)`. -/
theorem class_density_ge {G : Finset (Vertex m)} (hG : G.card = 6)
    {𝒵 : Finset (PerfectMatching (Vertex m))} {K : ℕ}
    (hK : ∀ T : PerfectMatching (Gᶜ : Finset (Vertex m)), ∃ P ∈ 𝒵, tailDist P T ≤ K) :
    1 / ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K : ℝ) ≤
      (𝒵.card : ℝ) / (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  obtain ⟨h1, h2⟩ := class_count hG hK
  have h : Nat.doubleFactorial (2 * m - 1) ≤
      𝒵.card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K) := by
    rw [doubleFactorial_two_mul_sub_one_eq h3]
    calc (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * Nat.doubleFactorial (2 * m - 7)
        ≤ (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (𝒵.card * ((K + 1) * (2 * m) ^ K)) :=
          Nat.mul_le_mul_left _ (h1.trans h2)
      _ = 𝒵.card * ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K) := by
          ring
  have hcast : (((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K : ℕ) : ℝ) =
      (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_sub (show 3 ≤ 2 * m by omega),
      Nat.cast_sub (show 5 ≤ 2 * m by omega)]
    ring
  have hpos : 0 < (2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K :=
    Nat.pos_of_ne_zero (by simp; omega)
  rw [div_le_div_iff₀ (hcast ▸ Nat.cast_pos.mpr hpos)
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)), one_mul, ← hcast]
  exact_mod_cast h

/-- **NG-A(a)**, tail-fraction form (`sqrt-m-obstructions.md` §1.2). The fraction of tails `T`
with `ρ_𝒵(T) ≤ K` is at most `U(𝒵) (2m - 1)(2m - 3)(2m - 5)(K + 1)(2m)^K`, where
`U(𝒵) = |𝒵| / (2m - 1)!!`. -/
theorem near_class_fraction_le {G : Finset (Vertex m)} (hG : G.card = 6)
    (𝒵 : Finset (PerfectMatching (Vertex m))) (K : ℕ) :
    ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ 𝒵, tailDist P T ≤ K).card : ℝ) / Nat.doubleFactorial (2 * m - 7) ≤
      (𝒵.card : ℝ) / Nat.doubleFactorial (2 * m - 1) *
        ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) * (K + 1) * (2 * m) ^ K) := by
  obtain ⟨h3, -⟩ := card_compl_gadget hG
  set D : ℝ := (((2 * m - 1) * (2 * m - 3) * (2 * m - 5) : ℕ) : ℝ) with hDdef
  set W : ℝ := (Nat.doubleFactorial (2 * m - 7) : ℝ) with hWdef
  have hD : ((2 * m - 1) * (2 * m - 3) * (2 * m - 5) : ℝ) = D := by
    rw [hDdef]
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_sub (show 3 ≤ 2 * m by omega),
      Nat.cast_sub (show 5 ≤ 2 * m by omega)]
    ring
  have hDpos : 0 < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by simp; omega))
  have hW : 0 < W := Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
  have hfac : (Nat.doubleFactorial (2 * m - 1) : ℝ) = D * W := by
    rw [doubleFactorial_two_mul_sub_one_eq h3, hDdef, hWdef]
    push_cast
    ring
  have h' : ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
      ∃ P ∈ 𝒵, tailDist P T ≤ K).card : ℝ) ≤ 𝒵.card * ((K + 1) * (2 * m) ^ K) := by
    exact_mod_cast card_near_class_le_pow hG 𝒵 K
  rw [hfac, hD]
  calc ((Finset.univ.filter fun T : PerfectMatching (Gᶜ : Finset (Vertex m)) ↦
        ∃ P ∈ 𝒵, tailDist P T ≤ K).card : ℝ) / W
      ≤ 𝒵.card * ((K + 1) * (2 * m) ^ K) / W := div_le_div_of_nonneg_right h' hW.le
    _ = 𝒵.card / (D * W) * (D * (K + 1) * (2 * m) ^ K) := by
        field_simp

end RoundRobin.Canonical

end Pairing
