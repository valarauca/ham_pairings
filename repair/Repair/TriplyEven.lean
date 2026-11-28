import Clifford.PolarSection
import Mathlib.FieldTheory.Finiteness
import Suppression.Canonical

/-!
# The fingerprint code is triply even (COD-303)

Let `|V| = 2n`. Each `u ∈ W V` gives the codeword `c_u = (⟨u, φ(Q)⟩)_Q` of the fingerprint code
`C_n`, and `⟨u, φ(Q)⟩ = u(Q)` (`fpForm_rowW_right`, ham-spin 87df892), so `C_n` is `W V` read as a
code in `𝔽₂^𝓜`. This file proves `results/parity-apps-contra.md` §4.4 (organize-archive d6e5620):
`8` divides every weight of `C_n` for `n ≥ 3`. The recursion is the vertex decomposition of the
proof of Proposition 1 in `results/outside-applications-contra.md` (organize-archive 8a04fbd).

* The star restriction. For an edge `vw` of `R` and `A = V ∖ {v, w}`, `X ↦ X ∪ R'` (`glue`,
  ham-spin 87df892) is a bijection from `𝓜(A)` onto the matchings through `vw` (`glueEquiv`,
  ham_pairings main dead080). `comp_glue_mem_W` : pulling back along it maps `W V` into `W A`, for
  any union `A` of edges of `R`, since a row `r_P` pulls back to `0` or to the row of the
  contraction `κ_P` (`H_glue_of_hasClosedCycle`, `H_glue`, ham-spin 87df892). This is the
  identification `L_e ≅ W_(n-1)` read on codewords. `card_filter_mate_eq` : a count over the
  matchings through `vw` is a count over `𝓜(A)`.
* `card_eq_sum_card_mate` : every `Q` has exactly one edge at `v`, so a weight splits over the
  edges `vw`, and each part is a weight of `C_(n-1)`.
* `card_apply_eq_one_of_card_eq_six` : at `n = 3` the fifteen fingerprints are the fifteen nonzero
  vectors of `W V ≅ 𝔽₂⁴`, so `C_3` is the `[15, 4, 8]` simplex code and every nonzero weight is
  `8`.
* `eight_dvd_card_apply_eq_one`, `eight_dvd_card_fpForm_eq_one` : `C_n` is triply even for every
  `n ≥ 3`.
* `card_add_eq`, `card_add_add_eq` : `wt(a + b) + 2|a ∩ b| = wt a + wt b` and its three-term form.
  `four_dvd_card_apply_and`, `even_card_apply_and_and` : two codewords meet in a multiple of `4`
  points and three in an even number.
* The rows. `H_eq_one_iff` : the row of `P` is the codeword `c_(φ(P))`, so `eight_dvd_card_ham` :
  `8 ∣ #{Q | Ham P Q}`, `four_dvd_card_ham_and_ham` : `4 ∣ #{Q | Ham P₁ Q ∧ Ham P₂ Q}`, and
  `even_card_ham_and_ham_and_ham` : `#{Q | Ham P₁ Q ∧ Ham P₂ Q ∧ Ham P₃ Q}` is even.
-/

namespace Pairing.PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem f2_eq_zero_iff_ne_one : ∀ a : F₂, a = 0 ↔ a ≠ 1 := by
  decide

section Star

/-- An edge `vw` of `R` leaves `V ∖ {v, w}` closed under `R`. -/
theorem mate_mem_compl_pair {R : PerfectMatching V} {v w : V} (hR : R.mate v = w) :
    ∀ x ∈ ({v, w} : Finset V)ᶜ, R.mate x ∈ ({v, w} : Finset V)ᶜ := by
  intro x hx
  simp only [mem_compl, mem_insert, mem_singleton, not_or] at hx ⊢
  refine ⟨fun h ↦ hx.2 ?_, fun h ↦ hx.1 (R.mate.injective (h.trans hR.symm))⟩
  rw [← R.mate_mate x, h, hR]

/-- The star restriction. For a union `A` of edges of `R`, pulling back along `X ↦ X ∪ R'`
(`glue`, ham-spin 87df892) maps `W V` into `W A`. A row `r_P` pulls back to `0` when `P ∪ R'` has
a closed cycle (`H_glue_of_hasClosedCycle`) and to the row of `κ_P = contract R P A hA` otherwise
(`H_glue`, ham-spin 87df892). -/
theorem comp_glue_mem_W (R : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, R.mate v ∈ A)
    (hA0 : A.Nonempty) {f : PerfectMatching V → F₂} (hf : f ∈ W V) :
    (fun X ↦ f (glue R A hA X)) ∈ W A := by
  have hle : W V ≤ (W A).comap (LinearMap.funLeft F₂ F₂ (glue R A hA)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, rfl⟩
    by_cases hC : HasClosedCycle R P A
    · have h0 : LinearMap.funLeft F₂ F₂ (glue R A hA) (H.row P) = 0 := by
        funext X
        change H P (glue R A hA X) = 0
        rw [H_comm]
        exact H_glue_of_hasClosedCycle R P A hA hC hA0 X
      rw [SetLike.mem_coe, Submodule.mem_comap, h0]
      exact zero_mem _
    · have h1 : LinearMap.funLeft F₂ F₂ (glue R A hA) (H.row P) = H (contract R P A hA) := by
        funext X
        change H P (glue R A hA X) = H (contract R P A hA) X
        rw [H_comm, H_glue R P A hA hC X, H_comm]
      rw [SetLike.mem_coe, Submodule.mem_comap, h1]
      exact row_mem_W _
  exact hle hf

/-- The matchings through an edge `vw` of `R` are the `X ∪ R'` with `X ∈ 𝓜(V ∖ {v, w})`
(`glueEquiv`, ham_pairings main dead080), so a count over them is a count over
`𝓜(V ∖ {v, w})`. -/
theorem card_filter_mate_eq (R : PerfectMatching V) {v w : V} (hR : R.mate v = w)
    (p : PerfectMatching V → Prop) [DecidablePred p] :
    #{Q | p Q ∧ Q.mate v = w} = #{X | p (glue R _ (mate_mem_compl_pair hR) X)} := by
  symm
  refine card_bij (fun X _ ↦ glue R _ (mate_mem_compl_pair hR) X) ?_ ?_ ?_
  · intro X hX
    rw [mem_filter] at hX ⊢
    refine ⟨mem_univ _, hX.2, ?_⟩
    rw [glue_mate_of_notMem _ _ _ _ (by simp), hR]
  · intro X₁ _ X₂ _ h
    exact (glueEquiv R _ (mate_mem_compl_pair hR)).injective (Subtype.ext h)
  · intro Q hQ
    rw [mem_filter] at hQ
    have hQw : Q.mate w = v := by rw [← hQ.2.2, mate_mate]
    have hRw : R.mate w = v := by rw [← hR, mate_mate]
    have hag : ∀ x ∉ ({v, w} : Finset V)ᶜ, Q.mate x = R.mate x := by
      intro x hx
      simp only [mem_compl, not_not, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hQ.2.2, hR]
      · rw [hQw, hRw]
    have hglue := glue_restrict_of_agree R _ (mate_mem_compl_pair hR) hag
    refine ⟨_, ?_, hglue⟩
    rw [mem_filter, hglue]
    exact ⟨mem_univ _, hQ.2.1⟩

/-- Every matching has exactly one edge at `v`, so a count over `𝓜(V)` splits over the partners
`w` of `v`. -/
theorem card_eq_sum_card_mate (v : V) (p : PerfectMatching V → Prop) [DecidablePred p] :
    #{Q | p Q} = ∑ w ∈ univ.erase v, #{Q | p Q ∧ Q.mate v = w} := by
  rw [card_eq_sum_card_fiberwise (f := fun Q ↦ Q.mate v) (t := univ.erase v)
    (fun Q _ ↦ mem_erase.mpr ⟨Q.mate_ne v, mem_univ _⟩)]
  simp only [filter_filter]

end Star

section Weight

/-- `C_3` is the `[15, 4, 8]` simplex code (`results/outside-applications-contra.md` §1.3,
organize-archive 8a04fbd). On `|V| = 6` every nonzero `u ∈ W V` has `u(Q) = 1` for exactly eight
matchings `Q`. The fifteen fingerprints are distinct and nonzero (`rowW_injective`,
`rowW_ne_zero`, ham-spin 87df892) in `W V ≅ 𝔽₂⁴` (`finrank_W_eq_of_card`), so they are all the
nonzero vectors, and `⟨u, ·⟩` is a nonzero functional (`fpForm_nondegenerate`). -/
theorem card_apply_eq_one_of_card_eq_six (hV : Fintype.card V = 6) {u : W V} (hu : u ≠ 0) :
    #{Q | (u : PerfectMatching V → F₂) Q = 1} = 8 := by
  classical
  have hV' : Fintype.card V = 2 * 3 := hV
  have hcard : Fintype.card (W V) = 16 := by
    rw [Module.card_eq_pow_finrank (K := F₂), finrank_W_eq_of_card hV' (by norm_num), ZMod.card]
    norm_num
  have hrange : univ.map ⟨rowW, rowW_injective hV' (by norm_num)⟩ = univ.erase (0 : W V) := by
    refine eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
    · obtain ⟨P, -, rfl⟩ := mem_map.mp hx
      exact mem_erase.mpr ⟨rowW_ne_zero hV' (by norm_num) P, mem_univ _⟩
    · rw [card_erase_of_mem (mem_univ _), card_univ, hcard, card_map, card_univ,
        card_eq_doubleFactorial hV']
      decide
  obtain ⟨g, hg⟩ : ∃ g, fpForm u g = 1 := by
    by_contra! h
    exact hu (fpForm_nondegenerate.1 u fun g ↦ (f2_eq_zero_iff_ne_one _).mpr (h g))
  have hgg : g + g = 0 := by
    rw [← two_smul F₂ g, show (2 : F₂) = 0 by decide, zero_smul]
  have h1 : #{Q | (u : PerfectMatching V → F₂) Q = 1} =
      #{x ∈ univ.erase (0 : W V) | fpForm u x = 1} := by
    rw [← hrange, filter_map, card_map]
    congr 1
    ext Q
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply, Function.Embedding.coeFn_mk,
      fpForm_rowW_right]
  have h2 : #{x ∈ univ.erase (0 : W V) | fpForm u x = 1} = #{x | fpForm u x = 1} := by
    congr 1
    ext x
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    rintro rfl
    rw [map_zero] at h
    exact zero_ne_one h
  have h3 : #{x | fpForm u x = 0} = #{x | fpForm u x = 1} := by
    refine card_bij (fun x _ ↦ x + g) ?_ ?_ ?_
    · intro x hx
      rw [mem_filter] at hx ⊢
      rw [map_add, hx.2, hg, zero_add]
      exact ⟨mem_univ _, rfl⟩
    · intro x₁ _ x₂ _ h
      exact add_right_cancel h
    · intro y hy
      rw [mem_filter] at hy
      refine ⟨y + g, ?_, ?_⟩
      · rw [mem_filter, map_add, hy.2, hg]
        exact ⟨mem_univ _, by decide⟩
      · rw [add_assoc, hgg, add_zero]
  have h4 : #{x | fpForm u x = 0} + #{x | fpForm u x = 1} = 16 := by
    have hneg : #{x | ¬fpForm u x = 0} = #{x | fpForm u x = 1} := by
      rw [filter_congr fun x _ ↦ by rw [f2_eq_zero_iff_ne_one, not_not]]
    rw [← hneg, card_filter_add_card_filter_not, card_univ, hcard]
  rw [h1, h2]
  omega

/-- `results/parity-apps-contra.md` §4.4 (organize-archive d6e5620), in function form. On
`|V| = 2n` with `n ≥ 3`, every `f ∈ W V` takes the value `1` on a multiple of eight matchings.
The base `n = 3` is `card_apply_eq_one_of_card_eq_six`. The step fixes a vertex `v`, splits the
count over the edges `vw` (`card_eq_sum_card_mate`) and reads each part as a weight on
`V ∖ {v, w}` (`card_filter_mate_eq`, `comp_glue_mem_W`). -/
theorem eight_dvd_card_apply_eq_one {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    {f : PerfectMatching V → F₂} (hf : f ∈ W V) : 8 ∣ #{Q | f Q = 1} := by
  induction n, hn using Nat.le_induction generalizing V with
  | base =>
    by_cases h0 : (⟨f, hf⟩ : W V) = 0
    · have hf0 : f = 0 := congrArg Subtype.val h0
      subst hf0
      simp
    · have h8 : #{Q | f Q = 1} = 8 := card_apply_eq_one_of_card_eq_six (hV.trans (by norm_num)) h0
      rw [h8]
  | succ n hn ih =>
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    rw [card_eq_sum_card_mate v]
    refine dvd_sum fun w hw ↦ ?_
    have hvw : v ≠ w := (ne_of_mem_erase hw).symm
    by_cases hR : ∃ R : PerfectMatching V, R.mate v = w
    · obtain ⟨R, hR⟩ := hR
      have hA : #({v, w} : Finset V)ᶜ = 2 * n := by
        rw [card_compl, card_pair hvw, hV]
        omega
      rw [card_filter_mate_eq R hR]
      exact ih (by rw [Fintype.card_coe, hA])
        (comp_glue_mem_W R _ _ (card_pos.mp (by omega)) hf)
    · rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun Q _ h ↦ hR ⟨Q, h.2⟩)]
      exact dvd_zero 8

/-- `results/parity-apps-contra.md` §4.4 (organize-archive d6e5620): the fingerprint code
`C_n = {(⟨u, φ(Q)⟩)_Q : u ∈ W V}` is triply even for `|V| = 2n` and every `n ≥ 3`. Every weight
`wt(c_u) = #{Q | ⟨u, φ(Q)⟩ = 1}` is divisible by `8` (`fpForm`, `rowW`, ham-spin 87df892). -/
theorem eight_dvd_card_fpForm_eq_one {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    (u : W V) : 8 ∣ #{Q | fpForm u (rowW Q) = 1} := by
  simp only [fpForm_rowW_right]
  exact eight_dvd_card_apply_eq_one hV hn u.2

/-- `wt(a + b) + 2|a ∩ b| = wt a + wt b` for `a, b : 𝓜(V) → 𝔽₂`, with `wt a = #{Q | a Q = 1}`. -/
theorem card_add_eq (a b : PerfectMatching V → F₂) :
    #{Q | (a + b) Q = 1} + 2 * #{Q | a Q = 1 ∧ b Q = 1} = #{Q | a Q = 1} + #{Q | b Q = 1} := by
  simp only [card_filter, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun Q _ ↦ ?_
  rw [Pi.add_apply]
  generalize a Q = x
  generalize b Q = y
  revert x y
  decide

/-- `wt(a + b + c) + 2(|a ∩ b| + |a ∩ c| + |b ∩ c|) = wt a + wt b + wt c + 4|a ∩ b ∩ c|` for
`a, b, c : 𝓜(V) → 𝔽₂`, with `wt a = #{Q | a Q = 1}`. -/
theorem card_add_add_eq (a b c : PerfectMatching V → F₂) :
    #{Q | (a + b + c) Q = 1} +
        2 * (#{Q | a Q = 1 ∧ b Q = 1} + #{Q | a Q = 1 ∧ c Q = 1} + #{Q | b Q = 1 ∧ c Q = 1}) =
      #{Q | a Q = 1} + #{Q | b Q = 1} + #{Q | c Q = 1} +
        4 * #{Q | a Q = 1 ∧ b Q = 1 ∧ c Q = 1} := by
  simp only [card_filter, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun Q _ ↦ ?_
  rw [Pi.add_apply, Pi.add_apply]
  generalize a Q = x
  generalize b Q = y
  generalize c Q = z
  revert x y z
  decide

/-- Two codewords of the triply even code `C_n` (`eight_dvd_card_apply_eq_one`) meet in a multiple
of four matchings, by `card_add_eq`, for `|V| = 2n` and `n ≥ 3`. -/
theorem four_dvd_card_apply_and {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    {a b : PerfectMatching V → F₂} (ha : a ∈ W V) (hb : b ∈ W V) :
    4 ∣ #{Q | a Q = 1 ∧ b Q = 1} := by
  have h := card_add_eq a b
  have h1 := eight_dvd_card_apply_eq_one hV hn ha
  have h2 := eight_dvd_card_apply_eq_one hV hn hb
  have h12 := eight_dvd_card_apply_eq_one hV hn (add_mem ha hb)
  omega

/-- Three codewords of the triply even code `C_n` (`eight_dvd_card_apply_eq_one`) meet in an even
number of matchings, by `card_add_add_eq` and `four_dvd_card_apply_and`, for `|V| = 2n` and
`n ≥ 3`. -/
theorem even_card_apply_and_and {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    {a b c : PerfectMatching V → F₂} (ha : a ∈ W V) (hb : b ∈ W V) (hc : c ∈ W V) :
    Even #{Q | a Q = 1 ∧ b Q = 1 ∧ c Q = 1} := by
  have h := card_add_add_eq a b c
  have h1 := eight_dvd_card_apply_eq_one hV hn ha
  have h2 := eight_dvd_card_apply_eq_one hV hn hb
  have h3 := eight_dvd_card_apply_eq_one hV hn hc
  have h123 := eight_dvd_card_apply_eq_one hV hn (add_mem (add_mem ha hb) hc)
  have h12 := four_dvd_card_apply_and hV hn ha hb
  have h13 := four_dvd_card_apply_and hV hn ha hc
  have h23 := four_dvd_card_apply_and hV hn hb hc
  rw [Nat.even_iff]
  omega

end Weight

section Rows

/-- The row of `P` is the codeword `c_(φ(P))`, since `⟨φ(P), φ(Q)⟩ = H[P, Q]` (`fpForm_rowW`,
ham-spin 87df892), and `H[P, Q] = 1` iff `P, Q` form a Hamiltonian pair. -/
theorem H_eq_one_iff (P Q : PerfectMatching V) : H P Q = 1 ↔ Ham P Q := by
  rw [H_apply]
  split_ifs with h <;> simp [h]

/-- On `|V| = 2n` with `n ≥ 3`, every matching forms a Hamiltonian pair with a multiple of eight
matchings, the weight of its row (`eight_dvd_card_apply_eq_one`). -/
theorem eight_dvd_card_ham {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    (P : PerfectMatching V) : 8 ∣ #{Q | Ham P Q} := by
  have e : #{Q | H P Q = 1} = #{Q | Ham P Q} := by
    congr 1
    ext Q
    simp only [mem_filter, mem_univ, true_and, H_eq_one_iff]
  rw [← e]
  exact eight_dvd_card_apply_eq_one hV hn (row_mem_W P)

/-- A corollary of `results/parity-apps-contra.md` §4.4 (organize-archive d6e5620), stated in
COD-303. On `|V| = 2n` with `n ≥ 3`, the number of matchings `Q` forming a Hamiltonian pair with
both `P₁` and `P₂` is divisible by `4` (`four_dvd_card_apply_and` on the rows). -/
theorem four_dvd_card_ham_and_ham {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    (P₁ P₂ : PerfectMatching V) : 4 ∣ #{Q | Ham P₁ Q ∧ Ham P₂ Q} := by
  have e : #{Q | H P₁ Q = 1 ∧ H P₂ Q = 1} = #{Q | Ham P₁ Q ∧ Ham P₂ Q} := by
    congr 1
    ext Q
    simp only [mem_filter, mem_univ, true_and, H_eq_one_iff]
  rw [← e]
  exact four_dvd_card_apply_and hV hn (row_mem_W P₁) (row_mem_W P₂)

/-- A corollary of `results/parity-apps-contra.md` §4.4 (organize-archive d6e5620), stated in
COD-303. On `|V| = 2n` with `n ≥ 3`, the number of matchings `Q` forming a Hamiltonian pair with
each of `P₁`, `P₂` and `P₃` is even (`even_card_apply_and_and` on the rows). -/
theorem even_card_ham_and_ham_and_ham {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 3 ≤ n)
    (P₁ P₂ P₃ : PerfectMatching V) : Even #{Q | Ham P₁ Q ∧ Ham P₂ Q ∧ Ham P₃ Q} := by
  have e : #{Q | H P₁ Q = 1 ∧ H P₂ Q = 1 ∧ H P₃ Q = 1} =
      #{Q | Ham P₁ Q ∧ Ham P₂ Q ∧ Ham P₃ Q} := by
    congr 1
    ext Q
    simp only [mem_filter, mem_univ, true_and, H_eq_one_iff]
  rw [← e]
  exact even_card_apply_and_and hV hn (row_mem_W P₁) (row_mem_W P₂) (row_mem_W P₃)

end Rows

end Pairing.PerfectMatching
