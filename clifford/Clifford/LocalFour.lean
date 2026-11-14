import Clifford.Contraction

/-!
# L-B. Four-point parity (sketch §2)

For `X, κ ∈ PM(A)` with `|A| = 4`, `X ∪ κ` is one cycle iff `X ≠ κ`. So two of the three
pairings complete `κ` to one cycle and `∑_X H[X, κ] = 0`.

`sum_H_orbit_four` is the same parity over the `⟨τ⟩`-orbit of `X₀ = {ab, cd}` with
`τ = (a b c)`, which runs through `{ab, cd}, {bc, ad}, {ca, bd}`. This is the form used in
T1, case 1.

Each statement is checked exhaustively on `Fin 4` and moved to any four points by `congr`.
-/

namespace Pairing.PerfectMatching

open Equiv

/-- L-B on `Fin 4`. -/
theorem ham_iff_ne_fin4 : ∀ X κ : PerfectMatching (Fin 4), Ham X κ ↔ X ≠ κ := by
  decide +kernel

/-- `{01, 23}` on `Fin 4`. -/
def X4 : PerfectMatching (Fin 4) where
  mate := swap 0 1 * swap 2 3
  mate_mate := by decide
  mate_ne := by decide

theorem X4_mate : ∀ i, X4.mate i = ![1, 0, 3, 2] i := by
  decide

/-- `τ = (0 1 2)` on `Fin 4`. -/
def τ4 : Perm (Fin 4) :=
  swap 0 1 * swap 1 2

/-- L-B over the `⟨τ⟩`-orbit on `Fin 4`. -/
theorem sum_H_orbit_fin4 :
    ∀ κ : PerfectMatching (Fin 4), H X4 κ + H (τ4 • X4) κ + H (τ4 ^ 2 • X4) κ = 0 := by
  decide +kernel

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- L-B. On four points `X ∪ κ` is one cycle iff `X ≠ κ`. -/
theorem ham_iff_ne_of_card_eq_four (hW : Fintype.card W = 4) (X κ : PerfectMatching W) :
    Ham X κ ↔ X ≠ κ := by
  let e : W ≃ Fin 4 := Fintype.equivFinOfCardEq hW
  rw [← ham_congr e, ham_iff_ne_fin4, Ne, Ne, (congr e).injective.eq_iff]

/-- Exactly two of the three pairings of four points complete `κ` to one cycle. -/
theorem card_filter_ham_of_card_eq_four (hW : Fintype.card W = 4) (κ : PerfectMatching W) :
    (Finset.univ.filter fun X ↦ Ham X κ).card = 2 := by
  have h : (Finset.univ.filter fun X ↦ Ham X κ) = Finset.univ.erase κ := by
    ext X
    simp [ham_iff_ne_of_card_eq_four hW]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ κ), Finset.card_univ,
    card_eq_doubleFactorial (n := 2) hW]
  decide

/-- L-B parity, `∑_{X ∈ PM(A)} H[X, κ] = 0`. -/
theorem sum_H_of_card_eq_four (hW : Fintype.card W = 4) (κ : PerfectMatching W) :
    ∑ X, H X κ = 0 := by
  simp only [H_apply]
  rw [Finset.sum_boole, card_filter_ham_of_card_eq_four hW κ]
  decide

/-- L-B over the `⟨τ⟩`-orbit of `{ab, cd}`, `τ = (a b c)`. -/
theorem sum_H_orbit_four (hW : Fintype.card W = 4) {a b c d : W}
    (hinj : Function.Injective ![a, b, c, d]) {X : PerfectMatching W} (hab : X.mate a = b)
    (hcd : X.mate c = d) (κ : PerfectMatching W) :
    H X κ + H ((swap a b * swap b c) • X) κ + H ((swap a b * swap b c) ^ 2 • X) κ = 0 := by
  let e : Fin 4 ≃ W := Equiv.ofBijective ![a, b, c, d]
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [Fintype.card_fin, hW]⟩)
  have hba : X.mate b = a := by rw [← hab, mate_mate]
  have hdc : X.mate d = c := by rw [← hcd, mate_mate]
  have hX : congr e X4 = X := by
    ext v
    obtain ⟨i, rfl⟩ := e.surjective v
    rw [congr_mate, e.symm_apply_apply]
    fin_cases i <;> simp [e, X4_mate, hab, hcd, hba, hdc]
  have hτ : e.permCongr τ4 = swap a b * swap b c := by
    rw [τ4, permCongr_mul, permCongr_def, permCongr_def, symm_trans_swap_trans,
      symm_trans_swap_trans]
    rfl
  have hκ : congr e ((congr e).symm κ) = κ := (congr e).apply_symm_apply κ
  have h1 : (swap a b * swap b c) • X = congr e (τ4 • X4) := by
    rw [congr_smul, hτ, hX]
  have h2 : (swap a b * swap b c) ^ 2 • X = congr e (τ4 ^ 2 • X4) := by
    simp only [congr_smul, pow_two, permCongr_mul, hτ, hX]
  rw [h1, h2, ← hX, ← hκ, H_congr, H_congr, H_congr]
  exact sum_H_orbit_fin4 _

end Pairing.PerfectMatching
