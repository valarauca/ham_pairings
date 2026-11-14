import Clifford.Contraction

/-!
# L-C. Six-point parity (sketch §2)

`A = {a, b, c}`, `B = {a', b', c'}`, and `X = X_{γ₀} = {aa', bb', cc'}`. With `τ = (a b c)`,
`τ X = X_{γ₀ τ⁻¹}` and `τ² X = X_{γ₀ τ}`, so `{X, τ X, τ² X} = {X_γ : γ ∈ γ₀ ∘ A₃}`. For every
`κ ∈ PM(A ⊔ B)` the number of these `X_γ` with `X_γ ∪ κ` one cycle is even.

The statement is checked exhaustively over the 15 matchings `κ` of `Fin 6` and moved to any
six points by `congr`. The sketch's argument by crossing number (three crossings through the
cycle type of `π_γ = σ⁻¹ γ`, one crossing through the `2`-cycle and the `6`-cycle) is not
formalized here. The exhaustive check replaces it.
-/

namespace Pairing.PerfectMatching

open Equiv

/-- `X_{γ₀} = {03, 14, 25}` on `Fin 6`, with `a, b, c, a', b', c' = 0, …, 5`. -/
def X6 : PerfectMatching (Fin 6) where
  mate := swap 0 3 * swap 1 4 * swap 2 5
  mate_mate := by decide
  mate_ne := by decide

theorem X6_mate : ∀ i, X6.mate i = ![3, 4, 5, 0, 1, 2] i := by
  decide

/-- `τ = (0 1 2)` on `Fin 6`. -/
def τ6 : Perm (Fin 6) :=
  swap 0 1 * swap 1 2

/-- L-C on `Fin 6`. -/
theorem sum_H_orbit_fin6 :
    ∀ κ : PerfectMatching (Fin 6), H X6 κ + H (τ6 • X6) κ + H (τ6 ^ 2 • X6) κ = 0 := by
  decide +kernel

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- L-C. `∑_{γ ∈ γ₀ ∘ A₃} H[X_γ, κ] = 0`. -/
theorem sum_H_orbit_six (hW : Fintype.card W = 6) {a b c a' b' c' : W}
    (hinj : Function.Injective ![a, b, c, a', b', c']) {X : PerfectMatching W}
    (ha : X.mate a = a') (hb : X.mate b = b') (hc : X.mate c = c') (κ : PerfectMatching W) :
    H X κ + H ((swap a b * swap b c) • X) κ + H ((swap a b * swap b c) ^ 2 • X) κ = 0 := by
  let e : Fin 6 ≃ W := Equiv.ofBijective ![a, b, c, a', b', c']
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [Fintype.card_fin, hW]⟩)
  have ha' : X.mate a' = a := by rw [← ha, mate_mate]
  have hb' : X.mate b' = b := by rw [← hb, mate_mate]
  have hc' : X.mate c' = c := by rw [← hc, mate_mate]
  have hX : congr e X6 = X := by
    ext v
    obtain ⟨i, rfl⟩ := e.surjective v
    rw [congr_mate, e.symm_apply_apply]
    fin_cases i <;> simp [e, X6_mate, ha, hb, hc, ha', hb', hc']
  have hτ : e.permCongr τ6 = swap a b * swap b c := by
    rw [τ6, permCongr_mul, permCongr_def, permCongr_def, symm_trans_swap_trans,
      symm_trans_swap_trans]
    rfl
  have hκ : congr e ((congr e).symm κ) = κ := (congr e).apply_symm_apply κ
  have h1 : (swap a b * swap b c) • X = congr e (τ6 • X6) := by
    rw [congr_smul, hτ, hX]
  have h2 : (swap a b * swap b c) ^ 2 • X = congr e (τ6 ^ 2 • X6) := by
    simp only [congr_smul, pow_two, permCongr_mul, hτ, hX]
  rw [h1, h2, ← hX, ← hκ, H_congr, H_congr, H_congr]
  exact sum_H_orbit_fin6 _

end Pairing.PerfectMatching
