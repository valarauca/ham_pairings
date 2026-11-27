import Clifford.PolarSection
import Repair.Covering.Witness
import Repair.SqrtObstructions.CertLength

/-!
# The dimension of the round-robin fingerprint span (COD-259)

Let `F : ι → 𝓜(V)` be a family of perfect matchings, `φ(P) = r_P` its fingerprints (`rowW`,
ham-spin fd082bf) and `R(F) = span{φ(F_t)}` (`fpSpan`, ham-spin fd082bf). Call `F` a Hamiltonian
clique when `F_s ∪ F_t` is one cycle exactly for `s ≠ t`. Its Gram matrix `G[s, t] = H[F_s, F_t]`
is then `J + I` over `𝔽₂`. At prime `n = 2m - 1` the round-robin factors form one, by the gcd law
(`ham_factor_of_ne`, ham_pairings main d1cda40).

* `fpCoeff F` : the coefficient map `c ↦ Σ_t c_t φ(F_t)`, with range `R(F)` (`range_fpCoeff`).
  `fpSum F = Σ_t φ(F_t)` is the image of the all-ones vector, and `coe_fpSum_apply` : its value
  at `P` is `#{t | Ham P F_t}` mod 2.
* `eq_sum_of_fpCoeff_eq_zero`, `ker_fpCoeff_le` : for a Hamiltonian clique every relation
  `Σ_t c_t φ(F_t) = 0` has constant `c`. Hence `card_sub_one_le_finrank_fpSpan` :
  `dim R(F) ≥ |ι| - 1`. `finrank_fpSpan_eq_card_iff` : `dim R(F) = |ι|` iff `Σ_t φ(F_t) ≠ 0`, and
  `finrank_fpSpan_eq_card_iff_exists_odd` : iff some `P` closes one cycle with an odd number of
  the `F_t`. `fpSum_mem_inf_orthogonal` : for odd `|ι|`, `Σ_t φ(F_t) ∈ R(F) ∩ R(F)^⊥`.
* `RoundRobin.Canonical` : at prime `2m - 1`, `finrank_rrSpan_of_prime` :
  `2m - 2 ≤ dim R_rr ≤ 2m - 1`. `finrank_rrSpan_eq_iff_exists_odd_hamCount` : `dim R_rr = 2m - 1`
  iff some `P` has odd `X(P)` (`hamCount`, ham_pairings main d1cda40), and
  `finrank_rrSpan_eq_sub_two_iff` : `dim R_rr = 2m - 2` iff every `X(P)` is even.
  `finrank_rrSpan_two`, `finrank_rrSpan_three` : `dim R_rr = 2m - 2` at `m = 2, 3`, where
  `dim W = 2^(m-1)` leaves no room for more.
-/

namespace Pairing.PerfectMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- The coefficient map `c ↦ Σ_t c_t φ(F_t)` into the fingerprint module `W V` (`rowW`, ham-spin
fd082bf). Its range is `R(F)` (`range_fpCoeff`). -/
noncomputable def fpCoeff (F : ι → PerfectMatching V) : (ι → F₂) →ₗ[F₂] W V :=
  Fintype.linearCombination F₂ fun t ↦ rowW (F t)

/-- The range of `fpCoeff F` is `R(F)` (`fpSpan`, ham-spin fd082bf). -/
theorem range_fpCoeff (F : ι → PerfectMatching V) : LinearMap.range (fpCoeff F) = fpSpan F :=
  Fintype.range_linearCombination _ _

/-- `Σ_t c_t φ(F_t)` evaluated at `P` is `Σ_t c_t H[F_t, P]` (`H`, `rowW`, ham-spin fd082bf). -/
theorem coe_fpCoeff_apply (F : ι → PerfectMatching V) (c : ι → F₂) (P : PerfectMatching V) :
    (fpCoeff F c : PerfectMatching V → F₂) P = ∑ t, c t * H (F t) P := by
  simp [fpCoeff, Fintype.linearCombination_apply, Finset.sum_apply, coe_rowW]

/-- The fingerprint sum `Σ_t φ(F_t)` in `W V` (`rowW`, ham-spin fd082bf). -/
noncomputable def fpSum (F : ι → PerfectMatching V) : W V :=
  ∑ t, rowW (F t)

/-- `fpSum F` is the image of the all-ones vector under `fpCoeff F`. -/
theorem fpCoeff_one (F : ι → PerfectMatching V) : fpCoeff F 1 = fpSum F := by
  simp [fpCoeff, Fintype.linearCombination_apply, fpSum]

/-- `Σ_t φ(F_t)` evaluated at `P` is `#{t | Ham P F_t}` mod 2 (`Ham`, ham-spin fd082bf). -/
theorem coe_fpSum_apply (F : ι → PerfectMatching V) (P : PerfectMatching V) :
    (fpSum F : PerfectMatching V → F₂) P = ((univ.filter fun t ↦ Ham P (F t)).card : F₂) := by
  rw [← fpCoeff_one, coe_fpCoeff_apply]
  simp_rw [Pi.one_apply, one_mul, H_apply, ham_comm (F _) P]
  rw [Finset.sum_boole]

/-- `Σ_t φ(F_t) = 0` iff every `P` closes one cycle with an even number of the `F_t` (`Ham`,
ham-spin fd082bf). -/
theorem fpSum_eq_zero_iff (F : ι → PerfectMatching V) :
    fpSum F = 0 ↔ ∀ P, Even (univ.filter fun t ↦ Ham P (F t)).card := by
  simp_rw [← ZMod.natCast_eq_zero_iff_even, ← coe_fpSum_apply]
  constructor
  · intro h P
    simp [h]
  · intro h
    exact Subtype.ext (funext h)

private theorem finrank_range_add_finrank_ker_fpCoeff (F : ι → PerfectMatching V) :
    Module.finrank F₂ (fpSpan F) + Module.finrank F₂ (LinearMap.ker (fpCoeff F)) =
      Fintype.card ι := by
  rw [← range_fpCoeff, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

variable {F : ι → PerfectMatching V}

/-- For a Hamiltonian clique, `F_s ∪ F_t` one cycle iff `s ≠ t` (`Ham`, ham-spin fd082bf), every
`c` with `Σ_t c_t φ(F_t) = 0` is constant: `c_s = Σ_t c_t`. This is the kernel of `J + I`. -/
theorem eq_sum_of_fpCoeff_eq_zero (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) {c : ι → F₂}
    (hc : fpCoeff F c = 0) (s : ι) : c s = ∑ t, c t := by
  classical
  have h0 : ∑ t, c t * H (F t) (F s) = 0 := by
    rw [← coe_fpCoeff_apply, hc]
    rfl
  have h1 : ∀ t, c t * H (F t) (F s) + (if t = s then c t else 0) = c t := by
    intro t
    rw [H_apply]
    by_cases hts : t = s
    · subst hts
      simp [hF]
    · simp [hF, hts]
  calc c s = ∑ t, c t * H (F t) (F s) + ∑ t, (if t = s then c t else 0) := by
        rw [h0, zero_add, Finset.sum_ite_eq']
        simp
    _ = ∑ t, c t := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ ↦ h1 t

/-- For a Hamiltonian clique (`Ham`, ham-spin fd082bf), the relations among the `φ(F_t)` lie in
the span of the all-ones vector. -/
theorem ker_fpCoeff_le (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    LinearMap.ker (fpCoeff F) ≤ Submodule.span F₂ {1} := by
  intro c hc
  rw [Submodule.mem_span_singleton]
  refine ⟨∑ t, c t, funext fun s ↦ ?_⟩
  rw [eq_sum_of_fpCoeff_eq_zero hF (LinearMap.mem_ker.mp hc) s]
  simp

/-- `dim R(F) ≥ |ι| - 1` for a Hamiltonian clique (`fpSpan`, `Ham`, ham-spin fd082bf), since its
Gram matrix `J + I` has rank at least `|ι| - 1`. -/
theorem card_sub_one_le_finrank_fpSpan (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Fintype.card ι - 1 ≤ Module.finrank F₂ (fpSpan F) := by
  have hrk := finrank_range_add_finrank_ker_fpCoeff F
  have hker : Module.finrank F₂ (LinearMap.ker (fpCoeff F)) ≤ 1 :=
    (Submodule.finrank_mono (ker_fpCoeff_le hF)).trans ((finrank_span_le_card _).trans (by simp))
  omega

/-- For a nonempty Hamiltonian clique (`Ham`, ham-spin fd082bf), the `φ(F_t)` are independent,
`dim R(F) = |ι|`, iff `Σ_t φ(F_t) ≠ 0` (`fpSpan`, ham-spin fd082bf). -/
theorem finrank_fpSpan_eq_card_iff [Nonempty ι] (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔ fpSum F ≠ 0 := by
  have hrk := finrank_range_add_finrank_ker_fpCoeff F
  constructor
  · intro h h0
    have hk : LinearMap.ker (fpCoeff F) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      omega
    have h1 : (1 : ι → F₂) ∈ LinearMap.ker (fpCoeff F) := by
      rw [LinearMap.mem_ker, fpCoeff_one, h0]
    rw [hk, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · intro h
    have hk : LinearMap.ker (fpCoeff F) = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (ker_fpCoeff_le hF hc)
      rw [LinearMap.mem_ker, map_smul, fpCoeff_one, smul_eq_zero] at hc
      rw [Submodule.mem_bot]
      rcases hc with rfl | h0
      · exact zero_smul _ _
      · exact absurd h0 h
    rw [hk, finrank_bot] at hrk
    omega

/-- For a nonempty Hamiltonian clique, `dim R(F) = |ι|` iff some `P` closes one cycle with an odd
number of the `F_t` (`fpSpan`, `Ham`, ham-spin fd082bf). -/
theorem finrank_fpSpan_eq_card_iff_exists_odd [Nonempty ι]
    (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι ↔
      ∃ P, Odd (univ.filter fun t ↦ Ham P (F t)).card := by
  rw [finrank_fpSpan_eq_card_iff hF, Ne, fpSum_eq_zero_iff]
  simp only [not_forall, Nat.not_even_iff_odd]

/-- For a nonempty Hamiltonian clique, `dim R(F) = |ι| - 1` iff `Σ_t φ(F_t) = 0` (`fpSpan`, `Ham`,
ham-spin fd082bf). -/
theorem finrank_fpSpan_eq_card_sub_one_iff [Nonempty ι] (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t) :
    Module.finrank F₂ (fpSpan F) = Fintype.card ι - 1 ↔ fpSum F = 0 := by
  have h1 := finrank_fpSpan_le F
  have h3 := finrank_fpSpan_eq_card_iff hF
  have hpos := Fintype.card_pos (α := ι)
  constructor
  · intro h
    by_contra h0
    have := h3.mpr h0
    omega
  · intro h0
    have h2 := card_sub_one_le_finrank_fpSpan hF
    have : Module.finrank F₂ (fpSpan F) ≠ Fintype.card ι := fun h ↦ h3.mp h h0
    omega

/-- For a Hamiltonian clique of odd size, `Σ_t φ(F_t)` lies in `R(F) ∩ R(F)^⊥`: each `F_s` is
Hamiltonian with the `|ι| - 1` others, an even number (`fpSpan`, `fpForm`, ham-spin fd082bf). -/
theorem fpSum_mem_inf_orthogonal (hF : ∀ s t, Ham (F s) (F t) ↔ s ≠ t)
    (hodd : Odd (Fintype.card ι)) :
    fpSum F ∈ fpSpan F ⊓ fpForm.orthogonal (fpSpan F) := by
  classical
  refine Submodule.mem_inf.mpr ⟨Submodule.sum_mem _ fun t _ ↦ Submodule.subset_span ⟨t, rfl⟩, ?_⟩
  rw [mem_orthogonal_fpSpan_iff]
  intro s
  rw [coe_fpSum_apply, ZMod.natCast_eq_zero_iff_even]
  have he : (univ.filter fun t ↦ Ham (F s) (F t)) = univ.erase s := by
    ext t
    simp [hF, eq_comm]
  rw [he, card_erase_of_mem (mem_univ s), card_univ]
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

end Pairing.PerfectMatching

namespace Pairing.RoundRobin.Canonical

open PerfectMatching Finset

variable {m : ℕ} [NeZero m]

/-- At prime `n = 2m - 1` the canonical factors (`factor`, ham-spin fd082bf) form a Hamiltonian
clique, `F_s ∪ F_t` is one cycle iff `s ≠ t`. The "if" half is the gcd law `ham_factor_of_ne`
(ham_pairings main d1cda40), and `F_t ∪ F_t` has a doubled edge. -/
theorem ham_factor_iff_ne (hp : (2 * m - 1).Prime) (s t : ZMod (2 * m - 1)) :
    Ham (factor m s) (factor m t) ↔ s ≠ t := by
  refine ⟨?_, ham_factor_of_ne hp⟩
  rintro h rfl
  have hm : 2 < Fintype.card (Vertex m) := by
    have := hp.two_le
    rw [card_vertex]
    omega
  exact not_ham_of_mate_eq_of_two_lt hm (v := none) rfl h

/-- `2m - 2 ≤ dim R_rr ≤ 2m - 1` at prime `n = 2m - 1`, as the Gram matrix of the factors is
`J + I` of rank `n - 1` (`rrSpan`, ham-spin fd082bf). -/
theorem finrank_rrSpan_of_prime (hp : (2 * m - 1).Prime) :
    2 * m - 2 ≤ Module.finrank F₂ (rrSpan m) ∧ Module.finrank F₂ (rrSpan m) ≤ 2 * m - 1 := by
  have h := card_sub_one_le_finrank_fpSpan (ham_factor_iff_ne hp)
  rw [ZMod.card] at h
  exact ⟨by omega, (finrank_rrSpan (m := m)).1⟩

/-- At prime `n = 2m - 1`, `dim R_rr = 2m - 1` iff some `P` has odd `X(P)` (`rrSpan`, ham-spin
fd082bf; `hamCount`, ham_pairings main d1cda40). -/
theorem finrank_rrSpan_eq_iff_exists_odd_hamCount (hp : (2 * m - 1).Prime) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 1 ↔ ∃ P, Odd (hamCount m P) := by
  have h := finrank_fpSpan_eq_card_iff_exists_odd (ham_factor_iff_ne hp)
  rw [ZMod.card] at h
  exact h

/-- At prime `n = 2m - 1`, `dim R_rr = 2m - 2` iff every `X(P)` is even, iff `Σ_t φ(F_t) = 0`
(`rrSpan`, ham-spin fd082bf; `hamCount`, ham_pairings main d1cda40). -/
theorem finrank_rrSpan_eq_sub_two_iff (hp : (2 * m - 1).Prime) :
    Module.finrank F₂ (rrSpan m) = 2 * m - 2 ↔ ∀ P, Even (hamCount m P) := by
  have h := finrank_fpSpan_eq_card_sub_one_iff (ham_factor_iff_ne hp)
  rw [ZMod.card, fpSum_eq_zero_iff, show 2 * m - 1 - 1 = 2 * m - 2 by omega] at h
  exact h

/-- At prime `n = 2m - 1`, `Σ_t φ(F_t) ∈ R_rr ∩ R_rr^⊥` (`rrSpan`, `fpForm`, ham-spin fd082bf). -/
theorem fpSum_factor_mem_inf_orthogonal (hp : (2 * m - 1).Prime) :
    fpSum (factor m) ∈ rrSpan m ⊓ fpForm.orthogonal (rrSpan m) :=
  fpSum_mem_inf_orthogonal (ham_factor_iff_ne hp) (by rw [ZMod.card]; exact modulus_odd m)

/-- `dim R_rr = 2 = 2m - 2` at `m = 2`, since `dim W = 2^(m-1) = 2` (`rrSpan`, ham-spin
fd082bf). -/
theorem finrank_rrSpan_two : Module.finrank F₂ (rrSpan 2) = 2 := by
  have h1 := (finrank_rrSpan_of_prime (m := 2) Nat.prime_three).1
  have h2 := (finrank_rrSpan (m := 2)).2
  norm_num at h1 h2
  omega

/-- `dim R_rr = 4 = 2m - 2` at `m = 3`, since `dim W = 2^(m-1) = 4` (`rrSpan`, ham-spin
fd082bf). -/
theorem finrank_rrSpan_three : Module.finrank F₂ (rrSpan 3) = 4 := by
  have h1 := (finrank_rrSpan_of_prime (m := 3) Nat.prime_five).1
  have h2 := (finrank_rrSpan (m := 3)).2
  norm_num at h1 h2
  omega

/-- If, for every `t`, the alternating walk of `P ∪ F_t` from `∞` either visits every vertex or
closes up early, then `X(P)` counts the `t` of the first kind (`hamCount`, ham_pairings main
d1cda40; `altWalk`, `ClosedMiss`, ham_pairings main d1cda40). -/
theorem hamCount_eq_card_walk {P : PerfectMatching (Vertex m)} {j : ℕ}
    (h : ∀ t, (∀ w, w ∈ Covering.altWalk P.mate (mateFn t) j none) ∨
      Covering.ClosedMiss P.mate (mateFn t) (Covering.altWalk P.mate (mateFn t) j none)) :
    hamCount m P =
      (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk P.mate (mateFn t) j none).card := by
  rw [hamCount]
  congr 1
  refine Finset.filter_congr fun t _ ↦ ⟨fun hH ↦ ?_, Covering.ham_of_altWalk P (factor m t) j none⟩
  rcases h t with hw | hc
  · exact hw
  · exact absurd hH
      (Covering.not_ham_of_closedMiss P (factor m t) (Covering.mem_altWalk_self _ _ _ _) hc)

/-- The three-switch `Q_3 = F_0 - {∞0, 16, 34} + {∞1, 03, 64}` at `m = 4`, `n = 7`, as label pairs
with `7 = ∞` (`natPairs`, ham_pairings main d1cda40). `3` is a nonresidue mod `7`. -/
def switchSevenMate : Vertex 4 → Vertex 4 :=
  Covering.Witness.natPairs 4 [(7, 1), (0, 3), (6, 4), (2, 5)]

/-- `switchSevenMate` is an involution. -/
theorem switchSevenMate_mate : ∀ v, switchSevenMate (switchSevenMate v) = v := by
  decide +kernel

/-- `switchSevenMate` has no fixed point. -/
theorem switchSevenMate_ne : ∀ v, switchSevenMate v ≠ v := by
  decide +kernel

/-- The perfect matching `Q_3` of `V_4` (`mkMatching`, ham_pairings main d1cda40). -/
def switchSeven : PerfectMatching (Vertex 4) :=
  Covering.mkMatching switchSevenMate switchSevenMate_mate switchSevenMate_ne

/-- `Q_3 ∪ F_t` is one cycle for exactly `t = 2, 3, 4`, so `X(Q_3) = 3` (`hamCount`, ham_pairings
main d1cda40). -/
theorem hamCount_switchSeven : hamCount 4 switchSeven = 3 := by
  rw [hamCount_eq_card_walk (j := 4)]
  · change (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk switchSevenMate (mateFn t) 4 none).card =
      3
    decide +kernel
  · change ∀ t, (∀ w, w ∈ Covering.altWalk switchSevenMate (mateFn t) 4 none) ∨
      Covering.ClosedMiss switchSevenMate (mateFn t)
        (Covering.altWalk switchSevenMate (mateFn t) 4 none)
    decide +kernel

/-- `dim R_rr = 7 = 2m - 1` at `m = 4` (`rrSpan`, ham-spin fd082bf), witnessed by `X(Q_3) = 3`. -/
theorem finrank_rrSpan_four : Module.finrank F₂ (rrSpan 4) = 7 :=
  (finrank_rrSpan_eq_iff_exists_odd_hamCount (m := 4) (by decide)).mpr
    ⟨switchSeven, by rw [hamCount_switchSeven]; decide⟩

/-- The three-switch `Q_2 = F_0 - {∞0, 1 10, 29} + {∞1, 02, 10 9}` at `m = 6`, `n = 11`, as label
pairs with `11 = ∞` (`natPairs`, ham_pairings main d1cda40). `2` is a nonresidue mod `11`. -/
def switchElevenMate : Vertex 6 → Vertex 6 :=
  Covering.Witness.natPairs 6 [(11, 1), (0, 2), (10, 9), (3, 8), (4, 7), (5, 6)]

/-- `switchElevenMate` is an involution. -/
theorem switchElevenMate_mate : ∀ v, switchElevenMate (switchElevenMate v) = v := by
  decide +kernel

/-- `switchElevenMate` has no fixed point. -/
theorem switchElevenMate_ne : ∀ v, switchElevenMate v ≠ v := by
  decide +kernel

/-- The perfect matching `Q_2` of `V_6` (`mkMatching`, ham_pairings main d1cda40). -/
def switchEleven : PerfectMatching (Vertex 6) :=
  Covering.mkMatching switchElevenMate switchElevenMate_mate switchElevenMate_ne

/-- `Q_2 ∪ F_t` is one cycle for exactly `t = 3, 5, 6, 7, 8, 9, 10`, so `X(Q_2) = 7` (`hamCount`,
ham_pairings main d1cda40). -/
theorem hamCount_switchEleven : hamCount 6 switchEleven = 7 := by
  rw [hamCount_eq_card_walk (j := 6)]
  · change (univ.filter fun t ↦ ∀ w, w ∈ Covering.altWalk switchElevenMate (mateFn t) 6 none).card =
      7
    decide +kernel
  · change ∀ t, (∀ w, w ∈ Covering.altWalk switchElevenMate (mateFn t) 6 none) ∨
      Covering.ClosedMiss switchElevenMate (mateFn t)
        (Covering.altWalk switchElevenMate (mateFn t) 6 none)
    decide +kernel

/-- `dim R_rr = 11 = 2m - 1` at `m = 6` (`rrSpan`, ham-spin fd082bf), witnessed by `X(Q_2) = 7`.
This is the rank in `results/autgroup-side-effects.md` (d7b3fa2) [7]. -/
theorem finrank_rrSpan_six : Module.finrank F₂ (rrSpan 6) = 11 :=
  (finrank_rrSpan_eq_iff_exists_odd_hamCount (m := 6) (by decide)).mpr
    ⟨switchEleven, by rw [hamCount_switchEleven]; decide⟩

end Pairing.RoundRobin.Canonical
