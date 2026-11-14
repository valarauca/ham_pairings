import Clifford.EdgeRelations
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Descent of the edge operators to `U_n` (sketch §5)

* `U V = {x : V → 𝔽₂ | ∑ x_i = 0}` and `v i j = ε_i + ε_j`.
* `qfun x = |supp x| / 2 mod 2` and `dot x y = x · y`. On `U`, `qfun_add` gives
  `q(x + y) = q(x) + q(y) + b(x, y)`, and `qForm` is the quadratic form `q` on `U`.
* `qfun_v` and `dot_v` give `q(v_e) = 1` and `b(v_e, v_f) = |e ∩ f| mod 2`.
* `gammaL o x = ∑_{j ≠ o} x_j Γ_{oj}` and `ΓU o` is its restriction to `U`.
* `gammaL_v` gives `Γ(v_ij) = Γ_ij` for every edge, using R4.
* `U_eq_span` says `U` is spanned by the `v o j`, so `ΓU_unique` says `Γ` is the unique
  linear map with `Γ(v_e) = Γ_e`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (V) in
/-- `U_n = {x : ∑ x_i = 0}`. -/
def U : Submodule F₂ (V → F₂) :=
  LinearMap.ker (∑ i, LinearMap.proj i)

omit [DecidableEq V] in
theorem mem_U {x : V → F₂} : x ∈ U V ↔ ∑ i, x i = 0 := by
  simp [U]

/-- `v_{ij} = ε_i + ε_j`. -/
def v (i j : V) : V → F₂ :=
  Pi.single i 1 + Pi.single j 1

theorem v_mem (i j : V) : v i j ∈ U V := by
  rw [mem_U]
  simp only [v, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

omit [Fintype V] in
theorem v_self (i : V) : v i i = 0 := by
  funext k
  simp only [v, Pi.add_apply, Pi.zero_apply]
  generalize (Pi.single i 1 : V → F₂) k = a
  revert a
  decide

/-- The support of `x`. -/
def supp (x : V → F₂) : Finset V :=
  Finset.univ.filter (x · ≠ 0)

/-- `q(x) = |supp x| / 2 mod 2`. -/
def qfun (x : V → F₂) : F₂ :=
  ((supp x).card / 2 : ℕ)

/-- `b(x, y) = x · y`. -/
def dot (x y : V → F₂) : F₂ :=
  ∑ i, x i * y i

private theorem f2_eq_ite (a : F₂) : a = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

omit [DecidableEq V] in
theorem sum_eq_card_supp (x : V → F₂) : ∑ i, x i = ((supp x).card : F₂) := by
  rw [supp, ← Finset.sum_boole]
  exact Finset.sum_congr rfl fun i _ ↦ f2_eq_ite (x i)

theorem dot_eq_card (x y : V → F₂) : dot x y = ((supp x ∩ supp y).card : F₂) := by
  rw [dot, supp, supp, ← Finset.filter_and, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  generalize x i = a
  generalize y i = b
  revert a b
  decide

theorem supp_add (x y : V → F₂) : supp (x + y) = symmDiff (supp x) (supp y) := by
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    Pi.add_apply]
  generalize x i = a
  generalize y i = b
  revert a b
  decide

omit [DecidableEq V] in
theorem even_card_supp {x : V → F₂} (hx : x ∈ U V) : Even (supp x).card := by
  rw [mem_U, sum_eq_card_supp] at hx
  exact (ZMod.natCast_eq_zero_iff_even).mp hx

omit [Fintype V] in
private theorem card_symmDiff_add (s t : Finset V) :
    (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_sdiff_add_card_inter s t
  have h2 := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm] at h2
  omega

omit [DecidableEq V] in
/-- `q(x + y) = q(x) + q(y) + b(x, y)` on `U`. -/
theorem qfun_add {x y : V → F₂} (hx : x ∈ U V) (hy : y ∈ U V) :
    qfun (x + y) = qfun x + qfun y + dot x y := by
  classical
  obtain ⟨a, ha⟩ := even_card_supp hx
  obtain ⟨b, hb⟩ := even_card_supp hy
  have hc := card_symmDiff_add (supp x) (supp y)
  have key : (supp (x + y)).card / 2 + (supp x ∩ supp y).card =
      (supp x).card / 2 + (supp y).card / 2 := by
    rw [supp_add]
    omega
  have hcast := congrArg (fun m : ℕ ↦ (m : F₂)) key
  simp only [Nat.cast_add] at hcast
  rw [qfun, qfun, qfun, dot_eq_card, ← hcast, add_assoc, CharTwo.add_self_eq_zero, add_zero]

omit [DecidableEq V] in
theorem qfun_zero : qfun (0 : V → F₂) = 0 := by
  simp [qfun, supp]

theorem supp_v {i j : V} (hij : i ≠ j) : supp (v i j) = {i, j} := by
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [supp, v, Pi.single_apply, Ne.symm hij]

/-- `q(v_e) = 1`. -/
theorem qfun_v {i j : V} (hij : i ≠ j) : qfun (v i j) = 1 := by
  rw [qfun, supp_v hij, Finset.card_pair hij]
  rfl

/-- `b(v_e, v_f) = |e ∩ f| mod 2`. -/
theorem dot_v {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    dot (v i j) (v k l) = ((({i, j} : Finset V) ∩ {k, l}).card : F₂) := by
  rw [dot_eq_card, supp_v hij, supp_v hkl]

omit [DecidableEq V] in
theorem dot_comm (x y : V → F₂) : dot x y = dot y x := by
  simp only [dot, mul_comm]

/-- `b` on `U`. -/
def dotU : LinearMap.BilinForm F₂ (U V) :=
  LinearMap.mk₂ F₂ (fun x y ↦ dot (x : V → F₂) y)
    (fun _ _ _ ↦ by simp [dot, add_mul, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [dot, Finset.mul_sum, mul_assoc])
    (fun _ _ _ ↦ by simp [dot, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [dot, Finset.mul_sum, mul_left_comm])

variable (V) in
/-- The quadratic form `q` on `U_n`. -/
def qForm : QuadraticForm F₂ (U V) where
  toFun x := qfun (x : V → F₂)
  toFun_smul a x := by
    rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
    · simp [qfun_zero]
    · simp
  exists_companion' := ⟨dotU, fun x y ↦ qfun_add x.2 y.2⟩

omit [DecidableEq V] in
theorem qForm_apply (x : U V) : qForm V x = qfun (x : V → F₂) :=
  rfl

omit [DecidableEq V] in
/-- `polar q = b` on `U`. -/
theorem polar_qForm (x y : U V) : QuadraticMap.polar (qForm V) x y = dot (x : V → F₂) y := by
  rw [QuadraticMap.polar, qForm_apply, qForm_apply, qForm_apply, Submodule.coe_add,
    qfun_add x.2 y.2]
  ring

theorem eq_sum_v (o : V) {x : V → F₂} (hx : x ∈ U V) : x = ∑ j, x j • v o j := by
  rw [mem_U] at hx
  funext k
  simp only [v, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_add,
    Finset.sum_add_distrib, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> simp [hx]

theorem U_eq_span (o : V) : U V = Submodule.span F₂ (Set.range (v o)) := by
  apply le_antisymm
  · intro x hx
    rw [eq_sum_v o hx]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact v_mem o j

/-- `G_j = Γ_{oj}` for `j ≠ o`, and `G_o = 0`. -/
def G (o j : V) : Module.End F₂ (W V) :=
  if j = o then 0 else Γ o j

/-- `Γ(x) = ∑_j x_j G_j` on `𝔽₂^V`. -/
def gammaL (o : V) : (V → F₂) →ₗ[F₂] Module.End F₂ (W V) :=
  ∑ j, (LinearMap.proj j : (V → F₂) →ₗ[F₂] F₂).smulRight (G o j)

theorem gammaL_apply (o : V) (x : V → F₂) : gammaL o x = ∑ j, x j • G o j := by
  simp [gammaL]

theorem gammaL_v_eq (o i j : V) : gammaL o (v i j) = G o i + G o j := by
  simp [gammaL_apply, v, Pi.single_apply, add_smul, Finset.sum_add_distrib]

/-- `Γ(v_ij) = Γ_ij`. -/
theorem gammaL_v (o : V) {i j : V} (hij : i ≠ j) : gammaL o (v i j) = Γ i j := by
  rw [gammaL_v_eq, G, G]
  by_cases hio : i = o
  · subst hio
    simp [Ne.symm hij]
  · by_cases hjo : j = o
    · subst hjo
      simp [hio, Γ_comm i j]
    · simp only [hio, hjo, ↓reduceIte]
      rw [Γ_eq_add hio (Ne.symm hjo) hij, Γ_comm o i]

theorem gammaL_v_base (o j : V) : gammaL o (v o j) = G o j := by
  simp [gammaL_v_eq, G]

/-- `Γ : U_n → End(W)`. -/
def ΓU (o : V) : U V →ₗ[F₂] Module.End F₂ (W V) :=
  (gammaL o).comp (U V).subtype

theorem ΓU_apply (o : V) (x : U V) : ΓU o x = gammaL o x :=
  rfl

/-- Uniqueness of the descent. -/
theorem ΓU_unique (o : V) (f : U V →ₗ[F₂] Module.End F₂ (W V))
    (hf : ∀ i j, i ≠ j → f ⟨v i j, v_mem i j⟩ = Γ i j) : f = ΓU o := by
  ext ⟨x, hx⟩ : 1
  have hx' := hx
  rw [U_eq_span o] at hx'
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [ΓU_apply]
    by_cases hj : j = o
    · subst hj
      have h0 : (⟨v j j, hx⟩ : U V) = 0 := Subtype.ext (v_self j)
      rw [h0, map_zero]
      simp
    · rw [hf o j (Ne.symm hj), gammaL_v o (Ne.symm hj)]
  | zero =>
    have h0 : (⟨0, hx⟩ : U V) = 0 := rfl
    rw [h0, map_zero, map_zero]
  | add a b ha hb iha ihb =>
    have hab : (⟨a + b, hx⟩ : U V) = ⟨a, (U_eq_span o) ▸ ha⟩ + ⟨b, (U_eq_span o) ▸ hb⟩ := rfl
    rw [hab, map_add, map_add, iha, ihb]
  | smul c a ha iha =>
    have hca : (⟨c • a, hx⟩ : U V) = c • ⟨a, (U_eq_span o) ▸ ha⟩ := rfl
    rw [hca, map_smul, map_smul, iha]

end Pairing.PerfectMatching
