import Spin.SchurForm

/-!
# M2. Reduction to `Cl(U_n, q)`

* `sq_of_span` : `f(u)² = Q(u)` holds on all of `M` once it holds on a spanning set together with
  the anticommutators.
* `adjU t = v_{t,t+1}`. `span_adjU` : these span `U_n`. `polar_adjU` : their polar form is
  `[|s - t| = 1]`.
* `reduceHom` : a family `P_t` in an `𝔽₂`-algebra with `P_t² = 1` and
  `{P_s, P_t} = [|s - t| = 1]` defines `Cl(U_n, q) → A` with `ι(v_{t,t+1}) ↦ P_t`.
* `stildeCl n : S̃_{2n} → Cl(U_n, q)ˣ` and `cliffordRep_stildeCl` : on `W_n` it is `ρ ∘ toPerm`.
-/

namespace Pairing

open Equiv PerfectMatching

/-- `f(u)² = Q(u)` everywhere from a spanning set. -/
theorem sq_of_span {R M A : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Ring A]
    [Algebra R A] (Q : QuadraticForm R M) (f : M →ₗ[R] A) {s : Set M}
    (hs : Submodule.span R s = ⊤) (h1 : ∀ x ∈ s, f x * f x = algebraMap R A (Q x))
    (h2 : ∀ x ∈ s, ∀ y ∈ s,
      f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y)) (u : M) :
    f u * f u = algebraMap R A (Q u) := by
  have hmem : ∀ y : M, y ∈ Submodule.span R s := fun y ↦ hs ▸ Submodule.mem_top
  have hA : ∀ x ∈ s, ∀ y : M,
      f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) := by
    intro x hx y
    induction hmem y using Submodule.span_induction with
    | mem y hy => exact h2 x hx y hy
    | zero => simp
    | add y z _ _ ihy ihz =>
      rw [QuadraticMap.polar_add_right, map_add, map_add, ← ihy, ← ihz]
      noncomm_ring
    | smul c y _ ih =>
      rw [QuadraticMap.polar_smul_right, map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add, ih,
        smul_eq_mul, map_mul, Algebra.smul_def]
  have hB : ∀ x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) := by
    intro x y
    induction hmem x using Submodule.span_induction with
    | mem x hx => exact hA x hx y
    | zero => simp
    | add x z _ _ ihx ihz =>
      rw [QuadraticMap.polar_add_left, map_add, map_add, ← ihx, ← ihz]
      noncomm_ring
    | smul c x _ ih =>
      rw [QuadraticMap.polar_smul_left, map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add, ih,
        smul_eq_mul, map_mul, Algebra.smul_def]
  induction hmem u using Submodule.span_induction with
  | mem x hx => exact h1 x hx
  | zero => simp
  | add x y _ _ ihx ihy =>
    rw [map_add, QuadraticMap.map_add Q x y, map_add, map_add, ← ihx, ← ihy, ← hB x y]
    noncomm_ring
  | smul c x _ ih =>
    rw [map_smul, smul_mul_smul_comm, ih, QuadraticMap.map_smul, smul_eq_mul, map_mul,
      Algebra.smul_def]

theorem neg_eq_self_F₂ {A : Type*} [AddCommGroup A] [Module F₂ A] (x : A) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_F₂ x)

variable (n : ℕ)

/-- The path edge `v_{t,t+1}` in `U_n`. -/
def adjU (t : Fin (2 * n - 1)) : U (Fin (2 * n)) :=
  ⟨v (⟨t, by omega⟩ : Fin (2 * n)) ⟨t + 1, by omega⟩, v_mem _ _⟩

theorem qForm_adjU (t : Fin (2 * n - 1)) : qForm _ (adjU n t) = 1 :=
  qfun_v (Fin.ne_of_val_ne (by simp))

theorem polar_adjU (s t : Fin (2 * n - 1)) :
    QuadraticMap.polar (qForm _) (adjU n s) (adjU n t) =
      if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0 := by
  rw [polar_qForm]
  simp only [adjU, dot_v_v, Fin.mk.injEq]
  split_ifs <;> first | decide | omega

theorem span_adjU (hn : 1 ≤ n) : Submodule.span F₂ (Set.range (adjU n)) = ⊤ := by
  set S := Submodule.span F₂ (Set.range (adjU n))
  have h0 : ∀ j (hj : j < 2 * n), (⟨v (base n hn) ⟨j, hj⟩, v_mem _ _⟩ : U (Fin (2 * n))) ∈ S := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [show (⟨v (base n hn) ⟨0, hj⟩, v_mem _ _⟩ : U (Fin (2 * n))) = 0 from
        Subtype.ext (v_self _)]
      exact zero_mem _
    | succ j ih =>
      intro hj
      have e : (⟨v (base n hn) ⟨j + 1, hj⟩, v_mem _ _⟩ : U (Fin (2 * n))) =
          ⟨v (base n hn) ⟨j, by omega⟩, v_mem _ _⟩ + adjU n ⟨j, by omega⟩ :=
        Subtype.ext (v_trans _ _ _).symm
      rw [e]
      exact add_mem (ih (by omega)) (Submodule.subset_span ⟨_, rfl⟩)
  rw [eq_top_iff]
  rintro ⟨u, hu⟩ -
  have hu' := hu
  rw [U_eq_span (base n hn)] at hu'
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h0 j j.2
  | zero => exact zero_mem _
  | add a b ha hb iha ihb =>
    exact add_mem (iha ((U_eq_span (base n hn)) ▸ ha)) (ihb ((U_eq_span (base n hn)) ▸ hb))
  | smul c a ha iha =>
    exact Submodule.smul_mem _ c (iha ((U_eq_span (base n hn)) ▸ ha))

/-- `x ↦ ∑_{s ≤ t} x_s`. -/
def prefixSum (t : Fin (2 * n - 1)) : (Fin (2 * n) → F₂) →ₗ[F₂] F₂ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (2 * n) ↦ (s : ℕ) ≤ t), LinearMap.proj s

theorem prefixSum_adjU (t t' : Fin (2 * n - 1)) :
    prefixSum n t (adjU n t' : Fin (2 * n) → F₂) = if t = t' then 1 else 0 := by
  simp only [prefixSum, adjU, v, LinearMap.sum_apply, LinearMap.proj_apply,
    Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.ext_iff]
  split_ifs <;> first | decide | omega

variable {n} {A : Type*} [Ring A] [Algebra F₂ A]

/-- `u ↦ ∑_t (∑_{s ≤ t} u_s) P_t`, so that `v_{t,t+1} ↦ P_t`. -/
def pathMap (P : Fin (2 * n - 1) → A) : U (Fin (2 * n)) →ₗ[F₂] A :=
  ∑ t, ((prefixSum n t).comp (U (Fin (2 * n))).subtype).smulRight (P t)

theorem pathMap_adjU (P : Fin (2 * n - 1) → A) (t : Fin (2 * n - 1)) :
    pathMap P (adjU n t) = P t := by
  simp only [pathMap, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, prefixSum_adjU, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Reduction mod 2. `P_t² = 1` and `{P_s, P_t} = [|s - t| = 1]` define a `Cl(U_n, q)`-action. -/
def reduceHom (hn : 1 ≤ n) (P : Fin (2 * n - 1) → A) (hP1 : ∀ t, P t * P t = 1)
    (hP2 : ∀ s t, P s * P t + P t * P s =
      if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0) : Cl n →ₐ[F₂] A :=
  CliffordAlgebra.lift _ ⟨pathMap P, sq_of_span _ _ (span_adjU n hn)
    (by
      rintro _ ⟨t, rfl⟩
      rw [pathMap_adjU, hP1, qForm_adjU, map_one])
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      rw [pathMap_adjU, pathMap_adjU, hP2, polar_adjU, apply_ite (algebraMap F₂ A), map_one,
        map_zero])⟩

theorem reduceHom_ι_adjU (hn : 1 ≤ n) (P : Fin (2 * n - 1) → A) (hP1 : ∀ t, P t * P t = 1)
    (hP2 : ∀ s t, P s * P t + P t * P s =
      if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0) (t : Fin (2 * n - 1)) :
    reduceHom hn P hP1 hP2 (CliffordAlgebra.ι _ (adjU n t)) = P t := by
  rw [reduceHom, CliffordAlgebra.lift_ι_apply]
  exact pathMap_adjU P t

variable (n)

/-- `T_t = ι(v_{t,t+1})` in `Cl(U_n, q)`. -/
def adjT (t : Fin (2 * n - 1)) : Cl n :=
  CliffordAlgebra.ι _ (adjU n t)

theorem adjT_sq (t : Fin (2 * n - 1)) : adjT n t * adjT n t = -1 := by
  rw [adjT, ι_sq_one n (qForm_adjU n t), neg_eq_self_F₂]

theorem adjT_anticomm (s t : Fin (2 * n - 1)) :
    adjT n s * adjT n t + adjT n t * adjT n s =
      if (t : ℕ) = s + 1 ∨ (s : ℕ) = t + 1 then 1 else 0 := by
  rw [adjT, adjT, CliffordAlgebra.ι_mul_ι_add_swap, polar_adjU, apply_ite (algebraMap F₂ (Cl n)),
    map_one, map_zero]

/-- `S̃_{2n} → Cl(U_n, q)ˣ`, `t_j ↦ ι(v_{j,j+1})`, `z ↦ -1 = 1`. -/
def stildeCl : Stilde (2 * n) →* (Cl n)ˣ :=
  Stilde.lift (Stilde.isData_clifford (adjT n) (adjT_sq n)
    (fun i j h ↦ by simp [adjT_anticomm, h])
    (fun i j h ↦ by
      rw [adjT_anticomm, ite_eq_right_iff]
      exact fun h' ↦ absurd h' (by omega)))

theorem stildeCl_t (j : Fin (2 * n - 1)) : (stildeCl n (Stilde.t j) : Cl n) = adjT n j := by
  rw [stildeCl, Stilde.lift_t]
  rfl

theorem stildeCl_z : (stildeCl n (Stilde.z (2 * n)) : Cl n) = 1 := by
  rw [stildeCl, Stilde.lift_z]
  exact neg_eq_self_F₂ 1

/-- On `W_n`, `S̃_{2n}` acts through `S_{2n}`. -/
theorem cliffordRep_stildeCl (o : Fin (2 * n)) (g : Stilde (2 * n)) :
    cliffordRep o (stildeCl n g : Cl n) = ρW (Stilde.toPerm (2 * n) g) := by
  have h := Stilde.hom_ext (f := (Units.map (cliffordRep o : Cl n →* Module.End F₂ _)).comp
      (stildeCl n)) (g := (MonoidHom.toHomUnits ρW).comp (Stilde.toPerm (2 * n)))
    (Units.ext (by
      simp only [MonoidHom.comp_apply, Units.coe_map, stildeCl_z, map_one, Stilde.toPerm_z,
        Units.val_one]))
    (fun j ↦ Units.ext (by
      simp only [MonoidHom.comp_apply, Units.coe_map, stildeCl_t, Stilde.toPerm_t,
        MonoidHom.coe_toHomUnits, adjT, adjU]
      exact cliffordRep_ι_v o (Fin.ne_of_val_ne (by simp))))
  exact congrArg Units.val (DFunLike.congr_fun h g)

end Pairing
