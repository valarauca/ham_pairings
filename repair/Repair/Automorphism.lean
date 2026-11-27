import Repair.FactorCap.Tail

/-!
# The automorphism group of the round-robin 1-factorization

Put `n = 2m - 1` and `𝓕 = {F_t}`, the round-robin 1-factorization `GK_{2m}` of `V_m`. An
automorphism of `𝓕` is a permutation of `V_m` that maps every factor `F_t` to some factor.

* `IsAut m σ`, `autGroup m` : the automorphisms of `𝓕`, a subgroup of `Perm V_m`.
* `isAut_affine` : the affine maps `v ↦ a v + b`, `a` a unit, are automorphisms.
* `edgeLabel m u w` : the label of the factor that holds the edge `uw`. `localSq m v` : the local
  Latin square `L_v(a, b)`, the label of the factor holding `F_a(v) F_b(v)`.
* `localSq_smul` (Lemma 1), `isMedial_localSq_none` (Lemma 2, `L_∞` is medial) and
  `not_isMedial_localSq_zero` (Lemma 3, `L_0` is not medial for `n ≥ 7`).
* `IsAut.apply_none` : for odd `n ≥ 7` every automorphism fixes `∞`.
* `IsAut.exists_affine` : an automorphism fixing `∞` is affine, for every odd `n`.
* `isAut_iff` : for odd `n ≥ 7`, `Aut(𝓕)` is exactly the affine maps. `autEquiv` is the
  bijection `(ℤ/n)ˣ × ℤ/n ≃ Aut(𝓕)`, `card_autGroup : |Aut(𝓕)| = n φ(n)`, and
  `autGroupMulEquiv : AGL(1, ℤ/n) ≃* Aut(𝓕)`, with `AGL(1, ℤ/n) = ℤ/n ≃ᵃ[ℤ/n] ℤ/n`.
* `stab_gadget` : for odd `n ≥ 13` the automorphisms fixing `G0 = {1, …, 6}` setwise are the
  identity and `gadgetFlip`, `x ↦ 7 - x`.
* Small cases, by `decide +kernel`. `autGroup_two` : at `n = 3` every permutation is an
  automorphism (`S_4`). `card_autGroup_three` : `|Aut(𝓕)| = 120` at `n = 5`, and
  `isAut_three_moebius` : `x ↦ -1/x` is an automorphism moving `∞` there. The identification
  with `PGL(2,5)` is not formalized.

Source: `results/autgroup-spike.md` §3 and §5.1. The second half of the main theorem is
Cameron 1975, Proposition 4, for `D = ℤ/n`. For prime `n` the result is Anderson 1977.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `σ` is an automorphism of the round-robin 1-factorization `{F_t}` on `V_m` when it maps every
factor `F_t` to some factor `F_s` (`results/autgroup-spike.md`). -/
def IsAut (m : ℕ) [NeZero m] (σ : Equiv.Perm (Vertex m)) : Prop :=
  ∀ t, ∃ s, σ • factor m t = factor m s

/-- `IsAut` is decidable, which the small cases of `results/autgroup-spike.md` §3 use. -/
instance (m : ℕ) [NeZero m] : DecidablePred (IsAut m) :=
  fun σ ↦ inferInstanceAs (Decidable (∀ t, ∃ s, σ • factor m t = factor m s))

/-- An automorphism permutes the factor labels, `σ • F_t = F_{π t}` for a permutation `π` of
`ℤ/n` (`results/autgroup-spike.md` §5.1). -/
theorem IsAut.exists_perm {σ : Equiv.Perm (Vertex m)} (hσ : IsAut m σ) :
    ∃ π : Equiv.Perm (ZMod (2 * m - 1)), ∀ t, σ • factor m t = factor m (π t) := by
  choose f hf using hσ
  have hinj : Function.Injective f := fun t s h ↦
    factor_injective m ((smul_left_cancel_iff σ).1 (by rw [hf, hf, h]))
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, hf⟩

/-- The automorphism group `Aut(𝓕)` of the round-robin 1-factorization on `V_m`
(`results/autgroup-spike.md`). -/
def autGroup (m : ℕ) [NeZero m] : Subgroup (Equiv.Perm (Vertex m)) where
  carrier := {σ | IsAut m σ}
  mul_mem' := by
    intro σ τ hσ hτ t
    obtain ⟨s, hs⟩ := hτ t
    obtain ⟨r, hr⟩ := hσ s
    exact ⟨r, by rw [mul_smul, hs, hr]⟩
  one_mem' := fun t ↦ ⟨t, one_smul _ _⟩
  inv_mem' := by
    intro σ hσ s
    obtain ⟨π, hπ⟩ := IsAut.exists_perm hσ
    refine ⟨π.symm s, ?_⟩
    rw [← smul_left_cancel_iff σ, smul_inv_smul, hπ, Equiv.apply_symm_apply]

/-- Membership in `Aut(𝓕)` is `IsAut` (`results/autgroup-spike.md`). -/
@[simp]
theorem mem_autGroup {σ : Equiv.Perm (Vertex m)} : σ ∈ autGroup m ↔ IsAut m σ :=
  Iff.rfl

/-- The pointwise form of `σ • F_t = F_s`, `F_s(σ v) = σ (F_t(v))` (`results/autgroup-spike.md`
§5.1, Lemma 1). -/
theorem mate_smul_eq {σ : Equiv.Perm (Vertex m)} {t s : ZMod (2 * m - 1)}
    (h : σ • factor m t = factor m s) (v : Vertex m) :
    (factor m s).mate (σ v) = σ ((factor m t).mate v) := by
  rw [← h, smul_mate, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

/-- Translations are automorphisms (`results/autgroup-spike.md` §5.1). -/
theorem isAut_shift (b : ZMod (2 * m - 1)) : IsAut m (shift m b) :=
  fun t ↦ ⟨t + b, shift_smul_factor m b t⟩

/-- The affine maps `v ↦ a v + b`, `a` a unit, are automorphisms, sending `F_t` to `F_{a t + b}`
(`results/autgroup-spike.md` §5.1). -/
theorem isAut_affine (a : (ZMod (2 * m - 1))ˣ) (b : ZMod (2 * m - 1)) :
    IsAut m (shift m b * scale m a) :=
  fun t ↦ ⟨a * t + b, affine_smul_factor m a b t⟩

/-- The label of the factor holding the edge `uw`. `∞x` lies in `F_x` and `xy` in
`F_{(x + y)/2}`, where `1/2 = m` in `ℤ/(2m-1)` (`results/autgroup-spike.md` §5.1). -/
def edgeLabel (m : ℕ) : Vertex m → Vertex m → ZMod (2 * m - 1)
  | none, none => 0
  | none, some y => y
  | some x, none => x
  | some x, some y => m * (x + y)

/-- `F_{edgeLabel u w}` pairs `u` with `w` (`results/autgroup-spike.md` §5.1). -/
theorem mate_edgeLabel {u w : Vertex m} (h : u ≠ w) :
    (factor m (edgeLabel m u w)).mate u = w := by
  rcases u with _ | x <;> rcases w with _ | y
  · exact absurd rfl h
  · rfl
  · simp [edgeLabel, factor]
  · have hxy : x ≠ y := fun e ↦ h (congrArg some e)
    have hx : x ≠ m * (x + y) := fun e ↦
      hxy (by linear_combination 2 * e + (x + y) * two_mul_natCast_self (m := m))
    rw [edgeLabel, factor, factor_mate, mateFn_of_ne _ _ hx, Option.some_inj]
    linear_combination (x + y) * two_mul_natCast_self (m := m)

/-- An edge `uw` of `F_t` has label `t` (`results/autgroup-spike.md` §5.1). -/
theorem edgeLabel_eq {t : ZMod (2 * m - 1)} {u w : Vertex m} (h : (factor m t).mate u = w) :
    edgeLabel m u w = t := by
  have hne : u ≠ w := fun e ↦ (factor m t).mate_ne u (h.trans e.symm)
  exact eq_of_adj_factor (modulus_odd m) (mate_edgeLabel hne) h

/-- For `a ≠ b`, the partners `F_a(v)` and `F_b(v)` differ (`results/autgroup-spike.md` §5.1). -/
theorem mate_ne_mate {a b : ZMod (2 * m - 1)} (hab : a ≠ b) (v : Vertex m) :
    (factor m a).mate v ≠ (factor m b).mate v := fun h ↦
  hab ((edgeLabel_eq (t := a) rfl).symm.trans (edgeLabel_eq h.symm))

/-- An automorphism with label map `π` preserves edge labels,
`edgeLabel (σ u) (σ w) = π (edgeLabel u w)` (`results/autgroup-spike.md` §5.1, Lemma 1). -/
theorem edgeLabel_smul {σ : Equiv.Perm (Vertex m)} {π : ZMod (2 * m - 1) → ZMod (2 * m - 1)}
    (hπ : ∀ t, σ • factor m t = factor m (π t)) {u w : Vertex m} (h : u ≠ w) :
    edgeLabel m (σ u) (σ w) = π (edgeLabel m u w) := by
  apply edgeLabel_eq
  rw [mate_smul_eq (hπ _), mate_edgeLabel h]

/-- The local Latin square at `v`. `L_v(a, b)` is the label of the factor holding the edge
`F_a(v) F_b(v)` for `a ≠ b`, and `L_v(a, a) = a` (`results/autgroup-spike.md` §5.1). -/
def localSq (m : ℕ) [NeZero m] (v : Vertex m) (a b : ZMod (2 * m - 1)) : ZMod (2 * m - 1) :=
  if a = b then a else edgeLabel m ((factor m a).mate v) ((factor m b).mate v)

/-- A binary operation `L` is medial when `L (L a b) (L c d) = L (L a c) (L b d)`
(`results/autgroup-spike.md` §5.1). -/
def IsMedial {α : Type*} (L : α → α → α) : Prop :=
  ∀ a b c d, L (L a b) (L c d) = L (L a c) (L b d)

/-- Mediality pulls back along an injective homomorphism `π`, `L' (π a) (π b) = π (L a b)`
(`results/autgroup-spike.md` §5.1). -/
theorem IsMedial.of_hom {α β : Type*} {L : α → α → α} {L' : β → β → β} {π : α → β}
    (hπ : Function.Injective π) (h : ∀ a b, L' (π a) (π b) = π (L a b)) (hL' : IsMedial L') :
    IsMedial L := by
  intro a b c d
  apply hπ
  simp only [← h]
  exact hL' _ _ _ _

/-- Lemma 1 of `results/autgroup-spike.md` §5.1. If `σ` maps `F_t` to `F_{π t}`, then
`L_{σ v}(π a, π b) = π L_v(a, b)`. -/
theorem localSq_smul {σ : Equiv.Perm (Vertex m)} {π : Equiv.Perm (ZMod (2 * m - 1))}
    (hπ : ∀ t, σ • factor m t = factor m (π t)) (v : Vertex m) (a b : ZMod (2 * m - 1)) :
    localSq m (σ v) (π a) (π b) = π (localSq m v a b) := by
  unfold localSq
  by_cases hab : a = b
  · rw [ite_eq_left hab, ite_eq_left (congrArg π hab)]
  · rw [ite_eq_right hab, ite_eq_right (π.injective.ne hab), mate_smul_eq (hπ a),
      mate_smul_eq (hπ b)]
    exact edgeLabel_smul hπ (mate_ne_mate hab v)

/-- Lemma 2 of `results/autgroup-spike.md` §5.1, `L_∞(a, b) = (a + b)/2`. -/
theorem localSq_none (a b : ZMod (2 * m - 1)) : localSq m none a b = m * (a + b) := by
  unfold localSq
  split_ifs with hab
  · subst hab
    linear_combination (-a) * two_mul_natCast_self (m := m)
  · simp [factor, edgeLabel]

/-- Lemma 2 of `results/autgroup-spike.md` §5.1, `L_∞` is medial. -/
theorem isMedial_localSq_none : IsMedial (localSq m none) := by
  intro a b c d
  simp only [localSq_none]
  ring

/-- Lemma 3 of `results/autgroup-spike.md` §5.1, `L_0(a, b) = a + b` for distinct nonzero
`a, b`. -/
theorem localSq_zero {a b : ZMod (2 * m - 1)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    localSq m (some 0) a b = a + b := by
  rw [localSq, ite_eq_right hab, factor, factor, factor_mate, factor_mate,
    mateFn_of_ne _ _ (Ne.symm ha), mateFn_of_ne _ _ (Ne.symm hb), edgeLabel]
  linear_combination (a + b) * two_mul_natCast_self (m := m)

omit [NeZero m] in
/-- Distinct naturals below `2m - 1` stay distinct in `ℤ/(2m-1)` (`results/autgroup-spike.md`
§5.1, Lemma 3). -/
theorem natCast_ne {k l : ℕ} (hk : k < 2 * m - 1) (hl : l < 2 * m - 1) (h : k ≠ l) :
    (k : ZMod (2 * m - 1)) ≠ l := fun e ↦ h (natCast_injOn hk hl e)

/-- Lemma 3 of `results/autgroup-spike.md` §5.1. For odd `n = 2m - 1 ≥ 7`, `L_0` is not medial,
with witness `L_0(L_0(1,1), L_0(2,3)) = 6 ≠ 7 = L_0(L_0(1,2), L_0(1,3))`. -/
theorem not_isMedial_localSq_zero (hm : 4 ≤ m) : ¬IsMedial (localSq m (some 0)) := by
  intro h
  have ne : ∀ k l : ℕ, k ≤ 6 → l ≤ 6 → k ≠ l → (k : ZMod (2 * m - 1)) ≠ l := fun k l hk hl hkl ↦
    natCast_ne (by omega) (by omega) hkl
  have h1 : (1 : ZMod (2 * m - 1)) ≠ 0 := by exact_mod_cast ne 1 0 (by omega) (by omega) (by omega)
  have h2 : (2 : ZMod (2 * m - 1)) ≠ 0 := by exact_mod_cast ne 2 0 (by omega) (by omega) (by omega)
  have h3 : (3 : ZMod (2 * m - 1)) ≠ 0 := by exact_mod_cast ne 3 0 (by omega) (by omega) (by omega)
  have h4 : (4 : ZMod (2 * m - 1)) ≠ 0 := by exact_mod_cast ne 4 0 (by omega) (by omega) (by omega)
  have h5 : (5 : ZMod (2 * m - 1)) ≠ 0 := by exact_mod_cast ne 5 0 (by omega) (by omega) (by omega)
  have h12 : (1 : ZMod (2 * m - 1)) ≠ 2 := by exact_mod_cast ne 1 2 (by omega) (by omega) (by omega)
  have h13 : (1 : ZMod (2 * m - 1)) ≠ 3 := by exact_mod_cast ne 1 3 (by omega) (by omega) (by omega)
  have h15 : (1 : ZMod (2 * m - 1)) ≠ 5 := by exact_mod_cast ne 1 5 (by omega) (by omega) (by omega)
  have h23 : (2 : ZMod (2 * m - 1)) ≠ 3 := by exact_mod_cast ne 2 3 (by omega) (by omega) (by omega)
  have h34 : (3 : ZMod (2 * m - 1)) ≠ 4 := by exact_mod_cast ne 3 4 (by omega) (by omega) (by omega)
  have e1 : localSq m (some 0) 1 1 = 1 := ite_eq_left rfl
  have e2 : localSq m (some 0) 2 3 = 5 := by
    rw [localSq_zero h2 h3 h23]
    norm_num
  have e3 : localSq m (some 0) 1 5 = 6 := by
    rw [localSq_zero h1 h5 h15]
    norm_num
  have e4 : localSq m (some 0) 1 2 = 3 := by
    rw [localSq_zero h1 h2 h12]
    norm_num
  have e5 : localSq m (some 0) 1 3 = 4 := by
    rw [localSq_zero h1 h3 h13]
    norm_num
  have e6 : localSq m (some 0) 3 4 = 7 := by
    rw [localSq_zero h3 h4 h34]
    norm_num
  have key := h 1 1 2 3
  rw [e1, e2, e3, e4, e5, e6] at key
  exact h1 (by linear_combination -key)

/-- For odd `n = 2m - 1 ≥ 7`, every automorphism of `𝓕` fixes `∞` (`results/autgroup-spike.md`
§5.1). `L_∞` is medial, while every `L_v` with `v` finite is isomorphic to `L_0`, which is not. -/
theorem IsAut.apply_none (hm : 4 ≤ m) {σ : Equiv.Perm (Vertex m)} (hσ : IsAut m σ) :
    σ none = none := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, σ (some x) = none := by
    rcases h : σ⁻¹ none with _ | x
    · exact absurd (Equiv.Perm.inv_eq_iff_eq.1 h).symm hne
    · exact ⟨x, (Equiv.Perm.inv_eq_iff_eq.1 h).symm⟩
  have hτ : IsAut m (σ * shift m x) := (autGroup m).mul_mem hσ (isAut_shift x)
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have h0 : (σ * shift m x) (some 0) = none := by simpa using hx
  have hconj : ∀ a b, localSq m none (π a) (π b) = π (localSq m (some 0) a b) := by
    intro a b
    rw [← h0]
    exact localSq_smul hπ _ a b
  exact not_isMedial_localSq_zero hm (IsMedial.of_hom π.injective hconj isMedial_localSq_none)

/-- An automorphism of `𝓕` fixing `∞` is affine, `v ↦ a v + b` with `a` a unit, for every odd
`n = 2m - 1` (`results/autgroup-spike.md` §5.1, and Cameron 1975, Proposition 4, for
`D = ℤ/n`). -/
theorem IsAut.exists_affine {σ : Equiv.Perm (Vertex m)} (hσ : IsAut m σ) (hfix : σ none = none) :
    ∃ (a : (ZMod (2 * m - 1))ˣ) (b : ZMod (2 * m - 1)), σ = shift m b * scale m a := by
  obtain ⟨π, hπ⟩ := hσ.exists_perm
  have hs : ∀ x, σ (some x) = some (π x) := by
    intro x
    have h := mate_smul_eq (hπ x) none
    rw [hfix] at h
    simpa [factor] using h.symm
  have hmid : ∀ x y, π (m * (x + y)) = m * (π x + π y) := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · have e : ∀ z : ZMod (2 * m - 1), (m : ZMod (2 * m - 1)) * (z + z) = z := fun z ↦ by
        linear_combination z * two_mul_natCast_self (m := m)
      rw [e, e]
    · have h := edgeLabel_smul hπ (u := some x) (w := some y) (by simpa using hxy)
      rw [hs, hs] at h
      exact h.symm
  have hadd : ∀ x y, π (x + y) - π 0 = (π x - π 0) + (π y - π 0) := by
    intro x y
    have h1 := hmid x y
    have h2 := hmid (x + y) 0
    rw [add_zero] at h2
    linear_combination
      2 * h1 - 2 * h2 + (π x + π y - π (x + y) - π 0) * two_mul_natCast_self (m := m)
  let f : ZMod (2 * m - 1) →+ ZMod (2 * m - 1) :=
    { toFun := fun x ↦ π x - π 0
      map_zero' := sub_self _
      map_add' := hadd }
  have hlin : ∀ x, π x - π 0 = x * (π 1 - π 0) := by
    intro x
    have h := f.map_nsmul x.val 1
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, nsmul_eq_mul, ZMod.natCast_zmod_val] at h
    exact h
  have hinj : Function.Injective f := fun x y h ↦ π.injective (sub_left_injective h)
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj 1
  have hu : IsUnit (π 1 - π 0) := IsUnit.of_mul_eq_one_right x ((hlin x).symm.trans hx)
  refine ⟨hu.unit, π 0, Equiv.ext fun v ↦ ?_⟩
  rcases v with _ | x
  · simp [hfix]
  · rw [hs, Equiv.Perm.mul_apply, scale_some, shift_some, IsUnit.unit_spec, Option.some_inj]
    linear_combination hlin x

/-- **`Aut(𝓕) = AGL(1, ℤ/n)`** for odd `n = 2m - 1 ≥ 7`. A permutation of `V_m` is an automorphism
of the round-robin 1-factorization iff it is `v ↦ a v + b` with `a` a unit, fixing `∞`
(`results/autgroup-spike.md` §5.1, Theorem, which needs no primality; Anderson 1977 for prime
`n`, and Cameron 1975, Proposition 4, for the stabiliser of `∞`). -/
theorem isAut_iff (hm : 4 ≤ m) {σ : Equiv.Perm (Vertex m)} :
    IsAut m σ ↔
      ∃ (a : (ZMod (2 * m - 1))ˣ) (b : ZMod (2 * m - 1)), σ = shift m b * scale m a :=
  ⟨fun hσ ↦ hσ.exists_affine (hσ.apply_none hm), fun ⟨a, b, h⟩ ↦ h ▸ isAut_affine a b⟩

omit [NeZero m] in
/-- The affine map `v ↦ a v + b` determines `a` and `b` (`results/autgroup-spike.md` §5.1). -/
theorem affine_inj {a a' : (ZMod (2 * m - 1))ˣ} {b b' : ZMod (2 * m - 1)}
    (h : shift m b * scale m a = shift m b' * scale m a') : a = a' ∧ b = b' := by
  have h0 := congrArg (fun σ : Equiv.Perm (Vertex m) ↦ σ (some 0)) h
  have h1 := congrArg (fun σ : Equiv.Perm (Vertex m) ↦ σ (some 1)) h
  simp only [Equiv.Perm.mul_apply, scale_some, shift_some, Option.some_inj, mul_zero, zero_add,
    mul_one] at h0 h1
  subst h0
  exact ⟨Units.ext (add_right_cancel h1), rfl⟩

/-- The bijection `(ℤ/n)ˣ × ℤ/n ≃ Aut(𝓕)`, `(a, b) ↦ (v ↦ a v + b)`, for odd `n = 2m - 1 ≥ 7`
(`results/autgroup-spike.md` §5.1). -/
noncomputable def autEquiv (hm : 4 ≤ m) : (ZMod (2 * m - 1))ˣ × ZMod (2 * m - 1) ≃ autGroup m :=
  Equiv.ofBijective (fun p ↦ ⟨shift m p.2 * scale m p.1, isAut_affine p.1 p.2⟩)
    ⟨fun p q h ↦ Prod.ext (affine_inj (Subtype.ext_iff.1 h)).1 (affine_inj (Subtype.ext_iff.1 h)).2,
      fun σ ↦ by
        obtain ⟨a, b, h⟩ := (isAut_iff hm).1 σ.2
        exact ⟨(a, b), Subtype.ext h.symm⟩⟩

/-- `|Aut(𝓕)| = n φ(n)` for odd `n = 2m - 1 ≥ 7` (`results/autgroup-spike.md` §3 and §5.1). -/
theorem card_autGroup (hm : 4 ≤ m) :
    Nat.card (autGroup m) = (2 * m - 1) * (2 * m - 1).totient := by
  rw [← Nat.card_congr (autEquiv hm), Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ZMod.card, mul_comm]

/-- An affine permutation `f` of `ℤ/n` acting on `V_m`, `x ↦ f x` and `∞ ↦ ∞`, as a homomorphism
from `AGL(1, ℤ/n) = (ℤ/n ≃ᵃ[ℤ/n] ℤ/n)` (`results/autgroup-spike.md` §5.1). -/
def affinePerm (m : ℕ) :
    (ZMod (2 * m - 1) ≃ᵃ[ZMod (2 * m - 1)] ZMod (2 * m - 1)) →* Equiv.Perm (Vertex m) where
  toFun f := Equiv.optionCongr f.toEquiv
  map_one' := Equiv.ext fun v ↦ by cases v <;> rfl
  map_mul' f g := Equiv.ext fun v ↦ by cases v <;> rfl

omit [NeZero m] in
/-- `affinePerm` sends `x` to `f x` (`results/autgroup-spike.md` §5.1). -/
@[simp]
theorem affinePerm_some (f : ZMod (2 * m - 1) ≃ᵃ[ZMod (2 * m - 1)] ZMod (2 * m - 1))
    (x : ZMod (2 * m - 1)) : affinePerm m f (some x) = some (f x) :=
  rfl

omit [NeZero m] in
/-- `affinePerm` is injective (`results/autgroup-spike.md` §5.1). -/
theorem affinePerm_injective : Function.Injective (affinePerm m) := fun f g h ↦
  AffineEquiv.ext fun x ↦ Option.some_inj.1 (by rw [← affinePerm_some, h, affinePerm_some])

omit [NeZero m] in
/-- An affine permutation of `ℤ/n` is `x ↦ a x + b` with `a = f.linear 1` and `b = f 0`
(`results/autgroup-spike.md` §5.1). -/
theorem affineEquiv_apply (f : ZMod (2 * m - 1) ≃ᵃ[ZMod (2 * m - 1)] ZMod (2 * m - 1))
    (x : ZMod (2 * m - 1)) : f x = f.linear 1 * x + f 0 := by
  have h := f.toAffineMap.linear_apply_vsub x 0
  have hl : ∀ y, f.linear y = y * f.linear 1 := fun y ↦ by
    simpa using f.linear.map_smul y 1
  simp only [vsub_eq_sub, sub_zero, AffineEquiv.linear_toAffineMap, LinearEquiv.coe_coe,
    AffineEquiv.coe_toAffineMap] at h
  rw [hl] at h
  linear_combination -h

/-- The image of `affinePerm` is `Aut(𝓕)` for odd `n = 2m - 1 ≥ 7` (`results/autgroup-spike.md`
§5.1). -/
theorem range_affinePerm (hm : 4 ≤ m) : (affinePerm m).range = autGroup m := by
  ext σ
  constructor
  · rintro ⟨f, rfl⟩
    have hl : ∀ y, f.linear y = y * f.linear 1 := fun y ↦ by
      simpa using f.linear.map_smul y 1
    have hu : IsUnit (f.linear 1) :=
      IsUnit.of_mul_eq_one_right (f.linear.symm 1) (by rw [← hl, LinearEquiv.apply_symm_apply])
    rw [mem_autGroup, show affinePerm m f = shift m (f 0) * scale m hu.unit from
      Equiv.ext fun v ↦ by
        rcases v with _ | x
        · rfl
        · simp [affineEquiv_apply f x]]
    exact isAut_affine _ _
  · intro hσ
    obtain ⟨a, b, rfl⟩ := (isAut_iff hm).1 hσ
    refine ⟨AffineEquiv.constVAdd _ _ b * (LinearEquiv.smulOfUnit a).toAffineEquiv,
      Equiv.ext fun v ↦ ?_⟩
    rcases v with _ | x
    · rfl
    · simp only [affinePerm_some, Equiv.Perm.mul_apply, scale_some, shift_some, AffineEquiv.coe_mul,
        Function.comp_apply, AffineEquiv.constVAdd_apply, LinearEquiv.coe_toAffineEquiv,
        vadd_eq_add, add_comm b]
      rfl

/-- **`AGL(1, ℤ/n) ≃* Aut(𝓕)`** for odd `n = 2m - 1 ≥ 7`. The affine group of `ℤ/n`, as the
group `ℤ/n ≃ᵃ[ℤ/n] ℤ/n` of affine equivalences, is isomorphic to the automorphism group of the
round-robin 1-factorization through `affinePerm` (`results/autgroup-spike.md` §5.1; Anderson 1977
for prime `n`). -/
noncomputable def autGroupMulEquiv (hm : 4 ≤ m) :
    (ZMod (2 * m - 1) ≃ᵃ[ZMod (2 * m - 1)] ZMod (2 * m - 1)) ≃* autGroup m :=
  (MonoidHom.ofInjective affinePerm_injective).trans (MulEquiv.subgroupCongr (range_affinePerm hm))

/-- The reflection `x ↦ 7 - x` of `V_m`, fixing `∞`, which reverses the gadget `G0 = {1, …, 6}`
(`results/autgroup-spike.md` §3). -/
def gadgetFlip (m : ℕ) [NeZero m] : Equiv.Perm (Vertex m) :=
  shift m 7 * scale m (-1)

/-- `gadgetFlip` sends `x` to `7 - x` (`results/autgroup-spike.md` §3). -/
@[simp]
theorem gadgetFlip_some (x : ZMod (2 * m - 1)) : gadgetFlip m (some x) = some (7 - x) := by
  simp [gadgetFlip, sub_eq_neg_add]

/-- **`Stab(G0) = {id, x ↦ 7 - x}`** for odd `n = 2m - 1 ≥ 13`. An automorphism of `𝓕` maps the
gadget `G0 = {1, …, 6}` onto itself iff it is the identity or `x ↦ 7 - x`
(`results/autgroup-spike.md` §3, proof of `Stab_Aut(G0) = {id, x ↦ 7 - x}`). -/
theorem stab_gadget (hm : 7 ≤ m) (σ : Equiv.Perm (Vertex m)) :
    (σ ∈ autGroup m ∧ (FactorCap.gadget m).map σ.toEmbedding = FactorCap.gadget m) ↔
      σ = 1 ∨ σ = gadgetFlip m := by
  constructor
  · rintro ⟨hσ, hG⟩
    obtain ⟨a, b, rfl⟩ := (isAut_iff (by omega)).1 hσ
    have hmem : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
        ∃ s : ℕ, 1 ≤ s ∧ s ≤ 6 ∧ (s : ZMod (2 * m - 1)) = a * k + b := by
      intro k hk1 hk6
      have hk : some (k : ZMod (2 * m - 1)) ∈ FactorCap.gadget m :=
        Finset.mem_image.2 ⟨k, Finset.mem_Icc.2 ⟨hk1, hk6⟩, rfl⟩
      have h := Finset.mem_map_of_mem (shift m b * scale m a).toEmbedding hk
      rw [hG] at h
      obtain ⟨s, hs, hs'⟩ := Finset.mem_image.1 h
      rw [Finset.mem_Icc] at hs
      refine ⟨s, hs.1, hs.2, ?_⟩
      simpa using hs'
    obtain ⟨s1, h1a, h1b, e1⟩ := hmem 1 le_rfl (by norm_num)
    obtain ⟨s2, h2a, h2b, e2⟩ := hmem 2 (by norm_num) (by norm_num)
    obtain ⟨s3, h3a, h3b, e3⟩ := hmem 3 (by norm_num) (by norm_num)
    obtain ⟨s4, h4a, h4b, e4⟩ := hmem 4 (by norm_num) (by norm_num)
    obtain ⟨s5, h5a, h5b, e5⟩ := hmem 5 (by norm_num) (by norm_num)
    obtain ⟨s6, h6a, h6b, e6⟩ := hmem 6 (by norm_num) (by norm_num)
    push_cast at e1 e2 e3 e4 e5 e6
    have step : ∀ k l : ℕ, k ≤ 12 → l ≤ 12 → (k : ZMod (2 * m - 1)) = l → k = l :=
      fun k l hk hl h ↦ natCast_injOn (by omega) (by omega) h
    have r3 := step (s3 + s1) (s2 + s2) (by omega) (by omega) (by
      push_cast
      linear_combination e3 + e1 - 2 * e2)
    have r4 := step (s4 + s1) (s2 + s3) (by omega) (by omega) (by
      push_cast
      linear_combination e4 + e1 - e2 - e3)
    have r5 := step (s5 + s1) (s2 + s4) (by omega) (by omega) (by
      push_cast
      linear_combination e5 + e1 - e2 - e4)
    have r6 := step (s6 + s1) (s2 + s5) (by omega) (by omega) (by
      push_cast
      linear_combination e6 + e1 - e2 - e5)
    have ha : (a : ZMod (2 * m - 1)) = s2 - s1 := by linear_combination e1 - e2
    have hb : b = 2 * s1 - s2 := by linear_combination e2 - 2 * e1
    have h12 : s1 ≠ s2 := by
      rintro rfl
      have h0 : (a : ZMod (2 * m - 1)) * ↑a⁻¹ = 1 := Units.mul_inv a
      rw [ha, sub_self, zero_mul] at h0
      have h01 := natCast_ne (m := m) (k := 0) (l := 1) (by omega) (by omega) (by omega)
      push_cast at h01
      exact h01 h0
    have hcase : (s1 = 1 ∧ s2 = 2) ∨ (s1 = 6 ∧ s2 = 5) := by omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      refine Equiv.ext fun v ↦ ?_
      rcases v with _ | x
      · rfl
      · norm_num at ha hb
        simp [ha, hb]
    · right
      refine Equiv.ext fun v ↦ ?_
      rcases v with _ | x
      · rfl
      · norm_num at ha hb
        rw [gadgetFlip_some, Equiv.Perm.mul_apply, scale_some, shift_some, ha, hb, Units.val_neg,
          Units.val_one, Option.some_inj]
        ring
  · have hmap : ∀ τ : Equiv.Perm (Vertex m), (∀ v ∈ FactorCap.gadget m, τ v ∈ FactorCap.gadget m) →
        (FactorCap.gadget m).map τ.toEmbedding = FactorCap.gadget m := fun τ h ↦
      Finset.map_eq_of_subset fun v hv ↦ by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
        exact h w hw
    rintro (rfl | rfl)
    · exact ⟨(autGroup m).one_mem, hmap 1 fun v hv ↦ hv⟩
    · refine ⟨isAut_affine _ _, hmap _ fun v hv ↦ ?_⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_Icc] at hk
      refine Finset.mem_image.2 ⟨7 - k, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
      rw [gadgetFlip_some, Nat.cast_sub (by omega : k ≤ 7)]
      norm_num

/-- At `n = 3` every permutation of `V_2` is an automorphism, so `Aut(𝓕) = S_4`
(`results/autgroup-spike.md` §1, item 6, and §3). -/
theorem autGroup_two : autGroup 2 = ⊤ := by
  have h : ∀ σ : Equiv.Perm (Vertex 2), IsAut 2 σ := by decide +kernel
  exact eq_top_iff.2 fun σ _ ↦ h σ

/-- `|Aut(𝓕)| = 24` at `n = 3` (`results/autgroup-spike.md` §3). -/
theorem card_autGroup_two : Nat.card (autGroup 2) = 24 := by
  rw [autGroup_two, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, card_vertex]
  rfl

/-- `|Aut(𝓕)| = 120` at `n = 5`, the order of `PGL(2,5) ≅ S_5` (`results/autgroup-spike.md` §3). -/
theorem card_autGroup_three : Nat.card (autGroup 3) = 120 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ ↦ (mem_autGroup (σ := σ))),
    Nat.card_eq_fintype_card]
  decide +kernel

/-- At `n = 5` the Möbius involution `x ↦ -1/x`, which is `(∞ 0)(1 4)`, is an automorphism that
moves `∞`, so `IsAut.apply_none` fails at `n = 5` (`results/autgroup-spike.md` §3 and §5.1). -/
theorem isAut_three_moebius :
    IsAut 3 (Equiv.swap none (some 0) * Equiv.swap (some 1) (some 4)) ∧
      (Equiv.swap none (some 0) * Equiv.swap (some 1) (some 4) : Equiv.Perm (Vertex 3)) none ≠
        none := by
  decide +kernel

end RoundRobin.Canonical

end Pairing
