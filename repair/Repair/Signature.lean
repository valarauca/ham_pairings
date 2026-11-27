import Repair.SqrtObstructions.CoreCertLength

/-!
# The signature barrier (Lemma K1, Theorem K1, X1 and X2)

Source: `results/sl5-kill.md` §1 and §2 (Lemma K1, Theorem K1, the excluded classes (X1), (X2) of
§5), with the orbit criterion of `results/sl5-contra.md` (Remark O5). The archive ancestor is the
two-switch profile identity, Theorem 11.1 of "Mathematical Pattern Investigation"
(`old-personal-chatgpt` doc `01a1e1d3-a7a1-728c-8db1-cd74249be926`), whose Corollary 11.2 is the
signature count. Lemma K1 is Lemma 1 of Hannenhalli and Pevzner, J. ACM 46 (1999), see also
Bafna and Pevzner, SIAM J. Comput. 25 (1996). Theorem K1(a) and the class (X1) are the
separating-system bound of Rényi, Acta Sci. Math. (Szeged) 22 (1961) 75-81, and Katona,
J. Combin. Theory 1 (1966) 174-194 (`results/citation-audit.md`, rows 2 and 3).

`twoarc` is not formalized, so everything is stated for a general perfect matching `M` of a finite
`V`, any factor family, and, in the round-robin part, any tail `T` of any six-vertex gadget with
any completion `M`. That includes `twoarc(p)` with its gadget edges.

General part (namespace `PerfectMatching`). For `a, a′` on distinct edges of `M`, the 2-switch
`twoSwitch M a a′` replaces `{a, Ma}, {a′, Ma′}` by `{a, Ma′}, {Ma, a′}`. Put `Φ = Q M`.
* `not_ham_twoSwitch_of_sameCycle` : if `a, a′` lie in one `Φ`-orbit, the switch is not
  Hamiltonian with `Q`. This is the case `c(σ) = 1`, equal signatures.
* `not_ham_twoSwitch_of_unreachable` : if some vertex lies in neither cycle of `M ∪ Q` through
  `a` or `a′`, the switch is not Hamiltonian with `Q`. This covers `c(σ) = 2` with `e, e′` in one
  cycle, and every `c(σ) ≥ 3`.
* `SameSig M Q a a′`, the disjunction of the two, and `not_ham_twoSwitch_of_sameSig` (Lemma K1,
  the direction the barrier uses).
* `sigBit` : a one-bit signature per factor, the `Φ`-orbit bit if `M ∪ Q` is one cycle and the
  component bit otherwise. `sameSig_of_sigBit_eq` : equal bits give `SameSig`.
  `ManyCycles M Q` (three pairwise separate cycles) gives `SameSig` for every pair
  (`sameSig_of_manyCycles`), the signature `∗`.
* `exists_uncovered_twoSwitch` (Theorem K1(a)) : if `E` holds endpoints of `|E|` distinct edges
  of `M` and `2^|𝓕₁₂| < |E|`, where `𝓕₁₂` are the members of `𝓕` without three separate cycles,
  some 2-switch of two edges of `E` is `𝓕`-uncovered.
* `exists_uncovered_twoSwitch_of_types` (Theorem K1(b), (X2)) : if the relation "same signature"
  under every member of `𝓕` is read off a type `τ : V → 𝒯` with `|𝒯| < |E|`, the same holds.

Round-robin part.
* `tailDist_twoSwitch_le` : a 2-switch of a completion of `T` is within `2` of `T`.
* `exists_uncovered_near_tail` (X1) : for any tail `T`, any completion `M` and any set `𝓕` of
  factors, of any height, with `2^|𝓕₁₂| < m - 3`, some perfect matching within `2` of `T` is
  `𝓕`-uncovered. `not_relativized_rho_ge_three` : so no `𝓕`-relativizing argument proves
  `ρ(T) ≥ 3`, and none proves `ρ(T) ≥ 6`. `not_relativized_rho_ge_three_of_card` is the cruder
  form `|𝓕| < log₂(m - 3)`.
* `exists_not_sameSig_of_rho` (Theorem K1(c)) : if `ρ(T) ≥ 3`, every pair of tail edges is
  separated by some factor.

Only the direction "equal signature implies not covered" of Lemma K1 is formalized. The converse
(a factor with different signatures covers the switch) is not needed for K1(a) to (c).
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*}

/-- The 2-switch of the edges `{a, Ma}` and `{a′, Ma′}` of `M` to `{a, Ma′}` and `{Ma, a′}`
(`sl5-kill.md` §2, `M₁ = M - e - e′ + {a, Ma′} + {Ma, a′}`), as `M` relabelled by the
transposition of `Ma` and `Ma′`. -/
def twoSwitch [DecidableEq V] (M : PerfectMatching V) (a a' : V) : PerfectMatching V :=
  Equiv.swap (M.mate a) (M.mate a') • M

/-- Off the four switched vertices the 2-switch agrees with `M`. -/
theorem twoSwitch_mate_of_ne [DecidableEq V] (M : PerfectMatching V) {a a' v : V} (h1 : v ≠ a)
    (h2 : v ≠ M.mate a) (h3 : v ≠ a') (h4 : v ≠ M.mate a') :
    (twoSwitch M a a').mate v = M.mate v := by
  rw [twoSwitch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne h2 h4]
  refine Equiv.swap_apply_of_ne_of_ne (fun h ↦ h1 ?_) (fun h ↦ h3 ?_)
  · rw [← M.mate_mate v, h, mate_mate]
  · rw [← M.mate_mate v, h, mate_mate]

/-- The 2-switch pairs `a` with `Ma′`. -/
theorem twoSwitch_mate_left [DecidableEq V]
    (M : PerfectMatching V) {a a' : V} (ha' : a' ≠ M.mate a) :
    (twoSwitch M a a').mate a = M.mate a' := by
  have h1 : a ≠ M.mate a := fun h ↦ M.mate_ne a h.symm
  have h2 : a ≠ M.mate a' := fun h ↦ ha' (by rw [h, mate_mate])
  rw [twoSwitch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_left]

/-- The 2-switch pairs `Ma` with `a′`. -/
theorem twoSwitch_mate_mate_left [DecidableEq V]
    (M : PerfectMatching V) {a a' : V} (ha' : a' ≠ M.mate a) :
    (twoSwitch M a a').mate (M.mate a) = a' := by
  rw [twoSwitch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_left, mate_mate,
    Equiv.swap_apply_of_ne_of_ne ha' fun h ↦ M.mate_ne a' h.symm]

/-- The 2-switch pairs `a′` with `Ma`. -/
theorem twoSwitch_mate_right [DecidableEq V]
    (M : PerfectMatching V) {a a' : V} (ha' : a' ≠ M.mate a) :
    (twoSwitch M a a').mate a' = M.mate a := by
  rw [twoSwitch, smul_mate, Equiv.swap_inv,
    Equiv.swap_apply_of_ne_of_ne ha' fun h ↦ M.mate_ne a' h.symm, Equiv.swap_apply_right]

/-- The 2-switch pairs `Ma′` with `a`. -/
theorem twoSwitch_mate_mate_right [DecidableEq V]
    (M : PerfectMatching V) {a a' : V} (ha' : a' ≠ M.mate a) :
    (twoSwitch M a a').mate (M.mate a') = a := by
  have h1 : a ≠ M.mate a := fun h ↦ M.mate_ne a h.symm
  have h2 : a ≠ M.mate a' := fun h ↦ ha' (by rw [h, mate_mate])
  rw [twoSwitch, smul_mate, Equiv.swap_inv, Equiv.swap_apply_right, mate_mate,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **Lemma K1, one orbit** (`sl5-kill.md` §2, case `c(σ) = 1`; `sl5-contra.md` Remark O5 (i)).
If `a ≠ a′` lie on distinct edges of `M` and in one orbit of `Φ = Q M`, then the 2-switch is
not Hamiltonian with `Q`: it closes the arc from `Ma` to `a′` into a cycle. -/
theorem not_ham_twoSwitch_of_sameCycle [Finite V] [DecidableEq V]
    (M Q : PerfectMatching V) {a a' : V} (haa : a ≠ a')
    (ha' : a' ≠ M.mate a) (h : (Q.mate * M.mate).SameCycle a a') :
    ¬Ham (twoSwitch M a a') Q := by
  set Φ := Q.mate * M.mate with hΦ
  have hstep : ∀ v, Φ v = Q.mate (M.mate v) := fun _ ↦ rfl
  have hex : ∃ j, 0 < j ∧ (Φ ^ j) a = a' := by
    obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
    refine ⟨i, Nat.pos_of_ne_zero fun h0 ↦ haa ?_, hi⟩
    rw [h0, pow_zero, Equiv.Perm.one_apply] at hi
    exact hi
  classical
  have hj : 0 < Nat.find hex ∧ (Φ ^ Nat.find hex) a = a' := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < Nat.find hex → (Φ ^ i) a ≠ a' := fun i hi hij h' ↦
    Nat.find_min hex hij ⟨hi, h'⟩
  set j := Nat.find hex with hjdef
  have hnota : ∀ i, 0 < i → i < j → (Φ ^ i) a ≠ a := by
    intro i hi hij h'
    refine hmin (j - i) (by omega) (by omega) ?_
    calc (Φ ^ (j - i)) a = (Φ ^ (j - i)) ((Φ ^ i) a) := by rw [h']
      _ = (Φ ^ j) a := by rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
      _ = a' := hj.2
  have hsc : ∀ i : ℕ, Φ.SameCycle a ((Φ ^ i) a) := fun i ↦
    Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl Φ a)
  have hnoM : ∀ v w, Φ.SameCycle v w → w ≠ M.mate v := fun v w hvw hw ↦
    not_sameCycle_mate_right Q M v (hw ▸ hvw)
  have hne1 : ∀ i, 0 < i → i < j → (Φ ^ i) a ≠ a ∧ (Φ ^ i) a ≠ M.mate a ∧ (Φ ^ i) a ≠ a' ∧
      (Φ ^ i) a ≠ M.mate a' := fun i hi hij ↦
    ⟨hnota i hi hij, hnoM a _ (hsc i), hmin i hi hij, hnoM a' _ (h.symm.trans (hsc i))⟩
  set B : Set V := {v | ∃ i, 0 < i ∧ i ≤ j ∧ v = (Φ ^ i) a} ∪
    {v | ∃ i, i < j ∧ v = M.mate ((Φ ^ i) a)} with hB
  have hQ : ∀ v ∈ B, Q.mate v ∈ B := by
    rintro v (⟨i, hi0, hij, rfl⟩ | ⟨i, hij, rfl⟩)
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine Or.inr ⟨i', by omega, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hstep, mate_mate]
    · refine Or.inl ⟨i + 1, by omega, by omega, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hstep]
  have hM1 : ∀ v ∈ B, (twoSwitch M a a').mate v ∈ B := by
    rintro v (⟨i, hi0, hij, rfl⟩ | ⟨i, hij, rfl⟩)
    · rcases lt_or_eq_of_le hij with hlt | rfl
      · obtain ⟨h1, h2, h3, h4⟩ := hne1 i hi0 hlt
        rw [twoSwitch_mate_of_ne M h1 h2 h3 h4]
        exact Or.inr ⟨i, hlt, rfl⟩
      · rw [hj.2, twoSwitch_mate_right M ha']
        exact Or.inr ⟨0, hj.1, by rw [pow_zero, Equiv.Perm.one_apply]⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero, Equiv.Perm.one_apply, twoSwitch_mate_mate_left M ha']
        exact Or.inl ⟨j, hj.1, le_rfl, hj.2.symm⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hne1 i hi0 hij
        have g1 : M.mate ((Φ ^ i) a) ≠ a := fun h' ↦
          h2 (by rw [← M.mate_mate ((Φ ^ i) a), h'])
        have g2 : M.mate ((Φ ^ i) a) ≠ M.mate a := fun h' ↦ h1 (M.mate.injective h')
        have g3 : M.mate ((Φ ^ i) a) ≠ a' := fun h' ↦
          h4 (by rw [← M.mate_mate ((Φ ^ i) a), h'])
        have g4 : M.mate ((Φ ^ i) a) ≠ M.mate a' := fun h' ↦ h3 (M.mate.injective h')
        rw [twoSwitch_mate_of_ne M g1 g2 g3 g4, mate_mate]
        exact Or.inl ⟨i, hi0, hij.le, rfl⟩
  have haB : a ∉ B := by
    rintro (⟨i, hi0, hij, hai⟩ | ⟨i, hij, hai⟩)
    · rcases lt_or_eq_of_le hij with hlt | rfl
      · exact hnota i hi0 hlt hai.symm
      · exact haa (hai.trans hj.2)
    · have h' := congrArg M.mate hai
      rw [mate_mate] at h'
      exact hnoM a _ (hsc i) h'.symm
  have ha'B : a' ∈ B := Or.inl ⟨j, hj.1, le_rfl, hj.2.symm⟩
  exact not_ham_of_closed (twoSwitch M a a') Q B hM1 hQ ha'B haB

/-- **Lemma K1, separate cycle** (`sl5-kill.md` §2, cases `c(σ) = 2` with `e, e′` in one cycle,
and `c(σ) ≥ 3`; `sl5-contra.md` Remark O5). If some vertex `w` is in neither component of
`M ∪ Q` through `a` or `a′`, its cycle survives the 2-switch, which is then not Hamiltonian with
`Q`. -/
theorem not_ham_twoSwitch_of_unreachable [DecidableEq V] (M Q : PerfectMatching V) {a a' w : V}
    (h1 : ¬(M.toGraph ⊔ Q.toGraph).Reachable a w) (h2 : ¬(M.toGraph ⊔ Q.toGraph).Reachable a' w) :
    ¬Ham (twoSwitch M a a') Q := by
  set G := M.toGraph ⊔ Q.toGraph with hG
  have hadjM : ∀ v, G.Reachable v (M.mate v) := fun v ↦
    SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl rfl))
  have hadjQ : ∀ v, G.Reachable v (Q.mate v) := fun v ↦
    SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr rfl))
  set B : Set V := {v | G.Reachable w v} with hB
  have hfar : ∀ v ∈ B, v ≠ a ∧ v ≠ M.mate a ∧ v ≠ a' ∧ v ≠ M.mate a' := by
    intro v hv
    refine ⟨fun h ↦ h1 (h ▸ hv).symm, fun h ↦ h1 ?_, fun h ↦ h2 (h ▸ hv).symm, fun h ↦ h2 ?_⟩
    · exact ((h ▸ hv : G.Reachable w (M.mate a)).trans (by
        simpa using hadjM (M.mate a))).symm
    · exact ((h ▸ hv : G.Reachable w (M.mate a')).trans (by
        simpa using hadjM (M.mate a'))).symm
  have hM1 : ∀ v ∈ B, (twoSwitch M a a').mate v ∈ B := by
    intro v hv
    obtain ⟨g1, g2, g3, g4⟩ := hfar v hv
    rw [twoSwitch_mate_of_ne M g1 g2 g3 g4]
    exact (show G.Reachable w v from hv).trans (hadjM v)
  have hQ : ∀ v ∈ B, Q.mate v ∈ B := fun v hv ↦ (show G.Reachable w v from hv).trans (hadjQ v)
  have hwB : w ∈ B := SimpleGraph.Reachable.refl w
  have haB : a ∉ B := fun h ↦ h1 (show G.Reachable w a from h).symm
  exact not_ham_of_closed (twoSwitch M a a') Q B hM1 hQ hwB haB

/-- `e` and `e′` have the same signature under `Q` (`sl5-kill.md` §1): `a, a′` lie in one orbit of
`Φ = Q M`, or some cycle of `M ∪ Q` avoids the cycles through `a` and `a′`. -/
def SameSig (M Q : PerfectMatching V) (a a' : V) : Prop :=
  (Q.mate * M.mate).SameCycle a a' ∨
    ∃ w, ¬(M.toGraph ⊔ Q.toGraph).Reachable a w ∧ ¬(M.toGraph ⊔ Q.toGraph).Reachable a' w

/-- **Lemma K1** (`sl5-kill.md` §2; archive Theorem 11.1; `sl5-contra.md` Remark O5;
Hannenhalli and Pevzner 1999, Lemma 1), the direction the barrier uses. If `a ≠ a′` lie on
distinct edges of `M` and have the same signature under `Q`, the 2-switch is not Hamiltonian
with `Q`. -/
theorem not_ham_twoSwitch_of_sameSig [Finite V] [DecidableEq V]
    (M Q : PerfectMatching V) {a a' : V} (haa : a ≠ a')
    (ha' : a' ≠ M.mate a) (h : SameSig M Q a a') : ¬Ham (twoSwitch M a a') Q := by
  rcases h with h | ⟨w, h1, h2⟩
  · exact not_ham_twoSwitch_of_sameCycle M Q haa ha' h
  · exact not_ham_twoSwitch_of_unreachable M Q h1 h2

/-- `M ∪ Q` has at least three cycles, so the signature under `Q` is `∗` (`sl5-kill.md` §1). -/
def ManyCycles (M Q : PerfectMatching V) : Prop :=
  ∃ x y z, ¬(M.toGraph ⊔ Q.toGraph).Reachable x y ∧ ¬(M.toGraph ⊔ Q.toGraph).Reachable x z ∧
    ¬(M.toGraph ⊔ Q.toGraph).Reachable y z

instance [Fintype V] [DecidableEq V] (M Q : PerfectMatching V) :
    Decidable (ManyCycles M Q) :=
  inferInstanceAs (Decidable (∃ x y z, ¬(M.toGraph ⊔ Q.toGraph).Reachable x y ∧
    ¬(M.toGraph ⊔ Q.toGraph).Reachable x z ∧ ¬(M.toGraph ⊔ Q.toGraph).Reachable y z))

/-- A factor with three or more cycles carries no information (`sl5-kill.md` §1 and Lemma K1,
case `c(σ) ≥ 3`): every pair has the same signature. -/
theorem sameSig_of_manyCycles {M Q : PerfectMatching V} (h : ManyCycles M Q) (a a' : V) :
    SameSig M Q a a' := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h
  refine Or.inr ?_
  by_contra hno
  have hcov : ∀ u, (M.toGraph ⊔ Q.toGraph).Reachable a u ∨
      (M.toGraph ⊔ Q.toGraph).Reachable a' u := by
    intro u
    by_contra hu
    push Not at hu
    exact hno ⟨u, hu.1, hu.2⟩
  have key : ∀ s p q, (M.toGraph ⊔ Q.toGraph).Reachable s p →
      (M.toGraph ⊔ Q.toGraph).Reachable s q → (M.toGraph ⊔ Q.toGraph).Reachable p q :=
    fun _ _ _ h1 h2 ↦ h1.symm.trans h2
  rcases hcov x with hx | hx <;> rcases hcov y with hy | hy <;> rcases hcov z with hz | hz <;>
    first
    | exact hxy (key _ _ _ hx hy)
    | exact hxz (key _ _ _ hx hz)
    | exact hyz (key _ _ _ hy hz)

/-- `Φ` reversed: if `Mv` and `Mv′` share a `Φ`-orbit, so do `v` and `v′`, since `M` conjugates
`Φ = Q M` to `Φ⁻¹` (`sl5-contra.md` Remark O5). This is `sameCycle_mate_right_iff` of the bridge,
ham-spin `core/Pairing/InvolutionProduct.lean` (fe1f6bf). -/
theorem sameCycle_of_sameCycle_mate (M Q : PerfectMatching V) {v v' : V}
    (h : (Q.mate * M.mate).SameCycle (M.mate v) (M.mate v')) :
    (Q.mate * M.mate).SameCycle v v' :=
  (sameCycle_mate_right_iff Q M).mp h

/-- If `M ∪ Q` is one cycle, every vertex lies in the `Φ`-orbit of `a₀` or of `M a₀`'s partner
side: `Φ` has the two orbits `O` and `M(O)` (`sl5-kill.md` §1, `Φ_σ` has `2c(σ)` orbits). This is
`ham_iff_forall_sameCycle` of the bridge, ham-spin `core/Pairing/InvolutionProduct.lean`
(fe1f6bf), with `Q u = Φ (M u)`. -/
theorem sameCycle_or_of_ham {M Q : PerfectMatching V} (hH : Ham M Q) (a₀ u : V) :
    (Q.mate * M.mate).SameCycle a₀ u ∨ (Q.mate * M.mate).SameCycle a₀ (M.mate u) := by
  have h : Q.mate u = (Q.mate * M.mate) (M.mate u) := by rw [Equiv.Perm.mul_apply, mate_mate]
  rw [← Equiv.Perm.sameCycle_apply_right (y := M.mate u), ← h]
  exact ((ham_iff_forall_sameCycle Q M).mp ((ham_comm M Q).mp hH)).2 a₀ u

open Classical in
/-- The one-bit signature of `v` under `Q` with base point `a₀` (`sl5-kill.md` §1): whether `v`
is in the `Φ`-orbit of `a₀` when `M ∪ Q` is one cycle, and whether `v` is in the cycle of `a₀`
otherwise. -/
noncomputable def sigBit (M Q : PerfectMatching V) (a₀ v : V) : Bool :=
  if Ham M Q then decide ((Q.mate * M.mate).SameCycle a₀ v)
  else decide ((M.toGraph ⊔ Q.toGraph).Reachable a₀ v)

/-- Equal bits give equal signatures (`sl5-kill.md` §1 and Theorem K1(a): each factor with
`c ≤ 2` splits the tail into at most two classes). -/
theorem sameSig_of_sigBit_eq {M Q : PerfectMatching V} {a₀ v v' : V}
    (h : sigBit M Q a₀ v = sigBit M Q a₀ v') : SameSig M Q v v' := by
  unfold sigBit at h
  split_ifs at h with hH
  · rw [decide_eq_decide] at h
    refine Or.inl ?_
    by_cases hv : (Q.mate * M.mate).SameCycle a₀ v
    · exact hv.symm.trans (h.mp hv)
    · have hv' : ¬(Q.mate * M.mate).SameCycle a₀ v' := fun h' ↦ hv (h.mpr h')
      have h1 := (sameCycle_or_of_ham hH a₀ v).resolve_left hv
      have h2 := (sameCycle_or_of_ham hH a₀ v').resolve_left hv'
      exact sameCycle_of_sameCycle_mate M Q (h1.symm.trans h2)
  · rw [decide_eq_decide] at h
    refine Or.inr ?_
    by_cases hv : (M.toGraph ⊔ Q.toGraph).Reachable a₀ v
    · have hv' := h.mp hv
      obtain ⟨w, hw⟩ : ∃ w, ¬(M.toGraph ⊔ Q.toGraph).Reachable a₀ w := by
        by_contra hall
        push Not at hall
        have : Nonempty V := ⟨a₀⟩
        exact hH (SimpleGraph.Connected.mk fun x y ↦ (hall x).symm.trans (hall y))
      exact ⟨w, fun h' ↦ hw (hv.trans h'), fun h' ↦ hw (hv'.trans h')⟩
    · have hv' : ¬(M.toGraph ⊔ Q.toGraph).Reachable a₀ v' := fun h' ↦ hv (h.mpr h')
      exact ⟨a₀, fun h' ↦ hv h'.symm, fun h' ↦ hv' h'.symm⟩

/-- **Theorem K1(a)** (`sl5-kill.md` §2; archive Corollary 11.2; the separating-system bound of
Rényi 1961 and Katona 1966). Let `E` be a set of endpoints of distinct edges of `M`
(`M a ∉ E` for `a ∈ E`), `𝓕` a finite family of factors `F i`, and `𝓕₁₂` its members without
three separate cycles with `M`. If `2^|𝓕₁₂| < |E|`, some two edges of `E` have a 2-switch that
no member of `𝓕` makes Hamiltonian. -/
theorem exists_uncovered_twoSwitch [Fintype V] [DecidableEq V] {ι : Type*}
    (M : PerfectMatching V) (F : ι → PerfectMatching V)
    (𝓕 : Finset ι) (E : Finset V) (hE : ∀ a ∈ E, M.mate a ∉ E)
    (hcard : 2 ^ (𝓕.filter fun i ↦ ¬ManyCycles M (F i)).card < E.card) :
    ∃ a ∈ E, ∃ a' ∈ E, a ≠ a' ∧ a' ≠ M.mate a ∧ ∀ i ∈ 𝓕, ¬Ham (twoSwitch M a a') (F i) := by
  classical
  obtain ⟨a₀, -⟩ : E.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _)
    (lt_of_le_of_lt (Nat.one_le_two_pow) hcard))
  set 𝓕₁₂ := 𝓕.filter fun i ↦ ¬ManyCycles M (F i) with h𝓕
  have hcodom : (Finset.univ : Finset (𝓕₁₂ → Bool)).card = 2 ^ 𝓕₁₂.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  obtain ⟨a, ha, a', ha', hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (hcodom ▸ hcard) (f := fun v (i : 𝓕₁₂) ↦ sigBit M (F i) a₀ v)
    (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
  have hMa : a' ≠ M.mate a := fun h ↦ hE a ha (h ▸ ha')
  refine ⟨a, ha, a', ha', hne, hMa, fun i hi ↦ not_ham_twoSwitch_of_sameSig M (F i) hne hMa ?_⟩
  by_cases hmc : ManyCycles M (F i)
  · exact sameSig_of_manyCycles hmc a a'
  · exact sameSig_of_sigBit_eq (congrFun hfeq ⟨i, Finset.mem_filter.mpr ⟨hi, hmc⟩⟩)

/-- **Theorem K1(b), the class (X2)** (`sl5-kill.md` §2 and §5). Suppose an argument reads, for
every member of `𝓕`, whether two edges of `E` have the same signature off a per-edge type
`τ : V → 𝒯`, so that equal types give equal signatures. If `|𝒯| < |E|`, some 2-switch of two
edges of `E` is `𝓕`-uncovered, so "every 2-core in `E` is `𝓕`-covered" is false. -/
theorem exists_uncovered_twoSwitch_of_types [Finite V] [DecidableEq V] {ι 𝒯 : Type*}
    [Fintype 𝒯] (M : PerfectMatching V)
    (F : ι → PerfectMatching V) (𝓕 : Finset ι) (E : Finset V) (hE : ∀ a ∈ E, M.mate a ∉ E)
    (τ : V → 𝒯) (hτ : ∀ i ∈ 𝓕, ∀ a ∈ E, ∀ a' ∈ E, τ a = τ a' → SameSig M (F i) a a')
    (hcard : Fintype.card 𝒯 < E.card) :
    ∃ a ∈ E, ∃ a' ∈ E, a ≠ a' ∧ a' ≠ M.mate a ∧ ∀ i ∈ 𝓕, ¬Ham (twoSwitch M a a') (F i) := by
  classical
  obtain ⟨a, ha, a', ha', hne, hτeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := Finset.univ) (by rwa [Finset.card_univ]) (f := τ)
    (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
  have hMa : a' ≠ M.mate a := fun h ↦ hE a ha (h ▸ ha')
  exact ⟨a, ha, a', ha', hne, hMa, fun i hi ↦
    not_ham_twoSwitch_of_sameSig M (F i) hne hMa (hτ i hi a ha a' ha' hτeq)⟩

/-- Every perfect matching `N` of `W` has a set of one endpoint from each edge: `2|E| = |W|` and
`N a ∉ E` for `a ∈ E` (`sl5-kill.md` §1, "for each tail edge fix an endpoint `a(e)`"). -/
theorem exists_endpoints {W : Type*} [Fintype W] (N : PerfectMatching W) :
    ∃ E : Finset W, 2 * E.card = Fintype.card W ∧ ∀ a ∈ E, N.mate a ∉ E := by
  classical
  set f := Fintype.equivFin W
  set E := Finset.univ.filter fun v ↦ f v < f (N.mate v) with hE
  set E' := Finset.univ.filter fun v ↦ f (N.mate v) < f v with hE'
  have hmemE : ∀ v, v ∈ E ↔ f v < f (N.mate v) := fun v ↦ by simp [hE]
  have hmemE' : ∀ v, v ∈ E' ↔ f (N.mate v) < f v := fun v ↦ by simp [hE']
  have hlt : ∀ v, f v < f (N.mate v) ∨ f (N.mate v) < f v := fun v ↦
    lt_or_gt_of_ne fun h ↦ N.mate_ne v (f.injective h).symm
  have hEE' : E.card = E'.card := by
    refine Finset.card_nbij' N.mate N.mate (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v _ ↦ mate_mate N v)
      (fun v _ ↦ mate_mate N v)
    · rw [Finset.mem_coe, hmemE] at hv
      rw [Finset.mem_coe, hmemE', mate_mate]
      exact hv
    · rw [Finset.mem_coe, hmemE'] at hv
      rw [Finset.mem_coe, hmemE, mate_mate]
      exact hv
  have hdisj : Disjoint E E' := Finset.disjoint_left.mpr fun v hv hv' ↦
    lt_asymm ((hmemE v).mp hv) ((hmemE' v).mp hv')
  have hunion : E ∪ E' = Finset.univ := Finset.eq_univ_of_forall fun v ↦ by
    rcases hlt v with h | h
    · exact Finset.mem_union_left _ ((hmemE v).mpr h)
    · exact Finset.mem_union_right _ ((hmemE' v).mpr h)
  refine ⟨E, ?_, fun a ha hNa ↦ ?_⟩
  · have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ] at h
    omega
  · have h1 := (hmemE a).mp ha
    have h2 := (hmemE _).mp hNa
    rw [mate_mate] at h2
    exact lt_asymm h1 h2

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- A 2-switch of a completion `M` of the tail `T` is within `2` of `T` (`sl5-kill.md` §2,
`M₁ = (T ∖ {e, e′}) ∪ R₁`). -/
theorem tailDist_twoSwitch_le {G : Finset (Vertex m)}
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (M : PerfectMatching (Vertex m))
    (hM : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u) (a a' : Vertex m) :
    tailDist (twoSwitch M a a') T ≤ 2 := by
  have h := two_mul_tailDist (twoSwitch M a a') T
  have hle : (Finset.univ.filter fun u : (Gᶜ : Finset (Vertex m)) ↦
      (T.mate u : Vertex m) ≠ (twoSwitch M a a').mate u).card ≤
      ({a, M.mate a, a', M.mate a'} : Finset (Vertex m)).card := by
    refine Finset.card_le_card_of_injOn (fun u ↦ (u : Vertex m)) (fun u hu ↦ ?_)
      (fun u _ w _ h ↦ Subtype.ext h)
    have hne := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    rw [Finset.mem_coe]
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hne (by rw [twoSwitch_mate_of_ne M hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2, hM u])
  have h4 := Finset.card_le_four (a := a) (b := M.mate a) (c := a') (d := M.mate a')
  omega

/-- **The class (X1)** (`sl5-kill.md` Theorem K1(a) and §5 (X1); Rényi 1961, Katona 1966). Let
`T` be a tail of a six-vertex gadget, `M` any completion of `T`, and `𝓕` any set of factors, of
any height. If `2^|𝓕₁₂| < m - 3`, where `𝓕₁₂` are the members without three separate cycles
with `M`, some perfect matching within `2` of `T` is `𝓕`-uncovered: a 2-switch of two tail edges
with equal `𝓕`-signatures. -/
theorem exists_uncovered_near_tail {G : Finset (Vertex m)} (hG : G.card = 6)
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (M : PerfectMatching (Vertex m))
    (hM : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u) (𝓕 : Finset (ZMod (2 * m - 1)))
    (hcard : 2 ^ (𝓕.filter fun t ↦ ¬ManyCycles M (factor m t)).card < m - 3) :
    ∃ P : PerfectMatching (Vertex m), tailDist P T ≤ 2 ∧ ∀ t ∈ 𝓕, ¬Ham P (factor m t) := by
  obtain ⟨-, hU⟩ := card_compl_gadget hG
  obtain ⟨E₀, hE₀, hE₀N⟩ := exists_endpoints T
  rw [Fintype.card_coe, hU] at hE₀
  set E := E₀.map (Function.Embedding.subtype _) with hE
  have hEcard : E.card = m - 3 := by rw [hE, Finset.card_map]; omega
  have hEM : ∀ a ∈ E, M.mate a ∉ E := by
    intro a ha hMa
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨w, hw, hwu⟩ := Finset.mem_map.mp hMa
    have hwu' : (w : Vertex m) = M.mate u := hwu
    rw [hM u] at hwu'
    exact hE₀N u hu (by rwa [show T.mate u = w from Subtype.ext hwu'.symm])
  obtain ⟨a, -, a', -, -, -, hunc⟩ := exists_uncovered_twoSwitch M (factor m) 𝓕 E hEM
    (by rwa [hEcard])
  exact ⟨twoSwitch M a a', tailDist_twoSwitch_le T M hM a a', hunc⟩

/-- **(X1), relativization form** (`sl5-kill.md` Theorem K1(a) and §5 (X1); `sl5-contra.md`
Corollary O3). Under the hypothesis of `exists_uncovered_near_tail`, the `𝓕`-relativized
statement "every perfect matching that no member of `𝓕` makes Hamiltonian is at least `3` from
`T`" is false. So no `𝓕`-relativizing argument proves `ρ(T) ≥ 3`, nor `ρ(twoarc(p)) ≥ 6`. -/
theorem not_relativized_rho_ge_three {G : Finset (Vertex m)} (hG : G.card = 6)
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (M : PerfectMatching (Vertex m))
    (hM : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u) (𝓕 : Finset (ZMod (2 * m - 1)))
    (hcard : 2 ^ (𝓕.filter fun t ↦ ¬ManyCycles M (factor m t)).card < m - 3) :
    ¬∀ P : PerfectMatching (Vertex m), (∀ t ∈ 𝓕, ¬Ham P (factor m t)) → 3 ≤ tailDist P T := by
  intro hall
  obtain ⟨P, hd, hP⟩ := exists_uncovered_near_tail hG T M hM 𝓕 hcard
  have := hall P hP
  omega

/-- **(X1), size form** (`sl5-kill.md` Theorem K1(a): every `𝓕` with `|𝓕| < log₂(m - 3)` fails).
If `2^|𝓕| < m - 3`, no `𝓕`-relativizing argument proves `ρ(T) ≥ 3` for any tail `T` of a
six-vertex gadget. -/
theorem not_relativized_rho_ge_three_of_card {G : Finset (Vertex m)} (hG : G.card = 6)
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (𝓕 : Finset (ZMod (2 * m - 1)))
    (hcard : 2 ^ 𝓕.card < m - 3) :
    ¬∀ P : PerfectMatching (Vertex m), (∀ t ∈ 𝓕, ¬Ham P (factor m t)) → 3 ≤ tailDist P T := by
  obtain ⟨M, hM⟩ := exists_extends (by rw [card_vertex]; exact even_two_mul m) T
  refine not_relativized_rho_ge_three hG T M hM 𝓕 (lt_of_le_of_lt ?_ hcard)
  exact Nat.pow_le_pow_right (by norm_num) (Finset.card_filter_le 𝓕 _)

/-- **Theorem K1(c)** (`sl5-kill.md` §2; (N1) of `sl5-contra.md` §4). If `ρ(T) ≥ 3`, then for
every two tail vertices `a ≠ a′` on distinct edges of a completion `M`, some factor separates
their signatures. -/
theorem exists_not_sameSig_of_rho {G : Finset (Vertex m)}
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (M : PerfectMatching (Vertex m))
    (hM : ∀ u : (Gᶜ : Finset (Vertex m)), M.mate u = T.mate u)
    (hρ : ∀ P : PerfectMatching (Vertex m), IsZeroState (factor m) P → 3 ≤ tailDist P T)
    {a a' : Vertex m} (haa : a ≠ a') (ha' : a' ≠ M.mate a) :
    ∃ t, ¬SameSig M (factor m t) a a' := by
  by_contra hall
  push Not at hall
  have h := hρ (twoSwitch M a a') fun t ↦ not_ham_twoSwitch_of_sameSig M _ haa ha' (hall t)
  have := tailDist_twoSwitch_le T M hM a a'
  omega

end RoundRobin.Canonical

end Pairing
