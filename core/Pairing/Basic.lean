import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Shared objects (sketch §0)

* `PerfectMatching V`, the perfect matchings of the complete graph on `V`, stored as
  fixed-point-free involutions. On `V = Fin (2 * n)` this is `𝓜_n`.
* `Ham P Q`, the statement that `P ∪ Q` is one cycle. A common edge is a doubled
  `2`-cycle, so it closes the cycle on its own. Since `P ∪ Q` is `2`-regular this is
  connectivity of the union graph.
* `H`, the `𝔽₂` matrix of `Ham`. Its rows are the `r_P`.
* `W V`, the span of the rows, and `ρ`, the action `(ρ σ f) Q = f (σ⁻¹ • Q)`.
* `Wsub`, the subrepresentation carried by `W V`, and `ρW`, the restricted action.
* `CKNUpperBound n`, the bound `rank H ≤ 2 ^ (n - 1)`. It is proved as `cknUpperBound` in
  `Clifford.Dimension`, together with `rank H = 2 ^ (n - 1)`.
-/

namespace Pairing

/-- The field with two elements. -/
abbrev F₂ := ZMod 2

/-- A perfect matching of the complete graph on `V`, as a fixed-point-free involution. -/
@[ext]
structure PerfectMatching (V : Type*) where
  /-- The partner of each vertex. -/
  mate : Equiv.Perm V
  mate_mate : ∀ v, mate (mate v) = v
  mate_ne : ∀ v, mate v ≠ v

namespace PerfectMatching

variable {V : Type*}

attribute [simp] mate_mate

/-- Bundled perfect matchings agree with fixed-point-free involutions of `V`. -/
def equivSubtype :
    PerfectMatching V ≃ {p : Equiv.Perm V // (∀ v, p (p v) = v) ∧ ∀ v, p v ≠ v} where
  toFun P := ⟨P.mate, P.mate_mate, P.mate_ne⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype V] [DecidableEq V] : DecidableEq (PerfectMatching V) :=
  fun P Q ↦ decidable_of_iff (P.mate = Q.mate) PerfectMatching.ext_iff.symm

instance [Fintype V] [DecidableEq V] : Fintype (PerfectMatching V) :=
  Fintype.ofEquiv _ equivSubtype.symm

/-- `S_V` acts on matchings by conjugation, `σ • P = σ P σ⁻¹`. -/
instance : MulAction (Equiv.Perm V) (PerfectMatching V) where
  smul σ P :=
    { mate := σ * P.mate * σ⁻¹
      mate_mate := by simp
      mate_ne := by
        intro v h
        apply P.mate_ne (σ⁻¹ v)
        simpa using congrArg (⇑σ⁻¹) h }
  one_smul P := by ext v; rfl
  mul_smul σ τ P := by ext v; rfl

@[simp]
theorem smul_mate (σ : Equiv.Perm V) (P : PerfectMatching V) (v : V) :
    (σ • P).mate v = σ (P.mate (σ⁻¹ v)) :=
  rfl

/-- The edge set of `P` as a simple graph. -/
def toGraph (P : PerfectMatching V) : SimpleGraph V where
  Adj v w := P.mate v = w
  symm := ⟨fun v w h ↦ by rw [← h, P.mate_mate]⟩
  loopless := ⟨fun v ↦ P.mate_ne v⟩

@[simp]
theorem toGraph_adj (P : PerfectMatching V) (v w : V) : P.toGraph.Adj v w ↔ P.mate v = w :=
  Iff.rfl

instance [DecidableEq V] (P : PerfectMatching V) : DecidableRel P.toGraph.Adj :=
  fun v w ↦ inferInstanceAs (Decidable (P.mate v = w))

/-- `Ham P Q` holds iff the multigraph `P ∪ Q` is a single cycle. -/
def Ham (P Q : PerfectMatching V) : Prop :=
  (P.toGraph ⊔ Q.toGraph).Connected

instance [Fintype V] [DecidableEq V] (P Q : PerfectMatching V) : Decidable (Ham P Q) :=
  inferInstanceAs (Decidable (P.toGraph ⊔ Q.toGraph).Connected)

theorem ham_comm (P Q : PerfectMatching V) : Ham P Q ↔ Ham Q P := by
  rw [Ham, Ham, sup_comm]

/-- Relabelling both matchings by `σ` is an isomorphism of union graphs. -/
def unionIso (σ : Equiv.Perm V) (P Q : PerfectMatching V) :
    (P.toGraph ⊔ Q.toGraph) ≃g ((σ • P).toGraph ⊔ (σ • Q).toGraph) where
  toEquiv := σ
  map_rel_iff' := by simp

theorem ham_smul (σ : Equiv.Perm V) (P Q : PerfectMatching V) :
    Ham (σ • P) (σ • Q) ↔ Ham P Q :=
  (unionIso σ P Q).connected_iff.symm

/-- Swapping the two ends of an edge of `P` fixes `P`. -/
theorem swap_mate_smul [DecidableEq V] (P : PerfectMatching V) (x : V) :
    Equiv.swap x (P.mate x) • P = P := by
  ext v
  rw [smul_mate, Equiv.swap_inv]
  by_cases hx : v = x
  · subst hx
    simp
  by_cases hy : v = P.mate x
  · subst hy
    simp
  have h1 : P.mate v ≠ x := fun h ↦ hy (by rw [← h, mate_mate])
  have h2 : P.mate v ≠ P.mate x := fun h ↦ hx (P.mate.injective h)
  rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- A vertex set closed under both matchings and missing some vertex blocks `Ham`. -/
theorem not_ham_of_closed (X Y : PerfectMatching V) (B : Set V) (hX : ∀ v ∈ B, X.mate v ∈ B)
    (hY : ∀ v ∈ B, Y.mate v ∈ B) {u w : V} (hu : u ∈ B) (hw : w ∉ B) : ¬Ham X Y := by
  intro h
  obtain ⟨p⟩ := h.preconnected u w
  have key : ∀ {a b : V} (_ : (X.toGraph ⊔ Y.toGraph).Walk a b), a ∈ B → b ∈ B := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hadj _ ih =>
      intro ha
      rcases (SimpleGraph.sup_adj _ _ _ _).mp hadj with h' | h'
      · exact ih (h' ▸ hX _ ha)
      · exact ih (h' ▸ hY _ ha)
  exact hw (key p hu)

section Congr

variable {V' : Type*}

/-- Transport of matchings along a bijection `e : V ≃ V'`, `X ↦ e X e⁻¹`. -/
def congr (e : V ≃ V') : PerfectMatching V ≃ PerfectMatching V' where
  toFun X :=
    { mate := e.permCongr X.mate
      mate_mate := by simp
      mate_ne := fun v h ↦ X.mate_ne (e.symm v) (by simpa using congrArg e.symm h) }
  invFun Y :=
    { mate := e.symm.permCongr Y.mate
      mate_mate := by simp
      mate_ne := fun v h ↦ Y.mate_ne (e v) (by simpa using congrArg e h) }
  left_inv X := by ext v; simp
  right_inv Y := by ext v; simp

@[simp]
theorem congr_mate (e : V ≃ V') (X : PerfectMatching V) (v : V') :
    (congr e X).mate v = e (X.mate (e.symm v)) :=
  rfl

/-- `e` is an isomorphism of union graphs. -/
def congrUnionIso (e : V ≃ V') (X Y : PerfectMatching V) :
    (X.toGraph ⊔ Y.toGraph) ≃g ((congr e X).toGraph ⊔ (congr e Y).toGraph) where
  toEquiv := e
  map_rel_iff' := by simp

theorem ham_congr (e : V ≃ V') (X Y : PerfectMatching V) :
    Ham (congr e X) (congr e Y) ↔ Ham X Y :=
  (congrUnionIso e X Y).connected_iff.symm

theorem permCongr_inv_apply (e : V ≃ V') (σ : Equiv.Perm V) (v : V') :
    (e.permCongr σ)⁻¹ v = e (σ⁻¹ (e.symm v)) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  simp

/-- Transport intertwines the two relabelling actions. -/
theorem congr_smul (e : V ≃ V') (σ : Equiv.Perm V) (X : PerfectMatching V) :
    congr e (σ • X) = e.permCongr σ • congr e X := by
  ext v
  simp [permCongr_inv_apply]

end Congr

open Equiv in
theorem cycleType_mate {n : ℕ} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2 * n)
    (P : PerfectMatching V) : P.mate.cycleType = Multiset.replicate n 2 := by
  have hpow : P.mate ^ 2 = 1 := by
    ext v
    simp [sq]
  have hall : ∀ c ∈ P.mate.cycleType, c = 2 :=
    (Perm.pow_prime_eq_one_iff (p := 2)).mp hpow
  have hrep : P.mate.cycleType = Multiset.replicate P.mate.cycleType.card 2 :=
    Multiset.eq_replicate_card.mpr hall
  have hsupp : P.mate.support = Finset.univ := by
    ext v
    simp [Perm.mem_support, P.mate_ne v]
  have hsum : P.mate.cycleType.sum = 2 * n := by
    rw [Perm.sum_cycleType, hsupp, Finset.card_univ, hV]
  have hcard : P.mate.cycleType.card * 2 = 2 * n := by
    calc
      P.mate.cycleType.card * 2 = (Multiset.replicate P.mate.cycleType.card 2).sum := by simp
      _ = P.mate.cycleType.sum := congrArg Multiset.sum hrep.symm
      _ = 2 * n := hsum
  rw [hrep]
  congr 1
  omega

open Equiv in
/-- A permutation of cycle type `2^n` on `2n` points is a perfect matching. -/
def ofCycleType {n : ℕ} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2 * n)
    (g : Perm V) (hg : g.cycleType = Multiset.replicate n 2) : PerfectMatching V where
  mate := g
  mate_mate v := by
    have hpow : g ^ 2 = 1 := by
      apply (Perm.pow_prime_eq_one_iff (p := 2)).mpr
      intro c hc
      rw [hg] at hc
      exact Multiset.eq_of_mem_replicate hc
    simpa [sq] using Perm.congr_fun hpow v
  mate_ne v hv := by
    have hsupp : g.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← Perm.sum_cycleType, hg, hV]
      simp [mul_comm]
    exact Perm.mem_support.mp (hsupp ▸ Finset.mem_univ v) hv

/-- `|𝓜_n| = (2n - 1)!!`. -/
theorem card_eq_doubleFactorial {n : ℕ} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 2 * n) :
    Fintype.card (PerfectMatching V) = Nat.doubleFactorial (2 * n - 1) := by
  have he : PerfectMatching V ≃ {g : Equiv.Perm V // g.cycleType = Multiset.replicate n 2} :=
    { toFun P := ⟨P.mate, cycleType_mate hV P⟩
      invFun g := ofCycleType hV g.1 g.2
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr he, Fintype.card_subtype, Equiv.Perm.card_of_cycleType]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hV]
  have hcond : (Multiset.replicate n 2).sum ≤ Fintype.card V ∧
      ∀ a ∈ Multiset.replicate n 2, 2 ≤ a :=
    ⟨by simp [hV, mul_comm], fun a ha ↦ (Multiset.eq_of_mem_replicate ha).symm ▸ le_rfl⟩
  rw [ite_eq_left hcond]
  have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * n - 1)
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at hfac
  simp only [Multiset.sum_replicate, hV, smul_eq_mul, mul_comm n 2, Nat.sub_self,
    Nat.factorial_zero, one_mul, Multiset.prod_replicate, Multiset.toFinset_replicate,
    hn.ne', ite_false, Finset.prod_singleton, Multiset.count_replicate_self]
  rw [hfac, Nat.doubleFactorial_two_mul, mul_comm (2 ^ n),
    Nat.mul_div_cancel_left _ (by positivity)]

/-- `S_V` acts transitively on perfect matchings. -/
theorem exists_smul_eq {n : ℕ} [Fintype V] (hV : Fintype.card V = 2 * n)
    (P Q : PerfectMatching V) : ∃ c : Equiv.Perm V, c • P = Q := by
  classical
  have h : IsConj P.mate Q.mate :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_mate hV, cycleType_mate hV])
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c, PerfectMatching.ext hc⟩

end PerfectMatching

open PerfectMatching

variable {V : Type*}

/-- The permutation representation on `𝔽₂^𝓜`, `(ρ σ f) Q = f (σ⁻¹ • Q)`. -/
def ρ : Representation F₂ (Equiv.Perm V) (PerfectMatching V → F₂) where
  toFun σ := LinearMap.funLeft F₂ F₂ (σ⁻¹ • ·)
  map_one' := LinearMap.ext fun _ ↦ funext fun _ ↦ by simp [LinearMap.funLeft_apply]
  map_mul' σ τ := LinearMap.ext fun _ ↦ funext fun _ ↦ by
    simp [LinearMap.funLeft_apply, mul_smul]

@[simp]
theorem ρ_apply (σ : Equiv.Perm V) (f : PerfectMatching V → F₂) (Q : PerfectMatching V) :
    ρ σ f Q = f (σ⁻¹ • Q) :=
  rfl

variable [Fintype V] [DecidableEq V]

/-- The Hamiltonian compatibility matrix, `H P Q = 1` iff `P ∪ Q` is one cycle. -/
def H : Matrix (PerfectMatching V) (PerfectMatching V) F₂ :=
  Matrix.of fun P Q ↦ if Ham P Q then 1 else 0

theorem H_apply (P Q : PerfectMatching V) : H P Q = if Ham P Q then 1 else 0 :=
  rfl

theorem H_comm (P Q : PerfectMatching V) : H P Q = H Q P := by
  simp only [H_apply, ham_comm P Q]

/-- `H[σP, σQ] = H[P, Q]`. -/
theorem H_smul (σ : Equiv.Perm V) (P Q : PerfectMatching V) : H (σ • P) (σ • Q) = H P Q := by
  simp only [H_apply, ham_smul]

/-- `H` is invariant under transport along `e : V ≃ V'`. -/
theorem H_congr {V' : Type*} [Fintype V'] [DecidableEq V'] (e : V ≃ V')
    (P Q : PerfectMatching V) : H (congr e P) (congr e Q) = H P Q := by
  simp only [H_apply, ham_congr]

variable (V) in
/-- `W_n`, the `𝔽₂`-span of the rows `r_P = H P` of `H`. -/
def W : Submodule F₂ (PerfectMatching V → F₂) :=
  Submodule.span F₂ (Set.range H.row)

theorem row_mem_W (P : PerfectMatching V) : H P ∈ W V :=
  Submodule.subset_span ⟨P, rfl⟩

/-- `dim W_n = rank_{𝔽₂} H`. -/
theorem finrank_W : Module.finrank F₂ (W V) = (H (V := V)).rank :=
  (Matrix.rank_eq_finrank_span_row _).symm

/-- `ρ(σ) r_P = r_{σP}`. -/
theorem ρ_row (σ : Equiv.Perm V) (P : PerfectMatching V) : ρ σ (H P) = H (σ • P) := by
  funext Q
  rw [ρ_apply, ← H_smul σ P (σ⁻¹ • Q), smul_inv_smul]

theorem W_le_comap_ρ (σ : Equiv.Perm V) : W V ≤ (W V).comap (ρ σ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, rfl⟩
  simpa [Matrix.row, ρ_row] using row_mem_W (σ • P)

/-- `W_n` as an `𝔽₂ S_V`-subrepresentation of `ρ`. -/
def Wsub : Subrepresentation (ρ (V := V)) where
  toSubmodule := W V
  apply_mem_toSubmodule σ _ hf := W_le_comap_ρ σ hf

/-- The action of `S_V` on `W_n`. -/
def ρW : Representation F₂ (Equiv.Perm V) (W V) :=
  (Wsub (V := V)).toRepresentation

@[simp]
theorem ρW_apply_coe (σ : Equiv.Perm V) (f : W V) : (ρW σ f : PerfectMatching V → F₂) = ρ σ f :=
  rfl

/-- The row `r_P` as a point of `W`. -/
def rowW (P : PerfectMatching V) : W V :=
  ⟨H P, row_mem_W P⟩

@[simp]
theorem coe_rowW (P : PerfectMatching V) : (rowW P : PerfectMatching V → F₂) = H P :=
  rfl

theorem ρW_rowW (σ : Equiv.Perm V) (P : PerfectMatching V) : ρW σ (rowW P) = rowW (σ • P) :=
  Subtype.ext (ρ_row σ P)

/-- The rows span `W`. -/
theorem span_rowW : Submodule.span F₂ (Set.range (rowW (V := V))) = ⊤ := by
  apply Submodule.map_injective_of_injective (W V).injective_subtype
  rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The upper half of the Cygan, Kratsch, Nederlof rank formula, proved as `cknUpperBound`. -/
def CKNUpperBound (n : ℕ) : Prop :=
  (H (V := Fin (2 * n))).rank ≤ 2 ^ (n - 1)

end Pairing
