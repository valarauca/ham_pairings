import Clifford.Contraction
import Pairing.RoundRobin

/-!
# Canonical suppression (COD-157)

`P` is a perfect matching of `V` and the boundary `A ⊆ V` is a union of edges of `P`. The edges
of `P` off `A` form the partial matching `E = edgesOff P A`, which leaves exactly `A` uncovered.
A matching `Z` of `V` contains `E` iff it agrees with `P` off `A` (`edgesOff_subset_iff`).

* `restrict_glue`, `glueEquiv` : `X ↦ X ∪ P'` is a bijection from `PM(A)` onto the matchings
  that contain `E`, with inverse `Z ↦ Z|_A`.
* `AvoidsContexts F P A hA X` : each `F t` either closes a cycle with `P'` or has derived
  context `κ_t = contract P (F t) A hA` with `¬Ham X κ_t`.
* `isZeroState_glue_iff` : for any family `F`, `X ∪ P'` is a zero state iff `X` avoids every
  derived context.
* `zeroStateEquiv` : the zero states of `F` that contain `E` correspond to the `X ∈ PM(A)` that
  avoid every derived context.
* `card_boundary` : `|V| = 2m` and `|E| = m - 3 - K` give `|A| = 2K + 6`.
* `IsPartialMatching E`, `uncovered E` : a finset of pairwise disjoint non-loop edges and the
  vertices it leaves uncovered. `uncovered_edgesOff` : `edgesOff P A` leaves exactly `A`
  uncovered. `exists_edgesOff_eq` : on a vertex type of even size every partial matching is
  `edgesOff P (uncovered E)` for some `P`.
* `RoundRobin.Canonical.suppression` : the round-robin case on `V_m`, for every `m`.
  `RoundRobin.Canonical.suppression_of_isPartialMatching` states it for a partial matching `E`
  alone.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*}

section Glue

variable [DecidableEq V] (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- `X ∪ P'` maps `A` into `A`. -/
theorem glue_mate_mem (X : PerfectMatching A) (v : V) (hv : v ∈ A) :
    (glue P A hA X).mate v ∈ A := by
  rw [glue_mate_of_mem P A hA X hv]
  exact (X.mate ⟨v, hv⟩).2

/-- `(X ∪ P')|_A = X`, the converse of `glue_restrict`. -/
theorem restrict_glue (X : PerfectMatching A) :
    restrict (glue P A hA X) A (glue_mate_mem P A hA X) = X := by
  ext a
  exact glue_mate_coe P A hA X a

omit [DecidableEq V] in
include hA in
/-- A matching that agrees with `P` off `A` maps `A` into `A`. -/
theorem mate_mem_of_agree {Z : PerfectMatching V} (hZ : ∀ v ∉ A, Z.mate v = P.mate v) (v : V)
    (hv : v ∈ A) : Z.mate v ∈ A := by
  by_contra h
  have h' := hZ _ h
  rw [Z.mate_mate] at h'
  exact h ((mate_mem_iff P A hA _).mp (h' ▸ hv))

/-- A matching that agrees with `P` off `A` is `Z|_A ∪ P'`. -/
theorem glue_restrict_of_agree {Z : PerfectMatching V} (hZ : ∀ v ∉ A, Z.mate v = P.mate v) :
    glue P A hA (restrict Z A (mate_mem_of_agree P A hA hZ)) = Z := by
  ext v
  by_cases h : v ∈ A
  · rw [glue_mate_of_mem P A hA _ h]
    rfl
  · rw [glue_mate_of_notMem P A hA _ h, hZ v h]

/-- `X ↦ X ∪ P'` is a bijection from `PM(A)` onto the matchings that agree with `P` off `A`. -/
def glueEquiv : PerfectMatching A ≃ {Z : PerfectMatching V // ∀ v ∉ A, Z.mate v = P.mate v} where
  toFun X := ⟨glue P A hA X, fun _ h ↦ glue_mate_of_notMem P A hA X h⟩
  invFun Z := restrict Z.1 A (mate_mem_of_agree P A hA Z.2)
  left_inv := restrict_glue P A hA
  right_inv Z := Subtype.ext (glue_restrict_of_agree P A hA Z.2)

end Glue

section Edges

variable [Fintype V] [DecidableEq V] (P : PerfectMatching V) (A : Finset V)
  (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- `E`, the edges of `P` off `A`. -/
def edgesOff : Finset (Sym2 V) :=
  Aᶜ.image fun v ↦ s(v, P.mate v)

/-- A matching contains `E` iff it agrees with `P` off `A`. -/
theorem edgesOff_subset_iff (Z : PerfectMatching V) :
    (edgesOff P A : Set (Sym2 V)) ⊆ Z.toGraph.edgeSet ↔ ∀ v ∉ A, Z.mate v = P.mate v := by
  constructor
  · intro h v hv
    exact (SimpleGraph.mem_edgeSet _).mp
      (h (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_compl.mpr hv))))
  · intro h _ he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he)
    exact (SimpleGraph.mem_edgeSet _).mpr (h v (Finset.mem_compl.mp hv))

include hA in
/-- `E` has `|V \ A| / 2` edges. -/
theorem two_mul_card_edgesOff : 2 * (edgesOff P A).card = Aᶜ.card := by
  rw [edgesOff, Finset.card_eq_sum_card_image (fun v ↦ s(v, P.mate v)) Aᶜ,
    Finset.sum_const_nat (m := 2), mul_comm]
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  have hv' : v ∉ A := Finset.mem_compl.mp hv
  have hfib : {w ∈ Aᶜ | s(w, P.mate w) = s(v, P.mate v)} = {v, P.mate v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff]
    constructor
    · rintro ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hv', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨fun h ↦ hv' ((mate_mem_iff P A hA v).mp h), Or.inr ⟨rfl, P.mate_mate v⟩⟩
  rw [hfib, Finset.card_pair (P.mate_ne v).symm]

include hA in
/-- With `|V| = 2m` and `|E| = m - 3 - K`, the boundary has `|A| = 2K + 6`. -/
theorem card_boundary {m K : ℕ} (hV : Fintype.card V = 2 * m) (hK : K + 3 ≤ m)
    (hE : (edgesOff P A).card = m - 3 - K) : A.card = 2 * K + 6 := by
  have h1 := two_mul_card_edgesOff P A hA
  have h2 := Finset.card_compl A
  have h3 := A.card_le_univ
  omega

end Edges

section PartialMatching

variable [Fintype V] [DecidableEq V]

/-- `E` is a partial matching of `V`: no edge of `E` is a loop, and distinct edges of `E` share
no vertex. -/
def IsPartialMatching (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬e.IsDiag) ∧ ∀ e ∈ E, ∀ f ∈ E, ∀ v ∈ e, v ∈ f → e = f

/-- The vertices that `E` leaves uncovered. -/
def uncovered (E : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v ↦ ∀ e ∈ E, v ∉ e

/-- `v` is uncovered iff no edge of `E` contains it. -/
theorem mem_uncovered {E : Finset (Sym2 V)} {v : V} : v ∈ uncovered E ↔ ∀ e ∈ E, v ∉ e := by
  simp [uncovered]

/-- The edges of `P` off `A` are the `s(v, P v)` with `v ∉ A`. -/
theorem mem_edgesOff {P : PerfectMatching V} {A : Finset V} {e : Sym2 V} :
    e ∈ edgesOff P A ↔ ∃ v ∉ A, s(v, P.mate v) = e := by
  simp [edgesOff]

/-- `edgesOff P A` is a partial matching. -/
theorem isPartialMatching_edgesOff (P : PerfectMatching V) (A : Finset V) :
    IsPartialMatching (edgesOff P A) := by
  refine ⟨fun e he ↦ ?_, fun e he f hf x hxe hxf ↦ ?_⟩
  · obtain ⟨v, _, rfl⟩ := mem_edgesOff.mp he
    exact fun h ↦ P.mate_ne v (Sym2.mk_isDiag_iff.mp h).symm
  · obtain ⟨v, _, rfl⟩ := mem_edgesOff.mp he
    obtain ⟨w, _, rfl⟩ := mem_edgesOff.mp hf
    rcases Sym2.mem_iff.mp hxe with rfl | rfl <;> rcases Sym2.mem_iff.mp hxf with h | h
    · rw [h]
    · rw [h, mate_mate, Sym2.eq_swap]
    · rw [← h, mate_mate, Sym2.eq_swap]
    · rw [P.mate.injective h]

/-- `edgesOff P A` leaves exactly `A` uncovered. -/
theorem uncovered_edgesOff (P : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) : uncovered (edgesOff P A) = A := by
  ext v
  rw [mem_uncovered]
  constructor
  · intro h
    by_contra hv
    exact h _ (mem_edgesOff.mpr ⟨v, hv, rfl⟩) (Sym2.mem_mk_left v _)
  · rintro hv _ he hve
    obtain ⟨w, hw, rfl⟩ := mem_edgesOff.mp he
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact hw hv
    · exact hw ((mate_mem_iff P A hA w).mp hv)

/-- A finite type of even size has a perfect matching. -/
theorem nonempty_of_even_card {W : Type*} [Fintype W] (hW : Even (Fintype.card W)) :
    Nonempty (PerfectMatching W) := by
  obtain ⟨n, hn⟩ := hW
  obtain ⟨e⟩ : Nonempty (Bool × Fin n ≃ W) := Fintype.card_eq.mp (by simp [hn]; omega)
  have hinv : Function.Involutive fun p : Bool × Fin n ↦ (!p.1, p.2) := fun p ↦ by simp
  refine ⟨congr e
    { mate := hinv.toPerm
      mate_mate := hinv
      mate_ne := ?_ }⟩
  rintro ⟨_ | _, _⟩ <;> simp [Function.Involutive.coe_toPerm]

/-- Every partial matching `E` of a vertex type of even size is `edgesOff P (uncovered E)` for a
perfect matching `P` that maps `uncovered E` into itself. -/
theorem exists_edgesOff_eq (hV : Even (Fintype.card V)) {E : Finset (Sym2 V)}
    (hE : IsPartialMatching E) :
    ∃ P : PerfectMatching V, (∀ v ∈ uncovered E, P.mate v ∈ uncovered E) ∧
      edgesOff P (uncovered E) = E := by
  induction E using Finset.induction_on with
  | empty =>
    obtain ⟨P⟩ := nonempty_of_even_card hV
    refine ⟨P, fun v _ ↦ mem_uncovered.mpr fun _ h ↦ absurd h (Finset.notMem_empty _), ?_⟩
    ext e
    simp [mem_edgesOff, mem_uncovered]
  | insert e E he ih =>
    induction e using Sym2.ind with
    | h a b =>
    obtain ⟨hd, hdisj⟩ := hE
    obtain ⟨P, hP, hPE⟩ := ih ⟨fun f hf ↦ hd f (Finset.mem_insert_of_mem hf),
      fun f hf g hg ↦ hdisj f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg)⟩
    have hab : a ≠ b := fun h ↦ hd _ (Finset.mem_insert_self _ _) (Sym2.mk_isDiag_iff.mpr h)
    have hfree : ∀ x ∈ s(a, b), x ∈ uncovered E := fun x hx ↦ mem_uncovered.mpr fun f hf hxf ↦
      he (hdisj _ (Finset.mem_insert_self _ _) f (Finset.mem_insert_of_mem hf) x hx hxf ▸ hf)
    have ha := hfree a (Sym2.mem_mk_left a b)
    have hb := hfree b (Sym2.mem_mk_right a b)
    have hmem : ∀ f, f ∈ E ↔ ∃ v ∉ uncovered E, s(v, P.mate v) = f := fun f ↦ by
      conv_lhs => rw [← hPE]
      exact mem_edgesOff
    have hU : ∀ v, v ∈ uncovered (insert s(a, b) E) ↔ v ≠ a ∧ v ≠ b ∧ v ∈ uncovered E := by
      intro v
      simp only [mem_uncovered, Finset.forall_mem_insert, Sym2.mem_iff, not_or]
      exact and_assoc
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = Equiv.swap b (P.mate a) := ⟨_, rfl⟩
    have hσU : ∀ x ∈ uncovered E, σ x ∈ uncovered E := by
      intro x hx
      rw [hσ, Equiv.swap_apply_def]
      split_ifs
      · exact hP a ha
      · exact hb
      · exact hx
    have hoff : ∀ v ∉ uncovered E, (σ • P).mate v = P.mate v := by
      intro v hv
      have hv' : P.mate v ∉ uncovered E := fun h ↦ hv ((mate_mem_iff P _ hP v).mp h)
      rw [smul_mate, hσ, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne (fun h : v = b ↦ hv (by rwa [h]))
          (fun h : v = P.mate a ↦ hv (by rw [h]; exact hP a ha)),
        Equiv.swap_apply_of_ne_of_ne (fun h : P.mate v = b ↦ hv' (by rwa [h]))
          (fun h : P.mate v = P.mate a ↦ hv' (by rw [h]; exact hP a ha))]
    have hPa : (σ • P).mate a = b := by
      rw [smul_mate, hσ, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hab (P.mate_ne a).symm,
        Equiv.swap_apply_right]
    have hPb : (σ • P).mate b = a := by
      rw [← hPa, mate_mate]
    refine ⟨σ • P, fun v hv ↦ ?_, ?_⟩
    · obtain ⟨hva, hvb, hv⟩ := (hU v).mp hv
      refine (hU _).mpr ⟨fun h ↦ hvb ?_, fun h ↦ hva ?_, ?_⟩
      · rw [← mate_mate (σ • P) v, h, hPa]
      · rw [← mate_mate (σ • P) v, h, hPb]
      · rw [smul_mate, hσ, Equiv.swap_inv, ← hσ]
        exact hσU _ (hP _ (hσU v hv))
    · ext f
      rw [mem_edgesOff, Finset.mem_insert, hmem]
      constructor
      · rintro ⟨v, hv, rfl⟩
        by_cases hv' : v ∈ uncovered E
        · left
          by_cases hva : v = a
          · rw [hva, hPa]
          · have hvb : v = b := by
              by_contra hvb
              exact hv ((hU v).mpr ⟨hva, hvb, hv'⟩)
            rw [hvb, hPb, Sym2.eq_swap]
        · exact Or.inr ⟨v, hv', by rw [hoff v hv']⟩
      · rintro (rfl | ⟨v, hv, rfl⟩)
        · exact ⟨a, fun h ↦ ((hU a).mp h).1 rfl, by rw [hPa]⟩
        · exact ⟨v, fun h ↦ hv ((hU v).mp h).2.2, by rw [hoff v hv]⟩

end PartialMatching

section Suppression

variable [Fintype V] [DecidableEq V] {ι : Type*} (F : ι → PerfectMatching V)
  (P : PerfectMatching V) (A : Finset V) (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- `X ∈ PM(A)` avoids every derived context of `F`: each `F t` either closes a cycle with
`P'`, or `X ∪ κ_{F t}` is not one cycle. -/
def AvoidsContexts (X : PerfectMatching A) : Prop :=
  ∀ t, HasClosedCycle P (F t) A ∨ ¬Ham X (contract P (F t) A hA)

/-- Canonical suppression for one boundary matching: `X ∪ P'` is a zero state of `F` iff `X`
avoids every derived context. -/
theorem isZeroState_glue_iff (hA0 : A.Nonempty) (X : PerfectMatching A) :
    IsZeroState F (glue P A hA X) ↔ AvoidsContexts F P A hA X := by
  refine forall_congr' fun t ↦ ?_
  by_cases hC : HasClosedCycle P (F t) A
  · exact iff_of_true (not_ham_glue P (F t) A hA hC hA0 X) (Or.inl hC)
  · rw [ham_glue_iff P (F t) A hA hC X]
    exact ⟨Or.inr, fun h ↦ h.resolve_left hC⟩

/-- Canonical suppression: the zero states of `F` that contain `E` correspond to the boundary
matchings `X ∈ PM(A)` that avoid every derived context, by `Z ↦ Z|_A` and `X ↦ X ∪ P'`. -/
def zeroStateEquiv (hA0 : A.Nonempty) :
    {Z : PerfectMatching V // (edgesOff P A : Set (Sym2 V)) ⊆ Z.toGraph.edgeSet ∧
      IsZeroState F Z} ≃ {X : PerfectMatching A // AvoidsContexts F P A hA X} where
  toFun Z :=
    have hZ := (edgesOff_subset_iff P A Z.1).mp Z.2.1
    ⟨restrict Z.1 A (mate_mem_of_agree P A hA hZ),
      (isZeroState_glue_iff F P A hA hA0 _).mp ((glue_restrict_of_agree P A hA hZ).symm ▸ Z.2.2)⟩
  invFun X := ⟨glue P A hA X.1,
    (edgesOff_subset_iff P A _).mpr fun _ h ↦ glue_mate_of_notMem P A hA X.1 h,
    (isZeroState_glue_iff F P A hA hA0 X.1).mpr X.2⟩
  left_inv Z := Subtype.ext
    (glue_restrict_of_agree P A hA ((edgesOff_subset_iff P A Z.1).mp Z.2.1))
  right_inv X := Subtype.ext (restrict_glue P A hA X.1)

/-- The two sides of canonical suppression have the same size. -/
theorem card_zeroStates_eq (hA0 : A.Nonempty) :
    Nat.card {Z : PerfectMatching V // (edgesOff P A : Set (Sym2 V)) ⊆ Z.toGraph.edgeSet ∧
      IsZeroState F Z} = Nat.card {X : PerfectMatching A // AvoidsContexts F P A hA X} :=
  Nat.card_congr (zeroStateEquiv F P A hA hA0)

end Suppression

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable (m : ℕ) [NeZero m] (P : PerfectMatching (Vertex m)) (A : Finset (Vertex m))
  (hA : ∀ v ∈ A, P.mate v ∈ A)

/-- Canonical suppression on `V_m` for one boundary matching: `X ∪ P'` is a zero state iff each
`F_t` closes a cycle with `P'` or has `¬Ham X κ_{F_t}`. -/
theorem isZeroState_glue_iff (hA0 : A.Nonempty) (X : PerfectMatching A) :
    IsZeroState (factor m) (glue P A hA X) ↔
      ∀ t, HasClosedCycle P (factor m t) A ∨ ¬Ham X (contract P (factor m t) A hA) :=
  PerfectMatching.isZeroState_glue_iff (factor m) P A hA hA0 X

/-- Canonical suppression on `V_m`, for every `m`. If `E` has `m - 3 - K` edges, the boundary
has `2K + 6` vertices, and the zero states that contain `E` correspond to the boundary matchings
that avoid every derived context. -/
theorem suppression {K : ℕ} (hK : K + 3 ≤ m) (hE : (edgesOff P A).card = m - 3 - K) :
    A.card = 2 * K + 6 ∧
      Nonempty ({Z : PerfectMatching (Vertex m) //
        (edgesOff P A : Set (Sym2 (Vertex m))) ⊆ Z.toGraph.edgeSet ∧ IsZeroState (factor m) Z} ≃
        {X : PerfectMatching A //
          ∀ t, HasClosedCycle P (factor m t) A ∨ ¬Ham X (contract P (factor m t) A hA)}) := by
  have hcard := card_boundary P A hA (card_vertex m) hK hE
  refine ⟨hcard, ⟨zeroStateEquiv (factor m) P A hA ?_⟩⟩
  rw [← Finset.card_pos, hcard]
  omega

/-- Canonical suppression on `V_m` for a partial matching `E`, for every `m`. If `E` has
`m - 3 - K` edges, it leaves `2K + 6` vertices uncovered. Some perfect matching `P` has
`edgesOff P (uncovered E) = E`, and for it the zero states that contain `E` correspond to the
matchings of the uncovered set that avoid every derived context. -/
theorem suppression_of_isPartialMatching {E : Finset (Sym2 (Vertex m))}
    (hE : IsPartialMatching E) {K : ℕ} (hK : K + 3 ≤ m) (hcard : E.card = m - 3 - K) :
    (uncovered E).card = 2 * K + 6 ∧
      ∃ P : PerfectMatching (Vertex m), ∃ hU : ∀ v ∈ uncovered E, P.mate v ∈ uncovered E,
        edgesOff P (uncovered E) = E ∧
          Nonempty ({Z : PerfectMatching (Vertex m) //
            (E : Set (Sym2 (Vertex m))) ⊆ Z.toGraph.edgeSet ∧ IsZeroState (factor m) Z} ≃
            {X : PerfectMatching (uncovered E) //
              ∀ t, HasClosedCycle P (factor m t) (uncovered E) ∨
                ¬Ham X (contract P (factor m t) (uncovered E) hU)}) := by
  obtain ⟨P, hU, hPE⟩ := exists_edgesOff_eq (by rw [card_vertex]; exact even_two_mul m) hE
  obtain ⟨hA, ⟨e⟩⟩ := suppression m P (uncovered E) hU hK (by rw [hPE]; exact hcard)
  exact ⟨hA, P, hU, hPE, ⟨(Equiv.subtypeEquivRight fun Z ↦ by rw [hPE]).trans e⟩⟩

end RoundRobin.Canonical

end Pairing
