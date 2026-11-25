import Suppression.Canonical

/-!
# Zero-forcing cores and the repair reduction (COD-165)

A partial matching `A` of `V` is a finset of edges with `IsPartialMatching A`, and
`uncovered A` is the set of vertices it misses.

* `Blocks A Q` : `A ∪ Q` has a closed alternating cycle on edges of `A`, encoded as a nonempty
  vertex set that is a union of edges of `A` and is closed under `Q`.
* `hasClosedCycle_of_blocks`, `isZeroForcing_of_blocks` : the sufficient direction of the
  zero-forcing criterion. If `A` leaves a vertex uncovered and blocks every `F t`, then every
  perfect matching that contains `A` is a zero state of `F`. This is `not_ham_glue`.
* `two_mul_card_eq` : a partial matching `A` covers exactly `2 |A|` vertices.
* `exists_greedy` : the greedy step. One shared edge of `F t` is added for each `t ∈ U`, which
  is possible while `4 (|A₀| + |U|) ≤ |V| + 3`.
* `exists_repair` : the reduction. For a partial matching `A` and any partial matching `T`, some
  perfect matching `P ⊇ A` misses at most `2 |A|` edges of `T`.
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*}

section Blocks

/-- `A` blocks `Q` when `A ∪ Q` has a closed alternating cycle on edges of `A`: a nonempty vertex
set `C` in which every vertex has an `A`-partner in `C`, and which `Q` maps into itself. -/
def Blocks (A : Finset (Sym2 V)) (Q : PerfectMatching V) : Prop :=
  ∃ C : Finset V, C.Nonempty ∧ (∀ v ∈ C, ∃ w ∈ C, s(v, w) ∈ A) ∧ ∀ v ∈ C, Q.mate v ∈ C

/-- Blocking survives adding edges. -/
theorem Blocks.mono {A A' : Finset (Sym2 V)} {Q : PerfectMatching V} (hAA : A ⊆ A')
    (h : Blocks A Q) : Blocks A' Q := by
  obtain ⟨C, hC, hA, hQ⟩ := h
  exact ⟨C, hC, fun v hv ↦ (hA v hv).imp fun _ hw ↦ ⟨hw.1, hAA hw.2⟩, hQ⟩

/-- A shared edge `s(v, Q v) ∈ A` blocks `Q`, as a doubled `2`-cycle. -/
theorem blocks_of_mem {A : Finset (Sym2 V)} {Q : PerfectMatching V} {v : V}
    (h : s(v, Q.mate v) ∈ A) : Blocks A Q := by
  classical
  refine ⟨{v, Q.mate v}, ⟨v, Finset.mem_insert_self _ _⟩, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨Q.mate w, by simp, h⟩
    · rw [Finset.mem_singleton.mp hw]
      exact ⟨v, by simp, by rw [Sym2.eq_swap]; exact h⟩
  · rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · rw [Finset.mem_singleton.mp hw, mate_mate]
      simp

/-- A perfect matching that contains the edge `s(v, w)` pairs `v` with `w`. -/
theorem mate_eq_of_mem {A : Finset (Sym2 V)} {P : PerfectMatching V}
    (hP : (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet) {v w : V} (h : s(v, w) ∈ A) : P.mate v = w :=
  (SimpleGraph.mem_edgeSet _).mp (hP h)

/-- A perfect matching that contains `A` maps the vertices `A` leaves uncovered among
themselves. -/
theorem mate_mem_uncovered [Fintype V] [DecidableEq V] {A : Finset (Sym2 V)} {P : PerfectMatching V}
    (hP : (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet) {v : V} (hv : v ∈ uncovered A) :
    P.mate v ∈ uncovered A := by
  rw [mem_uncovered] at hv ⊢
  intro e he hve
  have hPe := hP he
  induction e using Sym2.ind with
  | h a b =>
    have hab : P.mate a = b := (SimpleGraph.mem_edgeSet _).mp hPe
    rcases Sym2.mem_iff.mp hve with h | h
    · have hvb : v = b := by rw [← hab, ← h, mate_mate]
      exact hv _ he (hvb ▸ Sym2.mem_mk_right a b)
    · have hva : v = a := by rw [← P.mate_mate v, h, ← hab, mate_mate]
      exact hv _ he (hva ▸ Sym2.mem_mk_left a b)

/-- A block of `A` gives `Q ∪ P'` a closed cycle off the uncovered set, for every perfect
matching `P ⊇ A`. -/
theorem hasClosedCycle_of_blocks [Fintype V] [DecidableEq V] {A : Finset (Sym2 V)}
    {P Q : PerfectMatching V} (hP : (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet) (h : Blocks A Q) :
    HasClosedCycle P Q (uncovered A) := by
  obtain ⟨C, hC, hA, hQ⟩ := h
  refine ⟨C, hC, Finset.disjoint_left.mpr fun v hv hvU ↦ ?_, fun v hv ↦ ?_, hQ⟩
  · obtain ⟨w, _, hw⟩ := hA v hv
    exact mem_uncovered.mp hvU _ hw (Sym2.mem_mk_left v w)
  · obtain ⟨w, hw, hvw⟩ := hA v hv
    rw [mate_eq_of_mem hP hvw]
    exact hw

/-- `A` is zero-forcing for `F` when every perfect matching that contains `A` is a zero state
of `F`. -/
def IsZeroForcing {ι : Type*} (F : ι → PerfectMatching V) (A : Finset (Sym2 V)) : Prop :=
  ∀ P : PerfectMatching V, (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet → IsZeroState F P

/-- The sufficient direction of the zero-forcing criterion. If `A` leaves some vertex uncovered
and `A ∪ F t` has a closed alternating cycle for every `t`, then every perfect matching that
contains `A` is a zero state of `F`. -/
theorem isZeroForcing_of_blocks [Fintype V] [DecidableEq V] {ι : Type*} {F : ι → PerfectMatching V}
    {A : Finset (Sym2 V)} (hA0 : (uncovered A).Nonempty) (hB : ∀ t, Blocks A (F t)) :
    IsZeroForcing F A := by
  intro P hP t
  have hU : ∀ v ∈ uncovered A, P.mate v ∈ uncovered A := fun _ hv ↦ mate_mem_uncovered hP hv
  have h := not_ham_glue P (F t) (uncovered A) hU (hasClosedCycle_of_blocks hP (hB t)) hA0
    (restrict P (uncovered A) hU)
  rwa [glue_restrict] at h

end Blocks

section Counting

variable [Fintype V]

/-- A perfect matching contains its edges off `A`. -/
theorem edgesOff_subset_edgeSet [DecidableEq V] (P : PerfectMatching V) (A : Finset V) :
    (edgesOff P A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet :=
  (edgesOff_subset_iff P A P).mpr fun _ _ ↦ rfl

/-- On a vertex type of even size every partial matching extends to a perfect matching. -/
theorem exists_superset (hV : Even (Fintype.card V)) {A : Finset (Sym2 V)}
    (hA : IsPartialMatching A) :
    ∃ P : PerfectMatching V, (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet := by
  classical
  obtain ⟨P, -, hPA⟩ := exists_edgesOff_eq hV hA
  exact ⟨P, hPA ▸ edgesOff_subset_edgeSet P _⟩

/-- A partial matching `A` covers exactly `2 |A|` vertices. -/
theorem two_mul_card_eq [DecidableEq V] (hV : Even (Fintype.card V)) {A : Finset (Sym2 V)}
    (hA : IsPartialMatching A) : 2 * A.card = (uncovered A)ᶜ.card := by
  obtain ⟨P, hU, hPA⟩ := exists_edgesOff_eq hV hA
  have h := two_mul_card_edgesOff P (uncovered A) hU
  rwa [hPA] at h

/-- A partial matching with `2 |A| < |V|` leaves some vertex uncovered. -/
theorem uncovered_nonempty [DecidableEq V] (hV : Even (Fintype.card V)) {A : Finset (Sym2 V)}
    (hA : IsPartialMatching A) (hcard : 2 * A.card < Fintype.card V) :
    (uncovered A).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have h2 := two_mul_card_eq hV hA
  rw [h, Finset.compl_empty, Finset.card_univ] at h2
  omega

/-- If `4 |A| < |V|`, every perfect matching `Q` has an edge that avoids the vertices of `A`. -/
theorem exists_mate_mem_uncovered [DecidableEq V] (hV : Even (Fintype.card V)) {A : Finset (Sym2 V)}
    (hA : IsPartialMatching A) (hcard : 4 * A.card < Fintype.card V) (Q : PerfectMatching V) :
    ∃ v ∈ uncovered A, Q.mate v ∈ uncovered A := by
  by_contra! hno
  have h2 := two_mul_card_eq hV hA
  have hle : (uncovered A).card ≤ (uncovered A)ᶜ.card :=
    Finset.card_le_card_of_injOn Q.mate (fun v hv ↦ by simpa using hno v hv)
      Q.mate.injective.injOn
  have hc := Finset.card_compl (uncovered A)
  have hu := (uncovered A).card_le_univ
  omega

/-- Adding an edge between two uncovered vertices keeps a partial matching. -/
theorem IsPartialMatching.insert [DecidableEq V] {A : Finset (Sym2 V)}
    (hA : IsPartialMatching A) {a b : V} (hab : a ≠ b) (ha : a ∈ uncovered A)
    (hb : b ∈ uncovered A) : IsPartialMatching (insert s(a, b) A) := by
  obtain ⟨hd, hdisj⟩ := hA
  have hfree : ∀ g ∈ A, ∀ v ∈ s(a, b), v ∉ g := fun g hg v hv ↦ by
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact mem_uncovered.mp ha g hg
    · exact mem_uncovered.mp hb g hg
  refine ⟨fun e he ↦ ?_, fun e he f hf v hve hvf ↦ ?_⟩
  · rcases Finset.mem_insert.mp he with rfl | he
    · exact fun h ↦ hab (Sym2.mk_isDiag_iff.mp h)
    · exact hd e he
  · rcases Finset.mem_insert.mp he with rfl | he <;> rcases Finset.mem_insert.mp hf with rfl | hf
    · rfl
    · exact absurd hvf (hfree f hf v hve)
    · exact absurd hve (hfree e he v hvf)
    · exact hdisj e he f hf v hve hvf

/-- The greedy step. Starting from a partial matching `A₀`, one edge of `F t` that avoids every
edge placed so far is added for each `t ∈ U`. Each step needs `4 |A| < |V|`, which holds while
`4 (|A₀| + |U|) ≤ |V| + 3`. Each added edge is shared with its `F t`, so it blocks `F t`. -/
theorem exists_greedy {ι : Type*} (hV : Even (Fintype.card V))
    (F : ι → PerfectMatching V) {A₀ : Finset (Sym2 V)} (hA₀ : IsPartialMatching A₀)
    (U : Finset ι) (hU : 4 * (A₀.card + U.card) ≤ Fintype.card V + 3) :
    ∃ A, A₀ ⊆ A ∧ IsPartialMatching A ∧ A.card ≤ A₀.card + U.card ∧
      ∀ t ∈ U, Blocks A (F t) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨A₀, subset_rfl, hA₀, by simp, by simp⟩
  | insert t U ht ih =>
    rw [Finset.card_insert_of_notMem ht] at hU
    obtain ⟨A, hA₀A, hA, hcard, hB⟩ := ih (by omega)
    obtain ⟨v, hv, hw⟩ := exists_mate_mem_uncovered hV hA (by omega) (F t)
    refine ⟨insert s(v, (F t).mate v) A, hA₀A.trans (Finset.subset_insert _ _),
      hA.insert ((F t).mate_ne v).symm hv hw, ?_, fun t' ht' ↦ ?_⟩
    · rw [Finset.card_insert_of_notMem ht]
      have := Finset.card_insert_le s(v, (F t).mate v) A
      omega
    · rcases Finset.mem_insert.mp ht' with rfl | ht'
      · exact blocks_of_mem (Finset.mem_insert_self _ _)
      · exact (hB t' ht').mono (Finset.subset_insert _ _)

/-- The edges of a partial matching `T` that `P` misses meet the vertices that `A` covers, so
there are at most as many as those vertices, when `P` keeps every edge of `T` that avoids
them. -/
theorem card_filter_notMem_le [DecidableEq V] {A T : Finset (Sym2 V)} (hT : IsPartialMatching T)
    {P : PerfectMatching V}
    (hTP : ∀ e ∈ T, (∀ v ∈ e, v ∈ uncovered A) → e ∈ P.toGraph.edgeSet) :
    (T.filter fun e ↦ e ∉ P.toGraph.edgeSet).card ≤ (uncovered A)ᶜ.card := by
  calc (T.filter fun e ↦ e ∉ P.toGraph.edgeSet).card
      ≤ ((uncovered A)ᶜ.biUnion fun v ↦ T.filter fun e ↦ v ∈ e).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨heT, heP⟩ := Finset.mem_filter.mp he
        by_contra hno
        refine heP (hTP e heT fun v hv ↦ ?_)
        by_contra hvU
        exact hno (Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_compl.mpr hvU, Finset.mem_filter.mpr ⟨heT, hv⟩⟩)
    _ ≤ ∑ v ∈ (uncovered A)ᶜ, (T.filter fun e ↦ v ∈ e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ (uncovered A)ᶜ, 1 := by
        refine Finset.sum_le_sum fun v _ ↦ Finset.card_le_one.mpr fun e he f hf ↦ ?_
        rw [Finset.mem_filter] at he hf
        exact hT.2 e he.1 f hf.1 v he.2 hf.2
    _ = (uncovered A)ᶜ.card := by simp

/-- The reduction. For a partial matching `A` and a partial matching `T`, keep the edges of `T`
that avoid the vertices of `A`, install `A` and complete arbitrarily. The result is a perfect
matching `P ⊇ A` that misses at most `2 |A|` edges of `T`. -/
theorem exists_repair [DecidableEq V] (hV : Even (Fintype.card V)) {A T : Finset (Sym2 V)}
    (hA : IsPartialMatching A) (hT : IsPartialMatching T) :
    ∃ P : PerfectMatching V, (A : Set (Sym2 V)) ⊆ P.toGraph.edgeSet ∧
      (T.filter fun e ↦ e ∉ P.toGraph.edgeSet).card ≤ 2 * A.card := by
  classical
  have hE : IsPartialMatching (A ∪ T.filter fun e ↦ ∀ v ∈ e, v ∈ uncovered A) := by
    refine ⟨fun e he ↦ ?_, fun e he f hf v hve hvf ↦ ?_⟩
    · rcases Finset.mem_union.mp he with he | he
      · exact hA.1 e he
      · exact hT.1 e (Finset.mem_filter.mp he).1
    · rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
      · exact hA.2 e he f hf v hve hvf
      · exact absurd hve (mem_uncovered.mp ((Finset.mem_filter.mp hf).2 v hvf) e he)
      · exact absurd hvf (mem_uncovered.mp ((Finset.mem_filter.mp he).2 v hve) f hf)
      · exact hT.2 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 v hve hvf
  obtain ⟨P, hP⟩ := exists_superset hV hE
  refine ⟨P, fun e he ↦ hP (Finset.mem_union_left _ he), ?_⟩
  rw [two_mul_card_eq hV hA]
  convert card_filter_notMem_le hT fun e he hev ↦
    hP (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hev⟩))

/-- The reduction for a zero-forcing core `A`. Every partial matching `T` is within `2 |A|`
missing edges of a zero state of `F`. -/
theorem exists_zeroState_repair [DecidableEq V] {ι : Type*} {F : ι → PerfectMatching V}
    (hV : Even (Fintype.card V)) {A T : Finset (Sym2 V)} (hA : IsPartialMatching A)
    (hF : IsZeroForcing F A) (hT : IsPartialMatching T) :
    ∃ P : PerfectMatching V, IsZeroState F P ∧
      (T.filter fun e ↦ e ∉ P.toGraph.edgeSet).card ≤ 2 * A.card := by
  obtain ⟨P, hP, hcard⟩ := exists_repair hV hA hT
  exact ⟨P, hF P hP, hcard⟩

end Counting

end PerfectMatching

end Pairing
