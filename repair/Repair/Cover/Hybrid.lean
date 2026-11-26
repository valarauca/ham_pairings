import Repair.SqrtObstructions.NearHybrid

/-!
# Hybrids are spheres around the factor tail (Proposition 1, Corollary 1)

Source: `results/hybwin-contra.md` (organize-archive cd19551) §2, Proposition 1 and Corollary 1.

A hybrid of a perfect matching `T₀` of `W` is `(T₀ ∖ E′) ∪ R′`, where `E′` is a set of edges of
`T₀` and `R′` is a perfect matching of their vertex set `V(E′)` with no edge of `T₀`. In Lean,
`V(E′)` is a `T₀`-closed set `S ⊆ W`, `R′` is a `PerfectMatching S` with `IsEdgeFree T₀ R′`, and
the hybrid is `glue T₀ S hS R′` (`Clifford.Contraction`). Then `|E′| = |S| / 2`.

General part (any `W` and `T₀`).
* `defect_glue` : the defect of a hybrid against `T₀` is `V(E′)`.
* `exists_hybrid` (Proposition 1, existence) : every perfect matching `T` of `W` is the hybrid
  with `V(E′) = defect T₀ T` and `R′ = T` restricted there.
* `hybrid_unique` (Proposition 1, uniqueness) : two hybrids with no `T₀`-edge in `R′` that glue
  to the same matching have the same `V(E′)` and the same `R′`.
* `card_edgesOutside_comm` : `|T₀ ∖ T| = |T ∖ T₀|`, so `|E′| = |T₀ ∖ T|`.
* `card_edgesOutside_eq_iff_hybrid` (Corollary 1) : `T` is at distance `d′` from `T₀` iff it is
  a hybrid with `|E′| = d′`.

Round-robin part, for the default gadget `G0` and the factor tail `T(n)` (`FactorCap.factorTail`).
* `two_mul_tailDist_factor` : `2 · tailDist F_{s0} T = |defect T(n) T|`.
* `tailDist_eq_iff_hybrid` (Corollary 1) : the tails `T` with `tailDist F_{s0} T = d′` are
  exactly the hybrids of `T(n)` with `|E′| = d′`.
* `repairBound_iff_hybrid`, `repairBound_of_window` (Corollary 1, reduction) : `N_m ≤ K` holds
  iff every hybrid has `ρ ≤ K`. If every tail closer than `d₁` has `ρ ≤ K₀` and every hybrid with
  `|E′| ≥ d₁` has `ρ ≤ K`, then `N_m ≤ max(K, K₀)`. With `K₀` the bound of Theorem 4 of the rescue
  below `d₁`, this is the reduction of the window question to `N_m`. Theorem 4 itself is not
  formalized here.
-/

namespace Pairing

namespace PerfectMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `R′` has no edge of `T₀` (`hybwin-contra.md` (cd19551) §1, the normalisation of
Proposition 1). -/
def IsEdgeFree (T₀ : PerfectMatching W) {S : Finset W} (R : PerfectMatching S) : Prop :=
  ∀ a : S, (R.mate a : W) ≠ T₀.mate a

/-- The defect of the hybrid `(T₀ ∖ E′) ∪ R′` against `T₀` is `V(E′)` (`hybwin-contra.md`
(cd19551) §2, proof of Proposition 1). -/
theorem defect_glue (T₀ : PerfectMatching W) {S : Finset W} (hS : ∀ v ∈ S, T₀.mate v ∈ S)
    {R : PerfectMatching S} (hR : IsEdgeFree T₀ R) : defect T₀ (glue T₀ S hS R) = S := by
  ext v
  rw [mem_defect]
  by_cases hv : v ∈ S
  · simp only [hv, iff_true]
    rw [glue_mate_of_mem T₀ S hS R hv]
    exact hR ⟨v, hv⟩
  · simp only [hv, iff_false, not_not]
    rw [glue_mate_of_notMem T₀ S hS R hv]

/-- **Proposition 1, existence** (`hybwin-contra.md` (cd19551) §2). Every perfect matching `T`
of `W` is a hybrid `(T₀ ∖ E′) ∪ R′`, with `V(E′) = defect T₀ T`, the vertices of `T₀ ∖ T`, and
`R′ = T ∖ T₀`, which has no `T₀`-edge. -/
theorem exists_hybrid (T₀ T : PerfectMatching W) :
    ∃ (hS : ∀ v ∈ defect T₀ T, T₀.mate v ∈ defect T₀ T) (R : PerfectMatching (defect T₀ T)),
      IsEdgeFree T₀ R ∧ glue T₀ (defect T₀ T) hS R = T := by
  refine ⟨fun v hv ↦ mate_mem_defect_ref T₀ T hv,
    restrict T (defect T₀ T) (fun v hv ↦ mate_mem_defect T₀ T hv), fun a ↦ ?_, ?_⟩
  · exact mem_defect.mp a.2
  · refine glue_restrict_of_agree T₀ _ _ fun v hv ↦ ?_
    rw [mem_defect, not_not] at hv
    exact hv

/-- **Proposition 1, uniqueness** (`hybwin-contra.md` (cd19551) §2). If two hybrids whose `R′`
have no `T₀`-edge glue to the same matching, they have the same `V(E′)` and the same `R′`. -/
theorem hybrid_unique (T₀ : PerfectMatching W) {S S' : Finset W} (hS : ∀ v ∈ S, T₀.mate v ∈ S)
    (hS' : ∀ v ∈ S', T₀.mate v ∈ S') {R : PerfectMatching S} {R' : PerfectMatching S'}
    (hR : IsEdgeFree T₀ R) (hR' : IsEdgeFree T₀ R') (h : glue T₀ S hS R = glue T₀ S' hS' R') :
    S = S' ∧ ∀ v (hv : v ∈ S) (hv' : v ∈ S'), (R.mate ⟨v, hv⟩ : W) = R'.mate ⟨v, hv'⟩ := by
  refine ⟨by rw [← defect_glue T₀ hS hR, h, defect_glue T₀ hS' hR'], fun v hv hv' ↦ ?_⟩
  rw [← glue_mate_of_mem T₀ S hS R hv, h, glue_mate_of_mem T₀ S' hS' R' hv']

/-- `|T₀ ∖ T| = |T ∖ T₀|`, so `|E′| = |T₀ ∖ T|` in Proposition 1 (`hybwin-contra.md`
(cd19551) §2). -/
theorem card_edgesOutside_comm (T₀ T : PerfectMatching W) :
    (edgesOutside T T₀).card = (edgesOutside T₀ T).card := by
  have h1 := two_mul_card_edgesOutside T T₀
  have h2 := two_mul_card_edgesOutside T₀ T
  have h3 : defect T T₀ = defect T₀ T := by
    ext v
    rw [mem_defect, mem_defect, ne_comm]
  rw [h3] at h1
  omega

/-- **Corollary 1** (`hybwin-contra.md` (cd19551) §2). `T` is at distance `d′` from `T₀`
(`|T ∖ T₀| = d′`) iff it is a hybrid `(T₀ ∖ E′) ∪ R′` with `|E′| = d′` (`|V(E′)| = 2d′`) and no
`T₀`-edge in `R′`. -/
theorem card_edgesOutside_eq_iff_hybrid (T₀ T : PerfectMatching W) (d : ℕ) :
    (edgesOutside T₀ T).card = d ↔ ∃ (S : Finset W) (hS : ∀ v ∈ S, T₀.mate v ∈ S)
      (R : PerfectMatching S), IsEdgeFree T₀ R ∧ S.card = 2 * d ∧ glue T₀ S hS R = T := by
  constructor
  · rintro rfl
    obtain ⟨hS, R, hR, hT⟩ := exists_hybrid T₀ T
    exact ⟨_, hS, R, hR, (two_mul_card_edgesOutside T₀ T).symm, hT⟩
  · rintro ⟨S, hS, R, hR, hcard, rfl⟩
    have h := two_mul_card_edgesOutside T₀ (glue T₀ S hS R)
    rw [defect_glue T₀ hS hR] at h
    omega

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `2 · |T ∖ T(n)| = |defect T(n) T|` for a tail `T` of `G0`, where `|T ∖ T(n)|` is
`tailDist F_{s0} T` (`hybwin-contra.md` (cd19551) §1, the distance `d′ = |E′|`). -/
theorem two_mul_tailDist_factor (hm : 5 ≤ m)
    (T : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) :
    2 * tailDist (factor m (FactorCap.capCenter m)) T =
      (defect (FactorCap.factorTail m hm) T).card := by
  rw [two_mul_tailDist, defect]
  congr 1
  refine Finset.filter_congr fun u _ ↦ ?_
  rw [← FactorCap.factorTail_mate hm u, Ne, Ne, Subtype.ext_iff]

/-- **Corollary 1 for tails** (`hybwin-contra.md` (cd19551) §2). A tail `T` of `G0` lies at
distance `d′` from the factor tail `T(n)` iff it is a hybrid `(T(n) ∖ E′) ∪ R′` with `|E′| = d′`
and no `T(n)`-edge in `R′`. So the hybrids with `d′ ∈ [d₁, M]` are the tails at distance at
least `d₁`. -/
theorem tailDist_eq_iff_hybrid (hm : 5 ≤ m)
    (T : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m))) (d : ℕ) :
    tailDist (factor m (FactorCap.capCenter m)) T = d ↔
      ∃ (S : Finset ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
        (hS : ∀ v ∈ S, (FactorCap.factorTail m hm).mate v ∈ S) (R : PerfectMatching S),
        IsEdgeFree (FactorCap.factorTail m hm) R ∧ S.card = 2 * d ∧
          glue (FactorCap.factorTail m hm) S hS R = T := by
  rw [← card_edgesOutside_eq_iff_hybrid]
  have h1 := two_mul_tailDist_factor hm T
  have h2 := two_mul_card_edgesOutside (FactorCap.factorTail m hm) T
  omega

/-- **Corollary 1, reduction** (`hybwin-contra.md` (cd19551) §2). `N_m ≤ K` for `G0` iff every
hybrid of `T(n)` has a zero state within `K`. -/
theorem repairBound_iff_hybrid (hm : 5 ≤ m) (K : ℕ) :
    RepairBound m (FactorCap.gadget m) K ↔
      ∀ (S : Finset ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
        (hS : ∀ v ∈ S, (FactorCap.factorTail m hm).mate v ∈ S) (R : PerfectMatching S),
        IsEdgeFree (FactorCap.factorTail m hm) R →
          ∃ P : ZeroState m, tailDist P.1 (glue (FactorCap.factorTail m hm) S hS R) ≤ K := by
  constructor
  · exact fun h S hS R _ ↦ h _
  · intro h T
    obtain ⟨hS, R, hR, hT⟩ := exists_hybrid (FactorCap.factorTail m hm) T
    rw [← hT]
    exact h _ hS R hR

/-- **Corollary 1, window form** (`hybwin-contra.md` (cd19551) §2). If every tail at distance
below `d₁` from `T(n)` has `ρ ≤ K₀`, and every hybrid with `|E′| ≥ d₁` has `ρ ≤ K`, then
`N_m ≤ max(K, K₀)`. With `K₀` from Theorem 4 of the rescue, a rescue on the window is a bound on
`N_m`, which is COD-149. -/
theorem repairBound_of_window (hm : 5 ≤ m) {d₁ K K₀ : ℕ}
    (hlow : ∀ T : PerfectMatching ((FactorCap.gadget m)ᶜ : Finset (Vertex m)),
      tailDist (factor m (FactorCap.capCenter m)) T < d₁ → ∃ P : ZeroState m, tailDist P.1 T ≤ K₀)
    (hwin : ∀ (S : Finset ((FactorCap.gadget m)ᶜ : Finset (Vertex m)))
      (hS : ∀ v ∈ S, (FactorCap.factorTail m hm).mate v ∈ S) (R : PerfectMatching S),
      IsEdgeFree (FactorCap.factorTail m hm) R → 2 * d₁ ≤ S.card →
        ∃ P : ZeroState m, tailDist P.1 (glue (FactorCap.factorTail m hm) S hS R) ≤ K) :
    RepairBound m (FactorCap.gadget m) (max K K₀) := by
  intro T
  by_cases hd : tailDist (factor m (FactorCap.capCenter m)) T < d₁
  · obtain ⟨P, hP⟩ := hlow T hd
    exact ⟨P, hP.trans (le_max_right _ _)⟩
  · obtain ⟨S, hS, R, hR, hcard, hT⟩ :=
      (tailDist_eq_iff_hybrid hm T _).mp rfl
    obtain ⟨P, hP⟩ := hwin S hS R hR (by omega)
    exact ⟨P, (hT ▸ hP).trans (le_max_left _ _)⟩

end RoundRobin.Canonical

end Pairing
