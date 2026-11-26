import Repair.SqrtObstructions.Hole

/-!
# NG-B(d), the local precision floor

Source: `results/sqrt-m-obstructions.md` §1.3, Theorem NG-B(d). Fix a finite set `B` (a ball
`B_K(T)` or a cylinder) and events `A_t`, and let `U_B` be uniform on `B`. The zero states in `B`
are `zeroIn B A`, the states with `X ≥ 1` are `liveIn B A`, and `ν = |zeroIn B A| / |B|` is the
local zero density. The law `ν′ = U_B(· | X ≥ 1)` is uniform on `liveIn B A`.

* `interIn_liveIn` : for nonempty `S`, `⋂_{t ∈ S} A_t ⊆ {X ≥ 1}`, so `B` and `liveIn B A` have the
  same `S`-intersection.
* `zeroIn_liveIn` : `ν′` has no zero states.
* `cond_ratio_eq` : `ν′(⋂_{t ∈ S} A_t) = U_B(⋂_{t ∈ S} A_t) / (1 - ν)` for nonempty `S`.
* `local_precision_floor` (NG-B(d)) : for every `η ≥ ν / (1 - ν)` some nonempty `L ⊆ B` without
  zero states has `U_B(⋂_S) ≤ U_L(⋂_S) ≤ (1 + η) U_B(⋂_S)` for every nonempty `S`. So local
  intersection numbers with upper relative slack `ν / (1 - ν)` cannot show that `B` holds a zero
  state, that is `ρ(T) ≤ K` for `B = B_K(T)`, or `δ(T, D) > 0` for a cylinder.
* `RoundRobin.Canonical.local_precision_floor_ball` : the instance `B = B_K(T)` with the true
  events `A_t = {P | P ∪ F_t is one cycle}`.

The averaging identity `E_G E_T ν(T, K) = q_m` of the source, which turns the floor into slack
`q_m / (1 - q_m)` for gadget-uniform arguments, is not formalized here.
-/

namespace Pairing

namespace Obstruction

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι]

/-- The states of `B` with `X ≥ 1`, those in some event `A_t` (`sqrt-m-obstructions.md` §1.3). -/
def liveIn (B : Finset Ω) (A : ι → Finset Ω) : Finset Ω :=
  B.filter fun ω ↦ ∃ t, ω ∈ A t

/-- The zero states of `B`, those in no event `A_t` (`sqrt-m-obstructions.md` §1.3). -/
def zeroIn (B : Finset Ω) (A : ι → Finset Ω) : Finset Ω :=
  B.filter fun ω ↦ ∀ t, ω ∉ A t

/-- The states of `B` in `⋂_{t ∈ S} A_t` (`sqrt-m-obstructions.md` §1.3). -/
def interIn (B : Finset Ω) (A : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  B.filter fun ω ↦ ∀ t ∈ S, ω ∈ A t

/-- `|liveIn B A| + |zeroIn B A| = |B|` (`sqrt-m-obstructions.md` §1.3, NG-B(d)). -/
theorem card_liveIn_add_card_zeroIn (B : Finset Ω) (A : ι → Finset Ω) :
    (liveIn B A).card + (zeroIn B A).card = B.card := by
  rw [liveIn, zeroIn, ← Finset.card_filter_add_card_filter_not (s := B)
    (p := fun ω ↦ ∃ t, ω ∈ A t)]
  congr 2
  ext ω
  simp

/-- For nonempty `S`, `⋂_{t ∈ S} A_t ⊆ {X ≥ 1}`, so conditioning on `X ≥ 1` keeps the
`S`-intersection (`sqrt-m-obstructions.md` §1.3, NG-B(d)). -/
theorem interIn_liveIn (B : Finset Ω) (A : ι → Finset Ω) {S : Finset ι} (hS : S.Nonempty) :
    interIn (liveIn B A) A S = interIn B A S := by
  ext ω
  simp only [interIn, liveIn, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hB, -⟩, h⟩
    exact ⟨hB, h⟩
  · rintro ⟨hB, h⟩
    obtain ⟨t, ht⟩ := hS
    exact ⟨⟨hB, t, h t ht⟩, h⟩

/-- The conditioned law has no zero states (`sqrt-m-obstructions.md` §1.3, NG-B(d)). -/
theorem zeroIn_liveIn (B : Finset Ω) (A : ι → Finset Ω) : zeroIn (liveIn B A) A = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ω hω ↦ ?_
  obtain ⟨hl, hz⟩ := Finset.mem_filter.mp hω
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hl).2
  exact hz t ht

/-- **NG-B(d)**, the conditioning identity (`sqrt-m-obstructions.md` §1.3). For nonempty `S`,
`ν′(⋂_{t ∈ S} A_t) = U_B(⋂_{t ∈ S} A_t) / (1 - ν)` with `ν′ = U_B(· | X ≥ 1)` and
`ν = |zeroIn B A| / |B|`. -/
theorem cond_ratio_eq (B : Finset Ω) (A : ι → Finset Ω) {S : Finset ι} (hS : S.Nonempty)
    (hL : (liveIn B A).Nonempty) :
    ((interIn (liveIn B A) A S).card : ℝ) / (liveIn B A).card =
      ((interIn B A S).card / B.card) / (1 - (zeroIn B A).card / B.card) := by
  have hsum := card_liveIn_add_card_zeroIn B A
  have hl : (0 : ℝ) < (liveIn B A).card := Nat.cast_pos.mpr hL.card_pos
  have hb : (0 : ℝ) < B.card := by
    have : (liveIn B A).card ≤ B.card := by omega
    exact Nat.cast_pos.mpr (lt_of_lt_of_le hL.card_pos this)
  have hsum' : ((liveIn B A).card : ℝ) + (zeroIn B A).card = B.card := by exact_mod_cast hsum
  rw [interIn_liveIn B A hS, one_sub_div hb.ne', div_div_div_cancel_right₀ hb.ne', ← hsum',
    add_sub_cancel_right]

/-- **NG-B(d), the local precision floor** (`sqrt-m-obstructions.md` §1.3). Let `B` hold a state
with `X ≥ 1`, put `ν = |zeroIn B A| / |B|`, and let `η ≥ ν / (1 - ν)`. Then some nonempty `L ⊆ B`
without zero states (the support of `U_B(· | X ≥ 1)`) has
`U_B(⋂_S) ≤ U_L(⋂_S) ≤ (1 + η) U_B(⋂_S)` for every nonempty `S`. So local intersection data with
upper relative slack at least `ν / (1 - ν)` cannot show that `B` contains a zero state. -/
theorem local_precision_floor (B : Finset Ω) (A : ι → Finset Ω) (hL : (liveIn B A).Nonempty)
    {η : ℝ}
    (hη : ((zeroIn B A).card / B.card : ℝ) / (1 - (zeroIn B A).card / B.card) ≤ η) :
    ∃ L ⊆ B, L.Nonempty ∧ zeroIn L A = ∅ ∧ ∀ S : Finset ι, S.Nonempty →
      ((interIn B A S).card : ℝ) / B.card ≤ (interIn L A S).card / L.card ∧
        ((interIn L A S).card : ℝ) / L.card ≤ (1 + η) * ((interIn B A S).card / B.card) := by
  have hsum := card_liveIn_add_card_zeroIn B A
  have hl : (0 : ℝ) < (liveIn B A).card := Nat.cast_pos.mpr hL.card_pos
  have hb : (0 : ℝ) < B.card := by
    have : (liveIn B A).card ≤ B.card := by omega
    exact Nat.cast_pos.mpr (lt_of_lt_of_le hL.card_pos this)
  have hsum' : ((liveIn B A).card : ℝ) + (zeroIn B A).card = B.card := by exact_mod_cast hsum
  have hν : ((zeroIn B A).card / B.card : ℝ) / (1 - (zeroIn B A).card / B.card) =
      (zeroIn B A).card / (liveIn B A).card := by
    rw [one_sub_div hb.ne', div_div_div_cancel_right₀ hb.ne', ← hsum', add_sub_cancel_right]
  rw [hν] at hη
  refine ⟨liveIn B A, Finset.filter_subset _ _, hL, zeroIn_liveIn B A, fun S hS ↦ ?_⟩
  rw [interIn_liveIn B A hS]
  have hi : (0 : ℝ) ≤ (interIn B A S).card := Nat.cast_nonneg _
  constructor
  · have hz0 : (0 : ℝ) ≤ (zeroIn B A).card := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_left hi hl (by rw [← hsum']; linarith)
  · have hz : ((zeroIn B A).card : ℝ) ≤ η * (liveIn B A).card := by
      rwa [div_le_iff₀ hl] at hη
    rw [div_le_iff₀ hl, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hb, ← hsum']
    nlinarith [mul_le_mul_of_nonneg_left hz hi]

end Obstruction

namespace RoundRobin.Canonical

open PerfectMatching Obstruction

variable {m : ℕ} [NeZero m]

/-- The true events `A_t = {P | P ∪ F_t is one cycle}` as finsets (`sqrt-m-obstructions.md`
§1.3). -/
def hamFinset (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) : Finset (PerfectMatching (Vertex m)) :=
  Finset.univ.filter fun P ↦ Ham P (factor m t)

/-- **NG-B(d)** on a ball (`sqrt-m-obstructions.md` §1.3). Let the ball `B_K(T)` of a tail `T`
hold a matching that is not a zero state, let `ν = ν(T, K)` be its zero density and
`η ≥ ν / (1 - ν)`. Then some nonempty `L ⊆ B_K(T)` holds no zero state and matches every local
intersection number `U_B(⋂_{t ∈ S} A_t)`, `S` nonempty, within upper relative slack `η`. -/
theorem local_precision_floor_ball {G : Finset (Vertex m)}
    (T : PerfectMatching (Gᶜ : Finset (Vertex m))) (K : ℕ)
    (hlive : ∃ P, tailDist P T ≤ K ∧ ¬IsZeroState (factor m) P) {η : ℝ}
    (hη : ((zeroIn (Finset.univ.filter fun P ↦ tailDist P T ≤ K) (hamFinset m)).card /
        (Finset.univ.filter fun P ↦ tailDist P T ≤ K).card : ℝ) /
      (1 - (zeroIn (Finset.univ.filter fun P ↦ tailDist P T ≤ K) (hamFinset m)).card /
        (Finset.univ.filter fun P ↦ tailDist P T ≤ K).card) ≤ η) :
    ∃ L ⊆ Finset.univ.filter (fun P : PerfectMatching (Vertex m) ↦ tailDist P T ≤ K),
      L.Nonempty ∧ (∀ P ∈ L, ¬IsZeroState (factor m) P) ∧ ∀ S : Finset (ZMod (2 * m - 1)),
        S.Nonempty →
        ((interIn (Finset.univ.filter fun P ↦ tailDist P T ≤ K) (hamFinset m) S).card : ℝ) /
            (Finset.univ.filter fun P ↦ tailDist P T ≤ K).card ≤
          (interIn L (hamFinset m) S).card / L.card ∧
        ((interIn L (hamFinset m) S).card : ℝ) / L.card ≤
          (1 + η) * ((interIn (Finset.univ.filter fun P ↦ tailDist P T ≤ K) (hamFinset m) S).card /
            (Finset.univ.filter fun P ↦ tailDist P T ≤ K).card) := by
  obtain ⟨P, hP, hPz⟩ := hlive
  have hL : (liveIn (Finset.univ.filter fun P ↦ tailDist P T ≤ K) (hamFinset m)).Nonempty := by
    refine ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, ?_⟩⟩
    by_contra h
    push Not at h
    exact hPz fun t ht ↦ h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
  obtain ⟨L, hLB, hLne, hLz, hS⟩ := local_precision_floor _ (hamFinset m) hL hη
  refine ⟨L, hLB, hLne, fun Q hQ hQz ↦ ?_, hS⟩
  have : Q ∈ zeroIn L (hamFinset m) :=
    Finset.mem_filter.mpr ⟨hQ, fun t ht ↦ hQz t (Finset.mem_filter.mp ht).2⟩
  rw [hLz] at this
  exact Finset.notMem_empty _ this

end RoundRobin.Canonical

end Pairing
