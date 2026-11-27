import Pairing.InvolutionProduct
import Repair.Forcing
import Repair.SqrtObstructions.CertLength

/-!
# Theorem C′ for cores (partial matchings)

Source: `results/factor-tail-L-test.md`, Theorem C′, in the core form ("Let A be a core, or a zero
state"), with the definitions and Theorem B(i) of `results/cod-149-core-sharpening.md`. This is
NG-B(b) of `results/sqrt-m-obstructions.md` §1.3 for partial matchings. Put `n = 2m - 1`, prime.

A core is a partial matching `A` with `|A| ≤ m - 1` such that `A ∪ F_t` has a closed alternating
cycle for every `t`. As in `Repair.Forcing`, a closed alternating cycle is encoded by its vertex
set `C`, nonempty, a union of edges of `A`, and closed under `F_t`. It has `|C|/2` edges of `A`.
Put `A'' = A ∖ F_s`, `k = |A''|` and `X = V(A'')`, so `|X| = 2k`.

Alternating cycles (general `V`, two perfect matchings `a, b`, `σ = a b`). They use the
involution-product bridge, ham-spin `core/Pairing/InvolutionProduct.lean` (fe1f6bf), which now
holds `not_sameCycle_mate_right` and `not_sameCycle_mate_left`: no `σ`-orbit meets its image under
`a` or `b`.
* `mate_zpow_apply` : `b` conjugates `σ` to `σ⁻¹`.
* `exists_pow_eq_of_closed` : if `C ∋ y` is closed under `a` and `b`, then `σ^r y = y` for some
  `1 ≤ r` with `2r ≤ |C|`.

Round-robin part.
* `certLength_bound_of_hit` : the counting step of Theorem C′. If every `t ≠ s` has
  `E_t(y, i) ∈ X` for some `y ∈ X` and `i < L`, then `n - 1 ≤ |X|(|X| L + 2L - 1)`.
* `exists_walkEnd_mem_of_agree` (in `Repair.SqrtObstructions.CertLength`) : the walk step of
  `exists_walkEnd_mem`, for any `X` on which `P` agrees with `F_s` along the cycle.
* `exists_mem_coreDefect` : Theorem B(i) for cores. At prime `n` every closed alternating cycle of
  `A ∪ F_t`, `t ≠ s`, meets `X = V(A'')`.
* `core_certLength_bound` (Theorem C′, core form) : if every `t ≠ s` has a closed alternating cycle
  of `A ∪ F_t` with at most `L` edges of `A`, then `n - 1 ≤ 2k((2k + 2)L - 1)`.

The source states Theorem C′ for `L ≤ m - 1`. The core form here holds for every `L`, as the
zero-state form `certLength_bound` does.
-/

namespace Pairing

namespace PerfectMatching

section AltCycle

variable {V : Type*}

/-- `b (σ^z y) = σ^(-z) (b y)` for `σ = a b`: the involution `b` conjugates `σ` to `σ⁻¹`
(`factor-tail-L-test.md`, Theorem C′, cycles of `A ∪ F_t`). -/
theorem mate_zpow_apply (a b : PerfectMatching V) (z : ℤ) (y : V) :
    b.mate (((a.mate * b.mate) ^ z) y) = ((a.mate * b.mate) ^ (-z)) (b.mate y) := by
  have hconj : b.mate * (a.mate * b.mate) * b.mate⁻¹ = (a.mate * b.mate)⁻¹ := by
    rw [mate_mul_mate_inv, mate_inv, mul_assoc, mul_assoc, mate_mul_self, mul_one]
  have h : b.mate * (a.mate * b.mate) ^ z * b.mate⁻¹ = (a.mate * b.mate) ^ (-z) := by
    rw [← conj_zpow, hconj, inv_zpow']
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]

/-- A set closed under two perfect matchings `a, b` holds whole cycles of `a ∪ b`: every `y ∈ C`
has `σ^r y = y` with `σ = a b`, `1 ≤ r` and `2r ≤ |C|` (`factor-tail-L-test.md`, Theorem C′: a
closed alternating cycle on at most `2L` vertices has at most `L` edges of `a`). `C` holds the
component of `y`, which has twice as many vertices as the `σ`-cycle of `y`
(`card_reachable_eq_two_mul`, ham-spin `core/Pairing/InvolutionProduct.lean`, fe1f6bf). -/
theorem exists_pow_eq_of_closed [Finite V] (a b : PerfectMatching V)
    {C : Finset V} (ha : ∀ v ∈ C, a.mate v ∈ C) (hb : ∀ v ∈ C, b.mate v ∈ C) {y : V}
    (hy : y ∈ C) : ∃ r, 1 ≤ r ∧ 2 * r ≤ C.card ∧ ((a.mate * b.mate) ^ r) y = y := by
  have hreach : ∀ w, (a.toGraph ⊔ b.toGraph).Reachable y w → w ∈ C := fun _ h ↦
    mem_of_reachable_of_mate_mem a b (B := (C : Set V)) ha hb h hy
  set σ := a.mate * b.mate with hσ
  have hper : Function.IsPeriodicPt σ (orderOf σ) y := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow,
      pow_orderOf_eq_one]
    rfl
  set r := Function.minimalPeriod σ y with hr
  have hrpos : 0 < r := hper.minimalPeriod_pos (orderOf_pos σ)
  have hfix : (σ ^ r) y = y := by
    rw [← Equiv.Perm.iterate_eq_pow]
    exact Function.iterate_minimalPeriod
  have hcyc : r ≤ Nat.card {w // σ.SameCycle y w} := by
    rw [← Nat.card_fin r]
    refine Nat.card_le_card_of_injective (fun i ↦ ⟨(σ ^ (i : ℕ)) y,
      Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl σ y)⟩) fun i j h ↦ ?_
    have h' := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := y) i.2 j.2
    simp only [Equiv.Perm.iterate_eq_pow] at h'
    exact Fin.ext (h' (congrArg Subtype.val h))
  have hC : 2 * Nat.card {w // σ.SameCycle y w} ≤ C.card := by
    rw [← card_reachable_eq_two_mul, ← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun w ↦ ⟨w.1, hreach w.1 w.2⟩) fun _ _ h ↦
      Subtype.ext (Subtype.mk.inj h)
  exact ⟨r, hrpos, by omega, hfix⟩

end AltCycle

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- **The counting step of Theorem C′** (`factor-tail-L-test.md`, proof of Theorem C′). Let
`n = 2m - 1` be prime and `X` a vertex set. If every `t ≠ s` has `E_t(y, i) ∈ X` for some `y ∈ X`
and `i < L`, then `n - 1 ≤ |X| (|X| L + 2L - 1)`. -/
theorem certLength_bound_of_hit (hp : (2 * m - 1).Prime) (s : ZMod (2 * m - 1))
    (X : Finset (Vertex m)) {L : ℕ}
    (hhit : ∀ t ≠ s, ∃ y ∈ X, ∃ i < L, walkEnd s t y i ∈ X) :
    2 * m - 2 ≤ X.card * (X.card * L + 2 * L - 1) := by
  have hcardne : (Finset.univ.filter fun t : ZMod (2 * m - 1) ↦ t ≠ s).card = 2 * m - 2 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
    omega
  by_cases hL : L ≤ m - 1
  · rw [← hcardne]
    calc (Finset.univ.filter fun t : ZMod (2 * m - 1) ↦ t ≠ s).card
        ≤ (X.biUnion fun y ↦
            Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, walkEnd s t y i ∈ X).card := by
          refine Finset.card_le_card fun t ht ↦ ?_
          have hts := (Finset.mem_filter.mp ht).2
          obtain ⟨y, hy, i, hi, hiX⟩ := hhit t hts
          exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hts, i, hi, hiX⟩⟩
      _ ≤ ∑ y ∈ X, (Finset.univ.filter fun t ↦ t ≠ s ∧ ∃ i < L, walkEnd s t y i ∈ X).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ X, (L * X.card + (2 * L - 1)) :=
          Finset.sum_le_sum fun y _ ↦ card_walkHit_le hp s y X hL
      _ = X.card * (L * X.card + (2 * L - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ X.card * (X.card * L + 2 * L - 1) := by
          refine Nat.mul_le_mul_left _ ?_
          rcases Nat.eq_zero_or_pos L with rfl | hLpos
          · simp
          · rw [mul_comm L]
            generalize X.card * L = q
            omega
  · rcases X.eq_empty_or_nonempty with hXe | hXne
    · have hm : m = 1 := by
        by_contra hm
        have hm2 : 2 ≤ m := by have := NeZero.pos m; omega
        obtain ⟨y, hy, -⟩ := hhit (s + 1) (by
          intro h
          have h1 : ((1 : ℕ) : ZMod (2 * m - 1)) = 0 := by
            have : s + 1 - s = s - s := by rw [h]
            simpa using this
          exact natCast_ne_zero_of_lt (m := m) (k := 1) (by omega) (by omega) h1)
        rw [hXe] at hy
        exact Finset.notMem_empty _ hy
      subst hm
      omega
    · have hpos := hXne.card_pos
      have h1 : L ≤ X.card * L := Nat.le_mul_of_pos_left L hpos
      have h2 : X.card * L + 2 * L - 1 ≤ X.card * (X.card * L + 2 * L - 1) :=
        Nat.le_mul_of_pos_left _ hpos
      generalize X.card * (X.card * L + 2 * L - 1) = q at h2 ⊢
      generalize X.card * L = q' at h1 h2
      omega

/-- The new edges `A'' = A ∖ F_s` of a core `A` (`cod-149-core-sharpening.md`, Setup). -/
def coreNew (s : ZMod (2 * m - 1)) (A : Finset (Sym2 (Vertex m))) : Finset (Sym2 (Vertex m)) :=
  A.filter fun e ↦ e ∉ (factor m s).toGraph.edgeSet

/-- The vertex set `X = V(A'')` of the new edges of a core (`factor-tail-L-test.md`, proof of
Theorem C′). -/
def coreDefect (s : ZMod (2 * m - 1)) (A : Finset (Sym2 (Vertex m))) : Finset (Vertex m) :=
  (uncovered (coreNew s A))ᶜ

/-- `v ∈ V(A'')` iff some new edge contains `v`. -/
theorem mem_coreDefect {s : ZMod (2 * m - 1)} {A : Finset (Sym2 (Vertex m))} {v : Vertex m} :
    v ∈ coreDefect s A ↔ ∃ e ∈ coreNew s A, v ∈ e := by
  simp [coreDefect, mem_uncovered]

/-- **Theorem B(i) for cores** (`cod-149-core-sharpening.md`, Theorem B(i), at prime `n`). Let `A`
leave some vertex uncovered. For `t ≠ s`, every closed alternating cycle `C` of `A ∪ F_t` meets
`V(A'')`: otherwise `C` would be closed under `F_s` and `F_t`, hence all of `V_m`. -/
theorem exists_mem_coreDefect (hp : (2 * m - 1).Prime) {A : Finset (Sym2 (Vertex m))}
    (hU : (uncovered A).Nonempty) {s t : ZMod (2 * m - 1)} (hts : t ≠ s)
    {C : Finset (Vertex m)} (hC : C.Nonempty) (hCA : ∀ v ∈ C, ∃ w ∈ C, s(v, w) ∈ A)
    (hCt : ∀ v ∈ C, (factor m t).mate v ∈ C) : ∃ y ∈ C, y ∈ coreDefect s A := by
  by_contra hno
  push Not at hno
  have hCs : ∀ v ∈ C, (factor m s).mate v ∈ C := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hCA v hv
    have hnot : s(v, w) ∉ coreNew s A := fun h ↦
      hno v hv (mem_coreDefect.mpr ⟨_, h, Sym2.mem_mk_left v w⟩)
    have hF : s(v, w) ∈ (factor m s).toGraph.edgeSet := by
      by_contra hF
      exact hnot (Finset.mem_filter.mpr ⟨hvw, hF⟩)
    rw [(SimpleGraph.mem_edgeSet _).mp hF]
    exact hw
  obtain ⟨u, hu⟩ := hU
  obtain ⟨y, hy⟩ := hC
  by_cases huC : u ∈ C
  · obtain ⟨w, -, huw⟩ := hCA u huC
    exact mem_uncovered.mp hu _ huw (Sym2.mem_mk_left u w)
  · exact not_ham_of_closed (factor m s) (factor m t) (C : Set (Vertex m)) hCs hCt hy huC
      (ham_factor_of_ne hp (Ne.symm hts))

/-- **Theorem C′, core form** (`factor-tail-L-test.md`, Theorem C′ for a core; NG-B(b) of
`sqrt-m-obstructions.md` §1.3). Let `n = 2m - 1` be prime and `A` a partial matching of `V_m`
with `|A| ≤ m - 1`, and put `k = |A ∖ F_s|`. Suppose every `t ≠ s` has a closed alternating cycle
of `A ∪ F_t` with at most `L` edges of `A`, given as a nonempty vertex set `C` with `|C| ≤ 2L`,
covered by edges of `A` inside `C` and closed under `F_t`. Then `n - 1 ≤ 2k((2k + 2)L - 1)`. -/
theorem core_certLength_bound (hp : (2 * m - 1).Prime) {A : Finset (Sym2 (Vertex m))}
    (hA : IsPartialMatching A) (hAm : A.card < m) (s : ZMod (2 * m - 1)) {L : ℕ}
    (hcert : ∀ t ≠ s, ∃ C : Finset (Vertex m), C.Nonempty ∧ C.card ≤ 2 * L ∧
      (∀ v ∈ C, ∃ w ∈ C, s(v, w) ∈ A) ∧ ∀ v ∈ C, (factor m t).mate v ∈ C) :
    2 * m - 2 ≤ 2 * (coreNew s A).card * ((2 * (coreNew s A).card + 2) * L - 1) := by
  have hV : Even (Fintype.card (Vertex m)) := by
    rw [card_vertex]
    exact even_two_mul m
  have hU : (uncovered A).Nonempty := uncovered_nonempty hV hA (by rw [card_vertex]; omega)
  have hA'' : IsPartialMatching (coreNew s A) :=
    ⟨fun e he ↦ hA.1 e (Finset.filter_subset _ _ he),
      fun e he f hf ↦ hA.2 e (Finset.filter_subset _ _ he) f (Finset.filter_subset _ _ hf)⟩
  have hX : (coreDefect s A).card = 2 * (coreNew s A).card := (two_mul_card_eq hV hA'').symm
  obtain ⟨P, hPA⟩ := exists_superset hV hA
  have hhit : ∀ t ≠ s, ∃ y ∈ coreDefect s A, ∃ i < L, walkEnd s t y i ∈ coreDefect s A := by
    intro t hts
    obtain ⟨C, hCne, hCL, hCA, hCt⟩ := hcert t hts
    obtain ⟨y, hyC, hyX⟩ := exists_mem_coreDefect hp hU hts hCne hCA hCt
    have hPC : ∀ v ∈ C, P.mate v ∈ C := fun v hv ↦ by
      obtain ⟨w, hw, hvw⟩ := hCA v hv
      rw [mate_eq_of_mem hPA hvw]
      exact hw
    obtain ⟨r, hr1, hrC, hcyc⟩ := exists_pow_eq_of_closed P (factor m t) hPC hCt hyC
    have hyP : P.mate y ∈ coreDefect s A := by
      obtain ⟨e, he, hye⟩ := mem_coreDefect.mp hyX
      obtain ⟨w, rfl⟩ : ∃ w, s(y, w) = e := ⟨_, Sym2.other_spec hye⟩
      rw [mate_eq_of_mem hPA (Finset.filter_subset _ _ he)]
      exact mem_coreDefect.mpr ⟨_, he, Sym2.mem_mk_right y w⟩
    have horb : ∀ j : ℕ, (certPerm P t ^ j) y ∈ C := by
      intro j
      induction j with
      | zero => exact hyC
      | succ j ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hPC _ (hCt _ ih)
    have hagree : ∀ j < r, (factor m t).mate ((certPerm P t ^ j) y) ∉ coreDefect s A →
        P.mate ((factor m t).mate ((certPerm P t ^ j) y)) =
          (factor m s).mate ((factor m t).mate ((certPerm P t ^ j) y)) := by
      intro j _ hj
      obtain ⟨w, -, hvw⟩ := hCA _ (hCt _ (horb j))
      rw [mate_eq_of_mem hPA hvw]
      have hnot : s((factor m t).mate ((certPerm P t ^ j) y), w) ∉ coreNew s A := fun h ↦
        hj (mem_coreDefect.mpr ⟨_, h, Sym2.mem_mk_left _ w⟩)
      have hF : s((factor m t).mate ((certPerm P t ^ j) y), w) ∈
          (factor m s).toGraph.edgeSet := by
        by_contra hF
        exact hnot (Finset.mem_filter.mpr ⟨hvw, hF⟩)
      rw [SimpleGraph.mem_edgeSet, toGraph_adj] at hF
      exact hF.symm
    obtain ⟨i, hi, hiX⟩ := exists_walkEnd_mem_of_agree P s t (coreDefect s A) hyP hr1 hcyc hagree
    exact ⟨y, hyX, i, by omega, hiX⟩
  have h := certLength_bound_of_hit hp s (coreDefect s A) hhit
  rw [hX] at h
  rwa [add_mul]

end RoundRobin.Canonical

end Pairing
