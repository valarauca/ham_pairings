import Repair.FactorCap.Construction
import Suppression.Density

/-!
# P9, the factor-tail cap `ρ(T(n)) ≤ 5` (task T7)

Put `n = 2m - 1`. The default gadget is `G0 = {1, …, 6}`, and its three edges `{1, 6}, {2, 5},
{3, 4}` lie in the factor `F_{s0}` with `s0 = 7/2 = m + 3` (`capCenter`). The factor tail is
`T(n) = F_{s0} ∖ {16, 25, 34}`, the restriction of `F_{s0}` to `V_m ∖ G0` (`factorTail`).

The coordinate `x = 2v - 7` (`capAffine`) sends `F_{s0}` to `F_0` and `G0` to the ends
`±1, ±3, ±5`. `capState` is `P_q` pulled back to the original labels.

* `isZeroState_capState` : `P_q` is a zero state at every prime `n ≥ 17`, by
  `isZeroState_capMatching` and `isZeroState_affine_smul_iff`.
* `tailDist_capState_le` : `|T(n) ∖ P_q| ≤ 5`. By `two_mul_tailDist` this is the count of tail
  vertices that `T(n)` and `P_q` pair differently. Such a vertex is an end of `D` outside the
  gadget, and there are `16 - 6 = 10` of them. `tailDist_capState` : all ten differ, so
  `|T(n) ∖ P_q| = 5` exactly.
* `factorTail_cap` : P9. For prime `n = 2m - 1 ≥ 17` some zero state is within 5 edges of
  `T(n)`, so `ρ(T(n)) ≤ 5`.

Source: `results/cod-186-archive-cap-check.md` (claim C1 and the construction of `P_q`),
`results/cod-186-direct-construction-spike.md` (Lemma 4 and the factor tail `T(n)`), and
`results/lean-scope-p9-p10.md` §3, task T7.
-/

namespace Pairing

namespace FactorCap

open RoundRobin hiding factor
open RoundRobin.Canonical PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The centre `s0 = 7/2 = m + 3` of the factor that contains the gadget edges. -/
def capCenter (m : ℕ) : ZMod (2 * m - 1) :=
  ((m + 3 : ℕ) : ZMod (2 * m - 1))

/-- `2 s0 = 7`. -/
theorem two_mul_capCenter : 2 * capCenter m = 7 := by
  rw [capCenter]
  push_cast
  linear_combination (two_mul_natCast_self (m := m))

/-- The default gadget `G0 = {1, …, 6}`. -/
def gadget (m : ℕ) : Finset (Vertex m) :=
  (Finset.Icc 1 6).image fun k : ℕ ↦ some (k : ZMod (2 * m - 1))

/-- `F_{s0}` maps the gadget to itself, `v ↦ 7 - v`. -/
theorem factor_capCenter_mem_gadget (hm : 5 ≤ m) {v : Vertex m} (hv : v ∈ gadget m) :
    (factor m (capCenter m)).mate v ∈ gadget m := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
  rw [Finset.mem_Icc] at hk
  have hne : (k : ZMod (2 * m - 1)) ≠ capCenter m := fun h ↦ by
    have := natCast_injOn (m := m) (by omega) (by omega) h
    omega
  rw [factor, factor_mate, mateFn_of_ne _ _ hne, two_mul_capCenter]
  refine Finset.mem_image.2 ⟨7 - k, Finset.mem_Icc.2 (by omega), ?_⟩
  simp [Nat.cast_sub (show k ≤ 7 by omega)]

/-- `F_{s0}` maps the complement of the gadget to itself. -/
theorem factor_capCenter_mem_compl (hm : 5 ≤ m) :
    ∀ v ∈ (gadget m)ᶜ, (factor m (capCenter m)).mate v ∈ (gadget m)ᶜ := by
  intro v hv
  rw [Finset.mem_compl] at hv ⊢
  intro h
  exact hv (by simpa using factor_capCenter_mem_gadget hm h)

/-- The factor tail `T(n) = F_{s0} ∖ {16, 25, 34}`, the perfect matching of `V_m ∖ G0` cut out
of `F_{s0}`. -/
def factorTail (m : ℕ) [NeZero m] (hm : 5 ≤ m) :
    PerfectMatching ((gadget m)ᶜ : Finset (Vertex m)) :=
  restrict (factor m (capCenter m)) (gadget m)ᶜ (factor_capCenter_mem_compl hm)

/-- The partner of a tail vertex in `T(n)` is its partner in `F_{s0}`. -/
theorem factorTail_mate (hm : 5 ≤ m) (u : ((gadget m)ᶜ : Finset (Vertex m))) :
    ((factorTail m hm).mate u : Vertex m) = (factor m (capCenter m)).mate u :=
  rfl

/-- The coordinate change `x = 2v - 7`. -/
noncomputable def capAffine (m : ℕ) [NeZero m] : Equiv.Perm (Vertex m) :=
  shift m (-7) * scale m (isUnit_two (modulus_odd m)).unit

/-- `capAffine` sends `v` to `2v - 7`. -/
theorem capAffine_some (v : ZMod (2 * m - 1)) : capAffine m (some v) = some (2 * v - 7) := by
  simp [capAffine, sub_eq_add_neg]

/-- `capAffine` maps `F_t` to `F_{2t - 7}`. -/
theorem capAffine_smul_factor (t : ZMod (2 * m - 1)) :
    capAffine m • factor m t = factor m (2 * t - 7) := by
  rw [capAffine, affine_smul_factor, IsUnit.unit_spec, sub_eq_add_neg]

/-- `capAffine` maps `F_{s0}` to `F_0`, pointwise. -/
theorem capAffine_factor_capCenter_mate (v : Vertex m) :
    capAffine m ((factor m (capCenter m)).mate v) = (factor m 0).mate (capAffine m v) := by
  have h := capAffine_smul_factor (m := m) (capCenter m)
  rw [two_mul_capCenter, sub_self] at h
  rw [← h, smul_mate]
  simp

/-- The zero state `P_q` in the original labels, `capAffine⁻¹ • capMatching`. -/
noncomputable def capState (m : ℕ) [NeZero m] (hm : 9 ≤ m) : PerfectMatching (Vertex m) :=
  (capAffine m)⁻¹ • capMatching m hm

/-- `capAffine` maps `P_q` back to `capMatching`, pointwise. -/
theorem capAffine_capState_mate (hm : 9 ≤ m) (v : Vertex m) :
    capAffine m ((capState m hm).mate v) = (capMatching m hm).mate (capAffine m v) := by
  rw [capState, smul_mate, inv_inv]
  simp

/-- `P_q` is a zero state for prime `n = 2m - 1 ≥ 17`. -/
theorem isZeroState_capState (hp : (2 * m - 1).Prime) (hm : 9 ≤ m) :
    IsZeroState (factor m) (capState m hm) := by
  refine (isZeroState_affine_smul_iff m (isUnit_two (modulus_odd m)).unit (-7) _).1 ?_
  have h : capAffine m • capState m hm = capMatching m hm := smul_inv_smul _ _
  rw [capAffine] at h
  rw [h]
  exact isZeroState_capMatching hp hm

/-- The six gadget ends `±1, ±3, ±5` are the images of `1, …, 6` under `x = 2v - 7`. -/
theorem exists_capAffine_eq_endVtx {ε : ℕ} (hε : ε < 6) :
    ∃ k : ℕ, k ∈ Finset.Icc 1 6 ∧ capAffine m (some (k : ZMod (2 * m - 1))) = endVtx m ε := by
  interval_cases ε
  · exact ⟨4, by decide, by rw [capAffine_some, endVtx, show endInt 0 = 1 by decide]; norm_num⟩
  · exact ⟨3, by decide, by rw [capAffine_some, endVtx, show endInt 1 = -1 by decide]; norm_num⟩
  · exact ⟨5, by decide, by rw [capAffine_some, endVtx, show endInt 2 = 3 by decide]; norm_num⟩
  · exact ⟨2, by decide, by rw [capAffine_some, endVtx, show endInt 3 = -3 by decide]; norm_num⟩
  · exact ⟨6, by decide, by rw [capAffine_some, endVtx, show endInt 4 = 5 by decide]; norm_num⟩
  · exact ⟨1, by decide, by rw [capAffine_some, endVtx, show endInt 5 = -5 by decide]; norm_num⟩

/-- A vertex sent to one of the six gadget ends `±1, ±3, ±5` lies in the gadget. -/
theorem mem_gadget_of_capAffine_eq {v : Vertex m} {ε : ℕ} (hε : ε < 6)
    (hv : capAffine m v = endVtx m ε) : v ∈ gadget m := by
  obtain ⟨k, hk, hk'⟩ := exists_capAffine_eq_endVtx (m := m) hε
  rw [(capAffine m).injective (hv.trans hk'.symm)]
  exact Finset.mem_image.2 ⟨k, hk, rfl⟩

/-- `|T(n) ∖ P_q| ≤ 5`. The tail vertices that `T(n)` and `P_q` pair differently are ends of `D`
outside the gadget, and there are ten of them. -/
theorem tailDist_capState_le (hm : 9 ≤ m) :
    tailDist (capState m hm) (factorTail m (by omega)) ≤ 5 := by
  have h2 := two_mul_tailDist (capState m hm) (factorTail m (by omega))
  suffices hcard : (Finset.univ.filter fun u : ((gadget m)ᶜ : Finset (Vertex m)) ↦
      ((factorTail m (by omega)).mate u : Vertex m) ≠ (capState m hm).mate u).card ≤ 10 by
    omega
  have hT : ((Finset.Ico 6 16).image fun ε ↦ (capAffine m)⁻¹ (endVtx m ε)).card ≤ 10 :=
    Finset.card_image_le.trans (by simp)
  refine (Finset.card_le_card_of_injOn (fun u : ((gadget m)ᶜ : Finset (Vertex m)) ↦ (u : Vertex m))
    ?_ Subtype.val_injective.injOn).trans hT
  intro u hu
  replace hu := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
  rw [factorTail_mate] at hu
  have hne : (factor m 0).mate (capAffine m u) ≠ (capMatching m hm).mate (capAffine m u) := by
    rw [← capAffine_factor_capCenter_mate, ← capAffine_capState_mate]
    exact fun h ↦ hu ((capAffine m).injective h)
  obtain ⟨ε, hε, hεu⟩ : ∃ ε < 16, capAffine m u = endVtx m ε := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact hne (capMatching_of_ne_endVtx hm hcon).symm
  have h6 : 6 ≤ ε := by
    by_contra h6
    exact (Finset.mem_compl.1 u.2) (mem_gadget_of_capAffine_eq (by omega) hεu)
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨ε, Finset.mem_Ico.2 ⟨h6, hε⟩, ?_⟩)
  rw [← hεu]
  simp

/-- P9, the factor-tail cap. For every prime `n = 2m - 1 ≥ 17` the zero state `P_q` is within 5
edges of the factor tail `T(n)` of the default gadget, so `ρ(T(n)) ≤ 5`. This is claim C1 of
`cod-186-archive-cap-check.md` at prime `n`. -/
theorem factorTail_cap (hp : (2 * m - 1).Prime) (hn : 17 ≤ 2 * m - 1) :
    ∃ P : ZeroState m, tailDist P.1 (factorTail m (by omega)) ≤ 5 :=
  ⟨⟨capState m (by omega), isZeroState_capState hp (by omega)⟩, tailDist_capState_le (by omega)⟩

/-- Integers in `[-8, 8]` are determined by their residues mod `2m - 1` for `m ≥ 9`. -/
theorem intCast_inj_of_small (hm : 9 ≤ m) {a b : ℤ} (ha : -8 ≤ a ∧ a ≤ 8) (hb : -8 ≤ b ∧ b ≤ 8)
    (h : (a : ZMod (2 * m - 1)) = b) : a = b := by
  have h1 : ((a : ℤ) : ZMod (2 * m - 1)).valMinAbs = a :=
    valMinAbs_eq_of_eq rfl (by omega) (by omega)
  have h2 : ((b : ℤ) : ZMod (2 * m - 1)).valMinAbs = b :=
    valMinAbs_eq_of_eq rfl (by omega) (by omega)
  rw [← h1, ← h2, h]

/-- The end labels are distinct. -/
theorem endInt_injOn : ∀ ε < 16, ∀ ε' < 16, endInt ε = endInt ε' → ε = ε' := by
  decide

/-- The ten ends outside the gadget are not of the form `2k - 7` with `1 ≤ k ≤ 6`. -/
theorem endInt_ne_gadget :
    ∀ ε < 16, 6 ≤ ε → ∀ k : ℕ, k < 7 → 1 ≤ k → endInt ε ≠ 2 * (k : ℤ) - 7 := by
  decide

/-- `Q` moves every end: `capInt (endInt ε) ≠ -endInt ε`, and `capInt (endInt ε) ∈ [-8, 8]`. -/
theorem capInt_endInt_ne_neg : ∀ ε < 16,
    capInt (endInt ε) ≠ -endInt ε ∧ -8 ≤ capInt (endInt ε) ∧ capInt (endInt ε) ≤ 8 := by
  decide

/-- `|T(n) ∖ P_q| = 5` exactly. The ten ends of `D` outside the gadget are exactly the tail
vertices that `T(n)` and `P_q` pair differently, and `two_mul_tailDist` counts them. -/
theorem tailDist_capState (hm : 9 ≤ m) :
    tailDist (capState m hm) (factorTail m (by omega)) = 5 := by
  have hle := tailDist_capState_le hm
  have h2 := two_mul_tailDist (capState m hm) (factorTail m (by omega))
  set F := Finset.univ.filter fun u : ((gadget m)ᶜ : Finset (Vertex m)) ↦
    ((factorTail m (by omega)).mate u : Vertex m) ≠ (capState m hm).mate u with hF
  set g : ℕ → Vertex m := fun ε ↦ (capAffine m)⁻¹ (endVtx m ε) with hg
  have hsmall : ∀ ε < 16, -8 ≤ endInt ε ∧ endInt ε ≤ 8 := fun ε hε ↦ (endInt_bounds ε hε).2
  have hginj : Set.InjOn g (Finset.Ico 6 16 : Finset ℕ) := by
    intro ε hε ε' hε' h
    rw [Finset.coe_Ico, Set.mem_Ico] at hε hε'
    have h' : endVtx m ε = endVtx m ε' := (capAffine m)⁻¹.injective h
    rw [endVtx, endVtx, Option.some.injEq] at h'
    exact endInt_injOn ε (by omega) ε' (by omega)
      (intCast_inj_of_small hm (hsmall ε (by omega)) (hsmall ε' (by omega)) h')
  have hT : ((Finset.Ico 6 16).image g).card = 10 := by
    rw [Finset.card_image_of_injOn hginj]
    simp
  have hsub : (Finset.Ico 6 16).image g ⊆ F.image Subtype.val := by
    intro v hv
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_Ico] at hε
    have hσ : capAffine m (g ε) = endVtx m ε := by simp [hg]
    have hcomp : g ε ∈ (gadget m)ᶜ := by
      rw [Finset.mem_compl]
      intro hG
      obtain ⟨k, hk, hkv⟩ := Finset.mem_image.1 hG
      rw [Finset.mem_Icc] at hk
      rw [← hkv, capAffine_some, endVtx, Option.some.injEq] at hσ
      have hk' : ((2 * k - 7 : ℤ) : ZMod (2 * m - 1)) = (endInt ε : ZMod (2 * m - 1)) := by
        push_cast
        exact hσ
      exact endInt_ne_gadget ε hε.2 hε.1 k (by omega) hk.1
        (intCast_inj_of_small hm (by omega) (hsmall ε hε.2) hk').symm
    refine Finset.mem_image.2 ⟨⟨g ε, hcomp⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [factorTail_mate]
    intro h
    have h' := congrArg (capAffine m) h
    obtain ⟨hne, hc1, hc2⟩ := capInt_endInt_ne_neg ε hε.2
    obtain ⟨h0, h1, h3⟩ := endInt_bounds ε hε.2
    have hv : ((endInt ε : ℤ) : ZMod (2 * m - 1)).valMinAbs = endInt ε :=
      valMinAbs_eq_of_eq rfl (by omega) (by omega)
    have hz : ((endInt ε : ℤ) : ZMod (2 * m - 1)) ≠ 0 := by
      rw [Ne, ← ZMod.valMinAbs_eq_zero, hv]
      exact h0
    rw [capAffine_factor_capCenter_mate, capAffine_capState_mate, hσ, capMatching_mate, endVtx,
      capFn, ite_eq_right hz, hv, factor, factor_mate, mateFn_of_ne _ _ hz, Option.some.injEq] at h'
    have h'' : ((-endInt ε : ℤ) : ZMod (2 * m - 1)) = (capInt (endInt ε) : ZMod (2 * m - 1)) := by
      push_cast
      rw [← h']
      ring
    exact hne (intCast_inj_of_small hm (by omega) ⟨hc1, hc2⟩ h'').symm
  have hge : 10 ≤ F.card :=
    hT ▸ (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

end FactorCap

end Pairing
