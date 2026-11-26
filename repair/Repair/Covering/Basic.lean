import Pairing.RoundRobin
import Repair.Forcing

/-!
# Covering maps between round-robin structures (`covering-spike.md`)

Fix `a ∣ n` with `n` odd, and put `k = n / a`. Reduction mod `a` is the map
`proj h : V_n → V_a` on `Option (ZMod n)`, with `π ∞ = ∞`. Its finite fibres have `k` points.

* `Subordinate h P' P` (§1) : every edge of `P` projects to an edge of `P'` or to a single
  point. `IsCoveringLift h P' P` : moreover no edge of `P` lies inside a fibre other than the
  branch fibre over `P'(∞)`.
* `factor_subordinate` : `F_t` is subordinate to `F_{t mod a}`.
* `pullback_invariant` (Lemma 1) : a set invariant under `P'` and `F_{t'}` pulls back to a set
  invariant under every subordinate `P` and every `F_t` with `t ≡ t'`.
* `exists_closed_of_not_ham` : the converse of `not_ham_of_closed`.
* `not_ham_of_subordinate`, `ham_proj` (Corollary 2) : Hamiltonicity projects along `π`.
  `card_ham_le` : `X_n(P) ≤ k · X_a(P')`. `isUnit_sub_of_ham` : the "only if" half of the
  gcd law, `F_s ∪ F_t` one cycle forces `t - s` to be a unit.
* `isZeroState_of_subordinate` (Theorem 5) : every matching subordinate to a zero state is a
  zero state. This is the odd-divisor lifting theorem of `old-personal-chatgpt` doc
  01a1e303-3c8c-7386-b5e8-578014fbf101 §3, whose block-internal matchings are exactly the
  subordinate ones. `Canonical.isZeroState_of_subordinate` is the same for `V_{m'} ← V_m`.
* `LiesOver h A' A`, `blocks_lift` (Lemma 6) : a factor dead for a base core is dead for every
  core lying over it. `liesOver_sdiff`, `blocks_lift_sdiff` : the form `A = Λ \ S` of §3.
-/

namespace Pairing

namespace RoundRobin

namespace Covering

open PerfectMatching

variable {a n : ℕ}

/-- Reduction mod `a`, the map `π : V_n → V_a` with `π ∞ = ∞`. (`covering-spike.md` §1) -/
def proj (h : a ∣ n) (v : Option (ZMod n)) : Option (ZMod a) :=
  v.map (ZMod.castHom h (ZMod a))

/-- `π ∞ = ∞`. (`covering-spike.md` §1) -/
@[simp]
theorem proj_none (h : a ∣ n) : proj h none = none :=
  rfl

/-- `π x = x mod a` on finite vertices. (`covering-spike.md` §1) -/
@[simp]
theorem proj_some (h : a ∣ n) (x : ZMod n) :
    proj h (some x) = some (ZMod.castHom h (ZMod a) x) :=
  rfl

/-- `π` is onto. (`covering-spike.md` §1) -/
theorem proj_surjective (h : a ∣ n) : Function.Surjective (proj h) := by
  rintro (_ | x')
  · exact ⟨none, rfl⟩
  · obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod a)) x'
    exact ⟨some x, by rw [proj_some, hx]⟩

/-- `P` is subordinate to `P'` (`covering-spike.md` §1) when every edge `{v, P v}` of `P`
projects to the edge `{π v, P' (π v)}` of `P'` or to the single point `π v`. Equivalently `P`
refines the partition of `V_n` into the preimages of the edges of `P'`. -/
def Subordinate (h : a ∣ n) (P' : PerfectMatching (Option (ZMod a)))
    (P : PerfectMatching (Option (ZMod n))) : Prop :=
  ∀ v, proj h (P.mate v) = P'.mate (proj h v) ∨ proj h (P.mate v) = proj h v

/-- A covering lift of `P'` (`covering-spike.md` §1) is a subordinate `P` with no edge inside a
fibre other than the branch fibre over `b' = P'(∞)`. -/
def IsCoveringLift (h : a ∣ n) (P' : PerfectMatching (Option (ZMod a)))
    (P : PerfectMatching (Option (ZMod n))) : Prop :=
  Subordinate h P' P ∧ ∀ v, proj h (P.mate v) = proj h v → proj h v = P'.mate none

instance [NeZero n] (h : a ∣ n) (P' : PerfectMatching (Option (ZMod a)))
    (P : PerfectMatching (Option (ZMod n))) : Decidable (Subordinate h P' P) :=
  inferInstanceAs (Decidable (∀ _, _ ∨ _))

instance [NeZero n] (h : a ∣ n) (P' : PerfectMatching (Option (ZMod a)))
    (P : PerfectMatching (Option (ZMod n))) : Decidable (IsCoveringLift h P' P) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

/-- A covering lift is subordinate. (`covering-spike.md` §1) -/
theorem IsCoveringLift.subordinate {h : a ∣ n} {P' : PerfectMatching (Option (ZMod a))}
    {P : PerfectMatching (Option (ZMod n))} (hP : IsCoveringLift h P' P) : Subordinate h P' P :=
  hP.1

/-- A subordinate matching maps the preimage of a `P'`-invariant set into itself.
(`covering-spike.md` §1) -/
theorem mate_mem_preimage {h : a ∣ n} {P' : PerfectMatching (Option (ZMod a))}
    {P : PerfectMatching (Option (ZMod n))} (hP : Subordinate h P' P)
    {S' : Set (Option (ZMod a))} (hS : ∀ v ∈ S', P'.mate v ∈ S') {v : Option (ZMod n)}
    (hv : proj h v ∈ S') : proj h (P.mate v) ∈ S' := by
  rcases hP v with e | e <;> rw [e]
  · exact hS _ hv
  · exact hv

/-- `F_t` is subordinate to `F_{t mod a}` (`covering-spike.md` §1). Its edges `{x, 2t - x}`
project to edges of `F_{t'}` except the pairs `t ± ja`, which project to the point `t'`. -/
theorem factor_subordinate (ha : Odd a) (hn : Odd n) (h : a ∣ n) (t : ZMod n) :
    Subordinate h (factor ha (ZMod.castHom h (ZMod a) t)) (factor hn t) := by
  rintro (_ | x)
  · left
    simp
  rcases eq_or_ne x t with rfl | hxt
  · left
    simp
  rw [factor_mate, factor_mate, mateFn_of_ne t x hxt, proj_some, proj_some, map_sub, map_mul,
    map_ofNat]
  rcases eq_or_ne (ZMod.castHom h (ZMod a) x) (ZMod.castHom h (ZMod a) t) with hx' | hx'
  · right
    rw [hx', Option.some_inj]
    ring
  · left
    rw [mateFn_of_ne _ _ hx']

/-- **Lemma 1 (pullback)**, `covering-spike.md` §1. If `S' ⊆ V_a` is invariant under `P'` and
`F_{t'}`, then `π⁻¹(S')` is invariant under every `P` subordinate to `P'` and under `F_t` for
every `t ≡ t' (mod a)`. -/
theorem pullback_invariant (ha : Odd a) (hn : Odd n) (h : a ∣ n)
    {P' : PerfectMatching (Option (ZMod a))} {P : PerfectMatching (Option (ZMod n))}
    (hP : Subordinate h P' P) {t' : ZMod a} {S' : Set (Option (ZMod a))}
    (hSP : ∀ v ∈ S', P'.mate v ∈ S') (hSF : ∀ v ∈ S', (factor ha t').mate v ∈ S') {t : ZMod n}
    (ht : ZMod.castHom h (ZMod a) t = t') :
    (∀ v ∈ proj h ⁻¹' S', P.mate v ∈ proj h ⁻¹' S') ∧
      ∀ v ∈ proj h ⁻¹' S', (factor hn t).mate v ∈ proj h ⁻¹' S' := by
  subst ht
  exact ⟨fun _ hv ↦ mate_mem_preimage hP hSP hv,
    fun _ hv ↦ mate_mem_preimage (factor_subordinate ha hn h t) hSF hv⟩

/-- The converse of `not_ham_of_closed`. If `P ∪ Q` is not one cycle, some nonempty vertex set
closed under both matchings misses a vertex. (`covering-spike.md` §1) -/
theorem exists_closed_of_not_ham {V : Type*} [Nonempty V] {X Y : PerfectMatching V}
    (hXY : ¬Ham X Y) :
    ∃ B : Set V, (∀ v ∈ B, X.mate v ∈ B) ∧ (∀ v ∈ B, Y.mate v ∈ B) ∧ B.Nonempty ∧ ∃ w, w ∉ B := by
  have hp : ¬(X.toGraph ⊔ Y.toGraph).Preconnected := fun hp ↦ hXY ⟨hp⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  obtain ⟨u, w, huw⟩ := hp
  refine ⟨{v | (X.toGraph ⊔ Y.toGraph).Reachable u v}, fun v hv ↦ hv.trans ?_,
    fun v hv ↦ hv.trans ?_, ⟨u, SimpleGraph.Reachable.refl _⟩, w, huw⟩
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl rfl))
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr rfl))

/-- A proper nonempty set invariant under `P'` and `F_{t mod a}` pulls back to a proper
nonempty set invariant under `P` and `F_t` (`covering-spike.md` §1, Corollary 2). -/
theorem not_ham_of_subordinate (ha : Odd a) (hn : Odd n) (h : a ∣ n)
    {P' : PerfectMatching (Option (ZMod a))} {P : PerfectMatching (Option (ZMod n))}
    (hP : Subordinate h P' P) {t : ZMod n}
    (hP' : ¬Ham P' (factor ha (ZMod.castHom h (ZMod a) t))) : ¬Ham P (factor hn t) := by
  obtain ⟨B, hBP, hBF, ⟨u', hu'⟩, w', hw'⟩ := exists_closed_of_not_ham hP'
  obtain ⟨u, rfl⟩ := proj_surjective h u'
  obtain ⟨w, rfl⟩ := proj_surjective h w'
  obtain ⟨h1, h2⟩ := pullback_invariant ha hn h hP hBP hBF rfl
  exact not_ham_of_closed P (factor hn t) (proj h ⁻¹' B) h1 h2 hu' hw'

/-- **Corollary 2 (projection)**, `covering-spike.md` §1. If `P` is subordinate to `P'` and
`P ∪ F_t` is one cycle, then `P' ∪ F_{t mod a}` is one cycle. -/
theorem ham_proj (ha : Odd a) (hn : Odd n) (h : a ∣ n)
    {P' : PerfectMatching (Option (ZMod a))} {P : PerfectMatching (Option (ZMod n))}
    (hP : Subordinate h P' P) {t : ZMod n} (hH : Ham P (factor hn t)) :
    Ham P' (factor ha (ZMod.castHom h (ZMod a) t)) := by
  by_contra hc
  exact not_ham_of_subordinate ha hn h hP hc hH

/-- Each fibre of `ℤ/n → ℤ/a` has `k = n / a` points. (`covering-spike.md` §1) -/
theorem card_fiber (h : a ∣ n) [NeZero n] (t' : ZMod a) :
    (Finset.univ.filter fun t : ZMod n ↦ ZMod.castHom h (ZMod a) t = t').card = n / a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (Nat.eq_zero_of_zero_dvd h)
  have : NeZero a := ⟨ha0⟩
  set f := ZMod.castHom h (ZMod a)
  have hall : ∀ y : ZMod a, (Finset.univ.filter fun t : ZMod n ↦ f t = y).card =
      (Finset.univ.filter fun t : ZMod n ↦ f t = t').card := fun y ↦
    AddMonoidHom.card_fiber_eq_of_mem_range f (ZMod.ringHom_surjective f y)
      (ZMod.ringHom_surjective f t')
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (ZMod n)))
    (t := (Finset.univ : Finset (ZMod a))) (f := f) (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.sum_congr rfl fun y _ ↦ hall y, Finset.sum_const, Finset.card_univ,
    Finset.card_univ, ZMod.card, ZMod.card, smul_eq_mul] at hsum
  exact (Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero ha0) (hsum.trans (mul_comm _ _))).symm

/-- The count bound of Corollary 2, `covering-spike.md` §1. For `P` subordinate to `P'`,
`X_n(P) ≤ k · X_a(P')` with `k = n / a`, where `X(P)` counts the `t` with `P ∪ F_t` one
cycle. -/
theorem card_ham_le (ha : Odd a) (hn : Odd n) (h : a ∣ n) [NeZero a] [NeZero n]
    {P' : PerfectMatching (Option (ZMod a))} {P : PerfectMatching (Option (ZMod n))}
    (hP : Subordinate h P' P) :
    (Finset.univ.filter fun t ↦ Ham P (factor hn t)).card ≤
      n / a * (Finset.univ.filter fun t' ↦ Ham P' (factor ha t')).card := by
  set s := Finset.univ.filter fun t ↦ Ham P (factor hn t)
  refine (Finset.card_le_mul_card_image (f := ZMod.castHom h (ZMod a)) s (n / a)
    fun t' _ ↦ ?_).trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  · rw [← card_fiber h t']
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
  · intro t' ht'
    obtain ⟨t, hts, rfl⟩ := Finset.mem_image.mp ht'
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hts ⊢
    exact ham_proj ha hn h hP hts

/-- `X ∪ X` is not one cycle once `V` has a third vertex. (`covering-spike.md` §1) -/
theorem not_ham_self {V : Type*} (X : PerfectMatching V) {u w : V} (hwu : w ≠ u)
    (hwX : w ≠ X.mate u) : ¬Ham X X := by
  refine not_ham_of_closed X X {u, X.mate u} (fun v hv ↦ ?_) (fun v hv ↦ ?_) (w := w)
    (Or.inl rfl) ?_
  · rcases hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (X.mate_mate u)
  · rcases hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (X.mate_mate u)
  · rintro (h | h)
    exacts [hwu h, hwX h]

/-- The "only if" half of the gcd law, from Corollary 2 (`covering-spike.md` §1). If
`F_s ∪ F_t` is one cycle then `gcd(t - s, n) = 1`. With `d = gcd(t - s, n) > 1`, both `F_s`
and `F_t` are subordinate to `F_{s mod d}`, whose union with itself is not one cycle. -/
theorem isUnit_sub_of_ham (hn : Odd n) {s t : ZMod n} (hH : Ham (factor hn s) (factor hn t)) :
    IsUnit (t - s) := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  rw [← ZMod.natCast_zmod_val (t - s), ZMod.isUnit_iff_coprime]
  by_contra hc
  set d := Nat.gcd (t - s).val n
  have hdn : d ∣ n := Nat.gcd_dvd_right _ _
  have hdv : d ∣ (t - s).val := Nat.gcd_dvd_left _ _
  have hd : Odd d := Odd.of_dvd_nat hn hdn
  have hd1 : d ≠ 1 := hc
  have hd2 : 2 ≤ d := by
    rcases hd with ⟨j, hj⟩
    omega
  have hst : ZMod.castHom hdn (ZMod d) t = ZMod.castHom hdn (ZMod d) s := by
    rw [← sub_eq_zero, ← map_sub, ← ZMod.natCast_zmod_val (t - s), map_natCast,
      ZMod.natCast_eq_zero_iff]
    exact hdv
  have hH' := ham_proj hd hn hdn (factor_subordinate hd hn hdn s) hH
  rw [hst] at hH'
  refine not_ham_self (factor hd (ZMod.castHom hdn (ZMod d) s)) (u := none)
    (w := some (ZMod.castHom hdn (ZMod d) s + 1)) (by simp) ?_ hH'
  rw [factor_mate, mateFn_none, Ne, Option.some_inj, add_eq_left]
  have : Fact (1 < d) := ⟨hd2⟩
  exact one_ne_zero

/-- **Theorem 5 (zero states lift)**, `covering-spike.md` §2. If `P'` is a zero state of `V_a`,
every `P` subordinate to `P'` is a zero state of `V_n`, for every `t ∈ ℤ/n`. This is the
odd-divisor lifting theorem of `old-personal-chatgpt` doc 01a1e303-3c8c-7386-b5e8-578014fbf101
§3: a matching inside the blocks `R_r ∪ R_s` and `R_{r₀} ∪ {∞}` is a subordinate matching. -/
theorem isZeroState_of_subordinate (ha : Odd a) (hn : Odd n) (h : a ∣ n)
    {P' : PerfectMatching (Option (ZMod a))} {P : PerfectMatching (Option (ZMod n))}
    (hP' : IsZeroState (factor ha) P') (hP : Subordinate h P' P) : IsZeroState (factor hn) P :=
  fun _ ↦ not_ham_of_subordinate ha hn h hP (hP' _)

/-- **Theorem 5** for the canonical structures, `covering-spike.md` §2. If
`2m' - 1 ∣ 2m - 1`, every perfect matching of `V_m` subordinate to a zero state of `V_{m'}` is a
zero state of `V_m`. -/
theorem isZeroState_of_subordinate_canonical {m' m : ℕ} [NeZero m'] [NeZero m]
    (h : 2 * m' - 1 ∣ 2 * m - 1) (P' : Canonical.ZeroState m')
    {P : PerfectMatching (Canonical.Vertex m)} (hP : Subordinate h P'.1 P) :
    IsZeroState (Canonical.factor m) P :=
  Covering.isZeroState_of_subordinate (Canonical.modulus_odd m') (Canonical.modulus_odd m) h
    P'.2 hP

/-- A partial matching `A` of `V_n` lies over a partial matching `A'` of `V_a` when every vertex
over a vertex matched by `A'` is matched by `A` along an edge that projects to that `A'`-edge or
to a single point. -/
def LiesOver (h : a ∣ n) (A' : Finset (Sym2 (Option (ZMod a))))
    (A : Finset (Sym2 (Option (ZMod n)))) : Prop :=
  ∀ v w', s(proj h v, w') ∈ A' → ∃ w, s(v, w) ∈ A ∧ (proj h w = w' ∨ proj h w = proj h v)

/-- **Lemma 6 (dead factors lift)**, `covering-spike.md` §3. If `t'` is dead for the base core
`A'`, meaning `A' ∪ F_{t'}` has a closed alternating cycle (`Blocks`), then every `t ≡ t'` is
dead for every core `A` lying over `A'`. -/
theorem blocks_lift (ha : Odd a) (hn : Odd n) (h : a ∣ n) [NeZero n]
    {A' : Finset (Sym2 (Option (ZMod a)))} {A : Finset (Sym2 (Option (ZMod n)))}
    (hA : LiesOver h A' A) {t' : ZMod a} (hB : Blocks A' (factor ha t')) {t : ZMod n}
    (ht : ZMod.castHom h (ZMod a) t = t') : Blocks A (factor hn t) := by
  classical
  subst ht
  obtain ⟨C', ⟨u', hu'⟩, hCA, hCF⟩ := hB
  obtain ⟨u, rfl⟩ := proj_surjective h u'
  refine ⟨Finset.univ.filter fun v ↦ proj h v ∈ C', ⟨u, by simpa using hu'⟩, fun v hv ↦ ?_,
    fun v hv ↦ ?_⟩
  · rw [Finset.mem_filter] at hv
    obtain ⟨w', hw', hvw'⟩ := hCA _ hv.2
    obtain ⟨w, hw, hpw⟩ := hA v w' hvw'
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hw⟩
    rcases hpw with e | e <;> rw [e]
    exacts [hw', hv.2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact mate_mem_preimage (S' := (C' : Set _)) (factor_subordinate ha hn h t)
      (fun v hv ↦ hCF v hv) hv

/-- Removing edges over `S'` keeps a core over the base core (`covering-spike.md` §3). If `Λ`
lies over `T'`, every edge of `S` projects onto an edge of `S'`, and `S'` has no loop, then
`Λ \ S` lies over `T' \ S'`. -/
theorem liesOver_sdiff (h : a ∣ n) {T' S' : Finset (Sym2 (Option (ZMod a)))}
    {Λ S : Finset (Sym2 (Option (ZMod n)))} (hΛ : LiesOver h T' Λ)
    (hS : ∀ e ∈ S, e.map (proj h) ∈ S') (hS' : ∀ e ∈ S', ¬e.IsDiag) :
    LiesOver h (T' \ S') (Λ \ S) := by
  intro v w' hvw
  rw [Finset.mem_sdiff] at hvw
  obtain ⟨w, hw, hpw⟩ := hΛ v w' hvw.1
  refine ⟨w, Finset.mem_sdiff.mpr ⟨hw, fun hwS ↦ ?_⟩, hpw⟩
  have h1 := hS _ hwS
  rw [Sym2.map_mk] at h1
  rcases hpw with e | e <;> rw [e] at h1
  · exact hvw.2 h1
  · exact hS' _ h1 (Sym2.mk_isDiag_iff.mpr rfl)

/-- **Lemma 6** in the form of `covering-spike.md` §3. If `t'` is dead for the base core
`T' \ S'`, then every `t ≡ t'` is dead for every core `Λ \ S` with `Λ` over `T'` and
`S ⊆ π⁻¹(S')`. -/
theorem blocks_lift_sdiff (ha : Odd a) (hn : Odd n) (h : a ∣ n) [NeZero n]
    {T' S' : Finset (Sym2 (Option (ZMod a)))} {Λ S : Finset (Sym2 (Option (ZMod n)))}
    (hΛ : LiesOver h T' Λ) (hS : ∀ e ∈ S, e.map (proj h) ∈ S') (hS' : ∀ e ∈ S', ¬e.IsDiag)
    {t' : ZMod a} (hB : Blocks (T' \ S') (factor ha t')) {t : ZMod n}
    (ht : ZMod.castHom h (ZMod a) t = t') : Blocks (Λ \ S) (factor hn t) :=
  blocks_lift ha hn h (liesOver_sdiff h hΛ hS hS') hB ht

end Covering

end RoundRobin

end Pairing
