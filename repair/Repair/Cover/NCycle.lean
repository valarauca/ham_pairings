import Pairing.Union
import Repair.Signature

/-!
# Theorem S: Hamiltonicity is an `n`-cycle, and the coset form of covering

Source: `results/sl5-control-extend.md` (organize-archive d185a5e) §2, Theorem S and the
reduction (coset form of covering). The archive ancestor is the two-orbit criterion of
"Proof of Inequality" (`old-personal-chatgpt` doc `01a1e0fe-380f-7090-ac71-2e31f333cea0`).

For a perfect matching `P` of `α ∪ {∞}` (encoded as `Option α`, `none = ∞`) with `P ∞ = p₀`,
`pinned P` is the involution `P̃` of `α` equal to `P` off `p₀`, with `P̃ p₀ = p₀`. The source
states Theorem S for `Q = F_σ`, where `Q̃ = F̃_σ : y ↦ σ - y`. The proof only uses that `Q̃` is an
involution of `α` with the single fixed point `Q ∞`, so everything is stated for two arbitrary
perfect matchings `P, Q` of `Option α`. Put `Ψ = Q̃ P̃` and `Φ = Q P`.

* `sameCycle_pinned_of_sameCycle_none` : every point of the `Φ`-orbit of `∞` other than `∞` lies
  in the `Ψ`-cycle of `p₀`. `sameCycle_anchor_pinned` (Theorem S(a), first half) : `p₀` and
  `q₀ = Q ∞` share a `Ψ`-cycle.
* `ham_iff_sameCycle_pinned` (Theorem S(b), Hamiltonian case) : `P ∪ Q` is one cycle iff `Ψ` is
  a single cycle through all of `α`, an `n`-cycle for `α = ℤ/n`.
* `pinned_pow_half`, `pinned_anchor_eq_pow_half`, `sameCycle_none_of_le_half`,
  `sameCycle_anchor_of_half_lt` (Theorem S(c)) : if `|α| = 2h + 1` and `Ψ` is one cycle, then
  `Ψ^(h+1) p₀ = q₀`, `P̃ q₀ = Ψ^h p₀`, and the two `Φ`-orbits are `{∞} ∪ {Ψ^k p₀ : 1 ≤ k ≤ h}`
  and `{Ψ^k p₀ : h + 1 ≤ k ≤ 2h + 1}`. In the source's indexing `x_k = Ψ^(k+1) p₀`.
* `RoundRobin.pinned_factor` : `F̃_t y = 2t - y`, so `RoundRobin.ham_factor_iff_sameCycle` is
  Theorem S for `F_t` (the source's `F_σ` with `σ = 2t`).
* The reduction. `pinned_mul_eq_mul_mul` : `Q̃ P̃ = (Q̃ M̃)(M̃ P̃)` for any third matching `M`.
  `RoundRobin.ham_factor_iff_translate` : `P ∪ F_t` is one cycle iff
  `R_{2t} ∘ D ∘ π` is an `n`-cycle, with `D = -M̃` and `π = M̃ P̃`.
  `pinned_mul_pinned_apply_of_mate_eq` : `π` fixes every `y` with `P y = M y`, so `π` moves
  only points of the defect of `P` against `M`.

The cycle count `c(σ) = (cyc(Ψ) + 1)/2` of Theorem S(b) and the oddness and uniqueness of the
`P̃`-invariant cycle in Theorem S(a) are not formalized.
-/

namespace Pairing

namespace PerfectMatching

variable {α : Type*}

/-- The map `P̃` of `sl5-control-extend.md` (d185a5e) §2, Theorem S: `P` on `α` with the partner
`p₀ = P ∞` of `∞` made a fixed point. -/
def pinnedFn (P : PerfectMatching (Option α)) (y : α) : α :=
  (P.mate (some y)).getD y

/-- `P̃` is an involution (`sl5-control-extend.md` (d185a5e) §2, Theorem S). -/
theorem pinnedFn_involutive (P : PerfectMatching (Option α)) :
    Function.Involutive (pinnedFn P) := by
  intro y
  unfold pinnedFn
  rcases h : P.mate (some y) with _ | z
  · simp [h]
  · have hz : P.mate (some z) = some y := by rw [← h, mate_mate]
    simp [hz]

/-- `P̃` as a permutation of `α` (`sl5-control-extend.md` (d185a5e) §2, Theorem S). -/
def pinned (P : PerfectMatching (Option α)) : Equiv.Perm α :=
  Function.Involutive.toPerm _ (pinnedFn_involutive P)

/-- `P̃ y = z` when `P` pairs `y` with `z` (`sl5-control-extend.md` (d185a5e) §2). -/
theorem pinned_apply_of_mate_eq_some (P : PerfectMatching (Option α)) {y z : α}
    (h : P.mate (some y) = some z) : pinned P y = z := by
  simp [pinned, pinnedFn, h]

/-- `P̃ y = y` when `P` pairs `y` with `∞` (`sl5-control-extend.md` (d185a5e) §2). -/
theorem pinned_apply_of_mate_eq_none (P : PerfectMatching (Option α)) {y : α}
    (h : P.mate (some y) = none) : pinned P y = y := by
  simp [pinned, pinnedFn, h]

/-- `P̃ P̃ = 1` (`sl5-control-extend.md` (d185a5e) §2, Theorem S). -/
theorem pinned_mul_self (P : PerfectMatching (Option α)) : pinned P * pinned P = 1 := by
  ext y
  exact pinnedFn_involutive P y

/-- `P̃⁻¹ = P̃` (`sl5-control-extend.md` (d185a5e) §2, Theorem S). -/
theorem pinned_inv (P : PerfectMatching (Option α)) : (pinned P)⁻¹ = pinned P :=
  inv_eq_of_mul_eq_one_left (pinned_mul_self P)

/-- `P` pairs `y` with `∞` iff `y = p₀` (`sl5-control-extend.md` (d185a5e) §2). -/
theorem mate_some_eq_none_iff (P : PerfectMatching (Option α)) {p y : α}
    (hp : P.mate none = some p) : P.mate (some y) = none ↔ y = p := by
  rw [mate_eq_comm, hp, Option.some_inj, eq_comm]

/-- Off `p₀`, `P` pairs `y` with `P̃ y` (`sl5-control-extend.md` (d185a5e) §2). -/
theorem mate_some_eq_some_pinned (P : PerfectMatching (Option α)) {p y : α}
    (hp : P.mate none = some p) (hy : y ≠ p) : P.mate (some y) = some (pinned P y) := by
  rcases h : P.mate (some y) with _ | z
  · exact absurd ((mate_some_eq_none_iff P hp).mp h) hy
  · rw [pinned_apply_of_mate_eq_some P h]

/-- `P̃ p₀ = p₀` (`sl5-control-extend.md` (d185a5e) §2, Theorem S(a)). -/
theorem pinned_anchor (P : PerfectMatching (Option α)) {p : α} (hp : P.mate none = some p) :
    pinned P p = p :=
  pinned_apply_of_mate_eq_none P ((mate_some_eq_none_iff P hp).mpr rfl)

/-- `Φ = Q P` agrees with `Ψ = Q̃ P̃` off `p₀` and `P̃⁻¹ q₀` (`sl5-control-extend.md` (d185a5e)
§2, proof of Theorem S(b)). -/
theorem mate_mul_mate_some (P Q : PerfectMatching (Option α)) {p q y : α}
    (hp : P.mate none = some p) (hq : Q.mate none = some q) (hy : y ≠ p)
    (hyq : pinned P y ≠ q) :
    (Q.mate * P.mate) (some y) = some ((pinned Q * pinned P) y) := by
  rw [Equiv.Perm.mul_apply, mate_some_eq_some_pinned P hp hy,
    mate_some_eq_some_pinned Q hq hyq, Equiv.Perm.mul_apply]

/-- Each `Ψ`-step is a path of `P ∪ Q` (`sl5-control-extend.md` (d185a5e) §2, proof of
Theorem S(b)). -/
theorem reachable_pinned (P Q : PerfectMatching (Option α)) (y : α) :
    (P.toGraph ⊔ Q.toGraph).Reachable (some y) (some ((pinned Q * pinned P) y)) := by
  have hP : ∀ v, (P.toGraph ⊔ Q.toGraph).Reachable v (P.mate v) := fun v ↦
    SimpleGraph.Adj.reachable (Or.inl rfl)
  have hQ : ∀ v, (P.toGraph ⊔ Q.toGraph).Reachable v (Q.mate v) := fun v ↦
    SimpleGraph.Adj.reachable (Or.inr rfl)
  have hstep : ∀ z : α, (P.toGraph ⊔ Q.toGraph).Reachable (some z) (some (pinned Q z)) := by
    intro z
    rcases h : Q.mate (some z) with _ | w
    · rw [pinned_apply_of_mate_eq_none Q h]
    · rw [pinned_apply_of_mate_eq_some Q h, ← h]
      exact hQ _
  rw [Equiv.Perm.mul_apply]
  rcases h : P.mate (some y) with _ | z
  · rw [pinned_apply_of_mate_eq_none P h]
    exact hstep y
  · rw [pinned_apply_of_mate_eq_some P h]
    exact (h ▸ hP (some y)).trans (hstep z)

/-- The `Ψ`-cycle of `x` lies in one component of `P ∪ Q` (`sl5-control-extend.md` (d185a5e)
§2, proof of Theorem S(b)). -/
theorem reachable_of_sameCycle_pinned [Finite α] (P Q : PerfectMatching (Option α)) {x y : α}
    (h : (pinned Q * pinned P).SameCycle x y) :
    (P.toGraph ⊔ Q.toGraph).Reachable (some x) (some y) := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (reachable_pinned P Q _)

/-- Points of the `Φ`-orbit of `∞` lie in the `Ψ`-cycle of `p₀` (`sl5-control-extend.md`
(d185a5e) §2, proof of Theorem S(b): the orbit of `∞` runs `∞, Ψ p₀, Ψ² p₀, …, P̃ q₀`). -/
theorem sameCycle_pinned_of_sameCycle_none [Finite α] (P Q : PerfectMatching (Option α))
    {p y : α} (hp : P.mate none = some p)
    (h : (Q.mate * P.mate).SameCycle none (some y)) : (pinned Q * pinned P).SameCycle p y := by
  set Φ := Q.mate * P.mate with hΦ
  set Ψ := pinned Q * pinned P with hΨ
  have hnot : ∀ k : ℕ, (Φ ^ k) none ≠ some p := by
    intro k hk
    refine not_sameCycle_mate_right Q P none ?_
    rw [hp, ← hk]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have key : ∀ k : ℕ, (Φ ^ k) none = none ∨ ∃ y, (Φ ^ k) none = some y ∧ Ψ.SameCycle p y := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h0 | ⟨y, hy, hpy⟩
      · rw [h0, hΦ, Equiv.Perm.mul_apply, hp]
        rcases hw : Q.mate (some p) with _ | w
        · exact Or.inl rfl
        · refine Or.inr ⟨w, rfl, ?_⟩
          have : Ψ p = w := by
            rw [hΨ, Equiv.Perm.mul_apply, pinned_anchor P hp, pinned_apply_of_mate_eq_some Q hw]
          rw [← this]
          exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
      · have hyp : y ≠ p := fun h' ↦ hnot k (by rw [hy, h'])
        rw [hy, hΦ, Equiv.Perm.mul_apply, mate_some_eq_some_pinned P hp hyp]
        rcases hw : Q.mate (some (pinned P y)) with _ | w
        · exact Or.inl rfl
        · refine Or.inr ⟨w, rfl, ?_⟩
          have : Ψ y = w := by
            rw [hΨ, Equiv.Perm.mul_apply, pinned_apply_of_mate_eq_some Q hw]
          rw [← this]
          exact Equiv.Perm.sameCycle_apply_right.mpr hpy
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rcases key k with h0 | ⟨z, hz, hpz⟩
  · rw [hk] at h0
    exact absurd h0 (Option.some_ne_none y)
  · rw [hk, Option.some_inj] at hz
    exact hz ▸ hpz

/-- **Theorem S(a), first half** (`sl5-control-extend.md` (d185a5e) §2): `p₀ = P ∞` and
`q₀ = Q ∞` lie in one cycle `Z₀` of `Ψ = Q̃ P̃`. For `Q = F_σ`, `q₀ = σ/2`. -/
theorem sameCycle_anchor_pinned [Finite α] (P Q : PerfectMatching (Option α)) {p q : α}
    (hp : P.mate none = some p) (hq : Q.mate none = some q) :
    (pinned Q * pinned P).SameCycle p q := by
  rcases hz : P.mate (some q) with _ | z
  · rw [(mate_some_eq_none_iff P hp).mp hz]
  · have hqz : P.mate (some z) = some q := by rw [← hz, mate_mate]
    have hqq : Q.mate (some q) = none := by rw [← hq, mate_mate]
    have hΦ : (Q.mate * P.mate) (some z) = none := by
      rw [Equiv.Perm.mul_apply, hqz, hqq]
    have h1 : (Q.mate * P.mate).SameCycle none (some z) := by
      rw [← hΦ]
      exact Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)
    have h2 := sameCycle_pinned_of_sameCycle_none P Q hp h1
    have h3 : (pinned Q * pinned P) z = q := by
      rw [Equiv.Perm.mul_apply, pinned_apply_of_mate_eq_some P hqz,
        pinned_apply_of_mate_eq_none Q hqq]
    rw [← h3]
    exact Equiv.Perm.sameCycle_apply_right.mpr h2

/-- Points of the `Φ`-orbit of `p₀` lie in the `Ψ`-cycle of `p₀` (`sl5-control-extend.md`
(d185a5e) §2, proof of Theorem S(b): that orbit runs `p₀, q₀, Ψ q₀, …`). -/
theorem sameCycle_pinned_of_sameCycle_anchor [Finite α] (P Q : PerfectMatching (Option α))
    {p y : α} (hp : P.mate none = some p)
    (h : (Q.mate * P.mate).SameCycle (some p) (some y)) : (pinned Q * pinned P).SameCycle p y := by
  set Φ := Q.mate * P.mate with hΦ
  set Ψ := pinned Q * pinned P with hΨ
  obtain ⟨q, hq⟩ : ∃ q, Q.mate none = some q := Option.ne_none_iff_exists'.mp (Q.mate_ne none)
  have hpn : P.mate (some p) = none := by rw [← hp, mate_mate]
  have hnot : ∀ k : ℕ, (Φ ^ k) (some p) ≠ none := by
    intro k hk
    refine not_sameCycle_mate_right Q P (some p) ?_
    rw [hpn, ← hk]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have key : ∀ k : ℕ, ∃ y, (Φ ^ k) (some p) = some y ∧ Ψ.SameCycle p y := by
    intro k
    induction k with
    | zero => exact ⟨p, rfl, Equiv.Perm.SameCycle.refl _ _⟩
    | succ k ih =>
      obtain ⟨y, hy, hpy⟩ := ih
      have hk1 := hnot (k + 1)
      rw [pow_succ', Equiv.Perm.mul_apply, hy] at hk1 ⊢
      by_cases hyp : y = p
      · subst hyp
        rw [hΦ, Equiv.Perm.mul_apply, hpn, hq]
        exact ⟨q, rfl, sameCycle_anchor_pinned P Q hp hq⟩
      · rw [hΦ, Equiv.Perm.mul_apply, mate_some_eq_some_pinned P hp hyp] at hk1 ⊢
        rcases hw : Q.mate (some (pinned P y)) with _ | w
        · exact absurd hw hk1
        · refine ⟨w, rfl, ?_⟩
          have : Ψ y = w := by
            rw [hΨ, Equiv.Perm.mul_apply, pinned_apply_of_mate_eq_some Q hw]
          rw [← this]
          exact Equiv.Perm.sameCycle_apply_right.mpr hpy
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  obtain ⟨z, hz, hpz⟩ := key k
  rw [hk, Option.some_inj] at hz
  exact hz ▸ hpz

/-- **Theorem S(b), Hamiltonian case** (`sl5-control-extend.md` (d185a5e) §2). `P ∪ Q` is one
cycle iff `Ψ = Q̃ P̃` is a single cycle through every point of `α`. For `α = ℤ/n` and
`Q = F_σ` this is "`P ∪ F_σ` is Hamiltonian iff `F̃_σ P̃` is an `n`-cycle". -/
theorem ham_iff_sameCycle_pinned [Finite α] (P Q : PerfectMatching (Option α)) :
    Ham P Q ↔ ∀ x y, (pinned Q * pinned P).SameCycle x y := by
  obtain ⟨p, hp⟩ : ∃ p, P.mate none = some p := Option.ne_none_iff_exists'.mp (P.mate_ne none)
  constructor
  · intro hH
    have hall : ∀ y, (pinned Q * pinned P).SameCycle p y := by
      intro y
      rcases sameCycle_or_of_ham hH none (some y) with h | h
      · exact sameCycle_pinned_of_sameCycle_none P Q hp h
      · have hpn : P.mate (some p) = none := by rw [← hp, mate_mate]
        refine sameCycle_pinned_of_sameCycle_anchor P Q hp
          (sameCycle_of_sameCycle_mate P Q ?_)
        rw [hpn]
        exact h
    exact fun x y ↦ (hall x).symm.trans (hall y)
  · intro h
    have hr : ∀ v, (P.toGraph ⊔ Q.toGraph).Reachable none v := by
      have h0 : (P.toGraph ⊔ Q.toGraph).Reachable none (some p) :=
        hp ▸ SimpleGraph.Adj.reachable (Or.inl rfl)
      rintro (_ | y)
      · exact SimpleGraph.Reachable.refl _
      · exact h0.trans (reachable_of_sameCycle_pinned P Q (h p y))
    exact SimpleGraph.Connected.mk fun u v ↦ (hr u).symm.trans (hr v)

/-- `P̃` reverses `Ψ`: `P̃ Ψ^k P̃ = Ψ^(-k)` (`sl5-control-extend.md` (d185a5e) §2, proof of
Theorem S(a) and (c)). -/
theorem pinned_mul_pow_mul_pinned (P Q : PerfectMatching (Option α)) (k : ℕ) :
    pinned P * (pinned Q * pinned P) ^ k * pinned P = ((pinned Q * pinned P) ^ k)⁻¹ := by
  have h1 : pinned P * (pinned Q * pinned P) * (pinned P)⁻¹ = (pinned Q * pinned P)⁻¹ := by
    rw [pinned_inv, mul_inv_rev, pinned_inv, pinned_inv, mul_assoc, mul_assoc, pinned_mul_self,
      mul_one]
  have h2 : (pinned P * (pinned Q * pinned P) * (pinned P)⁻¹) ^ k =
      ((pinned Q * pinned P)⁻¹) ^ k := by rw [h1]
  rw [conj_pow, inv_pow, pinned_inv] at h2
  exact h2

/-- A permutation of a set of size `N` that is one cycle has period `N` at every point, so
`Ψ^a p = Ψ^b p` for `a, b < N` forces `a = b`, `Ψ^N p = p`, and every point is some `Ψ^j p` with
`j < N` (`sl5-control-extend.md` (d185a5e) §2, the listing `x_k` of Theorem S(c)). -/
theorem orbit_facts [Fintype α] (Ψ : Equiv.Perm α) {N : ℕ} (hα : Fintype.card α = N)
    (hcyc : ∀ x y, Ψ.SameCycle x y) (p : α) :
    (∀ a b, a < N → b < N → (Ψ ^ a) p = (Ψ ^ b) p → a = b) ∧ (Ψ ^ N) p = p ∧
      ∀ y, ∃ j < N, (Ψ ^ j) p = y := by
  classical
  have hper : Function.IsPeriodicPt Ψ (orderOf Ψ) p := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  have hpos := hper.minimalPeriod_pos (orderOf_pos Ψ)
  set r := Function.minimalPeriod Ψ p with hr
  have hinj : ∀ a b, a < r → b < r → (Ψ ^ a) p = (Ψ ^ b) p → a = b := by
    intro a b ha hb hab
    refine Function.iterate_injOn_Iio_minimalPeriod (f := Ψ) (x := p) (by simpa using ha)
      (by simpa using hb) ?_
    simp only [Equiv.Perm.iterate_eq_pow]
    exact hab
  have hex : ∀ y, ∃ j < r, (Ψ ^ j) p = y := by
    intro y
    obtain ⟨i, hi⟩ := (hcyc p y).exists_nat_pow_eq
    refine ⟨i % r, Nat.mod_lt _ hpos, ?_⟩
    rw [← Equiv.Perm.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
      Equiv.Perm.iterate_eq_pow, hi]
  have himg : (Finset.range r).image (fun i ↦ (Ψ ^ i) p) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨j, hj, hjy⟩ := hex y
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, hjy⟩
  have hcard := congrArg Finset.card himg
  rw [Finset.card_image_of_injOn (fun a ha b hb hab ↦ hinj a b (by simpa using ha)
    (by simpa using hb) hab), Finset.card_range, Finset.card_univ, hα] at hcard
  subst hcard
  refine ⟨hinj, ?_, hex⟩
  rw [← Equiv.Perm.iterate_eq_pow]
  exact Function.iterate_minimalPeriod

/-- **Theorem S(c)** (`sl5-control-extend.md` (d185a5e) §2), the positions of `q₀` and of
`P̃ q₀`. If `|α| = 2h + 1` and `Ψ` is one cycle, then `Ψ^(h+1) p₀ = q₀` and `P̃ q₀ = Ψ^h p₀`.
In the source's indexing `x_k = Ψ^(k+1) p₀`, `σ/2 = x_{(n-1)/2}` and `P(σ/2) = x_{(n-3)/2}`. -/
theorem pinned_pow_half [Fintype α] (P Q : PerfectMatching (Option α)) {p q : α} {h : ℕ}
    (hp : P.mate none = some p) (hq : Q.mate none = some q) (hα : Fintype.card α = 2 * h + 1)
    (hcyc : ∀ x y, (pinned Q * pinned P).SameCycle x y) :
    ((pinned Q * pinned P) ^ (h + 1)) p = q ∧ pinned P q = ((pinned Q * pinned P) ^ h) p := by
  set Ψ := pinned Q * pinned P with hΨ
  have hqq : Q.mate (some q) = none := by rw [← hq, mate_mate]
  have hΨq : Ψ (pinned P q) = q := by
    rw [hΨ, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply (pinned P), pinned_mul_self,
      Equiv.Perm.one_apply, pinned_apply_of_mate_eq_none Q hqq]
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  obtain ⟨hinj, hN, hex⟩ := orbit_facts Ψ hα hcyc p
  obtain ⟨j, hj, hjq⟩ := hex q
  have hrefl : pinned P q = ((Ψ ^ j)⁻¹) p := by
    have h1 := pinned_mul_pow_mul_pinned P Q j
    rw [← hΨ] at h1
    have h2 := congrArg (fun g : Equiv.Perm α ↦ g p) h1
    simp only [Equiv.Perm.mul_apply, pinned_anchor P hp] at h2
    rw [← hjq, h2]
  have h2j : (Ψ ^ (2 * j)) p = (Ψ ^ 1) p := by
    have h3 : Ψ (((Ψ ^ j)⁻¹) p) = (Ψ ^ j) p := by rw [← hrefl, hΨq, hjq]
    have hc : Ψ * (Ψ ^ j)⁻¹ = (Ψ ^ j)⁻¹ * Ψ := ((Commute.self_pow Ψ j).inv_right).eq
    have h4 : ((Ψ ^ j)⁻¹) (Ψ p) = (Ψ ^ j) p := by
      rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, h3]
    rw [pow_one, Equiv.Perm.inv_eq_iff_eq.mp h4, ← Equiv.Perm.mul_apply, ← pow_add, two_mul]
  have hj1 : j = h + 1 := by
    by_cases hlt : 2 * j < 2 * h + 1
    · have := hinj _ _ hlt (by omega) h2j
      omega
    · have h5 : (Ψ ^ (2 * j)) p = (Ψ ^ (2 * j - (2 * h + 1))) p := by
        conv_lhs => rw [show 2 * j = 2 * j - (2 * h + 1) + (2 * h + 1) by omega, pow_add,
          Equiv.Perm.mul_apply, hN]
      rw [h5] at h2j
      have := hinj _ _ (by omega) (by omega) h2j
      omega
  subst hj1
  refine ⟨hjq, Ψ.injective ?_⟩
  rw [hΨq, ← Equiv.Perm.mul_apply, ← pow_succ', hjq]

/-- **Theorem S(c), the two orbits, first half** (`sl5-control-extend.md` (d185a5e) §2). If
`|α| = 2h + 1` and `Ψ` is one cycle, then `∞` and `Ψ^k p₀` share a `Φ`-orbit for `1 ≤ k ≤ h`,
the points `x_0, …, x_{(n-3)/2}` of the source. -/
theorem sameCycle_none_of_le_half [Fintype α] (P Q : PerfectMatching (Option α)) {p q : α}
    {h : ℕ} (hp : P.mate none = some p) (hq : Q.mate none = some q)
    (hα : Fintype.card α = 2 * h + 1) (hcyc : ∀ x y, (pinned Q * pinned P).SameCycle x y)
    {k : ℕ} (hk1 : 1 ≤ k) (hkh : k ≤ h) :
    (Q.mate * P.mate).SameCycle none (some (((pinned Q * pinned P) ^ k) p)) := by
  set Ψ := pinned Q * pinned P with hΨ
  obtain ⟨hinj, -, -⟩ := orbit_facts Ψ hα hcyc p
  obtain ⟨hq1, hPq⟩ := pinned_pow_half P Q hp hq hα hcyc
  have hne : ∀ i, i ≠ 0 → i < 2 * h + 1 → (Ψ ^ i) p ≠ p := fun i hi hiN h' ↦
    hi (hinj i 0 hiN (by omega) (by rw [h', pow_zero, Equiv.Perm.one_apply]))
  have hpq : p ≠ q := fun h' ↦ hne (h + 1) (by omega) (by omega) (by rw [hq1, h'])
  induction k, hk1 using Nat.le_induction with
  | base =>
    have h1 : (Q.mate * P.mate) none = some ((Ψ ^ 1) p) := by
      rw [Equiv.Perm.mul_apply, hp, mate_some_eq_some_pinned Q hq hpq, pow_one, hΨ,
        Equiv.Perm.mul_apply, pinned_anchor P hp]
    rw [← h1]
    exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  | succ k hk ih =>
    have hy : (Ψ ^ k) p ≠ p := hne k (by omega) (by omega)
    have hyq : pinned P ((Ψ ^ k) p) ≠ q := by
      intro h'
      have h'' : (Ψ ^ k) p = (Ψ ^ h) p := by
        rw [← hPq, ← h', ← Equiv.Perm.mul_apply, pinned_mul_self, Equiv.Perm.one_apply]
      have := hinj k h (by omega) (by omega) h''
      omega
    have h1 := mate_mul_mate_some P Q hp hq hy hyq
    rw [← hΨ, ← Equiv.Perm.mul_apply, ← pow_succ'] at h1
    rw [← h1]
    exact Equiv.Perm.sameCycle_apply_right.mpr (ih (by omega))

/-- **Theorem S(c), the two orbits, second half** (`sl5-control-extend.md` (d185a5e) §2). If
`|α| = 2h + 1` and `Ψ` is one cycle, then `p₀` and `Ψ^k p₀` share a `Φ`-orbit for
`h + 1 ≤ k ≤ 2h + 1`, the points `x_{(n-1)/2}, …, x_{n-1}` of the source. This orbit misses `∞`
(`not_sameCycle_mate_right`). -/
theorem sameCycle_anchor_of_half_lt [Fintype α] (P Q : PerfectMatching (Option α)) {p q : α}
    {h : ℕ} (hp : P.mate none = some p) (hq : Q.mate none = some q)
    (hα : Fintype.card α = 2 * h + 1) (hcyc : ∀ x y, (pinned Q * pinned P).SameCycle x y)
    {k : ℕ} (hk1 : h + 1 ≤ k) (hkh : k ≤ 2 * h + 1) :
    (Q.mate * P.mate).SameCycle (some p) (some (((pinned Q * pinned P) ^ k) p)) := by
  set Ψ := pinned Q * pinned P with hΨ
  obtain ⟨hinj, -, -⟩ := orbit_facts Ψ hα hcyc p
  obtain ⟨hq1, hPq⟩ := pinned_pow_half P Q hp hq hα hcyc
  have hpn : P.mate (some p) = none := by rw [← hp, mate_mate]
  induction k, hk1 using Nat.le_induction with
  | base =>
    have h1 : (Q.mate * P.mate) (some p) = some ((Ψ ^ (h + 1)) p) := by
      rw [Equiv.Perm.mul_apply, hpn, hq, hq1]
    rw [← h1]
    exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  | succ k hk ih =>
    have hy : (Ψ ^ k) p ≠ p := fun h' ↦ by
      have := hinj k 0 (by omega) (by omega) (by rw [h', pow_zero, Equiv.Perm.one_apply])
      omega
    have hyq : pinned P ((Ψ ^ k) p) ≠ q := by
      intro h'
      have h'' : (Ψ ^ k) p = (Ψ ^ h) p := by
        rw [← hPq, ← h', ← Equiv.Perm.mul_apply, pinned_mul_self, Equiv.Perm.one_apply]
      have := hinj k h (by omega) (by omega) h''
      omega
    have h1 := mate_mul_mate_some P Q hp hq hy hyq
    rw [← hΨ, ← Equiv.Perm.mul_apply, ← pow_succ'] at h1
    rw [← h1]
    exact Equiv.Perm.sameCycle_apply_right.mpr (ih (by omega))

/-- `Q̃ P̃ = (Q̃ M̃)(M̃ P̃)` for any third matching `M` (`sl5-control-extend.md` (d185a5e) §2, the
reduction: `F̃_σ P̃ = (D + σ) ∘ π_{S,R}` with `π_{S,R} = M̃ P̃`). -/
theorem pinned_mul_eq_mul_mul (P Q M : PerfectMatching (Option α)) :
    pinned Q * pinned P = (pinned Q * pinned M) * (pinned M * pinned P) := by
  rw [mul_assoc, ← mul_assoc (pinned M), pinned_mul_self, one_mul]

/-- `π = M̃ P̃` fixes every `y` that `P` and `M` pair alike (`sl5-control-extend.md` (d185a5e)
§2, the reduction: `π_{S,R}` moves only points of `W ∪ {0}`). -/
theorem pinned_mul_pinned_apply_of_mate_eq {P M : PerfectMatching (Option α)} {y : α}
    (h : P.mate (some y) = M.mate (some y)) : (pinned M * pinned P) y = y := by
  have h1 : pinned P y = pinned M y := by
    simp only [pinned, Function.Involutive.coe_toPerm, pinnedFn, h]
  rw [Equiv.Perm.mul_apply, h1, ← Equiv.Perm.mul_apply, pinned_mul_self, Equiv.Perm.one_apply]

/-- `π = M̃ P̃` moves only points of the defect of `P` against `M` (`sl5-control-extend.md`
(d185a5e) §2, the reduction: `π_{S,R}` moves at most `2|S| + 7` points). -/
theorem mem_defect_of_pinned_mul_pinned_ne [Fintype α] [DecidableEq α]
    {P M : PerfectMatching (Option α)} {y : α} (h : (pinned M * pinned P) y ≠ y) :
    some y ∈ defect M P :=
  mem_defect.mpr fun h' ↦ h (pinned_mul_pinned_apply_of_mate_eq h')

end PerfectMatching

namespace RoundRobin

open PerfectMatching

variable {n : ℕ}

/-- `F̃_t y = 2t - y`, the source's `F̃_σ y = σ - y` with `σ = 2t` (`sl5-control-extend.md`
(d185a5e) §2, Theorem S). -/
theorem pinned_factor (hn : Odd n) (t y : ZMod n) : pinned (factor hn t) y = 2 * t - y := by
  by_cases h : y = t
  · subst h
    rw [pinned_apply_of_mate_eq_none _ (by rw [factor_mate, mateFn_self])]
    ring
  · rw [pinned_apply_of_mate_eq_some _ (by rw [factor_mate, mateFn_of_ne _ _ h])]

/-- **Theorem S** for round-robin factors (`sl5-control-extend.md` (d185a5e) §2). `P ∪ F_t` is
a Hamiltonian cycle iff `F̃_t P̃ : y ↦ 2t - P̃ y` is an `n`-cycle of `ℤ/n`. -/
theorem ham_factor_iff_sameCycle (hn : Odd n) [NeZero n] (P : PerfectMatching (Option (ZMod n)))
    (t : ZMod n) : Ham P (factor hn t) ↔ ∀ x y, (pinned (factor hn t) * pinned P).SameCycle x y :=
  ham_iff_sameCycle_pinned P _

/-- **The reduction, coset form of covering** (`sl5-control-extend.md` (d185a5e) §2). For any
perfect matching `M` of `ℤ/n ∪ {∞}`, put `D = -M̃` and `π = M̃ P̃`. Then `P ∪ F_t` is a
Hamiltonian cycle iff `R_{2t} ∘ D ∘ π` is an `n`-cycle, where `R_σ` is translation by `σ`. With
`M` the completion of the tail and `P = (T ∖ S) ∪ R`, this is "`σ` covers `(S, R)` iff
`R_σ D π_{S,R}` is an `n`-cycle". -/
theorem ham_factor_iff_translate (hn : Odd n) [NeZero n]
    (P M : PerfectMatching (Option (ZMod n))) (t : ZMod n) :
    Ham P (factor hn t) ↔ ∀ x y, (Equiv.addRight (2 * t) * (Equiv.neg (ZMod n) * pinned M) *
      (pinned M * pinned P)).SameCycle x y := by
  have h : pinned (factor hn t) * pinned M = Equiv.addRight (2 * t) * (Equiv.neg (ZMod n) *
      pinned M) := by
    ext y
    simp only [Equiv.Perm.mul_apply, pinned_factor, Equiv.coe_addRight, Equiv.neg_apply]
    ring
  rw [ham_factor_iff_sameCycle, pinned_mul_eq_mul_mul P (factor hn t) M, h]

end RoundRobin

end Pairing
