import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lemma L: the lane permutation of integer factors

Source: `results/sl5-control-extend.md` (organize-archive d185a5e) §1 and §3, Lemma L.

`twoarc` is not formalized elsewhere, so its slip map `D` is built here from the arc lengths.
Positions are `p = y + P ∈ [0, n)`, with `n = L_A + 2 L_B + 4`, so that the arcs are
`A_0 = [0, L_A)`, `B+ = [L_A, L_A + L_B)`, `A_1 = [L_A + L_B, L_A + L_B + 4)` and
`B- = [L_A + L_B + 4, n)`. `D` is the identity on `A_0 ∪ A_1` and the cyclic rotation by `-1`
of each of `B+` and `B-` (§1), so `D p = p + slip p`, with `slip = L_B - 1` at the two wrap points
`L_A` and `L_A + L_B + 4`, `slip = -1` elsewhere on the `B` arcs and `0` otherwise. The map
`D + β` on positions is `lap`. The entry window is `Σ = [0, β)`, the offsets `a` of the source.

* `lane_return` (Lemma L(i) and (ii)) : for `6 ≤ β ≤ L_B` and `β ≤ L_A`, every `a ∈ [0, β)`
  returns to `Σ` after `k ≥ 1` steps at `laneMap a = g3 (g2 (g1 a))`, every point strictly between
  lies in `[β, n)`, every point `y ∈ [0, L_A)` of the lane `y ≡ a (mod β)` is visited before the
  return, and no other point of `A_0` is.
* `laneMap_eq_rot` : `π_β = Rot′_u ∘ Rot_{-5} ∘ Rot′_u ∘ Rot_{-1-L_A}` on `[0, β)`, with
  `u = 1 - L_B`, the closed form of Lemma L(i).
* `laneStep`, `val_laneStep_iterate`, `lane_return_zmod` : the same on `ℤ/n`, where
  `laneStep x = x + β + slip x` is `D + β` read in positions.
* `laneMap_eq_of_dvd`, `laneMap_self_of_even` (Corollary R, rotation part) : if
  `(β - 1) ∣ (L_B - 1)`, then `π_β` is the rotation by `-(L_A + 6)`. For `β = L_B` and
  `L_A + 6 = 2 L_B + 1` (even `m`) it is the rotation by `-1`.

The link "`M ∪ F_β` is Hamiltonian iff `π_β` is one `β`-cycle" needs `twoarc`'s matching `M` with
`M̃ = -D` as a perfect matching, to feed Theorem S (`Repair.Cover.NCycle`). That matching, and
Corollaries H and P, are not formalized.

**Correction.** The source assumes `β ≤ L_B ≤ L_A + 1`. Its proof needs `β ≤ L_A` (for
`β = L_A + 1` the window `Σ` contains the wrap point `P + 1` of `B+`), so the hypotheses here
are `β ≤ L_B` and `β ≤ L_A`. For `twoarc(m)` with `L_B ≥ 6` one has `L_B ≤ L_A`, so nothing is
lost there.
-/

namespace Pairing

namespace Lane

/-- The slip `D p - p` of `twoarc` at position `p` (`sl5-control-extend.md` (d185a5e) §1: `D` is
the identity on `A_0 ∪ A_1` and the rotation by `-1` of each of `B+` and `B-`). -/
def slip (LA LB p : ℤ) : ℤ :=
  if p = LA ∨ p = LA + LB + 4 then LB - 1
  else if (LA < p ∧ p < LA + LB) ∨ LA + LB + 4 < p then -1 else 0

/-- `Ψ_β = D + β` in positions, reduced mod `n = L_A + 2 L_B + 4` (`sl5-control-extend.md`
(d185a5e) §3). -/
def lap (LA LB β p : ℤ) : ℤ :=
  (p + β + slip LA LB p) % (LA + 2 * LB + 4)

/-- `g1 a = (a - L_A) mod β`, the exit offset from `A_0` (`sl5-control-extend.md` (d185a5e) §3,
Lemma L(i)). -/
def g1 (LA β a : ℤ) : ℤ := (a - LA) % β

/-- `g2`, the `A_1` offset reached from `B+` (`sl5-control-extend.md` (d185a5e) §3, Lemma L(i)). -/
def g2 (LB β e : ℤ) : ℤ := if e = 0 then β - 1 else (e - LB) % (β - 1)

/-- `g3`, the window offset reached through `A_1` and `B-` (`sl5-control-extend.md` (d185a5e) §3,
Lemma L(i)). -/
def g3 (LB β g : ℤ) : ℤ :=
  if g = 4 then β - 1 else (g - 3 - (if 5 ≤ g then 1 else 0) - LB) % (β - 1)

/-- The lane permutation `π_β = g3 ∘ g2 ∘ g1` (`sl5-control-extend.md` (d185a5e) §3,
Lemma L(i)). -/
def laneMap (LA LB β a : ℤ) : ℤ := g3 LB β (g2 LB β (g1 LA β a))

/-- `Rot_k` on `ℤ/β = [0, β)` (`sl5-control-extend.md` (d185a5e) §3). -/
def rot (β k x : ℤ) : ℤ := (x + k) % β

/-- `Rot′_k`, the rotation of `[0, β - 2]` mod `β - 1` that fixes `β - 1`
(`sl5-control-extend.md` (d185a5e) §3). -/
def rot' (β k x : ℤ) : ℤ := if x = β - 1 then β - 1 else (x + k) % (β - 1)

/-- `x mod b = y` when `x = y + c b` and `0 ≤ y < b` (`sl5-control-extend.md` (d185a5e) §3). -/
theorem emod_eq_of_eq_add_mul {x y b c : ℤ} (h0 : 0 ≤ y) (h1 : y < b) (h : x = y + c * b) :
    x % b = y := by
  rw [h, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]

/-- Range and division identity of `x mod b` for `b > 0` (`sl5-control-extend.md` (d185a5e) §3). -/
theorem emod_spec (x b : ℤ) (hb : 0 < b) :
    0 ≤ x % b ∧ x % b < b ∧ x = x % b + (x / b) * b := by
  refine ⟨Int.emod_nonneg x hb.ne', Int.emod_lt_of_pos x hb, ?_⟩
  have := Int.emod_add_ediv_mul x b
  linarith

/-- A run of constant steps: if `f p = p + s` on `[lo, hi)`, then from any `p ∈ [lo, hi + s)` the
orbit moves by `s` until it first reaches `[hi, hi + s)` (`sl5-control-extend.md` (d185a5e) §3,
the three stages of the proof of Lemma L). -/
theorem run_exit {f : ℤ → ℤ} {lo hi s : ℤ} (hs : 0 < s)
    (hf : ∀ p, lo ≤ p → p < hi → f p = p + s) :
    ∀ (N : ℕ) (p : ℤ), hi - p ≤ N * s → lo ≤ p → p < hi + s →
      ∃ k : ℕ, f^[k] p = p + k * s ∧ hi ≤ p + k * s ∧ p + k * s < hi + s ∧
        ∀ j : ℕ, j < k → f^[j] p = p + j * s ∧ p + j * s < hi := by
  intro N
  induction N with
  | zero =>
    intro p hN hlo hhi
    refine ⟨0, by simp, by simp at hN ⊢; linarith, by simpa using hhi, fun j hj ↦ ?_⟩
    exact absurd hj (Nat.not_lt_zero _)
  | succ N ih =>
    intro p hN hlo hhi
    by_cases hp : hi ≤ p
    · refine ⟨0, by simp, by simpa using hp, by simpa using hhi, fun j hj ↦ ?_⟩
      exact absurd hj (Nat.not_lt_zero _)
    · push Not at hp
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (p + s) (by push_cast at hN; linarith) (by linarith)
        (by linarith)
      refine ⟨k + 1, ?_, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hf p hlo hp, hk1]
        push_cast
        ring
      · push_cast
        linarith
      · push_cast
        linarith
      · intro j hj
        rcases j with _ | j
        · simpa using hp
        · obtain ⟨h1, h2⟩ := hk4 j (by omega)
          rw [Function.iterate_succ_apply, hf p hlo hp, h1]
          push_cast
          constructor
          · ring
          · linarith

/-- `f^[k] x = y`, and every point strictly between lies in `R`. -/
def Path (f : ℤ → ℤ) (R : ℤ → Prop) (x y : ℤ) (k : ℕ) : Prop :=
  f^[k] x = y ∧ ∀ j : ℕ, 0 < j → j < k → R (f^[j] x)

/-- Concatenation of two paths at a junction point in `R` (`sl5-control-extend.md` (d185a5e) §3,
the stages of the proof of Lemma L). -/
theorem Path.trans {f : ℤ → ℤ} {R : ℤ → Prop} {x y z : ℤ} {k₁ k₂ : ℕ} (h₁ : Path f R x y k₁)
    (hy : R y) (h₂ : Path f R y z k₂) : Path f R x z (k₂ + k₁) := by
  refine ⟨by rw [Function.iterate_add_apply, h₁.1, h₂.1], fun j hj0 hjk ↦ ?_⟩
  rcases lt_trichotomy j k₁ with hj | rfl | hj
  · exact h₁.2 j hj0 hj
  · rw [h₁.1]
    exact hy
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + k₁ := ⟨j - k₁, by omega⟩
    rw [Function.iterate_add_apply, h₁.1]
    exact h₂.2 i (by omega) (by omega)

/-- One step is a path (`sl5-control-extend.md` (d185a5e) §3). -/
theorem Path.single (f : ℤ → ℤ) (R : ℤ → Prop) (x : ℤ) : Path f R x (f x) 1 :=
  ⟨rfl, fun j hj0 hj1 ↦ absurd hj1 (by omega)⟩

section Stages

variable {LA LB β : ℤ}

/-- `D + β` moves `A_0` by `β` (`sl5-control-extend.md` (d185a5e) §3, stage `A_0`). -/
theorem lap_A0 {p : ℤ} (hβ : 6 ≤ β) (hβB : β ≤ LB) (h0 : 0 ≤ p) (h1 : p < LA) :
    lap LA LB β p = p + β := by
  have hs : slip LA LB p = 0 := by
    unfold slip
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [lap, hs, add_zero, Int.emod_eq_of_lt (by omega) (by omega)]

/-- The wrap point `P + 1` of `B+` jumps to `m - 3 + β` (`sl5-control-extend.md` (d185a5e) §3,
stage `B+`). -/
theorem lap_Bp_wrap (hβ : 6 ≤ β) (hβB : β ≤ LB) (hA : 0 ≤ LA) :
    lap LA LB β LA = LA + LB + β - 1 := by
  have hs : slip LA LB LA = LB - 1 := by
    unfold slip
    rw [ite_eq_left (Or.inl rfl)]
  rw [lap, hs, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- `D + β` moves `B+` off its wrap point by `β - 1` (`sl5-control-extend.md` (d185a5e) §3,
stage `B+`). -/
theorem lap_Bp {p : ℤ} (hβ : 6 ≤ β) (hβB : β ≤ LB) (hA : 0 ≤ LA) (h0 : LA < p)
    (h1 : p < LA + LB) : lap LA LB β p = p + β - 1 := by
  have hs : slip LA LB p = -1 := by
    unfold slip
    rw [ite_eq_right (by omega), ite_eq_left (Or.inl ⟨h0, h1⟩)]
  rw [lap, hs, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- `D + β` moves `A_1` by `β` (`sl5-control-extend.md` (d185a5e) §3, stage `A_1`). -/
theorem lap_A1 {p : ℤ} (hβ : 6 ≤ β) (hβB : β ≤ LB) (hA : 0 ≤ LA) (h0 : LA + LB ≤ p)
    (h1 : p < LA + LB + 4) (h2 : p + β < LA + 2 * LB + 4) : lap LA LB β p = p + β := by
  have hs : slip LA LB p = 0 := by
    unfold slip
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [lap, hs, add_zero, Int.emod_eq_of_lt (by omega) h2]

/-- The wrap point `m + 2` of `B-` jumps to window offset `β - 1` (`sl5-control-extend.md`
(d185a5e) §3, stage `A_1`). -/
theorem lap_Bm_wrap (hβ : 6 ≤ β) (hβB : β ≤ LB) (hA : 0 ≤ LA) :
    lap LA LB β (LA + LB + 4) = β - 1 := by
  have hs : slip LA LB (LA + LB + 4) = LB - 1 := by
    unfold slip
    rw [ite_eq_left (Or.inr rfl)]
  rw [lap, hs]
  exact emod_eq_of_eq_add_mul (c := 1) (by omega) (by omega) (by ring)

/-- `D + β` moves `B-` off its wrap point by `β - 1` (`sl5-control-extend.md` (d185a5e) §3,
stage `B-`). -/
theorem lap_Bm {p : ℤ} (hβ : 6 ≤ β) (hA : 0 ≤ LA) (h0 : LA + LB + 4 < p)
    (h2 : p + β - 1 < LA + 2 * LB + 4) : lap LA LB β p = p + β - 1 := by
  have hs : slip LA LB p = -1 := by
    unfold slip
    rw [ite_eq_right (by omega), ite_eq_left (Or.inr h0)]
  rw [lap, hs, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- The last step of `B-` wraps into the window (`sl5-control-extend.md` (d185a5e) §3,
stage `B-`). -/
theorem lap_Bm_last {p : ℤ} (hβB : β ≤ LB) (hA : 0 ≤ LA) (h0 : LA + LB + 4 < p)
    (h1 : p < LA + 2 * LB + 4) (h2 : LA + 2 * LB + 4 ≤ p + β - 1) :
    lap LA LB β p = p + β - 1 - (LA + 2 * LB + 4) := by
  have hs : slip LA LB p = -1 := by
    unfold slip
    rw [ite_eq_right (by omega), ite_eq_left (Or.inr h0)]
  rw [lap, hs]
  exact emod_eq_of_eq_add_mul (c := 1) (by omega) (by omega) (by ring)

/-- The points strictly inside a lap: outside the window, inside `[0, n)`, and on the lane of
`a` when in `A_0` (`sl5-control-extend.md` (d185a5e) §3, Lemma L(ii)). -/
def Inside (LA LB β a p : ℤ) : Prop :=
  β ≤ p ∧ p < LA + 2 * LB + 4 ∧ (p < LA → p % β = a)

/-- Points of `[L_A, n)` are inside a lap (`sl5-control-extend.md` (d185a5e) §3). -/
theorem inside_of_ge {a p : ℤ} (hβA : β ≤ LA) (h0 : LA ≤ p) (h1 : p < LA + 2 * LB + 4) :
    Inside LA LB β a p :=
  ⟨by omega, h1, fun h ↦ absurd h (by omega)⟩

/-- Stage `A_0` (`sl5-control-extend.md` (d185a5e) §3, proof of Lemma L): from `a` the orbit
climbs lane `a` and leaves `A_0` at `L_A + g1 a`. Every point `y ∈ [0, L_A)` of the lane is
visited. -/
theorem stage_A0 (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {a : ℤ} (ha0 : 0 ≤ a) (haβ : a < β) :
    ∃ k : ℕ, 0 < k ∧ Path (lap LA LB β) (Inside LA LB β a) a (LA + g1 LA β a) k ∧
      ∀ y, 0 ≤ y → y < LA → y % β = a → ∃ j : ℕ, j < k ∧ (lap LA LB β)^[j] a = y := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := run_exit (f := lap LA LB β) (lo := 0) (hi := LA) (s := β)
    (by omega) (fun p h0 h1 ↦ lap_A0 hβ hβB h0 h1) LA.toNat a
    (by nlinarith [Int.self_le_toNat LA]) ha0 (by omega)
  obtain ⟨he0, he1, he2⟩ := emod_spec (a - LA) β (by omega)
  have hg1 : LA + g1 LA β a = a + k * β := by
    rw [g1]
    have : (a - LA) % β = a + k * β - LA :=
      emod_eq_of_eq_add_mul (c := -(k : ℤ)) (by omega) (by omega) (by ring)
    rw [this]
    ring
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk2
      omega
    · exact h
  refine ⟨k, hk0, ⟨by rw [hk1, hg1], fun j hj0 hjk ↦ ?_⟩, fun y hy0 hy1 hya ↦ ?_⟩
  · obtain ⟨h1, h2⟩ := hk4 j hjk
    rw [h1]
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast hj0
    refine ⟨by nlinarith, by omega, fun _ ↦ ?_⟩
    exact emod_eq_of_eq_add_mul (c := (j : ℤ)) ha0 haβ rfl
  · obtain ⟨-, -, hy⟩ := emod_spec y β (by omega)
    rw [hya] at hy
    have hq0 : 0 ≤ y / β := Int.ediv_nonneg hy0 (by omega)
    have hqk : y / β < k := by
      by_contra hc
      push Not at hc
      nlinarith
    refine ⟨(y / β).toNat, by omega, ?_⟩
    rw [(hk4 _ (by omega)).1, Int.toNat_of_nonneg hq0]
    linarith

/-- Stage `B+` (`sl5-control-extend.md` (d185a5e) §3, proof of Lemma L): from `L_A + e` the
orbit reaches `A_1` at offset `g2 e`. -/
theorem stage_Bp (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {a e : ℤ} (he0 : 0 ≤ e)
    (heβ : e < β) :
    ∃ k : ℕ, Path (lap LA LB β) (Inside LA LB β a) (LA + e) (LA + LB + g2 LB β e) k ∧
      0 ≤ g2 LB β e ∧ g2 LB β e < β := by
  by_cases he : e = 0
  · subst he
    refine ⟨1, ?_, ?_⟩
    · rw [add_zero, g2, ite_eq_left rfl]
      convert Path.single (lap LA LB β) (Inside LA LB β a) LA using 1
      rw [lap_Bp_wrap hβ hβB (by omega)]
      ring
    · rw [g2, ite_eq_left rfl]
      omega
  · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := run_exit (f := lap LA LB β) (lo := LA + 1) (hi := LA + LB)
      (s := β - 1) (by omega)
      (fun p h0 h1 ↦ by rw [lap_Bp hβ hβB (by omega) (by omega) h1]; ring) LB.toNat
      (LA + e) (by nlinarith [Int.self_le_toNat LB]) (by omega) (by omega)
    have hg : g2 LB β e = e + k * (β - 1) - LB := by
      rw [g2, ite_eq_right he]
      exact emod_eq_of_eq_add_mul (c := -(k : ℤ)) (by linarith) (by linarith) (by ring)
    refine ⟨k, ⟨by rw [hk1, hg]; ring, fun j _ hjk ↦ ?_⟩, by rw [hg]; linarith,
      by rw [hg]; linarith⟩
    obtain ⟨h1, h2⟩ := hk4 j hjk
    rw [h1]
    have : (0 : ℤ) ≤ j * (β - 1) := mul_nonneg (by positivity) (by omega)
    exact inside_of_ge hβA (by linarith) (by linarith)

/-- Stage `B-` (`sl5-control-extend.md` (d185a5e) §3, proof of Lemma L): from `B-` offset
`o ∈ [1, L_B)` the orbit enters the window at offset `(o - L_B) mod (β - 1)`. -/
theorem stage_Bm (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {a o : ℤ} (ho0 : 1 ≤ o)
    (ho1 : o < LB) :
    ∃ k : ℕ, Path (lap LA LB β) (Inside LA LB β a) (LA + LB + 4 + o) ((o - LB) % (β - 1)) k := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := run_exit (f := lap LA LB β) (lo := LA + LB + 5)
    (hi := LA + 2 * LB + 4 - β + 1) (s := β - 1) (by omega)
    (fun p h0 h1 ↦ by rw [lap_Bm hβ (by omega) (by omega) (by omega)]; ring) LB.toNat
    (LA + LB + 4 + o) (by nlinarith [Int.self_le_toNat LB]) (by omega) (by omega)
  have hlast := lap_Bm_last (LA := LA) (LB := LB) (β := β) (p := LA + LB + 4 + o + k * (β - 1))
    hβB (by omega) (by nlinarith) (by linarith) (by linarith)
  have hh : (o - LB) % (β - 1) = LA + LB + 4 + o + k * (β - 1) + β - 1 - (LA + 2 * LB + 4) :=
    emod_eq_of_eq_add_mul (c := -((k : ℤ) + 1)) (by linarith) (by linarith) (by ring)
  have hP : Path (lap LA LB β) (Inside LA LB β a) (LA + LB + 4 + o)
      (LA + LB + 4 + o + k * (β - 1)) k := by
    refine ⟨hk1, fun j _ hjk ↦ ?_⟩
    obtain ⟨h1, h2⟩ := hk4 j hjk
    rw [h1]
    have : (0 : ℤ) ≤ j * (β - 1) := mul_nonneg (by positivity) (by omega)
    exact inside_of_ge hβA (by linarith) (by linarith)
  refine ⟨1 + k, hP.trans (inside_of_ge hβA (by nlinarith) (by linarith)) ?_⟩
  rw [hh, ← hlast]
  exact Path.single _ _ _

/-- Stage `A_1` and `B-` (`sl5-control-extend.md` (d185a5e) §3, proof of Lemma L): from `A_1`
offset `g ∈ [0, β)` the orbit enters the window at `g3 g`. -/
theorem stage_A1 (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {a g : ℤ} (hg0 : 0 ≤ g)
    (hgβ : g < β) :
    ∃ k : ℕ, Path (lap LA LB β) (Inside LA LB β a) (LA + LB + g) (g3 LB β g) k := by
  by_cases h4 : g = 4
  · subst h4
    refine ⟨1, ?_⟩
    rw [g3, ite_eq_left rfl, ← lap_Bm_wrap (LA := LA) (LB := LB) hβ hβB (by omega)]
    exact Path.single _ _ _
  by_cases h5 : 5 ≤ g
  · obtain ⟨k, hk⟩ := stage_Bm (a := a) hβ hβB hβA (o := g - 4) (by omega) (by omega)
    refine ⟨k, ?_⟩
    rw [g3, ite_eq_right h4, ite_eq_left h5, show g - 3 - 1 - LB = g - 4 - LB by ring,
      show LA + LB + g = LA + LB + 4 + (g - 4) by ring]
    exact hk
  · obtain ⟨k, hk⟩ := stage_Bm (a := a) hβ hβB hβA (o := g + β - 4) (by omega) (by omega)
    have hstep := lap_A1 (LA := LA) (LB := LB) (β := β) (p := LA + LB + g) hβ hβB (by omega)
      (by omega) (by omega) (by omega)
    have hv : g3 LB β g = (g + β - 4 - LB) % (β - 1) := by
      rw [g3, ite_eq_right h4, ite_eq_right h5,
        show g + β - 4 - LB = g - 3 - 0 - LB + 1 * (β - 1) by ring,
        Int.add_mul_emod_self_right]
    refine ⟨k + 1, (Path.single _ _ _).trans ?_ ?_⟩
    · rw [hstep]
      exact inside_of_ge hβA (by omega) (by omega)
    · rw [hstep, hv, show LA + LB + g + β = LA + LB + 4 + (g + β - 4) by ring]
      exact hk

end Stages

/-- **Lemma L (i), (ii)** (`sl5-control-extend.md` (d185a5e) §3). Let `6 ≤ β ≤ L_B` and
`β ≤ L_A`. From every window offset `a ∈ [0, β)`, `D + β` returns to the window after `k ≥ 1`
steps, at `π_β a = laneMap a ∈ [0, β)`. Every point strictly between lies in `[β, n)`, so this is
the first return. The points of `A_0` visited in between are exactly the points `y < L_A` of the
lane `y ≡ a (mod β)`. -/
theorem lane_return {LA LB β : ℤ} (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {a : ℤ}
    (ha0 : 0 ≤ a) (haβ : a < β) :
    ∃ k : ℕ, 0 < k ∧ (lap LA LB β)^[k] a = laneMap LA LB β a ∧
      0 ≤ laneMap LA LB β a ∧ laneMap LA LB β a < β ∧
      (∀ j : ℕ, 0 < j → j < k → β ≤ (lap LA LB β)^[j] a ∧
        (lap LA LB β)^[j] a < LA + 2 * LB + 4 ∧
        ((lap LA LB β)^[j] a < LA → (lap LA LB β)^[j] a % β = a)) ∧
      ∀ y, 0 ≤ y → y < LA → y % β = a → ∃ j : ℕ, j < k ∧ (lap LA LB β)^[j] a = y := by
  obtain ⟨k₁, hk₁, hP₁, hlane⟩ := stage_A0 hβ hβB hβA ha0 haβ
  obtain ⟨he0, he1, -⟩ := emod_spec (a - LA) β (by omega)
  obtain ⟨k₂, hP₂, hg0, hg1⟩ := stage_Bp (a := a) hβ hβB hβA he0 he1
  obtain ⟨k₃, hP₃⟩ := stage_A1 (a := a) hβ hβB hβA hg0 hg1
  have hP := (hP₁.trans (inside_of_ge hβA (by unfold g1; omega) (by unfold g1; omega)) hP₂).trans
    (inside_of_ge hβA (by omega) (by omega)) hP₃
  have hrange : 0 ≤ laneMap LA LB β a ∧ laneMap LA LB β a < β := by
    unfold laneMap g3
    split_ifs
    · omega
    · obtain ⟨h0, h1, -⟩ := emod_spec (g2 LB β (g1 LA β a) - 3 - 1 - LB) (β - 1) (by omega)
      omega
    · obtain ⟨h0, h1, -⟩ := emod_spec (g2 LB β (g1 LA β a) - 3 - 0 - LB) (β - 1) (by omega)
      omega
  refine ⟨k₃ + (k₂ + k₁), by omega, hP.1, hrange.1, hrange.2, fun j hj0 hjk ↦ hP.2 j hj0 hjk,
    fun y hy0 hy1 hya ↦ ?_⟩
  obtain ⟨j, hj, hjy⟩ := hlane y hy0 hy1 hya
  exact ⟨j, by omega, hjy⟩

/-- **Lemma L (i), rotation form** (`sl5-control-extend.md` (d185a5e) §3). On `[0, β)`,
`π_β = Rot′_u ∘ Rot_{-5} ∘ Rot′_u ∘ Rot_{-1-L_A}` with `u = 1 - L_B`. -/
theorem laneMap_eq_rot {LA LB β : ℤ} (hβ : 6 ≤ β) {a : ℤ} :
    laneMap LA LB β a =
      rot' β (1 - LB) (rot β (-5) (rot' β (1 - LB) (rot β (-1 - LA) a))) := by
  have hg2 : ∀ e, 0 ≤ e → e < β → g2 LB β e = rot' β (1 - LB) ((e - 1) % β) := by
    intro e he0 he1
    by_cases he : e = 0
    · subst he
      have h : ((0 : ℤ) - 1) % β = β - 1 :=
        emod_eq_of_eq_add_mul (c := -1) (by omega) (by omega) (by ring)
      rw [g2, ite_eq_left rfl, rot', h, ite_eq_left rfl]
    · have h : (e - 1) % β = e - 1 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [g2, ite_eq_right he, rot', h, ite_eq_right (by omega)]
      ring_nf
  have hg3 : ∀ g, 0 ≤ g → g < β → g3 LB β g = rot' β (1 - LB) (rot β (-5) g) := by
    intro g hg0 hg1
    unfold g3 rot rot'
    by_cases h4 : g = 4
    · subst h4
      have h : ((4 : ℤ) + -5) % β = β - 1 :=
        emod_eq_of_eq_add_mul (c := -1) (by omega) (by omega) (by ring)
      rw [ite_eq_left rfl, h, ite_eq_left rfl]
    by_cases h5 : 5 ≤ g
    · have h : (g + -5) % β = g - 5 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [ite_eq_right h4, ite_eq_left h5, h, ite_eq_right (by omega)]
      ring_nf
    · have h : (g + -5) % β = g - 5 + β :=
        emod_eq_of_eq_add_mul (c := -1) (by omega) (by omega) (by ring)
      rw [ite_eq_right h4, ite_eq_right h5, h, ite_eq_right (by omega),
        show g - 5 + β + (1 - LB) = g - 3 - 0 - LB + 1 * (β - 1) by ring,
        Int.add_mul_emod_self_right]
  obtain ⟨he0, he1, -⟩ := emod_spec (a - LA) β (by omega)
  have hrot : rot β (-1 - LA) a = ((a - LA) % β - 1) % β := by
    have h := Int.emod_add_ediv_mul (a - LA) β
    rw [rot, show a + (-1 - LA) = ((a - LA) % β - 1) + (a - LA) / β * β by linarith,
      Int.add_mul_emod_self_right]
  have hg2r : 0 ≤ g2 LB β (g1 LA β a) ∧ g2 LB β (g1 LA β a) < β := by
    unfold g2 g1
    split_ifs
    · omega
    · obtain ⟨h0, h1, -⟩ := emod_spec ((a - LA) % β - LB) (β - 1) (by omega)
      omega
  rw [laneMap, hg3 _ hg2r.1 hg2r.2, g1, hg2 _ he0 he1, hrot]

/-- **Corollary R** (`sl5-control-extend.md` (d185a5e) §4). If `(β - 1) ∣ (L_B - 1)`, then
`u ≡ 0`, `Rot′_u` is the identity and `π_β` is the rotation by `-(L_A + 6)` of `ℤ/β`. -/
theorem laneMap_eq_of_dvd {LA LB β : ℤ} (hβ : 6 ≤ β) (hd : (β - 1) ∣ (LB - 1)) (a : ℤ) :
    laneMap LA LB β a = (a - (LA + 6)) % β := by
  have hrot' : ∀ x, 0 ≤ x → x < β → rot' β (1 - LB) x = x := by
    intro x hx0 hx1
    unfold rot'
    split_ifs with h
    · exact h.symm
    · obtain ⟨c, hc⟩ := hd
      exact emod_eq_of_eq_add_mul (c := -c) hx0 (by omega)
        (by rw [show x + (1 - LB) = x - (LB - 1) by ring, hc]; ring)
  obtain ⟨h0, h1, -⟩ := emod_spec (a + (-1 - LA)) β (by omega)
  obtain ⟨h2, h3, -⟩ := emod_spec ((a + (-1 - LA)) % β + -5) β (by omega)
  rw [laneMap_eq_rot hβ]
  simp only [rot]
  rw [hrot' _ h0 h1, hrot' _ h2 h3, Int.emod_add_emod]
  ring_nf

/-- **Corollary R, `β = L_B`** (`sl5-control-extend.md` (d185a5e) §4). When
`L_A + 6 = 2 L_B + 1`, as for `twoarc(m)` with `m` even, `π_{L_B}` is the rotation by `-1`, so it
is one `L_B`-cycle. -/
theorem laneMap_self_of_even {LA LB : ℤ} (hβ : 6 ≤ LB) (hA : LA + 6 = 2 * LB + 1) (a : ℤ) :
    laneMap LA LB LB a = (a - 1) % LB := by
  rw [laneMap_eq_of_dvd hβ (dvd_refl _), hA,
    show a - (2 * LB + 1) = a - 1 + (-2) * LB by ring, Int.add_mul_emod_self_right]

/-- `D + β` on `ℤ/n`, read in positions: `x ↦ x + β + slip x` (`sl5-control-extend.md`
(d185a5e) §3, `Ψ_β = D + β`). -/
def laneStep (N : ℕ) (LA LB β : ℤ) (x : ZMod N) : ZMod N :=
  x + (β : ZMod N) + (slip LA LB (x.val : ℤ) : ZMod N)

/-- `laneStep` is `lap` on representatives in `[0, n)` (`sl5-control-extend.md` (d185a5e) §3). -/
theorem val_laneStep {N : ℕ} [NeZero N] {LA LB β : ℤ} (hN : (N : ℤ) = LA + 2 * LB + 4)
    (x : ZMod N) : ((laneStep N LA LB β x).val : ℤ) = lap LA LB β (x.val : ℤ) := by
  have h : laneStep N LA LB β x = (((x.val : ℤ) + β + slip LA LB (x.val : ℤ) : ℤ) : ZMod N) := by
    rw [laneStep]
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.val_intCast, hN, lap]

/-- Iterates of `laneStep` are iterates of `lap` (`sl5-control-extend.md` (d185a5e) §3). -/
theorem val_laneStep_iterate {N : ℕ} [NeZero N] {LA LB β : ℤ}
    (hN : (N : ℤ) = LA + 2 * LB + 4) (x : ZMod N) (k : ℕ) :
    (((laneStep N LA LB β)^[k] x).val : ℤ) = (lap LA LB β)^[k] (x.val : ℤ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, val_laneStep hN, Function.iterate_succ_apply]

/-- **Lemma L (i) on `ℤ/n`** (`sl5-control-extend.md` (d185a5e) §3). For `6 ≤ β ≤ L_B`,
`β ≤ L_A` and `n = L_A + 2 L_B + 4`, every point `x` of the window `[0, β)` returns to the window
under `D + β` after `k ≥ 1` steps, at the point with representative `π_β x`, and the orbit stays
outside the window in between. -/
theorem lane_return_zmod {N : ℕ} [NeZero N] {LA LB β : ℤ} (hN : (N : ℤ) = LA + 2 * LB + 4)
    (hβ : 6 ≤ β) (hβB : β ≤ LB) (hβA : β ≤ LA) {x : ZMod N} (hx : (x.val : ℤ) < β) :
    ∃ k : ℕ, 0 < k ∧ (((laneStep N LA LB β)^[k] x).val : ℤ) = laneMap LA LB β (x.val : ℤ) ∧
      ∀ j : ℕ, 0 < j → j < k → β ≤ (((laneStep N LA LB β)^[j] x).val : ℤ) := by
  obtain ⟨k, hk, h1, -, -, h2, -⟩ := lane_return hβ hβB hβA (Int.natCast_nonneg x.val) hx
  refine ⟨k, hk, by rw [val_laneStep_iterate hN, h1], fun j hj0 hjk ↦ ?_⟩
  rw [val_laneStep_iterate hN]
  exact (h2 j hj0 hjk).1

end Lane

end Pairing
