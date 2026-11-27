import Mathlib.Tactic.LinearCombination
import Repair.Cover.NCycle
import Repair.LowerBound.Arc

/-!
# The walk through any finite set of special points

Source: `results/struct-lb-extend.md` §1 (positions and contexts, COD-186 Lemmas 1 and 2) and
§3.3, Theorem B, with `results/struct-lb-contra.md` §3.2 (organize-archive b5cb45e).

This generalises `ham_of_chart` of `ZeroCore.lean` from the six gadget points to any finite family
`g : α → ℤ/n` of special points that `F_{s0}` maps to itself by `τ`. Off the special points
`P̃ y = 2 s0 - y`, and on them `P̃ (g j) = g (r j)`. A unit `μ` (the multiplier of a factor `F_t`)
puts the point `g j` at the position `z j ≡ 2 (g j - s0) μ (mod n)`. If the positions, read in the
order `ord`, increase strictly inside a window of length less than `n`, and the arc map
`i ↦ ordInv (τ (r (ord (i + 1))))` runs through every arc, then `P ∪ F_t` is one cycle.

* `ham_of_positions` : the walk, for one factor and one cyclic order of the special points.
* `coversB_spec` : a Boolean check of the arc condition, for `decide`.
-/

namespace Pairing

namespace LowerBound

open Equiv PerfectMatching RoundRobin

variable {n : ℕ}

/-- The arc condition of `sameCycle_of_arcs`: iterating `i ↦ ordInv (τ (r (ord (i + 1))))` from
arc `0` reaches every arc. This is "`R` is one cycle with the context" of
`results/struct-lb-extend.md` §1 (organize-archive b5cb45e). -/
def ArcCovers {α : Type*} {N : ℕ} (ord : Fin (N + 1) → α) (ordInv : α → Fin (N + 1))
    (τ r : α → α) : Prop :=
  ∀ j, ∃ k : ℕ, (fun i ↦ ordInv (τ (r (ord (i + 1)))))^[k] 0 = j

/-- **The walk through special points** (`results/struct-lb-extend.md` §1 and Theorem B,
organize-archive b5cb45e). Let `P̃ y = 2 s0 - y` off the special points `g j`, and
`P̃ (g j) = g (r j)` on them, where `F_{s0}` maps `g j` to `g (τ j)`. Let `μ` be a unit and let
`z j ≡ 2 (g j - s0) μ` be integer positions that increase strictly along `ord`, with the last
less than the first plus `n`. If the arc map covers, then some round-robin factor `F_t` makes
`P ∪ F_t` one cycle. The factor has `4 (t - s0) = μ⁻¹`. -/
theorem ham_of_positions (hn : Odd n) [NeZero n] {s0 : ZMod n}
    {P : PerfectMatching (Option (ZMod n))} {α : Type*} (g : α → ZMod n) (τ : α → α)
    (hτ : ∀ j, g (τ j) = 2 * s0 - g j)
    (hP : ∀ y, (∀ j, y ≠ g j) → pinned P y = 2 * s0 - y)
    (r : α → α) (hr : ∀ j, pinned P (g j) = g (r j))
    {N : ℕ} (ord : Fin (N + 1) → α) (ordInv : α → Fin (N + 1)) (hord : ∀ j, ord (ordInv j) = j)
    {μ : ZMod n} (hμ : IsUnit μ) (z : α → ℤ) (hz : ∀ j, (z j : ZMod n) = 2 * (g j - s0) * μ)
    (hmono : StrictMono fun i ↦ z (ord i)) (hwin : z (ord (Fin.last N)) < z (ord 0) + n)
    (hcov : ArcCovers ord ordInv τ r) : ∃ t, Ham P (factor hn t) := by
  obtain ⟨d, hd⟩ : ∃ d : ZMod n, 2 * μ * d = 1 :=
    ⟨_, ((isUnit_two hn).mul hμ).mul_val_inv⟩
  obtain ⟨t, ht⟩ : ∃ t : ZMod n, 2 * (t - s0) = d := by
    obtain ⟨h, hh⟩ : ∃ h : ZMod n, 2 * h = 1 := ⟨_, (isUnit_two hn).mul_val_inv⟩
    exact ⟨s0 + d * h, by linear_combination d * hh⟩
  refine ⟨t, ?_⟩
  rw [ham_factor_iff_sameCycle]
  intro x y
  set e : ℤ → ZMod n := fun v ↦ s0 + v * d with he
  have hgz : ∀ j, e (z j) = g j := by
    intro j
    simp only [he]
    rw [hz]
    linear_combination (g j - s0) * hd
  have hσ : ∀ w, (pinned (factor hn t) * pinned P) w = 2 * t - pinned P w := by
    intro w
    rw [Perm.mul_apply, pinned_factor]
  refine sameCycle_of_arcs (r := N) _ e ?_ ?_ ?_ (fun i ↦ z (ord i)) hmono hwin
    (fun i ↦ ordInv (τ (r (ord i)))) ?_ ?_ hcov x y
  · intro v k
    simp only [he]
    push_cast [ZMod.natCast_self]
    ring
  · intro w
    refine ⟨(((w - s0) * (2 * μ) : ZMod n).val : ℤ), ?_⟩
    simp only [he, Int.cast_natCast, ZMod.natCast_zmod_val]
    linear_combination (w - s0) * hd
  · intro v v' h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [he] at h
    push_cast
    linear_combination 2 * μ * h - ((v : ZMod n) - v') * hd
  · intro v hv
    have hng : ∀ j, e v ≠ g j := by
      intro j h
      apply hv (ordInv j)
      rw [h, hord, hgz]
    rw [hσ, hP _ hng]
    simp only [he]
    push_cast
    linear_combination ht
  · intro i
    rw [hσ, hgz, hr]
    have h1 : e (z (ord (ordInv (τ (r (ord i))))) + 1) =
        e (z (ord (ordInv (τ (r (ord i)))))) + d := by
      simp only [he]
      push_cast
      ring
    rw [h1, hgz, hord, hτ]
    linear_combination ht

/-- The first `k` points of the orbit of `x` under `f`. -/
def orbit {β : Type*} (f : β → β) : ℕ → β → List β
  | 0, _ => []
  | k + 1, x => x :: orbit f k (f x)

/-- A point of `orbit f k x` is an iterate of `x`. -/
theorem exists_iterate_of_mem_orbit {β : Type*} {f : β → β} :
    ∀ {k : ℕ} {x y : β}, y ∈ orbit f k x → ∃ i, f^[i] x = y
  | 0, _, _, h => by simp [orbit] at h
  | k + 1, x, y, h => by
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, h.symm⟩
    · obtain ⟨i, hi⟩ := exists_iterate_of_mem_orbit h
      exact ⟨i + 1, by rw [Function.iterate_succ_apply, hi]⟩

/-- `allBelow p k` checks `p i` for every `i < k`. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => p k && allBelow p k

/-- `allBelow p k = true` gives `p i = true` for every `i < k`. -/
theorem allBelow_spec {p : ℕ → Bool} : ∀ {k : ℕ}, allBelow p k = true → ∀ i < k, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact allBelow_spec h.2 i hi
    · exact h.1

/-- The Boolean form of `ArcCovers`: the first `N + 1` points of the orbit of arc `0` contain
every arc (`results/struct-lb-extend.md` §1, organize-archive b5cb45e). -/
def coversB {α : Type*} {N : ℕ} (ord : Fin (N + 1) → α) (ordInv : α → Fin (N + 1))
    (τ r : α → α) : Bool :=
  let l := (orbit (fun i ↦ ordInv (τ (r (ord (i + 1))))) (N + 1) 0).map Fin.val
  allBelow (fun j ↦ decide (j ∈ l)) (N + 1)

/-- `coversB` is sound for `ArcCovers` (`results/struct-lb-extend.md` §1, organize-archive
b5cb45e). -/
theorem coversB_spec {α : Type*} {N : ℕ} {ord : Fin (N + 1) → α} {ordInv : α → Fin (N + 1)}
    {τ r : α → α} (h : coversB ord ordInv τ r = true) : ArcCovers ord ordInv τ r := by
  intro j
  have h1 := allBelow_spec h j j.2
  simp only [decide_eq_true_eq, List.mem_map] at h1
  obtain ⟨y, hy, hyj⟩ := h1
  obtain ⟨i, hi⟩ := exists_iterate_of_mem_orbit hy
  exact ⟨i, hi.trans (Fin.ext hyj)⟩

end LowerBound

end Pairing
