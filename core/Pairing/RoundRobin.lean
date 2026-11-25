import Mathlib.Tactic.LinearCombination
import Pairing.Basic

/-!
# Round-robin factors and zero states

For odd `n`, `RoundRobin.factor hn t` is the round-robin factor `F_t` on `ℤ/n ∪ {∞}`, encoded
as `Option (ZMod n)` with `none = ∞`. It pairs `∞` with `t` and `x ≠ t` with `2t - x`.

* `factor_injective`, `distinct_factors_edge_disjoint` : the `F_t` are distinct and pairwise
  edge-disjoint, and `card_block` : the block `{F_t}` has `n` members.
* `Canonical.Vertex m = V_m = ℤ/(2m-1) ∪ {∞}`, with `card_vertex : |V_m| = 2m`, and
  `Canonical.factor m t` is `F_t` on `V_m`.
* `IsZeroState F P` : no `P ∪ F t` is one cycle. `Canonical.ZeroState m` is the type of zero
  states for the canonical factors, and `Canonical.zeroCount m = Z_m` is their number.
-/

namespace Pairing

namespace PerfectMatching

/-- `P` is a zero state for the family `F` when no `P ∪ F t` is one cycle. -/
def IsZeroState {V ι : Type*} (F : ι → PerfectMatching V) (P : PerfectMatching V) : Prop :=
  ∀ t, ¬Ham P (F t)

instance {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (F : ι → PerfectMatching V) :
    DecidablePred (IsZeroState F) :=
  fun P ↦ inferInstanceAs (Decidable (∀ t, ¬Ham P (F t)))

end PerfectMatching

namespace RoundRobin

open PerfectMatching

variable {n : ℕ}

/-- The partner of a vertex in `F_t`, `∞ ↔ t` and `x ↔ 2t - x`. -/
def mateFn (t : ZMod n) : Option (ZMod n) → Option (ZMod n)
  | none => some t
  | some x => if x = t then none else some (2 * t - x)

/-- `F_t` pairs `∞` with `t`. -/
@[simp]
theorem mateFn_none (t : ZMod n) : mateFn t none = some t :=
  rfl

/-- `F_t` pairs `t` with `∞`. -/
@[simp]
theorem mateFn_self (t : ZMod n) : mateFn t (some t) = none := by
  simp [mateFn]

/-- `F_t` pairs `x ≠ t` with `2t - x`. -/
theorem mateFn_of_ne (t x : ZMod n) (h : x ≠ t) : mateFn t (some x) = some (2 * t - x) := by
  simp [mateFn, h]

/-- `F_t` is an involution. -/
theorem mateFn_involutive (t : ZMod n) : Function.Involutive (mateFn t) := by
  rintro (_ | x)
  · simp
  rcases eq_or_ne x t with rfl | hx
  · simp
  have h : 2 * t - x ≠ t := fun h ↦ hx (by linear_combination -h)
  rw [mateFn_of_ne t x hx, mateFn_of_ne t _ h, sub_sub_cancel]

/-- `2` is a unit of `ℤ/n` for odd `n`. -/
theorem isUnit_two (hn : Odd n) : IsUnit (2 : ZMod n) := by
  simpa using (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hn)).isUnit

/-- For odd `n`, `F_t` has no fixed point. -/
theorem mateFn_ne (hn : Odd n) (t : ZMod n) (v : Option (ZMod n)) : mateFn t v ≠ v := by
  rcases v with _ | x
  · simp
  rcases eq_or_ne x t with rfl | hx
  · simp
  rw [mateFn_of_ne t x hx, Ne, Option.some_inj]
  intro h
  have h2 : 2 * t = 2 * x := by linear_combination h
  exact hx ((isUnit_two hn).mul_left_cancel h2).symm

/-- The round-robin factor `F_t` on `ℤ/n ∪ {∞}`, for odd `n`. -/
def factor (hn : Odd n) (t : ZMod n) : PerfectMatching (Option (ZMod n)) where
  mate := Function.Involutive.toPerm _ (mateFn_involutive t)
  mate_mate := mateFn_involutive t
  mate_ne := mateFn_ne hn t

/-- The partner map of `F_t`. -/
@[simp]
theorem factor_mate (hn : Odd n) (t : ZMod n) (v : Option (ZMod n)) :
    (factor hn t).mate v = mateFn t v :=
  rfl

/-- `F_t` contains `∞t`, so distinct `t` give distinct factors. -/
theorem factor_injective (hn : Odd n) : Function.Injective (factor hn) := by
  intro t s h
  simpa using congrArg (fun F : PerfectMatching (Option (ZMod n)) ↦ F.mate none) h

/-- An edge lies in at most one `F_t`. -/
theorem eq_of_adj_factor (hn : Odd n) {t s : ZMod n} {v w : Option (ZMod n)}
    (ht : (factor hn t).toGraph.Adj v w) (hs : (factor hn s).toGraph.Adj v w) : t = s := by
  rw [toGraph_adj, factor_mate] at ht hs
  rw [← hs] at ht
  rcases v with _ | x
  · simpa using ht
  rcases eq_or_ne x t with rfl | hxt
  · rcases eq_or_ne x s with rfl | hxs
    · rfl
    · simp [mateFn_of_ne _ _ hxs] at ht
  · rcases eq_or_ne x s with rfl | hxs
    · simp [mateFn_of_ne _ _ hxt] at ht
    · rw [mateFn_of_ne t x hxt, mateFn_of_ne s x hxs, Option.some_inj] at ht
      exact (isUnit_two hn).mul_left_cancel (by linear_combination ht)

/-- Distinct round-robin factors share no edge. -/
theorem distinct_factors_edge_disjoint (hn : Odd n) {t s : ZMod n} (hts : t ≠ s)
    (v w : Option (ZMod n)) :
    ¬((factor hn t).toGraph.Adj v w ∧ (factor hn s).toGraph.Adj v w) :=
  fun h ↦ hts (eq_of_adj_factor hn h.1 h.2)

/-- The block `{F_t}` of all round-robin factors. -/
def block [NeZero n] (hn : Odd n) : Finset (PerfectMatching (Option (ZMod n))) :=
  Finset.univ.map ⟨factor hn, factor_injective hn⟩

/-- The members of the block are the `F_t`. -/
theorem mem_block [NeZero n] (hn : Odd n) (P : PerfectMatching (Option (ZMod n))) :
    P ∈ block hn ↔ ∃ t, factor hn t = P := by
  simp [block]

/-- The block has `n` members. -/
theorem card_block [NeZero n] (hn : Odd n) : (block hn).card = n := by
  simp [block, ZMod.card]

namespace Canonical

/-- `V_m = ℤ/(2m-1) ∪ {∞}`, with `none = ∞`. -/
abbrev Vertex (m : ℕ) :=
  Option (ZMod (2 * m - 1))

/-- `2m - 1` is odd. -/
theorem modulus_odd (m : ℕ) [NeZero m] : Odd (2 * m - 1) := by
  have := NeZero.pos m
  exact ⟨m - 1, by omega⟩

instance (m : ℕ) [NeZero m] : NeZero (2 * m - 1) :=
  ⟨(modulus_odd m).pos.ne'⟩

/-- `|V_m| = 2m`. -/
theorem card_vertex (m : ℕ) [NeZero m] : Fintype.card (Vertex m) = 2 * m := by
  have := NeZero.pos m
  rw [Fintype.card_option, ZMod.card]
  omega

/-- The canonical round-robin factor `F_t` on `V_m`. -/
def factor (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) : PerfectMatching (Vertex m) :=
  RoundRobin.factor (modulus_odd m) t

/-- Distinct `t` give distinct canonical factors. -/
theorem factor_injective (m : ℕ) [NeZero m] : Function.Injective (factor m) :=
  RoundRobin.factor_injective (modulus_odd m)

/-- Distinct canonical factors share no edge. -/
theorem distinct_factors_edge_disjoint (m : ℕ) [NeZero m] {t s : ZMod (2 * m - 1)}
    (hts : t ≠ s) (v w : Vertex m) :
    ¬((factor m t).toGraph.Adj v w ∧ (factor m s).toGraph.Adj v w) :=
  RoundRobin.distinct_factors_edge_disjoint (modulus_odd m) hts v w

/-- The canonical block `{F_t}` on `V_m`. -/
def block (m : ℕ) [NeZero m] : Finset (PerfectMatching (Vertex m)) :=
  RoundRobin.block (modulus_odd m)

/-- The canonical block has `2m - 1` members. -/
theorem card_block (m : ℕ) [NeZero m] : (block m).card = 2 * m - 1 :=
  RoundRobin.card_block (modulus_odd m)

/-- The zero states on `V_m`, matchings `P` with `¬Ham P F_t` for every `t`. -/
abbrev ZeroState (m : ℕ) [NeZero m] :=
  {P : PerfectMatching (Vertex m) // IsZeroState (factor m) P}

/-- `Z_m`, the number of zero states on `V_m`. -/
def zeroCount (m : ℕ) [NeZero m] : ℕ :=
  Fintype.card (ZeroState m)

end Canonical

end RoundRobin

end Pairing
