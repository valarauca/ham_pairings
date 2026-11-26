import Repair.Covering.Basic
import Suppression.Density

/-!
# Repair distance is not monotone under lifting (`covering-spike.md` §3, §4)

For a tail `T` of `V_m ∖ G` with gadget `G = {1, …, 6}`, `ρ(T)` is the least `tailDist P T` over
zero states `P`. This file exhibits a base tail `T'` at `m' = 6` (`a = 11`) with `ρ(T') = 2`
and a tail `T` at `m = 17` (`n = 33`) lying over it with `ρ(T) = 0`.

Certificates, proved sound for every order.
* `altWalk X Y j v` : the alternating walk `v, Y v, X (Y v), …`. `ham_of_altWalk` : if it visits
  every vertex, `X ∪ Y` is one cycle.
* `ClosedMiss`, `isZeroState_of_closedMiss` : if for each `t` the walk from `∞` is closed under
  `P` and `F_t` and misses a vertex, `P` is a zero state.
* `pairUp`, `allComplete` : a search over all perfect matchings that extend a symmetric partial
  pairing `f`. `allComplete_sound` : if it returns `true`, every perfect matching extending `f`
  passes the test. `not_isZeroState_of_allComplete` : with the test "some `F_t` closes one cycle",
  no perfect matching extending `f` is a zero state.

The witness (`covering-spike.md` §3, run R2, `scripts/covering-lift-a11k3.out`).
* `baseTail = {0 8, 7 9, 10 ∞}` at `a = 11`. `two_le_tailDist_baseTail` : every zero state misses
  two of its edges, by `allComplete` on its three two-edge cores (`3 · 105` completions).
  `baseZero` : a zero state missing exactly two.
* `baseFull = baseTail ∪ {1 2, 3 5, 4 6}` and its zero-voltage translation lift `liftFull` at
  `n = 33`, with reflection branch over `10`. `liftTail` is `liftFull` off `G`, the lifted tail
  `Λ_3(T', M', 0, 0)` of §3.
* `liftZero = liftTail ∪ {1 3, 2 4, 5 6}` is a zero state containing `liftTail`, and it is
  subordinate to no perfect matching of `V_11`.
* `rho_not_monotone` : all of the above together.

The general claim, stated as a conjecture and not proved here. *No pushforward*: there is no
constant `c` such that `ρ_a(T') ≤ ρ_{ka}(Λ) + c` for every odd `a`, `k`, base tail `T'` and
lifted tail `Λ = Λ_k(T', M', g, j₀)`. Equivalently no map from zero states near `Λ` to zero
states near `T'` loses only a bounded number of edges. The witness gives `c ≥ 2`. It refutes
monotonicity `ρ_a(T') ≤ ρ_{ka}(Λ)`, the slack-one form `ρ_a(T') ≤ ρ_{ka}(Λ) + 1`, and every map
`Φ` with `tailDist (Φ P) T' ≤ tailDist P Λ + 1`, and its zero state has no subordinate base
matching at all. It does not refute `c = 2` or any multiplicative form.

The archive's residue-structured lift `T↑` (`old-personal-chatgpt` doc
01a1e303-3c8c-7386-b5e8-578014fbf101 §4, COD-219) is a different tail from `Λ_k`. `T↑` carries
each base edge on one representative pair and matches every other point inside its residue
class, so `δ_S(T↑) = |T' ∖ S|` and `ρ(T↑) ≤ ρ(T')`. `Λ_k` carries each base edge on all `k`
sheets and `M'` on the `k - 1` gadget sheets, so the archive bound gives only
`ρ(Λ_k) ≤ k |T'_fin ∖ S| + [∞ b' ∉ S] + (k - 1) |M' ∖ S|`.
-/

namespace Pairing

namespace RoundRobin

namespace Covering

open PerfectMatching

section Certificates

variable {V : Type*}

/-- The alternating walk `v, Y v, X (Y v), …` with `j` steps of each matching.
(`covering-spike.md` §3, R2 witness) -/
def altWalk (X Y : V → V) : ℕ → V → List V
  | 0, v => [v]
  | j + 1, v => v :: Y v :: altWalk X Y j (X (Y v))

/-- The alternating walk starts at its first vertex. (`covering-spike.md` §3, R2 witness) -/
theorem mem_altWalk_self (X Y : V → V) (j : ℕ) (v : V) : v ∈ altWalk X Y j v := by
  cases j <;> simp [altWalk]

/-- Every vertex on the alternating walk from `v` is reachable from `v` in `X ∪ Y`.
(`covering-spike.md` §3, R2 witness) -/
theorem reachable_of_mem_altWalk (X Y : PerfectMatching V) :
    ∀ (j : ℕ) (v w : V), w ∈ altWalk X.mate Y.mate j v → (X.toGraph ⊔ Y.toGraph).Reachable v w
  | 0, v, w, hw => by
    rw [altWalk, List.mem_singleton] at hw
    rw [hw]
  | j + 1, v, w, hw => by
    have h1 : (X.toGraph ⊔ Y.toGraph).Reachable v (Y.mate v) :=
      SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr rfl))
    have h2 : (X.toGraph ⊔ Y.toGraph).Reachable (Y.mate v) (X.mate (Y.mate v)) :=
      SimpleGraph.Adj.reachable ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl rfl))
    rw [altWalk, List.mem_cons, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · rfl
    · exact h1
    · exact (h1.trans h2).trans (reachable_of_mem_altWalk X Y j _ w hw)

/-- If the alternating walk from `v` visits every vertex, `X ∪ Y` is one cycle.
(`covering-spike.md` §3, R2 witness) -/
theorem ham_of_altWalk (X Y : PerfectMatching V) (j : ℕ) (v : V)
    (h : ∀ w, w ∈ altWalk X.mate Y.mate j v) : Ham X Y :=
  have : Nonempty V := ⟨v⟩
  ⟨fun u w ↦ (reachable_of_mem_altWalk X Y j v u (h u)).symm.trans
    (reachable_of_mem_altWalk X Y j v w (h w))⟩

/-- `L` is closed under `p` and `q` and misses some vertex. (`covering-spike.md` §3, R2 witness) -/
def ClosedMiss (p q : V → V) (L : List V) : Prop :=
  (∀ v ∈ L, p v ∈ L) ∧ (∀ v ∈ L, q v ∈ L) ∧ ∃ w, w ∉ L

instance [Fintype V] [DecidableEq V] (p q : V → V) (L : List V) :
    Decidable (ClosedMiss p q L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A nonempty list closed under both matchings that misses a vertex blocks `Ham`.
(`covering-spike.md` §3, R2 witness) -/
theorem not_ham_of_closedMiss (X Y : PerfectMatching V) {L : List V} {u : V} (hu : u ∈ L)
    (h : ClosedMiss X.mate Y.mate L) : ¬Ham X Y := by
  obtain ⟨hX, hY, w, hw⟩ := h
  exact not_ham_of_closed X Y {v | v ∈ L} hX hY hu hw

/-- The partial pairing `f` is symmetric. (`covering-spike.md` §3, R2 witness) -/
def PartialSymm (f : V → Option V) : Prop :=
  ∀ x y, f x = some y → f y = some x

/-- The perfect matching `P` extends the partial pairing `f`. -/
def Extends (P : PerfectMatching V) (f : V → Option V) : Prop :=
  ∀ x y, f x = some y → P.mate x = y

/-- Every perfect matching extends the empty pairing. (`covering-spike.md` §3, R2 witness) -/
theorem extends_none (P : PerfectMatching V) : Extends P fun _ ↦ none :=
  fun _ _ h ↦ by simp at h

variable [DecidableEq V]

/-- The partial pairing `f` with the pair `v ↔ w` added. (`covering-spike.md` §3, R2 witness) -/
def pairUp (f : V → Option V) (v w : V) : V → Option V :=
  fun x ↦ if x = v then some w else if x = w then some v else f x

instance [Fintype V] (f : V → Option V) : Decidable (PartialSymm f) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))

/-- Adding a pair of `P` keeps `P` an extension. (`covering-spike.md` §3, R2 witness) -/
theorem Extends.pairUp {P : PerfectMatching V} {f : V → Option V} (hf : Extends P f) {v w : V}
    (hvw : P.mate v = w) : Extends P (pairUp f v w) := by
  intro x y h
  unfold Covering.pairUp at h
  split_ifs at h with h1 h2
  · rw [Option.some_inj] at h
    rw [h1, hvw, h]
  · rw [Option.some_inj] at h
    rw [h2, ← h, ← hvw, mate_mate]
  · exact hf x y h

/-- Adding a pair of two free vertices keeps a partial pairing symmetric.
(`covering-spike.md` §3, R2 witness) -/
theorem PartialSymm.pairUp {f : V → Option V} (hf : PartialSymm f) {v w : V} (hvw : w ≠ v)
    (hv : f v = none) (hw : f w = none) : PartialSymm (pairUp f v w) := by
  intro x y h
  unfold Covering.pairUp at h ⊢
  split_ifs at h with h1 h2
  · rw [Option.some_inj] at h
    subst h
    simp [hvw, h1]
  · rw [Option.some_inj] at h
    subst h
    simp [h2]
  · have hy := hf x y h
    have hyv : y ≠ v := by
      rintro rfl
      rw [hv] at hy
      cases hy
    have hyw : y ≠ w := by
      rintro rfl
      rw [hw] at hy
      cases hy
    simp [hyv, hyw, hy]

/-- `allComplete good vs fuel f` searches every perfect matching that extends `f`: it pairs the
first free vertex of `vs` with each other free vertex in turn, and tests `good` at the leaves.
(`covering-spike.md` §3, R2 witness) -/
def allComplete (good : (V → V) → Bool) (vs : List V) : ℕ → (V → Option V) → Bool
  | 0, _ => false
  | fuel + 1, f =>
    match vs.find? fun x ↦ (f x).isNone with
    | none => good fun x ↦ (f x).getD x
    | some v => vs.all fun w ↦
        !(decide (w ≠ v) && (f w).isNone) || allComplete good vs fuel (pairUp f v w)

/-- Soundness of the search. If `vs` lists every vertex, `f` is symmetric and `P` extends `f`,
then `allComplete good vs fuel f = true` forces `good P.mate = true`.
(`covering-spike.md` §3, R2 witness) -/
theorem allComplete_sound (good : (V → V) → Bool) (vs : List V) (hvs : ∀ x, x ∈ vs)
    (P : PerfectMatching V) :
    ∀ (fuel : ℕ) (f : V → Option V), PartialSymm f → Extends P f →
      allComplete good vs fuel f = true → good P.mate = true
  | 0, f, _, _, h => by simp [allComplete] at h
  | fuel + 1, f, hs, he, h => by
    rw [allComplete] at h
    split at h
    · rename_i hnone
      have hfun : (fun x ↦ (f x).getD x) = P.mate := by
        funext x
        have hx := List.find?_eq_none.mp hnone x (hvs x)
        rcases hfx : f x with _ | y
        · simp [hfx] at hx
        · rw [Option.getD_some, he x y hfx]
      rwa [hfun] at h
    · rename_i v hv
      have hfv : f v = none := by
        simpa using List.find?_some hv
      have hwv : P.mate v ≠ v := P.mate_ne v
      have hfw : f (P.mate v) = none := by
        rcases hf : f (P.mate v) with _ | u
        · rfl
        · have hu := he _ u hf
          rw [mate_mate] at hu
          subst hu
          rw [hs _ _ hf] at hfv
          cases hfv
      have hrec := List.all_eq_true.mp h (P.mate v) (hvs _)
      simp only [ne_eq, hwv, not_false_eq_true, decide_true, hfw, Option.isNone_none,
        Bool.and_self, Bool.not_true, Bool.false_or] at hrec
      exact allComplete_sound good vs hvs P fuel _ (hs.pairUp hwv hfv hfw) (he.pairUp rfl) hrec

end Certificates

section Orders

variable {n : ℕ}

/-- The test "some `F_t ∪ P` is one cycle", read off the alternating walk from `∞`.
(`covering-spike.md` §3, R2 witness) -/
def hamSome (n : ℕ) [NeZero n] (j : ℕ) (g : Option (ZMod n) → Option (ZMod n)) : Bool :=
  decide (∃ t : ZMod n, ∀ w, w ∈ altWalk g (mateFn t) j none)

/-- A perfect matching that passes `hamSome` is not a zero state.
(`covering-spike.md` §3, R2 witness) -/
theorem not_isZeroState_of_hamSome (hn : Odd n) [NeZero n] {j : ℕ}
    {P : PerfectMatching (Option (ZMod n))} (h : hamSome n j P.mate = true) :
    ¬IsZeroState (factor hn) P := by
  obtain ⟨t, ht⟩ := of_decide_eq_true h
  exact fun hz ↦ hz t (ham_of_altWalk P (factor hn t) j none ht)

/-- If the search with `hamSome` succeeds from a symmetric `f`, no perfect matching extending `f`
is a zero state. (`covering-spike.md` §3, R2 witness) -/
theorem not_isZeroState_of_allComplete (hn : Odd n) [NeZero n] {j fuel : ℕ}
    {vs : List (Option (ZMod n))} (hvs : ∀ x, x ∈ vs)
    {f : Option (ZMod n) → Option (Option (ZMod n))}
    (hs : PartialSymm f) (h : allComplete (hamSome n j) vs fuel f = true)
    {P : PerfectMatching (Option (ZMod n))} (hP : Extends P f) : ¬IsZeroState (factor hn) P :=
  not_isZeroState_of_hamSome hn (allComplete_sound _ vs hvs P fuel f hs hP h)

/-- If for each `t` the alternating walk from `∞` is closed under `P` and `F_t` and misses a
vertex, then `P` is a zero state. (`covering-spike.md` §3, R2 witness) -/
theorem isZeroState_of_closedMiss (hn : Odd n) {j : ℕ} {P : PerfectMatching (Option (ZMod n))}
    (h : ∀ t : ZMod n, ClosedMiss P.mate (mateFn t) (altWalk P.mate (mateFn t) j none)) :
    IsZeroState (factor hn) P :=
  fun t ↦ not_ham_of_closedMiss P (factor hn t) (mem_altWalk_self _ _ _ _) (h t)

/-- An edge `s(x, y)` lies in `P` iff `P` pairs `x` with `y`.
(`covering-spike.md` §3, R2 witness) -/
theorem mk_mem_edgeSet {V : Type*} (P : PerfectMatching V) (x y : V) :
    s(x, y) ∈ P.toGraph.edgeSet ↔ P.mate x = y :=
  SimpleGraph.mem_edgeSet _

/-- Two distinct tail edges missing from `P` give `tailDist P T ≥ 2`.
(`covering-spike.md` §3, R2 witness) -/
theorem two_le_tailDist {V : Type*} [DecidableEq V] {P : PerfectMatching V} {U : Finset V}
    {T : PerfectMatching U} {e₁ e₂ : Sym2 V} (hne : e₁ ≠ e₂) (h₁ : e₁ ∈ tailEdges T)
    (h₂ : e₂ ∈ tailEdges T) (hP₁ : e₁ ∉ P.toGraph.edgeSet) (hP₂ : e₂ ∉ P.toGraph.edgeSet) :
    2 ≤ tailDist P T := by
  rw [tailDist, ← Finset.card_pair hne]
  refine Finset.card_le_card fun e he ↦ ?_
  rw [Finset.mem_insert, Finset.mem_singleton] at he
  rw [Finset.mem_filter]
  rcases he with rfl | rfl
  exacts [⟨h₁, hP₁⟩, ⟨h₂, hP₂⟩]

end Orders

section Explicit

variable {V : Type*} [DecidableEq V]

/-- The partner function of an explicit list of pairs, the identity off the pairs.
(`covering-spike.md` §3, R2 witness) -/
def ofPairs (l : List (V × V)) (v : V) : V :=
  match l.find? fun e ↦ e.1 = v ∨ e.2 = v with
  | some e => if e.1 = v then e.2 else e.1
  | none => v

/-- The perfect matching with partner function `p`. -/
def mkMatching (p : V → V) (h1 : ∀ v, p (p v) = v) (h2 : ∀ v, p v ≠ v) : PerfectMatching V where
  mate := Function.Involutive.toPerm p h1
  mate_mate := h1
  mate_ne := h2

/-- The perfect matching of `U = V ∖ G` with partner function `p`. -/
def mkTail [Fintype V] (G : Finset V) (p : V → V) (h1 : ∀ v, p (p v) = v)
    (h2 : ∀ v ∉ G, p v ≠ v) (h3 : ∀ v ∉ G, p v ∉ G) : PerfectMatching (Gᶜ : Finset V) where
  mate :=
    { toFun := fun u ↦ ⟨p u, Finset.mem_compl.mpr (h3 u (Finset.mem_compl.mp u.2))⟩
      invFun := fun u ↦ ⟨p u, Finset.mem_compl.mpr (h3 u (Finset.mem_compl.mp u.2))⟩
      left_inv := fun u ↦ Subtype.ext (h1 u)
      right_inv := fun u ↦ Subtype.ext (h1 u) }
  mate_mate u := Subtype.ext (h1 u)
  mate_ne u h := h2 u (Finset.mem_compl.mp u.2) (congrArg Subtype.val h)

end Explicit

namespace Witness

open RoundRobin.Canonical

/-- The label `x < 2m - 1` as a vertex of `V_m`, and `2m - 1` as `∞`. -/
def lab (m : ℕ) (x : ℕ) : Vertex m :=
  if x = 2 * m - 1 then none else some (x : ZMod (2 * m - 1))

/-- The partner function on `V_m` of a list of label pairs. -/
def natPairs (m : ℕ) (l : List (ℕ × ℕ)) : Vertex m → Vertex m :=
  ofPairs (l.map fun e ↦ (lab m e.1, lab m e.2))

/-- The gadget `G = {1, …, 6}` of `V_m`. -/
def gadget (m : ℕ) : Finset (Vertex m) :=
  {some 1, some 2, some 3, some 4, some 5, some 6}

/-- `11 ∣ 33`, that is `2 · 6 - 1 ∣ 2 · 17 - 1`. (`covering-spike.md` §3, R2 witness) -/
theorem dvd_six_seventeen : 2 * 6 - 1 ∣ 2 * 17 - 1 :=
  ⟨3, rfl⟩

/-- The base tail pairs `T' = {0 8, 7 9, 10 ∞}` at `a = 11`. (`covering-spike.md` §3, R2 witness) -/
def baseTailPairs : List (ℕ × ℕ) :=
  [(0, 8), (7, 9), (10, 11)]

/-- The base gadget matching `M' = {1 2, 3 5, 4 6}`. -/
def baseGadgetPairs : List (ℕ × ℕ) :=
  [(1, 2), (3, 5), (4, 6)]

/-- The lifted tail pairs at `n = 33`: `T'` lifted by translations with zero voltage, `10 ∞` with
the reflection pair `21 32` about `10`, and `M'` on sheets `1` and `2`. -/
def liftTailPairs : List (ℕ × ℕ) :=
  [(0, 8), (11, 19), (22, 30), (7, 9), (18, 20), (29, 31), (10, 33), (21, 32), (12, 13),
    (23, 24), (14, 16), (25, 27), (15, 17), (26, 28)]

/-- The base tail `T'` on `V_6 ∖ G`. -/
def baseTail : PerfectMatching ((gadget 6)ᶜ : Finset (Vertex 6)) :=
  mkTail (gadget 6) (natPairs 6 baseTailPairs) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The lifted tail `T = Λ_3(T', M', 0, 0)` on `V_17 ∖ G`. -/
def liftTail : PerfectMatching ((gadget 17)ᶜ : Finset (Vertex 17)) :=
  mkTail (gadget 17) (natPairs 17 liftTailPairs) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The base matching `P' = T' ∪ M'` of `V_6`. -/
def baseFull : PerfectMatching (Vertex 6) :=
  mkMatching (natPairs 6 (baseTailPairs ++ baseGadgetPairs)) (by decide +kernel)
    (by decide +kernel)

/-- The covering lift of `P'` whose restriction to `V_17 ∖ G` is `T`. -/
def liftFull : PerfectMatching (Vertex 17) :=
  mkMatching (natPairs 17 (liftTailPairs ++ baseGadgetPairs)) (by decide +kernel)
    (by decide +kernel)

/-- A zero state of `V_6` that keeps only the edge `7 9` of `T'`. -/
def baseZero : PerfectMatching (Vertex 6) :=
  mkMatching (natPairs 6 [(0, 6), (1, 8), (2, 10), (3, 4), (5, 11), (7, 9)]) (by decide +kernel)
    (by decide +kernel)

/-- The zero state `T ∪ {1 3, 2 4, 5 6}` of `V_17`. -/
def liftZero : PerfectMatching (Vertex 17) :=
  mkMatching (natPairs 17 (liftTailPairs ++ [(1, 3), (2, 4), (5, 6)])) (by decide +kernel)
    (by decide +kernel)

/-- Every vertex of `V_6`. -/
def verts6 : List (Vertex 6) :=
  none :: (List.range 11).map fun x ↦ some (x : ZMod (2 * 6 - 1))

/-- The core `T' ∖ {e}` as a partial pairing, for the two kept edges `v₁ w₁` and `v₂ w₂`. -/
def core (v₁ w₁ v₂ w₂ : ℕ) : Vertex 6 → Option (Vertex 6) :=
  pairUp (pairUp (fun _ ↦ none) (lab 6 v₁) (lab 6 w₁)) (lab 6 v₂) (lab 6 w₂)

/-- `baseZero` is a zero state. (`covering-spike.md` §3, R2 witness) -/
theorem isZeroState_baseZero : IsZeroState (Canonical.factor 6) baseZero :=
  isZeroState_of_closedMiss (j := 6) (modulus_odd 6) (by decide +kernel)

/-- `liftZero` is a zero state. (`covering-spike.md` §3, R2 witness) -/
theorem isZeroState_liftZero : IsZeroState (Canonical.factor 17) liftZero :=
  isZeroState_of_closedMiss (j := 17) (modulus_odd 17) (by decide +kernel)

/-- The tail edges of `T'`. (`covering-spike.md` §3, R2 witness) -/
theorem tailEdges_baseTail :
    tailEdges baseTail = {s(lab 6 0, lab 6 8), s(lab 6 7, lab 6 9), s(lab 6 10, lab 6 11)} := by
  decide +kernel

/-- A matching that keeps two edges of `T'` is not a zero state.
(`covering-spike.md` §3, R2 witness) -/
theorem not_isZeroState_of_core {v₁ w₁ v₂ w₂ : ℕ}
    (hs : PartialSymm (core v₁ w₁ v₂ w₂))
    (hc : allComplete (hamSome (2 * 6 - 1) 6) verts6 12 (core v₁ w₁ v₂ w₂) = true)
    {P : PerfectMatching (Vertex 6)} (h₁ : P.mate (lab 6 v₁) = lab 6 w₁)
    (h₂ : P.mate (lab 6 v₂) = lab 6 w₂) : ¬IsZeroState (Canonical.factor 6) P :=
  not_isZeroState_of_allComplete (modulus_odd 6) (by decide +kernel) hs hc
    (((extends_none P).pairUp h₁).pairUp h₂)

/-- **Base lower bound**, `covering-spike.md` §3 (R1, `covering-base-m6.out`): `ρ(T') ≥ 2`.
Every zero state of `V_6` misses at least two edges of `T' = {0 8, 7 9, 10 ∞}`. -/
theorem two_le_tailDist_baseTail (P : ZeroState 6) : 2 ≤ tailDist P.1 baseTail := by
  by_contra hlt
  have key : ∀ x₁ y₁ x₂ y₂ : ℕ, s(lab 6 x₁, lab 6 y₁) ≠ s(lab 6 x₂, lab 6 y₂) →
      s(lab 6 x₁, lab 6 y₁) ∈ tailEdges baseTail → s(lab 6 x₂, lab 6 y₂) ∈ tailEdges baseTail →
      P.1.mate (lab 6 x₁) = lab 6 y₁ ∨ P.1.mate (lab 6 x₂) = lab 6 y₂ := by
    intro x₁ y₁ x₂ y₂ hne h₁ h₂
    by_contra hc
    rw [not_or] at hc
    exact hlt (two_le_tailDist hne h₁ h₂ (by rw [mk_mem_edgeSet]; exact hc.1)
      (by rw [mk_mem_edgeSet]; exact hc.2))
  have hm : ∀ x y : ℕ, s(lab 6 x, lab 6 y) ∈ tailEdges baseTail →
      s(lab 6 x, lab 6 y) ∈ tailEdges baseTail := fun _ _ h ↦ h
  rw [tailEdges_baseTail] at key hm
  have k1 := key 0 8 7 9 (by decide +kernel) (by simp) (by simp)
  have k2 := key 0 8 10 11 (by decide +kernel) (by simp) (by simp)
  have k3 := key 7 9 10 11 (by decide +kernel) (by simp) (by simp)
  rcases k1 with h08 | h79
  · rcases k3 with h79 | h10
    · exact not_isZeroState_of_core (by decide +kernel) (by decide +kernel) h08 h79 P.2
    · exact not_isZeroState_of_core (by decide +kernel) (by decide +kernel) h08 h10 P.2
  · rcases k2 with h08 | h10
    · exact not_isZeroState_of_core (by decide +kernel) (by decide +kernel) h08 h79 P.2
    · exact not_isZeroState_of_core (by decide +kernel) (by decide +kernel) h79 h10 P.2

/-- **Base upper bound**: `ρ(T') ≤ 2`, witnessed by `baseZero`.
(`covering-spike.md` §3, R2 witness) -/
theorem tailDist_baseZero : tailDist baseZero baseTail = 2 := by
  decide +kernel

/-- `T` lies over `T'`: `liftFull` is a covering lift of `P' = T' ∪ M'`, and it agrees with `T`
off the gadget and `P'` agrees with `T'` off the gadget (`covering-spike.md` §1, §3). -/
theorem isCoveringLift_liftFull :
    IsCoveringLift dvd_six_seventeen baseFull liftFull ∧
      (∀ u : ((gadget 17)ᶜ : Finset (Vertex 17)), liftFull.mate u = liftTail.mate u) ∧
      ∀ u : ((gadget 6)ᶜ : Finset (Vertex 6)), baseFull.mate u = baseTail.mate u := by
  decide +kernel

/-- **Lifted upper bound**: `ρ(T) = 0`, witnessed by `liftZero ⊇ T`.
(`covering-spike.md` §3, R2 witness) -/
theorem tailDist_liftZero : tailDist liftZero liftTail = 0 := by
  decide +kernel

/-- `liftZero` is not a lift: it is subordinate to no perfect matching of `V_6`. Its edges
`1 3` and `12 13` would force `P'(1) = 3` and `P'(1) = 2`. (`covering-spike.md` §3, R2 witness) -/
theorem not_subordinate_liftZero (P' : PerfectMatching (Vertex 6)) :
    ¬Subordinate dvd_six_seventeen P' liftZero := by
  intro hP
  have e1 : proj dvd_six_seventeen (liftZero.mate (lab 17 1)) = some 3 := by decide +kernel
  have e12 : proj dvd_six_seventeen (liftZero.mate (lab 17 12)) = some 2 := by decide +kernel
  have p1 : proj dvd_six_seventeen (lab 17 1) = some 1 := by decide +kernel
  have p12 : proj dvd_six_seventeen (lab 17 12) = some 1 := by decide +kernel
  have h1 : some 3 = P'.mate (some 1) := by
    rcases hP (lab 17 1) with h | h <;> rw [e1, p1] at h
    · exact h
    · exact absurd h (by decide)
  have h2 : some 2 = P'.mate (some 1) := by
    rcases hP (lab 17 12) with h | h <;> rw [e12, p12] at h
    · exact h
    · exact absurd h (by decide)
  exact absurd (h1.trans h2.symm) (by decide)

/-- **Repair distance is not monotone under lifting**, `covering-spike.md` §3, §4. The base tail
`T' = {0 8, 7 9, 10 ∞}` at `a = 11` has `ρ(T') = 2`. The tail `T = Λ_3(T', M', 0, 0)` at
`n = 33` lies over it, as the restriction off `G` of a covering lift of `T' ∪ M'`, and has
`ρ(T) = 0`. The zero state realising `ρ(T) = 0` is subordinate to no perfect matching of `V_11`,
so it is not a lift of a base repair. -/
theorem rho_not_monotone :
    (∀ P : ZeroState 6, 2 ≤ tailDist P.1 baseTail) ∧
      (∃ P : ZeroState 6, tailDist P.1 baseTail = 2) ∧
      IsCoveringLift dvd_six_seventeen baseFull liftFull ∧
      (∀ u : ((gadget 17)ᶜ : Finset (Vertex 17)), liftFull.mate u = liftTail.mate u) ∧
      (∀ u : ((gadget 6)ᶜ : Finset (Vertex 6)), baseFull.mate u = baseTail.mate u) ∧
      ∃ P : ZeroState 17, tailDist P.1 liftTail = 0 ∧
        ∀ P' : PerfectMatching (Vertex 6), ¬Subordinate dvd_six_seventeen P' P.1 :=
  ⟨two_le_tailDist_baseTail, ⟨⟨baseZero, isZeroState_baseZero⟩, tailDist_baseZero⟩,
    isCoveringLift_liftFull.1, isCoveringLift_liftFull.2.1, isCoveringLift_liftFull.2.2,
    ⟨liftZero, isZeroState_liftZero⟩, tailDist_liftZero, not_subordinate_liftZero⟩

end Witness

end Covering

end RoundRobin

end Pairing
