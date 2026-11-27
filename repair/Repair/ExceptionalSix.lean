import Repair.Automorphism
import Repair.Covering.Witness

/-!
# The exceptional symmetry at `m = 6`: `PSL(2,11)` acts on the zero states

At `m = 6` we have `n = 11` and `V_6 = ℤ/11 ∪ {∞}`, the projective line `P¹(𝔽₁₁)`. The zero-state
set `Z_6` is preserved by Möbius maps that are not automorphisms of the round-robin factorization.

* `zeroState i`, `i : Fin 22` : the 22 zero states of `scripts/autgroup-zero-m6.txt`.
  `isZeroState_iff` : a perfect matching of `V_6` is a zero state iff it is listed, and
  `zeroCount_six : Z_6 = 22`. The search `allComplete_listedOrHam` runs over the 945 perfect
  matchings that pair `∞` with `0`. Translations reduce every zero state to one of these.
* `moebius a b c d` : the Möbius map `x ↦ (a x + b)/(c x + d)` of `P¹(𝔽₁₁)`, and `moebius_moebius`,
  composition is matrix multiplication. `T x = x + 1`, `S x = -1/x` and `D x = 2 x`.
* `symZero` : the setwise stabiliser `Sym(Z_6)` of the zero states. `T`, `S` and `D` lie in it,
  `closure_le_symZero`, while `S ∉ Aut(𝓕)`, `S_not_mem_autGroup`.
* `mem_closure_TS_iff` : `⟨T, S⟩` is the group of Möbius maps of determinant `1`, that is
  `PSL(2,11)` on `P¹(𝔽₁₁)`, and `card_closure_TS : |⟨T, S⟩| = 660`. `mem_closure_TSD_iff` and
  `card_closure_TSD` : `⟨T, S, D⟩` is `PGL(2,11)`, of order `1320`.
* `sideA` : under `⟨T, S⟩`, `Z_6` splits into two orbits of `11` matchings,
  `keepsSides_of_mem_closure` and `exists_mem_closure_smul_eq`. Each is a 1-factorization of
  `K_12`, `mate_ne_of_side` and `exists_mate_eq_of_side`, and `D` swaps them.

Not done: the converse, that `Sym(Z_6)` is no larger than `PGL(2,11)`, which needs a search over
permutations of the 12 points.

Source: `results/autgroup-spike.md` §4, runs 4 and 5. By the exact computation of run 5 and the
uniqueness theorem of Cameron and Korchmáros 1993, each orbit is their sporadic 1-factorization of
`K_12`, with full automorphism group `PSL(2,11)`. That identification is not formalized. This file
proves only that each orbit is a 1-factorization on which `⟨T, S⟩` acts
(`results/symmetry-audit-contra.md` row L4, organize-archive bf3fe60).
-/

namespace Pairing

namespace RoundRobin.Canonical

namespace PSL211

open PerfectMatching

/-- The 22 zero states of `V_6` as lists of label pairs, with `11 = ∞`, in the order of
`scripts/autgroup-zero-m6.txt` (`results/autgroup-spike.md` §4). -/
def zeroPairs : List (List (ℕ × ℕ)) :=
  [[(0, 1), (2, 5), (3, 7), (4, 9), (6, 8), (10, 11)],
    [(0, 1), (2, 11), (3, 8), (4, 6), (5, 9), (7, 10)],
    [(0, 2), (1, 5), (3, 6), (4, 10), (7, 8), (9, 11)],
    [(0, 2), (1, 8), (3, 9), (4, 11), (5, 6), (7, 10)],
    [(0, 3), (1, 5), (2, 7), (4, 6), (8, 11), (9, 10)],
    [(0, 3), (1, 7), (2, 9), (4, 5), (6, 11), (8, 10)],
    [(0, 4), (1, 6), (2, 10), (3, 5), (7, 11), (8, 9)],
    [(0, 4), (1, 10), (2, 5), (3, 9), (6, 7), (8, 11)],
    [(0, 5), (1, 3), (2, 6), (4, 7), (8, 9), (10, 11)],
    [(0, 5), (1, 9), (2, 4), (3, 10), (6, 11), (7, 8)],
    [(0, 6), (1, 8), (2, 10), (3, 4), (5, 11), (7, 9)],
    [(0, 6), (1, 11), (2, 3), (4, 7), (5, 9), (8, 10)],
    [(0, 7), (1, 9), (2, 3), (4, 11), (5, 10), (6, 8)],
    [(0, 7), (1, 10), (2, 8), (3, 11), (4, 5), (6, 9)],
    [(0, 8), (1, 2), (3, 11), (4, 9), (5, 7), (6, 10)],
    [(0, 8), (1, 3), (2, 9), (4, 10), (5, 11), (6, 7)],
    [(0, 9), (1, 4), (2, 8), (3, 10), (5, 6), (7, 11)],
    [(0, 9), (1, 7), (2, 11), (3, 4), (5, 8), (6, 10)],
    [(0, 10), (1, 4), (2, 6), (3, 8), (5, 7), (9, 11)],
    [(0, 10), (1, 11), (2, 7), (3, 5), (4, 8), (6, 9)],
    [(0, 11), (1, 2), (3, 6), (4, 8), (5, 10), (7, 9)],
    [(0, 11), (1, 6), (2, 4), (3, 7), (5, 8), (9, 10)]]

/-- The partner function of the `i`-th listed zero state (`results/autgroup-spike.md` §4). -/
def zeroMate (i : Fin 22) : Vertex 6 → Vertex 6 :=
  Covering.Witness.natPairs 6 (zeroPairs.getD i [])

/-- Each listed partner function is an involution (`results/autgroup-spike.md` §4). -/
theorem zeroMate_zeroMate : ∀ (i : Fin 22) (v : Vertex 6), zeroMate i (zeroMate i v) = v := by
  decide +kernel

/-- Each listed partner function has no fixed point (`results/autgroup-spike.md` §4). -/
theorem zeroMate_ne : ∀ (i : Fin 22) (v : Vertex 6), zeroMate i v ≠ v := by
  decide +kernel

/-- The `i`-th listed zero state of `V_6` (`results/autgroup-spike.md` §4). -/
def zeroState (i : Fin 22) : PerfectMatching (Vertex 6) :=
  Covering.mkMatching (zeroMate i) (zeroMate_zeroMate i) (zeroMate_ne i)

/-- The partner map of `zeroState i` is `zeroMate i` (`results/autgroup-spike.md` §4). -/
@[simp]
theorem zeroState_mate (i : Fin 22) (v : Vertex 6) : (zeroState i).mate v = zeroMate i v :=
  rfl

/-- The 22 listed matchings are distinct (`results/autgroup-spike.md` §4). -/
theorem zeroState_injective : Function.Injective zeroState := by
  have h : ∀ i j : Fin 22, (∀ v, zeroMate i v = zeroMate j v) → i = j := by
    decide +kernel
  intro i j hij
  exact h i j fun v ↦ by rw [← zeroState_mate, hij, zeroState_mate]

/-- Every listed matching is a zero state: for each `t` the alternating walk from `∞` closes up
before it visits every vertex (`results/autgroup-spike.md` §4). -/
theorem isZeroState_zeroState (i : Fin 22) : IsZeroState (factor 6) (zeroState i) := by
  have h : ∀ (i : Fin 22) (t : ZMod (2 * 6 - 1)), Covering.ClosedMiss (zeroMate i) (mateFn t)
      (Covering.altWalk (zeroMate i) (mateFn t) 6 none) := by
    decide +kernel
  exact Covering.isZeroState_of_closedMiss (j := 6) (modulus_odd 6) (h i)

/-- Translations preserve zero states (`results/autgroup-spike.md` §4). -/
theorem isZeroState_shift_smul (b : ZMod (2 * 6 - 1)) {P : PerfectMatching (Vertex 6)}
    (hP : IsZeroState (factor 6) P) : IsZeroState (factor 6) (shift 6 b • P) := by
  intro t h
  apply hP (t - b)
  rw [← ham_smul (shift 6 b), shift_smul_factor, sub_add_cancel]
  exact h

/-- The leaf test of the search: some `F_t ∪ P` is one cycle, or `P` is a listed zero state
(`results/autgroup-spike.md` §4). -/
def listedOrHam (g : Vertex 6 → Vertex 6) : Bool :=
  Covering.hamSome (2 * 6 - 1) 6 g || decide (∃ i : Fin 22, ∀ v, g v = zeroMate i v)

/-- Every perfect matching of `V_6` that pairs `∞` with `0` passes `listedOrHam`. The search
covers `9!! = 945` matchings (`results/autgroup-spike.md` §4). -/
theorem allComplete_listedOrHam :
    Covering.allComplete listedOrHam Covering.Witness.verts6 12
      (Covering.pairUp (fun _ ↦ none) none (some 0)) = true := by
  decide +kernel

/-- A zero state pairing `∞` with `0` is listed (`results/autgroup-spike.md` §4). -/
theorem exists_eq_zeroState_of_mate_none {P : PerfectMatching (Vertex 6)}
    (hP : IsZeroState (factor 6) P) (h0 : P.mate none = some 0) : ∃ i, P = zeroState i := by
  have hs : Covering.PartialSymm (Covering.pairUp (fun _ ↦ none) (none : Vertex 6) (some 0)) := by
    decide +kernel
  have hg := Covering.allComplete_sound listedOrHam Covering.Witness.verts6 (by decide +kernel) P
    12 _ hs ((Covering.extends_none P).pairUp h0) allComplete_listedOrHam
  simp only [listedOrHam, Bool.or_eq_true] at hg
  rcases hg with h | h
  · exact absurd hP (Covering.not_isZeroState_of_hamSome (modulus_odd 6) h)
  · obtain ⟨i, hi⟩ := of_decide_eq_true h
    exact ⟨i, PerfectMatching.ext (Equiv.ext hi)⟩

/-- **The zero states at `m = 6`.** A perfect matching of `V_6` is a zero state iff it is one of
the 22 listed matchings (`results/autgroup-spike.md` §4, run 4). -/
theorem isZeroState_iff {P : PerfectMatching (Vertex 6)} :
    IsZeroState (factor 6) P ↔ ∃ i, P = zeroState i := by
  refine ⟨fun hP ↦ ?_, fun ⟨i, h⟩ ↦ h ▸ isZeroState_zeroState i⟩
  obtain ⟨x, hx⟩ : ∃ x, P.mate none = some x := Option.ne_none_iff_exists'.1 (P.mate_ne none)
  obtain ⟨i, hi⟩ := exists_eq_zeroState_of_mate_none (isZeroState_shift_smul (-x) hP)
    (by rw [smul_mate, shift_inv_none, hx, shift_some, add_neg_cancel])
  have hshift : ∀ (x : ZMod (2 * 6 - 1)) (i : Fin 22),
      ∃ j, shift 6 x • zeroState i = zeroState j := by
    decide +kernel
  obtain ⟨j, hj⟩ := hshift x i
  have h1 : shift 6 x * shift 6 (-x) = 1 := Equiv.ext fun v ↦ by
    rcases v with _ | y
    · rfl
    · exact congrArg some (neg_add_cancel_right y x)
  refine ⟨j, ?_⟩
  rw [← hj, ← hi, smul_smul, h1, one_smul]

/-- The zero-state set at `m = 6` is the set of listed matchings
(`results/autgroup-spike.md` §4). -/
theorem setOf_isZeroState : {P | IsZeroState (factor 6) P} = Set.range zeroState := by
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_range, isZeroState_iff, eq_comm]

/-- **`Z_6 = 22`** (`results/autgroup-spike.md` §4, run 4). -/
theorem zeroCount_six : zeroCount 6 = 22 := by
  have e : Fin 22 ≃ ZeroState 6 :=
    Equiv.ofBijective (fun i ↦ ⟨zeroState i, isZeroState_zeroState i⟩)
      ⟨fun i j h ↦ zeroState_injective (congrArg Subtype.val h),
        fun P ↦ (isZeroState_iff.1 P.2).imp fun i hi ↦ Subtype.ext hi.symm⟩
  rw [zeroCount, ← Fintype.card_congr e, Fintype.card_fin]

/-- `𝔽₁₁` is a field (`results/autgroup-spike.md` §4). -/
local instance : Fact (Nat.Prime (2 * 6 - 1)) :=
  ⟨by decide⟩

/-- The point of `P¹(𝔽₁₁)` with homogeneous coordinates `(N : M)`, `∞` when `M = 0`
(`results/autgroup-spike.md` §4). -/
def ofHomog (N M : ZMod (2 * 6 - 1)) : Vertex 6 :=
  if M = 0 then none else some (N * M⁻¹)

/-- The Möbius map `x ↦ (a x + b)/(c x + d)` of `V_6 = P¹(𝔽₁₁)`, with `∞ ↦ a/c`
(`results/autgroup-spike.md` §4). -/
def moebius (a b c d : ZMod (2 * 6 - 1)) : Vertex 6 → Vertex 6
  | none => ofHomog a c
  | some x => ofHomog (a * x + b) (c * x + d)

/-- Homogeneous coordinates are defined up to a nonzero scalar (`results/autgroup-spike.md` §4). -/
theorem ofHomog_mul {k : ZMod (2 * 6 - 1)} (hk : k ≠ 0) (N M : ZMod (2 * 6 - 1)) :
    ofHomog (k * N) (k * M) = ofHomog N M := by
  unfold ofHomog
  by_cases hM : M = 0
  · simp [hM]
  · rw [ite_eq_right (mul_ne_zero hk hM), ite_eq_right hM, Option.some_inj]
    field_simp

/-- A Möbius map acts linearly on homogeneous coordinates (`results/autgroup-spike.md` §4). -/
theorem moebius_ofHomog (p r s u : ZMod (2 * 6 - 1)) {N M : ZMod (2 * 6 - 1)}
    (h : N ≠ 0 ∨ M ≠ 0) :
    moebius p r s u (ofHomog N M) = ofHomog (p * N + r * M) (s * N + u * M) := by
  by_cases hM : M = 0
  · have hN : N ≠ 0 := h.resolve_right (not_not.2 hM)
    subst hM
    rw [show ofHomog N 0 = none from ite_eq_left rfl, mul_zero, add_zero, mul_zero, add_zero,
      mul_comm p, mul_comm s, ofHomog_mul hN]
    rfl
  · rw [show ofHomog N M = some (N * M⁻¹) from ite_eq_right hM]
    change ofHomog (p * (N * M⁻¹) + r) (s * (N * M⁻¹) + u) = _
    rw [← ofHomog_mul hM]
    congr 1
    · linear_combination (p * N) * mul_inv_cancel₀ hM
    · linear_combination (s * N) * mul_inv_cancel₀ hM

/-- **Composition of Möbius maps is matrix multiplication**, for an invertible inner matrix
(`results/autgroup-spike.md` §4). -/
theorem moebius_moebius (p r s u : ZMod (2 * 6 - 1)) {a b c d : ZMod (2 * 6 - 1)}
    (h : a * d - b * c ≠ 0) (v : Vertex 6) :
    moebius p r s u (moebius a b c d v) =
      moebius (p * a + r * c) (p * b + r * d) (s * a + u * c) (s * b + u * d) v := by
  rcases v with _ | x
  · have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h
      rw [hc.1, hc.2]
      ring
    exact moebius_ofHomog p r s u hac
  · have hx : a * x + b ≠ 0 ∨ c * x + d ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by linear_combination a * hc.2 - c * hc.1)
    change moebius p r s u (ofHomog (a * x + b) (c * x + d)) =
      ofHomog ((p * a + r * c) * x + (p * b + r * d)) ((s * a + u * c) * x + (s * b + u * d))
    rw [moebius_ofHomog p r s u hx]
    congr 1 <;> ring

/-- A Möbius map depends on its matrix only up to a nonzero scalar (`results/autgroup-spike.md`
§4). -/
theorem moebius_mul {k : ZMod (2 * 6 - 1)} (hk : k ≠ 0) (a b c d : ZMod (2 * 6 - 1)) :
    moebius (k * a) (k * b) (k * c) (k * d) = moebius a b c d := by
  funext v
  rcases v with _ | x
  · exact ofHomog_mul hk a c
  · change ofHomog (k * a * x + k * b) (k * c * x + k * d) = ofHomog (a * x + b) (c * x + d)
    rw [← ofHomog_mul hk (a * x + b)]
    congr 1 <;> ring

/-- The translation `T x = x + 1`, fixing `∞` (`results/autgroup-spike.md` §4). -/
def T : Equiv.Perm (Vertex 6) where
  toFun := moebius 1 1 0 1
  invFun := moebius 1 (-1) 0 1
  left_inv := by
    intro v
    revert v
    decide +kernel
  right_inv := by
    intro v
    revert v
    decide +kernel

/-- The involution `S x = -1/x`, swapping `0` and `∞` (`results/autgroup-spike.md` §4). -/
def S : Equiv.Perm (Vertex 6) where
  toFun := moebius 0 (-1) 1 0
  invFun := moebius 0 (-1) 1 0
  left_inv := by
    intro v
    revert v
    decide +kernel
  right_inv := by
    intro v
    revert v
    decide +kernel

/-- The non-square scaling `D x = 2 x`, fixing `∞` (`results/autgroup-spike.md` §4). -/
def D : Equiv.Perm (Vertex 6) where
  toFun := moebius 2 0 0 1
  invFun := moebius 1 0 0 2
  left_inv := by
    intro v
    revert v
    decide +kernel
  right_inv := by
    intro v
    revert v
    decide +kernel

/-- `T` fixes `∞` and sends `x` to `x + 1`, so `T` is the translation `shift 6 1`
(`results/autgroup-spike.md` §4). -/
theorem T_apply : T none = none ∧ (∀ x, T (some x) = some (x + 1)) ∧ T = shift 6 1 := by
  decide +kernel

/-- `S` swaps `∞` and `0` and sends `x ≠ 0` to `-1/x` (`results/autgroup-spike.md` §4). -/
theorem S_apply :
    S none = some 0 ∧ S (some 0) = none ∧ ∀ x, x ≠ 0 → S (some x) = some (-x⁻¹) := by
  decide +kernel

/-- `D` fixes `∞` and sends `x` to `2 x`, and `2` is not a square mod `11`
(`results/autgroup-spike.md` §4). -/
theorem D_apply :
    D none = none ∧ (∀ x, D (some x) = some (2 * x)) ∧ ∀ y : ZMod (2 * 6 - 1), y * y ≠ 2 := by
  decide +kernel

/-- `x ↦ -1/x` is not an automorphism of the round-robin factorization, since it moves `∞`
(`results/autgroup-spike.md` §4 and §5.1). -/
theorem S_not_mem_autGroup : S ∉ autGroup 6 := fun h ↦
  absurd (IsAut.apply_none (by norm_num) h) (by decide +kernel)

/-- The setwise stabiliser `Sym(Z_6)` of the zero states of `V_6` (`results/autgroup-spike.md`
§4). -/
def symZero : Subgroup (Equiv.Perm (Vertex 6)) where
  carrier := {σ | ∀ P, IsZeroState (factor 6) (σ • P) ↔ IsZeroState (factor 6) P}
  mul_mem' {σ τ} hσ hτ P := by
    rw [mul_smul]
    exact (hσ _).trans (hτ P)
  one_mem' P := by rw [one_smul]
  inv_mem' {σ} hσ P := by rw [← hσ (σ⁻¹ • P), smul_inv_smul]

/-- A permutation that maps the listed zero states, and whose inverse maps them, to listed zero
states lies in `Sym(Z_6)` (`results/autgroup-spike.md` §4). -/
theorem mem_symZero_of_forall {σ : Equiv.Perm (Vertex 6)}
    (h : ∀ i, ∃ j, σ • zeroState i = zeroState j) (h' : ∀ i, ∃ j, σ⁻¹ • zeroState i = zeroState j) :
    σ ∈ symZero := by
  intro P
  constructor
  · intro hP
    obtain ⟨i, hi⟩ := isZeroState_iff.1 hP
    obtain ⟨j, hj⟩ := h' i
    rw [← inv_smul_smul σ P, hi, hj]
    exact isZeroState_zeroState j
  · intro hP
    obtain ⟨i, rfl⟩ := isZeroState_iff.1 hP
    obtain ⟨j, hj⟩ := h i
    rw [hj]
    exact isZeroState_zeroState j

/-- `T` maps zero states to zero states (`results/autgroup-spike.md` §4). -/
theorem T_mem_symZero : T ∈ symZero :=
  mem_symZero_of_forall (by decide +kernel) (by decide +kernel)

/-- `S x = -1/x` maps zero states to zero states, although it is not an automorphism of the
round-robin factorization (`results/autgroup-spike.md` §4). -/
theorem S_mem_symZero : S ∈ symZero :=
  mem_symZero_of_forall (by decide +kernel) (by decide +kernel)

/-- `D x = 2 x` maps zero states to zero states (`results/autgroup-spike.md` §4). -/
theorem D_mem_symZero : D ∈ symZero :=
  mem_symZero_of_forall (by decide +kernel) (by decide +kernel)

/-- **`⟨T, S, D⟩` acts on `Z_6`.** The group generated by `T`, `S` and `D` lies in `Sym(Z_6)`
(`results/autgroup-spike.md` §4). -/
theorem closure_le_symZero : Subgroup.closure {T, S, D} ≤ symZero := by
  rw [Subgroup.closure_le]
  rintro σ (rfl | rfl | rfl)
  exacts [T_mem_symZero, S_mem_symZero, D_mem_symZero]

/-- `⟨T, S⟩ ≤ ⟨T, S, D⟩` (`results/autgroup-spike.md` §4). -/
theorem closure_TS_le_TSD : Subgroup.closure {T, S} ≤ Subgroup.closure {T, S, D} :=
  Subgroup.closure_mono fun σ hσ ↦ by
    rcases hσ with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-- **`⟨T, S⟩` acts on `Z_6`**: every element maps zero states to zero states
(`results/autgroup-spike.md` §4). -/
theorem isZeroState_smul {σ : Equiv.Perm (Vertex 6)} (hσ : σ ∈ Subgroup.closure {T, S})
    {P : PerfectMatching (Vertex 6)} (hP : IsZeroState (factor 6) P) :
    IsZeroState (factor 6) (σ • P) :=
  (closure_le_symZero (closure_TS_le_TSD hσ) P).2 hP

/-- `⟨T, S⟩` is not contained in `Aut(𝓕)` (`results/autgroup-spike.md` §4). -/
theorem closure_TS_not_le_autGroup : ¬Subgroup.closure {T, S} ≤ autGroup 6 := fun h ↦
  S_not_mem_autGroup (h (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))

/-- `Sym(Z_6)` acts on the zero states of `V_6` (`results/autgroup-spike.md` §4). -/
instance : MulAction symZero (ZeroState 6) where
  smul σ P := ⟨(σ : Equiv.Perm (Vertex 6)) • P.1, (σ.2 P.1).2 P.2⟩
  one_smul P := Subtype.ext (one_smul _ P.1)
  mul_smul σ τ P := Subtype.ext (mul_smul (σ : Equiv.Perm (Vertex 6)) τ P.1)

/-- The indices of the first `⟨T, S⟩`-orbit, the `T`-orbit of `zeroState 0`
(`results/autgroup-spike.md` §4). -/
def sideA : Finset (Fin 22) :=
  {0, 3, 4, 6, 9, 11, 13, 15, 17, 18, 20}

/-- `σ` maps each listed zero state to a listed zero state on the same side
(`results/autgroup-spike.md` §4). -/
def KeepsSides (σ : Equiv.Perm (Vertex 6)) : Prop :=
  ∀ i, ∃ j, σ • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∈ sideA)

/-- **The two orbits are invariant.** Every element of `⟨T, S⟩` keeps the two sides
(`results/autgroup-spike.md` §4). -/
theorem keepsSides_of_mem_closure {σ : Equiv.Perm (Vertex 6)}
    (hσ : σ ∈ Subgroup.closure {T, S}) : KeepsSides σ := by
  have hmul : ∀ x y, KeepsSides x → KeepsSides y → KeepsSides (x * y) := by
    intro x y hx hy i
    obtain ⟨j, hj, hji⟩ := hy i
    obtain ⟨k, hk, hkj⟩ := hx j
    exact ⟨k, by rw [mul_smul, hj, hk], hkj.trans hji⟩
  have hT : ∀ i, ∃ j, T • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∈ sideA) := by
    decide +kernel
  have hS : ∀ i, ∃ j, S • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∈ sideA) := by
    decide +kernel
  have hT' : ∀ i, ∃ j, T⁻¹ • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∈ sideA) := by
    decide +kernel
  have hS' : ∀ i, ∃ j, S⁻¹ • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∈ sideA) := by
    decide +kernel
  induction hσ using Subgroup.closure_induction_left with
  | one => exact fun i ↦ ⟨i, one_smul _ _, Iff.rfl⟩
  | mul_left x hx y _ ih =>
    rcases hx with rfl | rfl
    · exact hmul _ _ hT ih
    · exact hmul _ _ hS ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | rfl
    · exact hmul _ _ hT' ih
    · exact hmul _ _ hS' ih

/-- The base point of the side of `i` (`results/autgroup-spike.md` §4). -/
def sideBase (i : Fin 22) : Fin 22 :=
  if i ∈ sideA then 0 else 1

/-- **Each side is one orbit.** Listed zero states on the same side are related by an element of
`⟨T, S⟩`. The proof finds a power of `T` (`results/autgroup-spike.md` §4). -/
theorem exists_mem_closure_smul_eq {i j : Fin 22} (h : i ∈ sideA ↔ j ∈ sideA) :
    ∃ σ ∈ Subgroup.closure {T, S}, σ • zeroState i = zeroState j := by
  have hb : ∀ i, ∃ k : Fin 11, T ^ (k : ℕ) • zeroState (sideBase i) = zeroState i := by
    decide +kernel
  have hij : sideBase i = sideBase j := by
    unfold sideBase
    by_cases hi : i ∈ sideA
    · rw [ite_eq_left hi, ite_eq_left (h.1 hi)]
    · rw [ite_eq_right hi, ite_eq_right (mt h.2 hi)]
  obtain ⟨k, hk⟩ := hb i
  obtain ⟨l, hl⟩ := hb j
  have hT : T ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨T ^ (l : ℕ) * (T ^ (k : ℕ))⁻¹,
    mul_mem (pow_mem hT _) (inv_mem (pow_mem hT _)), ?_⟩
  rw [← hk, mul_smul, inv_smul_smul, hij, hl]

/-- **The two orbits have `11` matchings each** (`results/autgroup-spike.md` §4). -/
theorem card_sideA : sideA.card = 11 ∧ sideAᶜ.card = 11 := by
  decide +kernel

/-- **Each orbit is a 1-factorization of `K_12`, edge-disjointness.** Distinct zero states on
the same side share no edge (`results/autgroup-spike.md` §4; Cameron and Korchmáros 1993). -/
theorem mate_ne_of_side : ∀ i j : Fin 22, (i ∈ sideA ↔ j ∈ sideA) → i ≠ j →
    ∀ v, (zeroState i).mate v ≠ (zeroState j).mate v := by
  decide +kernel

/-- **Each orbit is a 1-factorization of `K_12`, covering.** Every edge `uw` of `K_12` lies in a
zero state of each side (`results/autgroup-spike.md` §4; Cameron and Korchmáros 1993). -/
theorem exists_mate_eq_of_side : ∀ u w : Vertex 6, u ≠ w →
    (∃ i ∈ sideA, (zeroState i).mate u = w) ∧ ∃ i ∈ sideAᶜ, (zeroState i).mate u = w := by
  decide +kernel

/-- `D` swaps the two sides (`results/autgroup-spike.md` §4). -/
theorem D_swaps_sides : ∀ i, ∃ j, D • zeroState i = zeroState j ∧ (j ∈ sideA ↔ i ∉ sideA) := by
  decide +kernel

/-- `D ∉ ⟨T, S⟩`, since `D` swaps the two orbits (`results/autgroup-spike.md` §4). -/
theorem D_not_mem_closure_TS : D ∉ Subgroup.closure {T, S} := by
  intro h
  obtain ⟨j, hj, hji⟩ := keepsSides_of_mem_closure h 0
  obtain ⟨k, hk, hki⟩ := D_swaps_sides 0
  rw [hk] at hj
  rw [zeroState_injective hj] at hki
  exact iff_not_self (hji.symm.trans hki)

/-- The parameters `(a, b, c, d)` of Möbius maps (`results/autgroup-spike.md` §4). -/
abbrev Quad :=
  ZMod (2 * 6 - 1) × ZMod (2 * 6 - 1) × ZMod (2 * 6 - 1) × ZMod (2 * 6 - 1)

/-- The Möbius map of `q = (a, b, c, d)` (`results/autgroup-spike.md` §4). -/
def quadMap (q : Quad) : Vertex 6 → Vertex 6 :=
  moebius q.1 q.2.1 q.2.2.1 q.2.2.2

/-- The determinant `a d - b c` of `q = (a, b, c, d)` (`results/autgroup-spike.md` §4). -/
def quadDet (q : Quad) : ZMod (2 * 6 - 1) :=
  q.1 * q.2.2.2 - q.2.1 * q.2.2.1

/-- The matrix product `g q` (`results/autgroup-spike.md` §4). -/
def quadMul (g q : Quad) : Quad :=
  (g.1 * q.1 + g.2.1 * q.2.2.1, g.1 * q.2.1 + g.2.1 * q.2.2.2,
    g.2.2.1 * q.1 + g.2.2.2 * q.2.2.1, g.2.2.1 * q.2.1 + g.2.2.2 * q.2.2.2)

/-- The scalar multiple `k q` (`results/autgroup-spike.md` §4). -/
def quadSmul (k : ZMod (2 * 6 - 1)) (q : Quad) : Quad :=
  (k * q.1, k * q.2.1, k * q.2.2.1, k * q.2.2.2)

/-- The determinant is multiplicative (`results/autgroup-spike.md` §4). -/
theorem quadDet_mul (g q : Quad) : quadDet (quadMul g q) = quadDet g * quadDet q := by
  unfold quadDet quadMul
  ring

/-- `det (k q) = k² det q` (`results/autgroup-spike.md` §4). -/
theorem quadDet_smul (k : ZMod (2 * 6 - 1)) (q : Quad) :
    quadDet (quadSmul k q) = k * k * quadDet q := by
  unfold quadDet quadSmul
  ring

/-- `quadMap (g q) = quadMap g ∘ quadMap q` for invertible `q` (`results/autgroup-spike.md` §4). -/
theorem quadMap_mul (g : Quad) {q : Quad} (hq : quadDet q ≠ 0) (v : Vertex 6) :
    quadMap g (quadMap q v) = quadMap (quadMul g q) v :=
  moebius_moebius _ _ _ _ hq v

/-- `quadMap (k q) = quadMap q` for `k ≠ 0` (`results/autgroup-spike.md` §4). -/
theorem quadMap_smul {k : ZMod (2 * 6 - 1)} (hk : k ≠ 0) (q : Quad) :
    quadMap (quadSmul k q) = quadMap q :=
  moebius_mul hk _ _ _ _

/-- The sign normalisation of `(c, d)`: `1 ≤ c ≤ 5`, or `c = 0` and `1 ≤ d ≤ 5`
(`results/autgroup-spike.md` §4). -/
def SignNormal (c d : ZMod (2 * 6 - 1)) : Prop :=
  (1 ≤ c.val ∧ c.val ≤ 5) ∨ (c = 0 ∧ 1 ≤ d.val ∧ d.val ≤ 5)

/-- `SignNormal` is decidable (`results/autgroup-spike.md` §4). -/
instance (c d : ZMod (2 * 6 - 1)) : Decidable (SignNormal c d) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `q` has determinant `1` and is sign normalised, one representative of each element of
`PSL(2,11)` (`results/autgroup-spike.md` §4). -/
def IsPSL (q : Quad) : Prop :=
  quadDet q = 1 ∧ SignNormal q.2.2.1 q.2.2.2

/-- `IsPSL` is decidable (`results/autgroup-spike.md` §4). -/
instance : DecidablePred IsPSL :=
  fun q ↦ inferInstanceAs (Decidable (quadDet q = 1 ∧ SignNormal q.2.2.1 q.2.2.2))

/-- `q` is invertible with `c = 1`, or `c = 0` and `d = 1`, one representative of each element of
`PGL(2,11)` (`results/autgroup-spike.md` §4). -/
def IsPGL (q : Quad) : Prop :=
  quadDet q ≠ 0 ∧ (q.2.2.1 = 1 ∨ q.2.2.1 = 0 ∧ q.2.2.2 = 1)

/-- `IsPGL` is decidable (`results/autgroup-spike.md` §4). -/
instance : DecidablePred IsPGL :=
  fun q ↦ inferInstanceAs (Decidable (quadDet q ≠ 0 ∧ (q.2.2.1 = 1 ∨ q.2.2.1 = 0 ∧ q.2.2.2 = 1)))

/-- One of `(c, d)` and `(-c, -d)` is sign normalised unless both vanish
(`results/autgroup-spike.md` §4). -/
theorem signNormal_or : ∀ c d : ZMod (2 * 6 - 1), c ≠ 0 ∨ d ≠ 0 →
    SignNormal c d ∨ SignNormal (-c) (-d) := by
  decide +kernel

/-- A determinant-one matrix has a sign-normalised representative with the same Möbius map
(`results/autgroup-spike.md` §4). -/
theorem exists_isPSL {q : Quad} (hq : quadDet q = 1) : ∃ q', IsPSL q' ∧ quadMap q' = quadMap q := by
  obtain ⟨a, b, c, d⟩ := q
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    simp only [quadDet, h.1, h.2, mul_zero, sub_zero] at hq
    exact zero_ne_one hq
  rcases signNormal_or c d hcd with h | h
  · exact ⟨_, ⟨hq, h⟩, rfl⟩
  · refine ⟨quadSmul (-1) (a, b, c, d), ⟨?_, ?_⟩, quadMap_smul (by decide) _⟩
    · rw [quadDet_smul, hq]
      ring
    · simpa [quadSmul] using h

/-- An invertible matrix has a representative with `c = 1`, or `c = 0` and `d = 1`, and the same
Möbius map (`results/autgroup-spike.md` §4). -/
theorem exists_isPGL {q : Quad} (hq : quadDet q ≠ 0) : ∃ q', IsPGL q' ∧ quadMap q' = quadMap q := by
  obtain ⟨a, b, c, d⟩ := q
  by_cases hc : c = 0
  · have hd : d ≠ 0 := fun h ↦ hq (by simp [quadDet, hc, h])
    refine ⟨quadSmul d⁻¹ (a, b, c, d), ⟨?_, Or.inr ⟨?_, ?_⟩⟩, quadMap_smul (inv_ne_zero hd) _⟩
    · rw [quadDet_smul]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hd)) hq
    · simp [quadSmul, hc]
    · exact inv_mul_cancel₀ hd
  · refine ⟨quadSmul c⁻¹ (a, b, c, d), ⟨?_, Or.inl (inv_mul_cancel₀ hc)⟩,
      quadMap_smul (inv_ne_zero hc) _⟩
    rw [quadDet_smul]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hc)) hq

/-- `660` sign-normalised matrices of determinant `1`, the order of `PSL(2,11)`
(`results/autgroup-spike.md` §4). -/
theorem card_isPSL : Fintype.card {q // IsPSL q} = 660 := by
  decide +kernel

/-- `1320` normalised invertible matrices, the order of `PGL(2,11)`
(`results/autgroup-spike.md` §4). -/
theorem card_isPGL : Fintype.card {q // IsPGL q} = 1320 := by
  decide +kernel

/-- If each generator, and each generator's inverse as a power of it, maps the Möbius maps of
`p` into themselves, so does every element of the generated group (`results/autgroup-spike.md`
§4). -/
theorem exists_quad_of_mem_closure {s : Set (Equiv.Perm (Vertex 6))} {p : Quad → Prop}
    (h1 : ∃ q, p q ∧ quadMap q = id)
    (hs : ∀ x ∈ s, ∀ q, p q → ∃ q', p q' ∧ ⇑x ∘ quadMap q = quadMap q')
    (hinv : ∀ x ∈ s, ∃ k : ℕ, x⁻¹ = x ^ k) {g : Equiv.Perm (Vertex 6)}
    (hg : g ∈ Subgroup.closure s) : ∃ q, p q ∧ ⇑g = quadMap q := by
  have hmul : ∀ x ∈ s, ∀ y : Equiv.Perm (Vertex 6), (∃ q, p q ∧ ⇑y = quadMap q) →
      ∃ q, p q ∧ ⇑(x * y) = quadMap q := by
    rintro x hx y ⟨q, hq, hy⟩
    obtain ⟨q', hq', h⟩ := hs x hx q hq
    exact ⟨q', hq', by rw [Equiv.Perm.coe_mul, hy, h]⟩
  have hpow : ∀ x ∈ s, ∀ (k : ℕ) (y : Equiv.Perm (Vertex 6)), (∃ q, p q ∧ ⇑y = quadMap q) →
      ∃ q, p q ∧ ⇑(x ^ k * y) = quadMap q := by
    intro x hx k
    induction k with
    | zero =>
      intro y h
      rwa [pow_zero, one_mul]
    | succ k ih =>
      intro y h
      rw [pow_succ', mul_assoc]
      exact hmul x hx _ (ih y h)
  induction hg using Subgroup.closure_induction_left with
  | one =>
    obtain ⟨q, hq, h⟩ := h1
    exact ⟨q, hq, by rw [h, Equiv.Perm.coe_one]⟩
  | mul_left x hx y _ ih => exact hmul x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, hk⟩ := hinv x hx
    rw [hk]
    exact hpow x hx k y ih

/-- A generator with a determinant-one matrix maps the `PSL(2,11)` Möbius maps into themselves
(`results/autgroup-spike.md` §4). -/
theorem step_isPSL {x : Equiv.Perm (Vertex 6)} {g : Quad} (hg : quadDet g = 1)
    (hx : ⇑x = quadMap g) (q : Quad) (hq : IsPSL q) :
    ∃ q', IsPSL q' ∧ ⇑x ∘ quadMap q = quadMap q' := by
  obtain ⟨q', hq', h⟩ := exists_isPSL (q := quadMul g q) (by rw [quadDet_mul, hg, hq.1, one_mul])
  refine ⟨q', hq', funext fun v ↦ ?_⟩
  rw [Function.comp_apply, hx, h, quadMap_mul g (by rw [hq.1]; exact one_ne_zero)]

/-- A generator with an invertible matrix maps the `PGL(2,11)` Möbius maps into themselves
(`results/autgroup-spike.md` §4). -/
theorem step_isPGL {x : Equiv.Perm (Vertex 6)} {g : Quad} (hg : quadDet g ≠ 0)
    (hx : ⇑x = quadMap g) (q : Quad) (hq : IsPGL q) :
    ∃ q', IsPGL q' ∧ ⇑x ∘ quadMap q = quadMap q' := by
  obtain ⟨q', hq', h⟩ :=
    exists_isPGL (q := quadMul g q) (by rw [quadDet_mul]; exact mul_ne_zero hg hq.1)
  refine ⟨q', hq', funext fun v ↦ ?_⟩
  rw [Function.comp_apply, hx, h, quadMap_mul g hq.1]

/-- An injective map from a subgroup into the normalised matrices of `p` bounds its order, and
an equality of orders makes it onto (`results/autgroup-spike.md` §4). -/
theorem card_le_and_mem {H : Subgroup (Equiv.Perm (Vertex 6))} {p : Quad → Prop}
    [DecidablePred p] (h : ∀ g ∈ H, ∃ q, p q ∧ ⇑g = quadMap q) :
    Nat.card H ≤ Fintype.card {q // p q} ∧
      (Fintype.card {q // p q} ≤ Nat.card H →
        ∀ q, p q → ∀ σ : Equiv.Perm (Vertex 6), ⇑σ = quadMap q → σ ∈ H) := by
  choose f hf using fun g : H ↦ h g g.2
  let F : H → {q // p q} := fun g ↦ ⟨f g, (hf g).1⟩
  have hinj : Function.Injective F := by
    intro g g' hgg
    have e : f g = f g' := congrArg Subtype.val hgg
    have e2 : ⇑(g : Equiv.Perm (Vertex 6)) = ⇑(g' : Equiv.Perm (Vertex 6)) := by
      rw [(hf g).2, (hf g').2, e]
    exact Subtype.ext (Equiv.coe_fn_injective e2)
  refine ⟨?_, fun hc q hq σ hσ ↦ ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective F hinj
  · rw [← Nat.card_eq_fintype_card] at hc
    obtain ⟨g, hg⟩ := (hinj.bijective_of_nat_card_le hc).2 ⟨q, hq⟩
    have e : f g = q := congrArg Subtype.val hg
    have e2 : ⇑σ = ⇑(g : Equiv.Perm (Vertex 6)) := by rw [hσ, (hf g).2, e]
    have hσg : σ = g := Equiv.coe_fn_injective e2
    rw [hσg]
    exact g.2

/-- Every element of `⟨T, S⟩` is a Möbius map of determinant `1`
(`results/autgroup-spike.md` §4). -/
theorem exists_isPSL_of_mem_closure {g : Equiv.Perm (Vertex 6)}
    (hg : g ∈ Subgroup.closure {T, S}) : ∃ q, IsPSL q ∧ ⇑g = quadMap q := by
  refine exists_quad_of_mem_closure ⟨(1, 0, 0, 1), by decide +kernel, ?_⟩ ?_ ?_ hg
  · funext v
    revert v
    decide +kernel
  · rintro x (rfl | rfl)
    · exact step_isPSL (g := (1, 1, 0, 1)) (by decide +kernel) rfl
    · exact step_isPSL (g := (0, -1, 1, 0)) (by decide +kernel) rfl
  · rintro x (rfl | rfl)
    · exact ⟨10, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩

/-- Every element of `⟨T, S, D⟩` is an invertible Möbius map (`results/autgroup-spike.md` §4). -/
theorem exists_isPGL_of_mem_closure {g : Equiv.Perm (Vertex 6)}
    (hg : g ∈ Subgroup.closure {T, S, D}) : ∃ q, IsPGL q ∧ ⇑g = quadMap q := by
  refine exists_quad_of_mem_closure ⟨(1, 0, 0, 1), by decide +kernel, ?_⟩ ?_ ?_ hg
  · funext v
    revert v
    decide +kernel
  · rintro x (rfl | rfl | rfl)
    · exact step_isPGL (g := (1, 1, 0, 1)) (by decide +kernel) rfl
    · exact step_isPGL (g := (0, -1, 1, 0)) (by decide +kernel) rfl
    · exact step_isPGL (g := (2, 0, 0, 1)) (by decide +kernel) rfl
  · rintro x (rfl | rfl | rfl)
    · exact ⟨10, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨9, by decide +kernel⟩

/-- `⟨T, S⟩` is transitive on the 12 points, so `12` divides its order
(`results/autgroup-spike.md` §4). -/
theorem twelve_dvd_card_closure_TS : 12 ∣ Nat.card (Subgroup.closure {T, S}) := by
  have hT : T ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hS : S ∈ Subgroup.closure {T, S} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hw : ∀ x : ZMod (2 * 6 - 1), (T ^ x.val * S) none = some x := by
    decide +kernel
  have horbit : MulAction.orbit (Subgroup.closure {T, S}) (none : Vertex 6) = Set.univ := by
    refine Set.eq_univ_of_forall fun v ↦ ?_
    rcases v with _ | x
    · exact MulAction.mem_orbit_self _
    · exact ⟨⟨T ^ x.val * S, mul_mem (pow_mem hT _) hS⟩, hw x⟩
  have h := (MulAction.stabilizer (Subgroup.closure {T, S}) (none : Vertex 6)).index_dvd_card
  rwa [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_eq_fintype_card,
    card_vertex] at h

/-- **`|⟨T, S⟩| = 660`**, the order of `PSL(2,11)` (`results/autgroup-spike.md` §4, run 5). -/
theorem card_closure_TS : Nat.card (Subgroup.closure {T, S}) = 660 := by
  have hT : T ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hS : S ∈ Subgroup.closure {T, S} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h11 : 11 ∣ Nat.card (Subgroup.closure {T, S}) := by
    have : Fact (Nat.Prime 11) := ⟨by decide⟩
    have h := orderOf_dvd_natCard (⟨T, hT⟩ : Subgroup.closure {T, S})
    rwa [Subgroup.orderOf_mk,
      orderOf_eq_prime (x := T) (p := 11) (by decide +kernel) (by decide +kernel)] at h
  have h5 : 5 ∣ Nat.card (Subgroup.closure {T, S}) := by
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h := orderOf_dvd_natCard
      (⟨S * T ^ 3, mul_mem hS (pow_mem hT 3)⟩ : Subgroup.closure {T, S})
    rwa [Subgroup.orderOf_mk,
      orderOf_eq_prime (x := S * T ^ 3) (p := 5) (by decide +kernel) (by decide +kernel)] at h
  have h660 : 660 ∣ Nat.card (Subgroup.closure {T, S}) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 132 5)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 11)
        twelve_dvd_card_closure_TS h11) h5
  have hle := (card_le_and_mem fun g hg ↦ exists_isPSL_of_mem_closure hg).1
  rw [card_isPSL] at hle
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h660)

/-- **`⟨T, S⟩ = PSL(2,11)`.** A permutation of `V_6 = P¹(𝔽₁₁)` lies in the group generated by
`x ↦ x + 1` and `x ↦ -1/x` iff it is a Möbius map `x ↦ (a x + b)/(c x + d)` with `a d - b c = 1`
(`results/autgroup-spike.md` §4, run 5). -/
theorem mem_closure_TS_iff {σ : Equiv.Perm (Vertex 6)} :
    σ ∈ Subgroup.closure {T, S} ↔ ∃ a b c d, a * d - b * c = 1 ∧ ⇑σ = moebius a b c d := by
  constructor
  · intro hσ
    obtain ⟨q, hq, h⟩ := exists_isPSL_of_mem_closure hσ
    exact ⟨q.1, q.2.1, q.2.2.1, q.2.2.2, hq.1, h⟩
  · rintro ⟨a, b, c, d, hdet, h⟩
    obtain ⟨q, hq, hqm⟩ := exists_isPSL (q := (a, b, c, d)) hdet
    refine (card_le_and_mem fun g hg ↦ exists_isPSL_of_mem_closure hg).2
      (by rw [card_isPSL, card_closure_TS]) q hq σ ?_
    rw [hqm, h]
    rfl

/-- **`|⟨T, S, D⟩| = 1320`**, the order of `PGL(2,11)`, and this group acts on `Z_6` by
`closure_le_symZero` (`results/autgroup-spike.md` §4, run 5). -/
theorem card_closure_TSD : Nat.card (Subgroup.closure {T, S, D}) = 1320 := by
  have hdvd : 660 ∣ Nat.card (Subgroup.closure {T, S, D}) :=
    card_closure_TS ▸ Subgroup.card_dvd_of_le closure_TS_le_TSD
  have hle := (card_le_and_mem fun g hg ↦ exists_isPGL_of_mem_closure hg).1
  rw [card_isPGL] at hle
  have hne : Nat.card (Subgroup.closure {T, S, D}) ≠ 660 := by
    intro h
    apply D_not_mem_closure_TS
    rw [Subgroup.eq_of_le_of_card_ge closure_TS_le_TSD (by rw [h, card_closure_TS])]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hpos : 0 < Nat.card (Subgroup.closure {T, S, D}) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- **`⟨T, S, D⟩ = PGL(2,11)`.** A permutation of `V_6` lies in the group generated by
`x ↦ x + 1`, `x ↦ -1/x` and `x ↦ 2 x` iff it is an invertible Möbius map
(`results/autgroup-spike.md` §4, run 5). -/
theorem mem_closure_TSD_iff {σ : Equiv.Perm (Vertex 6)} :
    σ ∈ Subgroup.closure {T, S, D} ↔ ∃ a b c d, a * d - b * c ≠ 0 ∧ ⇑σ = moebius a b c d := by
  constructor
  · intro hσ
    obtain ⟨q, hq, h⟩ := exists_isPGL_of_mem_closure hσ
    exact ⟨q.1, q.2.1, q.2.2.1, q.2.2.2, hq.1, h⟩
  · rintro ⟨a, b, c, d, hdet, h⟩
    obtain ⟨q, hq, hqm⟩ := exists_isPGL (q := (a, b, c, d)) hdet
    refine (card_le_and_mem fun g hg ↦ exists_isPGL_of_mem_closure hg).2
      (by rw [card_isPGL, card_closure_TSD]) q hq σ ?_
    rw [hqm, h]
    rfl

end PSL211

end RoundRobin.Canonical

end Pairing
