import Repair.HybridPair.CommonEdge
import Repair.FactorCap.ZigZag

/-!
# Contexts of a factor tail and their common edges (Lemma 3 of pair incoherence)

Put `n = 2m - 1`. A union `A` of `F_0`-edges is the vertex set `V(E)` of a set `E` of labels,
label `x` standing for the edge `{x, -x}`. The context of `F_t` is
`context m t A hA = contract F_0 F_t A hA`, the matching of `A` that pairs the two ends of each
path of `F_t ∪ (F_0 ∖ E)`. This is `C_t(E)` of `results/hybrid-pair-incoherence.md` §1.

For a unit `λ` and `2tλ = 1`, the zig-zag position of `v` in `F_0 ∪ F_t` is `zigPos m (λ v)`
(`zigPos_scale_factor_zero`, `zigPos_scale_factor`). A label `x` with `v = valMinAbs (λ x)` sits
at positions `2|v|` (entry) and `2|v| + 1` (exit). For `λ = 1`, `t = 1/2 = m` this is the label
order of the normal form.

* `contract_mate_of_pos` : for any two matchings whose union is a zig-zag in a position function,
  the contraction pairs each exit end with the entry end of the next defect, when there is one.
* `context_mate_of_lt` : the same for the contexts `C_t(E)`.
* `context_mate_neg_eq` (Lemma 3, "if") : if `0 < v < w` or `v < w < 0`, with
  `v = valMinAbs (λ x)`, `w = valMinAbs (λ x')`, and no label of `E` has `|valMinAbs (λ y)|`
  strictly between `|v|` and `|w|`, then `C_t(E)` pairs `-x` with `x'`.
* `context_half_mate_neg_eq` : the normal form `C_{1/2}(E)` pairs `-x` with the next label `x'`.
* `context_common_edge` (Lemma 3) : under both conditions `{-x, x'}` is a common edge of
  `C_{1/2}(E)` and `C_{1/(2λ)}(E)`, and `lattice_of_lt` gives the lattice vector `(h, k)`,
  `h, k ≥ 1`, `2k < n`, `k ≡ λh`.

Source: `results/hybrid-pair-incoherence.md` (organize-archive 0dca0a5), §1 and §2, Lemma 3,
with the zig-zag positions of Lemma P of `factor-tail-L-test.md` (`FactorCap/ZigZag.lean`).
-/

namespace Pairing

namespace PerfectMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The contraction along a zig-zag (`results/hybrid-pair-incoherence.md` §1, contexts). Let `pos`
be injective with values below `N`, let `P` pair each even position `p` with `p + 1` and `Q` each
odd position `p < N - 1` with `p + 1`. If `a ∈ A` has odd position, `u ∈ A` has even position
`pos u > pos a`, and no vertex of `A` lies strictly between them, then `κ_Q` pairs `a` with `u`. -/
theorem contract_mate_of_pos (P Q : PerfectMatching V) (A : Finset V)
    (hA : ∀ v ∈ A, P.mate v ∈ A) (pos : V → ℤ) (hinj : Function.Injective pos) {N : ℤ}
    (hN : ∀ v, pos v < N) (hP : ∀ v, pos v % 2 = 0 → pos (P.mate v) = pos v + 1)
    (hQ : ∀ v, pos v % 2 = 1 → pos v + 1 < N → pos (Q.mate v) = pos v + 1)
    (a : A) (ha : pos a % 2 = 1) {u : V} (hu : u ∈ A) (hu2 : pos u % 2 = 0)
    (hau : pos a < pos u) (hgap : ∀ v ∈ A, pos a < pos v → pos u ≤ pos v) :
    ((contract P Q A hA).mate a : V) = u := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, pos u = pos a + 2 * K + 1 :=
    ⟨((pos u - pos a - 1) / 2).toNat, by omega⟩
  have huN := hN u
  have key : ∀ k : ℕ, k ≤ K → pos (evenPt P Q a k) = pos a + 2 * k ∧
      pos (oddPt P Q a k) = pos a + 2 * k + 1 := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      rw [oddPt, evenPt_zero, hQ _ ha (by omega)]
      simp
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have he : pos (evenPt P Q a (k + 1)) = pos a + 2 * ((k + 1 : ℕ) : ℤ) := by
        rw [evenPt_succ, hP _ (by omega), h2]
        push_cast
        ring
      refine ⟨he, ?_⟩
      rw [oddPt, hQ _ (by rw [he]; omega) (by rw [he]; push_cast at hk ⊢; omega), he]
  have hoK : oddPt P Q a K = u := hinj (by rw [(key K le_rfl).2, hK])
  have hidx : exitIdx P Q A hA a = K := by
    rw [exitIdx, Nat.find_eq_iff]
    refine ⟨hoK ▸ hu, fun k hk hmem ↦ ?_⟩
    have h := hgap _ hmem (by rw [(key k hk.le).2]; omega)
    rw [(key k hk.le).2] at h
    omega
  rw [contract_mate, coe_contractFun, hidx, hoK]

end PerfectMatching

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The context `C_t(E) = κ_{F_t}`, the matching of `A = V(E)` that pairs the ends of each path of
`F_t ∪ (F_0 ∖ E)` (`results/hybrid-pair-incoherence.md` §1). -/
def context (m : ℕ) [NeZero m] (t : ZMod (2 * m - 1)) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A) : PerfectMatching A :=
  contract (factor m 0) (factor m t) A hA

/-- `2tλ = 1` gives `λt = 1/2 = m`. -/
theorem mul_eq_half {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)} (ht : 2 * t * lam = 1) :
    (lam : ZMod (2 * m - 1)) * t = m := by
  obtain ⟨u, hu⟩ := (RoundRobin.isUnit_two (modulus_odd m)).exists_left_inv
  have h2 := two_mul_natCast_self (m := m)
  linear_combination ((m : ZMod (2 * m - 1)) - lam * t) * hu + u * ht - u * h2

/-- `F_0` in the scaled positions `zigPos m (λ v)`: it pairs `2i ↔ 2i + 1`
(`results/hybrid-pair-incoherence.md` §1, Lemma P). -/
theorem zigPos_scale_factor_zero (lam : (ZMod (2 * m - 1))ˣ) (v : Vertex m) :
    zigPos m (scale m lam ((factor m 0).mate v)) =
      if zigPos m (scale m lam v) % 2 = 0 then zigPos m (scale m lam v) + 1
      else zigPos m (scale m lam v) - 1 := by
  rw [scale_mate_factor, mul_zero, zigPos_factor_zero]

/-- `F_t` in the scaled positions `zigPos m (λ v)` for `2tλ = 1`: it pairs `2i + 1 ↔ 2i + 2` and
`2m - 1 ↔ 0` (`results/hybrid-pair-incoherence.md` §1, Lemma P). -/
theorem zigPos_scale_factor (hm : 2 ≤ m) {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)}
    (ht : 2 * t * lam = 1) (v : Vertex m) :
    zigPos m (scale m lam ((factor m t).mate v)) =
      if zigPos m (scale m lam v) = 0 then (2 * m - 1 : ℤ)
      else if zigPos m (scale m lam v) = 2 * m - 1 then 0
      else if zigPos m (scale m lam v) % 2 = 1 then zigPos m (scale m lam v) + 1
      else zigPos m (scale m lam v) - 1 := by
  rw [scale_mate_factor, mul_eq_half ht, zigPos_factor_half hm]

/-- The contexts in zig-zag positions (`results/hybrid-pair-incoherence.md` §1). For `2tλ = 1`,
`C_t(E)` pairs an exit end `a` (odd position) with the entry end `u` (even position) of the next
defect, when no vertex of `A` lies strictly between them in the order `zigPos m (λ ·)`. -/
theorem context_mate_of_lt (hm : 2 ≤ m) {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)}
    (ht : 2 * t * lam = 1) (A : Finset (Vertex m)) (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A)
    {a u : Vertex m} (ha : a ∈ A) (hu : u ∈ A) (ha2 : zigPos m (scale m lam a) % 2 = 1)
    (hu2 : zigPos m (scale m lam u) % 2 = 0)
    (hau : zigPos m (scale m lam a) < zigPos m (scale m lam u))
    (hgap : ∀ v ∈ A, zigPos m (scale m lam a) < zigPos m (scale m lam v) →
      zigPos m (scale m lam u) ≤ zigPos m (scale m lam v)) :
    ((context m t A hA).mate ⟨a, ha⟩ : Vertex m) = u := by
  refine contract_mate_of_pos _ _ A hA (fun v ↦ zigPos m (scale m lam v))
    (zigPos_injective.comp (scale m lam).injective) (N := 2 * m)
    (fun v ↦ by have := zigPos_bounds (m := m) (scale m lam v); omega) (fun v hv ↦ ?_)
    (fun v hv hvN ↦ ?_) ⟨a, ha⟩ ha2 hu hu2 hau hgap
  · simp only [zigPos_scale_factor_zero, hv, ite_true]
  · have := zigPos_bounds (m := m) (scale m lam v)
    rw [zigPos_scale_factor hm ht]
    split_ifs <;> omega

/-- The zig-zag position of a finite vertex `y`: `2k` for `k = valMinAbs y > 0`, and `1 - 2k`
otherwise (`results/hybrid-pair-incoherence.md` §1). -/
theorem zigPos_scale_some (lam : (ZMod (2 * m - 1))ˣ) (y : ZMod (2 * m - 1)) :
    zigPos m (scale m lam (some y)) =
      if 0 < (lam * y).valMinAbs then 2 * (lam * y).valMinAbs
      else 1 - 2 * (lam * y).valMinAbs := by
  rw [scale_some, zigPos_some]

/-- `valMinAbs (-y) = -valMinAbs y` in `ℤ/(2m - 1)`. -/
theorem valMinAbs_neg' (y : ZMod (2 * m - 1)) : (-y).valMinAbs = -y.valMinAbs := by
  have hb := valMinAbs_bounds y
  have hodd : 2 * y.valMinAbs ≠ 2 * m - 1 := by omega
  refine valMinAbs_eq_of_eq (by rw [Int.cast_neg, ZMod.coe_valMinAbs]) (by omega) (by omega)

/-- A vertex of `A` whose position lies strictly between `2|v| + 1` and `2|w|` has a label `z`
with `|v| < |valMinAbs (λ z)| < |w|` (`results/hybrid-pair-incoherence.md`, Lemma 3). -/
theorem gap_of_abs_gap (lam : (ZMod (2 * m - 1))ˣ) (A : Finset (Vertex m)) {v w : ℤ}
    (hv0 : 0 ≤ v) (hgap : ∀ z, some z ∈ A →
      ¬(v < |(lam * z).valMinAbs| ∧ |(lam * z).valMinAbs| < w)) :
    ∀ y ∈ A, 2 * v + 1 < zigPos m (scale m lam y) → 2 * w ≤ zigPos m (scale m lam y) := by
  intro y hy h1
  by_contra h2
  push Not at h2
  rcases y with _ | z
  · simp at h1 h2
    omega
  refine hgap z hy ?_
  rw [zigPos_scale_some] at h1 h2
  split_ifs at h1 h2 with hk
  · rw [abs_of_pos hk]
    omega
  · rw [abs_of_nonpos (not_lt.mp hk)]
    omega

/-- Lemma 3 of `results/hybrid-pair-incoherence.md`, "if" direction, for one context. Let
`2tλ = 1`, `x, x'` labels of `E` (so `x, -x, x' ∈ A`), `v = valMinAbs (λ x)` and
`w = valMinAbs (λ x')`. If `0 < v < w` or `v < w < 0`, and no label `z` of `E` has
`|valMinAbs (λ z)|` strictly between `|v|` and `|w|`, then `C_t(E)` pairs `-x` with `x'`. -/
theorem context_mate_neg_eq (hm : 2 ≤ m) {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)}
    (ht : 2 * t * lam = 1) (A : Finset (Vertex m)) (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A)
    {x x' : ZMod (2 * m - 1)} (hnx : some (-x) ∈ A) (hx' : some x' ∈ A) {v w : ℤ}
    (hv : (lam * x).valMinAbs = v) (hw : (lam * x').valMinAbs = w)
    (hvw : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0))
    (hgap : ∀ z, some z ∈ A →
      ¬(min |v| |w| < |(lam * z).valMinAbs| ∧ |(lam * z).valMinAbs| < max |v| |w|)) :
    ((context m t A hA).mate ⟨some (-x), hnx⟩ : Vertex m) = some x' := by
  have hneg : (lam * -x).valMinAbs = -v := by rw [mul_neg, valMinAbs_neg', hv]
  have pnx := zigPos_scale_some (m := m) lam (-x)
  have px' := zigPos_scale_some (m := m) lam x'
  rw [hneg] at pnx
  rw [hw] at px'
  rcases hvw with ⟨h0, hlt⟩ | ⟨hlt, h0⟩
  · simp only [show ¬0 < -v by omega, show 0 < w by omega, ↓reduceIte] at pnx px'
    refine context_mate_of_lt hm ht A hA hnx hx' (by rw [pnx]; omega) (by rw [px']; omega)
      (by rw [pnx, px']; omega) ?_
    rw [pnx, px']
    rw [show 1 - 2 * -v = 2 * v + 1 by ring]
    refine gap_of_abs_gap lam A h0.le fun z hz h ↦ hgap z hz ?_
    rw [abs_of_pos h0, abs_of_pos (h0.trans hlt), min_eq_left hlt.le, max_eq_right hlt.le]
    simpa using h
  · simp only [show 0 < -v by omega, show ¬0 < w by omega, ↓reduceIte] at pnx px'
    have h := context_mate_of_lt hm ht A hA hx' hnx (by rw [px']; omega) (by rw [pnx]; omega)
      (by rw [pnx, px']; omega) (by
        rw [pnx, px', show 1 - 2 * w = 2 * (-w) + 1 by ring]
        refine gap_of_abs_gap lam A (by omega) fun z hz h ↦ hgap z hz ?_
        rw [abs_of_neg h0, abs_of_neg (hlt.trans h0), min_eq_right (by omega),
          max_eq_left (by omega)]
        exact h)
    have h' : (context m t A hA).mate ⟨some x', hx'⟩ = ⟨some (-x), hnx⟩ := Subtype.ext h
    rw [← h', mate_mate]

/-- The normal form `C_{1/2}(E)` is the label order (`results/hybrid-pair-incoherence.md`,
Theorem 1). For labels `0 < valMinAbs x < valMinAbs x'` of `E` with no label of `E` strictly
between, `C_{1/2}(E)` pairs `-x` with `x'`. -/
theorem context_half_mate_neg_eq (hm : 2 ≤ m) (A : Finset (Vertex m))
    (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A) {x x' : ZMod (2 * m - 1)} (hnx : some (-x) ∈ A)
    (hx' : some x' ∈ A) (h0 : 0 < x.valMinAbs) (hlt : x.valMinAbs < x'.valMinAbs)
    (hgap : ∀ z, some z ∈ A →
      ¬(x.valMinAbs < |z.valMinAbs| ∧ |z.valMinAbs| < x'.valMinAbs)) :
    ((context m m A hA).mate ⟨some (-x), hnx⟩ : Vertex m) = some x' := by
  have ht : 2 * (m : ZMod (2 * m - 1)) * ((1 : (ZMod (2 * m - 1))ˣ) : ZMod (2 * m - 1)) = 1 := by
    rw [Units.val_one, mul_one]
    exact two_mul_natCast_self
  have h1 : ∀ y : ZMod (2 * m - 1),
      (((1 : (ZMod (2 * m - 1))ˣ) : ZMod (2 * m - 1)) * y).valMinAbs = y.valMinAbs := fun y ↦ by
    rw [Units.val_one, one_mul]
  refine context_mate_neg_eq hm ht A hA hnx hx' (h1 x) (h1 x') (Or.inl ⟨h0, hlt⟩)
    fun z hz h ↦ hgap z hz ?_
  rw [h1] at h
  rw [abs_of_pos h0, abs_of_pos (h0.trans hlt), min_eq_left hlt.le,
    max_eq_right hlt.le] at h
  simpa using h

/-- The lattice vector of a common edge (`results/hybrid-pair-incoherence.md`, Lemma 3). With
`h = valMinAbs x' - valMinAbs x ≥ 1` the label gap and `k = w - v` the position gap, `0 < v < w`
or `v < w < 0` gives `(h, k) ∈ L_λ` with `h, k ≥ 1`, `2k < n` and `k ≡ λh (mod n)`. -/
theorem lattice_of_lt {lam : (ZMod (2 * m - 1))ˣ} {x x' : ZMod (2 * m - 1)} {v w : ℤ}
    (hv : (lam * x).valMinAbs = v) (hw : (lam * x').valMinAbs = w)
    (hvw : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0)) (hlab : x.valMinAbs < x'.valMinAbs) :
    1 ≤ x'.valMinAbs - x.valMinAbs ∧ 1 ≤ w - v ∧ 2 * (w - v) < 2 * m - 1 ∧
      ((w - v : ℤ) : ZMod (2 * m - 1)) =
        (lam : ZMod (2 * m - 1)) * ((x'.valMinAbs - x.valMinAbs : ℤ) : ZMod (2 * m - 1)) := by
  have bv := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * x)
  have bw := valMinAbs_bounds ((lam : ZMod (2 * m - 1)) * x')
  rw [hv] at bv
  rw [hw] at bw
  refine ⟨by omega, by omega, by omega, ?_⟩
  push_cast
  simp only [← hv, ← hw, ZMod.coe_valMinAbs]
  ring

/-- Lemma 3 of `results/hybrid-pair-incoherence.md` ("if" direction, and the lattice vector).
Let `2tλ = 1`, and let `x, x'` be consecutive labels of `E` in label order,
`0 < valMinAbs x < valMinAbs x'`. Put `v = valMinAbs (λ x)`, `w = valMinAbs (λ x')`. If
`0 < v < w` or `v < w < 0`, and no label of `E` has `|valMinAbs (λ z)|` strictly between `|v|`
and `|w|`, then `{-x, x'}` is a common edge of `C_{1/2}(E)` and `C_t(E)`, and
`(h, k) = (valMinAbs x' - valMinAbs x, w - v)` lies in `L_λ` with `h, k ≥ 1` and `2k < n`. -/
theorem context_common_edge (hm : 2 ≤ m) {lam : (ZMod (2 * m - 1))ˣ} {t : ZMod (2 * m - 1)}
    (ht : 2 * t * lam = 1) (A : Finset (Vertex m)) (hA : ∀ v ∈ A, (factor m 0).mate v ∈ A)
    {x x' : ZMod (2 * m - 1)} (hnx : some (-x) ∈ A) (hx' : some x' ∈ A)
    (h0 : 0 < x.valMinAbs) (hlt : x.valMinAbs < x'.valMinAbs)
    (hlab : ∀ z, some z ∈ A → ¬(x.valMinAbs < |z.valMinAbs| ∧ |z.valMinAbs| < x'.valMinAbs))
    {v w : ℤ} (hv : (lam * x).valMinAbs = v) (hw : (lam * x').valMinAbs = w)
    (hvw : (0 < v ∧ v < w) ∨ (v < w ∧ w < 0))
    (hgap : ∀ z, some z ∈ A →
      ¬(min |v| |w| < |(lam * z).valMinAbs| ∧ |(lam * z).valMinAbs| < max |v| |w|)) :
    ((context m m A hA).mate ⟨some (-x), hnx⟩ : Vertex m) = some x' ∧
      ((context m t A hA).mate ⟨some (-x), hnx⟩ : Vertex m) = some x' ∧
      1 ≤ x'.valMinAbs - x.valMinAbs ∧ 1 ≤ w - v ∧ 2 * (w - v) < 2 * m - 1 ∧
      ((w - v : ℤ) : ZMod (2 * m - 1)) =
        (lam : ZMod (2 * m - 1)) * ((x'.valMinAbs - x.valMinAbs : ℤ) : ZMod (2 * m - 1)) :=
  ⟨context_half_mate_neg_eq hm A hA hnx hx' h0 hlt hlab,
    context_mate_neg_eq hm ht A hA hnx hx' hv hw hvw hgap, lattice_of_lt hv hw hvw hlt⟩

end RoundRobin.Canonical

end Pairing
