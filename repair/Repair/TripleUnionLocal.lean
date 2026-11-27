import Mathlib.Data.Int.Interval
import Repair.TripleUnion

/-!
# Local universality of the triple unions (Proposition U)

Put `n = 2m - 1`. The triple union `G_r = F_0 ∪ F_1 ∪ F_r` is 3-edge-coloured, colour `0, 1, 2`
being the factor `F_0, F_1, F_r`. Each colour class is a perfect matching, so a walk from a vertex
is determined by its colour word.

* `wordAct μ w x` : the endpoint of the colour word `w` from `x`, for partner maps `μ c`.
  `wordBall μ x H` : the endpoints of words of length at most `H`, the rooted `H`-ball.
  `BallIso μ ν x y H` : a rooted colour-preserving isomorphism between the `H`-balls.
  `ballIso_of_words` : the balls are isomorphic when the same words of length `≤ H + 1` and `≤ H`
  meet on both sides.
* `tripleStep m r c` : the partner map of colour `c` in `G_r`, with `tripleUnion_adj_iff_exists`.
  `mem_wordBall_iff` : its word balls are the graph balls of `G_r`.
* `IsGeneric K r` : no `a + b r = 0` with `|a|, |b| ≤ K` and `(a, b) ≠ 0`. `isGeneric_iff` : for
  `K = 4H` this is the source's `H`-genericity, `r ≢ a/b` for `0 < |b| ≤ 4H`, `|a| ≤ 4H`.
  `card_not_isGeneric_le` : for prime `n` at most `(2K + 1)·2K` residues are not `K`-generic.
* `formalStep` : the formal triple union on `{∞} ∪ ℤ²`, where `(a, b)` stands for `a + b r`.
  `ballIso_formal` : around a formal point of size `K`, the ball of `G_r` is the formal ball when
  `r` is `(2K + 4H + 2)`-generic. `ballIso_none` : for `4H`-generic `r, r'` the `H`-balls of `∞` in
  `G_r` and `G_{r'}` are isomorphic. `ballIso_ev` : for `(8H + 4)`-generic `r, r'` the balls at
  `a + b r` and `a + b r'` are isomorphic, `|a|, |b| ≤ 2H + 1`.
* `honeyStep` : the 3-edge-coloured honeycomb on `ℤ² × {±1}`. `IsDefect K r v` : `v = a + b r` with
  `|a|, |b| ≤ K`, and `card_isDefect_le` : there are at most `(2K + 1)²` such `v`.
  `ballIso_honeycomb` : for `H ≥ 1` and `4H`-generic `r` every vertex `v` that is not
  `(2H + 1)`-defect has the honeycomb `H`-ball, and `ballIso_some_of_not_isDefect` compares two
  such vertices.
* `exists_ballIso_equiv` : **Proposition U**. For `(8H + 4)`-generic `r, r'` there is a bijection
  `ψ` of `V_m` with every `H`-ball of `G_r` at `x` isomorphic to the `H`-ball of `G_{r'}` at `ψ x`.
* The `(2H + 2)` form (Theorem U′). `HexSmall K p` : the hex norm `max(|a|, |b|, |a + b|)` of
  `p = (a, b)` is at most `K`, and `IsHexDefect K r v` : `v = a + b r` with `HexSmall K (a, b)`.
  `ballIso_honeycomb_hex` : for `H`-generic `r` every `v` that is not a hex site of size `H + 1` has
  the honeycomb `H`-ball, and `ballIso_some_of_not_isHexDefect` compares two such vertices.
  `ballIso_formal_hex` : the formal ball at a point of size `K` needs only
  `max(K + H + 1, 2H + 1)`-genericity. `ballIso_none_hex` (`2H + 1`) and `ballIso_ev_hex`
  (`2H + 2`, `|a|, |b| ≤ H + 1`). `exists_ballIso_equiv_hex` : **Proposition U** for
  `(2H + 2)`-generic `r, r'`, and `exists_ballIso_equiv` is a case of it.

Source: `results/k3-workaround-spike.md` §2.2, Proposition U, built on Lemma M (§2.1). The source
assumes `4H`-genericity. Its proof treats the balls at `∞`, at `T_r` and at vertices away from the
`O(H²)` sites `a + b r`. For `∞` and for those vertices this is `ballIso_none` and
`ballIso_honeycomb`, at `4H`. The proof does not treat the balls at the sites `a + b r` themselves,
which include `T_r`. They are matched here through `ballIso_formal`, which
needs the larger constant `8H + 4`, so the global statement is proved for `(8H + 4)`-generic `r`.
That is still all `r` outside `O(H²)` exceptional values.

`results/symmetry-audit-extend.md` §3 (organize-archive bf3fe60) replaces the two coordinate bounds
behind `8H + 4` by hex-norm bounds. Honeycomb positions after `ℓ` steps have hex norm about `ℓ/2`
(Lemma Y), even differences are halved since `2` is a unit, and a walk that has met `∞` is measured
from the colour label where it left `∞` (Lemma W). That gives `exists_ballIso_equiv_hex` at
`(2H + 2)`-genericity, hence the source's `4H` form for `H ≥ 1`. Exact computation in that file
shows that `2H`-genericity fails for `H = 2` to `5`.
-/

namespace Pairing

section ColourWords

variable {X Y : Type*}

/-- The endpoint of the colour word `w` from `x`, for the partner maps `μ c` of a 3-edge-colouring.
The word `c :: w` follows `w` and then the edge of colour `c` (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
def wordAct (μ : Fin 3 → X → X) : List (Fin 3) → X → X
  | [], x => x
  | c :: w, x => μ c (wordAct μ w x)

/-- The empty word stays put (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
@[simp]
theorem wordAct_nil (μ : Fin 3 → X → X) (x : X) : wordAct μ [] x = x :=
  rfl

/-- The word `c :: w` follows `w`, then colour `c` (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
@[simp]
theorem wordAct_cons (μ : Fin 3 → X → X) (c : Fin 3) (w : List (Fin 3)) (x : X) :
    wordAct μ (c :: w) x = μ c (wordAct μ w x) :=
  rfl

/-- A word `w ++ w'` follows `w'`, then `w` (`results/k3-workaround-spike.md`, Proposition U,
after Lemma M). -/
theorem wordAct_append (μ : Fin 3 → X → X) (w w' : List (Fin 3)) (x : X) :
    wordAct μ (w ++ w') x = wordAct μ w (wordAct μ w' x) := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [List.cons_append, wordAct_cons, wordAct_cons, ih]

/-- The rooted `H`-ball of `x₀`, the endpoints of the colour words of length at most `H`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def wordBall (μ : Fin 3 → X → X) (x₀ : X) (H : ℕ) : Set X :=
  {x | ∃ w : List (Fin 3), w.length ≤ H ∧ wordAct μ w x₀ = x}

/-- The root lies in its ball (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem mem_wordBall_self (μ : Fin 3 → X → X) (x₀ : X) (H : ℕ) : x₀ ∈ wordBall μ x₀ H :=
  ⟨[], Nat.zero_le H, rfl⟩

/-- A rooted colour-preserving isomorphism between the `H`-ball of `x₀` for `μ` and the `H`-ball of
`y₀` for `ν`. It sends the root to the root, and two points of the ball are joined by colour `c`
iff their images are (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def BallIso (μ : Fin 3 → X → X) (ν : Fin 3 → Y → Y) (x₀ : X) (y₀ : Y) (H : ℕ) : Prop :=
  ∃ e : wordBall μ x₀ H ≃ wordBall ν y₀ H, (e ⟨x₀, mem_wordBall_self μ x₀ H⟩ : Y) = y₀ ∧
    ∀ (c : Fin 3) (x y : wordBall μ x₀ H), μ c x = y ↔ ν c (e x) = e y

/-- If the same pairs of words, of lengths at most `H + 1` and `H`, meet from `x₀` and from `y₀`,
then the `H`-balls are isomorphic (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem ballIso_of_words {μ : Fin 3 → X → X} {ν : Fin 3 → Y → Y} {x₀ : X} {y₀ : Y} {H : ℕ}
    (h : ∀ w w' : List (Fin 3), w.length ≤ H + 1 → w'.length ≤ H →
      (wordAct μ w x₀ = wordAct μ w' x₀ ↔ wordAct ν w y₀ = wordAct ν w' y₀)) :
    BallIso μ ν x₀ y₀ H := by
  have h' : ∀ w w' : List (Fin 3), w.length ≤ H → w'.length ≤ H →
      (wordAct μ w x₀ = wordAct μ w' x₀ ↔ wordAct ν w y₀ = wordAct ν w' y₀) :=
    fun w w' hw hw' ↦ h w w' (hw.trans (Nat.le_succ H)) hw'
  let F : wordBall μ x₀ H → wordBall ν y₀ H := fun x ↦
    ⟨wordAct ν x.2.choose y₀, x.2.choose, x.2.choose_spec.1, rfl⟩
  let G : wordBall ν y₀ H → wordBall μ x₀ H := fun y ↦
    ⟨wordAct μ y.2.choose x₀, y.2.choose, y.2.choose_spec.1, rfl⟩
  have hF : ∀ (x : wordBall μ x₀ H) (w : List (Fin 3)), w.length ≤ H → wordAct μ w x₀ = x →
      (F x : Y) = wordAct ν w y₀ := fun x w hw hwx ↦
    (h' _ _ x.2.choose_spec.1 hw).1 (x.2.choose_spec.2.trans hwx.symm)
  have hG : ∀ (y : wordBall ν y₀ H) (w : List (Fin 3)), w.length ≤ H → wordAct ν w y₀ = y →
      (G y : X) = wordAct μ w x₀ := fun y w hw hwy ↦
    (h' _ _ y.2.choose_spec.1 hw).2 (y.2.choose_spec.2.trans hwy.symm)
  refine ⟨⟨F, G, fun x ↦ ?_, fun y ↦ ?_⟩, hF _ [] (Nat.zero_le H) rfl, fun c x y ↦ ?_⟩
  · obtain ⟨w, hw, hwx⟩ := x.2
    exact Subtype.ext ((hG (F x) w hw (hF x w hw hwx).symm).trans hwx)
  · obtain ⟨w, hw, hwy⟩ := y.2
    exact Subtype.ext ((hF (G y) w hw (hG y w hw hwy).symm).trans hwy)
  · obtain ⟨w, hw, hwx⟩ := x.2
    obtain ⟨w', hw', hwy⟩ := y.2
    change μ c x = y ↔ ν c (F x : Y) = (F y : Y)
    rw [hF x w hw hwx, hF y w' hw' hwy, ← hwx, ← hwy]
    exact h (c :: w) w' (by simpa using hw) hw'

/-- If `φ` commutes with the colour steps at every point reached by a word of length at most `H`,
it carries the words of length at most `H + 1` from `x₀` to those from `φ x₀`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem wordAct_map {μ : Fin 3 → X → X} {ν : Fin 3 → Y → Y} (φ : X → Y) {x₀ : X} {H : ℕ}
    (hcomm : ∀ w : List (Fin 3), w.length ≤ H →
      ∀ c, φ (μ c (wordAct μ w x₀)) = ν c (φ (wordAct μ w x₀))) :
    ∀ w : List (Fin 3), w.length ≤ H + 1 → φ (wordAct μ w x₀) = wordAct ν w (φ x₀)
  | [], _ => rfl
  | c :: w, hw => by
    have hw' : w.length ≤ H := by simpa using hw
    rw [wordAct_cons, wordAct_cons, hcomm w hw' c,
      wordAct_map φ hcomm w (hw'.trans (Nat.le_succ H))]

/-- If `φ` commutes with the colour steps along words of length at most `H` and separates the
endpoints of words of lengths at most `H + 1` and `H`, the same such words meet from `x₀` and from
`φ x₀` (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem words_iff_of_map {μ : Fin 3 → X → X} {ν : Fin 3 → Y → Y} (φ : X → Y) {x₀ : X} {H : ℕ}
    (hcomm : ∀ w : List (Fin 3), w.length ≤ H →
      ∀ c, φ (μ c (wordAct μ w x₀)) = ν c (φ (wordAct μ w x₀)))
    (hinj : ∀ w w' : List (Fin 3), w.length ≤ H + 1 → w'.length ≤ H →
      φ (wordAct μ w x₀) = φ (wordAct μ w' x₀) → wordAct μ w x₀ = wordAct μ w' x₀)
    (w w' : List (Fin 3)) (hw : w.length ≤ H + 1) (hw' : w'.length ≤ H) :
    wordAct μ w x₀ = wordAct μ w' x₀ ↔ wordAct ν w (φ x₀) = wordAct ν w' (φ x₀) := by
  rw [← wordAct_map φ hcomm w hw, ← wordAct_map φ hcomm w' (hw'.trans (Nat.le_succ H))]
  exact ⟨fun h ↦ congrArg φ h, hinj w w' hw hw'⟩

end ColourWords

namespace RoundRobin.Canonical

open PerfectMatching

variable {m : ℕ} [NeZero m]

/-! ### The colour steps of `G_r` -/

/-- The labels `0, 1, r` of the colours `0, 1, 2` of `G_r` (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
def colour (r : ZMod (2 * m - 1)) : Fin 3 → ZMod (2 * m - 1) :=
  ![0, 1, r]

/-- The partner map of colour `c` in `G_r`, the mate in `F_0`, `F_1` or `F_r`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def tripleStep (m : ℕ) [NeZero m] (r : ZMod (2 * m - 1)) (c : Fin 3) : Vertex m → Vertex m :=
  (factor m (colour r c)).mate

/-- Colour `c` joins `∞` to its label (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem tripleStep_none (r : ZMod (2 * m - 1)) (c : Fin 3) :
    tripleStep m r c none = some (colour r c) :=
  rfl

/-- Colour `c` joins `x` to `2 t - x`, or to `∞` when `x = t`, where `t` is its label
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem tripleStep_some (r : ZMod (2 * m - 1)) (c : Fin 3) (x : ZMod (2 * m - 1)) :
    tripleStep m r c (some x) =
      if x = colour r c then none else some (2 * colour r c - x) :=
  rfl

/-- The edges of `G_r` are the colour steps, so `wordBall (tripleStep m r) x H` is the ball of
radius `H` around `x` in `G_r` (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem tripleUnion_adj_iff_exists {r : ZMod (2 * m - 1)} {x y : Vertex m} :
    (tripleUnion m r).Adj x y ↔ ∃ c, tripleStep m r c x = y := by
  simp only [tripleUnion, SimpleGraph.sup_adj, toGraph_adj, tripleStep]
  constructor
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  · rintro ⟨c, h⟩
    fin_cases c
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]

/-- `wordBall (tripleStep m r) x H` is the ball of radius `H` around `x` in `G_r`, the endpoints of
the walks of length at most `H` (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem mem_wordBall_iff {r : ZMod (2 * m - 1)} {x y : Vertex m} {H : ℕ} :
    y ∈ wordBall (tripleStep m r) x H ↔ ∃ p : (tripleUnion m r).Walk x y, p.length ≤ H := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have key : ∀ w : List (Fin 3),
        ∃ p : (tripleUnion m r).Walk x (wordAct (tripleStep m r) w x), p.length = w.length := by
      intro w
      induction w with
      | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | cons c w ih =>
        obtain ⟨p, hp⟩ := ih
        exact ⟨p.concat (tripleUnion_adj_iff_exists.2 ⟨c, rfl⟩), by
          rw [SimpleGraph.Walk.length_concat, hp, List.length_cons]⟩
    obtain ⟨p, hp⟩ := key w
    exact ⟨p, hp ▸ hw⟩
  · rintro ⟨p, hp⟩
    have key : ∀ {a b : Vertex m} (p : (tripleUnion m r).Walk a b),
        ∃ w : List (Fin 3), w.length = p.length ∧ wordAct (tripleStep m r) w a = b := by
      intro a b p
      induction p with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons h p ih =>
        obtain ⟨c, hc⟩ := tripleUnion_adj_iff_exists.1 h
        obtain ⟨w, hw, hwe⟩ := ih
        exact ⟨w ++ [c], by simp [hw], by rw [wordAct_append, wordAct_cons, wordAct_nil, hc, hwe]⟩
    obtain ⟨w, hw, hwe⟩ := key p
    exact ⟨w, hw ▸ hp, hwe⟩

/-! ### Genericity -/

/-- `r` is `K`-generic when `a + b r = 0` with `|a|, |b| ≤ K` forces `a = b = 0`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def IsGeneric (K : ℕ) (r : ZMod (2 * m - 1)) : Prop :=
  ∀ a b : ℤ, |a| ≤ K → |b| ≤ K → (a : ZMod (2 * m - 1)) + b * r = 0 → a = 0 ∧ b = 0

omit [NeZero m] in
/-- Genericity is monotone in the bound (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem IsGeneric.mono {K K' : ℕ} {r : ZMod (2 * m - 1)} (h : IsGeneric K' r) (hK : K ≤ K') :
    IsGeneric K r := fun a b ha hb ↦
  h a b (ha.trans (by exact_mod_cast hK)) (hb.trans (by exact_mod_cast hK))

/-- `IsGeneric (4H) r` is the `H`-genericity of the source: `r ≢ a/b`, read as `b r ≠ a`, for all
`0 < |b| ≤ 4H` and `|a| ≤ 4H` (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem isGeneric_iff {K : ℕ} {r : ZMod (2 * m - 1)} :
    IsGeneric K r ↔ ∀ a b : ℤ, 0 < |b| → |b| ≤ K → |a| ≤ K →
      (b : ZMod (2 * m - 1)) * r ≠ a := by
  constructor
  · intro h a b hb0 hb ha hab
    have := (h (-a) b (by rwa [abs_neg]) hb (by push_cast; linear_combination hab)).2
    simp [this] at hb0
  · intro h a b ha hb hab
    by_cases hb0 : b = 0
    · subst hb0
      refine ⟨?_, rfl⟩
      by_contra ha0
      have hdvd : ((2 * m - 1 : ℕ) : ℤ) ∣ |a| :=
        (dvd_abs _ _).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd a _).1 (by simpa using hab))
      have hn : ((2 * m - 1 : ℕ) : ℤ) ≤ |a| := Int.le_of_dvd (abs_pos.2 ha0) hdvd
      have hval : (r.val : ℤ) < ((2 * m - 1 : ℕ) : ℤ) := by exact_mod_cast ZMod.val_lt r
      refine h r.val 1 (by norm_num) (by rw [abs_one]; omega)
        (by rw [abs_of_nonneg (by positivity)]; omega) ?_
      simp
    · refine absurd ?_ (h (-a) b (abs_pos.2 hb0) hb (by rwa [abs_neg]))
      push_cast
      linear_combination hab

open Classical in
/-- For prime `n`, at most `(2K + 1)·2K` residues are not `K`-generic, so at most `(8H + 1)·8H`
are not `H`-generic in the sense of the source (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
theorem card_not_isGeneric_le (hp : (2 * m - 1).Prime) (K : ℕ) :
    (Finset.univ.filter fun r : ZMod (2 * m - 1) ↦ ¬IsGeneric K r).card ≤ (2 * K + 1) * (2 * K) := by
  classical
  have : Fact (2 * m - 1).Prime := ⟨hp⟩
  set I : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hI
  have hIcard : I.card = 2 * K + 1 := by
    rw [hI, Int.card_Icc]
    omega
  have hmemI : ∀ a : ℤ, a ∈ I ↔ |a| ≤ K := fun a ↦ by rw [hI, Finset.mem_Icc, abs_le]
  have hsub : (Finset.univ.filter fun r : ZMod (2 * m - 1) ↦ ¬IsGeneric K r) ⊆
      (I ×ˢ I.erase 0).image fun ab ↦ (ab.1 : ZMod (2 * m - 1)) / ab.2 := by
    intro r hr
    rw [Finset.mem_filter, isGeneric_iff] at hr
    push Not at hr
    obtain ⟨-, a, b, hb0, hb, ha, hab⟩ := hr
    rw [Finset.mem_image]
    by_cases hbz : (b : ZMod (2 * m - 1)) = 0
    · have hdvd : ((2 * m - 1 : ℕ) : ℤ) ∣ |b| :=
        (dvd_abs _ _).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd b _).1 hbz)
      have hn : ((2 * m - 1 : ℕ) : ℤ) ≤ |b| := Int.le_of_dvd hb0 hdvd
      have hval : (r.val : ℤ) < ((2 * m - 1 : ℕ) : ℤ) := by exact_mod_cast ZMod.val_lt r
      refine ⟨(r.val, 1), Finset.mem_product.2 ⟨(hmemI _).2 ?_, Finset.mem_erase.2
        ⟨one_ne_zero, (hmemI _).2 (by rw [abs_one]; omega)⟩⟩, ?_⟩
      · rw [abs_of_nonneg (by positivity)]
        omega
      · show ((r.val : ℤ) : ZMod (2 * m - 1)) / ((1 : ℤ) : ZMod (2 * m - 1)) = r
        rw [Int.cast_one, div_one, Int.cast_natCast, ZMod.natCast_zmod_val]
    · refine ⟨(a, b), Finset.mem_product.2 ⟨(hmemI _).2 ha, Finset.mem_erase.2
        ⟨fun h ↦ hbz (by rw [show b = 0 from h, Int.cast_zero]), (hmemI _).2 hb⟩⟩, ?_⟩
      rw [div_eq_iff hbz, ← hab]
      exact mul_comm _ _
  calc (Finset.univ.filter fun r : ZMod (2 * m - 1) ↦ ¬IsGeneric K r).card
      ≤ ((I ×ˢ I.erase 0).image fun ab ↦ (ab.1 : ZMod (2 * m - 1)) / ab.2).card :=
        Finset.card_le_card hsub
    _ ≤ (I ×ˢ I.erase 0).card := Finset.card_image_le
    _ = (2 * K + 1) * (2 * K) := by
        rw [Finset.card_product, Finset.card_erase_of_mem ((hmemI 0).2 (by simp)), hIcard,
          Nat.add_sub_cancel]

/-! ### The formal triple union and the balls at `∞` and at the sites `a + b r` -/

/-- The formal labels `(0, 0)`, `(1, 0)` and `(0, 1)` of the colours `0, 1, 2`, where `(a, b)`
stands for `a + b r` (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def fcol : Fin 3 → ℤ × ℤ :=
  ![(0, 0), (1, 0), (0, 1)]

/-- The formal triple union on `{∞} ∪ ℤ²`. Colour `c` joins `∞` to `fcol c` and `p ≠ fcol c` to
`2 fcol c - p` (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def formalStep (c : Fin 3) : Option (ℤ × ℤ) → Option (ℤ × ℤ)
  | none => some (fcol c)
  | some p => if p = fcol c then none else some (2 * (fcol c).1 - p.1, 2 * (fcol c).2 - p.2)

/-- The evaluation `(a, b) ↦ a + b r` (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
def ev (r : ZMod (2 * m - 1)) (p : ℤ × ℤ) : ZMod (2 * m - 1) :=
  p.1 + p.2 * r

omit [NeZero m] in
/-- The formal labels evaluate to the labels (`results/k3-workaround-spike.md`, Proposition U,
after Lemma M). -/
theorem ev_fcol (r : ZMod (2 * m - 1)) (c : Fin 3) : ev r (fcol c) = colour r c := by
  fin_cases c <;> simp [ev, fcol, colour]

/-- Both coordinates of `p` have size at most `K` (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
def Small (K : ℤ) (p : ℤ × ℤ) : Prop :=
  |p.1| ≤ K ∧ |p.2| ≤ K

private theorem small_iff {K : ℤ} {p : ℤ × ℤ} :
    Small K p ↔ -K ≤ p.1 ∧ p.1 ≤ K ∧ -K ≤ p.2 ∧ p.2 ≤ K := by
  simp only [Small, abs_le, and_assoc]

private theorem small_mono {K K' : ℤ} {p : ℤ × ℤ} (h : Small K p) (hK : K ≤ K') : Small K' p :=
  ⟨h.1.trans hK, h.2.trans hK⟩

private theorem fcol_small (c : Fin 3) : Small 1 (fcol c) := by
  fin_cases c <;> simp [Small, fcol]

/-- `p = (a, b)` has hex norm `max(|a|, |b|, |a + b|)` at most `K`. The hex norm is the word metric
of the steps `±(1, 0)`, `±(0, 1)` and `±(1, -1)`, the moves of the honeycomb over two steps
(`results/symmetry-audit-extend.md` §3.1, organize-archive bf3fe60). -/
def HexSmall (K : ℤ) (p : ℤ × ℤ) : Prop :=
  |p.1| ≤ K ∧ |p.2| ≤ K ∧ |p.1 + p.2| ≤ K

private theorem hexSmall_iff {K : ℤ} {p : ℤ × ℤ} :
    HexSmall K p ↔ -K ≤ p.1 ∧ p.1 ≤ K ∧ -K ≤ p.2 ∧ p.2 ≤ K ∧ -K ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ K := by
  simp only [HexSmall, abs_le, and_assoc]

private theorem fcol_corner (c : Fin 3) :
    0 ≤ (fcol c).1 ∧ 0 ≤ (fcol c).2 ∧ (fcol c).1 + (fcol c).2 ≤ 1 := by
  fin_cases c <;> simp [fcol]

omit [NeZero m] in
/-- For `G`-generic `r`, evaluation is injective on points whose sizes add up to at most `G`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem ev_injOn {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r) {K K' : ℤ}
    {p q : ℤ × ℤ} (hp : Small K p) (hq : Small K' q) (hK : K + K' ≤ G) (h : ev r p = ev r q) :
    p = q := by
  rw [small_iff] at hp hq
  obtain ⟨h1, h2⟩ := hr (p.1 - q.1) (p.2 - q.2) (abs_le.2 ⟨by omega, by omega⟩)
    (abs_le.2 ⟨by omega, by omega⟩) (by simp only [ev] at h; push_cast; linear_combination h)
  exact Prod.ext (by omega) (by omega)

private theorem formal_small {K : ℤ} (hK : -1 ≤ K) {x₀ : Option (ℤ × ℤ)}
    (hx₀ : ∀ p, x₀ = some p → Small K p) :
    ∀ (w : List (Fin 3)) (p : ℤ × ℤ), wordAct formalStep w x₀ = some p →
      Small (K + 2 * w.length) p
  | [], p, h => by simpa using hx₀ p h
  | c :: w, p, h => by
    have hc := small_iff.1 (fcol_small c)
    rw [wordAct_cons] at h
    rw [List.length_cons, small_iff]
    push_cast
    rcases hw : wordAct formalStep w x₀ with _ | q
    · rw [hw] at h
      simp only [formalStep, Option.some_inj] at h
      subst h
      omega
    · have hq := small_iff.1 (formal_small hK hx₀ w q hw)
      rw [hw] at h
      by_cases hqc : q = fcol c
      · simp [formalStep, hqc] at h
      · simp only [formalStep, hqc, ↓reduceIte, Option.some_inj] at h
        rw [← h]
        dsimp only
        omega

private theorem formalStep_none_map (r : ZMod (2 * m - 1)) (c : Fin 3) :
    Option.map (ev r) (formalStep c none) = tripleStep m r c (Option.map (ev r) none) := by
  simp [formalStep, tripleStep_none, ev_fcol]

private theorem formalStep_some_map {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r)
    {K : ℤ} {p : ℤ × ℤ} (hp : Small K p) (hK : K + 1 ≤ G) (c : Fin 3) :
    Option.map (ev r) (formalStep c (some p)) = tripleStep m r c (Option.map (ev r) (some p)) := by
  rw [Option.map_some, tripleStep_some]
  by_cases hpc : p = fcol c
  · subst hpc
    simp [formalStep, ev_fcol]
  · have hne : ev r p ≠ colour r c := fun h ↦
      hpc (ev_injOn hr hp (fcol_small c) hK (h.trans (ev_fcol r c).symm))
    simp only [formalStep, hpc, hne, ↓reduceIte, Option.map_some, Option.some_inj]
    rw [← ev_fcol]
    simp only [ev]
    push_cast
    ring

private theorem formal_words_iff {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r) {K : ℤ}
    (hK : -1 ≤ K) {x₀ : Option (ℤ × ℤ)} (hx₀ : ∀ p, x₀ = some p → Small K p) {H : ℕ}
    (hG : 2 * K + 4 * H + 2 ≤ G) (w w' : List (Fin 3)) (hw : w.length ≤ H + 1)
    (hw' : w'.length ≤ H) :
    wordAct formalStep w x₀ = wordAct formalStep w' x₀ ↔
      wordAct (tripleStep m r) w (Option.map (ev r) x₀) =
        wordAct (tripleStep m r) w' (Option.map (ev r) x₀) := by
  refine words_iff_of_map (Option.map (ev r)) (fun u hu c ↦ ?_) (fun u u' hu hu' h ↦ ?_) w w'
    hw hw'
  · rcases hx : wordAct formalStep u x₀ with _ | p
    · exact formalStep_none_map r c
    · have hp := formal_small hK hx₀ u p hx
      have hu' : (u.length : ℤ) ≤ H := by exact_mod_cast hu
      exact formalStep_some_map hr hp (by omega) c
  · rcases hx : wordAct formalStep u x₀ with _ | p <;>
      rcases hx' : wordAct formalStep u' x₀ with _ | p' <;> rw [hx, hx'] at h
    · simp at h
    · simp at h
    · have hp := formal_small hK hx₀ u p hx
      have hp' := formal_small hK hx₀ u' p' hx'
      have h1 : (u.length : ℤ) ≤ H + 1 := by exact_mod_cast hu
      have h2 : (u'.length : ℤ) ≤ H := by exact_mod_cast hu'
      rw [Option.map_some, Option.map_some, Option.some_inj] at h
      rw [ev_injOn hr (small_mono hp (K' := K + 2 * (H + 1)) (by omega))
        (small_mono hp' (K' := K + 2 * H) (by omega)) (by omega) h]

/-- **Proposition U**, formal form. Let `x₀` be `∞` (`K = -1`) or a formal point of size at most
`K`. If `r` is `(2K + 4H + 2)`-generic, the `H`-ball of `G_r` at the evaluation of `x₀` is the
formal `H`-ball at `x₀`, which does not depend on `r` (`results/k3-workaround-spike.md`,
Proposition U, after Lemma M). -/
theorem ballIso_formal {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r) {K : ℤ} (hK : -1 ≤ K)
    {x₀ : Option (ℤ × ℤ)} (hx₀ : ∀ p, x₀ = some p → Small K p) {H : ℕ}
    (hG : 2 * K + 4 * H + 2 ≤ G) :
    BallIso formalStep (tripleStep m r) x₀ (Option.map (ev r) x₀) H :=
  ballIso_of_words (formal_words_iff hr hK hx₀ hG)

/-- **Proposition U** at `∞`. For `4H`-generic `r` and `r'`, the `H`-balls of `∞` in `G_r` and
`G_{r'}` are isomorphic, colour by colour (`results/k3-workaround-spike.md`, Proposition U, after
Lemma M). -/
theorem ballIso_none {H : ℕ} {r r' : ZMod (2 * m - 1)} (hr : IsGeneric (4 * H) r)
    (hr' : IsGeneric (4 * H) r') : BallIso (tripleStep m r) (tripleStep m r') none none H :=
  ballIso_of_words fun w w' hw hw' ↦
    (formal_words_iff (x₀ := none) hr (le_refl (-1)) (fun _ h ↦ by cases h)
      (by push_cast; omega) w w' hw hw').symm.trans
    (formal_words_iff (x₀ := none) hr' (le_refl (-1)) (fun _ h ↦ by cases h)
      (by push_cast; omega) w w' hw hw')

/-- **Proposition U** at the sites `a + b r`. For `(8H + 4)`-generic `r` and `r'` and
`|a|, |b| ≤ 2H + 1`, the `H`-ball of `a + b r` in `G_r` is isomorphic to the `H`-ball of `a + b r'`
in `G_{r'}` (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
theorem ballIso_ev {H : ℕ} {r r' : ZMod (2 * m - 1)} (hr : IsGeneric (8 * H + 4) r)
    (hr' : IsGeneric (8 * H + 4) r') {p : ℤ × ℤ} (hp : Small (2 * H + 1) p) :
    BallIso (tripleStep m r) (tripleStep m r') (some (ev r p)) (some (ev r' p)) H :=
  ballIso_of_words fun w w' hw hw' ↦
    (formal_words_iff (x₀ := some p) hr (by omega) (fun _ h ↦ Option.some_inj.1 h ▸ hp)
      (by push_cast; omega) w w' hw hw').symm.trans
    (formal_words_iff (x₀ := some p) hr' (by omega) (fun _ h ↦ Option.some_inj.1 h ▸ hp)
      (by push_cast; omega) w w' hw hw')

/-! ### The honeycomb -/

/-- The 3-edge-coloured honeycomb on `ℤ² × {±1}`. The point `(s₁, s₂, γ)` stands for
`γ v + 2 s₁ + 2 s₂ r`, and colour `c` sends it to `(c₁ - s₁, c₂ - s₂, -γ)`, where `fcol c = (c₁, c₂)`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def honeyStep (c : Fin 3) (q : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  ((fcol c).1 - q.1, (fcol c).2 - q.2.1, -q.2.2)

/-- The evaluation `(s₁, s₂, γ) ↦ γ v + 2 s₁ + 2 s₂ r` of the honeycomb into `G_r`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def honeyEv (r v : ZMod (2 * m - 1)) (q : ℤ × ℤ × ℤ) : Vertex m :=
  some (q.2.2 * v + 2 * q.1 + 2 * q.2.1 * r)

/-- `v` is a `K`-defect site of `G_r`, `v = a + b r` with `|a|, |b| ≤ K`
(`results/k3-workaround-spike.md`, Proposition U, after Lemma M). -/
def IsDefect (K : ℕ) (r v : ZMod (2 * m - 1)) : Prop :=
  ∃ a b : ℤ, |a| ≤ K ∧ |b| ≤ K ∧ v = a + b * r

open Classical in
/-- There are at most `(2K + 1)²` defect sites (`results/k3-workaround-spike.md`, Proposition U,
after Lemma M). -/
theorem card_isDefect_le (K : ℕ) (r : ZMod (2 * m - 1)) :
    (Finset.univ.filter (IsDefect K r)).card ≤ (2 * K + 1) ^ 2 := by
  set I : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hI
  have hIcard : I.card = 2 * K + 1 := by
    rw [hI, Int.card_Icc]
    omega
  have hsub : Finset.univ.filter (IsDefect K r) ⊆ (I ×ˢ I).image (ev r) := by
    intro v hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (Finset.mem_filter.1 hv).2
    exact Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2
      ⟨by rw [hI, Finset.mem_Icc]; exact abs_le.1 ha, by rw [hI, Finset.mem_Icc]; exact abs_le.1 hb⟩,
      rfl⟩
  calc (Finset.univ.filter (IsDefect K r)).card ≤ ((I ×ˢ I).image (ev r)).card :=
        Finset.card_le_card hsub
    _ ≤ (I ×ˢ I).card := Finset.card_image_le
    _ = (2 * K + 1) ^ 2 := by rw [Finset.card_product, hIcard, sq]

omit [NeZero m] in
private theorem isDefect_mono {K K' : ℕ} {r v : ZMod (2 * m - 1)} (h : IsDefect K r v)
    (hK : K ≤ K') : IsDefect K' r v := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact ⟨a, b, ha.trans (by exact_mod_cast hK), hb.trans (by exact_mod_cast hK), rfl⟩

/-- `v` is a hex site of size `K`, `v = a + b r` with `max(|a|, |b|, |a + b|) ≤ K`
(`results/symmetry-audit-extend.md` §3.1, organize-archive bf3fe60). -/
def IsHexDefect (K : ℕ) (r v : ZMod (2 * m - 1)) : Prop :=
  ∃ a b : ℤ, HexSmall K (a, b) ∧ v = a + b * r

omit [NeZero m] in
/-- A hex site of size `K` is a `K`-defect site (`results/symmetry-audit-extend.md` §3.1,
organize-archive bf3fe60). -/
theorem IsHexDefect.isDefect {K : ℕ} {r v : ZMod (2 * m - 1)} (h : IsHexDefect K r v) :
    IsDefect K r v := by
  obtain ⟨a, b, hab, rfl⟩ := h
  rw [hexSmall_iff] at hab
  exact ⟨a, b, abs_le.2 ⟨hab.1, hab.2.1⟩, abs_le.2 ⟨hab.2.2.1, hab.2.2.2.1⟩, rfl⟩

private def HoneyPos (ℓ : ℤ) (q : ℤ × ℤ × ℤ) : Prop :=
  (q.2.2 = 1 ∧ HexSmall ℓ (2 * q.1, 2 * q.2.1)) ∨
    (q.2.2 = -1 ∧ ∃ e : ℤ × ℤ, (0 ≤ e.1 ∧ 0 ≤ e.2 ∧ e.1 + e.2 ≤ 1) ∧
      HexSmall (ℓ - 1) (2 * (q.1 - e.1), 2 * (q.2.1 - e.2)))

private theorem honeyPos_zero : HoneyPos 0 (0, 0, 1) :=
  Or.inl ⟨rfl, by simp [hexSmall_iff]⟩

private theorem honeyPos_mono {ℓ ℓ' : ℤ} {q : ℤ × ℤ × ℤ} (hq : HoneyPos ℓ q) (h : ℓ ≤ ℓ') :
    HoneyPos ℓ' q := by
  simp only [HoneyPos, hexSmall_iff] at hq ⊢
  rcases hq with ⟨h1, hs⟩ | ⟨h1, e, he, hs⟩
  · exact Or.inl ⟨h1, by omega⟩
  · exact Or.inr ⟨h1, e, he, by omega⟩

private theorem honeyPos_nonneg {ℓ : ℤ} {q : ℤ × ℤ × ℤ} (hq : HoneyPos ℓ q) : 0 ≤ ℓ := by
  simp only [HoneyPos, hexSmall_iff] at hq
  omega

private theorem honeyPos_step {ℓ : ℤ} {q : ℤ × ℤ × ℤ} (hq : HoneyPos ℓ q) (c : Fin 3) :
    HoneyPos (ℓ + 1) (honeyStep c q) := by
  obtain ⟨s₁, s₂, γ⟩ := q
  have hc := fcol_corner c
  simp only [HoneyPos, honeyStep, hexSmall_iff] at hq ⊢
  rcases hq with ⟨rfl, hs⟩ | ⟨rfl, e, he, hs⟩
  · exact Or.inr ⟨rfl, fcol c, hc, by omega⟩
  · exact Or.inl ⟨by norm_num, by omega⟩

private theorem honeyPos_word : ∀ w : List (Fin 3),
    HoneyPos w.length (wordAct honeyStep w (0, 0, 1))
  | [] => honeyPos_zero
  | c :: w => by
    rw [wordAct_cons, List.length_cons]
    push_cast
    exact honeyPos_step (honeyPos_word w) c

private theorem honey_commute_hex {r v : ZMod (2 * m - 1)} {H : ℕ}
    (hv : ¬IsHexDefect (H + 1) r v) {q : ℤ × ℤ × ℤ} (hq : HoneyPos H q) (c : Fin 3) :
    honeyEv r v (honeyStep c q) = tripleStep m r c (honeyEv r v q) := by
  obtain ⟨s₁, s₂, γ⟩ := q
  have hc := fcol_corner c
  have hne : (γ : ZMod (2 * m - 1)) * v + 2 * s₁ + 2 * s₂ * r ≠ colour r c := by
    intro h
    rw [← ev_fcol, ev] at h
    simp only [HoneyPos, hexSmall_iff] at hq
    rcases hq with ⟨rfl, hs⟩ | ⟨rfl, e, he, hs⟩
    · exact hv ⟨(fcol c).1 - 2 * s₁, (fcol c).2 - 2 * s₂, hexSmall_iff.2 (by push_cast; omega),
        by push_cast at h ⊢; linear_combination h⟩
    · exact hv ⟨-((fcol c).1 - 2 * s₁), -((fcol c).2 - 2 * s₂),
        hexSmall_iff.2 (by push_cast; omega), by push_cast at h ⊢; linear_combination -h⟩
  simp only [honeyEv]
  rw [tripleStep_some, ite_eq_right hne]
  simp only [honeyStep, Option.some_inj]
  rw [← ev_fcol]
  simp only [ev]
  push_cast
  ring

private theorem honey_inj_hex {r v : ZMod (2 * m - 1)} {H : ℕ} (hr : IsGeneric H r)
    (hv : ¬IsHexDefect (H + 1) r v) {q q' : ℤ × ℤ × ℤ} (hq : HoneyPos (H + 1) q)
    (hq' : HoneyPos H q') (h : honeyEv r v q = honeyEv r v q') : q = q' := by
  have u2 := isUnit_two' (m := m)
  obtain ⟨s₁, s₂, γ⟩ := q
  obtain ⟨t₁, t₂, γ'⟩ := q'
  simp only [honeyEv, Option.some_inj] at h
  simp only [HoneyPos, hexSmall_iff] at hq hq'
  rcases hq with ⟨rfl, hs⟩ | ⟨rfl, e, he, hs⟩ <;> rcases hq' with ⟨rfl, ht⟩ | ⟨rfl, e', he', ht⟩
  · obtain ⟨e1, e2⟩ := hr (s₁ - t₁) (s₂ - t₂) (abs_le.2 ⟨by omega, by omega⟩)
      (abs_le.2 ⟨by omega, by omega⟩)
      (u2.mul_right_eq_zero.1 (by push_cast at h ⊢; linear_combination h))
    simp only [Prod.mk.injEq, and_true]
    omega
  · exact absurd ⟨t₁ - s₁, t₂ - s₂, hexSmall_iff.2 (by push_cast; omega),
      sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by push_cast at h ⊢; linear_combination h))⟩ hv
  · exact absurd ⟨s₁ - t₁, s₂ - t₂, hexSmall_iff.2 (by push_cast; omega),
      sub_eq_zero.1 (u2.mul_right_eq_zero.1 (by push_cast at h ⊢; linear_combination -h))⟩ hv
  · obtain ⟨e1, e2⟩ := hr (s₁ - t₁) (s₂ - t₂) (abs_le.2 ⟨by omega, by omega⟩)
      (abs_le.2 ⟨by omega, by omega⟩)
      (u2.mul_right_eq_zero.1 (by push_cast at h ⊢; linear_combination h))
    simp only [Prod.mk.injEq, and_true]
    omega

private theorem honey_words_iff_hex {r v : ZMod (2 * m - 1)} {H : ℕ} (hr : IsGeneric H r)
    (hv : ¬IsHexDefect (H + 1) r v) (w w' : List (Fin 3)) (hw : w.length ≤ H + 1)
    (hw' : w'.length ≤ H) :
    wordAct honeyStep w (0, 0, 1) = wordAct honeyStep w' (0, 0, 1) ↔
      wordAct (tripleStep m r) w (some v) = wordAct (tripleStep m r) w' (some v) := by
  have h0 : honeyEv r v (0, 0, 1) = some v := by simp [honeyEv]
  rw [← h0]
  refine words_iff_of_map (honeyEv r v) (fun u hu c ↦ ?_) (fun u u' hu hu' h ↦ ?_) w w' hw hw'
  · exact honey_commute_hex hv (honeyPos_mono (honeyPos_word u) (by exact_mod_cast hu)) c
  · exact honey_inj_hex hr hv (honeyPos_mono (honeyPos_word u) (by exact_mod_cast hu))
      (honeyPos_mono (honeyPos_word u') (by exact_mod_cast hu')) h

/-- **Proposition U**, honeycomb part at `H`-genericity (Theorem U′, item 1). For `H`-generic `r`
and `v` not a hex site of size `H + 1`, the `H`-ball of `v` in `G_r` is the `H`-ball of the
3-edge-coloured honeycomb. A honeycomb word of length `ℓ` ends at `(s, +1)` with hex norm
`2 N(s) ≤ ℓ` or at `(s, -1)` with `2 N(s - fcol c) + 1 ≤ ℓ` (Lemma Y), which replaces the
coordinate bound `ℓ` behind `ballIso_honeycomb` (`results/symmetry-audit-extend.md` §3.3,
organize-archive bf3fe60). -/
theorem ballIso_honeycomb_hex {H : ℕ} {r v : ZMod (2 * m - 1)} (hr : IsGeneric H r)
    (hv : ¬IsHexDefect (H + 1) r v) :
    BallIso honeyStep (tripleStep m r) (0, 0, 1) (some v) H :=
  ballIso_of_words (honey_words_iff_hex hr hv)

/-- **Proposition U**, honeycomb part, comparison at `H`-genericity. For `H`-generic `r` and `r'`,
and vertices `v`, `v'` that are not hex sites of size `H + 1` of `G_r`, `G_{r'}`, the `H`-balls
of `v` in `G_r` and of `v'` in `G_{r'}` are isomorphic (`results/symmetry-audit-extend.md` §3.3,
organize-archive bf3fe60). -/
theorem ballIso_some_of_not_isHexDefect {H : ℕ} {r r' v v' : ZMod (2 * m - 1)}
    (hr : IsGeneric H r) (hr' : IsGeneric H r') (hv : ¬IsHexDefect (H + 1) r v)
    (hv' : ¬IsHexDefect (H + 1) r' v') :
    BallIso (tripleStep m r) (tripleStep m r') (some v) (some v') H :=
  ballIso_of_words fun w w' hw hw' ↦
    (honey_words_iff_hex hr hv w w' hw hw').symm.trans (honey_words_iff_hex hr' hv' w w' hw hw')

/-- **Proposition U**, honeycomb part. For `H ≥ 1`, `4H`-generic `r` and `v` not a
`(2H + 1)`-defect site, the `H`-ball of `v` in `G_r` is the `H`-ball of the 3-edge-coloured
honeycomb (`results/k3-workaround-spike.md`, Proposition U, after Lemma M). It is a case of
`ballIso_honeycomb_hex`. -/
theorem ballIso_honeycomb {H : ℕ} (hH : 1 ≤ H) {r v : ZMod (2 * m - 1)}
    (hr : IsGeneric (4 * H) r) (hv : ¬IsDefect (2 * H + 1) r v) :
    BallIso honeyStep (tripleStep m r) (0, 0, 1) (some v) H :=
  ballIso_honeycomb_hex (hr.mono (by omega)) fun h ↦ hv (isDefect_mono h.isDefect (by omega))

/-- **Proposition U**, honeycomb part, comparison. For `H ≥ 1`, `4H`-generic `r` and `r'`, and
vertices `v`, `v'` that are not `(2H + 1)`-defect sites of `G_r`, `G_{r'}`, the `H`-balls of `v` in
`G_r` and of `v'` in `G_{r'}` are isomorphic (`results/k3-workaround-spike.md`, Proposition U,
after Lemma M). It is a case of `ballIso_some_of_not_isHexDefect`. -/
theorem ballIso_some_of_not_isDefect {H : ℕ} (hH : 1 ≤ H) {r r' v v' : ZMod (2 * m - 1)}
    (hr : IsGeneric (4 * H) r) (hr' : IsGeneric (4 * H) r') (hv : ¬IsDefect (2 * H + 1) r v)
    (hv' : ¬IsDefect (2 * H + 1) r' v') :
    BallIso (tripleStep m r) (tripleStep m r') (some v) (some v') H :=
  ballIso_some_of_not_isHexDefect (hr.mono (by omega)) (hr'.mono (by omega))
    (fun h ↦ hv (isDefect_mono h.isDefect (by omega)))
    (fun h ↦ hv' (isDefect_mono h.isDefect (by omega)))

/-! ### The balls at `∞` and at the sites at `(2H + 2)`-genericity -/

private def FormalPos (x₀ : Option (ℤ × ℤ)) (ℓ : ℤ) : Option (ℤ × ℤ) → Prop
  | none => ∀ p, x₀ = some p → Small ℓ p
  | some q => (∃ p, x₀ = some p ∧ ∃ h : ℤ × ℤ × ℤ, HoneyPos ℓ h ∧
        q = (h.2.2 * p.1 + 2 * h.1, h.2.2 * p.2 + 2 * h.2.1)) ∨
      ∃ e : ℤ × ℤ, (0 ≤ e.1 ∧ 0 ≤ e.2 ∧ e.1 + e.2 ≤ 1) ∧ ∃ (j : ℤ) (h : ℤ × ℤ × ℤ), HoneyPos j h ∧
        q = (h.2.2 * e.1 + 2 * h.1, h.2.2 * e.2 + 2 * h.2.1) ∧ 1 + j ≤ ℓ ∧
        ∀ p, x₀ = some p → Small (ℓ - 1 - j) p

private theorem formalPos_step {x₀ : Option (ℤ × ℤ)} {ℓ : ℤ} (hℓ : 0 ≤ ℓ) {o : Option (ℤ × ℤ)}
    (ho : FormalPos x₀ ℓ o) (c : Fin 3) : FormalPos x₀ (ℓ + 1) (formalStep c o) := by
  have hc := fcol_corner c
  rcases o with _ | q
  · refine Or.inr ⟨fcol c, hc, 0, (0, 0, 1), honeyPos_zero, by simp, by omega, fun p hp ↦ ?_⟩
    have := ho p hp
    rwa [show ℓ + 1 - 1 - 0 = ℓ by ring]
  · by_cases hqc : q = fcol c
    · simp only [formalStep, hqc, ↓reduceIte, FormalPos]
      intro p hp
      simp only [FormalPos] at ho
      rcases ho with ⟨p', hp', ⟨s₁, s₂, γ⟩, hs, hq⟩ | ⟨e, he, j, h, hs, -, hj, hsm⟩
      · rw [hp, Option.some_inj] at hp'
        subst hp'
        have h1 := congrArg Prod.fst (hqc.symm.trans hq)
        have h2 := congrArg Prod.snd (hqc.symm.trans hq)
        dsimp only at h1 h2
        simp only [HoneyPos, hexSmall_iff] at hs
        rw [small_iff]
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e', he', hs⟩ <;> omega
      · have h0 := honeyPos_nonneg hs
        have := small_iff.1 (hsm p hp)
        rw [small_iff]
        omega
    · simp only [formalStep, hqc, ↓reduceIte, FormalPos]
      simp only [FormalPos] at ho
      rcases ho with ⟨p, hp, h, hs, rfl⟩ | ⟨e, he, j, h, hs, rfl, hj, hsm⟩
      · refine Or.inl ⟨p, hp, honeyStep c h, honeyPos_step hs c, ?_⟩
        simp only [honeyStep]
        ext <;> dsimp only <;> ring
      · refine Or.inr ⟨e, he, j + 1, honeyStep c h, honeyPos_step hs c, ?_, by omega,
          fun p hp ↦ ?_⟩
        · simp only [honeyStep]
          ext <;> dsimp only <;> ring
        · rw [show ℓ + 1 - 1 - (j + 1) = ℓ - 1 - j by ring]
          exact hsm p hp

private theorem formalPos_word (x₀ : Option (ℤ × ℤ)) :
    ∀ w : List (Fin 3), FormalPos x₀ w.length (wordAct formalStep w x₀)
  | [] => by
    rcases x₀ with _ | p
    · simp only [wordAct_nil, FormalPos]
      intro p hp
      cases hp
    · exact Or.inl ⟨p, rfl, (0, 0, 1), honeyPos_zero, by simp⟩
  | c :: w => by
    rw [wordAct_cons, List.length_cons]
    push_cast
    exact formalPos_step (by positivity) (formalPos_word x₀ w) c
private theorem formalStep_some_map_of {r : ZMod (2 * m - 1)} {q : ℤ × ℤ} {c : Fin 3}
    (h : ev r q = ev r (fcol c) → q = fcol c) :
    Option.map (ev r) (formalStep c (some q)) = tripleStep m r c (Option.map (ev r) (some q)) := by
  rw [Option.map_some, tripleStep_some]
  by_cases hpc : q = fcol c
  · subst hpc
    simp [formalStep, ev_fcol]
  · have hne : ev r q ≠ colour r c := fun h' ↦ hpc (h (h'.trans (ev_fcol r c).symm))
    simp only [formalStep, hpc, hne, ↓reduceIte, Option.map_some, Option.some_inj]
    rw [← ev_fcol]
    simp only [ev]
    push_cast
    ring

omit [NeZero m] in
private theorem eq_of_ev_eq {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r) {x y : ℤ × ℤ}
    (h1 : -(G : ℤ) ≤ x.1 - y.1 ∧ x.1 - y.1 ≤ G) (h2 : -(G : ℤ) ≤ x.2 - y.2 ∧ x.2 - y.2 ≤ G)
    (h : ev r x = ev r y) : x = y := by
  obtain ⟨e1, e2⟩ := hr (x.1 - y.1) (x.2 - y.2) (abs_le.2 h1) (abs_le.2 h2)
    (by simp only [ev] at h; push_cast; linear_combination h)
  exact Prod.ext (by omega) (by omega)

private theorem eq_of_two_mul_ev_eq {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r)
    {x y : ℤ × ℤ} (h1 : -(G : ℤ) ≤ x.1 - y.1 ∧ x.1 - y.1 ≤ G)
    (h2 : -(G : ℤ) ≤ x.2 - y.2 ∧ x.2 - y.2 ≤ G) (h : 2 * ev r x = 2 * ev r y) : x = y :=
  eq_of_ev_eq hr h1 h2 ((isUnit_two' (m := m)).mul_left_cancel h)

private theorem formal_words_iff_hex {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r)
    {K : ℤ} {x₀ : Option (ℤ × ℤ)} (hx₀ : ∀ p, x₀ = some p → Small K p) {H : ℕ}
    (hK : K + H + 1 ≤ G) (hG : 2 * H + 1 ≤ G) (w w' : List (Fin 3)) (hw : w.length ≤ H + 1)
    (hw' : w'.length ≤ H) :
    wordAct formalStep w x₀ = wordAct formalStep w' x₀ ↔
      wordAct (tripleStep m r) w (Option.map (ev r) x₀) =
        wordAct (tripleStep m r) w' (Option.map (ev r) x₀) := by
  have hG' : (2 * H + 1 : ℤ) ≤ G := by exact_mod_cast hG
  refine words_iff_of_map (Option.map (ev r)) (fun u hu c ↦ ?_) (fun u u' hu hu' h ↦ ?_) w w'
    hw hw'
  · have hpos := formalPos_word x₀ u
    have hl : (u.length : ℤ) ≤ H := by exact_mod_cast hu
    generalize wordAct formalStep u x₀ = o at hpos ⊢
    generalize (u.length : ℤ) = ℓ at hpos hl
    rcases o with _ | q
    · exact formalStep_none_map r c
    · refine formalStep_some_map_of fun hev ↦ ?_
      have hc := fcol_corner c
      simp only [FormalPos] at hpos
      rcases hpos with ⟨p, hp, ⟨s₁, s₂, γ⟩, hs, rfl⟩ | ⟨e, he, j, ⟨s₁, s₂, γ⟩, hs, rfl, hj, -⟩
      · have hpK := small_iff.1 (hx₀ p hp)
        simp only [HoneyPos, hexSmall_iff] at hs
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e', he', hs⟩ <;>
          exact eq_of_ev_eq hr (by dsimp only; omega) (by dsimp only; omega) hev
      · simp only [HoneyPos, hexSmall_iff] at hs
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e', he', hs⟩ <;>
          exact eq_of_ev_eq hr (by dsimp only; omega) (by dsimp only; omega) hev
  · have hpos := formalPos_word x₀ u
    have hpos' := formalPos_word x₀ u'
    have hl : (u.length : ℤ) ≤ H + 1 := by exact_mod_cast hu
    have hl' : (u'.length : ℤ) ≤ H := by exact_mod_cast hu'
    generalize wordAct formalStep u x₀ = o at hpos h ⊢
    generalize wordAct formalStep u' x₀ = o' at hpos' h ⊢
    generalize (u.length : ℤ) = ℓ at hpos hl
    generalize (u'.length : ℤ) = ℓ' at hpos' hl'
    rcases o with _ | x <;> rcases o' with _ | y
    · rfl
    · simp at h
    · simp at h
    · rw [Option.map_some, Option.map_some, Option.some_inj] at h
      congr 1
      simp only [FormalPos] at hpos hpos'
      rcases hpos with ⟨p, hp, ⟨s₁, s₂, γ⟩, hs, rfl⟩ | ⟨e, he, j, ⟨s₁, s₂, γ⟩, hs, rfl, hj, hsm⟩ <;>
        rcases hpos' with ⟨p', hp', ⟨t₁, t₂, γ'⟩, ht, rfl⟩ |
          ⟨e', he', j', ⟨t₁, t₂, γ'⟩, ht, rfl, hj', hsm'⟩
      · rw [hp, Option.some_inj] at hp'
        subst hp'
        have hpK := small_iff.1 (hx₀ p hp)
        simp only [HoneyPos, hexSmall_iff] at hs ht
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e₁, he₁, hs⟩ <;>
          rcases ht with ⟨rfl, ht⟩ | ⟨rfl, e₂, he₂, ht⟩
        · have := eq_of_two_mul_ev_eq (x := (s₁, s₂)) (y := (t₁, t₂)) hr
            (by dsimp only; omega) (by dsimp only; omega)
            (by simp only [ev] at h ⊢; push_cast at h ⊢; linear_combination h)
          simp only [Prod.mk.injEq] at this ⊢
          omega
        · have := eq_of_two_mul_ev_eq (x := (p.1 + s₁, p.2 + s₂)) (y := (t₁, t₂)) hr
            (by dsimp only; omega) (by dsimp only; omega)
            (by simp only [ev] at h ⊢; push_cast at h ⊢; linear_combination h)
          simp only [Prod.mk.injEq] at this ⊢
          omega
        · have := eq_of_two_mul_ev_eq (x := (-p.1 + s₁, -p.2 + s₂)) (y := (t₁, t₂)) hr
            (by dsimp only; omega) (by dsimp only; omega)
            (by simp only [ev] at h ⊢; push_cast at h ⊢; linear_combination h)
          simp only [Prod.mk.injEq] at this ⊢
          omega
        · have := eq_of_two_mul_ev_eq (x := (s₁, s₂)) (y := (t₁, t₂)) hr
            (by dsimp only; omega) (by dsimp only; omega)
            (by simp only [ev] at h ⊢; push_cast at h ⊢; linear_combination h)
          simp only [Prod.mk.injEq] at this ⊢
          omega
      · have hpK := small_iff.1 (hsm' p hp)
        simp only [HoneyPos, hexSmall_iff] at hs ht
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e₁, he₁, hs⟩ <;>
          rcases ht with ⟨rfl, ht⟩ | ⟨rfl, e₂, he₂, ht⟩ <;>
          exact eq_of_ev_eq hr (by dsimp only; omega) (by dsimp only; omega) h
      · have hpK := small_iff.1 (hsm p' hp')
        simp only [HoneyPos, hexSmall_iff] at hs ht
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e₁, he₁, hs⟩ <;>
          rcases ht with ⟨rfl, ht⟩ | ⟨rfl, e₂, he₂, ht⟩ <;>
          exact eq_of_ev_eq hr (by dsimp only; omega) (by dsimp only; omega) h
      · simp only [HoneyPos, hexSmall_iff] at hs ht
        rcases hs with ⟨rfl, hs⟩ | ⟨rfl, e₁, he₁, hs⟩ <;>
          rcases ht with ⟨rfl, ht⟩ | ⟨rfl, e₂, he₂, ht⟩ <;>
          exact eq_of_ev_eq hr (by dsimp only; omega) (by dsimp only; omega) h

/-- **Proposition U**, formal form at `(2H + 2)`-genericity (Theorem U′, items 3 and 4). Let `x₀`
be `∞` or a formal point with coordinates of size at most `K`. If `r` is `G`-generic with
`K + H + 1 ≤ G` and `2H + 1 ≤ G`, the `H`-ball of `G_r` at the evaluation of `x₀` is the formal
`H`-ball at `x₀`. A walk from `x₀` that has not met `∞` sits at `γ x₀ + 2 s`, and one that has
sits at `γ fcol c + 2 s`, with `(s, γ)` a honeycomb position (Lemma W), which replaces the bound
`K + 2ℓ` behind `ballIso_formal` (`results/symmetry-audit-extend.md` §3.3, organize-archive
bf3fe60). -/
theorem ballIso_formal_hex {G : ℕ} {r : ZMod (2 * m - 1)} (hr : IsGeneric G r) {K : ℤ}
    {x₀ : Option (ℤ × ℤ)} (hx₀ : ∀ p, x₀ = some p → Small K p) {H : ℕ} (hK : K + H + 1 ≤ G)
    (hG : 2 * H + 1 ≤ G) :
    BallIso formalStep (tripleStep m r) x₀ (Option.map (ev r) x₀) H :=
  ballIso_of_words (formal_words_iff_hex hr hx₀ hK hG)

/-- **Proposition U** at `∞`, at `(2H + 1)`-genericity (Theorem U′, item 4). For `(2H + 1)`-generic
`r` and `r'`, the `H`-balls of `∞` in `G_r` and `G_{r'}` are isomorphic, colour by colour
(`results/symmetry-audit-extend.md` §3.3, organize-archive bf3fe60). -/
theorem ballIso_none_hex {H : ℕ} {r r' : ZMod (2 * m - 1)} (hr : IsGeneric (2 * H + 1) r)
    (hr' : IsGeneric (2 * H + 1) r') : BallIso (tripleStep m r) (tripleStep m r') none none H :=
  ballIso_of_words fun w w' hw hw' ↦
    (formal_words_iff_hex (K := H) (x₀ := none) hr (fun _ h ↦ by cases h) (by push_cast; omega)
      le_rfl w w' hw hw').symm.trans
    (formal_words_iff_hex (K := H) (x₀ := none) hr' (fun _ h ↦ by cases h) (by push_cast; omega)
      le_rfl w w' hw hw')

/-- **Proposition U** at the sites `a + b r`, at `(2H + 2)`-genericity (Theorem U′, item 3). For
`(2H + 2)`-generic `r` and `r'` and `|a|, |b| ≤ H + 1`, the `H`-ball of `a + b r` in `G_r` is
isomorphic to the `H`-ball of `a + b r'` in `G_{r'}` (`results/symmetry-audit-extend.md` §3.3,
organize-archive bf3fe60). -/
theorem ballIso_ev_hex {H : ℕ} {r r' : ZMod (2 * m - 1)} (hr : IsGeneric (2 * H + 2) r)
    (hr' : IsGeneric (2 * H + 2) r') {p : ℤ × ℤ} (hp : Small (H + 1) p) :
    BallIso (tripleStep m r) (tripleStep m r') (some (ev r p)) (some (ev r' p)) H :=
  ballIso_of_words fun w w' hw hw' ↦
    (formal_words_iff_hex (x₀ := some p) hr (fun _ h ↦ Option.some_inj.1 h ▸ hp)
      (by push_cast; omega) (by omega) w w' hw hw').symm.trans
    (formal_words_iff_hex (x₀ := some p) hr' (fun _ h ↦ Option.some_inj.1 h ▸ hp)
      (by push_cast; omega) (by omega) w w' hw hw')

/-! ### Proposition U -/

/-- **Proposition U** (local universality) at `(2H + 2)`-genericity, Theorem U′. For
`(2H + 2)`-generic `r` and `r'` there is a bijection `ψ` of `V_m` such that the `H`-ball of `G_r` at
every vertex `x` is isomorphic, colour by colour, to the `H`-ball of `G_{r'}` at `ψ x`. So the
rooted coloured `H`-balls of `G_r` and `G_{r'}` agree with multiplicity. `ψ` fixes `∞`, sends
`a + b r` to `a + b r'` for `|a|, |b| ≤ H + 1`, and matches the remaining vertices, whose balls are
honeycomb balls (`ballIso_honeycomb_hex`). Since `2H + 2 ≤ 4H` for `H ≥ 1`, this is the source's
`4H` form, and at most `(4H + 5)(4H + 4)` residues are excluded for prime `n`
(`card_not_isGeneric_le`) (`results/symmetry-audit-extend.md` §3.3, organize-archive bf3fe60). -/
theorem exists_ballIso_equiv_hex {H : ℕ} {r r' : ZMod (2 * m - 1)}
    (hr : IsGeneric (2 * H + 2) r) (hr' : IsGeneric (2 * H + 2) r') :
    ∃ ψ : Vertex m ≃ Vertex m, ∀ x, BallIso (tripleStep m r) (tripleStep m r') x (ψ x) H := by
  classical
  set B : Finset (ℤ × ℤ) := Finset.Icc (-(H + 1 : ℤ)) (H + 1) ×ˢ
    Finset.Icc (-(H + 1 : ℤ)) (H + 1) with hB
  have hBsmall : ∀ p ∈ B, Small (H + 1) p := fun p hp ↦ by
    rw [hB, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    exact ⟨abs_le.2 hp.1, abs_le.2 hp.2⟩
  let g : ZMod (2 * m - 1) → Option B → Vertex m := fun s o ↦ o.map fun p ↦ ev s p.1
  have hg : ∀ s, IsGeneric (2 * H + 2) s → Function.Injective (g s) := by
    intro s hs o o' h
    rcases o with _ | p <;> rcases o' with _ | p'
    · rfl
    · simp [g] at h
    · simp [g] at h
    · simp only [g, Option.map_some, Option.some_inj] at h
      exact congrArg some (Subtype.ext (ev_injOn hs (hBsmall _ p.2) (hBsmall _ p'.2)
        (by push_cast; omega) h))
  let e : Set.range (g r) ≃ Set.range (g r') :=
    (Equiv.ofInjective _ (hg r hr)).symm.trans (Equiv.ofInjective _ (hg r' hr'))
  have hcard : Fintype.card ↥(Set.range (g r))ᶜ = Fintype.card ↥(Set.range (g r'))ᶜ := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, Set.card_range_of_injective (hg r hr),
      Set.card_range_of_injective (hg r' hr')]
  let e₂ := Fintype.equivOfCardEq hcard
  let ψ : Vertex m ≃ Vertex m := (Equiv.Set.sumCompl (Set.range (g r))).symm.trans
    ((Equiv.sumCongr e e₂).trans (Equiv.Set.sumCompl (Set.range (g r'))))
  refine ⟨ψ, fun x ↦ ?_⟩
  by_cases hx : x ∈ Set.range (g r)
  · obtain ⟨o, rfl⟩ := hx
    have hmem : g r o ∈ Set.range (g r) := ⟨o, rfl⟩
    have hψ : ψ (g r o) = g r' o := by
      simp only [ψ, e, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmem,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_symm_apply,
        Equiv.ofInjective_apply]
    rw [hψ]
    rcases o with _ | p
    · exact ballIso_none_hex (hr.mono (by omega)) (hr'.mono (by omega))
    · exact ballIso_ev_hex hr hr' (hBsmall _ p.2)
  · have hψ : ψ x = (e₂ ⟨x, hx⟩ : Vertex m) := by
      simp only [ψ, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hx,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.Set.sumCompl_apply_inr]
    rw [hψ]
    have hy := (e₂ ⟨x, hx⟩).2
    generalize (e₂ ⟨x, hx⟩ : Vertex m) = y at hy ⊢
    have key : ∀ (s : ZMod (2 * m - 1)) (z : Vertex m), z ∉ Set.range (g s) →
        ∃ v, z = some v ∧ ¬IsHexDefect (H + 1) s v := by
      intro s z hz
      rcases z with _ | v
      · exact absurd ⟨none, rfl⟩ hz
      · refine ⟨v, rfl, fun hd ↦ ?_⟩
        obtain ⟨a, b, ha, hb, hab⟩ := hd.isDefect
        refine hz ⟨some ⟨(a, b), ?_⟩, ?_⟩
        · rw [hB, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
          exact ⟨abs_le.1 (by exact_mod_cast ha), abs_le.1 (by exact_mod_cast hb)⟩
        · simp [g, ev, hab]
    obtain ⟨v, rfl, hv⟩ := key r x hx
    obtain ⟨v', rfl, hv'⟩ := key r' y hy
    exact ballIso_some_of_not_isHexDefect (hr.mono (by omega)) (hr'.mono (by omega)) hv hv'

/-- **Proposition U** (local universality). For `H ≥ 1` and `(8H + 4)`-generic `r` and `r'` there
is a bijection `ψ` of `V_m` such that the `H`-ball of `G_r` at every vertex `x` is isomorphic, colour
by colour, to the `H`-ball of `G_{r'}` at `ψ x`. So the rooted coloured `H`-balls of `G_r` and
`G_{r'}` agree with multiplicity (`results/k3-workaround-spike.md`, Proposition U, after Lemma M).
It is a case of `exists_ballIso_equiv_hex`, which needs only `(2H + 2)`-genericity. -/
theorem exists_ballIso_equiv {H : ℕ} (hH : 1 ≤ H) {r r' : ZMod (2 * m - 1)}
    (hr : IsGeneric (8 * H + 4) r) (hr' : IsGeneric (8 * H + 4) r') :
    ∃ ψ : Vertex m ≃ Vertex m, ∀ x, BallIso (tripleStep m r) (tripleStep m r') x (ψ x) H :=
  exists_ballIso_equiv_hex (hr.mono (by omega)) (hr'.mono (by omega))

end RoundRobin.Canonical

end Pairing
