import Clifford.Frame

/-!
# Maas's GF(2) model and an explicit intertwiner (COD-105)

Maas (arXiv:0911.3794, Table 1) builds a basic spin representation of `S̃_m` over GF(2). He starts
from the one-dimensional representation of `S̃₂` and alternates two constructions.
* `S` (Lemma 5, doubled degree) sends `T_i` to `diag(T_i, T_i)` for `i ≤ m − 3`, sends `T_{m−2}` to
  `[[T_{m−2}, I], [0, T_{m−2}]]`, and adds `T_{m−1} = [[0, I], [I, 0]]`. These are his matrices
  with every sign dropped, since we are in characteristic 2.
* `S_I` (Lemma 7, `p = 2`) adds `T_{m−1} = J`, plus `I` when `m ≡ 2 mod 4`, where
  `J = ∑_{k ≤ m−2} k T_k` reduces mod 2 to the sum over odd `k`.

A basis vector of the degree-`2^k` model is a bit vector of length `k`, stored here as the set of
its set bits, `Bits k = Finset (Fin k)`. The doubling step adds the last bit, and its value picks
the block. `maasGen k i` is Maas's `T_i` for the stage-`(2k+2)` model.

* `maasGen_closed` : `T_{2j+2}` flips bit `j`, and `T_{2a+1} = I + L_{a−1} + L_a`, where `L_g`
  clears bit `g`.
* `toMatrix_ρW_adj` : the matrix of `ρ((t t+1))` in the basis `w_S` of `W_n` (`wBasis`) is Maas's
  `T_{t+1}` on `Bits (n − 1)`.
* `wBasis_equivFun_ρW` : the coordinate map of `wBasis` is a linear isomorphism `W_n ≃ 𝔽₂^{Bits}`
  carrying `ρ((t t+1))` to Maas's `T_{t+1}`. This is the explicit intertwiner.

Maas's Cor. 13 calls this model a basic spin representation, on the authority of Wales through
his Prop. 3 and Thm. 1. The intertwiner makes the identification concrete but does not remove that
dependence.
-/

namespace Pairing.PerfectMatching

open Equiv Matrix

/-- Bit vectors of length `k`, as the set of set bits. -/
abbrev Bits (k : ℕ) := Finset (Fin k)

/-- The first `k` bits of a vector of length `k + 1`. -/
def initBits {k : ℕ} (x : Bits (k + 1)) : Bits k :=
  Finset.univ.filter fun i ↦ i.castSucc ∈ x

theorem mem_initBits {k : ℕ} {x : Bits (k + 1)} {i : Fin k} : i ∈ initBits x ↔ i.castSucc ∈ x := by
  simp [initBits]

theorem bits_eq_iff {k : ℕ} {x y : Bits (k + 1)} :
    x = y ↔ initBits x = initBits y ∧ (Fin.last k ∈ x ↔ Fin.last k ∈ y) := by
  constructor
  · rintro rfl
    exact ⟨rfl, Iff.rfl⟩
  · rintro ⟨h1, h2⟩
    ext i
    induction i using Fin.lastCases with
    | last => exact h2
    | cast i =>
      have := Finset.ext_iff.mp h1 i
      rwa [mem_initBits, mem_initBits] at this

/-- Flip bit `j`. -/
def flipMat {k : ℕ} (j : Fin k) : Matrix (Bits k) (Bits k) F₂ :=
  Matrix.of fun x y ↦ if x = symmDiff {j} y then 1 else 0

/-- Clear bit `g`, sending `e_y` to `e_{y \ g}` when bit `g` of `y` is set, and to `0` otherwise. -/
def lowerMat {k : ℕ} (g : Fin k) : Matrix (Bits k) (Bits k) F₂ :=
  Matrix.of fun x y ↦ if g ∈ y ∧ x = y.erase g then 1 else 0

/-- `I + L_{a−1} + L_a`, with the out-of-range terms omitted. -/
def blockMat (k a : ℕ) : Matrix (Bits k) (Bits k) F₂ :=
  1 + (if h : 0 < a ∧ a - 1 < k then lowerMat ⟨a - 1, h.2⟩ else 0) +
    (if h : a < k then lowerMat ⟨a, h⟩ else 0)

/-- The block matrix `[[A, B], [C, D]]` on `Bits (k + 1)`, with the last bit picking the block. -/
def dbl {k : ℕ} (A B C D : Matrix (Bits k) (Bits k) F₂) : Matrix (Bits (k + 1)) (Bits (k + 1)) F₂ :=
  Matrix.of fun x y ↦
    (if Fin.last k ∈ x then (if Fin.last k ∈ y then D else C)
      else (if Fin.last k ∈ y then B else A)) (initBits x) (initBits y)

/-- Maas's construction `S` in characteristic 2, from stage `2k + 2` to stage `2k + 3`. -/
def maasS (k : ℕ) (T : ℕ → Matrix (Bits k) (Bits k) F₂) :
    ℕ → Matrix (Bits (k + 1)) (Bits (k + 1)) F₂ := fun j ↦
  if j ≤ 2 * k then dbl (T j) 0 0 (T j)
  else if j = 2 * k + 1 then dbl (T j) 1 0 (T j)
  else if j = 2 * k + 2 then dbl 0 1 1 0
  else 0

/-- Maas's construction `S_I` for `p = 2`, from stage `2k + 3` to stage `2k + 4`. -/
def maasSI (k : ℕ) (O : ℕ → Matrix (Bits (k + 1)) (Bits (k + 1)) F₂) :
    ℕ → Matrix (Bits (k + 1)) (Bits (k + 1)) F₂ := fun i ↦
  if i ≤ 2 * k + 2 then O i
  else if i = 2 * k + 3 then
    (∑ a ∈ Finset.range (k + 1), O (2 * a + 1)) + (if k % 2 = 1 then 1 else 0)
  else 0

/-- Maas's generators `T_i` of the stage-`(2k + 2)` GF(2) model, `S_I ∘ S` applied `k` times to
`S̃₂ ↦ (1)`. -/
def maasGen : (k : ℕ) → ℕ → Matrix (Bits k) (Bits k) F₂
  | 0 => fun i ↦ if i = 1 then 1 else 0
  | k + 1 => maasSI k (maasS k (maasGen k))

theorem mat_add_self {k : ℕ} (M : Matrix (Bits k) (Bits k) F₂) : M + M = 0 := by
  rw [← two_smul F₂ M, show (2 : F₂) = 0 by decide, zero_smul]

theorem dbl_apply {k : ℕ} (A B C D : Matrix (Bits k) (Bits k) F₂) (x y : Bits (k + 1)) :
    dbl A B C D x y = (if Fin.last k ∈ x then (if Fin.last k ∈ y then D else C)
      else (if Fin.last k ∈ y then B else A)) (initBits x) (initBits y) :=
  rfl

theorem dbl_add {k : ℕ} (A B C D A' B' C' D' : Matrix (Bits k) (Bits k) F₂) :
    dbl (A + A') (B + B') (C + C') (D + D') = dbl A B C D + dbl A' B' C' D' := by
  ext x y
  simp only [dbl_apply, Matrix.add_apply]
  split_ifs <;> rfl

theorem dbl_zero {k : ℕ} : dbl (0 : Matrix (Bits k) (Bits k) F₂) 0 0 0 = 0 := by
  ext x y
  simp only [dbl_apply, Matrix.zero_apply]
  split_ifs <;> rfl

theorem dbl_one {k : ℕ} : dbl (1 : Matrix (Bits k) (Bits k) F₂) 0 0 1 = 1 := by
  ext x y
  by_cases hx : Fin.last k ∈ x <;> by_cases hy : Fin.last k ∈ y <;>
    simp [dbl_apply, Matrix.one_apply, bits_eq_iff (k := k), hx, hy]

theorem initBits_symmDiff_castSucc {k : ℕ} (j : Fin k) (y : Bits (k + 1)) :
    initBits (symmDiff {j.castSucc} y) = symmDiff {j} (initBits y) := by
  ext i
  simp [mem_initBits, Finset.mem_symmDiff]

theorem last_mem_symmDiff_castSucc {k : ℕ} (j : Fin k) (y : Bits (k + 1)) :
    Fin.last k ∈ symmDiff {j.castSucc} y ↔ Fin.last k ∈ y := by
  simp [Finset.mem_symmDiff, (Fin.castSucc_lt_last j).ne']

theorem initBits_symmDiff_last {k : ℕ} (y : Bits (k + 1)) :
    initBits (symmDiff {Fin.last k} y) = initBits y := by
  ext i
  simp [mem_initBits, Finset.mem_symmDiff, (Fin.castSucc_lt_last i).ne]

theorem last_mem_symmDiff_last {k : ℕ} (y : Bits (k + 1)) :
    Fin.last k ∈ symmDiff {Fin.last k} y ↔ Fin.last k ∉ y := by
  simp [Finset.mem_symmDiff]

theorem initBits_erase_castSucc {k : ℕ} (g : Fin k) (y : Bits (k + 1)) :
    initBits (y.erase g.castSucc) = (initBits y).erase g := by
  ext i
  simp [mem_initBits, Fin.castSucc_inj]

theorem last_mem_erase_castSucc {k : ℕ} (g : Fin k) (y : Bits (k + 1)) :
    Fin.last k ∈ y.erase g.castSucc ↔ Fin.last k ∈ y := by
  simp [(Fin.castSucc_lt_last g).ne']

theorem initBits_erase_last {k : ℕ} (y : Bits (k + 1)) :
    initBits (y.erase (Fin.last k)) = initBits y := by
  ext i
  simp [mem_initBits, (Fin.castSucc_lt_last i).ne]

theorem dbl_flip {k : ℕ} (j : Fin k) : dbl (flipMat j) 0 0 (flipMat j) = flipMat j.castSucc := by
  ext x y
  by_cases hx : Fin.last k ∈ x <;> by_cases hy : Fin.last k ∈ y <;>
    simp [dbl_apply, flipMat, bits_eq_iff (k := k), initBits_symmDiff_castSucc,
      last_mem_symmDiff_castSucc, hx, hy]

theorem dbl_lower {k : ℕ} (g : Fin k) :
    dbl (lowerMat g) 0 0 (lowerMat g) = lowerMat g.castSucc := by
  ext x y
  by_cases hx : Fin.last k ∈ x <;> by_cases hy : Fin.last k ∈ y <;>
    simp [dbl_apply, lowerMat, bits_eq_iff (k := k), initBits_erase_castSucc, mem_initBits, hx,
      hy, (Fin.castSucc_lt_last g).ne']

theorem dbl_swap {k : ℕ} :
    dbl (0 : Matrix (Bits k) (Bits k) F₂) 1 1 0 = flipMat (Fin.last k) := by
  ext x y
  by_cases hx : Fin.last k ∈ x <;> by_cases hy : Fin.last k ∈ y <;>
    simp [dbl_apply, flipMat, Matrix.one_apply, bits_eq_iff (k := k), initBits_symmDiff_last,
      last_mem_symmDiff_last, hx, hy]

theorem dbl_upper {k : ℕ} :
    dbl (0 : Matrix (Bits k) (Bits k) F₂) 1 0 0 = lowerMat (Fin.last k) := by
  ext x y
  by_cases hx : Fin.last k ∈ x <;> by_cases hy : Fin.last k ∈ y <;>
    simp [dbl_apply, lowerMat, Matrix.one_apply, bits_eq_iff (k := k), initBits_erase_last, hx, hy]

theorem dbl_add_diag {k : ℕ} (A A' : Matrix (Bits k) (Bits k) F₂) :
    dbl (A + A') 0 0 (A + A') = dbl A 0 0 A + dbl A' 0 0 A' := by
  simpa using dbl_add A 0 0 A A' 0 0 A'

theorem dbl_upper_split {k : ℕ} (A : Matrix (Bits k) (Bits k) F₂) :
    dbl A 1 0 A = dbl A 0 0 A + lowerMat (Fin.last k) := by
  rw [← dbl_upper]
  simpa using dbl_add A 0 0 A 0 1 0 0

theorem dbl_dite_lower {k : ℕ} (p : Prop) [Decidable p] (g : p → Fin k) :
    dbl (if h : p then lowerMat (g h) else 0) 0 0 (if h : p then lowerMat (g h) else 0) =
      if h : p then lowerMat (g h).castSucc else 0 := by
  split_ifs with h
  · exact dbl_lower (g h)
  · exact dbl_zero

theorem dbl_blockMat {k a : ℕ} (ha : a < k) :
    dbl (blockMat k a) 0 0 (blockMat k a) = blockMat (k + 1) a := by
  rw [blockMat, dbl_add_diag, dbl_add_diag, dbl_one, dbl_dite_lower, dbl_dite_lower, blockMat]
  congr 1
  · congr 1
    by_cases h : 0 < a ∧ a - 1 < k
    · rw [dite_eq_left h, dite_eq_left ⟨h.1, by omega⟩]
      rfl
    · rw [dite_eq_right h, dite_eq_right (by omega)]
  · rw [dite_eq_left ha, dite_eq_left (by omega)]
    rfl

theorem dbl_blockMat_last (k : ℕ) :
    dbl (blockMat k k) 1 0 (blockMat k k) = blockMat (k + 1) k := by
  rw [dbl_upper_split, blockMat, dite_eq_right (lt_irrefl k), add_zero, dbl_add_diag, dbl_one,
    dbl_dite_lower, blockMat, dite_eq_left (by omega : k < k + 1)]
  congr 1
  congr 1
  by_cases h : 0 < k ∧ k - 1 < k
  · rw [dite_eq_left h, dite_eq_left ⟨h.1, by omega⟩]
    rfl
  · rw [dite_eq_right h, dite_eq_right (by omega)]

theorem natCast_F₂ (m : ℕ) : (m : F₂) = if m % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> decide

theorem nsmul_mat {k : ℕ} (m : ℕ) (M : Matrix (Bits k) (Bits k) F₂) :
    m • M = if m % 2 = 1 then M else 0 := by
  rw [← Nat.cast_smul_eq_nsmul F₂, natCast_F₂]
  split_ifs <;> simp

/-- Telescoping, `∑_{a ≤ m} (I + L_{a−1} + L_a) = (m + 1) I + L_m`. -/
theorem sum_blockMat (K m : ℕ) (hm : m < K) :
    ∑ a ∈ Finset.range (m + 1), blockMat K a = (m + 1) • (1 : Matrix (Bits K) (Bits K) F₂) +
      lowerMat ⟨m, hm⟩ := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one, blockMat, dite_eq_right (by omega), dite_eq_left hm, add_zero,
      zero_add, one_nsmul]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), blockMat, dite_eq_left ⟨by omega, by omega⟩,
      dite_eq_left hm]
    simp only [Nat.add_sub_cancel]
    calc (m + 1) • (1 : Matrix (Bits K) (Bits K) F₂) + lowerMat ⟨m, by omega⟩ +
          (1 + lowerMat ⟨m, by omega⟩ + lowerMat ⟨m + 1, hm⟩)
        = (m + 1) • (1 : Matrix (Bits K) (Bits K) F₂) + 1 +
          (lowerMat ⟨m, by omega⟩ + lowerMat ⟨m, by omega⟩) + lowerMat ⟨m + 1, hm⟩ := by abel
      _ = (m + 1 + 1) • (1 : Matrix (Bits K) (Bits K) F₂) + lowerMat ⟨m + 1, hm⟩ := by
        rw [mat_add_self, add_zero, succ_nsmul (1 : Matrix (Bits K) (Bits K) F₂) (m + 1)]

/-- Closed forms of Maas's GF(2) generators. -/
theorem maasGen_closed (k : ℕ) :
    (∀ j : Fin k, maasGen k (2 * j + 2) = flipMat j) ∧
      ∀ a ≤ k, maasGen k (2 * a + 1) = blockMat k a := by
  induction k with
  | zero =>
    refine ⟨fun j ↦ j.elim0, fun a ha ↦ ?_⟩
    obtain rfl : a = 0 := by omega
    simp [maasGen, blockMat]
  | succ k ih =>
    obtain ⟨ihG, ihB⟩ := ih
    have hOG : ∀ j : Fin (k + 1), maasS k (maasGen k) (2 * j + 2) = flipMat j := by
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hj := j'.isLt
        rw [maasS, ite_eq_left (by simp; omega), Fin.val_castSucc, ihG j', dbl_flip]
      · rw [maasS, ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left (by simp),
          dbl_swap]
    have hOB : ∀ a ≤ k, maasS k (maasGen k) (2 * a + 1) = blockMat (k + 1) a := by
      intro a ha
      rcases lt_or_eq_of_le ha with ha | rfl
      · rw [maasS, ite_eq_left (by omega), ihB a ha.le, dbl_blockMat ha]
      · rw [maasS, ite_eq_right (by omega), ite_eq_left rfl, ihB a le_rfl, dbl_blockMat_last]
    refine ⟨fun j ↦ ?_, fun a ha ↦ ?_⟩
    · have hj := j.isLt
      rw [maasGen, maasSI, ite_eq_left (by omega), hOG j]
    · rcases lt_or_eq_of_le ha with ha | rfl
      · rw [maasGen, maasSI, ite_eq_left (by omega), hOB a (by omega)]
      · rw [maasGen, maasSI, ite_eq_right (by omega), ite_eq_left (by omega),
          Finset.sum_congr rfl fun a ha ↦ hOB a (by simp at ha; omega),
          sum_blockMat (k + 1) k (by omega), blockMat, dite_eq_left ⟨by omega, by omega⟩,
          dite_eq_right (by omega), add_zero, nsmul_mat]
        simp only [Nat.add_sub_cancel]
        rcases Nat.mod_two_eq_zero_or_one k with h | h
        · rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero]
        · rw [ite_eq_right (by omega), ite_eq_left h, zero_add]
          exact add_comm _ _


section Intertwiner

variable (n : ℕ)

/-- The adjacency sum of `B_w`, split into the two neighbouring gaps. -/
theorem sum_filter_adj {M : Type*} [AddCommMonoid M] (S : Finset (Fin (n - 1))) (a : ℕ)
    (f : Fin (n - 1) → M) :
    ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a), f g =
      (if h : 0 < a ∧ a - 1 < n - 1 then (if (⟨a - 1, h.2⟩ : Fin (n - 1)) ∈ S then
        f ⟨a - 1, h.2⟩ else 0) else 0) +
      (if h : a < n - 1 then (if (⟨a, h⟩ : Fin (n - 1)) ∈ S then f ⟨a, h⟩ else 0) else 0) := by
  rw [Finset.filter_or, Finset.sum_union (Finset.disjoint_filter.mpr fun g _ h1 h2 ↦ by omega),
    add_comm]
  congr 1
  · by_cases h : 0 < a ∧ a - 1 < n - 1
    · rw [dite_eq_left h, Finset.filter_congr (q := fun g : Fin (n - 1) ↦ (g : ℕ) = a - 1)
        (fun g _ ↦ by omega), sum_filter_val_eq n S (a - 1) h.2]
    · rw [dite_eq_right h, Finset.filter_false_of_mem (fun g _ ↦ by have := g.isLt; omega),
        Finset.sum_empty]
  · by_cases h : a < n - 1
    · rw [dite_eq_left h, sum_filter_val_eq n S a h]
    · rw [dite_eq_right h, Finset.filter_false_of_mem (fun g _ ↦ by have := g.isLt; omega),
        Finset.sum_empty]

theorem lowerMat_apply {k : ℕ} (g : Fin k) (x y : Bits k) :
    lowerMat g x y = if g ∈ y then (if y.erase g = x then 1 else 0) else 0 := by
  rw [lowerMat, Matrix.of_apply]
  by_cases hg : g ∈ y <;> by_cases hx : x = y.erase g <;> simp [hg, hx, eq_comm]

variable (hn : 1 ≤ n)

/-- A gap swap in the basis `w_S` is Maas's `T_{2j+2}`. -/
theorem toMatrix_ρW_gap (j : Fin (n - 1)) :
    LinearMap.toMatrix (wBasis n hn) (wBasis n hn) (ρW (sigma n {j})) =
      maasGen (n - 1) (2 * j + 2) := by
  rw [(maasGen_closed (n - 1)).1 j]
  ext x y
  rw [LinearMap.toMatrix_apply, wBasis_apply, ρW_sigma_w, ← wBasis_apply n hn,
    Module.Basis.repr_self, Finsupp.single_apply, flipMat, Matrix.of_apply]
  exact if_congr eq_comm rfl rfl

/-- A block swap in the basis `w_S` is Maas's `T_{2a+1}`. -/
theorem toMatrix_B (a : Fin n) :
    LinearMap.toMatrix (wBasis n hn) (wBasis n hn) (B n a) = maasGen (n - 1) (2 * a + 1) := by
  rw [(maasGen_closed (n - 1)).2 a (by have := a.isLt; omega)]
  ext x y
  rw [LinearMap.toMatrix_apply, wBasis_apply, B_w, map_add, map_sum, Finsupp.add_apply,
    Finsupp.finsetSum_apply, sum_filter_adj, ← wBasis_apply n hn, Module.Basis.repr_self,
    Finsupp.single_apply, blockMat, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    add_assoc]
  have h1 : (if y = x then (1 : F₂) else 0) = if x = y then 1 else 0 := if_congr eq_comm rfl rfl
  have h2 : (if h : 0 < (a : ℕ) ∧ (a : ℕ) - 1 < n - 1 then
      (if (⟨(a : ℕ) - 1, h.2⟩ : Fin (n - 1)) ∈ y then
        ((wBasis n hn).repr (w n (y.erase ⟨(a : ℕ) - 1, h.2⟩))) x else 0) else 0) =
      (if h : 0 < (a : ℕ) ∧ (a : ℕ) - 1 < n - 1 then lowerMat ⟨(a : ℕ) - 1, h.2⟩ else 0) x y := by
    by_cases h : 0 < (a : ℕ) ∧ (a : ℕ) - 1 < n - 1
    · rw [dite_eq_left h, dite_eq_left h, lowerMat_apply, ← wBasis_apply n hn,
        Module.Basis.repr_self, Finsupp.single_apply]
    · rw [dite_eq_right h, dite_eq_right h, Matrix.zero_apply]
  have h3 : (if h : (a : ℕ) < n - 1 then
      (if (⟨(a : ℕ), h⟩ : Fin (n - 1)) ∈ y then
        ((wBasis n hn).repr (w n (y.erase ⟨(a : ℕ), h⟩))) x else 0) else 0) =
      (if h : (a : ℕ) < n - 1 then lowerMat ⟨(a : ℕ), h⟩ else 0) x y := by
    by_cases h : (a : ℕ) < n - 1
    · rw [dite_eq_left h, dite_eq_left h, lowerMat_apply, ← wBasis_apply n hn,
        Module.Basis.repr_self, Finsupp.single_apply]
    · rw [dite_eq_right h, dite_eq_right h, Matrix.zero_apply]
  rw [h1, h2, h3]

/-- The adjacent transposition `(t t+1)` in the basis `w_S` is Maas's `T_{t+1}`. -/
theorem toMatrix_ρW_adj (t : ℕ) (ht : t + 1 < 2 * n) :
    LinearMap.toMatrix (wBasis n hn) (wBasis n hn)
        (ρW (swap (⟨t, by omega⟩ : Fin (2 * n)) ⟨t + 1, ht⟩)) =
      maasGen (n - 1) (t + 1) := by
  rcases Nat.even_or_odd' t with ⟨a, rfl | rfl⟩
  · have ha : a < n := by omega
    have e : ρW (swap (⟨2 * a, by omega⟩ : Fin (2 * n)) ⟨2 * a + 1, ht⟩) = B n ⟨a, ha⟩ := rfl
    rw [e, toMatrix_B]
  · have hj : a < n - 1 := by omega
    have e : ρW (swap (⟨2 * a + 1, by omega⟩ : Fin (2 * n)) ⟨2 * a + 1 + 1, ht⟩) =
        ρW (sigma n {⟨a, hj⟩}) := by
      rw [sigma_single]
      rfl
    rw [e, toMatrix_ρW_gap]

/-- The explicit intertwiner. The coordinate map of `wBasis`, `W_n ≃ 𝔽₂^{Bits (n−1)}`, carries
`ρ((t t+1))` to Maas's GF(2) generator `T_{t+1}`. -/
theorem wBasis_equivFun_ρW (t : ℕ) (ht : t + 1 < 2 * n) (v : W (Fin (2 * n))) :
    (wBasis n hn).equivFun (ρW (swap (⟨t, by omega⟩ : Fin (2 * n)) ⟨t + 1, ht⟩) v) =
      (maasGen (n - 1) (t + 1)).mulVec ((wBasis n hn).equivFun v) := by
  rw [← toMatrix_ρW_adj n hn t ht, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

end Intertwiner

end Pairing.PerfectMatching
