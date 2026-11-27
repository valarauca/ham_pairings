import Repair.LowerBound.Eight

/-!
# The certificate disks of a finite 1-core

Source: `results/struct-lb-extend.md` §3.2, table `𝒯_2`, and §3.3, Theorem B case 2, with
`results/struct-lb-factcheck-extend.md` §3, claim 6 (organize-archive b5cb45e). The points are
those of `scripts/struct-lb-e-k2cert.out` (b5cb45e).

The 105 certificate points of `𝒯_2` take only eight distinct values. Each entry of `certT` is
one of them: the context `o` of its cell with inverse `oi`, the mask of the matchings that `o`
covers, the shifts `k`, and the centre `(U/Q, W/Q)`. `certT_ok` checks in integer arithmetic that
every gap form of the cell has clearance at least `13/640` at the centre, and that each mask is
right. `certT_full` checks that the eight masks together cover all 105 matchings.

* `exists_cert8` : every matching `r` of the eight ends has a context that covers it, on a whole
  open disk of radius `13/640`.
-/

namespace Pairing

namespace LowerBound

/-- A certificate point: the context `o`, its inverse `oi`, its cover mask `m`, the shifts `k`
and the centre `(U/Q, W/Q)` (`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
structure CertPt where
  o : List ℕ
  oi : List ℕ
  m : ℕ
  k : List ℤ
  U : ℤ
  W : ℤ
  Q : ℤ

/-- The eight distinct certificate points of `𝒯_2` (`scripts/struct-lb-e-k2cert.out`,
organize-archive b5cb45e). -/
def certT : List CertPt :=
  [⟨[7, 2, 1, 0, 4, 5, 6, 3], [3, 2, 1, 7, 4, 5, 6, 0], 4312689819023092548915552709464,
      [1, 3, 5, 0], 611, 291, 640⟩,
    ⟨[3, 2, 1, 0, 4, 5, 6, 7], [3, 2, 1, 0, 4, 5, 6, 7], 2355034569158839046879281843611,
      [1, 3, 5, 1], 611, 349, 640⟩,
    ⟨[7, 6, 5, 4, 0, 1, 2, 3], [4, 5, 6, 7, 3, 2, 1, 0], 562591490624581474952854059,
      [0, 0, 0, 0], 29, 291, 640⟩,
    ⟨[3, 6, 5, 4, 0, 1, 2, 7], [4, 5, 6, 0, 3, 2, 1, 7], 18434727723012024859075560041526,
      [0, 0, 0, 1], 29, 349, 640⟩,
    ⟨[2, 0, 5, 7, 3, 1, 4, 6], [1, 5, 0, 4, 6, 2, 7, 3], 4311745160846727647229602379696,
      [1, 2, 4, 0], 1393, 49, 1920⟩,
    ⟨[6, 5, 3, 4, 0, 7, 1, 2], [4, 6, 7, 2, 3, 1, 0, 5], 19417089534275587803778690857515,
      [0, 0, 0, 1], 133, 1705, 1920⟩,
    ⟨[4, 2, 7, 5, 1, 3, 6, 0], [7, 4, 1, 5, 0, 3, 6, 2], 27291221034537860184966225222534,
      [0, 1, 2, 0], 679, 241, 1920⟩,
    ⟨[2, 0, 5, 3, 7, 1, 4, 6], [1, 5, 0, 3, 6, 2, 7, 4], 32566488643811330522173102622574,
      [1, 2, 4, 1], 1393, 1731, 1920⟩]

/-- The check of one certificate point, with clearance `r² = 169/409600 = (13/640)²`. -/
def certOK (e : CertPt) : Bool :=
  maskOK e.o e.oi e.m && diskOK e.o e.k e.U e.W e.Q 169 409600 && decide (0 < e.Q)

/-- Every certificate point has clearance `13/640` and a correct mask
(`results/struct-lb-extend.md` §3.2, organize-archive b5cb45e). -/
theorem certT_ok : certT.all certOK = true := by
  decide +kernel

/-- The eight certificate contexts cover all 105 matchings (`results/struct-lb-extend.md` §3.2,
organize-archive b5cb45e). -/
theorem certT_full : orAll (certT.map CertPt.m) = 2 ^ 105 - 1 := by
  decide +kernel

/-- **The certificate disks** (`results/struct-lb-extend.md` §3.2, table `𝒯_2`, organize-archive
b5cb45e). Every fixed-point-free involution `r` of the eight ends has a context `o` that covers
it, and a disk of radius `13/640` inside the cell of `o`. -/
theorem exists_cert8 {r : Fin 8 → Fin 8} (h1 : ∀ j, r (r j) = j) (h2 : ∀ j, r j ≠ j) :
    ∃ (o oi : List ℕ) (k : List ℤ) (u w : ℝ), (∀ j, fin8 o (fin8 oi j) = j) ∧
      ArcCovers (fin8 o) (fin8 oi) tau8 r ∧
      ∀ x y : ℝ, (x - u) ^ 2 + (y - w) ^ 2 < (13 / 640) ^ 2 → RealCell8 o k x y := by
  obtain ⟨i, hi, rfl, m, hm, hb⟩ := exists_mask_of_orAll certT_full h1 h2
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have hok := List.all_eq_true.mp certT_ok e he
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hmask, hdisk⟩, hQ⟩ := hok
  refine ⟨e.o, e.oi, e.k, (e.U : ℝ) / e.Q, (e.W : ℝ) / e.Q, maskOK_inv hmask,
    maskOK_covers hmask hi hb, fun x y hd ↦ diskOK_spec hdisk hQ (by norm_num) ?_⟩
  push_cast
  linarith [show ((13 : ℝ) / 640) ^ 2 = 169 / 409600 by norm_num]

end LowerBound

end Pairing
