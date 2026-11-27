import Pairing.Affine
import Repair.Forcing

/-!
# A canonical zero state for every `m ≥ 6` (COD-165)

Labels are naturals below `2m - 1`, read in `ℤ/(2m-1)`. For an involution `p` of a set `S` of
labels, `natMatching m p S` is the partial matching of finite vertices with edges `s(x, p x)`.

* `blocks_factor` : a set `C ⊆ ℤ/(2m-1)` that is a union of edges of `A`, and that
  `x ↦ 2t - x` maps into itself without fixed points, blocks `F_t`.
* `blocks_natMatching` : the same for a set `W` of labels whose members pair up with sum `r` or
  `r + 2m - 1`, where `r ≡ 2t`.
* `stdMatching m`, for `m ≥ 7` : the edges `{1,6}, {2,3}, {4,5}` and `{2i-1, 2i}` for
  `4 ≤ i ≤ m - 1`. With `∞0` added it is the zero state `{∞0, 16, 23, 45, …}` of the ledger.
  `blocks_stdMatching` blocks each `F_t` by an interval of labels or by a `4`-cycle.
* `sixMatching`, for `m = 6` : the edges `{1,6}, {2,4}, {3,7}, {5,8}, {9,10}`.
* `exists_zeroForcing` : for every `m ≥ 6` some partial matching that leaves `∞` uncovered blocks
  every `F_t`. `nonempty_zeroState` : a canonical zero state exists for every `m ≥ 6`.
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- The partial matching of finite vertices of `V_m` with edges `s(x, p x)` for the labels
`x ∈ S`. -/
def natMatching (m : ℕ) (p : ℕ → ℕ) (S : Finset ℕ) : Finset (Sym2 (Vertex m)) :=
  S.image fun x : ℕ ↦ s(some (x : ZMod (2 * m - 1)), some (p x : ZMod (2 * m - 1)))

/-- The partner of a label in the standard matching: `1 ↔ 6`, `2 ↔ 3`, `4 ↔ 5`, and
`2i - 1 ↔ 2i` from `7` on. -/
def stdMate (x : ℕ) : ℕ :=
  if x = 1 then 6 else if x = 6 then 1 else if x = 2 then 3 else if x = 3 then 2
  else if x = 4 then 5 else if x = 5 then 4 else if x % 2 = 1 then x + 1 else x - 1

/-- `stdMate` is an involution of the positive labels. -/
theorem stdMate_stdMate {x : ℕ} (hx : 1 ≤ x) : stdMate (stdMate x) = x := by
  rcases Nat.lt_or_ge x 7 with h | h
  · interval_cases x <;> decide
  · have hodd : ∀ y, 7 ≤ y → y % 2 = 1 → stdMate y = y + 1 := fun y hy ho ↦ by
      unfold stdMate
      split_ifs <;> omega
    have heven : ∀ y, 7 ≤ y → y % 2 = 0 → stdMate y = y - 1 := fun y hy he ↦ by
      unfold stdMate
      split_ifs <;> omega
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · rw [heven x h he, hodd (x - 1) (by omega) (by omega)]
      omega
    · rw [hodd x h ho, heven (x + 1) (by omega) (by omega)]
      omega

/-- The standard partial matching of the labels `1, …, 2m - 2`. -/
def stdMatching (m : ℕ) : Finset (Sym2 (Vertex m)) :=
  natMatching m stdMate (Finset.Icc 1 (2 * m - 2))

/-- The partner of a label in the matching for `m = 6`: `1 ↔ 6`, `2 ↔ 4`, `3 ↔ 7`, `5 ↔ 8` and
`9 ↔ 10`. -/
def sixMate (x : ℕ) : ℕ :=
  if x = 1 then 6 else if x = 6 then 1 else if x = 2 then 4 else if x = 4 then 2
  else if x = 3 then 7 else if x = 7 then 3 else if x = 5 then 8 else if x = 8 then 5
  else if x = 9 then 10 else 9

/-- The partial matching of the labels `1, …, 10` for `m = 6`. -/
def sixMatching : Finset (Sym2 (Vertex 6)) :=
  natMatching 6 sixMate (Finset.Icc 1 10)

/-- If `s = a + b` is odd and `s ≡ r`, the members of `[a, b]` pair up as `x ↔ s - x`. -/
theorem forall_exists_Icc {a b r n s : ℕ} (hab : a + b = s) (hs : s % 2 = 1)
    (hr : s = r ∨ s = r + n) :
    ∀ x ∈ Finset.Icc a b, ∃ y ∈ Finset.Icc a b, x ≠ y ∧ (x + y = r ∨ x + y = r + n) := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  exact ⟨s - x, Finset.mem_Icc.mpr (by omega), by omega, by omega⟩

/-- If `a + d = b + c = s` with `a ≠ d`, `b ≠ c` and `s ≡ r`, the members of `{a, b, c, d}`
pair up as `a ↔ d` and `b ↔ c`. -/
theorem forall_exists_four {a b c d r n s : ℕ} (had : a + d = s) (hbc : b + c = s)
    (h1 : a ≠ d) (h2 : b ≠ c) (hr : s = r ∨ s = r + n) :
    ∀ x ∈ ({a, b, c, d} : Finset ℕ), ∃ y ∈ ({a, b, c, d} : Finset ℕ),
      x ≠ y ∧ (x + y = r ∨ x + y = r + n) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨d, by simp, by omega, by omega⟩
  · exact ⟨c, by simp, by omega, by omega⟩
  · exact ⟨b, by simp, by omega, by omega⟩
  · exact ⟨a, by simp, by omega, by omega⟩

variable {m : ℕ} [NeZero m]

/-- A set `C` of finite vertices that is a union of edges of `A`, and that `x ↦ 2t - x` maps
into itself without fixed points, blocks `F_t`. -/
theorem blocks_factor (A : Finset (Sym2 (Vertex m))) (t : ZMod (2 * m - 1))
    (C : Finset (ZMod (2 * m - 1))) (hC : C.Nonempty)
    (hA : ∀ x ∈ C, ∃ y ∈ C, s(some x, some y) ∈ A)
    (hF : ∀ x ∈ C, 2 * t - x ∈ C ∧ 2 * t - x ≠ x) : Blocks A (factor m t) := by
  refine ⟨C.image some, hC.image _, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y, hy, hxy⟩ := hA x hx
    exact ⟨some y, Finset.mem_image_of_mem _ hy, hxy⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have hxt : x ≠ t := by
      rintro rfl
      exact (hF x hx).2 (by ring)
    change mateFn t (some x) ∈ _
    rw [mateFn_of_ne t x hxt]
    exact Finset.mem_image_of_mem _ (hF x hx).1

omit [NeZero m] in
/-- `natMatching m p S` is a partial matching when `p` is a fixed-point-free involution of a set
`S` of labels below `2m - 1`. -/
theorem isPartialMatching_natMatching {p : ℕ → ℕ} {S : Finset ℕ}
    (hS : ∀ x ∈ S, x < 2 * m - 1) (hp : ∀ x ∈ S, p x ∈ S) (hpp : ∀ x ∈ S, p (p x) = x)
    (hne : ∀ x ∈ S, p x ≠ x) : IsPartialMatching (natMatching m p S) := by
  have key : ∀ e ∈ natMatching m p S, ∀ v ∈ e, ∃ k ∈ S, v = some (k : ZMod (2 * m - 1)) ∧
      e = s(some (k : ZMod (2 * m - 1)), some (p k : ZMod (2 * m - 1))) := by
    intro e he v hve
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact ⟨x, hx, rfl, rfl⟩
    · exact ⟨p x, hp x hx, rfl, by rw [hpp x hx, Sym2.eq_swap]⟩
  refine ⟨fun e he ↦ ?_, fun e he f hf v hve hvf ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    rw [Sym2.mk_isDiag_iff, Option.some_inj]
    exact fun h ↦ hne x hx (natCast_injOn (hS _ (hp x hx)) (hS x hx) h.symm)
  · obtain ⟨k, hk, rfl, rfl⟩ := key e he v hve
    obtain ⟨l, hl, hkl, rfl⟩ := key f hf _ hvf
    rw [natCast_injOn (hS k hk) (hS l hl) (Option.some_inj.mp hkl)]

/-- `natMatching m p S` leaves `∞` uncovered. -/
theorem none_mem_uncovered_natMatching (p : ℕ → ℕ) (S : Finset ℕ) :
    (none : Vertex m) ∈ uncovered (natMatching m p S) := by
  rw [mem_uncovered]
  intro e he hv
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
  simp at hv

/-- A set `W` of labels blocks `F_t` in `natMatching m p S` when `W ⊆ S` is closed under `p`
and its members pair up with sum `r` or `r + 2m - 1`, where `r ≡ 2t`. -/
theorem blocks_natMatching {p : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, x < 2 * m - 1)
    (t : ZMod (2 * m - 1)) {r : ℕ} (hr : (r : ZMod (2 * m - 1)) = 2 * t) (W : Finset ℕ)
    (hWS : W ⊆ S) (hW : W.Nonempty) (hpW : ∀ x ∈ W, p x ∈ W)
    (hF : ∀ x ∈ W, ∃ y ∈ W, x ≠ y ∧ (x + y = r ∨ x + y = r + (2 * m - 1))) :
    Blocks (natMatching m p S) (factor m t) := by
  refine blocks_factor _ t (W.image Nat.cast) (hW.image _) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨p k, Finset.mem_image_of_mem _ (hpW k hk), Finset.mem_image.mpr ⟨k, hWS hk, rfl⟩⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, hl, hkl, hsum⟩ := hF k hk
    have hcast : ((k + l : ℕ) : ZMod (2 * m - 1)) = r := by
      rcases hsum with h | h
      · rw [h]
      · rw [h, Nat.cast_add, ZMod.natCast_self, add_zero]
    have h2 : 2 * t - (k : ZMod (2 * m - 1)) = l := by
      rw [← hr, ← hcast]
      push_cast
      ring
    rw [h2]
    exact ⟨Finset.mem_image_of_mem _ hl,
      fun h ↦ hkl (natCast_injOn (hS l (hWS hl)) (hS k (hWS hk)) h).symm⟩

/-- For `m ≥ 7` the standard matching blocks every `F_t`. With `r ≡ 2t` in `[0, 2m - 1)`, the
block is `[1, 2m-2]` for `r = 0`, `[1, r-1]` for odd `r ≥ 7`, `[r+1, 2m-2]` for even
`6 ≤ r ≤ 2m - 4`, and a `4`-cycle or the edge `{2,3}` for `r ∈ {1, 2, 3, 4, 5, 2m - 2}`. -/
theorem blocks_stdMatching (hm : 7 ≤ m) (t : ZMod (2 * m - 1)) :
    Blocks (stdMatching m) (factor m t) := by
  have hS : ∀ x ∈ Finset.Icc 1 (2 * m - 2), x < 2 * m - 1 := fun x hx ↦ by
    rw [Finset.mem_Icc] at hx
    omega
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  generalize (2 * t).val = r at hr hrq
  rcases Nat.even_or_odd' r with ⟨k, rfl | rfl⟩
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ (3 ≤ k ∧ k ≤ m - 2) ∨ k = m - 1) with
      hk | hk | hk | hk | hk
    · refine blocks_natMatching hS t hr (Finset.Icc 1 (2 * m - 2)) subset_rfl
        ⟨1, by simp; omega⟩ ?_ (forall_exists_Icc (s := 2 * m - 1) (by omega) (by omega)
          (by omega))
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      unfold stdMate
      split_ifs <;> omega
    · refine blocks_natMatching hS t hr {7, 8, 2 * m - 7, 2 * m - 6} ?_ ⟨7, by simp⟩ ?_
        (forall_exists_four (s := 2 * m + 1) (by omega) (by omega) (by omega) (by omega)
          (by omega))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr {7, 8, 2 * m - 5, 2 * m - 4} ?_ ⟨7, by simp⟩ ?_
        (forall_exists_four (s := 2 * m + 3) (by omega) (by omega) (by omega) (by omega)
          (by omega))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr (Finset.Icc (2 * k + 1) (2 * m - 2)) ?_
        ⟨2 * m - 2, by simp; omega⟩ ?_ (forall_exists_Icc (s := 2 * k + (2 * m - 1))
          (by omega) (by omega) (by omega))
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr {2, 3, 2 * m - 5, 2 * m - 4} ?_ ⟨2, by simp⟩ ?_
        (forall_exists_four (s := 2 * m - 2) (by omega) (by omega) (by omega) (by omega)
          (by omega))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ (3 ≤ k ∧ k ≤ m - 2)) with hk | hk | hk | hk
    · refine blocks_natMatching hS t hr {2, 3, 2 * m - 3, 2 * m - 2} ?_ ⟨2, by simp⟩ ?_
        (forall_exists_four (s := 2 * m) (by omega) (by omega) (by omega) (by omega)
          (by omega))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr {4, 5, 2 * m - 3, 2 * m - 2} ?_ ⟨4, by simp⟩ ?_
        (forall_exists_four (s := 2 * m + 2) (by omega) (by omega) (by omega) (by omega)
          (by omega))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr (Finset.Icc 2 3) ?_ ⟨2, by simp⟩ ?_
        (forall_exists_Icc (s := 5) (by omega) (by omega) (by omega))
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        unfold stdMate
        split_ifs <;> omega
    · refine blocks_natMatching hS t hr (Finset.Icc 1 (2 * k)) ?_ ⟨1, by simp; omega⟩ ?_
        (forall_exists_Icc (s := 2 * k + 1) (by omega) (by omega) (by omega))
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        unfold stdMate
        split_ifs <;> omega

/-- For `m = 6` the matching `{1,6}, {2,4}, {3,7}, {5,8}, {9,10}` blocks every `F_t`. -/
theorem blocks_sixMatching (t : ZMod (2 * 6 - 1)) : Blocks sixMatching (factor 6 t) := by
  have hS : ∀ x ∈ Finset.Icc 1 10, x < 2 * 6 - 1 := by decide
  have hr := ZMod.natCast_zmod_val (2 * t)
  have hrq := ZMod.val_lt (2 * t)
  generalize (2 * t).val = r at hr hrq
  interval_cases r
  · exact blocks_natMatching hS t hr (Finset.Icc 1 10) (by decide) (by decide) (by decide)
      (by decide)
  · exact blocks_natMatching hS t hr {2, 3, 4, 5, 7, 8, 9, 10} (by decide) (by decide)
      (by decide) (by decide)
  · exact blocks_natMatching hS t hr {5, 8} (by decide) (by decide) (by decide) (by decide)
  · exact blocks_natMatching hS t hr {1, 2, 4, 5, 6, 8, 9, 10} (by decide) (by decide)
      (by decide) (by decide)
  · exact blocks_natMatching hS t hr {1, 3, 5, 6, 7, 8, 9, 10} (by decide) (by decide)
      (by decide) (by decide)
  · exact blocks_natMatching hS t hr {1, 2, 3, 4, 6, 7, 9, 10} (by decide) (by decide)
      (by decide) (by decide)
  · exact blocks_natMatching hS t hr {2, 4} (by decide) (by decide) (by decide) (by decide)
  · exact blocks_natMatching hS t hr {1, 6} (by decide) (by decide) (by decide) (by decide)
  · exact blocks_natMatching hS t hr {9, 10} (by decide) (by decide) (by decide) (by decide)
  · exact blocks_natMatching hS t hr (Finset.Icc 1 8) (by decide) (by decide) (by decide)
      (by decide)
  · exact blocks_natMatching hS t hr {3, 7} (by decide) (by decide) (by decide) (by decide)

/-- For every `m ≥ 6` some partial matching of `V_m` leaves a vertex uncovered and blocks every
canonical factor `F_t`. -/
theorem exists_zeroForcing (hm : 6 ≤ m) : ∃ A : Finset (Sym2 (Vertex m)),
    IsPartialMatching A ∧ (uncovered A).Nonempty ∧ ∀ t, Blocks A (factor m t) := by
  rcases hm.eq_or_lt with rfl | hm7
  · exact ⟨sixMatching, isPartialMatching_natMatching (by decide) (by decide) (by decide)
      (by decide), ⟨none, none_mem_uncovered_natMatching _ _⟩, blocks_sixMatching⟩
  · refine ⟨stdMatching m, isPartialMatching_natMatching (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (fun x hx ↦ stdMate_stdMate (Finset.mem_Icc.mp hx).1) (fun x hx ↦ ?_),
      ⟨none, none_mem_uncovered_natMatching _ _⟩, blocks_stdMatching hm7⟩
    · rw [Finset.mem_Icc] at hx
      omega
    all_goals
      simp only [Finset.mem_Icc] at hx ⊢
      unfold stdMate
      split_ifs <;> omega

/-- A canonical zero state exists for every `m ≥ 6`. -/
theorem nonempty_zeroState (hm : 6 ≤ m) : Nonempty (ZeroState m) := by
  obtain ⟨A, hA, hU, hB⟩ := exists_zeroForcing hm
  obtain ⟨P, hP⟩ := exists_superset (by rw [card_vertex]; exact even_two_mul m) hA
  exact ⟨⟨P, isZeroForcing_of_blocks hU hB P hP⟩⟩

end RoundRobin.Canonical

end Pairing
