import Clifford.EdgeRelations

/-!
# The dimension of `W_n` (COD-103)

Vertices are `Fin (2n)`. `P0 = {(2a, 2a+1)}`, and gap `j < n - 1` is `{2j+1, 2j+2}`. For
`S ⊆ Fin (n - 1)`, `σ_S` swaps across every gap in `S`, `X_S = σ_S • P0` and `w_S = r_{X_S}`.

* `sigma_mul`, `ρW_sigma_w` : `σ_S σ_T = σ_{S Δ T}`, so gap swaps permute the `w_S`.
* `blockSwap_w` : `ρ((2a 2a+1)) w_S = w_S + ∑_{g ∈ S, g adjacent to a} w_{S \ g}`, from R3.
* `span_w_eq_top` : the `w_S` span `W` (upper bound).
* `H_X` : `H[X_S, X_T] = [S Δ T = univ]`, so the `w_S` are independent (lower bound).
* `wBasis`, `finrank_W_eq` : `dim W_n = 2^(n-1)`, and `cknUpperBound` discharges
  `CKNUpperBound`.
-/

namespace Pairing.PerfectMatching

open Equiv

section Gaps

variable (n : ℕ)

/-- Gap `j` lies in `S`. -/
def GapIn (S : Finset (Fin (n - 1))) (j : ℕ) : Prop :=
  ∃ h : j < n - 1, (⟨j, h⟩ : Fin (n - 1)) ∈ S

instance (S : Finset (Fin (n - 1))) (j : ℕ) : Decidable (GapIn n S j) :=
  inferInstanceAs (Decidable (∃ _ : _, _))

theorem gapIn_symmDiff (S T : Finset (Fin (n - 1))) (j : ℕ) :
    GapIn n (symmDiff S T) j ↔ (GapIn n S j ↔ ¬GapIn n T j) := by
  unfold GapIn
  by_cases h : j < n - 1
  · simp only [h, exists_true_left, Finset.mem_symmDiff]
    tauto
  · simp [h]

theorem gapIn_empty (j : ℕ) : ¬GapIn n ∅ j := by
  simp [GapIn]

theorem gapIn_univ (j : ℕ) : GapIn n Finset.univ j ↔ j < n - 1 := by
  simp [GapIn]

theorem gapIn_val {S : Finset (Fin (n - 1))} {g : Fin (n - 1)} : GapIn n S g ↔ g ∈ S :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨g.2, h⟩⟩

/-- `σ_S` on `ℕ`. -/
def sigmaNat (S : Finset (Fin (n - 1))) (v : ℕ) : ℕ :=
  if v % 2 = 1 ∧ GapIn n S (v / 2) then v + 1
  else if v % 2 = 0 ∧ 0 < v ∧ GapIn n S (v / 2 - 1) then v - 1
  else v

theorem sigmaNat_lt (S : Finset (Fin (n - 1))) {v : ℕ} (hv : v < 2 * n) :
    sigmaNat n S v < 2 * n := by
  unfold sigmaNat GapIn
  split_ifs with h1 h2
  · obtain ⟨_, h, _⟩ := h1
    omega
  · omega
  · exact hv

theorem sigmaNat_sigmaNat (S T : Finset (Fin (n - 1))) (v : ℕ) :
    sigmaNat n S (sigmaNat n T v) = sigmaNat n (symmDiff S T) v := by
  rcases Nat.even_or_odd' v with ⟨k, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [sigmaNat]
    have e1 : 2 * k % 2 = 0 := by omega
    have e2 : 2 * k / 2 - 1 = k - 1 := by omega
    have e3 : (2 * k - 1) % 2 = 1 := by omega
    have e4 : (2 * k - 1) / 2 = k - 1 := by omega
    have e5 : 2 * k - 1 + 1 = 2 * k := by omega
    have e0 : 0 < 2 * k := by omega
    by_cases hT : GapIn n T (k - 1) <;> by_cases hS : GapIn n S (k - 1) <;>
      simp [sigmaNat, e1, e3, e4, e5, e0, hS, hT, gapIn_symmDiff]
  · have e1 : (2 * k + 1) % 2 = 1 := by omega
    have e2 : (2 * k + 1) / 2 = k := by omega
    have e3 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have e4 : (2 * k + 1 + 1) / 2 - 1 = k := by omega
    have e5 : 2 * k + 1 + 1 - 1 = 2 * k + 1 := by omega
    by_cases hT : GapIn n T k <;> by_cases hS : GapIn n S k <;>
      simp [sigmaNat, e1, e2, e3, e4, e5, hS, hT, gapIn_symmDiff]

theorem sigmaNat_empty (v : ℕ) : sigmaNat n ∅ v = v := by
  simp [sigmaNat, gapIn_empty]

/-- `σ_S` on `Fin (2n)`. -/
def sigmaFun (S : Finset (Fin (n - 1))) (v : Fin (2 * n)) : Fin (2 * n) :=
  ⟨sigmaNat n S v, sigmaNat_lt n S v.isLt⟩

theorem sigmaFun_involutive (S : Finset (Fin (n - 1))) : Function.Involutive (sigmaFun n S) := by
  intro v
  apply Fin.ext
  change sigmaNat n S (sigmaNat n S v) = v
  rw [sigmaNat_sigmaNat, symmDiff_self, Finset.bot_eq_empty, sigmaNat_empty]

/-- `σ_S`, the product of the gap swaps in `S`. -/
def sigma (S : Finset (Fin (n - 1))) : Perm (Fin (2 * n)) :=
  Function.Involutive.toPerm _ (sigmaFun_involutive n S)

theorem sigma_val (S : Finset (Fin (n - 1))) (v : Fin (2 * n)) :
    (sigma n S v : ℕ) = sigmaNat n S v :=
  rfl

theorem sigma_mul (S T : Finset (Fin (n - 1))) :
    sigma n S * sigma n T = sigma n (symmDiff S T) := by
  ext v
  simp only [Perm.coe_mul, Function.comp_apply, sigma_val, sigmaNat_sigmaNat]

theorem sigma_empty : sigma n ∅ = 1 := by
  ext v
  simp [sigma_val, sigmaNat_empty]

theorem sigma_mul_self (S : Finset (Fin (n - 1))) : sigma n S * sigma n S = 1 := by
  rw [sigma_mul, symmDiff_self, Finset.bot_eq_empty, sigma_empty]

theorem sigma_inv (S : Finset (Fin (n - 1))) : (sigma n S)⁻¹ = sigma n S :=
  inv_eq_of_mul_eq_one_right (sigma_mul_self n S)

/-- The lower end `2g+1` of gap `g`. -/
def gapLo (g : Fin (n - 1)) : Fin (2 * n) :=
  ⟨2 * g + 1, by have := g.isLt; omega⟩

/-- The upper end `2g+2` of gap `g`. -/
def gapHi (g : Fin (n - 1)) : Fin (2 * n) :=
  ⟨2 * g + 2, by have := g.isLt; omega⟩

theorem sigma_single (g : Fin (n - 1)) : sigma n {g} = swap (gapLo n g) (gapHi n g) := by
  ext v
  rw [sigma_val, swap_apply_def]
  have hg := g.isLt
  have hv := v.isLt
  simp only [sigmaNat, GapIn, Finset.mem_singleton, Fin.ext_iff, gapLo, gapHi, exists_prop]
  split_ifs <;> (try dsimp only at *) <;> omega

/-- `P0 = {(2a, 2a+1)}` on `ℕ`. -/
def p0Nat (v : ℕ) : ℕ :=
  if v % 2 = 0 then v + 1 else v - 1

/-- `P0` on `Fin (2n)`. -/
def p0Fun (v : Fin (2 * n)) : Fin (2 * n) :=
  ⟨p0Nat v, by have := v.isLt; unfold p0Nat; split_ifs <;> omega⟩

theorem p0Fun_involutive : Function.Involutive (p0Fun n) := by
  intro v
  apply Fin.ext
  change p0Nat (p0Nat v) = v
  unfold p0Nat
  split_ifs <;> omega

/-- The base matching `P0 = {(2a, 2a+1)}`. -/
def P0 : PerfectMatching (Fin (2 * n)) where
  mate := Function.Involutive.toPerm _ (p0Fun_involutive n)
  mate_mate := p0Fun_involutive n
  mate_ne v h := by
    have h' : p0Nat v = v := congrArg Fin.val h
    unfold p0Nat at h'
    split_ifs at h' <;> omega

theorem P0_mate_val (v : Fin (2 * n)) : ((P0 n).mate v : ℕ) = p0Nat v :=
  rfl

/-- The basis matching `X_S = σ_S • P0`. -/
def X (S : Finset (Fin (n - 1))) : PerfectMatching (Fin (2 * n)) :=
  sigma n S • P0 n

/-- The basis vector `w_S = r_{X_S}`. -/
def w (S : Finset (Fin (n - 1))) : W (Fin (2 * n)) :=
  rowW (X n S)

theorem w_empty : w n ∅ = rowW (P0 n) := by
  rw [w, X, sigma_empty, one_smul]

theorem ρW_sigma_w (S T : Finset (Fin (n - 1))) : ρW (sigma n T) (w n S) = w n (symmDiff T S) := by
  rw [w, w, X, X, ρW_rowW, smul_smul, sigma_mul]

theorem w_insert {g : Fin (n - 1)} {S : Finset (Fin (n - 1))} (hg : g ∉ S) :
    w n (insert g S) = ρW (sigma n {g}) (w n S) := by
  rw [ρW_sigma_w]
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl ⟨rfl, hg⟩
    · by_cases hxg : x = g
      · exact absurd (hxg ▸ hx) hg
      · exact Or.inr ⟨hx, hxg⟩
  · rintro (⟨rfl, _⟩ | ⟨hx, _⟩)
    · exact Or.inl rfl
    · exact Or.inr hx

end Gaps

section Upper

variable (n : ℕ)

/-- The lower end `2a` of block `a`. -/
def blockLo (a : Fin n) : Fin (2 * n) :=
  ⟨2 * a, by have := a.isLt; omega⟩

/-- The upper end `2a+1` of block `a`. -/
def blockHi (a : Fin n) : Fin (2 * n) :=
  ⟨2 * a + 1, by have := a.isLt; omega⟩

/-- `Γ` of the block edge `(2a, 2a+1)` of `P0`. -/
def B (a : Fin n) : Module.End F₂ (W (Fin (2 * n))) :=
  Γ (blockLo n a) (blockHi n a)

theorem P0_mate_blockLo (a : Fin n) : (P0 n).mate (blockLo n a) = blockHi n a := by
  apply Fin.ext
  rw [P0_mate_val]
  simp [blockLo, blockHi, p0Nat]

theorem B_rowW_P0 (a : Fin n) : B n a (rowW (P0 n)) = rowW (P0 n) := by
  rw [B, Γ, ρW_rowW, ← P0_mate_blockLo, swap_mate_smul]

theorem Γ_gap (g : Fin (n - 1)) : Γ (gapLo n g) (gapHi n g) = ρW (sigma n {g}) := by
  rw [sigma_single, Γ]

/-- A block edge and a gap edge anticommute to `I` when adjacent and commute otherwise. -/
theorem B_mul_sigma (a : Fin n) (g : Fin (n - 1)) :
    B n a * ρW (sigma n {g}) = ρW (sigma n {g}) * B n a +
      (if (g : ℕ) = a ∨ (g : ℕ) + 1 = a then 1 else 0) := by
  have hg := g.isLt
  have ha := a.isLt
  rw [← Γ_gap, B]
  split_ifs with hadj
  · have hanti : Γ (blockLo n a) (blockHi n a) * Γ (gapLo n g) (gapHi n g) +
        Γ (gapLo n g) (gapHi n g) * Γ (blockLo n a) (blockHi n a) = 1 := by
      rcases hadj with h | h
      · have e : gapLo n g = blockHi n a := Fin.ext (by simp [gapLo, blockHi, h])
        rw [e]
        exact Γ_anticomm_of_adj (Fin.ne_of_val_ne (by simp [blockLo, blockHi]))
          (Fin.ne_of_val_ne (by simp [blockHi, gapHi]; omega))
          (Fin.ne_of_val_ne (by simp [blockLo, gapHi]; omega))
      · have e : gapHi n g = blockLo n a := Fin.ext (by simp [gapHi, blockLo]; omega)
        rw [e, add_comm]
        exact Γ_anticomm_of_adj (Fin.ne_of_val_ne (by simp [gapLo, blockLo]; omega))
          (Fin.ne_of_val_ne (by simp [blockLo, blockHi]))
          (Fin.ne_of_val_ne (by simp [gapLo, blockHi]; omega))
    calc Γ (blockLo n a) (blockHi n a) * Γ (gapLo n g) (gapHi n g)
        = Γ (blockLo n a) (blockHi n a) * Γ (gapLo n g) (gapHi n g) +
          (Γ (gapLo n g) (gapHi n g) * Γ (blockLo n a) (blockHi n a) +
            Γ (gapLo n g) (gapHi n g) * Γ (blockLo n a) (blockHi n a)) := by
          rw [end_add_self, add_zero]
      _ = Γ (gapLo n g) (gapHi n g) * Γ (blockLo n a) (blockHi n a) + 1 := by
          rw [← hanti]
          abel
  · rw [add_zero]
    apply Γ_mul_comm_of_disjoint
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, not_or, Fin.ext_iff, blockLo, blockHi, gapLo, gapHi, not_false_eq_true]
    omega

/-- The block swap on the basis, from R3. -/
theorem B_w (a : Fin n) (S : Finset (Fin (n - 1))) :
    B n a (w n S) = w n S +
      ∑ g ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a), w n (S.erase g) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [w_empty, B_rowW_P0]
    simp
  | insert g S hg ih =>
    have hsum : ∑ h ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a),
        w n ((insert g S).erase h) =
        ∑ h ∈ S.filter (fun g : Fin (n - 1) ↦ (g : ℕ) = a ∨ (g : ℕ) + 1 = a),
          ρW (sigma n {g}) (w n (S.erase h)) := by
      refine Finset.sum_congr rfl fun h hh ↦ ?_
      have hS : h ∈ S := (Finset.mem_filter.mp hh).1
      have hne : g ≠ h := fun e ↦ hg (e ▸ hS)
      rw [Finset.erase_insert_of_ne hne,
        w_insert n (fun hm ↦ hg (Finset.mem_of_mem_erase hm))]
    rw [w_insert n hg, ← Module.End.mul_apply, B_mul_sigma, LinearMap.add_apply,
      Module.End.mul_apply, ih, map_add, map_sum, Finset.filter_insert]
    split_ifs with hadj
    · rw [Finset.sum_insert (fun hm ↦ hg (Finset.mem_filter.mp hm).1), Finset.erase_insert hg,
        hsum, Module.End.one_apply]
      abel
    · rw [hsum, LinearMap.zero_apply]
      abel

/-- The span of the `w_S`. -/
def Wspan : Submodule F₂ (W (Fin (2 * n))) :=
  Submodule.span F₂ (Set.range (w n))

theorem w_mem (S : Finset (Fin (n - 1))) : w n S ∈ Wspan n :=
  Submodule.subset_span ⟨S, rfl⟩

private theorem pres_of_gen {f : Module.End F₂ (W (Fin (2 * n)))}
    (h : ∀ S, f (w n S) ∈ Wspan n) : ∀ x ∈ Wspan n, f x ∈ Wspan n := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    exact h S
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

theorem pres_adj (t : ℕ) (ht : t + 1 < 2 * n) :
    ∀ x ∈ Wspan n, Γ (⟨t, by omega⟩ : Fin (2 * n)) ⟨t + 1, ht⟩ x ∈ Wspan n := by
  apply pres_of_gen
  intro S
  rcases Nat.even_or_odd' t with ⟨a, rfl | rfl⟩
  · have ha : a < n := by omega
    have e : Γ (⟨2 * a, by omega⟩ : Fin (2 * n)) ⟨2 * a + 1, ht⟩ = B n ⟨a, ha⟩ := rfl
    rw [e, B_w]
    exact add_mem (w_mem n S) (Submodule.sum_mem _ fun g _ ↦ w_mem n _)
  · have ha : a < n - 1 := by omega
    have e : Γ (⟨2 * a + 1, by omega⟩ : Fin (2 * n)) ⟨2 * a + 1 + 1, ht⟩ =
        ρW (sigma n {⟨a, ha⟩}) := by
      rw [← Γ_gap]
      rfl
    rw [e, ρW_sigma_w]
    exact w_mem n _

theorem pres_Γ (i j : Fin (2 * n)) : ∀ x ∈ Wspan n, Γ i j x ∈ Wspan n := by
  have key : ∀ d i (h : i + d + 1 < 2 * n),
      ∀ x ∈ Wspan n, Γ (⟨i, by omega⟩ : Fin (2 * n)) ⟨i + d + 1, h⟩ x ∈ Wspan n := by
    intro d
    induction d with
    | zero => exact fun i h ↦ pres_adj n i h
    | succ d ih =>
      intro i h x hx
      have hsplit : Γ (⟨i, by omega⟩ : Fin (2 * n)) ⟨i + (d + 1) + 1, h⟩ =
          Γ (⟨i, by omega⟩ : Fin (2 * n)) ⟨i + d + 1, by omega⟩ +
            Γ (⟨i + d + 1, by omega⟩ : Fin (2 * n)) ⟨i + d + 1 + 1, by omega⟩ :=
        Γ_eq_add (by simp only [ne_eq, Fin.mk.injEq]; omega)
          (by simp only [ne_eq, Fin.mk.injEq]; omega) (by simp only [ne_eq, Fin.mk.injEq]; omega)
      rw [hsplit, LinearMap.add_apply]
      exact add_mem (ih i (by omega) x hx) (pres_adj n (i + d + 1) (by omega) x hx)
  rcases lt_trichotomy i j with h | rfl | h
  · obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have hlt : i < j := h
    have e : (⟨j, hj⟩ : Fin (2 * n)) = ⟨i + (j - i - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact key (j - i - 1) i (by omega)
  · intro x hx
    rw [Γ, swap_self, ← Perm.one_def, map_one]
    exact hx
  · rw [Γ_comm]
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have hlt : j < i := h
    have e : (⟨i, hi⟩ : Fin (2 * n)) = ⟨j + (i - j - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact key (i - j - 1) j (by omega)

theorem pres_ρW (σ : Perm (Fin (2 * n))) : ∀ x ∈ Wspan n, ρW σ x ∈ Wspan n := by
  have hσ : σ ∈ Submonoid.closure {τ : Perm (Fin (2 * n)) | τ.IsSwap} := by
    rw [Perm.mclosure_isSwap]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, j, -, rfl⟩ := hτ
    exact pres_Γ n i j
  | one =>
    intro x hx
    rw [map_one]
    exact hx
  | mul τ τ' _ _ h h' =>
    intro x hx
    rw [map_mul, Module.End.mul_apply]
    exact h _ (h' x hx)

/-- Upper bound, the `w_S` span `W`. -/
theorem span_w_eq_top : Wspan n = ⊤ := by
  rw [eq_top_iff, ← span_rowW, Submodule.span_le]
  rintro _ ⟨P, rfl⟩
  obtain ⟨c, rfl⟩ := exists_smul_eq (n := n) (by simp) (P0 n) P
  rw [← ρW_rowW, ← w_empty]
  exact pres_ρW n c _ (w_mem n ∅)

theorem finrank_W_le : Module.finrank F₂ (W (Fin (2 * n))) ≤ 2 ^ (n - 1) := by
  rw [← finrank_top F₂ (W (Fin (2 * n))), ← span_w_eq_top n]
  calc Module.finrank F₂ (Wspan n) ≤ Fintype.card (Finset (Fin (n - 1))) :=
        finrank_range_le_card _
    _ = 2 ^ (n - 1) := by simp

end Upper

section Lower

variable (n : ℕ)

theorem X_mate (S : Finset (Fin (n - 1))) (v : Fin (2 * n)) :
    (X n S).mate v = sigma n S ((P0 n).mate (sigma n S v)) := by
  rw [X, smul_mate, sigma_inv]

/-- `H[X_S, X_T] = H[P0, X_{S Δ T}]`. -/
theorem H_X_eq (S T : Finset (Fin (n - 1))) :
    H (X n S) (X n T) = H (P0 n) (X n (symmDiff S T)) := by
  rw [← H_smul (sigma n S) (P0 n) (X n (symmDiff S T))]
  simp only [X, smul_smul, sigma_mul, symmDiff_symmDiff_cancel_left]

/-- If gap `g ∉ U`, the blocks up to `g` are closed under `P0` and `X_U`. -/
theorem not_ham_P0_X {U : Finset (Fin (n - 1))} (hU : U ≠ Finset.univ) : ¬Ham (P0 n) (X n U) := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ U := by
    by_contra! h
    exact hU (Finset.eq_univ_of_forall h)
  have hgl := g.isLt
  have hσ : ∀ v : Fin (2 * n), ((sigma n U v : ℕ) ≤ 2 * g + 1 ↔ (v : ℕ) ≤ 2 * g + 1) := by
    intro v
    rw [sigma_val]
    unfold sigmaNat
    split_ifs with h1 h2
    · obtain ⟨_, hgi⟩ := h1
      have hne : (v : ℕ) ≠ 2 * g + 1 := by
        intro hv
        rw [hv, show (2 * (g : ℕ) + 1) / 2 = g by omega] at hgi
        exact hg ((gapIn_val n).mp hgi)
      omega
    · obtain ⟨_, _, hgi⟩ := h2
      have hne : (v : ℕ) ≠ 2 * g + 2 := by
        intro hv
        rw [hv, show (2 * (g : ℕ) + 2) / 2 - 1 = g by omega] at hgi
        exact hg ((gapIn_val n).mp hgi)
      omega
    · rfl
  have hp : ∀ v : Fin (2 * n), (((P0 n).mate v : ℕ) ≤ 2 * g + 1 ↔ (v : ℕ) ≤ 2 * g + 1) := by
    intro v
    rw [P0_mate_val]
    unfold p0Nat
    split_ifs <;> omega
  refine not_ham_of_closed (P0 n) (X n U) {v | (v : ℕ) ≤ 2 * g + 1}
    (fun v hv ↦ (hp v).mpr hv) (fun v hv ↦ ?_) (u := ⟨0, by omega⟩)
    (w := ⟨2 * n - 1, by omega⟩) (by simp) (by change ¬(2 * n - 1 ≤ 2 * (g : ℕ) + 1); omega)
  change ((X n U).mate v : ℕ) ≤ 2 * g + 1
  change (v : ℕ) ≤ 2 * g + 1 at hv
  rw [X_mate]
  exact (hσ _).mpr ((hp _).mpr ((hσ v).mpr hv))

/-- `P0 ∪ X_univ` is one cycle. -/
theorem ham_P0_X_univ (hn : 1 ≤ n) : Ham (P0 n) (X n Finset.univ) := by
  have hX : ∀ v : Fin (2 * n), ((X n Finset.univ).mate v : ℕ) =
      sigmaNat n Finset.univ (p0Nat (sigmaNat n Finset.univ v)) := fun v ↦ by
    rw [X_mate, sigma_val, P0_mate_val, sigma_val]
  have step : ∀ b : ℕ, ∀ hb : b < n,
      ((P0 n).toGraph ⊔ (X n Finset.univ).toGraph).Reachable ⟨0, by omega⟩ ⟨2 * b, by omega⟩ ∧
      ((P0 n).toGraph ⊔ (X n Finset.univ).toGraph).Reachable ⟨0, by omega⟩
        ⟨2 * b + 1, by omega⟩ := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro hb
      have hev : ((P0 n).toGraph ⊔ (X n Finset.univ).toGraph).Reachable ⟨0, by omega⟩
          ⟨2 * b, by omega⟩ := by
        rcases b with _ | _ | b
        · exact SimpleGraph.Reachable.refl _
        · have e : (X n Finset.univ).mate ⟨0, by omega⟩ = ⟨2 * (0 + 1), by omega⟩ := by
            apply Fin.ext
            rw [hX]
            simp only [sigmaNat, p0Nat, gapIn_univ]
            split_ifs <;> simp_all
          rw [← e]
          exact (adj_mate_right _ _ _).reachable
        · obtain ⟨-, hr⟩ := ih b (by omega) (by omega)
          have e : (X n Finset.univ).mate ⟨2 * b + 1, by omega⟩ = ⟨2 * (b + 1 + 1), by omega⟩ := by
            apply Fin.ext
            rw [hX]
            simp only [sigmaNat, p0Nat, gapIn_univ]
            split_ifs <;> (try simp_all) <;> omega
          rw [← e]
          exact hr.trans (adj_mate_right _ _ _).reachable
      refine ⟨hev, hev.trans ?_⟩
      have e : (P0 n).mate ⟨2 * b, by omega⟩ = ⟨2 * b + 1, by omega⟩ := by
        apply Fin.ext
        rw [P0_mate_val]
        simp [p0Nat]
      rw [← e]
      exact (adj_mate_left _ _ _).reachable
  have hreach : ∀ v : Fin (2 * n),
      ((P0 n).toGraph ⊔ (X n Finset.univ).toGraph).Reachable ⟨0, by omega⟩ v := by
    intro v
    obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' (v : ℕ)
    · have e : v = ⟨2 * b, by omega⟩ := Fin.ext hb
      rw [e]
      exact (step b (by omega)).1
    · have e : v = ⟨2 * b + 1, by omega⟩ := Fin.ext hb
      rw [e]
      exact (step b (by omega)).2
  rw [Ham, SimpleGraph.connected_iff]
  exact ⟨fun u v ↦ (hreach u).symm.trans (hreach v), ⟨⟨0, by omega⟩⟩⟩

theorem H_P0_X (hn : 1 ≤ n) (U : Finset (Fin (n - 1))) :
    H (P0 n) (X n U) = if U = Finset.univ then 1 else 0 := by
  by_cases hU : U = Finset.univ
  · subst hU
    simp [H_apply, ham_P0_X_univ n hn]
  · simp [H_apply, hU, not_ham_P0_X n hU]

theorem symmDiff_compl_eq_univ (S T : Finset (Fin (n - 1))) :
    symmDiff S Tᶜ = Finset.univ ↔ S = T := by
  constructor
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    simp only [Finset.mem_symmDiff, Finset.mem_compl, Finset.mem_univ, iff_true] at hx
    tauto
  · rintro rfl
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_compl, Finset.mem_univ, iff_true]
    tauto

/-- Gram identity, `H[X_S, X_T] = [S Δ T = univ]`. -/
theorem H_X (hn : 1 ≤ n) (S T : Finset (Fin (n - 1))) :
    H (X n S) (X n T) = if symmDiff S T = Finset.univ then 1 else 0 := by
  rw [H_X_eq, H_P0_X n hn]

/-- Lower bound, the `w_S` are linearly independent. -/
theorem linearIndependent_w (hn : 1 ≤ n) : LinearIndependent F₂ (w n) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc T
  have h := congrArg
    (fun f : W (Fin (2 * n)) ↦ (f : PerfectMatching (Fin (2 * n)) → F₂) (X n Tᶜ)) hc
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ZeroMemClass.coe_zero, Pi.zero_apply, w, coe_rowW, H_X n hn, symmDiff_compl_eq_univ,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

/-- The basis `{w_S}` of `W_n`, indexed by subsets of the `n - 1` gaps. -/
noncomputable def wBasis (hn : 1 ≤ n) : Module.Basis (Finset (Fin (n - 1))) F₂ (W (Fin (2 * n))) :=
  Module.Basis.mk (linearIndependent_w n hn) (span_w_eq_top n).ge

theorem wBasis_apply (hn : 1 ≤ n) (S : Finset (Fin (n - 1))) : wBasis n hn S = w n S :=
  Module.Basis.mk_apply _ _ _

/-- COD-103. `dim W_n = 2^(n-1)`. -/
theorem finrank_W_eq (hn : 1 ≤ n) : Module.finrank F₂ (W (Fin (2 * n))) = 2 ^ (n - 1) := by
  rw [Module.finrank_eq_card_basis (wBasis n hn)]
  simp

/-- `rank_{𝔽₂} H_{2n} = 2^(n-1)`. -/
theorem rank_H_eq (hn : 1 ≤ n) : (H (V := Fin (2 * n))).rank = 2 ^ (n - 1) := by
  rw [← finrank_W, finrank_W_eq n hn]

/-- The former `[EXT: CKN]` hypothesis, now proved. -/
theorem cknUpperBound : CKNUpperBound n := by
  unfold CKNUpperBound
  rw [← finrank_W]
  exact finrank_W_le n

end Lower

end Pairing.PerfectMatching
