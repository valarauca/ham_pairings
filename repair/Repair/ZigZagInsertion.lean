import Repair.FreeDefects
import Repair.CyclicContext

/-!
# Lemma 5 for zig-zag contexts

Positions of defects are natural numbers, and every position `x` carries an entry end `(x, true)`
and an exit end `(x, false)`. For `t ≠ 0` the zig-zag context `C_t(E)` pairs the exit end of
each defect with the entry end of the next defect in `π_t`-order, cyclically. `context E` is that
perfect matching of `ends E = E × {entry, exit}`. Positions do not depend on `E`, so the context of
`E⁻ ∪ {y}` is the context of `E⁻` with the slot `f = {exit(p), entry(q)}` split.

* `context` : the zig-zag context as a perfect matching.
* `zigzag_insertion` : Lemma 5 for zig-zag contexts, stated as in the source.

Source: `results/hybrid-joint-incoherence.md` (organize-archive 4f82c7d), Lemma 5, with the
contexts of `results/hybrid-pair-incoherence.md` §1.
-/

namespace Pairing

namespace CyclicContext

open PerfectMatching

/-- `V(E)`: each position carries an entry end (`true`) and an exit end (`false`).
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
abbrev ends (E : Finset ℕ) : Finset (ℕ × Bool) := E ×ˢ Finset.univ

/-- The context pairs `exit(x)` with `entry(cnext x)` and `entry(x)` with `exit(cprev x)`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def ctxFun (E : Finset ℕ) (v : ℕ × Bool) : ℕ × Bool :=
  if v.2 then (cprev E v.1, false) else (cnext E v.1, true)

/-- The context maps `V(E)` into itself.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem ctxFun_mem {E : Finset ℕ} {v : ℕ × Bool} (hv : v ∈ ends E) : ctxFun E v ∈ ends E := by
  rw [Finset.mem_product] at hv
  unfold ctxFun
  split_ifs
  · exact Finset.mem_product.mpr ⟨cprev_mem hv.1, Finset.mem_univ _⟩
  · exact Finset.mem_product.mpr ⟨cnext_mem hv.1, Finset.mem_univ _⟩

/-- The context is an involution on `V(E)`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem ctxFun_ctxFun {E : Finset ℕ} {v : ℕ × Bool} (hv : v ∈ ends E) :
    ctxFun E (ctxFun E v) = v := by
  rw [Finset.mem_product] at hv
  obtain ⟨x, b⟩ := v
  cases b <;> simp [ctxFun, cnext_cprev hv.1, cprev_cnext hv.1]

/-- The zig-zag context `C_t(E)` as a perfect matching of `V(E)`
(`results/hybrid-pair-incoherence.md` §1, contexts). -/
def context (E : Finset ℕ) : PerfectMatching (ends E) where
  mate := Function.Involutive.toPerm (fun v ↦ ⟨ctxFun E v, ctxFun_mem v.2⟩)
    (fun v ↦ Subtype.ext (ctxFun_ctxFun v.2))
  mate_mate v := Subtype.ext (ctxFun_ctxFun v.2)
  mate_ne v h := by
    have h' := congrArg (fun z : ends E ↦ (z : ℕ × Bool).2) h
    obtain ⟨⟨x, b⟩, _⟩ := v
    cases b <;> simp [ctxFun] at h'

/-- Partners in the zig-zag context.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem context_mate (E : Finset ℕ) (v : ends E) :
    ((context E).mate v : ℕ × Bool) = ctxFun E v :=
  rfl

variable {Em : Finset ℕ} {y : ℕ}

/-- `V(E⁻)` as the lower vertex set `V(E⁻ ∪ {y}) ∖ {entry(y), exit(y)}` of Lemma 5.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
def lowerEquiv (hy : y ∉ Em) : ends Em ≃
    lowerSet (V := ends (insert y Em))
      ⟨(y, true), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩
      ⟨(y, false), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩ where
  toFun v := ⟨⟨v, Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem
      (Finset.mem_product.mp v.2).1, Finset.mem_univ _⟩⟩, mem_lowerSet.mpr
    ⟨fun h ↦ hy (by
        have := congrArg (fun z : ends (insert y Em) ↦ (z : ℕ × Bool).1) h
        simp only at this
        rw [← this]
        exact (Finset.mem_product.mp v.2).1),
      fun h ↦ hy (by
        have := congrArg (fun z : ends (insert y Em) ↦ (z : ℕ × Bool).1) h
        simp only at this
        rw [← this]
        exact (Finset.mem_product.mp v.2).1)⟩⟩
  invFun w := ⟨w.1, by
    have h1 := (mem_lowerSet.mp w.2).1
    have h2 := (mem_lowerSet.mp w.2).2
    obtain ⟨⟨⟨x, b⟩, hx⟩, _⟩ := w
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_insert.mp (Finset.mem_product.mp hx).1 with h | h
    · exfalso
      subst h
      cases b
      · exact h2 rfl
      · exact h1 rfl
    · exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reachability in the cut graph is transported along `e`.
(`results/hybrid-joint-incoherence.md`, Lemma 5). -/
theorem reachable_cut_congr {W W' : Type*} (e : W ≃ W') (Rm Cm : PerfectMatching W)
    (a b p u v : W) :
    (cutGraph (congr e Rm) (congr e Cm) (e a) (e b) (e p)).Reachable (e u) (e v) ↔
      (cutGraph Rm Cm a b p).Reachable u v := by
  have hadj : ∀ u v, (cutGraph (congr e Rm) (congr e Cm) (e a) (e b) (e p)).Adj (e u) (e v) ↔
      (cutGraph Rm Cm a b p).Adj u v := by
    intro u v
    simp only [cutGraph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, toGraph_adj,
      congr_mate, Equiv.symm_apply_apply, Set.mem_singleton_iff, EmbeddingLike.apply_eq_iff_eq]
    have k : ∀ x y z w : W, s(e x, e y) = s(e z, e w) ↔ s(x, y) = s(z, w) := by
      intro x y z w
      simp only [Sym2.eq_iff, EmbeddingLike.apply_eq_iff_eq]
    rw [k, k]
  have h := reachable_iff_of_retract (G := cutGraph Rm Cm a b p)
    (G' := cutGraph (congr e Rm) (congr e Cm) (e a) (e b) (e p)) e e.symm
    (fun x y hxy ↦ ((hadj x y).mpr hxy).reachable)
    (fun x y hxy ↦ by
      have := (hadj (e.symm x) (e.symm y)).mp (by simpa using hxy)
      exact this.reachable)
    (fun x ↦ by simp) u v
  exact h.symm

/-- **Lemma 5 (insertion of one defect), zig-zag form.** `results/hybrid-joint-incoherence.md`.
Let `y` be a new defect whose position falls in the slot of `p ∈ E⁻`, so that
`f = {exit(p), entry(q)}`, `q = cnext E⁻ p`, is the edge of `C_t(E⁻)` between the two labels
adjacent to `y`. Let `R` have edges `{entry(y), a}`, `{exit(y), b}` and let `R⁻` be `R` with these
replaced by `{a, b}`. Then `κ(R ∪ C_t(E)) − κ(R⁻ ∪ C_t(E⁻))` is `−1` when `f` and `{a, b}` lie on
different cycles of `R⁻ ∪ C_t(E⁻)`. When they lie on one cycle it is `+1` if `exit(p)` is joined
to `a = R(entry(y))` in `(R⁻ ∖ {a, b}) ∪ (C_t(E⁻) ∖ f)` and `0` otherwise, and `exit(p)` is joined
there to exactly one of `a`, `b`, so the two choices of which end of `y` is entered give `0` and
`+1` in some order. -/
theorem zigzag_insertion (hy : y ∉ Em) {p : ℕ} (hp : p ∈ Em) (hb : Between p y (cnext Em p))
    (R : PerfectMatching (ends (insert y Em))) (a b : ends Em)
    (hRa : (R.mate ⟨(y, true), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,
      Finset.mem_univ _⟩⟩ : ℕ × Bool) = a)
    (hRb : (R.mate ⟨(y, false), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,
      Finset.mem_univ _⟩⟩ : ℕ × Bool) = b)
    (Rm : PerfectMatching (ends Em)) (hRab : Rm.mate a = b)
    (hRm : ∀ v, v ≠ a → v ≠ b → (Rm.mate v : ℕ × Bool) = R.mate ⟨v, Finset.mem_product.mpr
      ⟨Finset.mem_insert_of_mem (Finset.mem_product.mp v.2).1, Finset.mem_univ _⟩⟩) :
    (¬(Rm.toGraph ⊔ (context Em).toGraph).Reachable
        ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ a →
      cycleCount R (context (insert y Em)) + 1 = cycleCount Rm (context Em)) ∧
    ((Rm.toGraph ⊔ (context Em).toGraph).Reachable
        ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ a →
      ((cutGraph Rm (context Em) a b ⟨(p, false), Finset.mem_product.mpr
          ⟨hp, Finset.mem_univ _⟩⟩).Reachable
          ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ a →
        cycleCount R (context (insert y Em)) = cycleCount Rm (context Em) + 1) ∧
      (¬(cutGraph Rm (context Em) a b ⟨(p, false), Finset.mem_product.mpr
          ⟨hp, Finset.mem_univ _⟩⟩).Reachable
          ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ a →
        cycleCount R (context (insert y Em)) = cycleCount Rm (context Em)) ∧
      ((cutGraph Rm (context Em) a b ⟨(p, false), Finset.mem_product.mpr
          ⟨hp, Finset.mem_univ _⟩⟩).Reachable
          ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ a ↔
        ¬(cutGraph Rm (context Em) a b ⟨(p, false), Finset.mem_product.mpr
          ⟨hp, Finset.mem_univ _⟩⟩).Reachable
          ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ b)) := by
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := insert_context hy hp hb
  set e := lowerEquiv hy with he
  set pe : ends Em := ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩⟩ with hpe
  have hy' : (⟨(y, true), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,
      Finset.mem_univ _⟩⟩ : ends (insert y Em)) ≠
      ⟨(y, false), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩ :=
    fun h ↦ by simp at h
  have hCp : (context (insert y Em)).mate (e pe : ends (insert y Em)) =
      ⟨(y, true), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩ :=
    Subtype.ext (by simp [context_mate, ctxFun, e, lowerEquiv, pe, i1])
  have hq : ((congr e (context Em)).mate (e pe) : ends (insert y Em)) =
      ⟨(cnext Em p, true), Finset.mem_product.mpr
        ⟨Finset.mem_insert_of_mem (cnext_mem hp), Finset.mem_univ _⟩⟩ :=
    Subtype.ext (by simp [congr_mate, context_mate, ctxFun, e, lowerEquiv, pe])
  have hCq : (context (insert y Em)).mate ((congr e (context Em)).mate (e pe) :
      ends (insert y Em)) =
      ⟨(y, false), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩ := by
    rw [hq]
    exact Subtype.ext (by simp [context_mate, ctxFun, i4])
  have hC : ∀ v, v ≠ e pe → v ≠ (congr e (context Em)).mate (e pe) →
      (context (insert y Em)).mate (v : ends (insert y Em)) =
        ((congr e (context Em)).mate v : ends (insert y Em)) := by
    intro v h1 h2
    obtain ⟨w, rfl⟩ := e.surjective v
    have hw := Finset.mem_product.mp w.2
    obtain ⟨⟨x, bit⟩, hxw⟩ := w
    rw [congr_mate, Equiv.symm_apply_apply] at h2 ⊢
    apply Subtype.ext
    cases bit
    · have hxp : x ≠ p := fun h ↦ h1 (by subst h; rfl)
      simp [context_mate, ctxFun, e, lowerEquiv, i5 x hw.1 hxp]
    · have hxq : x ≠ cnext Em p := fun h ↦ h2 (by
        subst h
        apply congrArg e
        exact Subtype.ext (by simp [context_mate, ctxFun, pe]))
      simp [context_mate, ctxFun, e, lowerEquiv, i6 x hw.1 hxq]
  have L5 := insertion_cycleCount hy' R (e a) (e b) (Subtype.ext hRa) (Subtype.ext hRb)
    (congr e Rm) (by rw [congr_mate, Equiv.symm_apply_apply, hRab])
    (fun v h1 h2 ↦ by
      rw [congr_mate]
      apply Subtype.ext
      exact hRm (e.symm v) (fun h ↦ h1 (by rw [← h, Equiv.apply_symm_apply]))
        (fun h ↦ h2 (by rw [← h, Equiv.apply_symm_apply])))
    (congr e (context Em)) (e pe) (context (insert y Em)) (Or.inl ⟨rfl, rfl⟩) hCp hCq hC
  have hκ := cycleCount_congr e Rm (context Em)
  have hG := reachable_congr e Rm (context Em) pe a
  have hcut := fun u v ↦ reachable_cut_congr e Rm (context Em) a b pe u v
  obtain ⟨L1, L2, L3⟩ := L5
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← hκ]
    exact L1 (fun h' ↦ h (hG.mp h'))
  · have hr := L2 (hG.mpr h) (e a) (Subtype.ext hRa).symm
    have hd := L3 (hG.mpr h)
    rw [hcut, hcut] at hd
    rw [hcut, hκ] at hr
    exact ⟨hr.1, hr.2, hd⟩

end CyclicContext

end Pairing
