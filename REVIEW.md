# Review of the Lean repo at 4a31a12

Files added after `4a31a12` were not reviewed. In ham_pairings (main 81fccb6) these are
`repair/Repair/Barrier/*`, `repair/Repair/Cover/*`, `repair/Repair/Reflection.lean` and
`repair/Repair/Translation.lean`. In ham-spin (0360f0d) they are
`clifford/Clifford/BasisFree.lean` and `spin/Spin/BasisFree.lean`. The dry run of section 6, first
made on branch `lean-review` (a955aa4), is replayed on ham_pairings branch `review-main` and
ham-spin branch `review-spin`.

Read-only review of the five libraries Pairing (`core/`), Clifford (`clifford/`), Spin (`spin/`),
Suppression (`suppression/`) and Repair (`repair/`) at commit `4a31a12` on `main`, with 813
endpoints in `AxiomCheck.lean`.

Every citation has the form `sha:path:line` and names a symbol, so `git show sha:path` shows the
cited text. Since COD-257, `core/`, `clifford/` and `spin/` live in `valarauca/ham-spin`, so their
citations and the one of its `AxiomCheck.lean` use ham-spin `0360f0d`. The other citations keep
ham_pairings `4a31a12`, whose cited files have the same lines at main `81fccb6`. Lines are those of
these base commits, not of later commits on `review-main` or `review-spin`. `results/X.md` means
`organize-archive/results/X.md`.

Method. A full build at `4a31a12` (97 warnings, all style or module-system notes), the Batteries
`unusedArguments` linter over all five libraries, the build's `unusedDecidableInType` and
`unusedFintypeInType` warnings, a token-level usage scan of every declaration across all `.lean`
files, `AxiomCheck.lean` and `results/*.md`, and a reading of the statements and proofs of the
main theorems. The satisfiability instances of section 2 are compiled in `VacuityCheck.lean` at
the root, which runs like `AxiomCheck.lean` (`lake env lean VacuityCheck.lean`).

## Summary

| category | findings | done in the dry run | left for the user |
|---|---|---|---|
| duplicates and near-duplicates | 56 | 5 | 51 |
| vacuous, bogus or weak statements | 11 | 0 | 11 |
| over-restricted hypotheses | 34 | 6 | 28 |
| unused code | 9 | 1 | 8 |

Most serious.

1. `HybridConditional.hybrid_theorem1` (`4a31a12:repair/Repair/HybridConditional.lean:702`) is
   empty at its intended instance for every large `m`. In Lean it is not vacuous, only because
   the law, the event and `PH` are free variables with no tie to the hybrid (section 2.1).
2. `HybridConditional.prob_le_of_tilt` (`4a31a12:repair/Repair/HybridConditional.lean:433`) has
   the hypothesis (H-T), which is false at its intended instance once `(1 - δ)ε > 8√2`
   (section 2.2).
3. No theorem has unsatisfiable hypotheses in Lean, and none is proved by unfolding a
   definition that already contains its conclusion. Every conditional endpoint checked has a
   compiled instance in `VacuityCheck.lean`.
4. Theorem 7 of COD-196 is stated three times with identical types, and five Tilt endpoints are
   wrappers that add unused hypotheses (section 1.2). These inflate `AxiomCheck.lean`.
5. FGPT appears nowhere in this repo (section 4, FGPT).

## 1. Duplicates and near-duplicates

### 1.1 The known collisions

- **D1. `cycleCount`.** One definition remains,
  `PerfectMatching.cycleCount` (`4a31a12:repair/Repair/CycleCount.lean:37`). The copy in
  `Insertion.lean` was dropped in d2276f6. Left over are
  `ham_iff_cycleCount_eq_one` (`4a31a12:repair/Repair/CycleCount.lean:49`, needs
  `[Nonempty V]`) and `ham_iff_cycleCount_eq_one'` (`4a31a12:repair/Repair/Insertion.lean:218`,
  the same statement without it), plus `cycleCount_comm`
  (`4a31a12:repair/Repair/Insertion.lean:212`), which belongs with the definition. **Done.**
- **D2. `not_ham_of_mate_eq`** (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:135`) and
  `not_ham_of_mate_eq_of_two_lt` (`4a31a12:repair/Repair/PairRecursion.lean:580`). The second is
  a corollary, not a duplicate. It trades the witness `w ∉ {a, P a}` for `2 < card V`. The true
  duplicate is `not_ham_self` (`4a31a12:repair/Repair/Covering/Basic.lean:200`), which is
  `not_ham_of_mate_eq rfl`. All three only need `not_ham_of_closed`
  (`0360f0d:core/Pairing/Basic.lean:123`). **Done** (both moved to `core/Pairing/Basic.lean`).
- **D3. `jointCount` and `hamPairCount`.** `hamPairCount` was merged into `jointCount`
  (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:266`) in e5511e3 and is gone. Remaining
  overlap: `hamDeg` (`4a31a12:repair/Repair/PairVariance.lean:147`) is `jointCount B B` by
  `and_self`, and `hamDeg_eq_closed` (`4a31a12:repair/Repair/PairVariance.lean:354`) reproves
  `card_ham_eq` (`4a31a12:repair/Repair/DensityGlue.lean:157`).

### 1.2 Suppression

- **D4.** `hamEvent` (`4a31a12:suppression/Suppression/ChainRule.lean:2045`) and `hamFamily`
  (`4a31a12:repair/Repair/SqrtObstructions/Hole.lean:113`) have the same body and full
  namespace. `Hole.lean` mixes both. `hamFinset`
  (`4a31a12:repair/Repair/SqrtObstructions/LocalFloor.lean:131`) is the Finset copy. **Done.**
- **D5. Theorem 7 of COD-196, three times.** `ChainRule.div_le_neg_log_prob_avoid`
  (`4a31a12:suppression/Suppression/ChainRule.lean:1523`),
  `div_le_neg_log_prob_avoid_of_reweight` (`4a31a12:suppression/Suppression/Reweighted.lean:1313`)
  and `div_le_neg_log_prob_avoid_of_reweight'` (`4a31a12:suppression/Suppression/VMinus.lean:636`)
  have identical types. So do `neg_log_prob_avoid_le_div`
  (`4a31a12:suppression/Suppression/ChainRule.lean:1539`), `..._of_reweight`
  (`4a31a12:suppression/Suppression/Reweighted.lean:1358`) and `..._of_reweight'`
  (`4a31a12:suppression/Suppression/VMinus.lean:654`), and the `_of_pairInfo` pairs
  (`4a31a12:suppression/Suppression/ChainRule.lean:1850`, `:1860`,
  `4a31a12:suppression/Suppression/Reweighted.lean:1415`, `:1424`). The proofs differ (through
  Proposition 6 or Theorem 3), so merging drops an alternative proof. The `_harmonic` forms
  (`4a31a12:suppression/Suppression/VMinus.lean:510`, `:556`, `:612`, `:624`) dominate all of
  them.
- **D6. Tilt wrappers.** `fano_criterion` (`4a31a12:suppression/Suppression/Tilt.lean:470`) is
  `exp_neg_div_le_of_fano_le` (`:444`) plus unused `_hp0 _hk`. Likewise
  `le_exp_neg_of_fano_nonneg` (`:505`) and `le_exp_neg_div_of_le_fano` (`:483`), `sbRatio_le`
  (`:629`) and `sbRatio_le_of_pairDeficit_le` (`:612`), `pair_criterion` (`:678`) and
  `exp_neg_mul_log_le_of_pairDeficit_le` (`:648`), `pair_criterion_weak` (`:701`) and
  `exp_neg_div_le_of_pairDeficit_le` (`:685`), and `RoundRobin.Canonical.fano_hamLaw` (`:819`)
  and `fano_hamLaw'` (`:777`).
- **D7. SizeBias dominated forms.** `upper_reduction`
  (`4a31a12:suppression/Suppression/SizeBias.lean:292`) and `upper_reduction_sqrt` (`:321`) are
  dominated by the `_of_le_add_two` forms, and `upper_reduction_of_le_add_two` (`:279`) by
  `upper_reduction_sqrt_of_le_add_two` (`:301`).
- **D8. ChainRule `p′ = p` specializations.** `mul_le_condProb`
  (`4a31a12:suppression/Suppression/ChainRule.lean:385`) of `mul_le_condProb_of_le` (`:372`), and
  `mul_pow_le_condProb` (`:594`), `pow_mul_le_condProb` (`:631`), `prob_avoid_le_pow` (`:669`),
  `prob_avoid_le_exp` (`:715`), `mul_le_condProb_pre` (`:911`) and `prob_avoid_le_pow_of_pre`
  (`:951`) of their `_of_mem_Icc` twins.
- **D9.** `card_le_card_mul_of_cover` (`4a31a12:suppression/Suppression/Density.lean:32`) is
  `card_le_sum_of_cover` (`4a31a12:suppression/Suppression/Layered.lean:501`) plus `sum_le_sum`,
  with copied steps.
- **D10.** `card_closed_le` (`4a31a12:suppression/Suppression/Density.lean:155`) is the
  `B = univ` case of `card_closed_subset` (`4a31a12:suppression/Suppression/Layered.lean:212`).
- **D11. Double-factorial identities.** `doubleFactorial_two_mul_sub_one_eq`
  (`4a31a12:suppression/Suppression/Density.lean:363`) is
  `doubleFactorial_two_mul_add_five` (`4a31a12:repair/Repair/HybridConditional.lean:60`) at
  `m = j + 3`, and overlaps `doubleFactorial_sub_three` and `doubleFactorial_sub_one`
  (`4a31a12:repair/Repair/PairLevelOne.lean:386`, `:395`).
- **D12. The count `X`.** `eventCount` (`4a31a12:suppression/Suppression/Reweighted.lean:65`)
  and `eventNum` (`4a31a12:suppression/Suppression/VMinus.lean:246`) are one function in ℝ and ℕ.
  `hamCount` (`4a31a12:suppression/Suppression/HamCount.lean:79`) is `eventNum (hamEvent m)` and
  `ctxCount (factor m)` (`4a31a12:repair/Repair/PairVariance.lean:165`). `lawOf_eventNum_zero`
  (`4a31a12:suppression/Suppression/VMinus.lean:305`) generalizes `prob_avoid_hamEvent`
  (`4a31a12:suppression/Suppression/ChainRule.lean:2060`).
- **D13.** `mismatch (Equiv.refl _)` (`4a31a12:suppression/Suppression/CouplingObstruction.lean:150`)
  is `(defect M N).card` (`4a31a12:suppression/Suppression/Density.lean:88`).
- **D14.** `reidCount_ne_one`
  (`4a31a12:suppression/Suppression/CouplingObstruction.lean:462`) is Mathlib
  `Equiv.Perm.card_support_ne_one`.
- **D15. Harmonic and reindexing helpers.** `harmonic_le_log`
  (`4a31a12:suppression/Suppression/VMinus.lean:463`) and `sum_inv_add_two_le_log`
  (`4a31a12:suppression/Suppression/ChainRule.lean:1322`) are one inequality, close to Mathlib
  `harmonic_le_one_add_log`. `sum_range_reflect_two`
  (`4a31a12:suppression/Suppression/ChainRule.lean:1316`), `sum_range_reflect_one`
  (`4a31a12:suppression/Suppression/Reweighted.lean:941`) and `sum_Icc_two_eq`
  (`4a31a12:suppression/Suppression/VMinus.lean:456`) are `Finset.sum_range_reflect` instances.
  `sum_corr_le` (`4a31a12:suppression/Suppression/ChainRule.lean:1347`) and `sum_corrLevel_le`
  (`4a31a12:suppression/Suppression/Reweighted.lean:1227`) are dominated by their `_harmonic`
  forms (`4a31a12:suppression/Suppression/VMinus.lean:474`, `:490`).
- **D16. Mathlib re-inventions.** `descFactorial_pos_of_le`
  (`4a31a12:suppression/Suppression/MixtureBarrier.lean:122`) is `Nat.descFactorial_pos`.
  `sum_mul_pow_eq` (`4a31a12:suppression/Suppression/SizeBias.lean:112`) is
  `Finset.sum_range_by_parts`. `monotoneOn_Ioc_of_hasDerivAt`
  (`4a31a12:suppression/Suppression/Tilt.lean:317`) wraps `monotoneOn_of_deriv_nonneg`.
- **D17.** `unifWeight` (`4a31a12:suppression/Suppression/HamCount.lean:161`) and `pmMean`,
  `hamProbOf` (`4a31a12:repair/Repair/PairVariance.lean:151`) are two uniform-law APIs.
  `card_ham_and_eq` (`4a31a12:suppression/Suppression/HamCount.lean:95`) is the `k = 1` case of
  `card_cycleCount_and_eq` (`4a31a12:repair/Repair/CycleStep.lean:440`).
- **D18.** `nonempty_of_even_card` (`4a31a12:suppression/Suppression/Canonical.lean:183`) and
  `card_perfectMatching_pos` (`4a31a12:suppression/Suppression/HamCount.lean:151`) follow from
  `card_eq_doubleFactorial` (`0360f0d:core/Pairing/Basic.lean:227`).
  `RoundRobin.Canonical.isZeroState_glue_iff`
  (`4a31a12:suppression/Suppression/Canonical.lean:326`) is an instance of
  `PerfectMatching.isZeroState_glue_iff` (`:283`). Both are endpoints.
- **D19.** `sum_indicator_eq_prob` (`4a31a12:repair/Repair/HybridConditional.lean:120`) restates
  the definition of `prob` (proof `rfl`), and `prob_compl_eq` (`:140`) is a general fact that
  belongs in `suppression/Suppression/Prob.lean`.

### 1.3 Repair, matching combinatorics

- **D20. `V ∖ {a, b}`, five encodings.** `pairCompl`
  (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:56`), `lowerSet`
  (`4a31a12:repair/Repair/Insertion.lean:540`, equal by `rfl`), `redSet`
  (`4a31a12:repair/Repair/PairRecursion.lean:442`), and the subtypes `Rest`
  (`4a31a12:repair/Repair/CycleCount.lean:75`) and `{v // v ≠ x ∧ v ≠ y}`
  (`4a31a12:suppression/Suppression/CouplingObstruction.lean:118`). Their `mem`, `card` and
  `mate_mem` lemmas are duplicated too.
- **D21. Edge contraction, four times.** `contractFn`
  (`4a31a12:repair/Repair/CycleCount.lean:80`) is `edgeContractFun`
  (`4a31a12:suppression/Suppression/CouplingObstruction.lean:62`) by `rfl`, `contractAt`
  (`4a31a12:repair/Repair/CycleCount.lean:143`) is `contractEdge`
  (`4a31a12:suppression/Suppression/CouplingObstruction.lean:118`) without its hypothesis,
  `red` (`4a31a12:repair/Repair/PairRecursion.lean:467`) is Clifford `contract` by
  `contract_eq_red` (`:477`), and `contract_mate_pairCompl`
  (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:97`) proves the formula a fourth time.
- **D22. Two-switch and insertion.** `switch` (`4a31a12:repair/Repair/PairRecursion.lean:400`)
  equals `twoSwitch` (`4a31a12:repair/Repair/Signature.lean:58`). `insertEdge`
  (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:153`) and `insertV`
  (`4a31a12:repair/Repair/FreeDefects.lean:391`) are the same `swap • glue` construction.
- **D23.** `commonCount` (`4a31a12:repair/Repair/HybridPair/Ratio.lean:102`) and `shared2`
  (`4a31a12:repair/Repair/PairLevelOne.lean:40`) are equal by `rfl`, with duplicate `_comm`
  lemmas.
- **D24.** `alt` (`4a31a12:repair/Repair/PairRecursion.lean:47`) is Clifford `evenPt`/`oddPt`
  with the matchings swapped. `cycleCount_congr` (`4a31a12:repair/Repair/FreeDefects.lean:62`)
  and `cycleCount_smul` (`4a31a12:repair/Repair/CycleStep.lean:427`) state one invariance.
- **D25. Two context notions.** `RoundRobin.Canonical.context`
  (`4a31a12:repair/Repair/HybridPair/Contexts.lean:93`) and `CyclicContext.context`
  (`4a31a12:repair/Repair/ZigZagInsertion.lean:54`) are not linked, so `zigzag_insertion`
  (`4a31a12:repair/Repair/ZigZagInsertion.lean:137`) speaks about the model only. The successor
  notion is built twice, `cnext` (`4a31a12:repair/Repair/CyclicContext.lean:33`) and
  `exists_next_entry` (`4a31a12:repair/Repair/HybridPair/Contexts.lean:280`).
- **D26. Copies forced by `private`.** `tri_vertex'`, `mem_rainbow_of_triangle'` and
  `eq_rainbow_of_triangle'` (`4a31a12:repair/Repair/TripleUnionAP.lean:83`, `:97`, `:108`) copy
  the private originals (`4a31a12:repair/Repair/TripleUnion.lean:141`, `:403`, `:414`).
  `mem_of_reachable'`, `reachable_map_of_adj'` (`4a31a12:repair/Repair/Insertion.lean:35`, `:43`),
  `mem_of_reachable''` (`4a31a12:repair/Repair/FreeDefects.lean:33`) and
  `mem_of_reachable_of_closed` (`4a31a12:repair/Repair/PairRecursion.lean:307`) copy the private
  pair in `0360f0d:clifford/Clifford/Contraction.lean:26` and `:34`.
- **D27. `IsGeneric` twice.** `IsGeneric` (`4a31a12:repair/Repair/FixedDefectLimit.lean:165`)
  and `RoundRobin.Canonical.IsGeneric` (`4a31a12:repair/Repair/TripleUnionLocal.lean:229`, the
  first at `![1, r]`), with sibling counts `card_not_generic_le` (`4a31a12:repair/Repair/FixedDefectLimit.lean:173`) and
  `card_not_isGeneric_le` (`4a31a12:repair/Repair/TripleUnionLocal.lean:269`).
- **D28. Mathlib overlaps.** `isUnit_natCast_of_coprime`
  (`4a31a12:repair/Repair/TripleUnion.lean:335`) is `ZMod.isUnit_iff_coprime`, and `mate_eq_comm`
  (`4a31a12:repair/Repair/CycleCount.lean:67`) is involutivity. `hamMat`
  (`4a31a12:repair/Repair/PairVariance.lean:404`) is core `H`
  (`0360f0d:core/Pairing/Basic.lean:280`) over ℝ.

### 1.4 Repair, round-robin and obstructions

- **D29.** `FamilyRepairBound (hamFamily m)`
  (`4a31a12:repair/Repair/SqrtObstructions/NoGo.lean:87`) is `RepairBound`
  (`4a31a12:suppression/Suppression/Density.lean:323`) with no bridge, and `class_count`,
  `class_density_ge` (`4a31a12:repair/Repair/SqrtObstructions/ClassCount.lean:68`, `:84`)
  generalize `repair_count` and `density_ge`
  (`4a31a12:suppression/Suppression/Density.lean:347`, `:391`) with separate proofs.
  **Bridge done.**
- **D30.** `Obstruction.zeroSet` (`4a31a12:repair/Repair/SqrtObstructions/Hole.lean:48`) is
  `avoid A univ` (`4a31a12:suppression/Suppression/ChainRule.lean:78`).
- **D31. The "if" half of the gcd law, three times.** `ham_factor_of_ne`
  (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:94`), `ham_factor_factor_zero`
  (`4a31a12:repair/Repair/HybridPair/MeanCount.lean:149`) and `ham_factor_two_zero`
  (`4a31a12:repair/Repair/TripleUnionAP.lean:342`). The "only if" half is `isUnit_sub_of_ham`
  (`4a31a12:repair/Repair/Covering/Basic.lean:216`). **General form done**, consumers unchanged.
- **D32. Two gadgets `{1, …, 6}`.** `Witness.gadget`
  (`4a31a12:repair/Repair/Covering/Witness.lean:314`) and `FactorCap.gadget`
  (`4a31a12:repair/Repair/FactorCap/Tail.lean:48`).
- **D33. Edge differences.** `edgesOutside`
  (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:42`) is `edgesOff P (defect Q P)ᶜ`
  (`4a31a12:suppression/Suppression/Canonical.lean:85`). `coreNew`
  (`4a31a12:repair/Repair/SqrtObstructions/CoreCertLength.lean:263`), `keptEdges`
  (`4a31a12:repair/Repair/SqrtObstructions/NearHybrid.lean:63`) and `coreDefect`
  (`4a31a12:repair/Repair/SqrtObstructions/CoreCertLength.lean:268`) repeat the `filter`
  construction of `tailDist` and `defect`.
- **D34.** `card_defect_le_of_extends` (`4a31a12:repair/Repair/SqrtObstructions/Defect.lean:47`)
  is the `tailDist = 0` case of `card_defect_le_tailDist_add`
  (`4a31a12:repair/Repair/SqrtObstructions/NearHybrid.lean:36`).
- **D35. Extending a tail, three times.** `exists_extends`
  (`4a31a12:repair/Repair/SqrtObstructions/Defect.lean:75`), `exists_superset`
  (`4a31a12:repair/Repair/Forcing.lean:118`) and `exists_extend_restrict`
  (`4a31a12:suppression/Suppression/Density.lean:267`). `isPartialMatching_tailEdges`
  (`4a31a12:repair/Repair/DensityFloor.lean:32`) repeats `isPartialMatching_edgesOff`
  (`4a31a12:suppression/Suppression/Canonical.lean:154`).
- **D36.** `card_coverage_change_le` (`4a31a12:repair/Repair/SqrtObstructions/Hole.lean:310`) and
  `abs_prob_profile_sub_le` (`:79`) are special cases of `card_coverage_change_le_of_radius`
  and `abs_prob_profile_sub_le_ne` (`4a31a12:repair/Repair/SqrtObstructions/NoGo.lean:166`,
  `:56`).
- **D37. Affine invariance of zero states, four times.** `isZeroState_affine_smul_iff`
  (`4a31a12:repair/Repair/FactorCap/Scale.lean:79`), `IsEquivFamily.smul_mem_zeroSet_iff`
  (`4a31a12:repair/Repair/SqrtObstructions/Hole.lean:133`), `isZeroState_shift_smul`
  (`4a31a12:repair/Repair/ExceptionalSix.lean:108`) and `hamCount_shift_smul`
  (`4a31a12:suppression/Suppression/HamCount.lean:92`).
- **D38. NearCore and SumCover.** `NearCore.mate` (`4a31a12:repair/Repair/NearCore.lean:51`)
  equals `stdMate` (`4a31a12:repair/Repair/ZeroState.lean:34`) off `{1, …, 6}`, and `NearCore.base`
  (`4a31a12:repair/Repair/NearCore.lean:39`) is `centers`
  (`4a31a12:repair/Repair/SumCover.lean:65`) without its filter. `J` and `openFactors` share
  names across the two files with different meanings
  (`4a31a12:repair/Repair/SumCover.lean:36`, `:283`, `4a31a12:repair/Repair/NearCore.lean:35`,
  `:165`).
- **D39.** `ManyCycles` (`4a31a12:repair/Repair/Signature.lean:221`) is
  `3 ≤ cycleCount M Q`.
- **D40. Mathlib restatements.** `valMinAbs_bounds` and `valMinAbs_eq_of_eq`
  (`4a31a12:repair/Repair/FactorCap/ZigZag.lean:42`, `:51`) are `ZMod.valMinAbs_mem_Ioc` and
  `ZMod.valMinAbs_spec`. `natCast_injOn` (`4a31a12:repair/Repair/ZeroState.lean:103`),
  `natCast_ne` (`4a31a12:repair/Repair/Automorphism.lean:192`), `natCast_ne_zero_of_lt`
  (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:88`) and `natCast_sub_ne`
  (`4a31a12:repair/Repair/SumCover.lean:255`) restate one fact.
- **D41.** `factor_mate_none'` (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:78`) is
  primed with no unprimed sibling and restates `factor_mate` with `mateFn_none`.
- **D42. Name collisions.** `card_ham_le` has two different statements
  (`4a31a12:repair/Repair/PartialCore.lean:29`, `4a31a12:repair/Repair/Covering/Basic.lean:184`),
  and `repairBound` (`4a31a12:repair/Repair/DensityFloor.lean:69`), `RepairBound` and
  `repair_bound` (`4a31a12:repair/Repair/SqrtBound.lean:63`) differ only in case.
- **D43.** `card_ham_le` (`4a31a12:repair/Repair/PartialCore.lean:29`) and `le_card_ham`
  (`4a31a12:repair/Repair/DensityGlue.lean:61`) run the same contraction induction. `autEquiv`
  (`4a31a12:repair/Repair/Automorphism.lean:315`) and `autGroupMulEquiv` (`:396`) present
  `Aut = AGL(1)` twice.
- **D44. Superseded density floors.** `density_ge_repair`,
  `doubleFactorial_le_zeroCount_mul_pow_repair` and `density_ge_repair_rpow`
  (`4a31a12:repair/Repair/DensityFloor.lean:82`, `:92`, `:109`) are weaker than the NearCore
  forms (`4a31a12:repair/Repair/NearCore.lean:318`, `:341`).

### 1.5 Clifford and Spin

- **D45.** `cliffordRepK` (`0360f0d:spin/Spin/Char2Modules.lean:238`) and `ρK`
  (`0360f0d:clifford/Clifford/BaseChange.lean:27`) are two base changes of one action. The bridge
  is reproved inline at `0360f0d:spin/Spin/Char2Modules.lean:393` and
  `0360f0d:spin/Spin/Reduction.lean:207`.
- **D46.** `invariant_eq_bot_or_top` (`0360f0d:clifford/Clifford/Irreducible.lean:61`) and
  `ρK_invariant_eq_bot_or_top` (`0360f0d:clifford/Clifford/BaseChange.lean:87`) have the same
  proof.
- **D47. ρW and ρK three-cycle pairs.** `minpoly_ρW_threeCycle`
  (`0360f0d:clifford/Clifford/Corollaries.lean:92`) and `minpoly_ρK_threeCycle`
  (`0360f0d:clifford/Clifford/BaseChange.lean:166`), `ρW_threeCycle_ne_smul_one`
  (`0360f0d:clifford/Clifford/Corollaries.lean:68`) and `ρK_threeCycle_ne_smul_one`
  (`0360f0d:clifford/Clifford/BaseChange.lean:134`), `ρW_threeCycle_sq_add`
  (`0360f0d:clifford/Clifford/Corollaries.lean:35`) and `ρK_threeCycle_sq_add`
  (`0360f0d:clifford/Clifford/BaseChange.lean:126`). The first of each pair is the second at
  `K = F₂`.
- **D48.** The dimension of `K ⊗ W` is computed three times, `finrank_baseChange_W`
  (`0360f0d:spin/Spin/Char2Modules.lean:417`), `nontrivial_baseChange`
  (`0360f0d:clifford/Clifford/BaseChange.lean:82`) and `finrank_W_eq`
  (`0360f0d:clifford/Clifford/Dimension.lean:537`) with `Module.finrank_baseChange`.
- **D49. Char-2 helpers.** `end_add_self` (`0360f0d:clifford/Clifford/EdgeRelations.lean:22`),
  `W_add_self` (`0360f0d:clifford/Clifford/Frame.lean:24`), `add_self_F₂`
  (`0360f0d:clifford/Clifford/ConceptualForm.lean:19`) and `mat_add_self`
  (`0360f0d:clifford/Clifford/MaasModel.lean:98`) are `ZModModule.add_self`. `neg_eq_self_F₂`
  (`0360f0d:spin/Spin/Reduce.lean:60`) is `ZModModule.neg_eq_self`. `two_eq_zero_K`
  (`0360f0d:clifford/Clifford/BaseChange.lean:123`) and `two_eq_zero_of_F₂`
  (`0360f0d:spin/Spin/Reduction.lean:69`) are identical.
- **D50. "Generators preserve, so Cl preserves", five times.** `intertwines_of_generators`
  (`0360f0d:spin/Spin/Char2Modules.lean:312`), `stable_of_adjU`
  (`0360f0d:spin/Spin/Reduction.lean:116`), an inline block at
  `0360f0d:spin/Spin/BasicSpin.lean:189`, `preserves_of_invariant`
  (`0360f0d:clifford/Clifford/Irreducible.lean:37`) and `0360f0d:clifford/Clifford/BaseChange.lean:89`.
- **D51. Generators under several names.** `adjU`, `adjT` (`0360f0d:spin/Spin/Reduce.lean:66`,
  `:156`) cover `blkU`, `gapU`, `blkC`, `gapC` (`0360f0d:spin/Spin/Char2Modules.lean:45`). `dot_v`
  (`0360f0d:clifford/Clifford/Descent.lean:133`) and `dot_v_v`
  (`0360f0d:spin/Spin/Char2Modules.lean:26`) compute one value.
- **D52.** `exists_vacuum` (`0360f0d:spin/Spin/Char2Modules.lean:197`) and `exists_jVacuum`
  (`0360f0d:spin/Spin/JSystem.lean:251`) share one induction.
- **D53.** `symmDiff_compl_eq_univ` (`0360f0d:clifford/Clifford/Dimension.lean:500`) and
  `symmDiff_univ_symmDiff_eq_univ` (`0360f0d:clifford/Clifford/Assembly.lean:133`).
- **D54.** `sum_H_orbit_four` (`0360f0d:clifford/Clifford/LocalFour.lean:69`) and
  `sum_H_orbit_six` (`0360f0d:clifford/Clifford/LocalSix.lean:41`) share one transport proof.
- **D55.** `polar_schurQ_single` (`0360f0d:spin/Spin/SchurForm.lean:46`) is a case of
  `polar_schurQ_single_right` (`0360f0d:spin/Spin/BasicSpin.lean:45`).
- **D56.** `finrank_le_of_simple'` (`0360f0d:spin/Spin/BasicSpin.lean:224`) is a `subst` wrapper
  used once.

### 1.6 Proposed shared module layout

- `core/Pairing/Basic.lean`. Matchings, `Ham`, `not_ham_of_closed`, `not_ham_of_mate_eq` and
  `not_ham_of_mate_eq_of_two_lt` (moved in the dry run), and public versions of the reachability
  helpers of D26.
- `core/Pairing/Union.lean` (new). The union `P ∪ Q` as a graph. `cycleCount` and its lemmas from
  `repair/Repair/CycleCount.lean`, one `pairCompl` (D20) and one hypothesis-free contraction
  (D21), with `red`, `contractEdge` and `contractAt` as abbreviations. `jointCount` and
  `jointHamProb` from `HybridPair/CommonEdge.lean`.
- `core/Pairing/Contraction.lean`. `clifford/Clifford/Contraction.lean` is pure matching
  combinatorics. Repair and Suppression use only this file of Clifford. Moving it removes their
  dependency on the Clifford library.
- `core/Pairing/RoundRobin.lean`. Factors, `hamEvent`, the gadget `G0` (D32), the gcd law in
  both directions (D31) and affine invariance of zero states (D37).
- `suppression/Suppression/Prob.lean`. One finite-law API, absorbing `unifWeight`, `pmMean`,
  `prob_compl_eq`, `sum_indicator_eq_prob` and `eventCount`/`eventNum` (D12, D17, D19).
- `clifford/Clifford/BaseChange.lean`. One base change `ρK = baseChangeHom ∘ ρW` used by Spin
  (D45 to D48).

## 2. Vacuity and bogus statements

### 2.1 `hybrid_theorem1` is empty at its intended instance

`HJIStar` (`4a31a12:repair/Repair/HybridConditional.lean:261`) is the moment form (H-JI*) for the
true-defect laws `Λ⁰`, not the literal cumulant (H-JI). For every pattern with `a + b ≤ K` it
asks `P(B) ≤ πδ/(80√d)` and `E(X − μ)^(2k) ≤ (4eHkμ)^k`. `hybrid_theorem1`
(`4a31a12:repair/Repair/HybridConditional.lean:702`) uses it at `N = 2m − 2`,
`d = ⌈ε√m⌉` (`defectSize`), `K = ⌊(1 − δ)d⌋` (`radius`), `k = ⌈(1 + η)K/θ⌉` (`halfOrder`) and
`H = m^(1/4 − θ)`.

- **In Lean it is not vacuous.** `Ω`, `P`, `X`, `B`, `PH` and `pB` are universally quantified
  with no link to the hybrid. A point mass satisfies every hypothesis at every `m ≥ m₀`
  (`VacuityCheck.Hybrid.hjiStar_pointMass` and the example after it).
- **At the intended instance it is empty for all large `m`.** With `PH = P_H(ρ(H) ≤ K)` for the
  hybrid, Theorem 4 of `results/ulzd-rescue.md` gives `PH = 1` for all large `m`, verified as
  Corollary 6 ("(H-JI) false") in `results/review-ulzd-rescue.md`. The Lean conclusion forces
  `PH < 1`. So the hypotheses cannot all hold there, at every admissible `(ε, δ, η, θ)`.
  `results/hybrid-mean-lambda0.md` argues that the mean bound and the union bound hold, which
  leaves `HJIStar` as the false one. That last step is an inference from unreviewed notes.
  `results/hji-contra.md` leaves (H-JI*) for `Λ⁰` "untouched" by its own mechanism. So the claim
  is "the hypothesis set fails", with `HJIStar` the likely culprit, not a direct refutation of
  (H-JI*).
- **The docstring overclaims.** "So some tail has `ρ > K`, and `N_m ≥ K + 1`" is not part of the
  statement. `hunion` is the only link to the hybrid, and `PH` is a free real.
- Also, the review in `results/review-ulzd-rescue.md` puts the threshold of Theorem 4 near
  `m ≈ 10¹³`, so the emptiness holds only past that size.

### 2.2 Other findings

- **V2. `prob_le_of_tilt`** (`4a31a12:repair/Repair/HybridConditional.lean:433`). Satisfiable in
  Lean (`X ≡ N` gives `tiltVar = 0`). At the intended law its hypothesis (H-T) is false when
  `(1 − δ)ε > 8√2`, by Proposition 9 of `results/hybrid-assembly.md`, verified in
  `results/review-hybrid-assembly.md`.
- **V3. `HamSpectral`** (`4a31a12:repair/Repair/PairVariance.lean:412`) is an assumed spectral
  resolution. `spectral_cGen`, `spectral_coherence` (`:515`, `:542`) and
  `HamSpectral.jointHamProb_div_sq` (`4a31a12:repair/Repair/PairFormula.lean:117`) are
  conditional on it. It exists mathematically for every `W`, but Lean has no instance beyond
  `|PM| = 1`.
- **V4. Trivial regime of the NG-A theorems.** `hole_isRobust`, `ngA_relativized`, `ngA_c` and
  `ngA_d` (`4a31a12:repair/Repair/SqrtObstructions/NoGo.lean:205`, `:241`, `:264`, `:291`). If
  `K + K′ + 3 ≥ m − 3` the hypotheses force `δ ≥ 1`, and then the conclusion is witnessed by
  `A′ t = univ`. Content exists only for large `m` with `K + K′ ≪ m`.
- **V5.** `factorTail_certLength_five`
  (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:505`) gives `n + 15 ≤ 288L`, which is
  automatic for `n ≤ 273`.
- **V6.** The `L(P)` bound of `exists_nearHybrid`
  (`4a31a12:repair/Repair/SqrtObstructions/NearHybrid.lean:186`) is vacuous once
  `ε + δ ≥ 1/√2`. The docstring says so.
- **V7.** The `upper_reduction*` bounds (`4a31a12:suppression/Suppression/SizeBias.lean:279` to
  `:321`) exceed `1` unless `μ > 2(2 + ε)/ε²`.
- **V8. Endpoints with trivial content.** `mixWeight_map_perm`
  (`4a31a12:suppression/Suppression/MixtureBarrier.lean:64`) holds by definition.
  `exists_ham_factor_zero` (`4a31a12:suppression/Suppression/HamCount.lean:234`) is witnessed by
  `factor m 1` and feeds only an unused hypothesis. Nine endpoints say only `0 ≤ x`
  (`condMean_nonneg`, `kerExp_nonneg`, `tiltVar_nonneg`, `condVar_nonneg`, `bernVarSum_nonneg`,
  `condSlack_nonneg`, `entSum_nonneg`, `binMI_nonneg`, `reweight_nonneg`). `schurHom_t`
  (`0360f0d:spin/Spin/SchurForm.lean:139`) is `lift_t` plus `rfl`.
- **V9.** Upper bounds on `−log q` (`neg_log_le_div_add_sum`,
  `4a31a12:suppression/Suppression/VMinus.lean:61`, and its relatives at `:210`, `:229`,
  `4a31a12:suppression/Suppression/Reweighted.lean:592`, `:622`) assume `0 < q` and so are sound,
  but `Real.log 0 = 0` means such a bound never certifies `q > 0`. Only the `exp` forms
  (`4a31a12:suppression/Suppression/VMinus.lean:429`, `:742`) do.
- **V10. Stale text.** The module docstring at
  `4a31a12:repair/Repair/SqrtObstructions/Hole.lean:36` says NG-A(c) and (d) are not formalized,
  but `NoGo.lean` formalizes both. `TODO.md` says Mathlib cannot state the basic-spin
  identification, which Spin now does. `0360f0d:clifford/Clifford/Corollaries.lean:150` has an
  unused `have := nontrivial_W n hn`.
- **V11.** `exists_not_sameSig_of_rho` (`4a31a12:repair/Repair/Signature.lean:485`) assumes
  `ρ(T) ≥ 3` with no Lean witness. `results/covering-spike.md` has `ρ = 3` tails at `m′ = 9`, so
  it is satisfiable.

### 2.3 Hypotheses that are open, not known false

These were checked against the cited results and their reviews.
`not_repairBound_of_le_hamBottomRatio` and `not_boundedRadius_of_le_hamBottomRatio`
(`4a31a12:repair/Repair/BoundedRadius.lean:245`, `:282`, hypothesis (BK)), the (V−_M), Palm-gap
and (V+_B) forms in `4a31a12:repair/Repair/DensityGlue.lean:352` to `:466`, `ngA_c_certTwo`
(`4a31a12:repair/Repair/SqrtObstructions/NoGo.lean:368`), `not_boundedRadius_of_cycleProfile_le`
(`4a31a12:repair/Repair/CycleStep.lean:386`), and the (A), (B′), Δ and (V±) inputs of
Suppression. COD-199's counterexample for `ε′ < 0` is respected, every `_of_mem_Icc` form has
`0 ≤ ε′`.

### 2.4 Compiled satisfiability instances (`VacuityCheck.lean`)

- Repair. `factorTail_cap` at `n = 17`, `repair_bound` at `m = 6` with `Witness.baseTail`,
  `exists_nearHybrid` at `m = 9`, the bridge `FamilyRepairBound (hamEvent m) ↔ RepairBound`, the
  gcd law from `IsUnit (s − t)`, and `not_farey_hit` from coprimality.
- Suppression. A Bernoulli(1/2) law satisfies `exp_neg_mul_log_le_of_pairDeficit_le`,
  `exp_neg_div_le_of_fano_le` and `upper_reduction_sqrt_of_le_add_two`. `Ω = Bool`, `ι = Unit`
  satisfies `div_le_neg_log_prob_avoid`. `RepairBound` from `repairBound` makes
  `doubleFactorial_le_zeroCount_mul_ballCount` non-vacuous.
- Hybrid. A point mass satisfies `HJIStar` and every hypothesis of `hybrid_theorem1`.
- Spin. `cod105` at `n = 2` over ℂ, `reduction_basicSpin` from its output, `exists_lattice` with a
  proper valuation subring, `finrank_le_of_jSystem` over `ZMod 5`,
  `exists_injective_intertwiner` and `exists_intertwining_equiv` on `W (Fin 4)`,
  `minpoly_ρK_threeCycle` over `GaloisField 2 2`, and `finrank_W_eq` at `n = 3`.

## 3. Over-restriction

"Proof unchanged" says whether the generalized statement goes through with the existing proof.

### 3.1 Done in the dry run

- **O1.** `ham_iff_cycleCount_eq_one` (`4a31a12:repair/Repair/CycleCount.lean:49`) drops
  `[Nonempty V]`. Proof changed by two lines.
- **O2.** `[NeZero m]` is unused (Batteries `unusedArguments`) in the defs `shift`
  (`4a31a12:suppression/Suppression/HamCount.lean:40`), `edgeLabel`, `affinePerm`
  (`4a31a12:repair/Repair/Automorphism.lean:97`, `:336`), `endVtx`, `capFn`
  (`4a31a12:repair/Repair/FactorCap/Construction.lean:98`, `:102`), `scale`
  (`4a31a12:repair/Repair/FactorCap/Scale.lean:26`), `capCenter`, `gadget`
  (`4a31a12:repair/Repair/FactorCap/Tail.lean:38`, `:48`), `zigPos`
  (`4a31a12:repair/Repair/FactorCap/ZigZag.lean:61`), `rainbow`, `infSquare`, `ladderSquare`
  (`4a31a12:repair/Repair/TripleUnion.lean:282`, `:455`, `:715`) and `apTriangle`
  (`4a31a12:repair/Repair/TripleUnionAP.lean:125`), and so in the `rfl` lemmas `scale_none`,
  `scale_some`, `scale_inv_none`, `scale_inv_some` (`4a31a12:repair/Repair/FactorCap/Scale.lean:31`
  to `:48`), `shift_none`, `shift_some`, `shift_inv_none`, `shift_inv_some`
  (`4a31a12:suppression/Suppression/HamCount.lean:45` to `:61`) and ten dependent theorems.
  Proof unchanged.
- **O3.** `HasClosedCycle` (`0360f0d:clifford/Clifford/Contraction.lean:284`) drops
  `[DecidableEq V]`, and so do `not_hasClosedCycle_of_ham` and `hasClosedCycle_self`
  (`4a31a12:repair/Repair/HybridPair/MeanCount.lean:84`, `:94`). Proof unchanged, one
  `classical` added.
- **O4.** `not_farey_hit` (`4a31a12:repair/Repair/FactorCap/Farey.lean:51`) needs only
  `Nat.Coprime n μ` and `16 < n`. Added as `not_farey_hit_of_coprime`. New three-line proof.
- **O5.** `ham_factor_of_ne` (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:94`) needs
  only `IsUnit (s − t)`. Added as `ham_factor_of_isUnit_sub` in `FactorCap/Scale.lean`. Proof
  unchanged.
- **O6.** `not_ham_self` (`4a31a12:repair/Repair/Covering/Basic.lean:200`) is derived from
  `not_ham_of_mate_eq`.

### 3.2 Left for the user

- **O7.** `exists_contains_of_prime`, `exists_checked_cell`, `cell_facts`
  (`4a31a12:repair/Repair/FactorCap/Checker.lean:233`, `4a31a12:repair/Repair/FactorCap/Cover.lean:24`,
  `:32`). Replace `n.Prime` by `Nat.Coprime n μ` through O4. Proof unchanged (pass-through).
- **O8. P9 without primality.** `not_ham_capMatching`
  (`4a31a12:repair/Repair/FactorCap/Construction.lean:194`) needs only `IsUnit u`, and the cap
  `isZeroState_capMatching`, `isZeroState_capState`, `factorTail_cap`
  (`4a31a12:repair/Repair/FactorCap/Construction.lean:280`,
  `4a31a12:repair/Repair/FactorCap/Tail.lean:114`, `:172`) should hold for
  `Nat.Coprime (2m − 1) 105` with `9 ≤ m`, by the gcd ≥ 11 closed-set argument of
  `results/cod-186-archive-cap-check.md`. About 40 new lines. Proof unchanged: no.
- **O9.** `card_hit_le` (`4a31a12:repair/Repair/SqrtObstructions/CertLength.lean:208`) needs only
  unit multipliers. The rest of the CertLength family uses primality for cancellation of small
  multipliers. Proof unchanged: almost.
- **O10.** `exists_nearHybrid` (`4a31a12:repair/Repair/SqrtObstructions/NearHybrid.lean:186`)
  uses `hp` only for its last conjunct. Split it. Proof unchanged.
- **O11.** `Odd a`, `[NeZero a]` and `[NeZero n]` in `4a31a12:repair/Repair/Covering/Basic.lean:98`
  to `:310` follow from `hn` and `a ∣ n`. Proof unchanged.
- **O12.** `repair_bound` (`4a31a12:repair/Repair/SqrtBound.lean:63`) takes `G` redundantly with
  `uncovered T = G`. Proof unchanged.
- **O13.** `isZeroState_shift_smul` (`4a31a12:repair/Repair/ExceptionalSix.lean:108`) is stated
  at `m = 6` with a generic proof. Proof unchanged.
- **O14. The six-vertex gadget.** `repair_count`, `doubleFactorial_le_zeroCount_mul`,
  `density_ge` (`4a31a12:suppression/Suppression/Density.lean:347` to `:391`) and
  `exists_uncovered_near_tail` (`4a31a12:repair/Repair/Signature.lean:436`, with `:461`, `:474`)
  use `G.card = 6` only for `|Gᶜ| = 2(m − 3)`. Any `G` with `|Gᶜ| = 2M` works, with `m − 3`
  replaced by `M`. Proof unchanged: likely.
- **O15.** `5 ≤ m` in `4a31a12:repair/Repair/FactorCap/Tail.lean:52`, `:73` would hold at
  `m = 4` except for one `natCast_injOn` step. Low value.
- **O16.** The Tilt wrappers of D6 carry unused `_hp0`, `_hk` and `_hA`. Proof unchanged.
- **O17.** `exp_neg_div_le_of_pairDeficit_le` (`4a31a12:suppression/Suppression/Tilt.lean:685`)
  holds for every `c < 1`, not only `0 < c`. Proof unchanged: no, one case split.
- **O18.** `expect_mismatch_sub_le` and `expect_rho_ge`
  (`4a31a12:suppression/Suppression/CouplingObstruction.lean:551`, `:607`) need only
  `prob P {y = a} ≤ 1/#A`, not uniformity. Proof unchanged: no, one step.
- **O19.** `sum_prob_mem_mixWeight (hn : 0 < n)` and `jointRatio_mixWeight (hN0 : 0 < N)`
  (`4a31a12:suppression/Suppression/MixtureBarrier.lean:292`, `:325`), and
  `lower_reduction (hK : 0 ≤ K)` (`4a31a12:suppression/Suppression/SizeBias.lean:329`). The
  degenerate cases hold. Low value.
- **O20.** `hybrid_theorem1` (`4a31a12:repair/Repair/HybridConditional.lean:702`) hard-codes the
  constants `40` and `80` and `H = m^(1/4 − θ)`. The monotonicity in `H` claimed in the docstring
  is not formalized.
- **O21.** The power-series section of `4a31a12:repair/Repair/CumulantTail.lean:45` to `:191` is
  stated over `ℝ⟦X⟧` and holds over any `ℚ`-algebra. Proof unchanged: likely.
- **O22.** `card_relation_le` (`4a31a12:repair/Repair/FixedDefectLimit.lean:129`) needs only
  `IsUnit (c b)`, `IsGeneric` (`:165`) picks up an unused `[Fact n.Prime]`, and the file's
  `import Repair.Insertion` is unused.
- **O23.** `card_fourCycles_neg_one` and `card_fourCycles_of_two_mul_eq_one`
  (`4a31a12:repair/Repair/TripleUnionAP.lean:318`, `:325`) are cases of `card_fourCycles_of_isAP`
  (`:332`). `fourCycles_two`, `card_fourCycles_two` (`4a31a12:repair/Repair/TripleUnion.lean:763`,
  `:806`) also hold at `m = 1`.
- **O24.** `var_ctxCount [Nonempty ι]` (`4a31a12:repair/Repair/PairVariance.lean:275`) holds for
  empty `ι`.
- **O25. `Fin (2 * n)` throughout Clifford and Spin**, for example `finrank_W_eq`, `cknUpperBound`
  (`0360f0d:clifford/Clifford/Dimension.lean:537`, `:546`) and `adjoin_ρW_eq_top`
  (`0360f0d:clifford/Clifford/Irreducible.lean:31`). Any `Fintype V` with `card V = 2n` works
  through `H_congr` (`0360f0d:core/Pairing/Basic.lean:294`). Proof unchanged: no.
- **O26.** `card_eq_of_lattice` and `finrank_eq_of_lattice`
  (`0360f0d:spin/Spin/Reduction.lean:164`, `:181`) assume lattice data that the conclusion does
  not need.
- **O27.** `finrank_le_of_jSystem` (`0360f0d:spin/Spin/JSystem.lean:296`) can drop
  `[Nontrivial Y]` and `[FiniteDimensional K Y]`.
- **O28.** `finrank_le_of_simple` and `exists_orthonormal_schurQ`
  (`0360f0d:spin/Spin/BasicSpin.lean:172`, `:131`) use `IsAlgClosed` only for square roots and
  `CharZero` only for `2 ≠ 0` and nondegeneracy.
- **O29.** `schurQ_nondegenerate` (`0360f0d:spin/Spin/BasicSpin.lean:78`) needs only
  `((m + 1 : ℕ) : K) ≠ 0`.
- **O30.** `polar_schurQ_single_right`, `sum_ite_pred`, `sum_ite_succ`
  (`0360f0d:spin/Spin/BasicSpin.lean:45`, `:21`, `:32`) hold over a `CommRing`.
- **O31.** `exists_intertwining_equiv` (`0360f0d:spin/Spin/Char2Modules.lean:424`) has a
  `[FiniteDimensional k M]` implied by `hM`.
- **O32. Derivable `1 ≤ n`.** `0360f0d:clifford/Clifford/BaseChange.lean:134`, `:166`,
  `0360f0d:clifford/Clifford/ConceptualForm.lean:25`, `:83`,
  `0360f0d:clifford/Clifford/MaasModel.lean:356`, `:373`, and with a subsingleton case
  `0360f0d:clifford/Clifford/Irreducible.lean:31`, `:61` and
  `0360f0d:clifford/Clifford/Corollaries.lean:148`.
- **O33.** `sum_H_orbit_four` (`0360f0d:clifford/Clifford/LocalFour.lean:69`) has a derivable
  `hcd`, and `exists_valuationSubring_two` (`0360f0d:spin/Spin/Existence.lean:122`) a stronger
  than needed `CharZero`.
- **O34.** `exists_partner`, `pairing_of_four`, `switchCut_reachable_iff`, `two_switch`
  (`4a31a12:repair/Repair/Insertion.lean:328`, `:371`, `:444`, `:461`) carry `[Fintype V]` (and
  `[DecidableEq V]`) unused in the type. The build's linter suggests `Finite V`. Proof unchanged:
  no.

Checked and needed. `coprime 3/15/105` in `4a31a12:repair/Repair/TripleUnion.lean` (105 enters
through `a3Six_dvd`, and Lemma M (c) fails at `n = 7`), `3 ≤ m` in `TripleUnionAP.lean`, primality
in `4a31a12:repair/Repair/HybridPair/MeanCount.lean:156`, `:178`, `4 ≤ m` in
`IsAut.apply_none` (`4a31a12:repair/Repair/Automorphism.lean:233`), `144 ≤ m` in
`mixture_barrier` (`4a31a12:suppression/Suppression/MixtureBarrier.lean:477`), `K + 3 ≤ m` in
`card_boundary` (`4a31a12:suppression/Suppression/Canonical.lean:122`), and `hI` in
`finrank_le_of_jSystem`.

## 4. Unused code

- **U1. Spin.** Only `0360f0d:AxiomCheck.lean:3` imports it. It is the COD-105 endpoint library,
  cited by `clifford/basic_spin.md` and `results/cod-154-review.md`, so it is not dead.
- **U2. Clifford.** Repair and Suppression import only `Clifford.Contraction`
  (`4a31a12:repair/Repair/Insertion.lean:1`, `4a31a12:suppression/Suppression/Canonical.lean:1`).
  The algebraic part of Clifford serves Spin and AxiomCheck. See 1.6 for moving Contraction to
  core.
- **U3. Leaf files.** Imported only by their library root: Layered, CouplingObstruction,
  MixtureBarrier in Suppression, and NearCore, ExceptionalSix, Signature, LocalFloor, NearHybrid,
  NoGo, TripleUnionAP, TripleUnionLocal, HybridConditional, Switching, HybridPair/CommonEdges,
  FixedDefectLimit, ZigZagInsertion and PairLevelOne in Repair. All carry AxiomCheck endpoints,
  so none is dead.
- **U4. Dead private helpers.** `unit5` and `unit7` (`4a31a12:repair/Repair/TripleUnion.lean:368`,
  `:373`) are used nowhere. **Removed in the dry run.**
- **U5. The raising operator.** `raise`, `raise_w`, `raise_lower_w`, `lower_raise_w`,
  `raise_mem_adjoin` and `symmDiff_single_of_notMem`
  (`0360f0d:clifford/Clifford/LocalFactor.lean:22` to `:76`) are used nowhere and cited nowhere.
  They are the matrix-unit content of sketch §6, so removal is the user's call.
- **U6. Public declarations used nowhere** and cited nowhere. `frameF_sq`, `frame_commute`,
  `frameE_commute`, `mem_symmDiff_single`, `symmDiff_single_erase_comm`
  (`0360f0d:clifford/Clifford/Frame.lean:141`, `:160`, `:178`, `:107`, `:112`), `ι_ones_commute`,
  `ι_ones_sq` (`0360f0d:clifford/Clifford/ConceptualForm.lean:56`, `:75`), `ΓU_anticomm`
  (`0360f0d:clifford/Clifford/Action.lean:121`), `last_mem_erase_castSucc`
  (`0360f0d:clifford/Clifford/MaasModel.lean:145`), `H_comm` (`0360f0d:core/Pairing/Basic.lean:286`),
  `mem_block` (`0360f0d:core/Pairing/RoundRobin.lean:125`), `restrictHom_apply`
  (`0360f0d:spin/Spin/Existence.lean:82`), `AntiComm.sub_right` (`0360f0d:spin/Spin/JSystem.lean:40`),
  `redHom_stildeCl_t`, `redHom_stildeCl_z` (`0360f0d:spin/Spin/Reduction.lean:105`, `:109`),
  `schurHom_z` (`0360f0d:spin/Spin/SchurForm.lean:145`), `coe_autEquiv`, `coe_autGroupMulEquiv`
  (`4a31a12:repair/Repair/Automorphism.lean:324`, `:402`), `mem_symZero`
  (`4a31a12:repair/Repair/ExceptionalSix.lean:323`), `coe_liftEquiv`
  (`4a31a12:repair/Repair/FreeDefects.lean:670`), `cycleOf_eq_iff_mem`
  (`4a31a12:repair/Repair/PairRecursion.lean:659`), `IsFourCycle.reverse`
  (`4a31a12:repair/Repair/TripleUnion.lean:120`), `cycleCount_comm`
  (`4a31a12:repair/Repair/Insertion.lean:212`) and eight `IsLaw` lemmas in
  `4a31a12:suppression/Suppression/SizeBias.lean:57` to `:181`. Most are small API lemmas
  (`simp`, `coe_`, `comm`). Removal saves little.
- **U7.** `ρW_threeCycle_ne_smul_one` and `eq_zero_of_ρW_threeCycle_fixed`
  (`0360f0d:clifford/Clifford/Corollaries.lean:68`, `:43`) are cited only by `TODO.md`, and
  `0360f0d:clifford/basic_spin.md:142` says they are no longer needed.
- **U8. `clifford/check_clifford.py`** checks over F₂ the facts that are now Lean theorems
  (`rank_H_eq`, `Γ_anticomm`, `frameE_sq`, `adjoin_frame_eq_top`, `cliffordRep_ι_ones`). Only
  `clifford/sketch.md` mentions it, and `sketch.md` still lists CKN as an external input.
- **U9. AxiomCheck-only endpoints** cited in no results file. About 40 in Suppression (Canonical,
  ChainRule, Reweighted, Tilt, VMinus) and 70 in Repair (PairFormula, PairLevelOne, Ratio,
  FixedDefectLimit, CumulantTail). Candidates if `AxiomCheck.lean` is trimmed, together with the
  superseded floors of D44.

### FGPT

FGPT is the Fixed-Generator Predecessor Theorem, balancing moves `q ↦ q + d(e_k − x)` on the
zero-sum cube. Nothing in this repo or its git history mentions it (`grep -i` for `fgpt`,
"fixed-generator", "predecessor theorem", zero-sum cube, balancing and carpooling, and
`git log --all`). Its formalization is a separate repo, `valarauca/Predecessor-Theorem`
(local copy `/home/valarauca/Documents/math/fgpt/Predecessor-Theorem`, libraries `FGPT/` and
`Carpooling/`), and `organize-archive/README.md` says the Hamiltonian work does not depend on it.
No file here duplicates any of its files. Candidates for what "the FGPT stuff" refers to.

1. The separate `Predecessor-Theorem` repo. Nothing in this repo uses it, which matches "nothing
   uses it", but removing it is outside this worktree.
2. The FGPT ancestry of the six-vertex gadget. The archive's repair bound `p_m ≤ 3`
   (`organize-archive/docs/04-bounded-repair/repair-bound-proof.md`, "Draft, assuming FGPT") was
   rejected (`results/cod-193-archive-bound-claims.md` row 4). The gadget it introduced survives in
   `RepairBound` (`4a31a12:suppression/Suppression/Density.lean:323`), `Witness.gadget` and
   `FactorCap.gadget` (D32). These are used throughout, so they are not removable.
3. The "FGPT fingerprint route", the uniform one-factorization hypothesis of
   `results/archive-audit-2026-11-25.md`. No Lean declaration states it.
4. The Spin library, which nothing else imports (U1). It is COD-105 work, not FGPT.

Nothing was removed under this item.

## 5. Docstring-only citation additions

From `results/citation-audit.md` (781b60d), keeping the existing citations.

- Lemma K2, `4a31a12:repair/Repair/PairRecursion.lean:6` and `jointCount_eq_k2Step` (`:1571`).
  Kanunnikov and Vassilieva, arXiv:1409.4356, Theorem 5, eq. (23) at `α = 2` (audit row 20).
- The common-edge factor, `jointHamProb_div_sq_eq_of_mate_eq`
  (`4a31a12:repair/Repair/HybridPair/CommonEdge.lean:366`). Kanunnikov and Vassilieva, Remark 1 at
  `α = 2` (row 23).
- The pair formula, `4a31a12:repair/Repair/PairFormula.lean:7` and
  `HamSpectral.jointHamProb_div_sq` (`:117`). Hanlon, Stanley and Stembridge, Contemp. Math. 138
  (1992), Lemma 3.3, with Goulden and Jackson (1996) and Tout, arXiv:1502.01932 (row 18).
- The variance identity, `4a31a12:repair/Repair/PairVariance.lean:11` and `var_ctxCount`
  (`:275`). The law of total variance, conditioned on the cycle type of `R ∪ B` (row 21).
- The signature barrier, `4a31a12:repair/Repair/Signature.lean:6`, Lemma K1
  `not_ham_twoSwitch_of_sameSig` (`:213`), Theorem K1(a) `exists_uncovered_twoSwitch` (`:329`) and
  (X1) `exists_uncovered_near_tail` (`:436`). Hannenhalli and Pevzner, J. ACM 46 (1999), Lemma 1
  (with Bafna and Pevzner 1996), and the separating-system bound of Rényi (1961) and Katona
  (1966) (rows 2 and 3).
- `autGroupMulEquiv` (`4a31a12:repair/Repair/Automorphism.lean:396`). **Not added.** Row 43 says
  Cameron 1975 is "probably identical", the handling of `n = 3, 5` is unchecked, and the full text
  was unreachable. The audit does not confirm it.

## 6. Dry run on `lean-review`

Done, in separate commits after this report.

1. `ham_iff_cycleCount_eq_one` without `[Nonempty V]`, `ham_iff_cycleCount_eq_one'` deprecated,
   `cycleCount_comm` moved to `CycleCount.lean`.
2. `not_ham_of_mate_eq` and `not_ham_of_mate_eq_of_two_lt` moved to `core/Pairing/Basic.lean`,
   `not_ham_self` derived from them.
3. `hamEvent` moved to `Suppression/HamCount.lean`. `hamFamily`, `mem_zeroSet_hamFamily` and
   `isEquivFamily_hamFamily` became deprecated aliases of the `hamEvent` names.
4. Unused instance arguments dropped (O2, O3), dead `unit5` and `unit7` removed.
5. Generalized forms added: `not_farey_hit_of_coprime`, `ham_factor_of_isUnit_sub`,
   `familyRepairBound_hamEvent_iff`.
6. The citations of section 5.

Every renamed or moved declaration is listed in `historic_references.md`. Left for the user,
because each changes an endpoint, drops a proof, or needs real proof work: D5, D6 and D7 (dropping
duplicate endpoints), the module moves of 1.6, O7 to O34, U5 to U9, and the FGPT question.
