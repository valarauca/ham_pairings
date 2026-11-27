# Historic references

Declarations renamed, moved, re-stated or removed by the dry run of `REVIEW.md`, replayed on
ham_pairings branch `review-main` (from main `81fccb6`) and ham-spin branch `review-spin` (from
`0360f0d`). "Last old form" is the last commit that has the old name, location or statement.
`git show <commit>:<path>` shows the old proof. Every renamed public name keeps a
`@[deprecated]` alias at its old name. A "last old form" at `81fccb6` is in ham_pairings and one
at `0360f0d` is in ham-spin. Both have the same lines as `4a31a12`, the commit the review read.
The review commit `48a334a` has the same Lean sources as `81fccb6`. The changes are in `4e06a6f`
(cycle count and core moves), `c70e6bd` (`hamEvent`), `bb45181` (instance arguments, dead lemmas),
`890c3dc` (general forms) and `0a756d7` (docstring citations) on `review-main`, and in `bba5727` (core
moves) and `a2e8996` (`HasClosedCycle`) on `review-spin`. The first dry run, on branch
`lean-review`, has the same changes in `20cae08`, `a599056`, `2ef33ef`, `130de45` and `6675ea1`.

All names are in namespace `Pairing`. `PM` abbreviates `PerfectMatching` and `RRC` abbreviates
`RoundRobin.Canonical`. Paths under `core/` and `clifford/` are in ham-spin, all others in
ham_pairings.

The last section, "Risky items", records the second pass on branch `review-risky`. It keeps a
`@[deprecated]` alias only where a results file or the frontier cites the old name.

## Renamed (deprecated alias kept)

| old name | new name | new location | last old form |
|---|---|---|---|
| `PM.ham_iff_cycleCount_eq_one'` | `PM.ham_iff_cycleCount_eq_one` | `repair/Repair/CycleCount.lean` (alias in `repair/Repair/Insertion.lean`) | `81fccb6:repair/Repair/Insertion.lean:218` |
| `RRC.hamFamily` | `RRC.hamEvent` | `suppression/Suppression/HamCount.lean` (alias in `repair/Repair/SqrtObstructions/Hole.lean`) | `81fccb6:repair/Repair/SqrtObstructions/Hole.lean:113` |
| `RRC.mem_zeroSet_hamFamily` | `RRC.mem_zeroSet_hamEvent` | `repair/Repair/SqrtObstructions/Hole.lean` | `81fccb6:repair/Repair/SqrtObstructions/Hole.lean:117` |
| `RRC.isEquivFamily_hamFamily` | `RRC.isEquivFamily_hamEvent` | `repair/Repair/SqrtObstructions/Hole.lean` | `81fccb6:repair/Repair/SqrtObstructions/Hole.lean:127` |

## Moved (same full name)

| name | old location | new location | last old form |
|---|---|---|---|
| `PM.cycleCount_comm` | `repair/Repair/Insertion.lean` | `repair/Repair/CycleCount.lean` | `81fccb6:repair/Repair/Insertion.lean:212` |
| `PM.not_ham_of_mate_eq` | `repair/Repair/HybridPair/CommonEdge.lean` | ham-spin `core/Pairing/Basic.lean` | `81fccb6:repair/Repair/HybridPair/CommonEdge.lean:135` |
| `PM.not_ham_of_mate_eq_of_two_lt` | `repair/Repair/PairRecursion.lean` | ham-spin `core/Pairing/Basic.lean` | `81fccb6:repair/Repair/PairRecursion.lean:580` |
| `RRC.hamEvent` | `suppression/Suppression/ChainRule.lean` | `suppression/Suppression/HamCount.lean` | `81fccb6:suppression/Suppression/ChainRule.lean:2045` |

## Same name, weaker hypotheses

| name | dropped | location | last old form |
|---|---|---|---|
| `PM.ham_iff_cycleCount_eq_one` | `[Nonempty V]` | `repair/Repair/CycleCount.lean` | `81fccb6:repair/Repair/CycleCount.lean:49` |
| `PM.HasClosedCycle` | `[DecidableEq V]` | ham-spin `clifford/Clifford/Contraction.lean` | `0360f0d:clifford/Clifford/Contraction.lean:284` |
| `PM.not_hasClosedCycle_of_ham`, `PM.hasClosedCycle_self` | `[DecidableEq V]` | `repair/Repair/HybridPair/MeanCount.lean` | `81fccb6:repair/Repair/HybridPair/MeanCount.lean:84`, `:94` |
| `RRC.shift`, `RRC.shift_none`, `RRC.shift_some`, `RRC.shift_inv_none`, `RRC.shift_inv_some` | `[NeZero m]` | `suppression/Suppression/HamCount.lean` | `81fccb6:suppression/Suppression/HamCount.lean:40` to `:61` |
| `RRC.scale`, `RRC.scale_none`, `RRC.scale_some`, `RRC.scale_inv_none`, `RRC.scale_inv_some` | `[NeZero m]` | `repair/Repair/FactorCap/Scale.lean` | `81fccb6:repair/Repair/FactorCap/Scale.lean:26` to `:48` |
| `RRC.edgeLabel`, `RRC.affinePerm`, `RRC.affine_inj`, `RRC.affinePerm_some`, `RRC.affinePerm_injective` | `[NeZero m]` | `repair/Repair/Automorphism.lean` | `81fccb6:repair/Repair/Automorphism.lean` |
| `FactorCap.endVtx`, `FactorCap.capFn` | `[NeZero m]` | `repair/Repair/FactorCap/Construction.lean` | `81fccb6:repair/Repair/FactorCap/Construction.lean:98`, `:102` |
| `FactorCap.capCenter`, `FactorCap.gadget` | `[NeZero m]` | `repair/Repair/FactorCap/Tail.lean` | `81fccb6:repair/Repair/FactorCap/Tail.lean:38`, `:48` |
| `RRC.zigPos`, `RRC.zigPos_none`, `RRC.zigPos_some`, `RRC.zigPos_injective` | `[NeZero m]` | `repair/Repair/FactorCap/ZigZag.lean` | `81fccb6:repair/Repair/FactorCap/ZigZag.lean:61` |
| `RRC.zigPos_scale_some`, `RRC.gap_of_abs_gap` | `[NeZero m]` | `repair/Repair/HybridPair/Contexts.lean` | `81fccb6:repair/Repair/HybridPair/Contexts.lean` |
| `RRC.rainbow`, `RRC.infSquare`, `RRC.ladderSquare` | `[NeZero m]` | `repair/Repair/TripleUnion.lean` | `81fccb6:repair/Repair/TripleUnion.lean:282`, `:455`, `:715` |
| `RRC.apTriangle`, `RRC.none_mem_apTriangle`, `RRC.ladder_ends` | `[NeZero m]` | `repair/Repair/TripleUnionAP.lean` | `81fccb6:repair/Repair/TripleUnionAP.lean` |
| `RRC.card_gadget` | `[NeZero m]` | `repair/Repair/SqrtObstructions/CertLength.lean` | `81fccb6:repair/Repair/SqrtObstructions/CertLength.lean:468` |

## Same statement, new proof

| name | now proved from | location | last old proof |
|---|---|---|---|
| `RoundRobin.Covering.not_ham_self` | `PM.not_ham_of_mate_eq` | `repair/Repair/Covering/Basic.lean` | `81fccb6:repair/Repair/Covering/Basic.lean:200` |
| `RRC.ham_factor_of_ne` | `RRC.ham_factor_of_isUnit_sub` | `repair/Repair/SqrtObstructions/CertLength.lean` | `81fccb6:repair/Repair/SqrtObstructions/CertLength.lean:94` |
| `FactorCap.not_farey_hit` | `FactorCap.not_farey_hit_of_coprime` | `repair/Repair/FactorCap/Farey.lean` | `81fccb6:repair/Repair/FactorCap/Farey.lean:51` |

## New generalized forms

| name | generalizes | location |
|---|---|---|
| `FactorCap.not_farey_hit_of_coprime` | `not_farey_hit` (prime `n` becomes `Nat.Coprime n μ`) | `repair/Repair/FactorCap/Farey.lean` |
| `RRC.ham_factor_of_isUnit_sub` | `ham_factor_of_ne` (prime `n` becomes `IsUnit (s - t)`) | `repair/Repair/FactorCap/Scale.lean` |
| `RRC.familyRepairBound_hamEvent_iff` | bridge `FamilyRepairBound (hamEvent m) ↔ RepairBound` | `repair/Repair/SqrtObstructions/NoGo.lean` |

## Removed

| name | location | last old form |
|---|---|---|
| `unit5`, `unit7` (private, unused) | `repair/Repair/TripleUnion.lean` | `81fccb6:repair/Repair/TripleUnion.lean:368`, `:373` |

## Risky items (COD-245, branch `review-risky`)

The items of `REVIEW.md` that were left for the user, done on ham_pairings only, from main
`7168bcb`. Every "last old form" is at main `7168bcb` unless stated. The changes are in `8ba5211`
(duplicate endpoints, D5 to D7), `70612aa` (dead lemmas, U6), `a84cdde` (P9 for `n` coprime to
`105`, O7 and O8) and `19ef46a` (the cycle count taken from ham-spin `fd082bf`). The names below
were checked against ham_pairings, ham-spin (`a2e8996`) and `organize-archive/results/` before
removal. A removed name without an alias is cited by none of them.

### Removed duplicates

| old name | use instead | last old form |
|---|---|---|
| `ChainRule.div_le_neg_log_prob_avoid_of_reweight` | `ChainRule.div_le_neg_log_prob_avoid` (same statement) | `7168bcb:suppression/Suppression/Reweighted.lean:1313` |
| `ChainRule.neg_log_prob_avoid_le_div_of_reweight` | `ChainRule.neg_log_prob_avoid_le_div` (same statement) | `7168bcb:suppression/Suppression/Reweighted.lean:1358` |
| `ChainRule.div_le_neg_log_prob_avoid_of_pairInfo_of_reweight` | `ChainRule.div_le_neg_log_prob_avoid_of_pairInfo` (same statement) | `7168bcb:suppression/Suppression/Reweighted.lean:1415` |
| `ChainRule.neg_log_prob_avoid_le_div_of_pairInfo_of_reweight` | `ChainRule.neg_log_prob_avoid_le_div_of_pairInfo` (same statement) | `7168bcb:suppression/Suppression/Reweighted.lean:1424` |
| `ChainRule.div_le_neg_log_prob_avoid_of_reweight'` | `ChainRule.div_le_neg_log_prob_avoid` (same statement) | `7168bcb:suppression/Suppression/VMinus.lean:636` |
| `ChainRule.neg_log_prob_avoid_le_div_of_reweight'` | `ChainRule.neg_log_prob_avoid_le_div` (same statement) | `7168bcb:suppression/Suppression/VMinus.lean:654` |
| `Tilt.sbRatio_le` | `Tilt.sbRatio_le_of_pairDeficit_le` (without `p 0 > 0`, `p k > 0`) | `7168bcb:suppression/Suppression/Tilt.lean:629` |
| `Tilt.pair_criterion_weak` | `Tilt.exp_neg_div_le_of_pairDeficit_le` (without `p 0 > 0`, `p k > 0`) | `7168bcb:suppression/Suppression/Tilt.lean:701` |
| `RRC.fano_hamLaw'` | `RRC.fano_hamLaw` (same type now) | `7168bcb:suppression/Suppression/Tilt.lean:777` |

"Same statement" means the same hypotheses and conclusion with the implicit and instance binders
in another order. The `_of_reweight` forms proved Theorem 7 of COD-196 through Theorem 3 of
COD-198. That route stays in the `_harmonic` forms of `suppression/Suppression/VMinus.lean`.

### Deprecated aliases

Each alias has the type of its target, so its statement is the old one with weaker hypotheses.

| old name | alias of | hypotheses dropped | last old form |
|---|---|---|---|
| `Tilt.fano_criterion` | `Tilt.exp_neg_div_le_of_fano_le` | `p 0 > 0`, `p k > 0` | `7168bcb:suppression/Suppression/Tilt.lean:470` |
| `Tilt.pair_criterion` | `Tilt.exp_neg_mul_log_le_of_pairDeficit_le` | `p 0 > 0`, `p k > 0` | `7168bcb:suppression/Suppression/Tilt.lean:678` |
| `SizeBias.upper_reduction` | `SizeBias.upper_reduction_of_le_add_two` | `(1 + ε) μ ≤ J` becomes `≤ J + 2` | `7168bcb:suppression/Suppression/SizeBias.lean:292` |
| `SizeBias.upper_reduction_sqrt` | `SizeBias.upper_reduction_sqrt_of_le_add_two` | `(1 + ε) μ ≤ J` becomes `≤ J + 2` | `7168bcb:suppression/Suppression/SizeBias.lean:321` |

### Same name, weaker hypotheses

| name | change | location | last old form |
|---|---|---|---|
| `Tilt.le_exp_neg_of_fano_nonneg` | drops `p 0 > 0`, `p k > 0` | `suppression/Suppression/Tilt.lean` | `7168bcb:suppression/Suppression/Tilt.lean:505` |
| `RRC.fano_hamLaw` | drops `∃ P, Ham P (factor m 0)`, now the proof of `fano_hamLaw'` | `suppression/Suppression/Tilt.lean` | `7168bcb:suppression/Suppression/Tilt.lean:819` |
| `FactorCap.exists_checked_cell`, `FactorCap.cell_facts` | `n.Prime` and `0 < μ` become `Nat.Coprime n μ` | `repair/Repair/FactorCap/Cover.lean` | `7168bcb:repair/Repair/FactorCap/Cover.lean:24`, `:32` |
| `FactorCap.not_ham_capMatching` | `(2m - 1).Prime` and `u ≠ 0` become `IsUnit u` | `repair/Repair/FactorCap/Construction.lean` | `7168bcb:repair/Repair/FactorCap/Construction.lean:194` |

### Renamed

| old name | new name | location | last old form |
|---|---|---|---|
| `FactorCap.exists_contains_of_prime` | `FactorCap.exists_contains_of_coprime` (`n.Prime` and `0 < μ` become `Nat.Coprime n μ`, no alias) | `repair/Repair/FactorCap/Checker.lean` | `7168bcb:repair/Repair/FactorCap/Checker.lean:233` |

### Same statement, new proof

| name | now proved from | location | last old proof |
|---|---|---|---|
| `FactorCap.isZeroState_capMatching` | `FactorCap.isZeroState_capMatching_of_coprime` | `repair/Repair/FactorCap/Construction.lean` | `7168bcb:repair/Repair/FactorCap/Construction.lean:280` |
| `FactorCap.isZeroState_capState` | `FactorCap.isZeroState_capState_of_coprime` | `repair/Repair/FactorCap/Tail.lean` | `7168bcb:repair/Repair/FactorCap/Tail.lean:114` |
| `FactorCap.factorTail_cap` | `FactorCap.factorTail_cap_of_coprime` | `repair/Repair/FactorCap/Tail.lean` | `7168bcb:repair/Repair/FactorCap/Tail.lean:172` |

### New generalized forms

| name | generalizes | location |
|---|---|---|
| `FactorCap.factorTail_cap_of_coprime` | `factorTail_cap` (prime `n` becomes `Nat.Coprime n 105`) | `repair/Repair/FactorCap/Tail.lean` |
| `FactorCap.isZeroState_capState_of_coprime` | `isZeroState_capState` (the same) | `repair/Repair/FactorCap/Tail.lean` |
| `FactorCap.isZeroState_capMatching_of_coprime` | `isZeroState_capMatching` (the same) | `repair/Repair/FactorCap/Construction.lean` |
| `FactorCap.not_ham_capMatching_of_not_isUnit` | the non-unit factors, including `u = 0` | `repair/Repair/FactorCap/Construction.lean` |
| `FactorCap.not_dvd_endInt`, `FactorCap.coprime_105_of_prime` | helpers of the above | `repair/Repair/FactorCap/Construction.lean` |

### Removed dead lemmas

Item U6 of `REVIEW.md`, used nowhere and cited nowhere.

| name | location | last old form |
|---|---|---|
| `RRC.coe_autEquiv`, `RRC.coe_autGroupMulEquiv` | `repair/Repair/Automorphism.lean` | `7168bcb:repair/Repair/Automorphism.lean:325`, `:405` |
| `RRC.PSL211.mem_symZero` | `repair/Repair/ExceptionalSix.lean` | `7168bcb:repair/Repair/ExceptionalSix.lean:323` |
| `PM.coe_liftEquiv` | `repair/Repair/FreeDefects.lean` | `7168bcb:repair/Repair/FreeDefects.lean:670` |
| `PM.cycleOf_eq_iff_mem` | `repair/Repair/PairRecursion.lean` | `7168bcb:repair/Repair/PairRecursion.lean:648` |
| `IsFourCycle.reverse` | `repair/Repair/TripleUnion.lean` | `7168bcb:repair/Repair/TripleUnion.lean:120` |
| `PM.cycleCount_comm` | `repair/Repair/CycleCount.lean` (ham-spin `core/Pairing/Union.lean` at `fd082bf` still declares it) | `7168bcb:repair/Repair/CycleCount.lean:61` |

### Module moved to ham-spin

Done in `19ef46a`, which requires ham-spin at `fd082bf`. Every declaration name is unchanged, so
there are no aliases. Its importers now import `Pairing.Union`.

| old module | new module | last old form |
|---|---|---|
| `Repair.CycleCount` (`repair/Repair/CycleCount.lean`) | ham-spin `Pairing.Union` (`core/Pairing/Union.lean`, `fd082bf`) | `ea9376f:repair/Repair/CycleCount.lean`, and `7168bcb:repair/Repair/CycleCount.lean`, the version ham-spin copied |

The ham-spin copy is the `7168bcb` file, so `PM.cycleCount_comm`, removed here in `70612aa`, is
still declared there. The endpoints `PM.ham_iff_cycleCount_eq_one`, `PM.cycleCount_le_contractAt`,
`PM.cycleCount_le_contractAt_add_one` and `PM.sum_pow_cycleCount_le` moved from this
`AxiomCheck.lean` to the ham-spin `AxiomCheck.lean` (`fd082bf`).

## Affine maps and the automorphism group moved to ham-spin (COD-259, branch `agl-main`)

Done in `760cd71`, for ham-spin branch `agl` (`c1941cf` moves the declarations, `7f4fd9b` adds the
AGL instance of the polar section). Every declaration name and namespace is unchanged, so there
are no aliases. Every "last old form" is at main `d1cda40`. ham-spin `HISTORY.md` lists the same
moves.

### Module moved to ham-spin

| old module | new module | last old form |
|---|---|---|
| `Repair.Automorphism` (`repair/Repair/Automorphism.lean`) | ham-spin `Pairing.Automorphism` (`core/Pairing/Automorphism.lean`, `c1941cf`) | `d1cda40:repair/Repair/Automorphism.lean` |

`Repair.Automorphism` stays as a module that imports `Pairing.Automorphism` and
`Repair.FactorCap.Tail`, so its importers are unchanged.

### Declarations moved to ham-spin (same full name)

| name | old location | new location | last old form |
|---|---|---|---|
| `RRC.shift`, `RRC.shift_none`, `RRC.shift_some`, `RRC.shift_inv_none`, `RRC.shift_inv_some`, `RRC.shift_smul_factor` | `suppression/Suppression/HamCount.lean` | ham-spin `core/Pairing/Affine.lean` (`c1941cf`) | `d1cda40:suppression/Suppression/HamCount.lean:40` to `:66` |
| `RRC.scale`, `RRC.scale_none`, `RRC.scale_some`, `RRC.scale_inv_none`, `RRC.scale_inv_some`, `RRC.scale_smul_factor`, `RRC.scale_mate_factor`, `RRC.affine_smul_factor`, `RRC.isZeroState_affine_smul_iff` | `repair/Repair/FactorCap/Scale.lean` | ham-spin `core/Pairing/Affine.lean` (`c1941cf`) | `d1cda40:repair/Repair/FactorCap/Scale.lean:26` to `:73`, `:90` |
| `RRC.two_mul_natCast_self`, `RRC.natCast_injOn` | `repair/Repair/ZeroState.lean` | ham-spin `core/Pairing/Affine.lean` (`c1941cf`) | `d1cda40:repair/Repair/ZeroState.lean:94`, `:103` |
| `FactorCap.gadget` | `repair/Repair/FactorCap/Tail.lean` | ham-spin `core/Pairing/Automorphism.lean` (`c1941cf`) | `d1cda40:repair/Repair/FactorCap/Tail.lean:49` |
| every declaration of `Repair.Automorphism`, from `RRC.IsAut` to `RRC.isAut_three_moebius` | `repair/Repair/Automorphism.lean` | ham-spin `core/Pairing/Automorphism.lean` (`c1941cf`) | `d1cda40:repair/Repair/Automorphism.lean:41` to `:506` |

`Suppression.HamCount`, `Repair.ZeroState` and `Repair.FactorCap.Tail` now import
`Pairing.Affine` or `Pairing.Automorphism`. `RRC.ham_factor_of_isUnit_sub` stays in
`repair/Repair/FactorCap/Scale.lean`.

### AxiomCheck

862 endpoints at `d1cda40`, 843 after. The 19 endpoints of the moved declarations
(`RRC.shift_smul_factor`, `RRC.scale_smul_factor`, `RRC.isZeroState_affine_smul_iff` and the 16
from `RRC.isAut_affine` to `RRC.isAut_three_moebius`) moved to the ham-spin `AxiomCheck.lean`
(`c1941cf`), which also checks the four new AGL theorems (`7f4fd9b`).

## Involution-product bridge (COD-266 stage 2, branch `mig`)

The walk engines moved onto the involution-product bridge, ham-spin
`core/Pairing/InvolutionProduct.lean` (`fe1f6bf`), from main `77d3de5`. Every "last old form" is at
main `77d3de5`.

### Moved to ham-spin (same full name)

| name | old location | new location | last old form |
|---|---|---|---|
| `PM.mate_inv`, `PM.mate_mul_self`, `PM.not_sameCycle_mate_right`, `PM.not_sameCycle_mate_left` | `repair/Repair/SqrtObstructions/CoreCertLength.lean` | ham-spin `core/Pairing/InvolutionProduct.lean` (`fe1f6bf`) | `77d3de5:repair/Repair/SqrtObstructions/CoreCertLength.lean:45`, `:50`, `:68`, `:94` |

### Same statement, new proof

| name | now proved from | location | last old proof |
|---|---|---|---|
| `PM.exists_pow_eq_of_closed` | `PM.card_reachable_eq_two_mul` | `repair/Repair/SqrtObstructions/CoreCertLength.lean` | `77d3de5:repair/Repair/SqrtObstructions/CoreCertLength.lean:104` |
