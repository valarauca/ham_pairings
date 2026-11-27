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
