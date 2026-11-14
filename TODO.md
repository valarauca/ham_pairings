# TODO (COD-105 follow-up)

Handoff notes from a review of commit `d6b896d` against Linear COD-105
("Settle the basic-spin identification of W_n").

## Current state

- `d6b896d` is on `origin/main`. The working tree was clean at review time.
- Every theorem named in `clifford/basic_spin.md` exists with the stated form.
  `ρW_threeCycle_sq_add`, `adjoin_ρW_eq_top`, `invariant_eq_bot_or_top`, `minpoly_ρW_threeCycle`,
  `ρW_threeCycle_ne_smul_one`, `finrank_W_eq`, `eq_zero_of_ρW_threeCycle_fixed` and
  `not_isNilpotent_ρW_threeCycle_sub_one` are all in `clifford/Clifford/Corollaries.lean`,
  `Irreducible.lean` or `Dimension.lean`.
- No `sorry`, `axiom`, `admit` or `native_decide` appears in the sources. No built `.olean` contains
  `sorryAx`, and every `.olean` is newer than its source. `AxiomCheck.lean` was not run.
- The Maas quotes in `clifford/basic_spin.md` match arXiv:0911.3794 verbatim. That covers the
  intro sentence on p = 2, Definition 2, Proposition 3 and Theorem 1 (2), (3).

## Blockers

### Mathlib cannot state the identification

Mathlib has no double cover S̃_n, no Schur basic spin representation, no modular reduction, no
Specht modules and no D^λ. The isomorphism W_n ⊗ F̄₂ ≅ basic spin therefore cannot be stated in
Lean. The most Lean can reach is an isomorphism between W_n and an explicit model, such as Maas's
GF(2) construction (`S`, `S_I`, Table 1). Calling that model "basic spin" still depends on Wales.

### Gaps in COD-105 itself

1. **Primary source not read.** COD-105 item 1 asks for the statement and hypotheses from the
   primary source. The note quotes only Maas. Maas attributes Theorem 1 (2) to Wales Thm 7.7 and
   Theorem 1 (3) to Wales Thm 8.1, and says "the case n = 4 in (3) is handled by direct
   inspection". Wales was never checked, and in particular it is unconfirmed that Wales covers p = 2.
2. **2n = 4 argument rests on a reading.** The note avoids the exception in Theorem 1 (3)
   ("an ordinary 2-dimensional representation of S̃4 which contains z in its kernel") by reading
   "ordinary" as characteristic 0. W_2 is in fact a 2-dimensional representation with z in the
   kernel, because S_4 acts on the three matchings of K_4 through S_3. Replace the argument with a
   direct one that avoids the exception.
   - Theorem 1 (2) makes Y_4 irreducible of degree δ(S̃_4) = 2 in characteristic 2.
   - The 2-regular classes of S_4 are the identity and the 3-cycles. So F̄₂S_4 has exactly two
     simple modules, the trivial module and the 2-dimensional D^(3,1).
   - W_2 ⊗ F̄₂ is irreducible of dimension 2. So W_2 ⊗ F̄₂ ≅ D^(3,1) ≅ Y_4.
3. **The D^(n+1,n-1) label has no source.** The COD-105 claim and the archive ledgers name the
   module D^(n+1,n-1). Maas never uses D^λ labels, and `basic_spin.md` only says "the archive,
   following Morotti, writes it D^(n+1,n-1)". Either cite a source that identifies the 2-modular
   basic spin module of S_{2n} with D^(n+1,n-1) (Benson 1988, "Spin modules for symmetric groups",
   is the likely one, unverified), or restate the result as W_n ⊗ F̄₂ ≅ Y_{2n} and drop the label.
4. **Base change is on paper only.** Lean proves `adjoin_ρW_eq_top` over F₂. Absolute
   irreducibility of W_n ⊗ F̄₂ and the invariance of the minimal polynomial under extension of
   scalars are argued in prose, not in Lean. This is standard and low priority.

## Tasks

- [x] Obtain Wales, "Some projective representations of S_n", J. Algebra 61 (1979) 37–57. Quote
      Theorems 7.7 and 8.1 with hypotheses in `clifford/basic_spin.md`. Record whether p = 2 is
      covered. If it is not, the conditional result rests only on Maas's restatement, and the note
      must say so.
- [x] Replace the 2n = 4 paragraph in `clifford/basic_spin.md` with the direct argument above.
- [x] Source the D^(n+1,n-1) label, or drop it in favour of Y_{2n}.
- [x] Optional. For 2n ≥ 6, Proposition 3 is not needed, because W_n ⊗ F̄₂ is absolutely
      irreducible and Theorem 1 (3) applies directly. Simplify the "By case" section.
- [x] Optional Lean. Prove irreducibility of `W ⊗ K` for any field `K` of characteristic 2, or
      `Algebra.adjoin K (range (ρW.baseChange K)) = ⊤`, to close gap 4.
- [x] Optional Lean. Formalize Maas's GF(2) model and an explicit intertwiner with W_n. This is
      the "explicit basic-spin intertwiner" alternative listed in COD-105. It does not remove the
      dependence on Wales.
- [x] Run `lake env lean AxiomCheck.lean` and confirm each endpoint uses only `propext`,
      `Classical.choice` and `Quot.sound`.

## Linear

- Project "Hamiltonian Prefect Pairing" (P-COD-3), team COD. COD-105 is blocked by COD-102 and
  COD-103.
- **Never edit an issue description once it is opened. Record findings as comments.** Status,
  relations and attachments may change. See the team document "Agent conventions".
- COD-105 can close as conditional once the Wales check and the label task are done. Link the
  commit and `clifford/basic_spin.md` in the closing comment.
- `d6b896d` also claims COD-103 and COD-104. Check their comments before closing them.
