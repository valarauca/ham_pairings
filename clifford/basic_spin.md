# Basic spin identification of W_n (COD-105)

For n ≥ 2, the claim is that W_n ⊗ F̄₂ is the basic spin module of S_{2n} in characteristic 2
(the archive, following Morotti, writes it D^(n+1,n-1)).

This stays conditional on one cited theorem. Mathlib has no Specht modules, basic spin
representations or Wales recognition theorem, so the isomorphism cannot be stated in Lean. Every
hypothesis of the cited theorem is proved in Lean, in the `Clifford` library.

## Cited statements

L. A. Maas, "On a Construction of the Basic Spin Representations of Symmetric Groups",
Comm. Algebra 38(12) (2010), 4545–4552, arXiv:0911.3794. Quoted from the arXiv version.

> If we consider representations over a splitting field of characteristic p = 2, then every
> representation of S̃n or Ŝn contains the central element z in its kernel, and essentially, we
> deal with 2-modular representations of Sn.

> Definition 2. Let T = (T1, ..., Tn−1) be a representation of S̃n over a field K. We say that
> T satisfies ∆ if
> (∆) (Z Ti Ti+1)² + Z Ti Ti+1 + I = 0 for i ∈ {1, ..., n − 2}.

> Proposition 3. Let n ≥ 4 and T = (T1, ..., Tn−1) be a representation of S̃n over a splitting
> field K of characteristic p ≥ 0. For n = 4 or p = 3 we shall assume that z ∉ ker T. If T
> satisfies ∆, then all T-composition factors are basic spin.

> Theorem 1. (2) For any prime number p, the modular reduction Xn± = Yn± over a splitting field
> of characteristic p is irreducible unless p | n and n is odd. [...]
> (3) Let n ≥ 4. Assume that T is an absolutely irreducible representation of S̃n, and let
> t ∈ S̃n be an element of order 3 projecting to a 3-cycle in Sn. If tT has a quadratic minimal
> polynomial, then T is equivalent to a basic spin representation of S̃n, or T is an ordinary
> 2-dimensional representation of S̃4 which contains z in its kernel.

Maas gives the degree of a basic spin representation of S̃_{2k} as δ = 2^{k-1}, and attributes
Theorem 1 (2) and (3) to D. B. Wales, "Some projective representations of Sn", J. Algebra 61
(1979), 37–57, Theorems 7.7 and 8.1. Wales was not checked directly.

## Hypotheses and where they are proved

Here S̃ is taken on 2n letters, Z = I in characteristic 2, and T_i = ρ((i i+1)).

| Hypothesis | Lean |
|---|---|
| ∆, that is ρ(τ)² + ρ(τ) + 1 = 0 for the 3-cycles τ = (i i+1)(i+1 i+2) | `ρW_threeCycle_sq_add`, for every 3-cycle |
| W_n is absolutely irreducible, so W_n ⊗ F̄₂ is its own only composition factor | `adjoin_ρW_eq_top`, `invariant_eq_bot_or_top` |
| A 3-cycle has quadratic minimal polynomial | `minpoly_ρW_threeCycle` (it is x² + x + 1) |
| ρ(τ) is not a scalar | `ρW_threeCycle_ne_smul_one` |
| dim W_n = 2^{n-1} = δ(S̃_{2n}) | `finrank_W_eq`, proved without citing CKN |
| A 3-cycle fixes no nonzero vector and is not unipotent | `eq_zero_of_ρW_threeCycle_fixed`, `not_isNilpotent_ρW_threeCycle_sub_one` |

The minimal polynomial of an operator does not change under extension of scalars, so the
F₂ statements carry over to F̄₂.

## By case

- **2n ≥ 6.** Proposition 3 applies with p = 2, because its extra hypothesis z ∉ ker T is
  needed only for 2n = 4 or p = 3. Every composition factor of W_n ⊗ F̄₂ is basic spin, and there
  is only one. Theorem 1 (2) gives an irreducible reduction of degree 2^{n-1} for 2n even, which
  matches `finrank_W_eq`.
- **2n = 4.** Proposition 3 does not apply, since z ∈ ker T in characteristic 2. Theorem 1 (3)
  applies instead, because W_2 ⊗ F̄₂ is absolutely irreducible and a 3-cycle acts with minimal
  polynomial x² + x + 1. Reading "ordinary" as characteristic 0, its second alternative does not
  arise here, so W_2 ⊗ F̄₂ is basic spin.

## The four COD-105 items

1. The criterion covers characteristic 2, as quoted, except that 2n = 4 is handled by Theorem 1 (3)
   instead of Proposition 3.
2. The quadratic minimal polynomial holds on every composition factor, because there is exactly one
   (`adjoin_ρW_eq_top`) and on it the minimal polynomial is x² + x + 1.
3. For 2n = 4, the case follows from Theorem 1 (3) and the Lean facts in the last table row.
4. The factor dimension 2^{n-1} comes from Maas's degree table and Theorem 1 (2), citing Wales
   Theorem 7.7. On the W_n side it is `finrank_W_eq`.
