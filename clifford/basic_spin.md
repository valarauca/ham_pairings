# Basic spin identification of W_n (COD-105)

**Claim.** For n ≥ 2, W_n ⊗ F̄₂ is the 2-modular basic spin module of S_{2n}. That module is
D^(n+1,n-1), of dimension 2^(n-1).

**Status.** Conditional on the cited theorems below. Mathlib has no double cover S̃_n, no basic
spin representation, no D^λ and no Brauer theory, so the identification itself cannot be stated
in Lean. Every hypothesis that the cited theorems put on W_n is proved in Lean, in the `Clifford`
library. Lean also proves an explicit isomorphism between W_n and Maas's GF(2) model of the basic
spin representation.

## Cited statements

Quotes are transcribed from the PDF scans. The ~ on S̃_n is Wales's S_n^-.

**D. B. Wales, "Some projective representations of S_n", J. Algebra 61 (1979), 37–57,
doi:10.1016/0021-8693(79)90304-1.**

> §1. If p = 2, these are faithful 2-modular representations of S_n as −1 is in the 2-modular
> kernel.

> §7. In this section we investigate V^G in the case in which k has characteristic p and is a
> splitting field for the representations appearing.

> Theorem 7.7. Let X_n be the ordinary basic representation ⟨n⟩ described in Table I. Then X̄_n is
> irreducible unless p | n and n is odd. [...] For n even X̄_n ≇ X̄_n* unless p | n in which case
> X̄_n ≅ X̄_n*. Note for p = 2 that X̄_n = X̄_n*.

> Theorem 8.1. Suppose Y is an irreducible representation of S̃_n for which Y(T) has a quadratic
> minimal polynomial with T an element of order 3 represented in S_n by (123). Assume n ≥ 5. Then
> Y is one of the basic representations Y_n or X_n described in Table III.

Wales works over a splitting field of any characteristic p, and Theorem 7.7 treats p = 2
explicitly, so p = 2 is covered. Theorem 8.1 has no restriction on the characteristic and needs
at least 5 letters.

**D. Benson, "Spin modules for symmetric groups", J. London Math. Soc. (2) 38 (1988), 250–262,
doi:10.1112/jlms/s2-38.2.250.** Here Ā± is the reduction mod 2 of the basic spin
representation.

> Theorem 5.1. As F₂Σ_n-modules, we have Ā⁺ ≅ Ā⁻ ≅ D^(n/2+1,n/2−1) if n is even,
> D^((n+1)/2,(n−1)/2) if n is odd, an irreducible module of dimension 2^[(n−1)/2].

> Lemma 5.3. dim_{F₂} D^([n/2]+1,[(n−1)/2]) = 2^[(n−1)/2].

On 2n letters this gives D^(n+1,n−1), of dimension 2^(n−1).

**A. Kleshchev and P. H. Tiep, Trans. Amer. Math. Soc. 356 (2004), 1971–1999,
doi:10.1090/S0002-9947-03-03364-6.** They work over an algebraically closed field F of
characteristic p, and restate Wales 8.1 as follows.

> Lemma 2.3 ([32, 8.1]). Let n ≥ 5, c = (123)⁺ ∈ Ŝ_n, and V be an irreducible FŜ_n-module on
> which c has a quadratic minimal polynomial. Then V is basic spin.

**L. Morotti, arXiv:1901.06997, §2.** This is the source of the archive's label.

> If p = 2 a special role will be played by the irreducible modules indexed by the partition
> β_n := (⌈(n+1)/2⌉, ⌊(n−1)/2⌋). Such modules (for Σ_n) can be obtained by reducing modulo 2 a
> basic spin module of the covering group of Σ_n and are therefore also called basic spin modules
> (see [4]).

Morotti's [4] is Benson 1988.

**L. A. Maas, Comm. Algebra 38(12) (2010), 4545–4552, arXiv:0911.3794.** Corollary 13 and
Table 1 build a basic spin representation of S̃_m over GF(2) by alternating his constructions S
and S_I. Maas relies on Wales for that claim.

## What Lean proves about W_n

In characteristic 2 the central element of S̃_{2n} acts trivially (Wales §1), so W_n ⊗ F̄₂ is a
representation of S̃_{2n} in which T acts as ρ((123)).

| Hypothesis | Lean |
|---|---|
| W_n ⊗ K is irreducible for every field K of characteristic 2, in particular F̄₂ | `adjoin_ρK_eq_top`, `ρK_invariant_eq_bot_or_top` |
| Over K a 3-cycle has quadratic minimal polynomial, namely x² + x + 1 | `minpoly_ρK_threeCycle` |
| A 3-cycle is not a scalar over K. This uses that a 3-cycle is conjugate to its inverse. | `ρK_threeCycle_ne_smul_one` |
| dim W_n = 2^(n−1) | `finrank_W_eq` |
| W_n is isomorphic to Maas's GF(2) model, by the coordinate map of `wBasis` | `toMatrix_ρW_adj`, `wBasis_equivFun_ρW`, `maasGen_closed` |

The same facts over F₂ are `adjoin_ρW_eq_top` and `minpoly_ρW_threeCycle`.

## By case

- **2n ≥ 6.** Wales 8.1 applies to Y = W_n ⊗ F̄₂, so Y is a basic representation. For 2n even
  and p = 2, Wales 7.7 makes the reduction X̄_{2n} irreducible with X̄_{2n} = X̄_{2n}*, so there is
  one basic module. Benson 5.1 identifies it with D^(n+1,n−1), of dimension 2^(n−1), which
  matches `finrank_W_eq`. Maas's Proposition 3 is not needed.
- **2n = 4.** Wales 8.1 needs at least 5 letters, so this case uses a direct argument.
  - Benson 5.1 with n = 4, or Wales 7.7, gives an irreducible D^(3,1) of dimension 2.
  - The 2-regular classes of S_4 are the identity and the 3-cycles. By Brauer, F̄₂S_4 therefore has
    exactly two simple modules, the trivial module and D^(3,1).
  - W_2 ⊗ F̄₂ is irreducible of dimension 2, so it is D^(3,1).
- **Explicit model.** `toMatrix_ρW_adj` shows that the matrix of ρ((t t+1)) in the basis w_S is
  Maas's generator T_{t+1}. Here S, a set of gaps, is read as a bit vector, and the construction is
  his GF(2) recursion of Table 1. The identification is therefore realized by an explicit linear
  isomorphism, though calling the model basic spin still rests on Wales through Maas.

Benson's proof of Theorem 5.1 uses the same structure as `Dimension.lean`. He builds the module
from the isotropic span of x₁₂, x₃₄, …, checks that 1 + (2j−1, 2j) kills the generator, and
checks Garnir relations on {2j−1, 2j, 2j+1}.

## The four COD-105 items

1. **Primary source.** Wales covers p = 2, as the quotes above show. Theorem 8.1 needs at least 5
   letters, and Theorem 7.7 gives one irreducible basic module for 2n even and p = 2.
2. **Minimal polynomial on every composition factor.** W_n ⊗ F̄₂ is irreducible, so it is its own
   only composition factor. On it the minimal polynomial is x² + x + 1, proved over any field of
   characteristic 2 (`minpoly_ρK_threeCycle`).
3. **2n = 4.** Settled by the direct argument above, without reading "ordinary" in Maas Theorem 1
   (3).
4. **Dimension 2^(n−1).** This comes from Benson Theorem 5.1 and Lemma 5.3 (primary), and the
   label D^(n+1,n−1) comes from Benson through Morotti. On the W_n side it is `finrank_W_eq`.

## Not formalized

These remain citations.
- Wales 7.7 and 8.1.
- Benson 5.1.
- Brauer's count of simple modules.
- Maas's claim that his model is basic spin.
