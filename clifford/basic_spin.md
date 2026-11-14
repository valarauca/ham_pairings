# Basic spin identification of W_n (COD-105)

**Claim.** For n ≥ 1, W_n ⊗ k is the reduction mod 2 of the basic spin representation of
S̃_{2n}, for every field k of characteristic 2. It is irreducible of dimension 2^(n-1). For
n ≥ 2 the module is D^(n+1,n-1).

**Status.** Proved in Lean, in the `Spin` library, except for the D^λ label. The only definitional
input is Schur's definition of a basic spin representation, as a simple module over the Clifford
algebra of the A_{2n-1} root form. Wales 7.7 at p = 2, Wales 8.1 and Brauer's count are no longer
used. Benson 5.1 is still cited, but only for the name D^(n+1,n-1).

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

## What Lean proves

### Definitions

- `schurQ K m` is Q(x) = -Σ x_j² + Σ x_j x_{j+1} on K^m, the negated A_m root form. Its Gram
  matrix `schurG` has integer entries.
- `Stilde m` is S̃_m, presented on z and t_j by Maas's relations. `Stilde.toPerm` sends t_j to the
  transposition (j, j+1).
- `schurHom` sends t_j to ι(b_j) and z to -1 in `CliffordAlgebra (schurQ K (m-1))`. This is
  Schur's realization of S̃_m.
- A basic spin representation of S̃_{2n} over an algebraically closed field K of characteristic 0
  is a simple `CliffordAlgebra (schurQ K (2n-1))`-module Y, viewed as a representation through
  `schurHom`. Both associates are such modules.
- A lattice is a K-basis of Y in which every ι(b_j) has its matrix entries in a subring R ⊆ K. A
  reduction is a ring hom ψ from R to a field k of characteristic 2. `redMat` applies ψ entrywise.

### Results

| Statement | Lean |
|---|---|
| Every Cl(U_n, q)-module over a field of characteristic 2 contains k ⊗ W_n | `exists_injective_intertwiner` |
| A Cl(U_n, q)-module of dimension 2^(n-1) is isomorphic to k ⊗ W_n | `exists_intertwining_equiv` |
| Schur's form is nondegenerate in characteristic 0 | `schurQ_nondegenerate` |
| A simple Cl_K(schurQ)-module has dimension at most 2^(n-1) | `finrank_le_of_simple` |
| A basic spin representation with a lattice has dimension 2^(n-1) | `finrank_eq_of_lattice` |
| Its reduction is isomorphic to k ⊗ W_n as a kS̃_{2n}-module, with S̃_{2n} acting on k ⊗ W_n through S_{2n} | `reduction_basicSpin` |
| Its reduction is irreducible | `reduction_irreducible` |
| A basic spin representation and a lattice exist, with R a valuation subring of K and k its residue field | `cod105` |

`reduction_basicSpin` holds for every basic spin representation, every lattice and every reduction
map. So both associates reduce to the same module, which is Wales's X̄ = X̄* at p = 2, and the
result does not depend on the lattice.

### How the proof goes

- **Characteristic 2** (`Char2Modules.lean`). The elements ι(v_{2a,2a+1}) + 1 square to zero and
  commute, so every nonzero module has a vector m₀ that they all kill. Sending w_S to the product
  of the ι(v_{2g+1,2g+2}) over g ∈ S, applied to m₀, intertwines the Clifford action. The map is
  injective because k ⊗ W_n is simple (`ρK_invariant_eq_bot_or_top`).
- **Reduction** (`Reduce.lean`, `Reduction.lean`). The relation t_j t_{j+1} + t_{j+1} t_j = 1 is
  linear. It holds for the integral matrices because R ⊆ K is injective, and so it survives ψ.
  The group relations of S̃_{2n} alone would not give this, since the trivial representation
  satisfies them mod 2. Mod 2, b_j maps to v_{j,j+1} and the Gram matrix of `schurQ` becomes the
  polar form of q, so the reduced matrices define a Cl(U_n, q)-module (`reduceHom`).
- **Characteristic 0** (`JSystem.lean`, `BasicSpin.lean`). An orthonormal basis of `schurQ` gives
  2n-1 anticommuting involutions J_j. With E_k = J_{2k} + iJ_{2k+1} and F_k = J_{2k} - iJ_{2k+1}, a
  vacuum vector and the tower A_{j+1} = A_j + F_j A_j give dim Y ≤ 2^(n-1). The lower bound comes
  from the characteristic 2 side, because the reduction contains k ⊗ W_n.
- **Existence** (`Monomials.lean`, `Existence.lean`, `Witness.lean`). Ordered monomials in the
  t_j span Cl_K(schurQ), so it is finite over K and has a simple left ideal. A valuation subring V
  of K with 2 in its maximal ideal exists. The V-span of the ordered monomials applied to a basis
  is a finitely generated, torsion-free V-module, hence free, and a V-basis of it is a K-basis of
  Y with V-integral matrices.

Benson's basis u_I of Δ_K is integral for the e_j. When j and k lie in different pairs,
[jk] = ½√2(e_j - e_k) has entries ±½√2 in it, which is why the lattice is built abstractly rather
than from the u_I.

### Facts about W_n used above

| Fact | Lean |
|---|---|
| W_n ⊗ K is irreducible for every field K of characteristic 2 | `adjoin_ρK_eq_top`, `ρK_invariant_eq_bot_or_top` |
| The Clifford action on W_n is onto End(W_n) | `cliffordRep_surjective` |
| dim W_n = 2^(n−1) | `finrank_W_eq` |
| The basis w_S and the frame operators | `lower_w`, `frameF_w`, `B_rowW_P0` |
| W_n is isomorphic to Maas's GF(2) model | `toMatrix_ρW_adj`, `wBasis_equivFun_ρW`, `maasGen_closed` |

With `reduction_basicSpin`, the last row also proves Maas's claim that his model is basic spin.

## The four COD-105 items

1. **Primary source.** Wales was checked, and covers p = 2. The result no longer depends on it.
2. **Minimal polynomial on every composition factor.** No longer needed, since the identification
   no longer goes through Wales 8.1. `minpoly_ρK_threeCycle` still holds.
3. **2n = 4.** Covered by `reduction_basicSpin` with n = 2, without Brauer's count.
4. **Dimension 2^(n−1).** Proved, by `finrank_eq_of_lattice` and `finrank_W_eq`. The label
   D^(n+1,n−1) comes from Benson 5.1 through Morotti.

## Not formalized

- The label D^(n+1,n−1). Mathlib has no Specht modules or D^λ, so Benson 5.1 remains a citation.
