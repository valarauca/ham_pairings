# Prompt

Expand the sketch below into a complete written proof (LaTeX) of T3 (Clifford action) and T4 (irreducibility), with every lemma it depends on.

- Keep each statement as given. If one is false, stop and report a counterexample instead of weakening it.
- `[OBL]` needs a written argument. `[STD]` may be cited with an exact reference. `[EXT]` stays a named hypothesis.
- `[CHK]` items were verified by exact F₂ computation for n = 2..5 (`check_clifford.py`). They are sanity checks, not proofs.
- The output is mathematics only, with no prose about the process or these instructions.
- Optional: mirror the DAG in §8 in Lean under `binary_stuff/hopefully/Hamiltonian-Pairing-Clifford`.

---

# Sketch

## 0. Objects

$$
V=[2n],\quad \mathcal M_n=\mathrm{PM}(K_{2n}),\quad |\mathcal M_n|=(2n-1)!!,\quad n\ge 2
$$
$$
H[P,Q]=1 \iff P\cup Q \text{ (multigraph; common edge = doubled 2-cycle) is one cycle}
$$
$$
H[\sigma P,\sigma Q]=H[P,Q]\quad(\sigma\in S_{2n})
$$
$$
r_P:=H[P,\cdot]\in\mathbb F_2^{\mathcal M_n},\qquad
W_n:=\mathrm{span}_{\mathbb F_2}\{r_P\}\subseteq \mathbb F_2^{\mathcal M_n},\qquad
(\rho(\sigma)f)(Q)=f(\sigma^{-1}Q)
$$
$$
\rho(\sigma)r_P=r_{\sigma P}\quad\Rightarrow\quad W_n \text{ is an } \mathbb F_2S_{2n}\text{-submodule; no basis choice, no well-definedness issue}
$$
$$
\dim W_n=\operatorname{rank}_{\mathbb F_2}H_{2n}\overset{[\mathrm{EXT:\,CKN}]}{=}2^{n-1}\qquad(\text{only }\le\text{ is needed; see C2})
$$

## 1. Contraction lemma `[OBL]`

$S\subseteq P$ active edges, $A=V(S)$, $|A|=2k$, $P'=P\setminus S$. For $Q\in\mathcal M_n$, the graph $Q\cup P'$ has degree 1 on $A$ and degree 2 off $A$.

$$
Q\cup P' \supseteq \text{closed cycle} \;\Rightarrow\; H[X\cup P',Q]=0\quad\forall X\in\mathrm{PM}(A)
$$
$$
\text{else } Q\cup P'=\bigsqcup_{t=1}^{k}\text{paths} \;\Rightarrow\; \kappa_Q\in\mathrm{PM}(A)\ (\text{endpoint pairing}),\qquad
H[X\cup P',Q]=\big[\,X\cup\kappa_Q \text{ is one cycle on } A\,\big]
$$

Check the doubled-edge convention: a path of length 1 that is also an edge of $X$ is a 2-cycle, which is Hamiltonian iff $k=1$.

## 2. Local parity lemmas

**L-B (4 points)** `[OBL, trivial]`. $A=\{a,b,c,d\}$. For $X,\kappa\in\mathrm{PM}(A)$ (3 pairings each):
$$
X\cup\kappa \text{ one cycle} \iff X\neq\kappa
\;\Rightarrow\; \#\{X: \text{Ham}\}=2
\;\Rightarrow\; \textstyle\sum_{X\in \mathrm{PM}(A)}[\cdot]=0 .
$$

**L-C (6 points)** `[OBL]`. $A=\{a,b,c\}$, $B=\{a',b',c'\}$, $\gamma_0:a\mapsto a',\,b\mapsto b',\,c\mapsto c'$. Matchings $A\leftrightarrow B$ correspond to bijections $\gamma:A\to B$.
$$
\mathcal C:=\gamma_0\circ A_3=\{\gamma_0,\ \gamma_0\tau,\ \gamma_0\tau^2\},\qquad \tau=(a\,b\,c)
$$
For $\kappa\in\mathrm{PM}(A\sqcup B)$: $\#\text{crossing}(\kappa)=3-2\,\#\{AA\text{ edges}\}\in\{1,3\}$.

- **3 crossing.** $\kappa=\kappa_\sigma$ with $\sigma:A\to B$. The alternating walk $a\xrightarrow{X_\gamma}\gamma(a)\xrightarrow{\kappa}\sigma^{-1}\gamma(a)$ gives
$$
\text{cycles of }X_\gamma\cup\kappa_\sigma \;\leftrightarrow\; \text{cycles of }\pi_\gamma:=\sigma^{-1}\gamma\in S_A,\qquad \text{length }2\ell\leftrightarrow\ell
$$
$$
\{\pi_\gamma:\gamma\in\mathcal C\}=\pi_0A_3 \in\{A_3,\ S_3\setminus A_3\}
\;\Rightarrow\; \#\{\pi_\gamma\text{ a 3-cycle}\}\in\{2,0\}
$$
- **1 crossing.** $\kappa=\{xy,\ a_1a_2,\ b_1b_2\}$ with $x\in A$, $y\in B$. The map $\gamma\mapsto\gamma(x)$ is a bijection $\mathcal C\to B$, so exactly one $\gamma$ has $xy\in X_\gamma$, giving a 2-cycle (0). For the other two:
$$
x\to y\to\gamma^{-1}(y)\to a''\to\gamma(a'')\to\gamma(x)\to x \quad\text{(one 6-cycle)}\;\Rightarrow\; 2
$$
$$
\Rightarrow\quad \textstyle\sum_{\gamma\in\mathcal C}[X_\gamma\cup\kappa \text{ Ham}]\equiv 0 .
$$

## 3. T1: three-cycle annihilation

$\tau=(a\,b\,c)$, $P\in\mathcal M_n$. At most one edge of $P$ lies in $\{a,b,c\}$.

- **Case 1:** $ab\in P$ (cyclic relabel), $cd\in P$:
$$
\{P,\tau P,\tau^2P\}=\{\{ab,cd\},\{bc,ad\},\{ca,bd\}\}\cup P' \;\xrightarrow{\text{L-A, L-B}}\; \text{parity }0
$$
- **Case 2:** $aa',bb',cc'\in P$ with $a',b',c'\notin\{a,b,c\}$:
$$
\tau P\leftrightarrow\gamma_0\tau^{-1},\quad \tau^2P\leftrightarrow\gamma_0\tau
\;\Rightarrow\; \{P,\tau P,\tau^2P\}=\{X_\gamma\cup P':\gamma\in\mathcal C\}\;\xrightarrow{\text{L-A, L-C}}\; \text{parity }0
$$
$$
\forall Q:\ H[P,Q]+H[\tau P,Q]+H[\tau^2P,Q]=0
\;\Rightarrow\; r_P+r_{\tau P}+r_{\tau^2P}=0
\;\Rightarrow\; \boxed{I+\rho(\tau)+\rho(\tau)^2=0 \text{ on } W_n}
$$
`[CHK]` all $P$, all $\tau$.

## 4. T2: edge relations

$\Gamma_{ij}:=\rho((i\,j))$.

$$
\text{(R1)}\ \Gamma_e^2=I \qquad
\text{(R2)}\ e\cap f=\varnothing\Rightarrow \{\Gamma_e,\Gamma_f\}=0 \qquad
\text{(R3)}\ |e\cap f|=1\Rightarrow \{\Gamma_e,\Gamma_f\}=I \qquad
\text{(R4)}\ \Gamma_{ij}+\Gamma_{jk}+\Gamma_{ik}=0
$$

Here $\{X,Y\}:=XY+YX$, which over $\mathbb F_2$ is also the commutator.

- **R2:** disjoint transpositions commute, and $2=0$.
- **R3:** $(ij)(jk)$ and $(jk)(ij)$ are mutually inverse 3-cycles $\tau,\tau^2$, so $\{\Gamma_{ij},\Gamma_{jk}\}=\rho(\tau)+\rho(\tau)^2\overset{\mathrm{T1}}{=}I$.
- **R4:** $(ij)(jk)(ij)=(ik)$. Right-multiplying R3 by $\Gamma_{ij}$ gives $\Gamma_{ik}+\Gamma_{jk}=\Gamma_{ij}$.

Uniform form:
$$
\{\Gamma_e,\Gamma_f\}=(|e\cap f| \bmod 2)\,I\qquad\forall e,f\quad(e=f:\ 2\equiv 0)
$$
`[CHK]` all edge pairs and triples.

## 5. T3: the Clifford action (main target)

$$
U_n=\{x\in\mathbb F_2^{2n}:\textstyle\sum x_i=0\},\qquad q(x)=\tfrac12\mathrm{wt}(x)\bmod 2,\qquad v_{ij}=\varepsilon_i+\varepsilon_j
$$
$$
\mathrm{wt}(x+y)=\mathrm{wt}\,x+\mathrm{wt}\,y-2|x\wedge y| \;\Rightarrow\; q(x+y)=q(x)+q(y)+b(x,y),\quad b(x,y)=x\cdot y
$$
$$
b(v_e,v_f)=|e\cap f|\bmod 2,\qquad q(v_e)=1,\qquad \mathrm{rad}\,b|_{U_n}=\langle\mathbf 1\rangle,\qquad q(\mathbf 1)=n\bmod 2
$$

**Descent** `[OBL]`. Let $\partial:\mathbb F_2^{E(K_{2n})}\twoheadrightarrow U_n$, $e\mapsto v_e$.
$$
\ker\partial=Z_1(K_{2n})=\mathrm{span}\{\triangle_{1jk}: 2\le j<k\}
$$
These are the fundamental cycles of the star tree at vertex 1, with $\binom{2n-1}{2}=\binom{2n}{2}-(2n-1)$ of them. Since $\tilde\Gamma:e\mapsto\Gamma_e$ kills every triangle by R4:
$$
\exists!\ \Gamma:U_n\to\mathrm{End}_{\mathbb F_2}(W_n)\ \text{linear},\qquad \Gamma(v_e)=\Gamma_e
$$

**Polarization.** Let $\beta(x,y):=\{\Gamma(x),\Gamma(y)\}+b(x,y)I$. It is bilinear, and $\beta(v_e,v_f)=0$ by T2, so $\beta\equiv 0$.

Let $g(x):=\Gamma(x)^2+q(x)I$. Then $g(x+y)=g(x)+g(y)+\beta(x,y)=g(x)+g(y)$, so $g$ is additive, hence $\mathbb F_2$-linear. Since $g(v_e)=I+I=0$, $g\equiv 0$.
$$
\boxed{\Gamma(x)^2=q(x)I,\qquad \{\Gamma(x),\Gamma(y)\}=b(x,y)I}
\;\xrightarrow{\text{univ. prop.}}\;
\mathrm{Cl}(U_n,q)\to\mathrm{End}_{\mathbb F_2}(W_n)
$$
Equivariance: $\rho(\sigma)\Gamma(x)\rho(\sigma)^{-1}=\Gamma(\sigma x)$.

## 6. T4: hyperbolic frame and irreducibility (no PBW, no structure theorem for singular Cl)

For $k=1,\dots,n-1$:
$$
e_k:=\sum_{i=1}^{k}v_{2i-1,2i},\qquad f_k:=v_{2k,2k+1}
$$
$$
b(e_k,e_l)=0,\quad b(f_k,f_l)=0\ (k\ne l),\quad b(e_k,f_l)=\delta_{kl},\quad q(e_k)=k\bmod 2,\quad q(f_k)=1
$$
Proof hint: $|\{2i-1,2i\}\cap\{2l,2l+1\}|=1\iff i\in\{l,l+1\}$, so the sum over $i\le k$ gives $\delta_{kl}$.
$$
Y:=\mathrm{span}\{e_k,f_k\},\qquad \dim Y=2n-2,\qquad U_n=Y\perp\langle\mathbf 1\rangle
$$

Operators, needing only R1–R3 (not T3):
$$
E_k:=\sum_{i\le k}\Gamma_{2i-1,2i},\qquad F_k:=\Gamma_{2k,2k+1}
$$
$$
E_k^2=(k\bmod 2)I,\quad F_k^2=I,\quad \{E_k,F_k\}=I,\quad [X_k,Y_l]=0\ \ (k\ne l,\ X,Y\in\{E,F\})
$$
`[CHK]`

**Local factor** `[OBL]`. Let $\mathcal A_\kappa:=\mathbb F_2\langle E,F\rangle/(E^2=\kappa,\ F^2=1,\ EF+FE=1)$. It is spanned by $1,E,F,EF$, so $\dim\le 4$. It surjects onto $M_2(\mathbb F_2)$ via
$$
\kappa=1:\ E=\begin{pmatrix}1&1\\0&1\end{pmatrix},\ F=\begin{pmatrix}1&0\\1&1\end{pmatrix};\qquad
\kappa=0:\ E=\begin{pmatrix}0&1\\0&0\end{pmatrix},\ F=\begin{pmatrix}0&1\\1&0\end{pmatrix}
$$
Hence $\mathcal A_\kappa\cong M_2(\mathbb F_2)$.

**Assembly** `[STD]`. The factors commute, so
$$
\Phi:\ \bigotimes_{k=1}^{n-1}\mathcal A_{k\bmod 2}\cong M_{2^{n-1}}(\mathbb F_2)\longrightarrow \mathrm{End}_{\mathbb F_2}(W_n)
$$
is a unital algebra map. The domain is simple and $\Phi(1)=I\ne 0$, so $\Phi$ is injective.

- **C1 (no CKN).** $W_n$ is an $M_{2^{n-1}}(\mathbb F_2)$-module, so $W_n\cong(\mathbb F_2^{2^{n-1}})^{\oplus m}$ and $\boxed{2^{n-1}\mid\operatorname{rank}_{\mathbb F_2}H_{2n}}$, with $m\ge1$ because $W_n\ne0$ (an even Hamiltonian cycle splits into two perfect matchings).
- **C2.** With [EXT] $\operatorname{rank}\le 2^{n-1}$: $m=1$, and $\Phi$ is bijective, so $\mathrm{im}\,\Phi=\mathrm{End}(W_n)$.
- Since $E_k,F_k\in\rho(\mathbb F_2S_{2n})$, we get $\rho(\mathbb F_2S_{2n})=\mathrm{End}_{\mathbb F_2}(W_n)$, so
$$
\boxed{W_n \text{ is absolutely irreducible},\quad \dim 2^{n-1}}
$$
`[CHK]` $\dim\langle E_k,F_k\rangle=4^{n-1}=(\dim W_n)^2$.

## 7. Corollaries

**C3 (radical).** For any $M\in\mathcal M_n$, $\mathbf 1=\sum_{e\in M}v_e$, so $\Gamma(\mathbf 1)=\sum_{e\in M}\Gamma_e$. Since $b(\mathbf 1,\cdot)=0$, $\Gamma(\mathbf 1)$ commutes with $\mathrm{im}\,\Phi=\mathrm{End}(W_n)$, so $\Gamma(\mathbf 1)=\lambda I$. Then $\lambda^2=q(\mathbf 1)$ with $\lambda\in\mathbb F_2$ gives
$$
\boxed{\textstyle\sum_{e\in M}\Gamma_e=(n\bmod 2)\,I}
$$
`[CHK]`

**C4 (conceptual form, not needed above)** `[STD]`. This needs $\dim\mathrm{Cl}(V,q)=2^{\dim V}$ in characteristic 2.
$$
\mathrm{Cl}(U_n,q)\cong \mathrm{Cl}(Y)\otimes\mathbb F_2[z]/(z^2+n)\cong M_{2^{n-1}}(\mathbb F_2)\otimes\Lambda_n,\quad \Lambda_n \text{ local}
$$
So $\mathrm{Cl}(U_n,q)$ has a unique simple module, $W_n$.

**C5 (COD-105 hook).** $W_n\otimes\overline{\mathbb F}_2$ is irreducible, so it has one composition factor. COD-105 item 2 collapses. On that factor the minimal polynomial of $\rho(\tau)$ is $x^2+x+1$: $\rho(\tau)$ cannot be a scalar, because it is defined over $\mathbb F_2$ and $\rho(\tau)=I$ would give $3I=I\ne0$.

## 8. Dependency DAG

```
L-A ─┬─ L-B ─┐
     └─ L-C ─┴─ T1 ── R1..R3 ──┬── R4 ── Descent ── T3 (Cl(U_n,q)-module) ── C4
                               │
                               └── frame (E_k,F_k) ── A_κ≅M2 ── Φ injective ── C1 (2^{n-1} | rank)
                                                                     │
                                         [EXT] rank ≤ 2^{n-1} ───────┴── C2 / T4 (abs. irreducible) ── C3, C5
```

The only external input to T4 is the upper bound $\operatorname{rank}\le 2^{n-1}$. The lower bound and divisibility come from $\Phi$, which narrows COD-103 to the $\le$ half.

## 9. Finite checks (`check_clifford.py`, exact over F₂)

| n | \|M_n\| | rank H | R1–R4 | frame relations | dim⟨E,F⟩ | Γ(1) |
|---|---|---|---|---|---|---|
| 2 | 3 | 2 | ✓ | ✓ | 4 | 0 |
| 3 | 15 | 4 | ✓ | ✓ | 16 | I |
| 4 | 105 | 8 | ✓ | ✓ | 64 | 0 |
| 5 | 945 | 16 | ✓ | ✓ | 256 | I |
