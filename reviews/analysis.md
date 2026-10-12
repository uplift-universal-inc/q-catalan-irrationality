# Fresh analytic review of the pure q-Catalan candidate

Review date: 12 October 2026. Supplied source baseline: `b19558937c91876d6330c8464871e146a820c909`. The supplied source directory is not a Git worktree, so this review binds to the exact file hashes below rather than independently certifying that commit label.

## Scope and source identity

I read the complete `sources/ledger/qbeta/qbeta2/PROOF_CANDIDATE.md`, `sources/ledger/qbeta/qbeta2-audit/MIXTURE_FINAL_AUDIT.md`, and `sources/ledger/qbeta/PARENT_REVIEW.md`. The latter two are corroborating records, not mathematical authorities. I independently reconstructed the analytic estimates and nonvanishing proof; their prior approvals were not assumed.

| Source | SHA256 |
|---|---|
| `PROOF_CANDIDATE.md` | `ea0b193954e83afa6f715eb4296df29397d28b3dced4e73dd120343129dcd588` |
| `MIXTURE_FINAL_AUDIT.md` | `50139c5e7a01343858bdbc448d6a78a2aab452dcf44f28ccd02f7ac0735ba021` |
| `PARENT_REVIEW.md` | `4079bff38f5b9b4050484c744d094166db347734cd4aa4e6896d93838dc0bb26` |

The assigned scope is the pure theorem for every integer \(p\ge2\), with emphasis on convergence, entry decay, degree bounds, shared kernel zeros, compact-support annihilation, and infinitely many nonzero determinants. I also checked the growth calculation in Section 4 from the displayed exponents and the final analytic/arithmetic assembly. I did **not** independently certify the local arithmetic bounds in Sections 2–3 or review bibliography or novelty. No source or manuscript was edited.

## Verdict

**No blocking mathematical error found in the assigned analytic and nonvanishing argument.** The all-size entry estimate, cubic decay exponent, and infinitely-many-nonzero conclusion are valid. The final irrationality contradiction is correctly scaled, conditional on the integer normalization proved in the separately reviewed arithmetic sections. One minor wording clarification is recorded below; no change of theorem or analytic constant is needed.

## Findings

### QC-AN-001 — Clarify the transform's extended domain and convergence quantifiers

**Severity:** low; exposition only, not an obstruction to the proof.

**Exact evidence:** Section 1 initially defines \(L\) on rational functions analytic near \([0,q]\). Section 6, lines 378–382, writes

\[
\mathcal F(z)=L((z-x)^{-1})
=\sum_{m\ge1}\frac{\chi(m)q^m}{(z-q^m)^2}
\]

and then uses the series away from zero and the support. Line 414 says, “All expansions and differentiations converge uniformly away from the support.”

The initial \(L\)-notation literally applies to this kernel for \(z\notin[0,q]\); the displayed series supplies its continuation to the complement of the closed support. Uniformity of this series and its differentiated versions is **local**, on compact subsets of that complement. The geometric expansion in powers of \(1/z\), used for orthogonality, is justified on exterior regions \(|z|\ge r>q\), not on the entire complement of the support. All arguments in the source need only these correct forms of uniformity.

**Smallest repair:** State that the series continues the initially defined transform to

\[
\Omega=\mathbb C\setminus\bigl(\{0\}\cup\{q^{2s+1}:s\ge0\}\bigr),
\]

and replace the sentence at line 414 by: “The defining series and their derivatives converge locally uniformly on \(\Omega\); the geometric expansion at infinity is valid under \(L\) on every exterior region \(|z|\ge r>q\).” The same local convergence assertion applies to \(R_{n,Q}\), for each fixed \(n,Q\).

## Independently checked proof obligations

### QC-AN-002 — Functional convergence and genuine poles: verified

For every \(C^1\) function on the interval,

\[
|L(f)|\le\sum_{m\text{ odd}}q^m\|f'\|_\infty
=\frac{q}{1-q^2}\|f'\|_\infty.
\]

Thus \(L\) is continuous in the \(C^1\) norm, and all rational functions used in the determinant construction are in its domain: \(D_n\) has its zeros at \(p^{2a}>q\). This also justifies applying \(L\) to the geometric Cauchy-kernel expansion and its derivative on \(|z|\ge r>q\). The initial double-sum rearrangement is absolute, since

\[
\sum_{m\ge1}\sum_{j\ge1}j q^{mj}
=\sum_{m\ge1}\frac{q^m}{(1-q^m)^2}<\infty.
\]

For a compact subset of \(\Omega\), sufficiently large \(m\) give a denominator bounded away from zero, so the transform tail is bounded by a constant times \(\sum q^m\). The same argument works after any fixed number of \(z\)-derivatives. Near one odd node \(x_m=q^m\), isolate its summand: the remaining series is analytic there, while the isolated term has double-pole coefficient \(\chi(m)x_m\ne0\). The infinitely many poles prove nonrationality, including nonrationality of the germ at infinity by analytic continuation on the connected domain \(\Omega\). The transform is analytic at infinity with \(O(z^{-2})\) decay.

**Source anchors:** Section 1, definition of \(L\) and the moment identities; Section 6, lines 375–382.

### QC-AN-003 — Entry estimate and determinant exponent: verified

Let \(R=\max(R_i,R_j)\). Every odd node with \(m<R\) is a double root of at least one of \(B_i,B_j\); therefore the entire product and its derivative vanish there. This remains true if the other factor is constant. For \(m\ge R\), every root exponent of each nonconstant factor is at most \(m\), and direct product differentiation gives exactly the source's bounds

\[
|B_j(q^m)|\le q^{a_j},\qquad
|\theta B_j(q^m)|\le j q^{a_j}q^{m-R_j}.
\]

The constants for \(W_K\) are uniform in \(K\):

\[
\theta\log W_K(x)
=\sum_{a=1}^K\frac{q^{2a}x}{1-q^{2a}x}
\le\frac{q^2x}{(1-q^2)(1-q^3)}\le\frac8{21}x,
\]

and \(-\log(1-t)\le t/(1-t)\) gives \(W_K\le e^{4/21}\). Consequently, at every surviving node,

\[
|\theta(B_iB_jW_K)(q^m)|
\le e^{4/21}q^{a_i+a_j}(i+j+8/21)q^{m-R}.
\]

When \(i=j=0\), take \(R=0\); the same inequality follows directly from the \(W_K\) derivative bound. For \(R\ge1\), the surviving odd-node sum of \(q^{m-R}\) is \(1/(1-q^2)\le4/3\); when \(R=0\), it is smaller. Since \((4/3)e^{4/21}<2\), this proves

\[
|L(B_iB_j/D_K)|\le2(i+j+1)q^{a_i+a_j}.
\]

The monic triangular basis change has determinant one. After extracting the indicated row and column factors, each row has Euclidean norm at most \(2(2K-1)\sqrt K\). Hence (15) follows from Hadamard, for every \(K\ge1\), with no sign or nonvanishing premise.

The exponent identity is exact because \(2\lceil j^2/2\rceil=j^2+\mathbf1_{j\text{ odd}}\):

\[
2\sum_{0\le j<K}a_j
=\frac{K(K-1)(2K-1)}6+\lfloor K/2\rfloor.
\]

It yields \(-K^3\log p/3+O_p(K^2)\), since the prefactor contributes only \(O(K\log K)\).

**Source anchors:** Section 5, lines 330–371.

### QC-AN-004 — All interpolation degree bounds and common zeros: verified

For a singular \(n\times n\) matrix, a nonzero kernel vector gives a nonzero polynomial \(Q_n\) of degree at most \(n-1\), with the stated \(n\) orthogonality relations. There is no assumption that its degree is exactly \(n-1\).

As a polynomial in \(z\), the numerator defining \(T_{n,Q}\) has degree at most \(n\) and vanishes at \(z=x\). Its quotient by \(z-x\) therefore has degree at most \(n-1\). Applying \(L\) to its finitely many rational-in-\(x\) coefficients preserves that bound. The pointwise algebraic identity at line 404 is exact.

The expansion

\[
\frac1{z-x}=\sum_{j=0}^{n-1}\frac{x^j}{z^{j+1}}
+\frac{x^n}{z^n(z-x)}
\]

together with \(C^1\) continuity proves \(R_{n,Q_n}=O(z^{-n-1})\). The constants may depend on \(n,Q_n\), which is sufficient. Since \(\deg D_n=n\), the error is \(E_n=O(z^{-1})\). At each \(p^{2a}\), \(R_{n,Q_n}\) is analytic and \(D_n\) vanishes, giving the asserted interpolation zero even when \(Q_n\) also vanishes there.

For consecutive singular sizes, the polynomial

\[
C_n=T_{n+1}Q_n-T_nQ_{n+1}
=Q_{n+1}E_n-Q_nE_{n+1}
\]

is \(O(z^{n-1})\), since \(\deg Q_{n+1}\le n\). Thus \(\deg C_n\le n-1\). Both errors vanish at all \(n\) common exterior nodes, so \(C_n\) has \(n\) distinct roots and is identically zero. This includes \(n=1\). **No evaluation of the rational quotient \(T_n/Q_n\) at a node is used**, so shared zeros cannot invalidate the argument.

**Source anchors:** Section 6, lines 384–422.

### QC-AN-005 — Eventual singularity gives a contradiction: verified

If every size \(n\ge N\) is singular, the consecutive equalities give one reduced rational function \(T/Q\). Coprimality implies polynomial factorizations \(Q_n=U_nQ\), \(T_n=U_nT\). If \(T=0\), choose the reduced representation \(T=0,Q=1\); the same conclusion holds. Every \(U_n\) is nonzero.

The fixed function \(E=\mathcal FQ-T\) is nonzero and meromorphic at infinity. Since \(U_NE=O(z^{-1})\), it actually has a zero at infinity of some finite integer order \(h\ge1\):

\[
E(z)=c z^{-h}(1+O(z^{-1})),\qquad c\ne0.
\]

Then \(U_nE=O(z^{-1})\) forces \(\deg U_n\le h-1\) for every \(n\ge N\). This is a bound independent of \(n\). There is also a fixed radius beyond which \(E\) has no zeros. For every exterior node \(p^{2a}\) beyond that radius with \(a\le n\), \(E_n=U_nE=0\) forces \(U_n(p^{2a})=0\). Their number tends to infinity with \(n\), contradicting the fixed degree bound. Thus infinitely many actual determinants are nonzero.

**Source anchors:** Section 6, lines 424–426.

### QC-AN-006 — Compact support causes no hidden annihilation problem: verified

The source does not rely on positivity or on a bare assertion that compact support implies nonvanishing. Nevertheless, the relevant stronger property can be checked explicitly: no nonzero fixed polynomial \(Q\) can satisfy \(L(x^jQ)=0\) for every \(j\ge0\).

Indeed those moment conditions would make

\[
H_Q(z)=L\left(\frac{Q(x)}{z-x}\right)
\]

vanish on \(|z|>q\), by the justified expansion. Its continued series is

\[
H_Q(z)=\sum_{m\text{ odd}}\chi(m)x_m
\left(\frac{Q'(x_m)}{z-x_m}+\frac{Q(x_m)}{(z-x_m)^2}\right).
\]

At each support node with \(Q(x_m)\ne0\) there is a genuine double pole. A nonzero polynomial has only finitely many zeros, so such poles exist and contradict the identically zero continuation. This verifies the compact-support issue for the signed derivative functional without improperly treating it as a positive measure. It is an independent check, not an additional premise needed by QC-AN-005.

**Source anchors:** the functional in Section 1 and the Cauchy transform in Section 6.

### QC-AN-007 — Growth assembly and final polynomial degree: verified within scope

From the displayed \(E(K,d)\), the odd \(d\le K\) contribution rewrites as

\[
E(K,d)=2K+\sum_{a\ge3,\ a\text{ odd}}(K-ad)_+.
\]

The stated odd totient asymptotic follows directly from

\[
\sum_{d\le T,\ d\text{ odd}}\varphi(d)
=\sum_{r\le T,\ r\text{ odd}}\mu(r)
\sum_{s\le T/r,\ s\text{ odd}}s
=\frac{2}{\pi^2}T^2+O(T\log T).
\]

Writing \(u=2^vs\), \(s\) odd, gives \(\varphi(4u)=2^{v+1}\varphi(s)\), and hence the second asymptotic with coefficient \(8/\pi^2\). Partial summation gives each fixed odd-\(a\) positive-part contribution \(2K^3/(3\pi^2a^2)+o(K^3)\). A bound of the form \(O(K^3/a^2)\), obtained using \(\varphi(d)\le d\), justifies truncation uniformly. These yield the source's four contributions

\[
\frac1{12}+\frac{10}{3\pi^2},\quad
\frac8{3\pi^2},\quad
\frac1{12},\quad
\frac{409}{150\pi^2}.
\]

The last integral equals \(409/2400\) before multiplication by 16; this was also checked in exact rational arithmetic. Summing gives \(C=1/6+1309/(150\pi^2)\). The unweighted exponent sum is \(O(K^2\log K)\): each colliding range is bounded by a harmonic sum of \(O(K^2/d+K)\), and the remaining ranges contribute \(O(K^2)\). The uniform Möbius-product error for \(\log\Phi_d(p)\) is valid, so it does not alter the cubic constant.

I also independently checked the exact degree assertion. With \(r_a=p^{2a}\), the coefficient-of-\(X\) matrix is \(V\operatorname{diag}(w_a)V^{\mathsf T}\), where

\[
V_{ia}=r_a^i,\qquad
w_a=\frac{(-1)^a}{\prod_{b\ne a}(1-r_a/r_b)}.
\]

Multiplying the weights by the squared Vandermonde gives

\[
[X^K]\Delta_K=(-1)^K\left(\prod_{a=1}^K r_a\right)^{K-1}
=(-1)^Kp^{K(K^2-1)}\ne0.
\]

The nonzero scalar normalization preserves degree \(K\). Given the independently required integer-coefficient assertion, the rationality lower bound \(b^KP_K(a/b)\in\mathbb Z\) is therefore valid. Combining the stated \(c_K=5K^3/6+O(K^2)\) with the checked analytic exponent gives

\[
C-\frac56-\frac13=-1+\frac{1309}{150\pi^2}=-\delta<0.
\]

The bound \(\delta>41/1350\) follows from \(\pi^2>9\). Along the infinitely many nonzero indices, the \(O(K)\) cost \(K\log b\) cannot offset the negative cubic term. No assumption that all sufficiently large determinants are nonzero is needed.

**Source anchors:** Section 1, equation (1); Section 4, lines 275–326; Section 7, lines 428–448. The proof of the input \(p\)-content and cyclotomic integrality assertions remains outside this review's certification.

## Disposition

The analytic estimate and nonvanishing argument may proceed to manuscript preparation after the arithmetic dependency is separately accepted. QC-AN-001 should be addressed when expressing the analytic domains and convergence in the manuscript. This report establishes neither novelty nor external acceptance, and its findings apply only to the exact source hashes above.
