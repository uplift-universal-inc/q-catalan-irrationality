# Fresh bounded arithmetic review: pure step-two q-Catalan candidate

Review date: 2026-10-12. Requested baseline: `b19558937c91876d6330c8464871e146a820c909`.

**Verdict: no arithmetic blocker found in the audited coarse construction.** I independently reconstructed the leading coefficient, coefficientwise prime-power content, all three cyclotomic cases, the cubic denominator cost, and the integer-polynomial normalization. The conclusion of this review is conditional on the separate real determinant bound and infinitely-many-nonzero-determinants argument; I did not audit those arguments here. I did not conduct a literature or novelty review.

The evidence below is the reconstruction itself, not the sources' status labels or their reported finite checks. The requested step-four audit was used only as a comparison: its zero cost at orders congruent to two modulo four must not be transferred to the present step-two construction. The present candidate does not make that transfer.

## Source identity and scope

The following are SHA-256 hashes of the actual files read. The `qcatalan-source` directory is a file snapshot without `.git`; I could not independently authenticate its mapping to the requested commit. The nearby `qzeta3-irrationality` checkout is a different checkout, at `1862300092a9fc805c11462c15209d3b5fdee47f`, and does not contain the requested commit object. This is a provenance limitation, not a mathematical defect. These hashes pin the precise review scope.

| Source | SHA-256 |
|---|---|
| `qcatalan-source/qbeta2/PROOF_CANDIDATE.md` | `36450caaf25991a5bda13e681d84272c3f9a023a3abafc23ad0be84ed40c7539` |
| `qcatalan-source/qbeta2-step2-content/CONTENT_PROOF.md` | `3814ed5bd45f007c364fbab602a8754afe748882a8376fa1c46243f933f61596` |
| `qcatalan-source/qbeta2-step2-cost/REPORT.md` | `d601e2561ad5c80daf40e4d20781900ec07edbd7285f97829ef17c7cc4f74eb0` |
| `qcatalan-source/qbeta2-audit/STEP4_CYCLOTOMIC_AUDIT.md` | `f4de18c62028ae06ffe23d4eae029aa2581bb2c29159a2b90ee5ff35707c87c8` |
| `sources/ledger/qbeta/PARENT_REVIEW.md` | `4079bff38f5b9b4050484c744d094166db347734cd4aa4e6896d93838dc0bb26` |

The mathematical audit covers candidate Sections 1–4 and 7. Findings QBA-001–QBA-008 below have severity **none / checked**. QBA-000 is an **informational provenance limitation**: the smallest repair is to record a manifest or verified repository mapping from the above hashes to the intended commit; no mathematical change is required.

## QBA-001 — Formal target and leading coefficient

**Evidence:** candidate lines 50–84, equations (1) and the simple-pole identity. **Smallest repair:** none.

The character shift gives

\[
\sum_{m\ge1}\chi(m)g_2(p^{-m-2a})
=(-1)^a(\xi_p-S_{2a}),
\]

with the sign multiplying both target and tail. Thus the stated formal functional matches the actual target when (X=\xi_p).

Put (r_a=p^{2a}), (F=\prod_a(x-r_a)), and (T=K(K+1)). The coefficient of (X) in the (k\)-th moment is

\[
\sum_a \beta_a r_a^k,
\qquad
\beta_a=\frac{(-1)^{K+1+a}p^T}{r_aF'(r_a)}.
\]

Its Hankel matrix is (V\operatorname{diag}(\beta_a)V^t). Since

\[
\prod_aF'(r_a)=(-1)^{K(K-1)/2}(\det V)^2,
\qquad \prod_ar_a=p^T,
\]

the determinant has sign ((-1)^{K(K+1)/2+K(K-1)/2}=(-1)^K) and power (p^{KT-T}=p^{K(K^2-1)}). This proves the exact degree (K), including the (K=1) case.

## QBA-002 — Coefficientwise content, including composite (p)

**Evidence:** candidate lines 94–154; content note Sections 1–4, especially lines 73–103. **Smallest repair:** none.

Fix any prime (\ell\mid p) and set (r=v_\ell(p)). The inversion identity for (g_2), the character shift, and convergent (\ell)-adic geometric series give

\[
S_{2a}=Z-(-1)^aH(r_a),\qquad
H(t)=\sum_{j\ge1}\mu_jt^j,
\qquad v_\ell(\mu_j)\ge rj.
\]

Both (Z) and (H)'s coefficients are integral. Partial fractions in the monic denominator give exactly

\[
M_k=-U\sum_a\frac{(-1)^ar_a^{k-1}}{F'(r_a)}+R_k,
\quad U=X-Z,
\]

\[
R_k=-\sum_{j\ge1}\mu_jh_{k+j-K}
      +\sum_{j=1}^{k-K}\mu_jh_{k-K-j},
\]

where (h_t=0) for (t<0). The first sum is integral and convergent because each surviving term has valuation at least (rj+2r(k+j-K)), tending to infinity. The second sum is integral. In particular, the exponent (k-1), rather than (k), is correct.

The valuation of an individual alternating summand divided by (r) is

\[
a^2+(2k-2K-1)a.
\]

Its minimum is (-(K-k)(K-k+1)) for (0\le k<K), and it is nonnegative for (k\ge K). Therefore the Gauss valuation bound is coefficientwise in (U), hence also in (X), since translation by an integral (Z) preserves the bound.

The discrete sequence (h(k)=-(K-k)_+((K-k)_++1)) is concave. Uncrossing an inverted assignment yields

\[
h(i+a)+h(j+b)\le h(i+b)+h(j+a)
\quad(i<j,\ a<b).
\]

Thus the identity permutation minimizes the determinant-term valuation sum. Restoring the factor (p^{K^2(K+1)}) gives exactly

\[
c_K=K^2(K+1)-\sum_{i<K}(K-2i)_+((K-2i)_++1)
=\frac{10K^3+3K^2-10K-3(K\bmod2)}{12}.
\]

No primality assumption on (p) was used. Applying this argument separately to every prime divisor of (p), with its actual multiplicity (r), proves the claimed composite-(p) result.

## QBA-003 — Local basis and odd cyclotomic orders

**Evidence:** candidate lines 160–208; cost note Sections 2–3 and 9. **Smallest repair:** none.

At a primitive (d)-th root, nodes collide with spacing (d/\gcd(d,2)). The displayed basis (G_j=(F/F_I)(x-\rho)^j) reduces modulo the local parameter to an invertible confluent Chinese-remainder basis. Its determinant is a unit. Products from distinct clusters are divisible by (F), so their proper-pole contribution vanishes. Division by the monic (F) has integral local coefficients.

For odd (d), moments are regular and finite tails have poles of order at most two. Hence the proper entry valuation is at least (j+k-m-1). Row/column weights

\[
w_j=\max(0,(m+1)/2-j)
\]

clear those entries and preserve the regular polynomial part. Their doubled sum is (f(m)=\lfloor(m+2)^2/4\rfloor) for (m\ge1), with (f(0)=0). Half-integer weights cause no problem after adjoining a square root of the local uniformizer: the resulting determinant exponent is integral.

Thus the coarse exponent for odd (d\le K), with (K=rd+t), is

\[
t f(r+1)+(d-t)f(r).
\]

For odd (K<d\le2K), clusters are singletons. Exactly those (a) with (2a\ge d) may have singular tails, giving (2(K-\lfloor(d-1)/2\rfloor)). For odd (d>2K), no denominator can be singular.

The optional sharper exponent in the cost note is consistent as well: its upper-node basis leaves only the lowest node in the last basis vector. If that node's tail is regular, every entry involving this vector is regular, and eliminating its original weight saves ((3-m)_+). Counting the two possible cluster sizes gives exactly the note's subtraction. This refinement is not needed for the coarse manuscript or its margin.

## QBA-004 — Orders (d=2h) with (h) odd

**Evidence:** candidate lines 210–219; cost note Section 4. **Smallest repair:** none.

Only even tail indices could be singular, and their character values vanish; the polynomial moments are regular. However, ((-1)^a) alternates within a collision class because its spacing (h) is odd. The proof correctly avoids borrowing the stronger step-four interpolation cancellation.

The raw proper entry valuation (j+k-m+1) is cleared by weights \(\max(0,(m-1)/2-j)\), with cluster cost \(\lfloor m^2/4\rfloor\). Using

\[
\lfloor m^2/4\rfloor=\sum_{a\ge1,\ a\ {m odd}}(m-a)_+,
\]

and summing over the (h) cluster sizes yields

\[
E(K,2h)=\sum_{a\ge1,\ a\ {m odd}}(K-ah)_+.
\]

This includes (d=2), where all nodes collide, and gives zero when (h\ge K), as required.

## QBA-005 — Orders (d=4u): formal interpolation and double zero

**Evidence:** candidate lines 221–259; cost note Section 5. **Smallest repair:** none. An optional exposition improvement is to insert the explicit square factorization below.

In a fixed cluster, (N=2a) is fixed modulo (d), (epsilon=(-1)^a) is constant, and (ho^u=epsilon). Write the coefficient of (	au^r) in the finite tail as (P_r(N)). Periodicity of the coefficient of (b^r) proves that (P_r) is a polynomial of degree at most (r+1). Every monomial resulting from

\[
\tau^{r+1}P_r(\log(x/\rho)/\tau)
\]

has the form (	au^{r+1-s}(\log(x/\rho))^s), where (0\le s\le r+1). Its lowest total degree in ((\tau,x-\rho)) is (r+1). Therefore the sum belongs to (mathbb C[[\tau,x-\rho]]): each coefficient receives only finitely many contributions. Evaluation at the class nodes is legitimate because (x-\rho) is divisible by (	au). This establishes integral divided differences after multiplying by (	au), without an analytic convergence assumption in independent variables.

The leading coefficient of the periodic weighted sum is its period mean divided by (r+1). Consequently the residue interpolant is exactly

\[
\frac{G_1(1)-G_1(\rho/x)}d.
\]

The finite character Fourier transform vanishes unless the Fourier index is an odd multiple of (u); its two nonzero classes modulo (4u) have opposite coefficients. Thus

\[
G_1(y)=\kappa u\frac{y^u}{1+y^{2u}},\quad\kappa\ne0.
\]

After multiplying by (-epsilon), the residue for the signed formal data is a common nonzero scalar times

\[
H(x)=\frac{x^u}{1+x^{2u}}-\frac\epsilon2
=-\frac{\epsilon(x^u-\epsilon)^2}{2(1+x^{2u})}.
\]

The denominator equals (4) in the last expression's full denominator at (x=\rho), and (x^u-\epsilon) has a simple zero there. Hence (H) has exactly a double zero. The partial-fraction factors, including (1/x), are units at this nonzero center and preserve it.

A residue entry is a confluent divided difference of order (m-1) whose numerator vanishes to order at least (j+k+2). It vanishes when (j+k>m-3), so the last two rows are zero and its rank is at most ((m-2)_+). Summing over the (2u) balanced classes gives ((K-4u)_+). This verifies both the double-zero mechanism and the factor (4u), which differs from the step-four construction.

## QBA-006 — Polynomial-quotient residue and determinant exponent

**Evidence:** candidate lines 261–266; cost note lines 116–124. **Smallest repair:** none.

At (d=4u), the singular polynomial moments are precisely those with index an odd multiple of (u), and each pole is simple. If (\deg f\le u) and (\deg g<K), the quotient in division of (fg) by (D_K) has degree at most (u-1). It therefore contributes no singular moment. The polynomial-part residue form on the (K)-dimensional space of polynomials of degree less than (K) has a radical of dimension at least (min(K,u+1)), so its rank is at most ((K-u-1)_+).

Every complete entry has at most a simple pole by QBA-005 and this polynomial argument. The rank of the combined residue is at most the sum of the two separate rank bounds; no independence or equality is required. For a size-(K) matrix with a simple pole and residue rank (R), multilinearity after constant row/column reduction gives determinant pole order at most (R), capped at (K). This proves

\[
E(K,4u)=\min\{K,(K-4u)_++(K-u-1)_+\}.
\]

In particular, small-(K) empty quotient ranges and singleton clusters do not require exceptions beyond the displayed positive parts.

## QBA-007 — Cubic arithmetic cost

**Evidence:** candidate Section 4; cost note Sections 7 and 9. **Smallest repair:** none.

The needed totient sums are

\[
\sum_{d\le T,\ d\ {m odd}}\varphi(d)\sim\frac2{\pi^2}T^2,
\qquad
\sum_{u\le T}\varphi(4u)\sim\frac8{\pi^2}T^2.
\]

For the second, directly use (arphi(4u)=2u\sum_{e\mid u,\ e\ {m odd}}\mu(e)/e), giving leading coefficient (sum_{e\ {m odd}}\mu(e)/e^2=8/\pi^2). The first follows similarly by summing odd multiples in the usual totient divisor formula. Thus the densities used in the partial sums are consistent.

For odd (d\le K), the cluster identity is

\[
E(K,d)=2K+\sum_{a\ge3,\ a\ {m odd}}(K-ad)_+.
\]

The first term contributes (4/\pi^2), and each (a)-term contributes (2/(3\pi^2a^2)). Summing gives (1/12+10/(3\pi^2)). The outer odd range contributes (8/(3\pi^2)). Since (arphi(2h)=\varphi(h)) for odd (h), the orders with (v_2(d)=1) contribute (1/12).

For (d=4u), the limiting exponent divided by (K), at (x=u/K), is (1) on ([0,1/5]), (2-5x) on ([1/5,1/4]), and (1-x) on ([1/4,1]). Therefore its coefficient is

\[
\frac{16}{\pi^2}\left(\int_0^{1/5}x\,dx+
\int_{1/5}^{1/4}x(2-5x)\,dx+
\int_{1/4}^{1}x(1-x)\,dx\right)
=\frac{409}{150\pi^2}.
\]

The exact integral in parentheses is (409/2400). Adding all four contributions proves

\[
C=\frac16+\frac{1309}{150\pi^2}.
\]

Truncation of the odd positive-part sums is justified uniformly by their convergent (a^{-2}) tails. The estimate (sum_dE(K,d)=O(K^2\log K)) and the uniformly bounded error (log\Phi_d(p)-\varphi(d)\log p=O_p(1)) make the substitution of logarithmic cyclotomic sizes valid. Numerically (C\approx1.0508628625854677) and (7/6-C\approx0.11580380408119895); the rigorous lower margin (41/1350) follows from (pi^2>9).

## QBA-008 — Global integer coefficients and rationality scaling

**Evidence:** candidate lines 269–273, equation (14), and Section 7. **Smallest repair:** none.

The original formulas use integer Laurent polynomials, monic polynomial division (up to Laurent units), pole differences, tails with denominators ((z^b-1)^2), and moments with denominators (1+z^{2j}). There are no hidden rational constant denominators. All non-Laurent denominator factors are cyclotomic; their possible orders lie within the stated (1\le d\le4K) range.

Treating (X) as transcendental proves each local determinant bound over the coefficient field and therefore for every (X)-coefficient. Monic divisibility then cancels the required cyclotomic factors over (mathbb Z[z]), yielding (C_K(z)\Delta_K\in\mathbb Z[z,z^{-1}][X]). Formal Taylor denominators such as (r!) are used only to establish characteristic-zero local bounds; they do not alter the original denominator set.

For a prime dividing (p), QBA-002 gives integrality of (p^{-c_K}\Delta_K), and multiplication by (C_K(p)\in\mathbb Z) preserves it. At every other prime, Laurent integrality of (C_K(p)\Delta_K) suffices, since (p) is a unit. Hence

\[
P_K=C_K(p)p^{-c_K}\Delta_K\in\mathbb Z[X],\quad\deg P_K=K.
\]

Assuming the separately audited decay (1/3) and infinitely many nonzero actual determinants, the net exponent is (C-5/6-1/3=-\delta<0). For a hypothetical rational target (a/b), multiplication by (b^K) is sufficient and costs (K\log b), negligible against (K^3\log p). The final integer contradiction is correctly scaled.

## Independent bounded exact checks performed

I did not rerun the supplied coefficient or determinant verification scripts; those replays were assigned centrally. A fresh inline Python check, with integer arithmetic and `fractions.Fraction` only, verified:

- the two expressions for (c_K) and (c_K\le K(K^2-1)), for (1\le K\le59);
- the balanced-cluster identities for the coarse odd cost and the (2h) cost, for (1\le K\le59) and (1\le h\le2K);
- the sum of the (4u) proper-residue rank bounds, for (1\le u\le K\le59);
- the determinant-term Monge inequality against every permutation, for (1\le K\le8);
- the exact rational integral (409/2400) and total inverse-(\pi^2) coefficient (1309/150).

All passed. These finite checks corroborate edge cases and exact arithmetic only; the all-index reasons are given in QBA-001–QBA-008. No source or manuscript was edited. This review file is the only written artifact.
