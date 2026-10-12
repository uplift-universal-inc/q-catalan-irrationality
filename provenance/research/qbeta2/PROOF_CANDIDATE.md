# A step-two moving-denominator candidate proof for a q-analogue of Catalan's constant

11 October 2026.

**Status.** This is a self-contained research proof candidate assembled from independent internal arithmetic and analytic audits. It awaits external expert review. No novelty or publication-status claim is made. The conclusion concerns the displayed q-series at reciprocal integer arguments, not ordinary Catalan's constant and not a limit as q tends to 1.

Related literature includes F. Jouhet and E. Mosaki, *Diophantine properties for q-analogues of Dirichlet's beta function at positive integers*, [arXiv:0811.4287](https://arxiv.org/abs/0811.4287), which supplies the established collective-irrationality context. The organizing pattern here comes from the supplied internal moving-denominator q-zeta(3) manuscript: pure determinant polynomials, arithmetic normalization, geometric-lattice decay, and nested-node nonvanishing. The step-two character signs and the arithmetic below are specific to this construction.

## Candidate statement

For every integer p>=2, the real number

\[
\xi_p=B_2(1/p):=\sum_{n=1}^{\infty}\frac{n p^n}{p^{2n}+1}
\]

is irrational.

We construct integer polynomials P_K of degree K such that, for a fixed positive delta,

\[
\log|P_K(\xi_p)|\le(-\delta+o(1))K^3\log p,
\qquad
P_K(\xi_p)\ne0\ \text{for infinitely many }K.
\]

The explicit sufficient margin is

\[
\delta=1-\frac{1309}{150\pi^2}>\frac{41}{1350}>0.
\]

The value at zero is understood as negative infinity in logarithmic upper bounds.

## 1. The formal functional and pure determinant

Write q=1/p, let chi=chi_4 be the character with chi(1)=1, chi(3)=-1 and chi(even)=0, and put theta=x d/dx. For rational functions analytic near [0,q], define

\[
L(f)=\sum_{m\ge1}\chi(m)(\theta f)(q^m).
\]

The derivative makes the summands O(q^m), so the series converges absolutely. Let

\[
g_s(y)=\sum_{j\ge1}j^{s-1}y^j,
\qquad g_2(y)=\frac{y}{(1-y)^2}.
\]

Absolute double summation and \(\sum_{m\ge1}\chi(m)t^m=t/(1+t^2)\) give

\[
\xi_p=\sum_{m\ge1}\chi(m)g_2(q^m),\qquad
L(1)=0,\qquad L(x^j)=\mu_j:=\frac{j p^j}{1+p^{2j}}\quad(j\ge1).
\]

Set

\[
S_N=\sum_{b=1}^N\chi(b)g_2(q^b),\qquad
D_K(x)=\prod_{a=1}^K(1-p^{-2a}x).
\]

Since chi(m+2a)=(-1)^a chi(m),

\[
L\big((1-p^{-2a}x)^{-1}\big)=(-1)^a(\xi_p-S_{2a}).
\]

Define the formal functional L_X by replacing xi_p with X in this identity while retaining the rational polynomial moments. Polynomial division and partial fractions uniquely determine L_X on every function f(x)/D_K(x). Thus

\[
\Delta_K(X)=\det\left[L_X\left(\frac{x^{i+j}}{D_K(x)}\right)\right]_{0\le i,j<K}
\in\mathbb Q[X].
\]

The coefficient of X in the moment matrix is a Vandermonde congruence with nonzero node weights. Its determinant is

\[
[X^K]\Delta_K(X)=(-1)^K p^{K(K^2-1)}. \tag{1}
\]

For completeness, the determinant for unsigned simple-pole node weights is
\((-1)^{K(K-1)/2}p^{K(K^2-1)}\), obtained by multiplying the weights and the squared Vandermonde. The factors (-1)^a multiply it by \((-1)^{K(K+1)/2}\); their combined sign is (-1)^K. In particular Delta_K has degree exactly K.

## 2. A coefficientwise p-primary content bound

Put

\[
r_a=p^{2a},\quad F_K(x)=\prod_{a=1}^K(x-r_a),\quad A=K(K+1)/2.
\]

Then D_K=(-1)^K p^{-2A}F_K. Fix a prime ell dividing p and use the ell-adic field. Reciprocity g_2(1/y)=g_2(y) gives the convergent identities

\[
Z=\sum_{b\ge1}\chi(b)g_2(p^b),\qquad
H(t)=\sum_{j\ge1}\frac{j p^j}{1+p^{2j}}t^j,\qquad
S_{2a}=Z-(-1)^aH(r_a).
\]

Both Z and all coefficients of H are ell-integral, and H has zero constant term. Let U=X-Z and

\[
M_k=L_X(x^k/F_K).
\]

Partial fractions give

\[
M_k=-U\sum_{a=1}^K\frac{(-1)^a r_a^{k-1}}{F_K'(r_a)}+R_k, \tag{2}
\]

where R_k is ell-integral. Indeed the H contribution is a convergent sum of divided differences of nonnegative powers: the exponent is k+j-1>=0. For any nonnegative t,
\(\sum_a r_a^t/F_K'(r_a)\) is zero for t<K-1 and otherwise a complete homogeneous symmetric polynomial in the nodes, so it is integral. The polynomial-quotient contribution uses only integral coefficients and the integral moments mu_j.

Since r_a-r_b has valuation \(2\min(a,b)v_\ell(p)\),

\[
\frac{v_\ell(r_a^{k-1}/F_K'(r_a))}{v_\ell(p)}
=a^2+(2k-2K-1)a.
\]

Minimizing this quadratic over 1<=a<=K yields, coefficientwise in U,

\[
v_\ell(M_k)\ge-v_\ell(p)w_K(k),\qquad
w_K(k)=(K-k)_+((K-k)_++1), \tag{3}
\]

where t_+=max(t,0). Translation from U to X preserves this bound because Z is integral.

The sequence h(k)=-w_K(k) is concave. The elementary rearrangement inequality for a concave function of sums gives

\[
\sum_{i=0}^{K-1}h(i+\sigma(i))\ge\sum_{i=0}^{K-1}h(2i)
\]

for every permutation sigma. One may prove this by successively removing inversions: the increasing matching makes the two sums farther apart, and concavity can only decrease their sum. Applying (3) to every determinant term, then using
\(\Delta_K=(-1)^{K^2}p^{2AK}\det[M_{i+j}]\), proves

\[
p^{-c_K}\Delta_K(X)\text{ is ell-integral for every ell dividing p}, \tag{4}
\]

where the integer exponent is

\[
\begin{aligned}
c_K&=K^2(K+1)-\sum_{i=0}^{K-1}(K-2i)_+((K-2i)_++1)\\
&=\frac{10K^3+3K^2-10K-3(K\bmod2)}{12}
=\frac56K^3+O(K^2).
\end{aligned} \tag{5}
\]

This is a lower bound for the whole polynomial's p-primary content. It is sufficient and need not be sharp.

## 3. A complete cyclotomic coefficient clearer

Replace p by an indeterminate z. All exact formulas belong to the localization of \(\mathbb Z[z,z^{-1}]\) at cyclotomic polynomials: the only denominators arise from pole differences, finite tails, and z^(2j)+1. Let Phi_d denote the d-th cyclotomic polynomial. We construct nonnegative integer exponents E(K,d) for which

\[
C_K(z)\Delta_K(X)\in\mathbb Z[z,z^{-1}][X],\qquad
C_K(z)=\prod_{d=1}^{4K}\Phi_d(z)^{E(K,d)}. \tag{6}
\]

Fix a primitive d-th root omega and use tau=log(z/omega) as a local uniformizer. The nodes z^(2a) collide in index classes with spacing h=d/gcd(d,2). Separate these classes by the Chinese remainder decomposition. Within a class I of size m and center rho, a suitable basis is

\[
G_j(x)=(F_K/F_I)(x)(x-\rho)^j,\qquad 0\le j<m.
\]

This is an invertible basis change over the local ring: distinct centers remain distinct modulo tau, and F_K/F_I is a unit at its own center. Products from different classes are divisible by F_K, so their proper-part pairing is zero. Within a class, node evaluations of G_j have valuation at least j and the residue denominator has valuation m-1. Polynomial quotients have coefficients integral in tau. Their moments are regular unless d=4u, in which case their poles are simple and the smallest singular moment index is j=u.

### 3.1 Odd d<=K

Finite tails have poles of order at most two, so proper-part entries have valuation at least j+k-m-1. No polynomial moment is singular. The weights

\[
w_j=\max(0,(m+1)/2-j)
\]

clear the entries after scaling row and column j by tau^w_j. Fractional weights can be interpreted in the quadratic extension of the local field; the total determinant cost is an integer. A size-m class costs

\[
f(m)=\sum_{j=0}^{m-1}\max(0,m+1-2j)
=\left\lfloor\frac{(m+2)^2}{4}\right\rfloor\quad(m\ge1),
\qquad f(0)=0.
\]

Write K=rd+t, 0<=t<d. Use

\[
E(K,d)=t f(r+1)+(d-t)f(r),\qquad d\le K\text{ odd}. \tag{7}
\]

These weights are nonnegative, so they also preserve the regular polynomial part.

### 3.2 Odd K<d<=2K

There are no collisions. The tail S_(2a) is analytic if 2a<d; every other tail has pole order at most two. Polynomial moments remain analytic. Therefore

\[
E(K,d)=2\left(K-\left\lfloor\frac{d-1}{2}\right\rfloor\right),
\qquad K<d\le2K\text{ odd}. \tag{8}
\]

For odd d>2K take E(K,d)=0. Formula (8) can equivalently be written \(2(K-\lceil d/2\rceil+1)\) for odd d.

### 3.3 d=2h, h odd

Every finite tail and every polynomial moment is regular. We do not assume that the data are analytically interpolable: the (-1)^a factor can alternate inside these collision classes. The raw proper-part entry bound is j+k-m+1. Weights max(0,(m-1)/2-j) give class cost floor(m^2/4). Summing the classes gives

\[
E(K,2h)=\sum_{\substack{a\ge1\\a\text{ odd}}}(K-ah)_+,
\qquad h\text{ odd}. \tag{9}
\]

Only finitely many summands are nonzero.

### 3.4 d=4u

Here collision spacing is 2u, so epsilon_a=(-1)^a is constant within each class. Its center rho satisfies rho^u=epsilon_a.

Although the finite tails are individually regular, their divided differences require an additional argument. For N=2a in a fixed residue class modulo d, the coefficient of tau^r in S_N(omega exp(tau)) equals

\[
\frac{(-1)^r}{r!}\sum_{b\le N}\chi(b)b^r g_{r+2}(\omega^{-b}). \tag{10}
\]

The coefficient multiplying b^r is periodic with period d, so this sum is a polynomial in N of degree at most r+1. Substitute
\(N=\log(x/\rho)/\tau\) in tau times its Taylor series. Each resulting term has nonnegative powers of tau, and only finitely many terms occur at each total degree. Thus tau S_N is the restriction to the class nodes of a formal power series in tau and x-rho. This formal argument establishes integral divided differences after multiplication by tau; no analytic convergence assertion in two independent variables is needed.

To find its residue, put

\[
G_1(y)=\sum_{b=1}^{d}\chi(b)g_1(\omega^{-b}y),
\qquad g_1(y)=y/(1-y).
\]

Finite Fourier summation gives

\[
G_1(y)=\kappa u\frac{y^u}{1+y^{2u}},\qquad \kappa\ne0.
\]

Indeed the Fourier coefficients vanish except at indices j congruent to u or 3u modulo 4u; those two coefficients are nonzero and opposite. The degree-(r+1) coefficients of the period sums (10) sum to

\[
\frac{G_1(1)-G_1(\rho/x)}{d}.
\]

Consequently the residue interpolant for tau epsilon_a(X-S_N), up to one nonzero scalar, is

\[
H_a(x)=\frac{x^u}{1+x^{2u}}-\frac{\epsilon_a}{2}. \tag{11}
\]

Because rho^u=epsilon_a, this has a double zero at x=rho, and its denominator is a local unit. The residue of a same-class proper-part entry is a divided difference of order m-1 with numerator containing H_a(x)(x-rho)^(j+k), multiplied by local units. It therefore vanishes for j+k>m-3. Its rank is at most (m-2)_+. Summing classes gives proper-part residue rank at most (K-4u)_+.

For the polynomial-part residue, every polynomial of degree at most u is in the radical: after multiplying it by any polynomial of degree <K and dividing by D_K, the quotient has degree at most u-1, below the first singular moment. Thus this residue has rank at most (K-u-1)_+.

The whole matrix has at most a simple pole. Its residue rank is at most the sum of these two ranks. The determinant of a size-K matrix with at most a simple pole and residue rank R has pole order at most min(K,R), as follows by expansion after diagonalizing the residue over the residue field. We may therefore take

\[
E(K,4u)=\min\{K,(K-4u)_++(K-u-1)_+\}. \tag{12}
\]

### 3.5 Global integrality

Equations (7)-(12) bound the pole order of every coefficient of Delta_K at every possible cyclotomic denominator. These coefficientwise bounds may be obtained by treating X as transcendental over the residue field. The determinant estimates then hold over that field, so they bound all coefficients in X.

To make the last integrality step explicit, write Delta_K=N(z,X)/[z^M product_d Phi_d(z)^a_d] with N in Z[z,X]. The local bounds imply that each necessary power of Phi_d divides every coefficient of N in Q[z]. Since Phi_d is monic, the quotient is in Z[z]. Cancelling all such factors proves (6); the local formal series used in the proof introduce no new integer-prime denominators.

## 4. The arithmetic growth constant

The standard totient asymptotics in the needed residue classes are

\[
\sum_{\substack{d\le T\\d\text{ odd}}}\varphi(d)
=\frac{2}{\pi^2}T^2+o(T^2),\qquad
\sum_{u\le T}\varphi(4u)=\frac{8}{\pi^2}T^2+o(T^2).
\]

Partial summation also gives the corresponding linear-weight sums. In (7), the identity

\[
f(m)=2m+\sum_{\substack{a\ge3\\a\text{ odd}}}(m-a)_+
\]

shows that the odd range d<=K contributes
\(1/12+10/(3\pi^2)\) to the coefficient of K^3. Formula (8) contributes \(8/(3\pi^2)\). For example, the latter is
\((4/\pi^2)\int_1^2 x(2-x)\,dx\).

In (9), each positive odd a contributes \(2/(3\pi^2a^2)\); summing the odd inverse squares gives 1/12. For (12), putting x=u/K gives contribution

\[
\frac{16}{\pi^2}\left[
\int_0^{1/5}x\,dx+
\int_{1/5}^{1/4}x(2-5x)\,dx+
\int_{1/4}^{1}x(1-x)\,dx\right]
=\frac{409}{150\pi^2}.
\]

The infinite positive-part sums are justified by first truncating a and bounding the omitted contributions by a constant times K^3 times the tail of sum 1/a^2. Therefore

\[
\sum_d E(K,d)\varphi(d)=
\left(\frac16+\frac{1309}{150\pi^2}+o(1)\right)K^3.
\]

For fixed p>=2,
\(\log\Phi_d(p)=\varphi(d)\log p+O_p(1)\) uniformly in d, by the Möbius product and convergence of \(\sum_{a\ge1}|\log(1-p^{-a})|\). The sum of exponents is O(K^2 log K), which is lower order. Hence

\[
\log C_K(p)=\left(C+o(1)\right)K^3\log p,
\qquad C=\frac16+\frac{1309}{150\pi^2}. \tag{13}
\]

By (4) and (6),

\[
P_K(X):=C_K(p)p^{-c_K}\Delta_K(X)\in\mathbb Z[X]. \tag{14}
\]

At primes dividing p, use (4); at every other prime, use the Laurent integrality (6). Equation (1) proves that P_K still has degree exactly K.

## 5. An all-size real determinant bound

Only odd geometric nodes occur in L. Use the monic polynomial basis

\[
B_j(x)=\prod_{t=1}^{j}\left(x-q^{2\lceil t/2\rceil-1}\right),\quad
B_0=1,\quad
 a_j=\sum_{t=1}^{j}(2\lceil t/2\rceil-1)=\lceil j^2/2\rceil.
\]

Put R_j=2 ceil(j/2)-1 for j>=1 and R_0=0. Each odd node q^m with m<R_j is a double root of B_j, so both B_j and theta B_j vanish there. At a surviving node m>=R_j, product differentiation gives

\[
|B_j(q^m)|\le q^{a_j},\qquad
|\theta B_j(q^m)|\le j q^{a_j}q^{m-R_j}.
\]

The second expression is zero for j=0. Write W_K=1/D_K. For 0<=x<=q<=1/2,

\[
\alpha(x):=\theta\log W_K(x)
\le\frac{q^2}{(1-q^2)(1-q^3)}x\le\frac8{21}x.
\]

Also log W_K<=alpha<=4/21, whence
\(|W_K|\le e^{4/21}\) and \(|\theta W_K|\le(8/21)e^{4/21}x\).

Using the product rule and summing over surviving odd nodes yields

\[
|L(B_iB_jW_K)|\le2(i+j+1)q^{a_i+a_j}.
\]

Here the geometric sum is at most 4/3 and \((4/3)e^{4/21}<2\). The monic basis change has determinant one. Extracting q^a_i from row i and q^a_j from column j, then applying Hadamard, proves the explicit bound

\[
|\Delta_K(\xi_p)|\le[2(2K-1)\sqrt K]^Kq^{b_K},
\quad
b_K=\frac{K(K-1)(2K-1)}6+\lfloor K/2\rfloor. \tag{15}
\]

Indeed b_K=2 sum_(j<K)a_j. In particular
\(\log|\Delta_K(\xi_p)|\le-(K^3/3)\log p+O_p(K^2)\).
No positivity or nonzero assumption enters this estimate.

## 6. Infinitely many actual determinants are nonzero

Define the Cauchy transform

\[
\mathcal F(z)=L((z-x)^{-1})
=\sum_{m\ge1}\frac{\chi(m)q^m}{(z-q^m)^2}.
\]

The series converges normally on compact sets away from zero and the support. It is analytic at infinity and O(z^-2). At each odd support node it has a genuine double pole with nonzero coefficient chi(m)q^m. It is therefore not rational.

If Delta_n(xi_p)=0, a nonzero kernel vector supplies a polynomial Q_n of degree at most n-1 satisfying

\[
L(x^jQ_n(x)/D_n(x))=0\quad(0\le j<n).
\]

For any such Q, set

\[
R_{n,Q}(z)=L\left(\frac{Q(x)}{(z-x)D_n(x)}\right),
\]

\[
T_{n,Q}(z)=L\left(
\frac{Q(z)D_n(x)-D_n(z)Q(x)}{(z-x)D_n(x)}\right).
\]

Division by z-x is exact in the numerator, so T_(n,Q) is a polynomial of degree at most n-1. Linearity gives

\[
\mathcal F(z)Q(z)-T_{n,Q}(z)=D_n(z)R_{n,Q}(z).
\]

For Q=Q_n, orthogonality makes R_(n,Q_n)=O(z^(-n-1)). Consequently

\[
E_n(z):=\mathcal F(z)Q_n(z)-T_n(z)=O(z^{-1}),
\quad E_n(p^{2a})=0\ (1\le a\le n). \tag{16}
\]

The transforms R are analytic at these exterior nodes. All expansions and differentiations converge uniformly away from the support, justifying the operations for this signed functional.

If n and n+1 are both singular, the polynomial

\[
T_{n+1}Q_n-T_nQ_{n+1}=Q_{n+1}E_n-Q_nE_{n+1}
\]

has degree at most n-1 by its growth at infinity. It vanishes at the n distinct nodes p^2,...,p^(2n), so it is zero. Thus T_n/Q_n=T_(n+1)/Q_(n+1) as rational functions, without dividing by values of Q_n at any node.

Suppose every determinant from some N onward vanished. Choose the common reduced rational expression T/Q and write Q_n=U_nQ, T_n=U_nT. Since the transform is nonrational, \(E=\mathcal F Q-T\) is nonzero. The relation U_NE=O(z^-1) forces E to have a finite positive order h of vanishing at infinity. Every relation U_nE=O(z^-1) then bounds deg U_n<=h-1.

The leading Laurent term of E shows that E has no zeros for sufficiently large |z|. At every sufficiently large exterior node among p^2,...,p^(2n), (16) forces U_n to vanish. This gives arbitrarily many distinct zeros of a nonzero polynomial of degree at most h-1, a contradiction. Hence Delta_K(xi_p) is nonzero for infinitely many K.

## 7. Rationality contradiction

Combine (5), (13), (14), and (15):

\[
\log|P_K(\xi_p)|
\le\left[C-\frac56-\frac13+o(1)\right]K^3\log p
=(-\delta+o(1))K^3\log p,
\]

where
\(\delta=1-1309/(150\pi^2)>41/1350\), using pi^2>9. By Section 6 these integer-polynomial values are nonzero for infinitely many K.

If xi_p=a/b were rational with integers a,b and b>=1, then b^K P_K(a/b) would be an integer, since deg P_K=K. Along those infinitely many nonzero indices it would be a nonzero integer. But

\[
\log|b^K P_K(\xi_p)|
\le K\log b+(-\delta+o(1))K^3\log p\longrightarrow-\infty.
\]

Eventually its absolute value would be strictly between zero and one, which is impossible for an integer. This completes the proposed proof.

## 8. Independent checks and reproducibility

The all-index argument above is separate from the following finite corroboration:

- 100 exact coefficient-denominator checks for p=2,3,4,5,6 and K=1,...,20, including the simpler sufficient clearer used here.
- 40 independent exact rational-polynomial content checks for p=2,3,4,6 and K=1,...,10.
- 144 independent formal-entry versus direct-functional comparisons; 12 independently enclosed primitive determinant values; direct determinant comparisons at X=0,1,2/3.
- Certified p=2 primitive values through K=48, using outward-rounded Arb balls and an explicit infinite-series tail bound. At K=48 the primitive value is enclosed near 2.31706456337800408658276 times 10^(-8478).

Local supporting files are `step2.py`, `step2_scan.py`, `step2_scan.jsonl`; the independent notes and code are in the adjacent `qbeta2-step2-content`, `qbeta2-step2-cost`, and `qbeta2-audit` directories. The primitive polynomials used for these finite values may have smaller normalization than (14); the proof uses only the explicit safe normalization (14).

These computations do not certify the infinite argument by themselves. External mathematical review remains necessary before treating this candidate as an established result, and a dedicated literature comparison is necessary before making any novelty claim.
