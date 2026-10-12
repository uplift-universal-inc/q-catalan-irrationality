# Independent audit: step-2 q-beta(2) functional, real decay, and nonvanishing

11 October 2026. These are all-size analytic results plus separate finite consistency checks. This note does not independently certify the arithmetic normalization; that is assigned to other auditors. It makes no novelty or publication-status claim.

## 1. Correct target and pole signs

Let p>=2, q=1/p, chi=chi_4, theta=x d/dx, and

xi = sum_(n>=1) n q^n/(1+q^(2n)),
L(f)=sum_(m>=1) chi(m)(theta f)(q^m),
D_K(x)=prod_(a=1)^K(1-q^(2a)x).

The target has the equivalent expansion

xi=sum_(m>=1)chi(m)g_2(q^m),  g_2(y)=y/(1-y)^2.

This follows by absolutely convergent double summation and

sum_(m>=1)chi(m)t^m=t/(1+t^2).

Thus L(1)=0 and L(x^j)=j q^j/(1+q^(2j)) for j>=1, as in the proposed code. Put S_(2a)=sum_(m<=2a)chi(m)g_2(q^m). The shift identity chi(m+2a)=(-1)^a chi(m) gives exactly

L((1-q^(2a)x)^(-1))=(-1)^a(xi-S_(2a)).

In particular the alternating coefficient belongs on both xi and the finite-tail term. The proposed entry engine uses this sign correctly.

Let L_X be the corresponding formal rational functional and

Delta_K(X)=det[L_X(x^(i+j)/D_K)]_(0<=i,j<K).

The degree is exactly K. As an independent sign check,

[X^K]Delta_K(X)=(-1)^K p^[K(K^2-1)].

Indeed the ordinary simple-pole coefficient matrix has determinant
(-1)^[K(K-1)/2]p^[K(K^2-1)], and multiplying its node weights by (-1)^a contributes (-1)^[K(K+1)/2]. Their combined sign is (-1)^(K^2)=(-1)^K. This leading coefficient is not a claim about the full polynomial's primitive content.

## 2. Exact all-size real determinant bound

For every K>=1,

|Delta_K(xi)| <= [2(2K-1)sqrt(K)]^K q^b_K,

where

b_K=K(K-1)(2K-1)/6+floor(K/2).

Consequently

log|Delta_K(xi)| <= -(log p)K^3/3+O_p(K^2),

with the inequality understood in the extended sense at zero values.

### Proof

Only odd support indices occur in L. Define the monic basis

B_j(x)=prod_(t=1)^j(x-q^[2ceil(t/2)-1]),  B_0=1,
a_j=sum_(t=1)^j[2ceil(t/2)-1],
R_j=2ceil(j/2)-1 for j>=1; R_0=0.

Every support node q^m with odd m<R_j is a double root of B_j. Therefore B_j and theta B_j vanish there. At each surviving node m>=R_j, all roots rho of B_j satisfy q^m<=rho. Product differentiation yields

|B_j(q^m)|<=q^a_j,
|theta B_j(q^m)|<=j q^a_j q^(m-R_j).

The derivative is zero for j=0.

Write W_K=1/D_K and alpha=theta log W_K. For 0<=x<=q<=1/2,

alpha(x)=sum_(a=1)^K q^(2a)x/(1-q^(2a)x)
        <= [q^2/((1-q^2)(1-q^3))]x <=8x/21.

Also log W_K<=alpha<=4/21. Hence

|W_K|<=exp(4/21),
|theta W_K|<= (8/21)exp(4/21)x.

For h=i+j and R=max(R_i,R_j), all summands in L(B_i B_j W_K) with odd m<R vanish. At a surviving node, the product rule gives

|theta(B_i B_j W_K)(q^m)|
 <= exp(4/21)(h+8/21)q^(a_i+a_j)q^(m-R).

The sum over surviving odd m is bounded by 1/(1-q^2)<=4/3. Since (4/3)exp(4/21)<2, we obtain

|L(B_i B_j W_K)|<=2(i+j+1)q^(a_i+a_j).

The basis change is monic triangular and has determinant one. Extract q^a_i from row i and q^a_j from column j. Hadamard's inequality gives the claimed prefactor and exponent 2sum_(j<K)a_j.

Finally a_j=ceil(j^2/2), so

2sum_(j<K)a_j=sum_(j<K)j^2+#{odd j:0<=j<K}
              =K(K-1)(2K-1)/6+floor(K/2).

No positivity, sign pattern, numerical interpolation, or nonzero assumption is used in this bound.

## 3. Infinitely many nonzero determinants

The actual determinants Delta_K(xi) are nonzero for infinitely many K. This statement is independent of the p-content or cyclotomic arithmetic.

### Proof

The Cauchy transform is

F(z)=L((z-x)^(-1))=sum_(m>=1)chi(m)q^m/(z-q^m)^2.

It converges normally on compact sets avoiding zero and the support nodes. It is analytic at infinity and O(z^-2). At every odd m it has a genuine double pole with nonzero leading coefficient chi(m)q^m; all other summands are analytic nearby. Thus F is not rational.

Suppose Delta_n(xi)=0. Its kernel supplies a nonzero Q_n with degree <=n-1 and

L(x^j Q_n(x)/D_n(x))=0, 0<=j<n.

For any Q of degree <=n-1, define

R_(n,Q)(z)=L(Q(x)/[(z-x)D_n(x)]),
T_(n,Q)(z)=L([Q(z)D_n(x)-D_n(z)Q(x)]/[(z-x)D_n(x)]).

The numerator is divisible by z-x. Therefore T_(n,Q) is a polynomial in z of degree <=n-1, and

F(z)Q(z)-T_(n,Q)(z)=D_n(z)R_(n,Q)(z).

For Q=Q_n, orthogonality makes R_(n,Q_n)(z)=O(z^(-n-1)). Thus

E_n(z):=F(z)Q_n(z)-T_n(z)=O(z^-1).

Moreover E_n(p^(2a))=0 for 1<=a<=n. The transforms R are analytic at these exterior nodes. All expansions and differentiations converge uniformly away from the real support, so these operations are legitimate for the signed functional as well.

If both n and n+1 are singular, the polynomial

V=T_(n+1)Q_n-T_n Q_(n+1)=Q_(n+1)E_n-Q_n E_(n+1)

has degree <=n-1 by its behavior at infinity. It vanishes at the n distinct nodes p^2,p^4,...,p^(2n), hence V=0. No division by the Q_n's at these nodes is used.

If every determinant from some N onward vanished, all T_n/Q_n would equal a fixed reduced rational function T/Q. Write Q_n=U_nQ and T_n=U_nT. Nonrationality of F implies E=FQ-T is nonzero. The condition U_NE=O(z^-1) implies a finite positive vanishing order h of E at infinity. From U_nE=O(z^-1), all degrees deg U_n are <=h-1.

The Laurent expansion of E shows that it has no zeros for sufficiently large |z|. At every sufficiently large exterior node p^(2a) with a<=n, the identity E_n=U_nE forces U_n(p^(2a))=0. This produces arbitrarily many distinct zeros of a nonzero polynomial of bounded degree, a contradiction. Therefore singularity cannot persist at every sufficiently large size.

The change from poles p^(4a) to p^(2a) affects neither the nonrational transform nor the nested-node interpolation argument.

## 4. Independent finite verification

`check.py` has passed:

- 144 formal matrix entries against direct evaluation of the signed differential functional, over p=2,3,4,6 and K=1,...,6.
- 12 primitive determinant evaluations with a separately derived target enclosure.
- Three exact direct determinant comparisons per primitive case, checking the characteristic-polynomial construction at X=0,1,2/3.
- The exact leading coefficient and its alternating sign in every primitive case.

The independent target enclosure sums the **positive** series n q^n/(1+q^(2n)), rather than the proposer's divisor-sum representation. Since each term is bounded above by n q^n, the remaining tail after N is bounded by

(N+1)q^(N+1)/(1-rho),  rho=q(N+2)/(N+1)<1.

For the direct matrix-entry check, the evaluated derivative is

theta(x^k W_K)=x^k W_K[k+theta log W_K].

The omitted signed tail is bounded in absolute value by 2(k+1)q^(N+1)/(1-q). All finite tests use outward-rounded Arb balls.

Representative independently reproduced natural logarithms of primitive absolute values are:

| p | K | log absolute value |
|---|---:|---:|
| 2 | 8 | -67.9646564325 |
| 2 | 16 | -636.641278721 |
| 3 | 8 | -124.478464202 |
| 3 | 12 | -448.069163903 |
| 4 | 8 | -153.990399097 |
| 6 | 8 | -198.756803400 |

Every listed ball excludes zero. These data verify finite values; the all-size decay bound and nonvanishing theorem above do not rely on them. The proposed arithmetic normalization requires its own all-index proof.

## Reproduction

Requires Python 3 and python-flint. Run `python check.py`. The bundled `source/step2.py` is the proposer's exact entry engine with an unused import removed; the functional evaluator, positive-series enclosure, leading-sign check, and determinant comparisons in `check.py` are separate audit code. Full ball enclosures are in `checks.json`.
