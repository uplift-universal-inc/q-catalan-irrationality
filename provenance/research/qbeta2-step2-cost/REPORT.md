# Independent cyclotomic denominator theorem for the step-two q-beta(2) determinant

Date: 2026-10-11. This note proves the cyclotomic arithmetic bound for the construction below. It does not independently establish the p-content, analytic estimate, or infinitely-many-nonzero-determinants hypotheses. Those ingredients must be supplied separately before asserting irrationality.

## 1. Construction and result

Let p>=2 be an integer and define

B_2(1/p)=sum_(n>=1) n p^n/(p^(2n)+1),
L(f)=sum_(m>=1) chi_4(m) theta f(p^-m),
D_K(x)=prod_(a=1)^K(1-p^(-2a)x),
Delta_K(X)=det[L_X(x^(i+j)/D_K)]_(0<=i,j<K).

The formal functional is determined by

mu_0=0,
mu_j=j p^j/(p^(2j)+1) for j>=1,
L_X((1-p^(-2a)x)^(-1))=(-1)^a(X-S_(2a)),
S_N=sum_(b=1)^N chi_4(b)g_2(p^-b), g_2(y)=y/(1-y)^2.

Replace p by z. The explicit exponents E(K,d) below give

C_K(z) Delta_K(X) in Z[z,z^-1][X],
C_K(z)=prod_(1<=d<=4K) Phi_d(z)^E(K,d).

For every fixed p>=2,

log C_K(p)=[C+o(1)]K^3 log p,
C=1/6+5281/(675 pi^2)=0.959373586392868... .

If the separately proved content lower bound is p^((5/6)K^3+O(K^2)) and the separately proved analytic bound is log|Delta_K(B_2)|<=-(1/3)K^3 log p+O(K^2), these bounds leave the strictly positive normalized-decay margin

7/6-C=1-5281/(675 pi^2)=0.207293080273799... .

The strict inequality follows already from pi^2>9, since 5281<6075. This note uses the sufficient 5/6 content constant; it does not assume the numerically suggested sharper 7/8 constant.

## 2. Local setup and cluster basis

Fix a primitive d-th root omega and use tau=log(z/omega). The pole locations z^(2a) collide in index classes with spacing

h=d/gcd(d,2).

Let F(x)=prod_a(x-z^(2a)); in a cluster I of size m use

G_j(x)=(F/F_I)(x) prod_(upper j nodes b in I)(x-z^(2b)), 0<=j<m.

These bases, taken over all clusters, give an invertible basis change over the local ring. This follows from the Chinese remainder decomposition between distinct residue centers and the unit triangular change from powers of x-rho within each cluster. The determinant of the basis change is a local unit, so pole orders of Gram determinants are unchanged.

Products of basis vectors from distinct clusters are divisible by F, so their proper-part pairing is exactly zero. At a node of their own cluster, G_j has valuation at least j; the residue denominator F' has valuation m-1.

Polynomial quotients have coefficients analytic in tau, since division is by the monic F. Their moments can have poles only at d divisible by four: z^(2j)+1 vanishes at omega precisely when d=4u and j is an odd multiple of u. All such moment poles are simple.

## 3. Odd d

Finite tails have poles of order at most two, and polynomial moments are regular. The proper pairing of indices j,k in a size-m cluster has valuation at least j+k-m-1. The weights

w_j=max(0,(m+1)/2-j)

therefore clear the block. Its determinant cost is

f(m)=sum_(j=0)^(m-1) max(0,m+1-2j)=floor((m+2)^2/4) for m>=1; f(0)=0.

Write K=rd+t, 0<=t<d. The first t index classes have size r+1 and the others size r. Put A=min(K,floor((d-1)/2)). A cluster whose smallest index a is at most A has 2a<d, so S_(2a) is analytic at omega. Its last upper-node vector vanishes at every upper node; all entries involving it receive only the analytic lower-node contribution. Its weight can be reduced to zero, saving (3-m)_+.

Thus, for odd d,

E(K,d)=t f(r+1)+(d-t)f(r)
       -min(A,t)(2-r)_+ -(A-t)_+(3-r)_+.

For K<d<=2K this reduces to 2(K-floor((d-1)/2)). For d>2K it is zero. The factor (-1)^a in the formal tail data changes signs but not these local valuation bounds.

## 4. d=2h with h odd

No finite tail is singular because possible singular g_2 terms have even index and chi_4 then vanishes. Polynomial moments are regular too. The data may alternate within a collision cluster, so no analytic interpolation cancellation is assumed here.

The raw proper-part valuation bound is j+k-m+1. Weights max(0,(m-1)/2-j) give cluster cost floor(m^2/4). Summing cluster costs gives exactly

E(K,2h)=sum_(a>=1 odd)(K-ah)_+.

This treats the alternating X coefficient explicitly through a general bound; it does not reuse the vanishing cost valid for step-four poles.

## 5. d=4u: at most simple poles and the double-zero residue

Collision spacing is 2u. Thus epsilon_a=(-1)^a is constant within a collision cluster, and its center rho=omega^(2a) satisfies rho^u=epsilon_a.

The finite tails are analytic term by term, but their divided differences can be singular. We now exhibit an integral interpolant after multiplying the data by tau.

For N=2a in a fixed index class modulo d, the coefficient of tau^r in S_N(omega exp(tau)) is

(-1)^r/r! sum_(b<=N) chi_4(b)b^r g_(r+2)(omega^-b).

The coefficient multiplying b^r is periodic with period d. The sum is therefore a polynomial in N of degree at most r+1. Multiplication by tau followed by N=log(x/rho)/tau shows that tau S_N is the restriction of a formal power series in tau and x-rho. This justifies integral divided differences after multiplication by tau.

The degree-(r+1) coefficient determines the residue. Define

G_1(y)=sum_(b=1)^d chi_4(b)g_1(omega^-b y), g_1(y)=y/(1-y).

Finite Fourier summation gives

G_1(y)=c u y^u/(1+y^(2u)), c!=0.

Summing the highest-degree coefficients yields the residue interpolant for tau S_N,

[G_1(1)-G_1(rho/x)]/d.

Therefore the residue interpolant for tau epsilon_a(X-S_N) is, up to a common nonzero scalar,

H_a(x)=x^u/(1+x^(2u))-epsilon_a/2.

Because rho^u=epsilon_a in {+1,-1}, H_a has a double zero at x=rho; its denominator is a local unit there. Multiplication by the unit factors arising from partial fractions preserves this double zero.

The proper-part residue inside a cluster of size m is a divided difference of order m-1 of a numerator with a zero of order at least j+k+2 at rho. Thus entries vanish whenever j+k>m-3, and the block residue rank is at most (m-2)_+. Summing clusters gives

rank(proper residue)<=(K-4u)_+.

For the polynomial-part residue, every polynomial f of degree <=u lies in the radical: multiplying it by a polynomial of degree <K and dividing by D_K gives quotient degree at most u-1, below the first singular moment index u. Hence

rank(polynomial residue)<=(K-u-1)_+.

The whole matrix has at most a simple pole. A size-K matrix of this kind whose residue has rank at most R has determinant pole order at most min(K,R). Consequently

E(K,4u)=min(K,(K-4u)_+ +(K-u-1)_+).

No independence between the two residue forms is required: the sum of ranks is only an upper bound.

## 6. Global integral clearer

The exact construction uses Laurent polynomials with integer coefficients and denominators that factor into cyclotomic polynomials: pole differences, finite tails, and moments all have this property. There are no other irreducible denominator factors. The characteristic-zero local bounds above therefore imply by Gauss's lemma that the product C_K clears every coefficient over Z[z,z^-1]. They do not introduce factorial or constant prime denominators.

## 7. Cubic arithmetic constant

Use

sum_(d<=x odd) phi(d)=(2/pi^2)x^2+o(x^2),
sum_(u<=x) phi(4u)=(8/pi^2)x^2+o(x^2).

For odd d<=K the unsaved cluster cost gives 1/12+10/(3pi^2). The range K<d<=2K contributes 8/(3pi^2). The upper-node saving is

(4/pi^2)[int_(2/5)^(1/2) x((5/2)x-1)dx
         +int_(1/2)^(2/3) x(x/2)dx
         +int_(2/3)^1 x(2x-1)dx]
=1219/(1350pi^2).

Thus

C_odd=1/12+6881/(1350pi^2)=0.599771158994760... .

For d=2h with h odd, each (K-ah)_+ contributes 2/(3pi^2 a^2), and the sum over positive odd a is pi^2/8. Hence

C_(v2=1)=1/12.

For d=4u, putting x=u/K gives

C_(v2>=2)=(16/pi^2)[int_0^(1/5) x dx
                      +int_(1/5)^(1/4) x(2-5x)dx
                      +int_(1/4)^1 x(1-x)dx]
=409/(150pi^2)=0.276269094064774... .

Adding the three disjoint classes gives C=1/6+5281/(675pi^2). Replacing cyclotomic degrees by log Phi_d(p)/log p changes only lower-order terms for fixed p. Tail truncation in the infinite positive-part sums is justified by their convergent sums of inverse squares.

## 8. Exact finite audit

`check.py` constructs the exact rational determinant polynomial and verifies coefficientwise clearing by the stated exponents for p=2,3,4,5,6 and every K=1,...,20. All 100 cases pass; `check.json` records every exponent vector. This confirms these finite instances and accompanies the all-size proof. It is not the logical basis for the asymptotic theorem.

Reproduction requires Python with python-flint and the neighboring `qbeta2/step2.py` exact construction engine. Run `python check.py`.

## 9. Simpler sufficient version for the main proof

The full low-order odd-cluster saving in Section 3 is unnecessary for a positive margin. For the main proof one may use these simpler odd exponents:

- If d is odd and d<=K, use E_coarse(K,d)=t f(r+1)+(d-t)f(r), with no upper-node saving.
- If d is odd and K<d<=2K, use E_coarse(K,d)=2(K-floor((d-1)/2)). Here all clusters are singletons; analyticity for 2a<d is immediate and requires no upper-node argument.
- For odd d>2K use zero.
- Keep the even exponents of Sections 4–5 unchanged.

The resulting global constant is

C_coarse=1/6+1309/(150pi^2)=1.050862862585468...,

and the normalized-decay margin under the separate 5/6 content and 1/3 analytic bounds is

7/6-C_coarse=1-1309/(150pi^2)>41/1350>0,

using only pi^2>9. (The displayed decimal is diagnostic; the exact expression and rational strict lower bound are the assertions.)

This version avoids the low-order upper-node saving entirely and suffices for the candidate irrationality assembly. The sharper constant and its exact checks can remain an optional refinement. The coarse exponents dominate the checked exponents coefficientwise, so all 100 exact integrality checks also pass for this version.
