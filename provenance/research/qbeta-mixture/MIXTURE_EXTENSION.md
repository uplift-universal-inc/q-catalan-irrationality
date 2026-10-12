# Mixed q-beta(1)/q-beta(2): an internally derived linear-independence extension

Date: 2026-10-11. This is a separate extension of the step-two determinant candidate. It includes a complete mathematical assembly based on the local cluster and moving-denominator lemmas audited in this research turn. It is not a claim of external validation or established novelty.

## Claimed extension and normalization

For each integer p>=2 define, in this precise normalization,

`B_1(p)=sum_(j>=1) p^j/(p^(2j)+1)`,

`B_2(p)=sum_(j>=1) j p^j/(p^(2j)+1)`.

The candidate extension is that **1, B_1(p), B_2(p) are linearly independent over Q**.

It is enough to prove irrationality of `Xi=A B_1+B B_2` for every integer pair A,B not both zero, with A even. Indeed any proposed rational linear relation can be multiplied by a common denominator and then by two. Requiring A even merely keeps the local constant A/2 integral, and places no restriction on rational linear relations.

Let q=1/p, let chi be the character modulo four, and put theta=x d/dx. Use the renormalized functional

`L(f)=A sum_(m>=1) chi(m)[f(q^m)-f(0)]`

`     +B sum_(m>=1) chi(m) theta f(q^m)`.

Both sums converge absolutely on functions analytic near [0,q]. Constants are annihilated. Its moments are

`mu_j=(A+Bj)p^j/(1+p^(2j))` for j>=1, `mu_0=0`.

With `g_0(y)=y/(1-y)`, `g_1(y)=y/(1-y)^2`, and

`S_N=sum_(m=1)^N chi(m)[A g_0(q^m)+B g_1(q^m)]`,

absolute double-series summation gives the pure pole value

`L((1-p^(-2a)x)^(-1))=(-1)^a(Xi-S_(2a))`.

Define L_X by replacing Xi by X in this identity, and put

`D_K(x)=prod_(a=1)^K(1-p^(-2a)x)`,

`Delta_K(X)=det[L_X(x^(i+j)/D_K)]_(i,j<K)`.

The coefficient of X is the shared signed residue; it is **not** multiplied by A+B. The exact leading coefficient is unchanged:

`[X^K]Delta_K=(-1)^K p^[K(K^2-1)]`.

## 1. Local p-primary content, including the extra constant

Fix ell|p. Define ell-adically

`Z_r=sum_(m>=1)chi(m)g_r(p^m)`,

`H_r(t)=sum_(m>=1)chi(m)g_r(p^m t)` for r=0,1.

The reciprocal identities are `g_0(y^(-1))=-1-g_0(y)` and `g_1(y^(-1))=g_1(y)`. Also

`sum_(m=1)^(2a)chi(m)=(1-(-1)^a)/2`.

Writing epsilon_a=(-1)^a and y_a=p^(2a), the pole data are exactly

`epsilon_a(X-S_(2a))=epsilon_a U-A/2+H(y_a)`,

`U=X+A/2+A Z_0-B Z_1`,

`H(t)=-A H_0(t)+B H_1(t)`

`     =sum_(j>=1) [(-A+Bj)p^j/(1+p^(2j))]t^j`.

Since A is even, U is an integral polynomial at ell. The coefficients of H have valuation at least `v_ell(p)j`.

Let `F_K(x)=prod_a(x-y_a)` and let h_t denote the complete homogeneous functions in the y_a. The same partial fractions as in the step-two content proof give

`M_k=L_X(x^k/F_K)=-U T_k+R_k+C_k`,

`T_k=sum_a epsilon_a y_a^(k-1)/F_K'(y_a)`,

where R_k is integral: its analytic-tail part is `-sum_(j>=1)[(-A+Bj)p^j/(1+p^(2j))]h_(k+j-K)` and its polynomial quotient part uses the integral moments mu_j. The additional common pole constant gives

`C_0=-A/[2F_K(0)]`,

`C_k=(A/2)h_(k-K)` for k>=1.

Thus **R_0+C_0 need not be integral**. Its possible valuation loss is at most `v_ell(p)K(K+1)`, exactly the already allowed bound at k=0. For 1<=k<K, C_k=0; for k>=K it is integral.

Consequently the same coefficientwise entry bound remains valid:

`v_ell(M_k)>=-v_ell(p) max(K-k,0)[max(K-k,0)+1]`.

The discrete-concavity rearrangement of determinant terms therefore gives the full unchanged content exponent

`E_K=[10K^3+3K^2-10K-3(K mod2)]/12`

`    =(5/6)K^3+O(K^2)`.

This proof includes composite p and the prime ell=2. Dropping the new C_0 term or declaring the entire remainder integral would be incorrect, although the final bound survives it.

## 2. The real bound survives zeroth-order renormalization

Only odd lattice indices carry nonzero chi. Use the monic basis

`B_j(x)=prod_(t=1)^j(x-q^[2ceil(t/2)-1])`,

`a_j=sum_(t=1)^j[2ceil(t/2)-1]`.

Its determinant of basis change is one. For `f=B_i B_j/D_K`, its value at zero has absolute value `q^(a_i+a_j)`. Put `R=max(ceil(i/2),ceil(j/2))`.

At all earlier odd nodes m<2R-1, both f(q^m) and theta f(q^m) vanish: one basis factor has a double root there. The renormalized zeroth-order summand is nevertheless `-f(0)`, not zero. Its total over those earlier nodes is bounded by `|f(0)|`, since partial sums of chi have absolute value at most one. Even the coarser O(K)|f(0)| bound would suffice.

At a surviving node x=q^m, all polynomial roots are at least x. The usual product differentiation and uniform reciprocal-weight estimates give

`|theta f(x)| <= C(i+j+1)q^(a_i+a_j) x/q^(2R-1)`.

The same estimate is valid on the interval [0,x]. Integrating `f'(t)=theta f(t)/t` consequently gives

`|f(x)-f(0)| <= C(i+j+1)q^(a_i+a_j) x/q^(2R-1)`.

Summing the surviving odd geometric progression is bounded independently of K. If R=0, f=1/D_K and the ordinary bound `theta f=O(x)` gives the same conclusion directly. Therefore

`|L(B_i B_j/D_K)| <= C_(A,B)(i+j+1)q^(a_i+a_j)`.

Hadamard after extracting the row and column powers yields

`log|Delta_K(Xi)| <= -(1/3)(log p)K^3+O_(p,A,B)(K^2)`,

because `2 sum_(j<K)a_j=K^3/3+O(K^2)`.

## 3. Complete coarse cyclotomic exponents

Replace p by z. The original functional uses integer Laurent rational functions localized only at cyclotomic factors, because A,B are integers. The following bounds consequently yield a coefficientwise integer Laurent-polynomial clearer.

For odd d<=K, write K=rd+t and define f(0)=0, `f(m)=floor((m+2)^2/4)` for m>=1. Use

`E(K,d)=t f(r+1)+(d-t)f(r)`.

For odd K<d<=2K use

`E(K,d)=2(K-floor((d-1)/2))`,

and use zero for odd d>2K. These are precisely the coarse step-two bounds: finite tails have at most double poles and polynomial moments are regular. Outside the collision range all singleton moments with 2a<d are analytic.

For d=2h with h odd, finite tails and polynomial moments are analytic, but the pole data may alternate within a cluster. The raw divided-difference weights therefore give

`E(K,2h)=sum_(a>=1 odd)(K-ah)_+`.

The only change from the pure B_2 construction occurs at d=4u.

### 3a. The B_1 residue is locally analytic with a simple zero

Fix a primitive d-th root omega, d=4u, set tau=log(z/omega), and let rho be a collision center. Collision spacing is 2u, so epsilon_a is constant within a cluster, with rho^u=epsilon_a.

Define the finite Fourier sum

`G(y)=sum_(b=1)^d chi(b)g_0(omega^(-b)y)`.

Geometric-series summation, or the finite Fourier transform of chi, gives

`G(y)=c u y^u/(1+y^(2u))`, with c nonzero.

In a fixed class N=2a modulo d, the coefficient of tau^r in the finite B_1 tail is

`(-1)^r/r! sum_(b<=N)chi(b)b^r [theta_y^r g_0](omega^(-b))`.

It is a polynomial in N of degree at most r+1. Its highest coefficient is `(-1)^r(theta^r G)(1)/(d(r+1)!)`. Multiplication by tau and substitution `N=log(x/rho)/tau` therefore give an integral formal local interpolant. Its residue is

`I_0(x)=(1/d) integral_0^[log(x/rho)] G(e^(-t)) dt`.

This is a convergent local power series near x=rho, regardless of how a global antiderivative is written. It vanishes there, and

`I_0'(rho)=G(1)/(d rho) !=0`.

Thus it has a simple zero. For the B_2 tail the corresponding residue is

`I_1(x)=[G(1)-G(rho/x)]/d`.

It has a double zero because theta G(1)=0. Every mixture `A I_0+B I_1` has at least a simple zero. If A=0 its order is at least two, but this improvement is unnecessary.

The formal substitution is well defined coefficientwise: a monomial N^j tau^(r+1) becomes tau^(r+1-j)log(x/rho)^j with nonnegative tau exponent; for any fixed tau and x-rho degree only finitely many terms contribute. Thus no unproved global logarithm branch or transcendental denominator assertion enters the local valuation bound.

### 3b. Residue ranks

The full matrix has at most a simple pole at d=4u. In a size-m cluster, the proper-part residue entry of indices j,k vanishes when `j+k>m-2`, because its numerator has the extra zero just proved and its divided difference has order m-1. Its rank is at most `(m-1)_+`. Summing the 2u clusters gives

`rank(proper residue)<=(K-2u)_+`.

The polynomial quotient part is unchanged: the first potentially singular moment index is u, and the degree-at-most-u subspace is in the exact radical of its coefficient form. Thus

`rank(polynomial residue)<=(K-u-1)_+`.

Use the sufficient exponent

`E(K,4u)=min(K,(K-2u)_+ +(K-u-1)_+)`.

Because the matrix has only a simple pole, residue rank bounds its determinant pole order. An O(1) correction to the residue matrix is integral and cannot increase that bound.

### 3c. Cost and global integrality

Let `C_K(p)=prod_(d<=4K) Phi_d(p)^E(K,d)`. The three order classes contribute respectively

`C_odd=1/12+6/pi^2`,

`C_(v2=1)=1/12`,

`C_(v2>=2)=82/(27pi^2)`.

For the last expression use `sum_(u<=H)phi(4u)~8H^2/pi^2` and integrate `min(1,(1-2x)_++(1-x)_+)` against `16x/pi^2`. It gives

`(16/pi^2)[integral_0^(1/3)x dx +integral_(1/3)^(1/2)x(2-3x)dx +integral_(1/2)^1x(1-x)dx]`.

The total logarithmic cubic coefficient is therefore

`C_mix=1/6+244/(27pi^2)<7/6`.

The strict inequality follows, for example, from pi>31/10: `1-244/(27pi^2)>1547/25947>0`.

The local bounds and the original cyclotomic localization prove `C_K(z)Delta_K(X)` is an integer Laurent polynomial in z. Combining specialization at p with the prime-by-prime content bound gives

`P_K(X)=C_K(p)p^(-E_K)Delta_K(X) in Z[X]`, `deg P_K=K`.

## 4. Explicit Cauchy transform and infinitely many nonzero values

For |z|>q, the transform is

`F(z)=A sum_(m>=1)chi(m)[1/(z-q^m)-1/z]`

`     +B sum_(m>=1)chi(m)q^m/(z-q^m)^2`.

Both series converge locally normally away from zero and the odd-index nodes, and F is analytic at infinity with order O(z^(-2)). At an odd node q^m:

- if B!=0 there is a genuine double pole with coefficient `B chi(m)q^m`;
- if B=0 then A!=0 and there is a genuine simple pole with coefficient `A chi(m)`.

Hence F is nonrational. The subtraction of 1/z affects neither these principal parts nor their noncancellation.

The moving-denominator nonvanishing lemma applies verbatim. For completeness: singularity at size n supplies a nonzero Q_n of degree at most n-1 whose first n weighted moments vanish. The polynomial divided-difference identity yields `FQ_n-T_n=O(z^(-1))`, with zeros at p^2,...,p^(2n). Consecutive singular sizes force `T_n/Q_n=T_(n+1)/Q_(n+1)` by a polynomial with n zeros and degree at most n-1. An eventually singular tail would then give a fixed rational T/Q, with bounded-degree multipliers Q_n/Q. Since the nonzero error FQ-T has finite order at infinity, it is nonzero at all sufficiently large exterior nodes; the multipliers would have arbitrarily many zeros. This contradiction proves infinitely many nonzero actual determinants.

No positivity, determinant-sign pattern, or genericity of A,B is used.

## 5. Assembly

The content, coefficient clearer, and real bound give

`log|P_K(Xi)| <= -[1-244/(27pi^2)](log p)K^3+o(K^3)`.

Infinitely many values are nonzero. If Xi=a/b were rational, b^K P_K(a/b) would be an integer, nonzero infinitely often, whose absolute value tends to zero. This is impossible. Therefore every such mixture Xi is irrational, and clearing rational relation coefficients proves the claimed linear independence.

This argument does not establish independence of the ordinary beta values, ordinary Catalan's constant, or a limit as q tends to one.

## Exact finite tests

`check.py` independently constructs exact mixed moments using Fraction arithmetic and checks all coefficients after the stated coarse cyclotomic and p-primary normalization. It includes A=2,B=-1, where cancellation-sensitive sign conventions matter, and checks the unchanged leading coefficient. The tested pairs are `(2,1),(2,-1),(2,0),(0,1),(4,3)`, bases p=2,3,4,6, and sizes K=1,...,6: 120 exact cases. Results are in `checks.json`. These tests are consistency evidence accompanying the all-index argument.
