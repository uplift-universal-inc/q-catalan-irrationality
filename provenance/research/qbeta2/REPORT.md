# q-beta(2): complete cyclotomic analysis and certified primitive tests

Date: 2026-10-11. Scope: the character-twisted determinant from `qbeta_twist.md`, with s=2, p>=2 an integer. This is a research derivation with finite exact checks, not external validation or an irrationality proof. The improved even-order argument below needs an independent audit before promotion to the theorem inventory.

## Outcome

For

    B_2(1/p) = sum_(n>=1) n p^n/(p^(2n)+1),
    L(f) = sum_(m>=1) chi_4(m) theta f(p^-m),
    D_K(x) = prod_(a=1)^K (1-p^(-4a)x),
    Delta_K(X) = det[L_X(x^(i+j)/D_K)]_(0<=i,j<K),

I obtain the full cyclotomic coefficient-clearer constant

    C = 1/12 + (64/3 - 4759/12150 + 82/27)/pi^2
      = 2.512881890003484... .

This improves a direct safe bound of 2.892022192358174..., but exceeds the available content-plus-decay budget 7/3 by 0.179548556670151.... Consequently these complete estimates do not prove irrationality. Failure of this sufficient bound is not an impossibility theorem for primitive values or for different constructions.

The p=2 primitive values at K=2,4,8,12,16,24,32 are certified nonzero and have natural logarithms of absolute value

    14.2687, 53.5028, 243.2266, 574.7300, 1092.8737, 2941.0482, 6088.9503.

There is no finite evidence of normalized decay at these sizes. These finite observations imply no asymptotic nondecay theorem.

## 1. Local setup

Set p=z, let omega be a primitive d-th root, and use tau=log(z/omega) as a uniformizer over the characteristic-zero local field. Pole positions are z^(4a). Their collision spacing is h=d/gcd(d,4). The rational finite tails are

    S_(4a)(z) = sum_(b=1)^(4a) chi_4(b) g_2(z^-b),
    g_2(y)=y/(1-y)^2.

The polynomial moments are

    mu_j(z)=j z^j/(z^(2j)+1).

Only odd d give singular finite tails. Polynomial moments can be singular only if 4 divides d, say d=4h, and then the first possible singular index is j=h; all such poles are simple. All formulas are in the localization of Z[z,z^-1] at cyclotomic polynomials, so coefficientwise local bounds combine into an integral Laurent-polynomial clearer by Gauss's lemma.

## 2. Odd-order bound

For odd d, put K=rd+t, 0<=t<d. Cluster sizes are r+1 in the first t residue classes and r in the others. A cluster of size m has the proper-part entry bound

    v_tau(entry_(j,k)) >= j+k-m-1.

There are no singular polynomial moments. Weights max(0,(m+1)/2-j) clear this block, at cost

    f(m)=floor((m+2)^2/4) for m>=1; f(0)=0.

For a cluster whose smallest pole index a satisfies 4a<d, the lower-node tail is analytic. Using the upper-node Newton basis, the last basis vector vanishes at all upper nodes, so every proper-part entry involving this vector is analytic. Its weight can be changed to zero, saving (3-m)_+.

Define A=min(K,floor((d-1)/4)). The explicit bound is

    E_odd(K,d) = t f(r+1)+(d-t) f(r)
               -min(A,t)(2-r)_+ -(A-t)_+(3-r)_+.

This also handles d>K, where it reduces to exactly

    E_odd(K,d)=2(K-floor((d-1)/4)),   K<d<=4K.

All odd orders beyond 4K have cost zero.

## 3. Even-order cancellation: the interpolation lemma

Fix a collision class a=c+kh. The coefficient of tau^r in S_(4a)(omega exp(tau)) is

    (-1)^r/r! sum_(b<=4a) chi_4(b)b^r g_(r+2)(omega^-b).

Since the summand apart from b^r is periodic in b, this coefficient is a polynomial in k of degree at most r+1. This implies that multiplying the tail data by tau gives values of a formal power series H(tau,x-rho), integral in tau, at the collision nodes x=z^(4a), where rho=omega^(4c). One direct justification: express each coefficient as a polynomial in a, replace a by log(x/rho)/(4 tau) with the harmless c-dependent translation, and note that the prefactor tau removes all negative powers. The substitution is valid in the completed local ring because x-rho=O(tau) at every node.

Thus the proper-part matrix has at most simple poles at even d. Its residue is determined by the highest-degree, degree-(r+1), coefficient in these period sums.

### 3.1 Orders d=2h with h odd

The full period has length 2d=4h. Pairing b with b+d gives identical omega^-b but opposite chi_4 values. Therefore every period average is zero, for every r. The polynomial in k above has degree at most r, and the tails themselves (without multiplying by tau) admit an integral local interpolant. Divided differences are integral. Polynomial moments are also regular. Consequently

    E(K,d)=0 when v_2(d)=1.

### 3.2 Orders d=4h

Let

    G_1(y)=sum_(b=1)^d chi_4(b) g_1(omega^-b y),
    g_1(y)=y/(1-y).

The elementary finite Fourier sum gives, with a nonzero constant c depending on omega,

    G_1(y)=c h y^h/(1+y^(2h)).

Summing the highest-degree Taylor coefficients in the period sums gives the local interpolant's residue, up to a nonzero common factor, as

    H_0(x)=x^h/(1+x^(2h)) - 1/2
          =-(x^h-1)^2/[2(1+x^(2h))].

Every collision center satisfies rho^h=1. H_0 therefore has a double zero at each center, and its denominator is a local unit there.

Use the Chinese-remainder cluster basis

    G_(c,j)(x)=(F/F_c)(x)(x-rho)^j, 0<=j<m_c,
    F=prod_(a=1)^K(x-z^(4a)).

This is a unit basis change. Proper-part blocks belonging to distinct clusters vanish. Within a cluster, the residue of a proper-part entry is a divided difference of order m_c-1 with numerator containing H_0(x)(x-rho)^(j+k). It vanishes if j+k>m_c-3. Hence the proper-part residue rank is at most

    sum_c(m_c-2)_+ = (K-2h)_+.

The polynomial-part residue form has radical containing every polynomial of degree <=h: multiplying one by any polynomial of degree <K and dividing by D_K gives quotient degree <h, while the first singular moment index is h. Thus its rank is at most

    (K-h-1)_+.

Both parts have at most a simple pole. A size-K matrix with at most a simple pole and residue rank R has determinant pole order at most min(K,R), by the determinant expansion. Therefore

    E_even(K,4h) = min(K,(K-2h)_+ +(K-h-1)_+).

These exponents are upper bounds, not a claim of coefficientwise sharpness.

## 4. Cubic cost

For odd orders,

    sum_(d odd<=K) phi(d) [2K+sum_(a>=3 odd)(K-ad)_+]
      = [1/12 +10/(3pi^2)]K^3+o(K^3).

The upper-node saving is

    (4759/(12150 pi^2)) K^3+o(K^3).

For clarity, this saving comes from the integral

    (4/pi^2)[ integral_(4/9)^(1/2) x(9x/4-1) dx
              +integral_(1/2)^1 x^2/4 dx
              +integral_(4/5)^1 x(5x/4-1) dx ],

whose bracket equals 4759/48600. The outer odd range K<d<=4K contributes 18/pi^2. Thus

    C_odd =1/12 +(64/3 -4759/12150)/pi^2
          =2.205165702645273... .

For even orders only d=4h survives. Using

    sum_(h<=H) phi(4h) = (8/pi^2)H^2+o(H^2),

and E_even/K approaching min(1,(1-2x)_+ +(1-x)_+) at h=xK gives

    C_even =(16/pi^2)[integral_0^(1/3) x dx
                      +integral_(1/3)^(1/2) x(2-3x) dx
                      +integral_(1/2)^1 x(1-x) dx]
           =82/(27pi^2).

For C_K(z)=prod_d Phi_d(z)^E(K,d), the construction therefore gives C_K(z)Delta_K(X) in Z[z,z^-1][X], and

    log C_K(p) = (C_odd+C_even+o(1))K^3 log p.

Combining the existing exact p-content p^(2K(K^2-1)) with the real bound

    log|Delta_K(B_2)| <= -(1/3)K^3 log p+O_p(K^2)

gives only

    log|C_K(p)p^(-2K(K^2-1)) Delta_K(B_2)|
       <= (0.179548556670151...+o(1))K^3 log p.

The coefficient is positive. This does not settle irrationality.

## 5. Computation and scope of certification

- `costs.py` implements all finite exponents and a modular divisibility check for the cyclotomic clearer.
- `check.py` checks exact degree, exact p-content and denominator divisibility for p=2,3,4,5,6 and 1<=K<=16, using rational FLINT matrices. Results: `checks.json`.
- `scan.py` computes the actual primitive integer determinant polynomial at p=2, then evaluates it in Arb. The target enclosure uses B_2=sum_N a_N p^-N with a_N=sum_(d|N)d chi_4(N/d), |a_N|<=N^2. Its tail is bounded geometrically by (N+1)^2 p^(-N-1)/(1-rho), rho=((N+2)/(N+1))^2/p<1. Results: `scan.jsonl`.
- All finite evaluations listed above exclude zero. They certify only those values; they do not establish a limiting sign, asymptotic growth, or infinitely many nonzero determinants.

The best next mathematical improvement would require a lower true combined residue rank, cancellations among odd-order clusters, or changed pole geometry. Positivity and purity alone cannot close this quantified gap.
