# A uniform p-primary content bound for the step-two q-beta(2) determinant

Date: 2026-10-11. Status: independent all-index derivation. The bound is deliberately conservative; it does not extrapolate the observed 7/8 cubic coefficient.

## Theorem

Let p>=2 be an integer, q=1/p, and let chi be the nontrivial Dirichlet character modulo four. Define

`B=sum_(j>=1) j p^j/(p^(2j)+1)`,

`L(f)=sum_(m>=1) chi(m) theta f(q^m)`,

`D_K(x)=prod_(a=1)^K (1-p^(-2a)x)`.

The formal functional L_X has polynomial moments

`L_X(1)=0`, `L_X(x^j)=mu_j=j p^j/(p^(2j)+1)`,

and simple-pole moments

`L_X((1-p^(-2a)x)^(-1))=(-1)^a(X-S_(2a))`,

where `S_A=sum_(m=1)^A chi(m) g(p^(-m))` and `g(y)=y/(1-y)^2`. Put

`Delta_K(X)=det[L_X(x^(i+j)/D_K)]_(0<=i,j<K)`.

For every prime ell dividing p, every coefficient of Delta_K has valuation at least

`v_ell(p) E_K`,

where

`E_K=K^2(K+1)-sum_(i=0)^(K-1) t_i(t_i+1)`, `t_i=max(K-2i,0)`.

Equivalently,

`E_K=[10K^3+3K^2-10K-3(K mod 2)]/12`.

In particular,

`E_K=(5/6)K^3+O(K^2)`.

The stronger finite content values reported elsewhere are compatible with this lower bound, but are not used. All claims are coefficientwise in X and valid for composite p.

## 1. The alternating local-tail identity

Fix ell|p and put r=v_ell(p). All series in this subsection are taken in Q_ell. Define

`Z=sum_(m>=1) chi(m) g(p^m)`,

`H(t)=sum_(m>=1) chi(m) g(p^m t)=sum_(j>=1) mu_j t^j`.

These converge at the required arguments, since `v_ell(mu_j)>=rj`. The inversion identity `g(y^(-1))=g(y)` and `chi(m+2a)=(-1)^a chi(m)` give

`S_(2a)=Z-(-1)^a H(p^(2a))`.

Consequently, with U=X-Z and y_a=p^(2a),

`(-1)^a(X-S_(2a))=(-1)^a U+H(y_a)`.

The alternating coefficient of U cannot be discarded. That is exactly why the full step-four content proof does not transplant unchanged.

## 2. Monic-denominator moments

Let

`F_K(x)=prod_(a=1)^K(x-y_a)`.

Then `D_K=(-1)^K p^(-K(K+1))F_K`. Let h_t be the complete homogeneous symmetric polynomial in y_1,...,y_K, with h_0=1 and h_t=0 for t<0. It satisfies `v_ell(h_t)>=2rt` for t>=0.

Polynomial division and the divided-difference identity give, for k>=0,

`M_k(X):=L_X(x^k/F_K)=-U T_k+R_k`,

`T_k=sum_(a=1)^K (-1)^a y_a^(k-1)/F_K'(y_a)`,

`R_k=-sum_(j>=1) mu_j h_(k+j-K)`

`    +sum_(j=1)^(k-K) mu_j h_(k-K-j)`.

The second sum is empty if k-K<1. In the first sum, every nonzero term has valuation at least `rj+2r(k+j-K)>=0`, tending to infinity. The second sum is integral as well. Thus every R_k is ell-integral, and U is an integral polynomial in X because Z is integral.

## 3. Entrywise quadratic valuation bound

For a fixed a,

`v_ell(F_K'(y_a))=r[2aK-a^2-a]`.

This is obtained by using `v_ell(y_a-y_b)=2r min(a,b)` and summing over b!=a. Therefore

`v_ell(y_a^(k-1)/F_K'(y_a))`

`=r[a^2+(2k-2K-1)a]`.

For 0<=k<K, the minimum over a=1,...,K is `-r(K-k)(K-k+1)`. The adjacent minimizers may cancel, which would improve the valuation; the proof only uses the lower bound. For k>=K, every displayed valuation is nonnegative.

Since R_k is integral, the coefficientwise Gauss valuation satisfies

`v_ell(M_k)>=r h(k)`,

`h(k)=-max(K-k,0)[max(K-k,0)+1]`.

The exponent here depends on `y_a^(k-1)`, not `y_a^k`; retaining the minus one is necessary for the exact finite formula.

## 4. Rearrangement of the determinant exponents

The sequence h(k) is discretely concave: its successive increments are `2(K-k)` for k<K, and zero thereafter. For i<j and a<b this gives the Monge inequality

`h(i+a)+h(j+b) <= h(i+b)+h(j+a)`.

Indeed, compare the sum of equal numbers of successive increments over the two shifted intervals; concavity makes the earlier interval's increments larger. Removing any inversion of a permutation therefore cannot increase its total cost. Thus for every permutation pi of 0,...,K-1,

`sum_i h(i+pi(i)) >= sum_i h(2i)`.

Every determinant term of `[M_(i+j)]` has valuation at least the right side times r. Addition cannot lower this bound, so

`v_ell(det[M_(i+j)]) >= -r sum_i t_i(t_i+1)`.

Finally

`Delta_K=(-1)^(K^2) p^[K^2(K+1)] det[M_(i+j)]`,

which proves the stated E_K. Summing the even or odd arithmetic progression gives the closed formula.

## 5. Relation to the full irrationality budget

If the other independent ingredients provide a cyclotomic coefficient-clearer with cubic logarithmic cost C and the real determinant bound has cubic decay 1/3, this result permits total budget

`5/6+1/3=7/6`.

Hence any rigorously established `C<7/6` suffices for the arithmetic-plus-real comparison. An exact 7/8 content asymptotic is unnecessary for that comparison. This note proves only the p-primary content component; the real estimate, complete cyclotomic bound, and nonvanishing argument must be checked separately.

## Finite independent checks

`check.py` uses fresh Fraction arithmetic, exact polynomial division and residues, and determinant interpolation. It tests p=2,3,4,6 and 1<=K<=10, checking all coefficient valuations against E_K and the exact leading coefficient

`[X^K]Delta_K=(-1)^K p^[K(K^2-1)]`.

The exact leading coefficient follows independently from the Vandermonde determinant of the simple-pole residue matrix and the product of the alternating node signs. These finite checks corroborate the formulas; they do not replace the all-index proof.
